import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.LocalFunctionApplication

/-! Independent structural annotations and lexical bodies fix the original Core.
Static nominal inputs never manufacture the values needed for actual execution. -/
set_option autoImplicit false
namespace Tests.FrontendStructuralLet
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"StructuralLet", by decide⟩], by decide⟩⟩, 35⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"structural-let.sol"⟩,235,1⟩
private def named : Syntax.TypeExpr := ⟨span,.named ⟨span,⟨⟨⟨span,"Payload"⟩,[]⟩⟩⟩ none⟩
private def unitType : Syntax.TypeExpr := ⟨span,.tuple []⟩
private def shape : Nat → Syntax.TypeExpr
  | 0 => ⟨span,.tuple [named]⟩
  | n+1 => ⟨span,.tuple [unitType,shape n]⟩
private def nested (type : Core.Ty) : Nat → Core.Ty
  | 0 => type
  | n+1 => .product .unit (nested type n)
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"],type)]
private theorem meaning (type : Core.Ty) (n : Nat) : StructuralTypeDenotes (types type) (shape n) (nested type n) := by
  induction n with
  | zero => exact .single (.named .head)
  | succ n ih => exact .pair .unit ih
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def unit : Syntax.Expr := ⟨span,.tuple ⟨span,[]⟩⟩
private def returned (name : String) : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (ref name))⟩]⟩
private def bind (annotation : Syntax.TypeExpr) (name : String) (initializer : Syntax.Expr) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span,⟨span,.letDecl ⟨span,name⟩ (some annotation) (some initializer)⟩ :: tail.value⟩
private def seed (type : Core.Ty) : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "seed" type
private def zero : Syntax.Expr := ⟨span,.literal ⟨span,.decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span,.binary zero ⟨span,.equal⟩ zero⟩
private def guardCore : Core.Expr := .binary .wordEq (.word .zero) (.word .zero)
private theorem zeroMeaning : WordLiteralDenotes ⟨span,.decimal "0"⟩ Core.Word.zero :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def branch (left right : Syntax.Block) : Syntax.Block := ⟨span,[⟨span,.ifThen guard left (some right)⟩]⟩
private def tree (annotation : Syntax.TypeExpr) : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => bind annotation name (ref previous) (branch (tree annotation rest name) (returned name))
private def core : Nat → Core.Expr
  | 0 => .var 0
  | n+1 => .letE (.var 0) (.ifE guardCore (core n) (.var 0))
private theorem treeElab (names : List String) (previous : String) (type : Core.Ty) (depth : Nat)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var 0))
    (typed : Resolved.HasType initial.context resolved (nested type depth)) :
    TypedLetReturnTreeElaborates (types type) owner initial (tree (shape depth) names previous)
      (core names.length) (nested type depth) := by
  induction names generalizing previous initial resolved with
  | nil => exact .single (.expression resolution (by simpa only [LocalTypeInputs.context_ids, List.length_nil, core] using lowered) typed)
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      apply TypedLetReturnTreeElaborates.binding (meaning type depth) (fresh name (by simp)) resolution lowered typed
      apply TypedLetReturnTreeElaborates.conditional (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning))
        (.binary .word .word) (.binary .word .word)
      · apply ih name (initial.bindFresh owner name (nested type depth)) _ parts.2
        · intro next member
          simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
          exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
        · exact .identifier .head
        · exact .var .head
        · exact .var .head
      · exact .single (.expression (.identifier .head) (.var .head) (.var .head))
private theorem seeded (names : List String) (type : Core.Ty) (depth : Nat)
    (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed (nested type depth))
      (tree (shape depth) names "seed") (core names.length) (nested type depth) := by
  apply treeElab names "seed" type depth _ _ distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head
private theorem coreTyped (n : Nat) (type : Core.Ty) (tail : Core.Context) (definitions : Core.DataEnvironment) :
    Core.HasType (type :: tail) (core n) type definitions := by
  induction n generalizing tail with
  | zero => exact .var rfl
  | succ n ih => exact .letE (.var rfl) (.ifE (.binary .word .word) (ih (type :: tail)) (.var rfl))

theorem arbitrary_type_and_let_depth_have_independent_exact_provenance
    (names : List String) (type : Core.Ty) (depth : Nat) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (definitions : Core.DataEnvironment) :
    StructuralTypeDenotes (types type) (shape depth) (nested type depth) ∧
    TypedLetReturnTreeElaborates (types type) owner (seed (nested type depth))
      (tree (shape depth) names "seed") (core names.length) (nested type depth) ∧
    TypedLetReturnTreeHasType (types type) owner (seed (nested type depth)) (tree (shape depth) names "seed") (nested type depth) ∧
    elaborateTypedLetReturnTree? (types type) owner (seed (nested type depth)) (tree (shape depth) names "seed") =
      some (core names.length,nested type depth) ∧ Core.HasType [nested type depth] (core names.length) (nested type depth) definitions :=
  ⟨meaning type depth, seeded names type depth distinct fresh, (seeded names type depth distinct fresh).hasType,
    (seeded names type depth distinct fresh).complete, coreTyped _ _ [] definitions⟩

theorem structural_success_does_not_make_the_old_prefix_checker_equivalent
    (type : Core.Ty) (depth : Nat) :
    elaborateTypedLetReturnTree? (types type) owner (seed (nested type depth)) (tree (shape depth) ["local"] "seed") =
      some (core 1,nested type depth) ∧
    elaborateTypedLetReturnBody? (types type) owner (seed (nested type depth)) (tree (shape depth) ["local"] "seed") = none := by
  refine ⟨(seeded ["local"] type depth (by decide) (by decide)).complete, ?_⟩
  apply elaborateTypedLetReturnBody?_eq_none_iff.mpr
  rintro ⟨result, typing⟩
  cases typing with
  | terminal child => cases child with | single child => cases child
  | binding oldMeaning _ _ _ => cases depth <;> cases oldMeaning

theorem first_binding_keeps_old_scope_and_exact_fresh_tail (type : Core.Ty) (depth : Nat) :
    ∃ declared initializer tail,
      interpretStructuralType? (types type) (shape depth) = some declared ∧
      elaborateLocalExpression? (seed (nested type depth)).names (seed (nested type depth)).context (ref "seed") = some (initializer,declared) ∧
      elaborateTypedLetReturnTree? (types type) owner ((seed (nested type depth)).bindFresh owner "local" declared)
        (branch (returned "local") (returned "local")) = some (tail,nested type depth) ∧ core 1 = .letE initializer tail := by
  obtain ⟨declared, initializer, tail, _, interpreted, initial, rest, same⟩ :=
    elaborateTypedLetReturnTree?_binding_children (seeded ["local"] type depth (by decide) (by decide)).complete
  exact ⟨declared,initializer,tail,interpreted,initial,rest,same⟩

theorem old_named_typing_and_exact_prefix_successes_still_embed (type : Core.Ty) :
    TypedLetReturnTreeHasType (types type) owner (seed type) (bind named "local" (ref "seed") (returned "local")) type ∧
    elaborateTypedLetReturnTree? (types type) owner (seed type) (bind named "local" (ref "seed") (returned "local")) =
      some (.letE (.var 0) (.var 0),type) := by
  have old : TypedLetReturnBodyElaborates (types type) owner (seed type)
      (bind named "local" (ref "seed") (returned "local")) (.letE (.var 0) (.var 0)) type :=
    .binding (.named .head) (by change "local" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head))))
  exact ⟨old.hasType.returnTree, elaborateTypedLetReturnTree?_some_of_typedLetReturnBody old.complete⟩

private def unitBody (annotation : Syntax.TypeExpr) : Syntax.Block := bind annotation "local" unit (returned "local")
theorem unit_initializer_accepts_unit_but_not_an_arbitrary_product (table : TypeNameTable) (left right : Syntax.TypeExpr) :
    elaborateTypedLetReturnTree? table owner .empty (unitBody unitType) = some (.letE .unit (.var 0),.unit) ∧
    elaborateTypedLetReturnTree? table owner .empty (unitBody ⟨span,.tuple [left,right]⟩) = none := by
  have good : TypedLetReturnTreeElaborates table owner .empty (unitBody unitType) (.letE .unit (.var 0)) .unit :=
    .binding .unit (by simp) .unit .unit .unit (.single (.expression (.identifier .head) (.var .head) (.var .head)))
  refine ⟨good.complete, elaborateTypedLetReturnTree?_eq_none_iff.mpr ?_⟩
  rintro ⟨type, typing⟩
  cases typing with
  | single child => cases child
  | binding declared _ initializer _ => cases declared; cases initializer

private def strict : Syntax.Block := bind ⟨span,.tuple [named,unitType]⟩ "unused"
  ⟨span,.tuple ⟨span,[ref "seed",unit]⟩⟩ (returned "seed")
private def strictCore : Core.Expr := .letE (.pair (.var 0) .unit) (.var 1)
private theorem strictElab (type : Core.Ty) : TypedLetReturnTreeElaborates (types type) owner (seed type) strict strictCore type :=
  .binding (.pair (.named .head) .unit) (by change "unused" ∉ ["seed"]; decide)
    (.pair (.identifier .head) .unit) (.pair (.var .head) .unit) (.pair (.var .head) .unit)
    (.single (.expression (.identifier (.tail (by change "unused" ≠ "seed"; decide) .head))
      (.var (.tail (by change id 1 ≠ id 0; decide) .head)) (.var (.tail (by change id 1 ≠ id 0; decide) .head))))
private abbrev Actual (type : Core.Ty) := {value : Core.Value // Core.ValueHasType value type}
private def actualInputs {type : Core.Ty} (actual : Actual type) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "seed" type actual.val actual.property
private theorem strictCost {type : Core.Ty} (actual : Actual type) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (actualInputs actual).names (actualInputs actual).environment store strict actual.val store 8 := by
  apply TypedLetReturnTreeEvaluatesWithCost.binding (boundValue := .pair actual.val .unit)
    (middleStore := store) (initializerCost := 5) (tailCost := 1)
  · exact .pair (leftCost := 1) (rightCost := 1) (.identifier .head .head) .unit
  · exact .single (.expression (.identifier (.tail (by change "unused" ≠ "seed"; decide) .head)
      (.tail (by change id 1 ≠ id 0; decide) .head)))

theorem an_unused_structural_product_initializer_keeps_its_strict_eight_steps
    {type : Core.Ty} (actual : Actual type) (store : Core.Store) (continuation : List Core.Frame) :
    elaborateTypedLetReturnTree? (types type) owner (actualInputs actual).toTypeInputs strict = some (strictCore,type) ∧
    TypedLetReturnTreeEvaluatesWithCost owner (actualInputs actual).names (actualInputs actual).environment store strict actual.val store 8 ∧
    Core.Steps 8 ⟨.eval strictCore [actual.val],continuation,store⟩ ⟨.ret actual.val,continuation,store⟩ :=
  ⟨(strictElab type).complete, strictCost actual store,
    (strictCost actual store).checked_toStepsWithContinuation (strictElab type).complete rfl continuation⟩

theorem equal_result_types_do_not_identify_a_different_core (type : Core.Ty) (definitions : Core.DataEnvironment) :
    Core.HasType [type] (.var 0) type definitions ∧
    ¬ TypedLetReturnTreeElaborates (types type) owner (seed type) strict (.var 0) type := by
  refine ⟨.var rfl, ?_⟩
  intro wrong
  cases (wrong.result_unique (strictElab type)).1

theorem nominal_nested_static_types_do_not_supply_actual_inputs (nominal : Core.DataTypeId) (depth : Nat) :
    elaborateTypedLetReturnTree? (types (.namedData nominal)) owner (seed (nested (.namedData nominal) depth))
      (tree (shape depth) ["local"] "seed") = some (core 1,nested (.namedData nominal) depth) ∧
    ¬ ∃ value, Core.ValueHasType value (nested (.namedData nominal) depth) := by
  refine ⟨(seeded ["local"] _ depth (by decide) (by decide)).complete, ?_⟩
  induction depth with
  | zero =>
      rintro ⟨value, typed⟩
      cases typed with
      | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  | succ depth ih => rintro ⟨value, typed⟩; cases typed with | pair _ right => exact ih ⟨_,right⟩

theorem opaque_cells_and_captured_closures_are_returned_without_unpacking (location : Core.Location) (word : Core.Word) (store : Core.Store) :
    Core.Steps 8 (Core.State.initial strictCore [.cellRef .word location] store) (Core.State.final (.cellRef .word location) store) ∧
    Core.Steps 8 (Core.State.initial strictCore [.closure .word .word (.var 1) [.word word]] store)
      (Core.State.final (.closure .word .word (.var 1) [.word word]) store) :=
  ⟨(an_unused_structural_product_initializer_keeps_its_strict_eight_steps ⟨_,.cellRef⟩ store []).2.2,
    (an_unused_structural_product_initializer_keeps_its_strict_eight_steps ⟨_,.closure (.cons .word .nil) (.var rfl)⟩ store []).2.2⟩

theorem semantic_extension_and_owner_relabeling_retain_the_original_tree
    (type : Core.Ty) (depth : Nat) (next : TypeNameTable) (extension : TypeNameTable.Extends (types type) next)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    elaborateTypedLetReturnTree? next owner (seed (nested type depth)) (tree (shape depth) ["local"] "seed") =
      some (core 1,nested type depth) ∧
    elaborateTypedLetReturnTree? (types type) (mapping owner)
      ((seed (nested type depth)).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
      (tree (shape depth) ["local"] "seed") = some (core 1,nested type depth) :=
  ⟨((seeded ["local"] type depth (by decide) (by decide)).extend_types extension).complete,
    ((seeded ["local"] type depth (by decide) (by decide)).mapOwner mapping injective).complete⟩

end Tests.FrontendStructuralLet
