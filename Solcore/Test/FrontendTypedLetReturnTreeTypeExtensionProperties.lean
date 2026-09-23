import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.TypedLetReturnBody

/-! Independent recursive provenance distinguishes meaning extension from row
membership. Fixed actual inputs retain every result and their real checkpoints. -/
set_option autoImplicit false
namespace Tests.FrontendTypedLetReturnTreeTypeExtension
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeTypes", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "tree-types.sol"⟩, 221, 8⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Flag"], .bool)]
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def binding (annotation : Syntax.TypeExpr) (name : String) (value : Syntax.Expr) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some value)⟩ :: tail.value⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def initial (type : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"seed", id 0, type⟩, ⟨"side", id 1, .word⟩, ⟨"c", id 2, .bool⟩], by change [id 0, id 1, id 2].Nodup; decide⟩
private def zero : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span, .binary zero ⟨span, .equal⟩ zero⟩
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree (annotation : Syntax.TypeExpr) : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => binding annotation name (ref previous) (branch guard (tree annotation rest name) (returned name))
private def treeCore : Nat → Core.Expr
  | 0 => .var 0
  | depth + 1 => .letE (.var 0) (.ifE (.binary .wordEq (.word .zero) (.word .zero)) (treeCore depth) (.var 0))
private theorem treeElab (names : List String) (previous : String) (type : Core.Ty)
    (table : TypeNameTable) (annotation : Syntax.TypeExpr) (meaning : TypeNameDenotes table annotation type)
    (inputs : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ inputs.names.map Prod.fst)
    (resolution : ResolvesLocalExpression inputs.names (ref previous) resolved)
    (lowered : Resolved.Lowers inputs.ids resolved (.var 0)) (typing : Resolved.HasType inputs.context resolved type) :
    TypedLetReturnTreeElaborates table owner inputs (tree annotation names previous) (treeCore names.length) type := by
  induction names generalizing previous inputs resolved with
  | nil =>
    simp only [tree, List.length_nil, treeCore]
    exact .single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing)
  | cons name rest ih =>
    have parts := List.nodup_cons.mp distinct
    simp only [tree, List.length_cons, treeCore, binding]
    apply TypedLetReturnTreeElaborates.binding (name := ⟨span, name⟩) meaning.structural (fresh name (by simp)) resolution lowered typing
    apply TypedLetReturnTreeElaborates.conditional (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning))
      (.binary .word .word) (.binary .word .word)
    · apply ih name (inputs.bindFresh owner name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head
    · exact .single (.expression (.identifier .head) (.var .head) (.var .head))
private theorem oneElab (type : Core.Ty) (table : TypeNameTable) (annotation : Syntax.TypeExpr)
    (meaning : TypeNameDenotes table annotation type) :
    TypedLetReturnTreeElaborates table owner (initial type) (tree annotation ["z"] "seed") (treeCore 1) type :=
  treeElab ["z"] "seed" type table annotation meaning (initial type) _ (by decide)
    (by change ∀ name ∈ ["z"], name ∉ ["seed", "side", "c"]; decide) (.identifier .head) (.var .head) (.var .head)

theorem arbitrary_fresh_depth_preserves_independent_provenance_and_whole_typing
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "c"])
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types type) next) :
    TypedLetReturnTreeElaborates next owner (initial type) (tree (named "Payload") names "seed") (treeCore names.length) type ∧
    TypedLetReturnTreeHasType next owner (initial type) (tree (named "Payload") names "seed") type ∧
    elaborateTypedLetReturnTree? next owner (initial type) (tree (named "Payload") names "seed") = some (treeCore names.length, type) := by
  have original := treeElab names "seed" type (types type) (named "Payload") (.named .head) (initial type) _ distinct fresh
    (.identifier .head) (.var .head) (.var .head)
  exact ⟨original.extend_types extension, original.hasType.extend_types extension,
    elaborateTypedLetReturnTree?_some_of_extends extension original.complete⟩

theorem nominal_static_success_does_not_create_an_actual_inhabitant
    (names : List String) (nominal : Core.DataTypeId) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "c"]) (extras : TypeNameTable) :
    elaborateTypedLetReturnTree? (types (.namedData nominal) ++ extras) owner (initial (.namedData nominal))
      (tree (named "Payload") names "seed") = some (treeCore names.length, .namedData nominal) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(arbitrary_fresh_depth_preserves_independent_provenance_and_whole_typing names _ distinct fresh _ (TypeNameTable.Extends.append_right _ extras)).2.2, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private theorem cR (type : Core.Ty) : ResolvesLocalExpression (initial type).names (ref "c") (.var (id 2)) :=
  .identifier (.tail (by change "seed" ≠ "c"; decide) (.tail (by decide) .head))
private theorem cL (type : Core.Ty) : Resolved.Lowers (initial type).ids (.var (id 2)) (.var 2) := .var (.tail (by change id 0 ≠ id 2; decide) (.tail (by decide) .head))
private theorem cT (type : Core.Ty) : Resolved.HasType (initial type).context (.var (id 2)) .bool := .var (.tail (by change id 0 ≠ id 2; decide) (.tail (by decide) .head))
private def sub : Syntax.Expr := ⟨span, .binary (ref "seed") ⟨span, .subtract⟩ (ref "side")⟩
private def body := branch (ref "c") (binding (named "Payload") "z" sub (returned "z")) (binding (named "Flag") "z" (ref "c") (returned "side"))
private def core : Core.Expr := .ifE (.var 2) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0)) (.letE (.var 2) (.var 2))
private theorem bodyElab : TypedLetReturnTreeElaborates (types .word) owner (initial .word) body core .word :=
  .conditional (cR _) (cL _) (cT _)
    (.binding (.named .head) (by decide) (.subtract (.identifier .head) (.identifier (.tail (by decide) .head)))
      (.binary (.var .head) (.var (.tail (by decide) .head))) (.binary (.var .head) (.var (.tail (by decide) .head)))
      (.single (.expression (.identifier .head) (.var .head) (.var .head))))
    (.binding (.named (.tail (by decide) .head)) (by decide) (cR _) (cL _) (cT _)
      (.single (.expression (.identifier (.tail (by decide) (.tail (by decide) .head)))
        (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) (.tail (by decide) .head))))))

theorem different_annotation_meanings_share_a_scope_local_id_without_changing_order (extras : TypeNameTable) :
    (initial .word |>.bindFresh owner "z" .word).ids = id 3 :: (initial .word).ids ∧
    (initial .word |>.bindFresh owner "z" .bool).ids = (initial .word |>.bindFresh owner "z" .word).ids ∧
    TypedLetReturnTreeElaborates (types .word ++ extras) owner (initial .word) body core .word :=
  ⟨rfl, rfl, bodyElab.extend_types (TypeNameTable.Extends.append_right _ extras)⟩

private def hidden (type later : Core.Ty) : TypeNameTable := types type ++ [(["Payload"], later)]
private theorem hiddenExtends (type first second : Core.Ty) : TypeNameTable.Extends (hidden type first) (hidden type second) := by
  intro key result found
  cases found with
  | head => exact .head
  | tail different rest =>
    cases rest with
    | head => exact .tail different .head
    | tail other rest =>
      cases rest with
      | head => exact False.elim (different rfl)
      | tail _ absent => cases absent
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def inputs {type : Core.Ty} (actual : Actual type) (side : Core.Word) (choice : Bool) : LocalInputs :=
  ⟨[⟨"seed", id 0, type, actual.val, actual.property⟩, ⟨"side", id 1, .word, .word side, .word⟩,
    ⟨"c", id 2, .bool, .bool choice, .bool⟩], by change [id 0, id 1, id 2].Nodup; decide⟩

theorem unequal_nonunique_tables_preserve_full_options_including_rejection
    {type : Core.Ty} (actual : Actual type) (side : Core.Word) (choice : Bool) (source : Syntax.Block) (fuel : Nat) (store : Core.Store) :
    hidden type .word ≠ hidden type .bool ∧ ¬ ((hidden type .word).map Prod.fst).Nodup ∧
    (inputs actual side choice).runTypedLetReturnTree? (hidden type .word) owner fuel ⟨span, []⟩ store = none ∧
    (inputs actual side choice).runTypedLetReturnTree? (hidden type .bool) owner fuel ⟨span, []⟩ store = none ∧
    elaborateTypedLetReturnTree? (hidden type .word) owner (initial type) source = elaborateTypedLetReturnTree? (hidden type .bool) owner (initial type) source ∧
    (inputs actual side choice).checkTypedLetReturnTree? (hidden type .word) owner source = (inputs actual side choice).checkTypedLetReturnTree? (hidden type .bool) owner source ∧
    (inputs actual side choice).runTypedLetReturnTree? (hidden type .word) owner fuel source store = (inputs actual side choice).runTypedLetReturnTree? (hidden type .bool) owner fuel source store := by
  refine ⟨?_, by change ¬ ([ ["Payload"], ["Flag"], ["Payload"] ]).Nodup; decide,
    by simp [LocalInputs.runTypedLetReturnTree?, LocalInputs.checkTypedLetReturnTree?, elaborateTypedLetReturnTree?],
    by simp [LocalInputs.runTypedLetReturnTree?, LocalInputs.checkTypedLetReturnTree?, elaborateTypedLetReturnTree?],
    elaborateTypedLetReturnTree?_eq_of_mutual_extends (hiddenExtends type .word .bool) (hiddenExtends type .bool .word) owner _ source,
    (inputs actual side choice).checkTypedLetReturnTree?_eq_of_mutual_extends (hiddenExtends type .word .bool) (hiddenExtends type .bool .word) owner source,
    (inputs actual side choice).runTypedLetReturnTree?_eq_of_mutual_extends (hiddenExtends type .word .bool) (hiddenExtends type .bool .word) owner fuel source store⟩
  intro same
  have later := congrArg (fun table => table[2]?) same
  cases later

private theorem runExact (seed side : Core.Word) (choice : Bool) (store : Core.Store) (fuel : Nat) :
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnTree? (types .word) owner fuel body store =
      some (.word, Core.runStateful fuel (Core.State.initial core [.word seed, .word side, .bool choice] store)) :=
  LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, bodyElab.complete, rfl⟩
theorem one_way_extension_preserves_the_whole_successful_pair_at_every_fuel
    (seed side : Core.Word) (choice : Bool) (store : Core.Store) (fuel : Nat) (next : TypeNameTable) (extension : TypeNameTable.Extends (types .word) next) :
    (inputs ⟨.word seed, .word⟩ side choice).checkTypedLetReturnTree? next owner body = some (core, .word) ∧
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnTree? next owner fuel body store =
      some (.word, Core.runStateful fuel (Core.State.initial core [.word seed, .word side, .bool choice] store)) :=
  ⟨LocalInputs.checkTypedLetReturnTree?_some_of_extends (inputs := inputs ⟨.word seed, .word⟩ side choice) extension bodyElab.complete,
    LocalInputs.runTypedLetReturnTree?_some_of_extends extension (runExact seed side choice store fuel)⟩

private theorem bodyCost (seed side : Core.Word) (choice : Bool) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (initial .word).names
      [(id 0, .word seed), (id 1, .word side), (id 2, .bool choice)] store body
      (.word (if choice then seed.sub side else side)) store (if choice then 11 else 7) := by
  have c : LocalExpressionEvaluatesWithCost (initial .word).names
      [(id 0, .word seed), (id 1, .word side), (id 2, .bool choice)] store (ref "c") (.bool choice) store 1 :=
    .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
  cases choice
  · apply TypedLetReturnTreeEvaluatesWithCost.ifFalse (branchCost := 4) c
    apply TypedLetReturnTreeEvaluatesWithCost.binding (tailCost := 1) c
    exact .single (.expression (.identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))))
  · apply TypedLetReturnTreeEvaluatesWithCost.ifTrue (branchCost := 8) c
    apply TypedLetReturnTreeEvaluatesWithCost.binding (boundValue := .word (seed.sub side)) (initializerCost := 5) (tailCost := 1)
    · exact .subtract (left := ref "seed") (right := ref "side") (leftValue := seed) (rightValue := side)
        (.identifier .head .head) (.identifier (.tail (by decide) .head) (.tail (by decide) .head))
    · exact .single (.expression (.identifier .head .head))
theorem unused_initialization_keeps_independent_asymmetric_thresholds_under_extension
    (seed side : Core.Word) (choice : Bool) (store : Core.Store) (fuel : Nat)
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types .word) next) :
    TypedLetReturnTreeEvaluatesWithCost owner (initial .word).names
      [(id 0, .word seed), (id 1, .word side), (id 2, .bool choice)] store body
      (.word (if choice then seed.sub side else side)) store (if choice then 11 else 7) ∧
    ((inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnTree? next owner fuel body store =
      some (.word, .done (.word (if choice then seed.sub side else side)) store) ↔ (if choice then 11 else 7) ≤ fuel) := by
  refine ⟨bodyCost seed side choice store, ?_⟩
  rw [(one_way_extension_preserves_the_whole_successful_pair_at_every_fuel seed side choice store fuel next extension).2]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  exact (bodyCost seed side choice store).checked_runStateful_done_iff bodyElab.complete rfl

private def checkpoint (seed side : Core.Word) (choice : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (if choice then .word (seed.sub side) else .bool false),
    [.letBody (if choice then .var 0 else .var 2) [.word seed, .word side, .bool choice]], store⟩
private def conditionCheckpoint (seed side : Core.Word) (choice : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0))
    (.letE (.var 2) (.var 2)) [.word seed, .word side, .bool choice]], store⟩
theorem real_initializer_checkpoints_keep_exact_cost_and_resume_in_multiple_chunks
    (seed side : Core.Word) (choice : Bool) (store : Core.Store) (additional : Nat) :
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnTree? (hidden .word .bool) owner 2 body store =
      some (.word, .outOfFuel (conditionCheckpoint seed side choice store)) ∧
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnTree? (hidden .word .bool) owner (if choice then 9 else 5) body store =
      some (.word, .outOfFuel (checkpoint seed side choice store)) ∧
    Core.runStateful 2 (conditionCheckpoint seed side choice store) =
      .outOfFuel ⟨.eval (if choice then .binary .wordSub (.var 0) (.var 1) else .var 2)
        [.word seed, .word side, .bool choice], (checkpoint seed side choice store).continuation, store⟩ ∧
    Core.runStateful (if choice then 7 else 3) (conditionCheckpoint seed side choice store) = .outOfFuel (checkpoint seed side choice store) ∧
    Core.runStateful 1 (checkpoint seed side choice store) = .outOfFuel ⟨.eval (if choice then .var 0 else .var 2)
      ((if choice then .word (seed.sub side) else .bool false) :: [.word seed, .word side, .bool choice]), [], store⟩ ∧
    Core.runStateful 2 (checkpoint seed side choice store) = .done (.word (if choice then seed.sub side else side)) store ∧
    (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnTree? (hidden .word .bool) owner ((if choice then 9 else 5) + additional) body store =
      some (.word, Core.runStateful additional (checkpoint seed side choice store)) := by
  have real : (inputs ⟨.word seed, .word⟩ side choice).runTypedLetReturnTree? (types .word) owner (if choice then 9 else 5) body store =
      some (.word, .outOfFuel (checkpoint seed side choice store)) := (runExact seed side choice store _).trans (by cases choice <;> rfl)
  have mapped := LocalInputs.runTypedLetReturnTree?_some_of_extends (TypeNameTable.Extends.append_right (types .word) [(["Payload"], .bool)]) real
  refine ⟨?_, mapped, by cases choice <;> rfl, by cases choice <;> rfl, by cases choice <;> rfl,
    by cases choice <;> rfl, LocalInputs.runTypedLetReturnTree?_resume mapped additional⟩
  exact ((one_way_extension_preserves_the_whole_successful_pair_at_every_fuel seed side choice store 2 _
    (TypeNameTable.Extends.append_right _ [(["Payload"], .bool)])).2).trans (by cases choice <;> rfl)

private def repair (annotation : Syntax.TypeExpr) := branch (ref "c") (returned "seed") (binding annotation "z" (ref "seed") (returned "z"))
private def repairCore : Core.Expr := .ifE (.var 2) (.var 0) (.letE (.var 0) (.var 0))
private theorem repairElab (type : Core.Ty) (table : TypeNameTable) (annotation : Syntax.TypeExpr) (meaning : TypeNameDenotes table annotation type) :
    TypedLetReturnTreeElaborates table owner (initial type) (repair annotation) repairCore type :=
  .conditional (cR _) (cL _) (cT _) (.single (.expression (.identifier .head) (.var .head) (.var .head)))
    (.binding meaning.structural (by change "z" ∉ ["seed", "side", "c"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.single (.expression (.identifier .head) (.var .head) (.var .head))))
private theorem opaqueDone {type : Core.Ty} (actual : Actual type) (side : Core.Word) (store : Core.Store) (extras : TypeNameTable) :
    (inputs actual side false).runTypedLetReturnTree? (types type ++ extras) owner 7 (repair (named "Payload")) store = some (type, .done actual.val store) :=
  LocalInputs.runTypedLetReturnTree?_some_of_extends (TypeNameTable.Extends.append_right _ extras)
    (LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨repairCore, (repairElab type (types type) (named "Payload") (.named .head)).complete, rfl⟩)
theorem actual_opaque_cells_and_closures_remain_unchanged
    (location : Core.Location) (word side : Core.Word) (store : Core.Store) (extras : TypeNameTable) :
    (inputs (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word)) side false).runTypedLetReturnTree? (types (.cell .word) ++ extras) owner 7
      (repair (named "Payload")) store = some (.cell .word, .done (.cellRef .word location) store) ∧
    (inputs (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word)) side false).runTypedLetReturnTree?
      (types (.function .bool .word) ++ extras) owner 7 (repair (named "Payload")) store = some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨opaqueDone _ side store extras, opaqueDone _ side store extras⟩

theorem a_previously_unknown_unselected_annotation_can_repair_the_same_input_bundle
    {type : Core.Ty} (actual : Actual type) (side : Core.Word) (store : Core.Store) (fuel : Nat) :
    TypeNameTable.Extends (types type) ((["Alias"], type) :: types type) ∧
    (inputs actual side true).runTypedLetReturnTree? (types type) owner fuel (repair (named "Alias")) store = none ∧
    (inputs actual side true).runTypedLetReturnTree? ((["Alias"], type) :: types type) owner fuel (repair (named "Alias")) store =
      some (type, Core.runStateful fuel (Core.State.initial repairCore [actual.val, .word side, .bool true] store)) := by
  refine ⟨TypeNameTable.Extends.cons_fresh _ ["Alias"] type (by change ["Alias"] ∉ [["Payload"], ["Flag"]]; decide), ?_,
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨repairCore, (repairElab type _ (named "Alias") (.named .head)).complete, rfl⟩⟩
  apply LocalInputs.runTypedLetReturnTree?_eq_none_iff.mpr
  apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
  rintro ⟨_, typing⟩
  cases typing with
  | single child => cases child
  | conditional _ _ no =>
    cases no with
    | single child => cases child
    | binding meaning _ _ _ =>
      have impossible := meaning.complete
      simp [interpretStructuralType?, named, types, qualifiedTypeNameKey, TypeNameTable.lookup?, Syntax.NonemptyList.toList] at impossible

theorem keeping_every_row_does_not_allow_a_conflicting_first_meaning :
    (∀ row ∈ types .word, row ∈ ((["Payload"], Core.Ty.bool) :: types .word)) ∧
    ¬ TypeNameTable.Extends (types .word) ((["Payload"], .bool) :: types .word) ∧
    elaborateTypedLetReturnTree? (types .word) owner (initial .word) (tree (named "Payload") ["z"] "seed") = some (treeCore 1, .word) ∧
    elaborateTypedLetReturnTree? ((["Payload"], .bool) :: types .word) owner (initial .word) (tree (named "Payload") ["z"] "seed") = none := by
  refine ⟨fun row member => List.mem_cons_of_mem _ member, ?_, (oneElab .word _ (named "Payload") (.named .head)).complete, ?_⟩
  · intro extension
    have conflict := (extension (.head : TypeNameTable.Lookup (types .word) ["Payload"] .word)).type_unique (.head : TypeNameTable.Lookup _ ["Payload"] .bool)
    cases conflict
  · have seedAccepted : elaborateLocalExpression? (initial .word).names (initial .word).context (ref "seed") = some (.var 0, .word) :=
      elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
    simp [tree, binding, elaborateTypedLetReturnTree?, seedAccepted, interpretStructuralType?, named, types,
      qualifiedTypeNameKey, TypeNameTable.lookup?, Syntax.NonemptyList.toList]

private def qualified : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Pkg"⟩, [⟨span, "Token"⟩]⟩⟩⟩ none⟩
theorem qualified_components_do_not_collapse_to_a_dotted_key (type : Core.Ty) :
    TypeNameTable.Extends [(["Pkg", "Token"], type)] [(["Pkg.Token"], .bool), (["Pkg", "Token"], type)] ∧
    elaborateTypedLetReturnTree? [(["Pkg.Token"], .bool), (["Pkg", "Token"], type)] owner (initial type) (tree qualified ["z"] "seed") = some (treeCore 1, type) ∧
    elaborateTypedLetReturnTree? [(["Pkg.Token"], type)] owner (initial type) (tree qualified ["z"] "seed") = none := by
  refine ⟨TypeNameTable.Extends.cons_fresh _ ["Pkg.Token"] .bool (by change ["Pkg.Token"] ∉ [["Pkg", "Token"]]; decide),
    (oneElab type _ qualified (.named (.tail (by decide) .head))).complete, ?_⟩
  simp [tree, binding, elaborateTypedLetReturnTree?, interpretStructuralType?, qualified, qualifiedTypeNameKey, TypeNameTable.lookup?, Syntax.NonemptyList.toList]

theorem branch_local_bindings_remain_outside_the_old_prefix_adapter (table : TypeNameTable) (inputs : LocalTypeInputs) :
    elaborateTypedLetReturnBody? table owner inputs body = none := by
  cases checked : elaborateLocalExpression? inputs.names inputs.context (ref "c") with
  | none => simp [body, branch, binding, elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?, checked]
  | some pair => rcases pair with ⟨core, type⟩; simp [body, branch, binding, elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?, checked]
private def closedArm := binding (named "Payload") "z" zero (returned "z")
private def closedEntry : Syntax.FunctionDecl := ⟨span, ⟨⟨span, ⟨span, "closed"⟩, none, ⟨span, []⟩,
  ⟨none, none⟩, some ⟨span, ⟨span, [named "Payload"]⟩⟩, none⟩, branch guard closedArm closedArm⟩⟩
private def closedCore : Core.Expr := .ifE (.binary .wordEq (.word .zero) (.word .zero))
  (.letE (.word .zero) (.var 0)) (.letE (.word .zero) (.var 0))
theorem valid_recursive_entry_has_independent_header_parameters_and_exact_compilation :
    RuntimeFunctionHeader (types .word) closedEntry.value.signature .word ∧
    RuntimeParametersDeclare (types .word) owner [] .empty ∧
    RuntimeFunctionCompiles (types .word) owner closedEntry ⟨.empty, closedCore, .word⟩ ∧
    compileRuntimeFunction? (types .word) owner closedEntry = some ⟨.empty, closedCore, .word⟩ := by
  have arm : TypedLetReturnTreeElaborates (types .word) owner .empty closedArm (.letE (.word .zero) (.var 0)) .word :=
    .binding (.named .head) (by decide) (.wordLiteral zeroMeaning) .word .word
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))
  have compiled : RuntimeFunctionCompiles (types .word) owner closedEntry ⟨.empty, closedCore, .word⟩ :=
    ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, .nil,
      .conditional (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)) (.binary .word .word) (.binary .word .word) arm arm⟩
  exact ⟨compiled.header, compiled.parameters, compiled, compiled.complete⟩

end Tests.FrontendTypedLetReturnTreeTypeExtension
