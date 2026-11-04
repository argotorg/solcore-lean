import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.TypedLetReturnBody
import Solcore.Frontend.RuntimeFunction
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RuntimeParameterDeclarations

/-!
# Typed let tree owner tests

Owners of typed let return trees.
-/

section
-- leanmerge: from Solcore.Test.FrontendTypedLetReturnTreeOwnerProperties
/-! Independent recursive provenance keeps both sibling scopes local. Owner
transport changes identities, not syntax, positional Core, actual values or
same-store checkpoints; static nominal types supply no runtime inhabitants. -/
set_option autoImplicit false
namespace Tests.FrontendTypedLetReturnTreeOwner
open Solcore Solcore.Frontend

private def owner (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeOwners", by decide⟩], by decide⟩⟩, index⟩
private def id (declaration index : Nat) : Resolved.LocalId := ⟨owner declaration, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "tree-owners.sol"⟩, 17, 8⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def binding (name : String) (value : Syntax.Expr) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some value)⟩ :: tail.value⟩
private def branch (guard : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen guard yes (some no)⟩]⟩
private def zero : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span, .binary zero ⟨span, .equal⟩ zero⟩
private def guardCore : Core.Expr := .binary .wordEq (.word .zero) (.word .zero)
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => branch guard (binding name (ref previous) (tree rest name)) (binding name (ref previous) (returned name))
private def treeCore : Nat → Core.Expr
  | 0 => .var 0
  | count + 1 => .ifE guardCore (.letE (.var 0) (treeCore count)) (.letE (.var 0) (.var 0))
private def initial (type : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"seed", id 0 7, type⟩, ⟨"side", id 1 199, .word⟩, ⟨"old", id 0 2, .bool⟩], by change [id 0 7, id 1 199, id 0 2].Nodup; decide⟩
private def mapped (inputs : LocalTypeInputs) (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) := inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)
private def shift (declaration : Resolved.DeclarationId) : Resolved.DeclarationId := { declaration with declarationIndex := declaration.declarationIndex + 5 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private theorem treeElaborated (names : List String) (previous : String) (type : Core.Ty)
    (inputs : LocalTypeInputs) (resolved : Resolved.Expr)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ inputs.names.map Prod.fst)
    (resolution : ResolvesLocalExpression inputs.names (ref previous) resolved)
    (lowered : Resolved.Lowers inputs.ids resolved (.var 0)) (typing : Resolved.HasType inputs.context resolved type) :
    TypedLetReturnTreeElaborates (types type) (owner 0) inputs (tree names previous) (treeCore names.length) type := by
  induction names generalizing previous inputs resolved with
  | nil =>
      simp only [tree, List.length_nil, treeCore]
      exact .single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing)
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      simp only [tree, List.length_cons, treeCore, branch, binding]
      apply TypedLetReturnTreeElaborates.conditional (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning))
        (.binary .word .word) (.binary .word .word)
      · apply TypedLetReturnTreeElaborates.binding (name := ⟨span, name⟩) (annotation := annotation)
          (.named .head) (fresh name (by simp)) resolution lowered typing
        have sourceSpan : (⟨span, (tree rest name).value⟩ : Syntax.Block) = tree rest name := by cases rest <;> rfl
        rw [sourceSpan]
        apply ih name (inputs.bindFresh (owner 0) name type) _ parts.2
        · intro next member
          simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
          exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
        · exact .identifier .head
        · exact .var .head
        · exact .var .head
      · exact .binding (.named .head) (fresh name (by simp)) resolution lowered typing
          (.single (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem seedTree (names : List String) (type : Core.Ty) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "old"]) :
    TypedLetReturnTreeElaborates (types type) (owner 0) (initial type) (tree names "seed") (treeCore names.length) type :=
  treeElaborated names "seed" type (initial type) _ distinct fresh (.identifier .head) (.var .head) (.var .head)

theorem arbitrary_depth_both_arm_provenance_and_typing_keep_the_original_core
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "old"])
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    TypedLetReturnTreeElaborates (types type) (mapping (owner 0)) (mapped (initial type) mapping injective)
      (tree names "seed") (treeCore names.length) type ∧
    TypedLetReturnTreeHasType (types type) (mapping (owner 0)) (mapped (initial type) mapping injective) (tree names "seed") type ∧
    elaborateTypedLetReturnTree? (types type) (mapping (owner 0)) (mapped (initial type) mapping injective) (tree names "seed") =
      some (treeCore names.length, type) :=
  ⟨(seedTree names type distinct fresh).mapOwner mapping injective, (seedTree names type distinct fresh).hasType.mapOwner mapping injective,
    (elaborateTypedLetReturnTree?_mapOwner mapping injective (types type) (owner 0) (initial type) _).trans (seedTree names type distinct fresh).complete⟩

theorem nonsurjective_owner_maps_transport_nominal_types_without_creating_values
    (names : List String) (nominal : Core.DataTypeId) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "old"]) :
    ¬ Function.Surjective shift ∧
    elaborateTypedLetReturnTree? (types (.namedData nominal)) (owner 5) (mapped (initial (.namedData nominal)) shift shiftInjective)
      (tree names "seed") = some (treeCore names.length, .namedData nominal) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨?_, (arbitrary_depth_both_arm_provenance_and_typing_keep_the_original_core names _ distinct fresh shift shiftInjective).2.2, ?_⟩
  · intro onto
    obtain ⟨preimage, same⟩ := onto (owner 0)
    have indices := congrArg Resolved.DeclarationId.declarationIndex same
    change preimage.declarationIndex + 5 = 0 at indices
    omega
  · rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem mixed_sparse_indices_and_scope_local_sibling_fresh_ids_are_not_row_counts (type : Core.Ty) :
    Resolved.freshLocalId (owner 0) (initial type).ids = id 0 8 ∧
    Resolved.freshLocalId (owner 5) (mapped (initial type) shift shiftInjective).ids = id 5 8 ∧
    ((mapped (initial type) shift shiftInjective).bindFresh (owner 5) "x" type).ids = [id 5 8, id 5 7, id 6 199, id 5 2] ∧
    ((mapped (initial type) shift shiftInjective).bindFresh (owner 5) "x" type).ids =
      ((mapped (initial type) shift shiftInjective).bindFresh (owner 5) "other" .bool).ids ∧
    (mapped (initial type) shift shiftInjective).names.map Prod.fst = ["seed", "side", "old"] ∧
    (mapped (initial type) shift shiftInjective).context.values = [type, .word, .bool] ∧
    (mapped (initial type) shift shiftInjective).ids ≠ (initial type).ids := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro same
  have head := congrArg (fun ids => ids.head?.map (·.owner.declarationIndex)) same
  cases head

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def inputs {type : Core.Ty} (actual : Actual type) (side : Core.Word) (old : Bool) : LocalInputs :=
  ⟨[⟨"seed", id 0 7, type, actual.val, actual.property⟩, ⟨"side", id 1 199, .word, .word side, .word⟩,
    ⟨"old", id 0 2, .bool, .bool old, .bool⟩], by change [id 0 7, id 1 199, id 0 2].Nodup; decide⟩
private def relabeled (inputs : LocalInputs) := inputs.mapIds (ownerLocalIdMap shift) (ownerLocalIdMap_injective shift shiftInjective)
theorem actual_values_and_whole_optional_results_are_identical_at_every_fuel_and_store
    {type : Core.Ty} (actual : Actual type) (side : Core.Word) (old : Bool) (body : Syntax.Block) (fuel : Nat) (store : Core.Store) :
    (relabeled (inputs actual side old)).environment.values = [actual.val, .word side, .bool old] ∧
    (relabeled (inputs actual side old)).environment.ids = [id 5 7, id 6 199, id 5 2] ∧
    (relabeled (inputs actual side old)).checkTypedLetReturnTree? (types type) (owner 5) body =
      (inputs actual side old).checkTypedLetReturnTree? (types type) (owner 0) body ∧
    (relabeled (inputs actual side old)).runTypedLetReturnTree? (types type) (owner 5) fuel body store =
      (inputs actual side old).runTypedLetReturnTree? (types type) (owner 0) fuel body store :=
  ⟨rfl, rfl, (inputs actual side old).checkTypedLetReturnTree?_mapOwner shift shiftInjective (types type) (owner 0) body,
    (inputs actual side old).runTypedLetReturnTree?_mapOwner shift shiftInjective (types type) (owner 0) fuel body store⟩

private def subtract (left right : String) : Syntax.Expr := ⟨span, .binary (ref left) ⟨span, .subtract⟩ (ref right)⟩
private def inside := branch (ref "old") (binding "w" (ref "z") (returned "w")) (binding "w" (ref "side") (returned "w"))
private def ordered := branch (ref "old") (binding "z" (subtract "seed" "side") inside) (binding "z" (subtract "side" "seed") (returned "z"))
private def insideCore : Core.Expr := .ifE (.var 3) (.letE (.var 0) (.var 0)) (.letE (.var 2) (.var 0))
private def orderedCore : Core.Expr := .ifE (.var 2) (.letE (.binary .wordSub (.var 0) (.var 1)) insideCore)
  (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0))
private theorem orderedElab : TypedLetReturnTreeElaborates (types .word) (owner 0) (initial .word) ordered orderedCore .word :=
  .conditional (.identifier (.tail (by decide) (.tail (by decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) (.tail (by decide) .head)))
    (.binding (.named .head) (by decide) (.subtract (.identifier .head) (.identifier (.tail (by decide) .head)))
      (.binary (.var .head) (.var (.tail (by decide) .head))) (.binary (.var .head) (.var (.tail (by decide) .head)))
      (.conditional (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
        (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
        (.binding (.named .head) (by decide) (.identifier .head) (.var .head) (.var .head)
          (.single (.expression (.identifier .head) (.var .head) (.var .head))))
        (.binding (.named .head) (by decide) (.identifier (.tail (by decide) (.tail (by decide) .head)))
          (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) (.tail (by decide) .head)))
          (.single (.expression (.identifier .head) (.var .head) (.var .head))))))
    (.binding (.named .head) (by decide) (.subtract (.identifier (.tail (by decide) .head)) (.identifier .head))
      (.binary (.var (.tail (by decide) .head)) (.var .head)) (.binary (.var (.tail (by decide) .head)) (.var .head))
      (.single (.expression (.identifier .head) (.var .head) (.var .head))))
private theorem orderedRun (seed side : Core.Word) (old : Bool) (fuel : Nat) (store : Core.Store) :
    (inputs ⟨.word seed, .word⟩ side old).runTypedLetReturnTree? (types .word) (owner 0) fuel ordered store =
      some (.word, Core.runStateful fuel (.initial orderedCore [.word seed, .word side, .bool old] store)) :=
  LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨orderedCore, orderedElab.complete, rfl⟩
theorem ordered_both_arm_core_and_asymmetric_completion_are_owner_independent
    (seed side : Core.Word) (old : Bool) (store : Core.Store) :
    (relabeled (inputs ⟨.word seed, .word⟩ side old)).checkTypedLetReturnTree? (types .word) (owner 5) ordered = some (orderedCore, .word) ∧
    (relabeled (inputs ⟨.word seed, .word⟩ side old)).runTypedLetReturnTree? (types .word) (owner 5) (if old then 17 else 11) ordered store =
      some (.word, .done (.word (if old then seed.sub side else side.sub seed)) store) := by
  refine ⟨((inputs ⟨.word seed, .word⟩ side old).checkTypedLetReturnTree?_mapOwner shift shiftInjective _ _ _).trans orderedElab.complete, ?_⟩
  apply Eq.trans ((inputs ⟨.word seed, .word⟩ side old).runTypedLetReturnTree?_mapOwner shift shiftInjective (types .word) (owner 0) (if old then 17 else 11) ordered store)
  rw [orderedRun]
  cases old <;> rfl

private def ifCheckpoint (seed side : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool true), [.ifBranches (.letE (.binary .wordSub (.var 0) (.var 1)) insideCore)
    (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)) [.word seed, .word side, .bool true]], store⟩
private def initCheckpoint (seed side : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word (seed.sub side)), [.letBody insideCore [.word seed, .word side, .bool true]], store⟩
private def tailCheckpoint (seed side : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.eval (.var 0) [.word (seed.sub side), .word (seed.sub side), .word seed, .word side, .bool true], [], store⟩
theorem genuine_if_initializer_and_recursive_tail_checkpoints_keep_all_frames_and_values
    (seed side : Core.Word) (store : Core.Store) (additional : Nat) :
    (relabeled (inputs ⟨.word seed, .word⟩ side true)).runTypedLetReturnTree? (types .word) (owner 5) 2 ordered store = some (.word, .outOfFuel (ifCheckpoint seed side store)) ∧
    (relabeled (inputs ⟨.word seed, .word⟩ side true)).runTypedLetReturnTree? (types .word) (owner 5) 9 ordered store = some (.word, .outOfFuel (initCheckpoint seed side store)) ∧
    (relabeled (inputs ⟨.word seed, .word⟩ side true)).runTypedLetReturnTree? (types .word) (owner 5) 16 ordered store = some (.word, .outOfFuel (tailCheckpoint seed side store)) ∧
    Core.runStateful 7 (ifCheckpoint seed side store) = .outOfFuel (initCheckpoint seed side store) ∧
    Core.runStateful 7 (initCheckpoint seed side store) = .outOfFuel (tailCheckpoint seed side store) ∧
    Core.runStateful 1 (tailCheckpoint seed side store) = .done (.word (seed.sub side)) store ∧
    (relabeled (inputs ⟨.word seed, .word⟩ side true)).runTypedLetReturnTree? (types .word) (owner 5) (9 + additional) ordered store =
      some (.word, Core.runStateful additional (initCheckpoint seed side store)) := by
  have checkpoints (fuel : Nat) : (relabeled (inputs ⟨.word seed, .word⟩ side true)).runTypedLetReturnTree? (types .word) (owner 5) fuel ordered store =
      some (.word, Core.runStateful fuel (.initial orderedCore [.word seed, .word side, .bool true] store)) :=
    ((inputs ⟨.word seed, .word⟩ side true).runTypedLetReturnTree?_mapOwner shift shiftInjective _ _ _ _ _).trans (orderedRun seed side true fuel store)
  have genuine : (relabeled (inputs ⟨.word seed, .word⟩ side true)).runTypedLetReturnTree? (types .word) (owner 5) 9 ordered store =
      some (.word, .outOfFuel (initCheckpoint seed side store)) := checkpoints 9
  exact ⟨checkpoints 2, genuine, checkpoints 16, rfl, rfl, rfl, LocalInputs.runTypedLetReturnTree?_resume genuine additional⟩

private theorem opaqueRun {type : Core.Ty} (actual : Actual type) (side : Core.Word) (old : Bool) (store : Core.Store) :
    (relabeled (inputs actual side old)).runTypedLetReturnTree? (types type) (owner 5) 21 (tree ["x", "y"] "seed") store = some (type, .done actual.val store) :=
  ((inputs actual side old).runTypedLetReturnTree?_mapOwner shift shiftInjective _ _ _ _ _).trans
    (LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨treeCore 2, (seedTree ["x", "y"] type (by decide) (by decide)).complete, rfl⟩)
theorem recursive_opaque_values_are_reused_without_allocation_or_invocation
    (location : Core.Location) (word side : Core.Word) (old : Bool) (store : Core.Store) :
    (relabeled (inputs (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word)) side old)).runTypedLetReturnTree? (types (.cell .word)) (owner 5) 21
      (tree ["x", "y"] "seed") store = some (.cell .word, .done (.cellRef .word location) store) ∧
    (relabeled (inputs (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word)) side old)).runTypedLetReturnTree?
      (types (.function .bool .word)) (owner 5) 21 (tree ["x", "y"] "seed") store = some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨opaqueRun _ side old store, opaqueRun _ side old store⟩

private def bad := branch guard (returned "seed") (binding "x" (ref "seed") (returned "x"))
theorem an_unknown_unselected_annotation_remains_whole_none_under_a_nonsurjective_map
    {type : Core.Ty} (actual : Actual type) (side : Core.Word) (old : Bool) (fuel : Nat) (store : Core.Store) :
    elaborateTypedLetReturnTree? [] (owner 5) (mapped (initial type) shift shiftInjective) bad = none ∧
    (relabeled (inputs actual side old)).runTypedLetReturnTree? [] (owner 5) fuel bad store = none := by
  have rejected : elaborateTypedLetReturnTree? [] (owner 0) (initial type) bad = none := by
    apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
    rintro ⟨_, typing⟩
    cases typing with
    | single child => cases child
    | conditional _ _ no =>
      cases no with
      | single child => cases child
      | binding meaning _ _ _ => cases meaning with | named found => cases found
  exact ⟨(elaborateTypedLetReturnTree?_mapOwner shift shiftInjective [] (owner 0) (initial type) _).trans rejected,
    ((inputs actual side old).runTypedLetReturnTree?_mapOwner shift shiftInjective [] (owner 0) fuel bad store).trans
      (LocalInputs.runTypedLetReturnTree?_eq_none_iff.mpr rejected)⟩

private def closedBody := branch guard (binding "x" zero (returned "x")) (binding "x" zero (returned "x"))
private def declaration : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "closed"⟩, none, ⟨span, []⟩, ⟨none, none⟩, some ⟨span, ⟨span, [annotation]⟩⟩, none⟩, closedBody⟩⟩
theorem valid_recursive_bodies_compile_at_each_owner_while_old_prefixes_reject :
    RuntimeFunctionHeader (types .word) declaration.value.signature .word ∧
    RuntimeParametersDeclare (types .word) (owner 0) declaration.value.signature.parameters.elements .empty ∧
    elaborateTypedLetReturnTree? (types .word) (owner 0) .empty closedBody =
      some (.ifE guardCore (.letE (.word .zero) (.var 0)) (.letE (.word .zero) (.var 0)), .word) ∧
    elaborateTypedLetReturnBody? (types .word) (owner 0) .empty closedBody = none ∧
    elaborateTypedLetReturnBody? (types .word) (owner 5) .empty closedBody = none ∧
    compileRuntimeFunction? (types .word) (owner 0) declaration =
      some ⟨.empty, .ifE guardCore (.letE (.word .zero) (.var 0)) (.letE (.word .zero) (.var 0)), .word⟩ ∧
    compileRuntimeFunction? (types .word) (owner 5) declaration =
      some ⟨.empty, .ifE guardCore (.letE (.word .zero) (.var 0)) (.letE (.word .zero) (.var 0)), .word⟩ := by
  have accepted (declarationOwner : Resolved.DeclarationId) : TypedLetReturnTreeElaborates (types .word) declarationOwner .empty closedBody
      (.ifE guardCore (.letE (.word .zero) (.var 0)) (.letE (.word .zero) (.var 0))) .word :=
    .conditional (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)) (.binary .word .word) (.binary .word .word)
      (.binding (.named .head) (by decide) (.wordLiteral zeroMeaning) .word .word
        (.single (.expression (.identifier .head) (.var .head) (.var .head))))
      (.binding (.named .head) (by decide) (.wordLiteral zeroMeaning) .word .word
        (.single (.expression (.identifier .head) (.var .head) (.var .head))))
  have oldTree : elaborateTerminalReturnTree? LocalTypeInputs.empty.names LocalTypeInputs.empty.context closedBody = none := by
    simp [closedBody, branch, binding, elaborateTerminalReturnTree?]
  have oldPrefix (declarationOwner : Resolved.DeclarationId) : elaborateTypedLetReturnBody? (types .word) declarationOwner .empty closedBody = none := by
    simpa only [closedBody, branch, elaborateTypedLetReturnBody?] using oldTree
  have compilation (declarationOwner : Resolved.DeclarationId) : RuntimeFunctionCompiles (types .word) declarationOwner declaration
      ⟨.empty, .ifE guardCore (.letE (.word .zero) (.var 0)) (.letE (.word .zero) (.var 0)), .word⟩ :=
    ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, .nil, accepted declarationOwner⟩
  exact ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, .nil, (accepted _).complete,
    oldPrefix _, oldPrefix _, (compilation _).complete, (compilation _).complete⟩

private def collapse (_ : Resolved.DeclarationId) := owner 0
private def indexShift (identifier : Resolved.LocalId) : Resolved.LocalId := { identifier with binderIndex := identifier.binderIndex + 10 }
theorem owner_collapse_and_injective_index_shifts_do_not_commute_with_fresh_allocation :
    ¬ Function.Injective collapse ∧
    Resolved.freshLocalId (collapse (owner 0)) ([id 1 199].map (ownerLocalIdMap collapse)) = id 0 200 ∧
    ownerLocalIdMap collapse (Resolved.freshLocalId (owner 0) [id 1 199]) = id 0 0 ∧
    Resolved.freshLocalId (collapse (owner 0)) ([id 1 199].map (ownerLocalIdMap collapse)) ≠
      ownerLocalIdMap collapse (Resolved.freshLocalId (owner 0) [id 1 199]) ∧
    Function.Injective indexShift ∧
    Resolved.freshLocalId (owner 0) ([].map indexShift) ≠ indexShift (Resolved.freshLocalId (owner 0) []) := by
  refine ⟨?_, rfl, rfl, by decide, ?_, by decide⟩
  · intro injective
    have same := injective (a₁ := owner 0) (a₂ := owner 1) rfl
    cases same
  · intro left right same
    have owners := congrArg Resolved.LocalId.owner same
    have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
    cases left; cases right; cases owners; cases indices; rfl

end Tests.FrontendTypedLetReturnTreeOwner
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetReturnTreeOwner
/-! Original parsed syntax and separately supplied Core build independent
provenance. Owner covariance retains actual values and full fixed-store states;
nominal entry compilation requires no inhabitants and keeps parameter-only rows. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeOwners", by decide⟩], by decide⟩⟩, 17⟩
private def shift (id : Resolved.DeclarationId) : Resolved.DeclarationId := { id with declarationIndex := id.declarationIndex + 11 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private theorem shiftNotSurjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨original, same⟩ := onto { owner with declarationIndex := 0 }
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  change original.declarationIndex + 11 = 0 at indices
  omega
private def mapping := ownerLocalIdMap shift
private theorem mappingInjective : Function.Injective mapping := ownerLocalIdMap_injective shift shiftInjective
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["FnOpaque"], .function .word (.namedData ⟨91⟩)), (["Opaque"], .bool)]
private def stores : List Core.Store := [[.word (word 91), .cellRef .word 40],
  [.closure .bool .bool (.var 0) [], .bool true, .word Core.Word.maximum]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-tree-owners.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"function did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "incomplete or diagnosed declaration"
  return source
private def declared (source : Syntax.FunctionDecl) : IO LocalTypeInputs := do
  let some inputs := declareRuntimeParameters? types owner source.value.signature.parameters.elements
    | throw (IO.userError "original value-free parameters rejected")
  return inputs
private def actual (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO LocalInputs := do
  let static ← declared source
  match accepted : bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "actual typed arguments rejected")
  | some inputs =>
      have _ := (bindRuntimeParameters?_sound accepted).erase_values.complete
      assertTrue (decide (inputs.names = static.names ∧ inputs.context = static.context ∧
        inputs.environment.values = arguments.reverse.map (·.value))) "original parameter names/types or single argument reversal changed"
      return inputs

private structure Expression (inputs : LocalTypeInputs) (source : Syntax.Expr) (core : Core.Expr) (type : Core.Ty) where
  resolved : Resolved.Expr
  resolution : ResolvesLocalExpression inputs.names source resolved
  lowered : Resolved.Lowers inputs.ids resolved core
  typing : Resolved.HasType inputs.context resolved type
private def expression (inputs : LocalTypeInputs) (source : Syntax.Expr) (core : Core.Expr) (type : Core.Ty) :
    IO (Expression inputs source core type) := do
  match sourceAt : source, coreAt : core, typeAt : type with
  | ⟨_, .identifier name⟩, .var index, type =>
      match named : inputs.names.lookup? name.value with
      | none => throw (IO.userError "independent reference name missing")
      | some id =>
          if indexed : Resolved.LocalScope.index? inputs.ids id = some index then
            if typed : inputs.context.lookup? id = some type then
              return ⟨.var id, by rw [sourceAt]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
                by rw [coreAt]; exact .var (Resolved.LocalScope.index?_iff.mp indexed),
                by rw [typeAt]; exact .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
            else throw (IO.userError "independent reference type differs")
          else throw (IO.userError "independent reference position differs")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩, .binary .wordSub first second, .word =>
      let l ← expression inputs left first .word
      let r ← expression inputs right second .word
      return ⟨.binary .wordSub l.resolved r.resolved, by rw [sourceAt]; exact .subtract l.resolution r.resolution,
        by rw [coreAt]; exact .binary l.lowered r.lowered,
        by rw [typeAt]; exact .binary l.typing r.typing⟩
  | _, _, _ => throw (IO.userError "expression differs from independent fixture Core")
termination_by sizeOf source
private structure Evidence (inputs : LocalTypeInputs) (body : Syntax.Block) (core : Core.Expr) (type : Core.Ty) : Type where
  elaboration : TypedLetReturnTreeElaborates types owner inputs body core type
private def certify (inputs : LocalTypeInputs) (body : Syntax.Block) (core : Core.Expr) (type : Core.Ty)
    (nextIndex : Nat) : IO (Evidence inputs body core type) := do
  match sourceAt : body, coreAt : core, typeAt : type with
  | ⟨_, [⟨_, .returnStmt none⟩]⟩, .unit, .unit => return ⟨by rw [sourceAt, coreAt, typeAt]; exact .single .bare⟩
  | ⟨_, [⟨_, .returnStmt (some source)⟩]⟩, core, type =>
      let child ← expression inputs source core type
      return ⟨by rw [sourceAt, coreAt, typeAt]; exact .single (.expression child.resolution
        (by simpa only [LocalTypeInputs.context_ids] using child.lowered) child.typing)⟩
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩, .letE initial tail, type =>
      match meaning : interpretTypeName? types annotation with
      | none => throw (IO.userError "written annotation has no meaning")
      | some declaredType =>
          if unused : name.value ∉ inputs.names.map Prod.fst then
            let child ← expression inputs initializer initial declaredType
            let extended := inputs.bindFresh owner name.value declaredType
            let mapped := inputs.mapIds mapping mappingInjective
            have _ := inputs.bindFresh_mapOwner owner shift shiftInjective name.value declaredType
            assertTrue (decide (extended.ids = (⟨owner, nextIndex⟩ : Resolved.LocalId) :: inputs.ids ∧
              (mapped.bindFresh (shift owner) name.value declaredType).ids =
                (⟨shift owner, nextIndex⟩ : Resolved.LocalId) :: mapped.ids)) "fresh index used length or a sibling allocation"
            let childTail ← certify extended ⟨blockSpan, rest⟩ tail type (nextIndex + 1)
            return ⟨by
              rw [sourceAt, coreAt, typeAt]
              exact .binding (interpretTypeName?_sound meaning).structural unused
                child.resolution child.lowered child.typing childTail.elaboration⟩
          else throw (IO.userError "independent binding reused a name")
  | ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩, .letE initial tail, type =>
      let .identifier originalName := initializer.value | throw (IO.userError "inferred fixture expected original reference")
      let some inferredType := (inputs.names.lookup? originalName.value).bind inputs.context.lookup?
        | throw (IO.userError "original reference type missing")
      if unused : name.value ∉ inputs.names.map Prod.fst then
        let child ← expression inputs initializer initial inferredType
        let extended := inputs.bindFresh owner name.value inferredType
        assertTrue (blockSpan.contains letSpan && letSpan.contains name.span && letSpan.contains initializer.span &&
          decide (name.span.endByte ≤ initializer.span.startByte ∧ extended.context = (⟨owner, nextIndex⟩, inferredType) :: inputs.context) &&
          (elaborateTypedLetReturnBody? types owner inputs body).isNone) "inferred annotation/span/fresh type or old prefix changed"
        let childTail ← certify extended ⟨blockSpan, rest⟩ tail type (nextIndex + 1)
        return ⟨by rw [sourceAt, coreAt, typeAt]; exact .inferred unused child.resolution child.lowered child.typing childTail.elaboration⟩
      else throw (IO.userError "independent inference reused a name")
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩, .ifE guard first second, type =>
      let child ← expression inputs condition guard .bool
      let l ← certify inputs left first type nextIndex
      let r ← certify inputs right second type nextIndex
      return ⟨by rw [sourceAt, coreAt, typeAt]; exact .conditional child.resolution child.lowered child.typing l.elaboration r.elaboration⟩
  | _, _, _ => throw (IO.userError "original tree differs from independent fixture Core")
termination_by sizeOf body
private def checkedStatic (inputs : LocalTypeInputs) (body : Syntax.Block) (core : Core.Expr) (type : Core.Ty)
    (nextIndex : Nat) : IO Unit := do
  let proof ← certify inputs body core type nextIndex
  have _ := proof.elaboration.mapOwner shift shiftInjective
  have _ := proof.elaboration.hasType.mapOwner shift shiftInjective
  have _ := elaborateTypedLetReturnTree?_mapOwner shift shiftInjective types owner inputs body
  let mapped := inputs.mapIds mapping mappingInjective
  assertTrue (decide (elaborateTypedLetReturnTree? types owner inputs body = some (core, type) ∧
    elaborateTypedLetReturnTree? types (shift owner) mapped body = some (core, type) ∧ Core.infer? inputs.context.values core = some type ∧
    mapped.names.map Prod.fst = inputs.names.map Prod.fst ∧ mapped.context.values = inputs.context.values ∧
    mapped.ids = inputs.ids.map mapping ∧ mapped.ids.map (·.binderIndex) = inputs.ids.map (·.binderIndex))) "static owner change altered exact source/Core/rows"
private def runChecked (inputs : LocalInputs) (body : Syntax.Block) (core : Core.Expr) (type : Core.Ty)
    (value : Core.Value) (cost bound nextIndex : Nat) : IO Unit := do
  checkedStatic inputs.toTypeInputs body core type nextIndex
  let mapped := inputs.mapIds mapping mappingInjective
  have _ := inputs.checkTypedLetReturnTree?_mapOwner shift shiftInjective types owner body
  assertTrue (decide (mapped.environment.values = inputs.environment.values ∧ mapped.ids ≠ inputs.ids ∧
    mapped.checkTypedLetReturnTree? types (shift owner) body = some (core, type) ∧ typedLetReturnTreeFuelBound body = bound)) "actual values or bound changed"
  for store in stores do
    let run := fun fuel => inputs.runTypedLetReturnTree? types owner fuel body store
    let renamed := fun fuel => mapped.runTypedLetReturnTree? types (shift owner) fuel body store
    for fuel in List.range (bound + 3) do
      have _ := inputs.runTypedLetReturnTree?_mapOwner shift shiftInjective types owner fuel body store
      assertTrue (decide (renamed fuel = run fuel ∧ run fuel = some (type, Core.runStateful fuel (.initial core inputs.environment.values store))))
        "full same-fuel owner result changed the independent Core or actual positional values"
      if cost ≤ fuel then assertTrue (decide (run fuel = some (type, .done value store))) "independent value/cost changed"
      else
        match original : run fuel, shifted : renamed fuel with
        | some (t, .outOfFuel state), some (u, .outOfFuel shiftedState) =>
            assertTrue (decide (t = type ∧ u = type ∧ state = shiftedState ∧ state.store = store)) "genuine checkpoint differed"
            for remaining in List.range (cost - fuel + 3) do
              have _ := LocalInputs.runTypedLetReturnTree?_resume original remaining
              have _ := LocalInputs.runTypedLetReturnTree?_resume shifted remaining
              assertTrue (decide (run (fuel + remaining) = some (type, Core.runStateful remaining state) ∧
                renamed (fuel + remaining) = some (type, Core.runStateful remaining shiftedState))) "resumption rebuilt values or frames"
            assertTrue (decide (Core.runStateful (cost - fuel) state = .done value store)) "actual residual lost expected value"
            if 0 < fuel then assertTrue (decide (run (cost - fuel) ≠ some (type, .done value store))) "restart became checkpoint resumption"
        | _, _ => throw (IO.userError "actual below-cost checkpoint missing")
private def alternating (depth level : Nat) (annotation : String) : String × Core.Expr :=
  match depth with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 2 else 0))
  | count + 1 =>
      let (tail, core) := alternating count (level + 1) annotation
      ("if(c){" ++ s!"let z{level}: {annotation}=" ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail ++
        "}else{" ++ s!"let z{level}: {annotation}=y;return z{level};" ++ "}",
        .ifE (.var level) (.letE (.var (if level = 0 then 2 else 0)) core) (.letE (.var (level + 1)) (.var 0)))
private def fixture (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (expected : TypedRuntimeArgument) (cost bound : Nat) : IO Unit := do
  let source ← parsed content
  let inputs ← actual source arguments
  assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some expected.type) &&
    (elaborateTypedLetReturnBody? types owner inputs.toTypeInputs source.value.body).isNone) "header or old prefix boundary changed"
  for chosenOwner in [owner, shift owner] do
    let names := if chosenOwner = owner then inputs.names else (inputs.mapIds mapping mappingInjective).names
    assertTrue (decide ((compileRuntimeFunction? types chosenOwner source).map (fun c => (c.core, c.returnType, c.inputs.names, c.inputs.context.values)) =
      some (core, expected.type, names, inputs.context.values)) && (prepareRuntimeFunction? types chosenOwner source arguments).any (fun p =>
        decide (p.core = core ∧ p.returnType = expected.type ∧ p.inputs.names = names ∧ p.inputs.context.values = inputs.context.values ∧
          p.inputs.environment.values = arguments.reverse.map (·.value)))) "owner changed exact compilation or actual parameter rows"
    for store in stores do
      for fuel in List.range (bound + 3) do
        assertTrue (decide (runRuntimeFunction? types chosenOwner source arguments fuel store =
          some (expected.type, Core.runStateful fuel (.initial core inputs.environment.values store)))) "owner changed the full entry result or checkpoint"
  runChecked inputs source.value.body core expected.type expected.value cost bound arguments.length

def frontendParsedTypedLetReturnTreeOwnerTests : IO Unit := do
  have _ := shiftNotSurjective
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (annotation, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩), ("FnOpaque", .function .word (.namedData ⟨91⟩))] do
    for depth in [1, 2, 5, 12] do
      let (body, core) := alternating depth 0 annotation
      let source ← parsed (s!"function nominal(x: {annotation},y: {annotation},c: Bool) returns ({annotation})" ++ "{" ++ body ++ "}")
      let inputs ← declared source
      checkedStatic inputs source.value.body core type 3
      for chosenOwner in [owner, shift owner] do
        let names := if chosenOwner = owner then inputs.names else (inputs.mapIds mapping mappingInjective).names
        assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some type ∧
          (compileRuntimeFunction? types chosenOwner source).map (fun c => (c.core, c.returnType, c.inputs.names, c.inputs.context.values)) =
            some (core, type, names, inputs.context.values))) "nominal owner compilation changed exact Core or demanded an inhabitant"
  let left : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  let right : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  for (annotation, x, y) in [("Word", wordArg 9, wordArg 2), ("Cell", ⟨.cell .word, .cellRef .word 17, .cellRef⟩, ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
      ("Fn", left, right), ("Bool", boolArg false, boolArg true)] do
    for depth in [1, 2, 5] do
      let (body, core) := alternating depth 0 annotation
      for c in [false, true] do
        fixture (s!"function recursive(x: {annotation},y: {annotation},c: Bool) returns ({annotation})" ++ "{" ++ body ++ "}")
          [x, y, boolArg c] core (if c then x else y) (if c then 6 * depth + 1 else 7) (6 * depth + 1)
  for (x, y) in [(9, 2), (2, 9), (0, Core.Word.maximum.val)] do
    for c in [false, true] do
      for d in [false, true] do
        fixture "function ordered(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x - y;if(d){let w: Word=z;return w;}else{let w: Word=y - z;return w;}}else{let z: Word=y - x;return y;}}"
          [boolArg c, boolArg d, wordArg x, wordArg y] (.ifE (.var 3)
            (.letE (.binary .wordSub (.var 1) (.var 0)) (.ifE (.var 3) (.letE (.var 0) (.var 0))
              (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 1)))
          ⟨.word, .word (if c then if d then (word x).sub (word y) else (word y).sub ((word x).sub (word y)) else word y), .word⟩
          (if c then if d then 17 else 21 else 11) 21
  for c in [false, true] do
    fixture "function siblings(x: Word,c: Bool){if(c){let z: Word=x;return;}else{let z: Bool=c;return;}}"
      [wordArg 9, boolArg c] (.ifE (.var 0) (.letE (.var 1) .unit) (.letE (.var 0) .unit)) ⟨.unit, .unit, .unit⟩ 7 7
  let source ← parsed "function sparse(x: Word,y: Word,c: Bool) returns (Word){if(c){let z: Word=x;return z;}else{let z: Word=y;return z;}}"
  let mixed : LocalInputs := ⟨[⟨"c", ⟨owner, 2⟩, .bool, .bool true, .bool⟩,
    ⟨"y", ⟨shift owner, 999⟩, .word, .word (word 2), .word⟩, ⟨"x", ⟨owner, 7⟩, .word, .word (word 9), .word⟩], by decide⟩
  let ordinary ← actual source [wordArg 9, wordArg 2, boolArg true]
  assertTrue (decide (mixed.names.map Prod.fst = ordinary.names.map Prod.fst ∧ mixed.context.values = ordinary.context.values ∧
    mixed.environment.values = ordinary.environment.values)) "sparse IDs changed original parsed argument positions"
  let expected := Core.Expr.ifE (.var 0) (.letE (.var 2) (.var 0)) (.letE (.var 1) (.var 0))
  runChecked mixed source.value.body expected .word (.word (word 9)) 7 7 8
  for store in stores do
    let env := mixed.environment.values
    let run := fun fuel => mixed.runTypedLetReturnTree? types owner fuel source.value.body store
    for (fuel, state) in [(1, (⟨.eval (.var 0) env, [.ifBranches (.letE (.var 2) (.var 0)) (.letE (.var 1) (.var 0)) env], store⟩ : Core.State)),
        (4, ⟨.eval (.var 2) env, [.letBody (.var 0) env], store⟩), (5, ⟨.ret (.word (word 9)), [.letBody (.var 0) env], store⟩),
        (6, ⟨.eval (.var 0) (.word (word 9) :: env), [], store⟩)] do
      assertTrue (decide (run fuel = some (.word, .outOfFuel state))) "independent if/initializer/captured-value/tail checkpoint changed"
  let rawIds := mixed.ids ++ [⟨owner, 7⟩]
  have _ := Resolved.freshLocalId_map_owner shift shiftInjective owner rawIds
  let indexShift := fun id : Resolved.LocalId => { id with binderIndex := id.binderIndex + 1 }
  have _ : Function.Injective indexShift := by
    intro left right same
    have owners := congrArg Resolved.LocalId.owner same
    have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
    cases left; cases right; cases owners; cases indices; rfl
  assertTrue (decide (Resolved.freshLocalId owner rawIds = ⟨owner, 8⟩ ∧
    Resolved.freshLocalId (shift owner) (rawIds.map mapping) = ⟨shift owner, 8⟩ ∧
    Resolved.freshLocalId owner (([] : List Resolved.LocalId).map indexShift) ≠ indexShift (Resolved.freshLocalId owner []) ∧
    Resolved.freshLocalId owner (rawIds.map (ownerLocalIdMap (fun _ => owner))) ≠
      ownerLocalIdMap (fun _ => owner) (Resolved.freshLocalId owner rawIds))) "inadmissible allocator mapping was silently generalized"
  for c in [false, true] do
    fixture "function rejected(x: Word,y: Word,c: Bool) returns (Word){if(c){let z=x;return z;}else{return y;}}"
      [wordArg 9, wordArg 2, boolArg c] (.ifE (.var 0) (.letE (.var 2) (.var 0)) (.var 1)) (wordArg (if c then 9 else 2)) (if c then 7 else 4) 7
  for body in ["{if(c){let z: Word=x;return z;}else{let z: Unknown=y;return z;}}",
      "{if(c){let z: Word=x;return z;}else{let z: Bool=y;return y;}}", "{if(c){let x: Word=y;return x;}else{return y;}}",
      "{if(c){let z: Word=z;return x;}else{return y;}}", "{if(c){return x;}else{return z;}}",
      "{if(c){let z: Word;return x;}else{return y;}}",
      "{if(c){let z: Word=x;return z;}else{if(c){return y;}else{return missing;}}}",
      "{if(c){return x;}else{return c;}}", "{if(x){return x;}else{return y;}}", "{if(c){return x;}}", "{return x;return y;}", "{}"] do
    let source ← parsed ("function rejected(x: Word,y: Word,c: Bool) returns (Word)" ++ body)
    let inputs ← actual source [wordArg 9, wordArg 2, boolArg true]
    let mapped := inputs.mapIds mapping mappingInjective
    have _ := elaborateTypedLetReturnTree?_mapOwner shift shiftInjective types owner inputs.toTypeInputs source.value.body
    have _ := inputs.checkTypedLetReturnTree?_mapOwner shift shiftInjective types owner source.value.body
    assertTrue ((inputs.checkTypedLetReturnTree? types owner source.value.body).isNone &&
      (mapped.checkTypedLetReturnTree? types (shift owner) source.value.body).isNone) "owner map repaired whole rejection"
    for store in stores do
      for fuel in List.range (typedLetReturnTreeFuelBound source.value.body + 3) do
        have _ := inputs.runTypedLetReturnTree?_mapOwner shift shiftInjective types owner fuel source.value.body store
        assertTrue ((inputs.runTypedLetReturnTree? types owner fuel source.value.body store).isNone &&
          (mapped.runTypedLetReturnTree? types (shift owner) fuel source.value.body store).isNone) "owner/fuel repaired rejected source"

end Tests
end
