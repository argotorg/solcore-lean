import Solcore.Frontend.TypedLetReturnTreeRunnerOwnerProperties
import Solcore.Frontend.TypedLetReturnTreeResumptionProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties

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
theorem valid_recursive_bodies_do_not_expand_the_existing_function_entry :
    RuntimeFunctionHeader (types .word) declaration.value.signature .word ∧
    RuntimeParametersDeclare (types .word) (owner 0) declaration.value.signature.parameters.elements .empty ∧
    elaborateTypedLetReturnTree? (types .word) (owner 0) .empty closedBody =
      some (.ifE guardCore (.letE (.word .zero) (.var 0)) (.letE (.word .zero) (.var 0)), .word) ∧
    compileRuntimeFunction? (types .word) (owner 0) declaration = none ∧ compileRuntimeFunction? (types .word) (owner 5) declaration = none := by
  have accepted : TypedLetReturnTreeElaborates (types .word) (owner 0) .empty closedBody
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
  have entryNone (declarationOwner : Resolved.DeclarationId) : compileRuntimeFunction? (types .word) declarationOwner declaration = none := by
    apply compileRuntimeFunction?_eq_none_iff.mpr
    rintro ⟨candidate, compilation⟩
    have declared : RuntimeParametersDeclare (types .word) declarationOwner declaration.value.signature.parameters.elements .empty := .nil
    have same := compilation.parameters.result_unique declared
    have bodyAccepted := compilation.body.complete
    rw [same] at bodyAccepted
    change elaborateTypedLetReturnBody? (types .word) declarationOwner .empty closedBody = some _ at bodyAccepted
    rw [oldPrefix] at bodyAccepted
    cases bodyAccepted
  exact ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, .nil, accepted.complete, entryNone _, entryNone _⟩

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
