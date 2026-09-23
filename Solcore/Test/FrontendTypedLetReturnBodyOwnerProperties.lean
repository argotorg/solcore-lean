import Solcore.Frontend.TypedLetReturnBody

/-! Owner-only covariance preserves fresh allocation and exact positional Core.
Static nominal inputs and actual runtime values remain separate boundaries. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetReturnBodyOwner

open Solcore Solcore.Frontend

private def owner (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetOwners", by decide⟩], by decide⟩⟩, index⟩
private def localId (declaration index : Nat) : Resolved.LocalId := ⟨owner declaration, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-owners.sol"⟩, 177, 8⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def binding (name : String) (value : Syntax.Expr) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some value)⟩
private def returned (value : Syntax.Expr) : Syntax.Statement := ⟨span, .returnStmt (some value)⟩
private def statements : List String → String → List Syntax.Statement
  | [], previous => [returned (ref previous)]
  | name :: rest, previous => binding name (ref previous) :: statements rest name
private def chain (names : List String) (previous : String) : Syntax.Block := ⟨span, statements names previous⟩
private def chainCore : Nat → Core.Expr
  | 0 => .var 0
  | count + 1 => .letE (.var 0) (chainCore count)
private def initial (type : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"seed", localId 0 7, type⟩, ⟨"side", localId 1 199, .word⟩, ⟨"old", localId 0 2, .bool⟩],
    by change [localId 0 7, localId 1 199, localId 0 2].Nodup; decide⟩
private def mapped (inputs : LocalTypeInputs) (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) := inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)
private theorem chainElaborated (names : List String) (previous : String) (type : Core.Ty)
    (inputs : LocalTypeInputs) (resolved : Resolved.Expr)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ inputs.names.map Prod.fst)
    (resolution : ResolvesLocalExpression inputs.names (ref previous) resolved)
    (lowered : Resolved.Lowers inputs.ids resolved (.var 0)) (typing : Resolved.HasType inputs.context resolved type) :
    TypedLetReturnBodyElaborates (types type) (owner 0) inputs (chain names previous) (chainCore names.length) type := by
  induction names generalizing previous inputs resolved with
  | nil =>
      simp only [chain, statements, List.length_nil, chainCore]
      exact .terminal (.single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing))
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      simp only [chain, statements, List.length_cons, chainCore]
      apply TypedLetReturnBodyElaborates.binding (name := ⟨span, name⟩) (annotation := annotation)
        (.named .head) (fresh name (by simp)) resolution lowered typing
      apply ih name (inputs.bindFresh (owner 0) name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head
private theorem seedChain (names : List String) (type : Core.Ty) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "old"]) :
    TypedLetReturnBodyElaborates (types type) (owner 0) (initial type) (chain names "seed") (chainCore names.length) type :=
  chainElaborated names "seed" type (initial type) _ distinct fresh (.identifier .head) (.var .head) (.var .head)
private def shift (id : Resolved.DeclarationId) : Resolved.DeclarationId := { id with declarationIndex := id.declarationIndex + 5 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl

theorem arbitrary_raw_scopes_and_value_free_extended_inputs_commute_with_owner_allocation
    (scope : List Resolved.LocalId) (inputs : LocalTypeInputs) (declaration : Resolved.DeclarationId)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) (name : String) (type : Core.Ty) :
    Resolved.freshLocalId (mapping declaration) (scope.map (ownerLocalIdMap mapping)) =
      ⟨mapping declaration, (Resolved.freshLocalId declaration scope).binderIndex⟩ ∧
    mapped (inputs.bindFresh declaration name type) mapping injective =
      (mapped inputs mapping injective).bindFresh (mapping declaration) name type :=
  ⟨Resolved.freshLocalId_map_owner mapping injective declaration scope, inputs.bindFresh_mapOwner declaration mapping injective name type⟩

theorem sparse_mixed_owners_and_repeated_raw_ids_do_not_replace_maximum_index_allocation_with_row_count
    (type : Core.Ty) :
    Resolved.freshLocalId (owner 0) [localId 0 7, localId 1 199, localId 0 2, localId 0 7] = localId 0 8 ∧
    Resolved.freshLocalId (shift (owner 0)) ([localId 0 7, localId 1 199, localId 0 2, localId 0 7].map (ownerLocalIdMap shift)) = localId 5 8 ∧
    (((mapped (initial type) shift shiftInjective).bindFresh (owner 5) "x" type).bindFresh (owner 5) "y" type).ids =
      [localId 5 9, localId 5 8, localId 5 7, localId 6 199, localId 5 2] :=
  ⟨rfl, Resolved.freshLocalId_map_owner shift shiftInjective (owner 0) _, rfl⟩

theorem arbitrary_length_independent_static_provenance_and_typing_keep_exact_core
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "old"])
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    TypedLetReturnBodyElaborates (types type) (mapping (owner 0)) (mapped (initial type) mapping injective)
      (chain names "seed") (chainCore names.length) type ∧
    TypedLetReturnBodyHasType (types type) (mapping (owner 0)) (mapped (initial type) mapping injective) (chain names "seed") type ∧
    elaborateTypedLetReturnBody? (types type) (mapping (owner 0)) (mapped (initial type) mapping injective) (chain names "seed") =
      some (chainCore names.length, type) :=
  ⟨(seedChain names type distinct fresh).mapOwner mapping injective, (seedChain names type distinct fresh).hasType.mapOwner mapping injective,
    (elaborateTypedLetReturnBody?_mapOwner mapping injective (types type) (owner 0) (initial type) _).trans (seedChain names type distinct fresh).complete⟩

theorem nonsurjective_owner_changes_preserve_nominal_provenance_without_supplying_an_inhabitant
    (names : List String) (nominal : Core.DataTypeId) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "side", "old"]) :
    ¬ Function.Surjective shift ∧
    elaborateTypedLetReturnBody? (types (.namedData nominal)) (owner 5) (mapped (initial (.namedData nominal)) shift shiftInjective)
      (chain names "seed") = some (chainCore names.length, .namedData nominal) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨?_, (arbitrary_length_independent_static_provenance_and_typing_keep_exact_core names _ distinct fresh shift shiftInjective).2.2, ?_⟩
  · intro onto
    obtain ⟨preimage, same⟩ := onto (owner 0)
    have indices := congrArg Resolved.DeclarationId.declarationIndex same
    change preimage.declarationIndex + 5 = 0 at indices
    omega
  · rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem row_order_spellings_types_and_indices_remain_fixed_while_actual_owners_change (type : Core.Ty) :
    (mapped (initial type) shift shiftInjective).ids = [localId 5 7, localId 6 199, localId 5 2] ∧
    (mapped (initial type) shift shiftInjective).names.map Prod.fst = ["seed", "side", "old"] ∧
    (mapped (initial type) shift shiftInjective).context.values = [type, .word, .bool] ∧
    (mapped (initial type) shift shiftInjective).ids.map (·.binderIndex) = (initial type).ids.map (·.binderIndex) ∧
    (mapped (initial type) shift shiftInjective).ids ≠ (initial type).ids := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro same
  have head := congrArg (fun ids => ids.head?.map (·.owner.declarationIndex)) same
  cases head

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def inputs {type : Core.Ty} (actual : Actual type) (side : Core.Word) (old : Bool) : LocalInputs :=
  ⟨[⟨"seed", localId 0 7, type, actual.val, actual.property⟩, ⟨"side", localId 1 199, .word, .word side, .word⟩,
    ⟨"old", localId 0 2, .bool, .bool old, .bool⟩], by change [localId 0 7, localId 1 199, localId 0 2].Nodup; decide⟩
private def mappedValues (inputs : LocalInputs) (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) := inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)
theorem actual_typed_inputs_preserve_complete_checker_and_runner_options_at_every_fuel
    {type : Core.Ty} (actual : Actual type) (side : Core.Word) (old : Bool) (body : Syntax.Block) (fuel : Nat) (store : Core.Store)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    (mappedValues (inputs actual side old) mapping injective).checkTypedLetReturnBody? (types type) (mapping (owner 0)) body =
      (inputs actual side old).checkTypedLetReturnBody? (types type) (owner 0) body ∧
    (mappedValues (inputs actual side old) mapping injective).runTypedLetReturnBody? (types type) (mapping (owner 0)) fuel body store =
      (inputs actual side old).runTypedLetReturnBody? (types type) (owner 0) fuel body store :=
  ⟨(inputs actual side old).checkTypedLetReturnBody?_mapOwner mapping injective (types type) (owner 0) body,
    (inputs actual side old).runTypedLetReturnBody?_mapOwner mapping injective (types type) (owner 0) fuel body store⟩

private def subtract (left right : String) : Syntax.Expr := ⟨span, .binary (ref left) ⟨span, .subtract⟩ (ref right)⟩
private def ordered : Syntax.Block := ⟨span, [binding "x" (subtract "seed" "side"), binding "y" (ref "x"), returned (subtract "side" "x")]⟩
private def orderedTail : Core.Expr := .letE (.var 0) (.binary .wordSub (.var 3) (.var 1))
private def orderedCore : Core.Expr := .letE (.binary .wordSub (.var 0) (.var 1)) orderedTail
private theorem orderedElab : TypedLetReturnBodyElaborates (types .word) (owner 0) (initial .word) ordered orderedCore .word :=
  .binding (.named .head) (by decide)
    (.subtract (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.binary (.var .head) (.var (.tail (by decide) .head))) (.binary (.var .head) (.var (.tail (by decide) .head)))
    (.binding (.named .head) (by decide) (.identifier .head) (.var .head) (.var .head)
      (.terminal (.single (.expression
        (.subtract (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.identifier (.tail (by decide) .head)))
        (.binary (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) .head)))
        (.binary (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) .head)))))))
private def checkpoint (seed side : Core.Word) (old : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.word seed), [.binaryRight .wordSub (.var 1) [.word seed, .word side, .bool old],
    .letBody orderedTail [.word seed, .word side, .bool old]], store⟩
private def tailCheckpoint (seed side : Core.Word) (old : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.word (seed.sub side)), [.letBody (.binary .wordSub (.var 3) (.var 1)) [.word (seed.sub side), .word seed, .word side, .bool old]], store⟩
private theorem exhausted (seed side : Core.Word) (old : Bool) (store : Core.Store) :
    (inputs ⟨.word seed, .word⟩ side old).runTypedLetReturnBody? (types .word) (owner 0) 3 ordered store = some (.word, .outOfFuel (checkpoint seed side old store)) :=
  LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨orderedCore, orderedElab.complete, rfl⟩

theorem exact_noncommutative_core_and_genuine_checkpoints_survive_nonsurjective_owner_changes
    (seed side : Core.Word) (old : Bool) (store : Core.Store) (additional : Nat) :
    (mappedValues (inputs ⟨.word seed, .word⟩ side old) shift shiftInjective).checkTypedLetReturnBody? (types .word) (owner 5) ordered = some (orderedCore, .word) ∧
    (mappedValues (inputs ⟨.word seed, .word⟩ side old) shift shiftInjective).runTypedLetReturnBody? (types .word) (owner 5) 3 ordered store =
      some (.word, .outOfFuel (checkpoint seed side old store)) ∧
    Core.runStateful 6 (checkpoint seed side old store) = .outOfFuel (tailCheckpoint seed side old store) ∧
    (mappedValues (inputs ⟨.word seed, .word⟩ side old) shift shiftInjective).runTypedLetReturnBody? (types .word) (owner 5) 9 ordered store =
      some (.word, .outOfFuel (tailCheckpoint seed side old store)) ∧
    Core.runStateful 6 (tailCheckpoint seed side old store) = .done (.word (side.sub (seed.sub side))) store ∧
    (mappedValues (inputs ⟨.word seed, .word⟩ side old) shift shiftInjective).runTypedLetReturnBody? (types .word) (owner 5) (3 + additional) ordered store =
      some (.word, Core.runStateful additional (checkpoint seed side old store)) ∧
    (mappedValues (inputs ⟨.word seed, .word⟩ side old) shift shiftInjective).runTypedLetReturnBody? (types .word) (owner 5) (9 + additional) ordered store =
      some (.word, Core.runStateful additional (tailCheckpoint seed side old store)) := by
  have relabeled := ((inputs ⟨.word seed, .word⟩ side old).runTypedLetReturnBody?_mapOwner shift shiftInjective (types .word) (owner 0) 3 ordered store).trans
    (exhausted seed side old store)
  have tailOriginal : (inputs ⟨.word seed, .word⟩ side old).runTypedLetReturnBody? (types .word) (owner 0) 9 ordered store =
      some (.word, .outOfFuel (tailCheckpoint seed side old store)) :=
    LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨orderedCore, orderedElab.complete, rfl⟩
  have tailRelabeled := ((inputs ⟨.word seed, .word⟩ side old).runTypedLetReturnBody?_mapOwner shift shiftInjective (types .word) (owner 0) 9 ordered store).trans tailOriginal
  exact ⟨((inputs ⟨.word seed, .word⟩ side old).checkTypedLetReturnBody?_mapOwner shift shiftInjective (types .word) (owner 0) ordered).trans orderedElab.complete,
    relabeled, rfl, tailRelabeled, rfl, LocalInputs.runTypedLetReturnBody?_resume relabeled additional,
    LocalInputs.runTypedLetReturnBody?_resume tailRelabeled additional⟩

private theorem oneMapped {type : Core.Ty} (actual : Actual type) (side : Core.Word) (old : Bool) (store : Core.Store) :
    (mappedValues (inputs actual side old) shift shiftInjective).runTypedLetReturnBody? (types type) (owner 5) 4 (chain ["x"] "seed") store =
      some (type, .done actual.val store) :=
  ((inputs actual side old).runTypedLetReturnBody?_mapOwner shift shiftInjective (types type) (owner 0) 4 _ store).trans
    (LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨chainCore 1, (seedChain ["x"] type (by decide) (by decide)).complete, rfl⟩)
theorem actual_cells_and_closures_keep_the_identical_store_bearing_completed_result
    (location : Core.Location) (word side : Core.Word) (old : Bool) (store : Core.Store) :
    (mappedValues (inputs (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word)) side old) shift shiftInjective).runTypedLetReturnBody?
      (types (.cell .word)) (owner 5) 4 (chain ["x"] "seed") store = some (.cell .word, .done (.cellRef .word location) store) ∧
    (mappedValues (inputs (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word)) side old)
      shift shiftInjective).runTypedLetReturnBody? (types (.function .bool .word)) (owner 5) 4 (chain ["x"] "seed") store =
      some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨oneMapped _ side old store, oneMapped _ side old store⟩

theorem unknown_annotation_failure_survives_owner_changes_without_an_inverse_map
    {type : Core.Ty} (actual : Actual type) (side : Core.Word) (old : Bool) (fuel : Nat) (store : Core.Store) :
    elaborateTypedLetReturnBody? [] (owner 5) (mapped (initial type) shift shiftInjective) (chain ["x"] "seed") = none ∧
    (mappedValues (inputs actual side old) shift shiftInjective).runTypedLetReturnBody? [] (owner 5) fuel (chain ["x"] "seed") store = none := by
  have rejected : elaborateTypedLetReturnBody? [] (owner 0) (initial type) (chain ["x"] "seed") = none := by
    simp [chain, statements, binding, elaborateTypedLetReturnBody?, interpretTypeName?, annotation, TypeNameTable.lookup?]
  exact ⟨(elaborateTypedLetReturnBody?_mapOwner shift shiftInjective [] (owner 0) (initial type) _).trans rejected,
    ((inputs actual side old).runTypedLetReturnBody?_mapOwner shift shiftInjective [] (owner 0) fuel _ store).trans
      (LocalInputs.runTypedLetReturnBody?_eq_none_iff.mpr rejected)⟩

private def collapse (_ : Resolved.DeclarationId) := owner 0
private def indexShift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex + 10 }
theorem owner_collapse_and_injective_index_shifts_do_not_commute_with_fresh_allocation :
    ¬ Function.Injective collapse ∧
    Resolved.freshLocalId (collapse (owner 0)) ([localId 1 199].map (ownerLocalIdMap collapse)) = localId 0 200 ∧
    ownerLocalIdMap collapse (Resolved.freshLocalId (owner 0) [localId 1 199]) = localId 0 0 ∧
    Resolved.freshLocalId (collapse (owner 0)) ([localId 1 199].map (ownerLocalIdMap collapse)) ≠
      ownerLocalIdMap collapse (Resolved.freshLocalId (owner 0) [localId 1 199]) ∧
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

end Tests.FrontendTypedLetReturnBodyOwner
