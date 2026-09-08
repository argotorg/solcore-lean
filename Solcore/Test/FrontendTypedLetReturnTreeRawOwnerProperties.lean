import Solcore.Frontend.TypedLetReturnTreeRawOwnerProperties
import Solcore.Frontend.TypedLetReturnTreeOwnerProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluatorExecutionProperties

/-! Raw rows need not be aligned, unique or typed. Owner transport preserves
first matches and actual values; the final checked path has its own premises. -/
set_option autoImplicit false
namespace Tests.FrontendTypedLetReturnTreeRawOwner
open Solcore Solcore.Frontend

private def owner (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RawOwners", by decide⟩], by decide⟩⟩, index⟩
private def id (declaration index : Nat) : Resolved.LocalId := ⟨owner declaration, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "raw-owners.sol"⟩, 226, 8⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation (name : String := "Payload") : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def binding (name : String) (value : Syntax.Expr) (tail : Syntax.Block) (typeName : String := "Payload") : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some (annotation typeName)) (some value)⟩ :: tail.value⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def zero : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span, .binary zero ⟨span, .equal⟩ zero⟩
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => binding name (ref previous) (branch guard (tree rest name) (returned name))
private def names : LocalNameTable := [("seed", id 0 7), ("seed", id 1 199), ("alias", id 0 7), ("old", id 0 2)]
private def values (value hidden : Core.Value) : Resolved.Environment :=
  [(id 0 8, hidden), (id 1 199, .bool false), (id 0 7, value), (id 0 7, .bool true), (id 0 2, .unit)]
private def mappedNames (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (table : LocalNameTable) := table.mapIds (ownerLocalIdMap mapping)
private def mappedValues (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (env : Resolved.Environment) := env.mapIds (ownerLocalIdMap mapping)
private def shift (declaration : Resolved.DeclarationId) : Resolved.DeclarationId := { declaration with declarationIndex := declaration.declarationIndex + 5 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private theorem counted (locals : List String) (previous : String) (table : LocalNameTable) (env : Resolved.Environment)
    (value : Core.Value) (store : Core.Store) (head : LocalExpressionEvaluatesWithCost table env store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost (owner 0) table env store (tree locals previous) value store (10 * locals.length + 1) := by
  induction locals generalizing previous table env with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
    have count : 1 + (5 + (10 * rest.length + 1) + 2) + 2 = 10 * (name :: rest).length + 1 := by simp; omega
    simpa only [count, tree, binding, branch, guard, zero] using TypedLetReturnTreeEvaluatesWithCost.binding
      (name := ⟨span, name⟩) (annotation := annotation) head
      (.ifTrue (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)) (ih name _ _ (.identifier .head .head)))
private theorem raw (locals : List String) (value hidden : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost (owner 0) names (values value hidden) store (tree locals "seed") value store (10 * locals.length + 1) :=
  counted locals "seed" names (values value hidden) value store (.identifier .head (.tail (by decide) (.tail (by decide) .head)))
private theorem output (locals : List String) (value hidden : Core.Value) :
    evaluateTypedLetReturnTreeWithCost? (owner 0) names (values value hidden) (tree locals "seed") = some (value, 10 * locals.length + 1) :=
  evaluateTypedLetReturnTreeWithCost?_complete (raw locals value hidden [])

theorem arbitrary_raw_depth_and_duplicate_unaligned_rows_keep_values_costs_and_stores
    (locals : List String) (value hidden : Core.Value) (store : Core.Store)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    evaluateTypedLetReturnTreeWithCost? (mapping (owner 0)) (mappedNames mapping names) (mappedValues mapping (values value hidden))
      (tree locals "seed") = some (value, 10 * locals.length + 1) ∧
    TypedLetReturnTreeEvaluatesWithCost (mapping (owner 0)) (mappedNames mapping names) (mappedValues mapping (values value hidden))
      store (tree locals "seed") value store (10 * locals.length + 1) ∧
    TypedLetReturnTreeEvaluates (mapping (owner 0)) (mappedNames mapping names) (mappedValues mapping (values value hidden))
      store (tree locals "seed") value store ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) names (values value hidden) (tree locals "seed") = some (value, 10 * locals.length + 1) := by
  have same := evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective (owner 0) names (values value hidden) (tree locals "seed")
  have mappedResult := same.trans (output locals value hidden)
  exact ⟨mappedResult,
    (typedLetReturnTreeEvaluatesWithCost_mapOwner_iff mapping injective).mpr (raw locals value hidden store),
    (typedLetReturnTreeEvaluates_mapOwner_iff mapping injective).mpr (raw locals value hidden store).erase,
    same.symm.trans mappedResult⟩

theorem reflection_retains_exact_final_store_value_and_cost
    (locals : List String) (value hidden result : Core.Value) (store final : Core.Store) (cost : Nat) :
    (TypedLetReturnTreeEvaluatesWithCost (owner 5) (mappedNames shift names) (mappedValues shift (values value hidden))
      store (tree locals "seed") result final cost ↔ result = value ∧ final = store ∧ cost = 10 * locals.length + 1) ∧
    (TypedLetReturnTreeEvaluates (owner 5) (mappedNames shift names) (mappedValues shift (values value hidden))
      store (tree locals "seed") result final ↔ result = value ∧ final = store) := by
  constructor
  · constructor
    · intro path
      exact ((typedLetReturnTreeEvaluatesWithCost_mapOwner_iff shift shiftInjective (owner := owner 0)
        (table := names) (environment := values value hidden)).mp path).deterministic (raw locals value hidden store)
    · rintro ⟨sameValue, sameStore, sameCost⟩; subst result; subst final; subst cost
      exact (typedLetReturnTreeEvaluatesWithCost_mapOwner_iff shift shiftInjective).mpr (raw locals value hidden store)
  · constructor
    · intro path
      exact ((typedLetReturnTreeEvaluates_mapOwner_iff shift shiftInjective (owner := owner 0)
        (table := names) (environment := values value hidden)).mp path).deterministic (raw locals value hidden store).erase
    · rintro ⟨sameValue, sameStore⟩; subst result; subst final
      exact (typedLetReturnTreeEvaluates_mapOwner_iff shift shiftInjective).mpr (raw locals value hidden store).erase

theorem a_nonsurjective_owner_map_changes_only_owners_not_indices_or_row_order (value hidden : Core.Value) :
    ¬ Function.Surjective shift ∧
    mappedNames shift names = [("seed", id 5 7), ("seed", id 6 199), ("alias", id 5 7), ("old", id 5 2)] ∧
    (mappedValues shift (values value hidden)).values = [hidden, .bool false, value, .bool true, .unit] ∧
    (mappedValues shift (values value hidden)).ids ≠ (mappedNames shift names).map Prod.snd ∧
    ¬ ((mappedNames shift names).map Prod.snd).Nodup := by
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · intro onto
    obtain ⟨preimage, same⟩ := onto (owner 0)
    have impossible := congrArg Resolved.DeclarationId.declarationIndex same
    change preimage.declarationIndex + 5 = 0 at impossible
    omega
  · intro same; cases same
  · decide

theorem fresh_name_table_allocation_can_collide_with_an_extra_environment_row
    (value hidden : Core.Value) (store : Core.Store) :
    Resolved.freshLocalId (owner 0) (names.map Prod.snd) = id 0 8 ∧
    Resolved.freshLocalId (owner 5) ((mappedNames shift names).map Prod.snd) = id 5 8 ∧
    (mappedValues shift (values value hidden)).lookup? (id 5 8) = some hidden ∧
    evaluateTypedLetReturnTreeWithCost? (owner 5) (mappedNames shift names) (mappedValues shift (values value hidden))
      (binding "seed" (ref "seed") (returned "seed")) = some (value, 4) ∧
    TypedLetReturnTreeEvaluatesWithCost (owner 5) (mappedNames shift names) (mappedValues shift (values value hidden))
      store (binding "seed" (ref "seed") (returned "seed")) value store 4 := by
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) names (values value hidden) store
      (binding "seed" (ref "seed") (returned "seed")) value store 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head (.tail (by decide) (.tail (by decide) .head))
    · exact .single (.expression (.identifier .head .head))
  exact ⟨rfl, rfl, rfl,
    (evaluateTypedLetReturnTreeWithCost?_mapOwner shift shiftInjective (owner 0) names _ _).trans
      (evaluateTypedLetReturnTreeWithCost?_complete original),
    (typedLetReturnTreeEvaluatesWithCost_mapOwner_iff shift shiftInjective).mpr original⟩

private def clean (type : Core.Ty) : LocalTypeInputs := ⟨[⟨"seed", id 0 7, type⟩], by change [id 0 7].Nodup; decide⟩
private def cleanValues (value : Core.Value) : Resolved.Environment := [(id 0 7, value)]
private def unknown := binding "fresh" (ref "seed") (returned "fresh") "Unknown"
private def skipped := branch guard (returned "seed") unknown
theorem raw_selected_success_does_not_establish_the_unselected_annotation_contract
    (value : Core.Value) (type : Core.Ty) (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? (owner 5) (mappedNames shift (clean type).names)
      (mappedValues shift (cleanValues value)) skipped = some (value, 8) ∧
    elaborateTypedLetReturnTree? [(["Payload"], type)] (owner 5)
      ((clean type).mapIds (ownerLocalIdMap shift) (ownerLocalIdMap_injective shift shiftInjective)) skipped = none := by
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) (clean type).names (cleanValues value) store skipped value store 8 := by
    apply TypedLetReturnTreeEvaluatesWithCost.ifTrue (conditionCost := 5) (branchCost := 1)
    · exact .equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)
    · exact .single (.expression (.identifier .head .head))
  refine ⟨(evaluateTypedLetReturnTreeWithCost?_mapOwner shift shiftInjective (owner 0) _ _ _).trans
    (evaluateTypedLetReturnTreeWithCost?_complete original),
    (elaborateTypedLetReturnTree?_mapOwner shift shiftInjective _ (owner 0) (clean type) skipped).trans ?_⟩
  apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
  rintro ⟨_, typing⟩
  cases typing with
  | single child => cases child
  | conditional _ _ other =>
    cases other with
    | single child => cases child
    | binding meaning _ _ _ =>
      have impossible := meaning.complete
      change none = some _ at impossible
      cases impossible

theorem missing_selected_initializers_remain_absent_in_both_raw_relations (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? (owner 5) (mappedNames shift names) [] unknown = none ∧
    ¬ (∃ result cost, TypedLetReturnTreeEvaluatesWithCost (owner 5) (mappedNames shift names) [] store unknown result store cost) ∧
    ¬ (∃ result, TypedLetReturnTreeEvaluates (owner 5) (mappedNames shift names) [] store unknown result store) := by
  have absent : ¬ ∃ result cost, TypedLetReturnTreeEvaluatesWithCost (owner 0) names [] store unknown result store cost := by
    rintro ⟨_, _, path⟩
    cases path with
    | single child => cases child
    | binding initializer _ => cases initializer with | identifier _ found => cases found
  refine ⟨(evaluateTypedLetReturnTreeWithCost?_mapOwner shift shiftInjective (owner 0) names [] unknown).trans
    ((evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mpr absent), ?_, ?_⟩
  · rintro ⟨result, cost, path⟩
    exact absent ⟨result, cost, (typedLetReturnTreeEvaluatesWithCost_mapOwner_iff shift shiftInjective).mp path⟩
  · rintro ⟨result, path⟩
    obtain ⟨cost, costed⟩ := ((typedLetReturnTreeEvaluates_mapOwner_iff shift shiftInjective
      (owner := owner 0) (table := names) (environment := [])).mp path).exists_cost
    exact absent ⟨result, cost, costed⟩

theorem opaque_values_are_not_retyped_or_invoked_by_owner_transport
    (locals : List String) (location : Core.Location) (hidden : Core.Value) :
    evaluateTypedLetReturnTreeWithCost? (owner 5) (mappedNames shift names)
      (mappedValues shift (values (.cellRef .word location) hidden)) (tree locals "seed") = some (.cellRef .word location, 10 * locals.length + 1) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 5) (mappedNames shift names)
      (mappedValues shift (values (.closure .word .bool (.var 999) [.unit]) hidden)) (tree locals "seed") =
      some (.closure .word .bool (.var 999) [.unit], 10 * locals.length + 1) :=
  ⟨(arbitrary_raw_depth_and_duplicate_unaligned_rows_keep_values_costs_and_stores locals _ hidden [] shift shiftInjective).1,
    (arbitrary_raw_depth_and_duplicate_unaligned_rows_keep_values_costs_and_stores locals _ hidden [] shift shiftInjective).1⟩

private def collapse (_ : Resolved.DeclarationId) := owner 0
private def collisionNames : LocalNameTable := [("seed", id 1 0)]
private def collisionValues : Resolved.Environment := [(id 0 0, .bool false), (id 1 0, .bool true)]
private def collisionBody := binding "z" (ref "seed") (returned "z")
theorem a_noninjective_owner_collapse_changes_the_actual_first_match :
    ¬ Function.Injective collapse ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) collisionNames collisionValues collisionBody = some (.bool true, 4) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) (mappedNames collapse collisionNames) (mappedValues collapse collisionValues) collisionBody = some (.bool false, 4) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) collisionNames collisionValues collisionBody ≠
      evaluateTypedLetReturnTreeWithCost? (owner 0) (mappedNames collapse collisionNames) (mappedValues collapse collisionValues) collisionBody := by
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) collisionNames collisionValues [] collisionBody (.bool true) [] 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head (.tail (by decide) .head)
    · exact .single (.expression (.identifier .head .head))
  have collapsed : TypedLetReturnTreeEvaluatesWithCost (owner 0) (mappedNames collapse collisionNames) (mappedValues collapse collisionValues) [] collisionBody (.bool false) [] 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head .head
    · exact .single (.expression (.identifier .head .head))
  have before := evaluateTypedLetReturnTreeWithCost?_complete original
  have after := evaluateTypedLetReturnTreeWithCost?_complete collapsed
  refine ⟨?_, before, after, ?_⟩
  · intro injective
    have impossible := injective (a₁ := owner 0) (a₂ := owner 1) rfl
    cases impossible
  · rw [before, after]; intro impossible; cases impossible

private def indexShift (binder : Resolved.LocalId) : Resolved.LocalId := { binder with binderIndex := binder.binderIndex + 10 }
theorem arbitrary_index_shifts_fail_allocator_commutation_without_claiming_changed_raw_results :
    Function.Injective indexShift ∧
    Resolved.freshLocalId (owner 0) ([].map indexShift) = id 0 0 ∧
    indexShift (Resolved.freshLocalId (owner 0) []) = id 0 10 ∧
    Resolved.freshLocalId (owner 0) ([].map indexShift) ≠ indexShift (Resolved.freshLocalId (owner 0) []) := by
  refine ⟨?_, rfl, rfl, by decide⟩
  intro left right same
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases left; cases right; cases owners; cases indices; rfl

theorem a_checked_core_path_uses_separate_whole_provenance_and_aligned_ids
    (type : Core.Ty) (value : Core.Value) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 4 ⟨.eval (.letE (.var 0) (.var 0)) [value], continuation, store⟩ ⟨.ret value, continuation, store⟩ := by
  have elaboration : TypedLetReturnTreeElaborates [(["Payload"], type)] (owner 0) (clean type)
      (binding "x" (ref "seed") (returned "x")) (.letE (.var 0) (.var 0)) type :=
    .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) (clean type).names (cleanValues value) store
      (binding "x" (ref "seed") (returned "x")) value store 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head .head
    · exact .single (.expression (.identifier .head .head))
  have evaluated := (evaluateTypedLetReturnTreeWithCost?_mapOwner shift shiftInjective (owner 0) _ _ _).trans
    (evaluateTypedLetReturnTreeWithCost?_complete original)
  exact evaluateTypedLetReturnTreeWithCost?_checked_toStepsWithContinuation evaluated
    (elaboration.mapOwner shift shiftInjective).complete rfl continuation

end Tests.FrontendTypedLetReturnTreeRawOwner
