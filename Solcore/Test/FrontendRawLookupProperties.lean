import Solcore.Frontend.LocalExpressionLookupProperties
import Solcore.Frontend.TypedLetReturnTreeLookupProperties
import Solcore.Frontend.TypedLetReturnTreeRunnerProperties
import Solcore.Frontend.LocalNameRenaming
import Solcore.Resolved.RenamingProperties

/-! Composed lookup, not hidden identities or positional machine layouts, is
the raw observation. All concrete results begin with independent source paths. -/
set_option autoImplicit false
namespace Tests.FrontendRawLookup
open Solcore Solcore.Frontend

private def owner (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Lookup", by decide⟩], by decide⟩⟩, index⟩
private def id (declaration index : Nat) : Resolved.LocalId := ⟨owner declaration, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "lookup.sol"⟩, 227, 9⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Word"⟩, []⟩⟩⟩ none⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def binding (name : String) (value : Syntax.Expr) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some value)⟩ :: tail.value⟩
private def zero : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span, .binary zero ⟨span, .equal⟩ zero⟩
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => binding name (ref previous)
      ⟨span, [⟨span, .ifThen guard (tree rest name) (some (returned name))⟩]⟩
private def leftTable : LocalNameTable := [("seed", id 0 7), ("seed", id 1 199), ("alias", id 0 7)]
private def rightTable : LocalNameTable :=
  [("ghost", id 2 80), ("seed", id 3 3), ("alias", id 3 3), ("seed", id 4 9), ("ghost", id 4 10)]
private def leftEnv (value hidden : Core.Value) : Resolved.Environment :=
  [(id 0 8, hidden), (id 1 199, .bool false), (id 0 7, value), (id 0 7, .bool true)]
private def rightEnv (value hidden : Core.Value) : Resolved.Environment :=
  [(id 2 81, hidden), (id 3 3, value), (id 4 9, .bool false), (id 3 3, .bool true), (id 0 900, .unit)]
private theorem sameLookup (value hidden : Core.Value) (name : String) :
    (leftTable.lookup? name).bind (leftEnv value hidden).lookup? =
      (rightTable.lookup? name).bind (rightEnv value hidden).lookup? := by
  by_cases seed : name = "seed"
  · subst name; rfl
  by_cases alias : name = "alias"
  · subst name; rfl
  by_cases ghost : name = "ghost"
  · subst name; rfl
  simp [leftTable, rightTable, LocalNameTable.lookup?, Ne.symm seed, Ne.symm alias, Ne.symm ghost]
private theorem counted (locals : List String) (who : Resolved.DeclarationId) (previous : String)
    (table : LocalNameTable) (env : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost table env store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost who table env store (tree locals previous) value store (10 * locals.length + 1) := by
  induction locals generalizing previous table env with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
    have count : 1 + (5 + (10 * rest.length + 1) + 2) + 2 = 10 * (name :: rest).length + 1 := by simp; omega
    simpa only [count, tree, binding, guard, zero] using TypedLetReturnTreeEvaluatesWithCost.binding
      (name := ⟨span, name⟩) (annotation := annotation) head
      (.ifTrue (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)) (ih name _ _ (.identifier .head .head)))
private theorem raw (locals : List String) (value hidden : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost (owner 0) leftTable (leftEnv value hidden) store (tree locals "seed") value store (10 * locals.length + 1) :=
  counted locals (owner 0) "seed" leftTable (leftEnv value hidden) value store
    (.identifier .head (.tail (by decide) (.tail (by decide) .head)))

theorem arbitrary_names_and_depth_preserve_exact_values_costs_and_both_stores
    (locals : List String) (value hidden : Core.Value) (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? (owner 0) leftTable (leftEnv value hidden) (tree locals "seed") = some (value, 10 * locals.length + 1) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv value hidden) (tree locals "seed") = some (value, 10 * locals.length + 1) ∧
    TypedLetReturnTreeEvaluatesWithCost (owner 2) rightTable (rightEnv value hidden) store (tree locals "seed") value store (10 * locals.length + 1) ∧
    TypedLetReturnTreeEvaluates (owner 2) rightTable (rightEnv value hidden) store (tree locals "seed") value store := by
  have original := evaluateTypedLetReturnTreeWithCost?_complete (raw locals value hidden store)
  exact ⟨original,
    (evaluateTypedLetReturnTreeWithCost?_congr_lookup (owner 0) (owner 2) leftTable rightTable _ _ (sameLookup value hidden) _).symm.trans original,
    (typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff (sameLookup value hidden)).mp (raw locals value hidden store),
    (typedLetReturnTreeEvaluates_congr_lookup_iff (sameLookup value hidden)).mp (raw locals value hidden store).erase⟩

theorem reflection_does_not_drop_the_final_store_constraint
    (locals : List String) (value hidden result : Core.Value) (store final : Core.Store) (cost : Nat) :
    (TypedLetReturnTreeEvaluatesWithCost (owner 2) rightTable (rightEnv value hidden) store (tree locals "seed") result final cost ↔
      result = value ∧ final = store ∧ cost = 10 * locals.length + 1) ∧
    (TypedLetReturnTreeEvaluates (owner 2) rightTable (rightEnv value hidden) store (tree locals "seed") result final ↔
      result = value ∧ final = store) := by
  constructor
  · constructor
    · intro path
      exact ((typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff (leftOwner := owner 0)
        (sameLookup value hidden)).mpr path).deterministic (raw locals value hidden store)
    · rintro ⟨sameValue, sameStore, sameCost⟩; subst result; subst final; subst cost
      exact (typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff (sameLookup value hidden)).mp (raw locals value hidden store)
  · constructor
    · intro path
      exact ((typedLetReturnTreeEvaluates_congr_lookup_iff (leftOwner := owner 0)
        (sameLookup value hidden)).mpr path).deterministic (raw locals value hidden store).erase
    · rintro ⟨sameValue, sameStore⟩; subst result; subst final
      exact (typedLetReturnTreeEvaluates_congr_lookup_iff (sameLookup value hidden)).mp (raw locals value hidden store).erase

theorem absent_and_unbound_names_can_change_allocation_without_changing_results (value hidden : Core.Value) :
    leftTable.lookup? "ghost" = none ∧ rightTable.lookup? "ghost" = some (id 2 80) ∧
    (rightEnv value hidden).lookup? (id 2 80) = none ∧
    Resolved.freshLocalId (owner 0) (leftTable.map Prod.snd) = id 0 8 ∧
    Resolved.freshLocalId (owner 2) (rightTable.map Prod.snd) = id 2 81 ∧
    (leftEnv value hidden).lookup? (id 0 8) = some hidden ∧ (rightEnv value hidden).lookup? (id 2 81) = some hidden ∧
    leftTable.length ≠ rightTable.length ∧ (leftEnv value hidden).length ≠ (rightEnv value hidden).length ∧
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv value hidden) (tree ["ghost", "seed", "seed"] "seed") = some (value, 31) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by change 4 ≠ 5; decide,
    (arbitrary_names_and_depth_preserve_exact_values_costs_and_both_stores _ value hidden []).2.1⟩

private def shortCircuit : Syntax.Expr := ⟨span, .binary (ref "seed") ⟨span, .logicalAnd⟩ (ref "ghost")⟩
theorem composed_lookup_preserves_short_circuit_success_and_selected_absence (hidden : Core.Value) :
    evaluateLocalExpressionWithCost? leftTable (leftEnv (.bool false) hidden) shortCircuit = some (.bool false, 4) ∧
    evaluateLocalExpressionWithCost? rightTable (rightEnv (.bool false) hidden) shortCircuit = some (.bool false, 4) ∧
    evaluateLocalExpressionWithCost? leftTable (leftEnv (.bool true) hidden) shortCircuit = none ∧
    evaluateLocalExpressionWithCost? rightTable (rightEnv (.bool true) hidden) shortCircuit = none := by
  have falsePath : LocalExpressionEvaluatesWithCost leftTable (leftEnv (.bool false) hidden) [] shortCircuit (.bool false) [] 4 :=
    .andFalse (.identifier .head (.tail (by decide) (.tail (by decide) .head)))
  have succeeded := evaluateLocalExpressionWithCost?_complete falsePath
  have absent : evaluateLocalExpressionWithCost? leftTable (leftEnv (.bool true) hidden) shortCircuit = none := by
    simp [evaluateLocalExpressionWithCost?, shortCircuit, ref, leftTable, leftEnv,
      LocalNameTable.lookup?, Resolved.LocalScope.lookup?, id, owner]
  exact ⟨succeeded,
    (evaluateLocalExpressionWithCost?_congr_lookup _ _ _ _ (sameLookup (.bool false) hidden) _).symm.trans succeeded,
    absent, (evaluateLocalExpressionWithCost?_congr_lookup _ _ _ _ (sameLookup (.bool true) hidden) _).symm.trans absent⟩

theorem opaque_values_keep_their_exact_representation (locals : List String) (location : Core.Location) :
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv (.cellRef .word location) .unit) (tree locals "seed") =
      some (.cellRef .word location, 10 * locals.length + 1) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv (.closure .word .bool (.var 90) [.unit]) .unit) (tree locals "seed") =
      some (.closure .word .bool (.var 90) [.unit], 10 * locals.length + 1) :=
  ⟨(arbitrary_names_and_depth_preserve_exact_values_costs_and_both_stores locals _ .unit []).2.1,
    (arbitrary_names_and_depth_preserve_exact_values_costs_and_both_stores locals _ .unit []).2.1⟩

private def indexShift (binder : Resolved.LocalId) : Resolved.LocalId := { binder with binderIndex := binder.binderIndex + 10 }
private theorem indexInjective : Function.Injective indexShift := by
  intro left right same
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases left; cases right; cases owners; cases indices; rfl
theorem injective_index_changes_can_preserve_raw_results_without_allocator_commutation (value : Core.Value) :
    Function.Injective indexShift ∧
    Resolved.freshLocalId (owner 0) ([id 1 0].map indexShift) ≠ indexShift (Resolved.freshLocalId (owner 0) [id 1 0]) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) [("seed", id 1 0)] [(id 1 0, value)] (binding "z" (ref "seed") (returned "z")) = some (value, 4) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) (LocalNameTable.mapIds indexShift [("seed", id 1 0)])
      (Resolved.LocalScope.mapIds indexShift [(id 1 0, value)]) (binding "z" (ref "seed") (returned "z")) = some (value, 4) := by
  have lookup (name : String) :
      (LocalNameTable.lookup? [("seed", id 1 0)] name).bind (Resolved.LocalScope.lookup? [(id 1 0, value)]) =
        (LocalNameTable.lookup? (LocalNameTable.mapIds indexShift [("seed", id 1 0)]) name).bind
          (Resolved.LocalScope.lookup? (Resolved.LocalScope.mapIds indexShift [(id 1 0, value)])) := by
    by_cases hit : name = "seed"
    · subst name; rfl
    · simp [LocalNameTable.mapIds, LocalNameTable.lookup?, Ne.symm hit]
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) [("seed", id 1 0)] [(id 1 0, value)] []
      (binding "z" (ref "seed") (returned "z")) value [] 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head .head
    · exact .single (.expression (.identifier .head .head))
  have output := evaluateTypedLetReturnTreeWithCost?_complete original
  exact ⟨indexInjective, by decide, output,
    (evaluateTypedLetReturnTreeWithCost?_congr_lookup (owner 0) (owner 0) _ _ _ _ lookup _).symm.trans output⟩

theorem changing_a_visible_first_match_really_can_change_the_result :
    ¬ (∀ name, (leftTable.lookup? name).bind (leftEnv (.bool false) .unit).lookup? =
      (rightTable.lookup? name).bind (rightEnv (.bool true) .unit).lookup?) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) leftTable (leftEnv (.bool false) .unit) (returned "seed") = some (.bool false, 1) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv (.bool true) .unit) (returned "seed") = some (.bool true, 1) := by
  refine ⟨?_, evaluateTypedLetReturnTreeWithCost?_complete (raw [] (.bool false) .unit []),
    (arbitrary_names_and_depth_preserve_exact_values_costs_and_both_stores [] (.bool true) .unit []).2.1⟩
  intro same
  have impossible := same "seed"
  change some (Core.Value.bool false) = some (Core.Value.bool true) at impossible
  cases impossible

theorem a_strict_missing_initializer_is_absent_even_when_its_name_exists_on_one_side (value hidden : Core.Value) (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? (owner 0) leftTable (leftEnv value hidden) (binding "unused" (ref "ghost") (returned "seed")) = none ∧
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv value hidden) (binding "unused" (ref "ghost") (returned "seed")) = none := by
  have absent : ¬ ∃ result cost, TypedLetReturnTreeEvaluatesWithCost (owner 0) leftTable (leftEnv value hidden)
      store (binding "unused" (ref "ghost") (returned "seed")) result store cost := by
    rintro ⟨result, cost, path⟩
    cases path with
    | single child => cases child
    | binding initializer _ =>
      cases initializer with
      | identifier found _ =>
        have impossible := LocalNameTable.lookup?_iff.mpr found
        change none = some _ at impossible
        cases impossible
  have rejected := (evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mpr absent
  exact ⟨rejected, (evaluateTypedLetReturnTreeWithCost?_congr_lookup (owner 0) (owner 2) _ _ _ _ (sameLookup value hidden) _).symm.trans rejected⟩

theorem strict_unused_arithmetic_keeps_its_cost_and_the_old_visible_value (word : Core.Word) (hidden : Core.Value) (store : Core.Store) :
    let body := binding "unused" ⟨span, .binary zero ⟨span, .subtract⟩ (ref "seed")⟩ (returned "seed")
    evaluateTypedLetReturnTreeWithCost? (owner 0) leftTable (leftEnv (.word word) hidden) body = some (.word word, 8) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv (.word word) hidden) body = some (.word word, 8) ∧
    TypedLetReturnTreeEvaluatesWithCost (owner 2) rightTable (rightEnv (.word word) hidden) store body (.word word) store 8 := by
  intro body
  have seed : LocalExpressionEvaluatesWithCost leftTable (leftEnv (.word word) hidden) store (ref "seed") (.word word) store 1 :=
    .identifier .head (.tail (by decide) (.tail (by decide) .head))
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) leftTable (leftEnv (.word word) hidden) store body (.word word) store 8 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 5) (tailCost := 1)
    · exact .subtract (.wordLiteral zeroMeaning) seed
    · exact .single (.expression (.identifier (.tail (by decide) .head)
        (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
  have output := evaluateTypedLetReturnTreeWithCost?_complete original
  exact ⟨output, (evaluateTypedLetReturnTreeWithCost?_congr_lookup (owner 0) (owner 2) _ _ _ _ (sameLookup (.word word) hidden) body).symm.trans output,
    (typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff (sameLookup (.word word) hidden)).mp original⟩

private def leftInputs (word : Core.Word) : LocalInputs := ⟨[⟨"seed", id 0 7, .word, .word word, .word⟩], by change [id 0 7].Nodup; decide⟩
private def rightInputs (word : Core.Word) : LocalInputs :=
  ⟨[⟨"seed", id 1 3, .word, .word word, .word⟩, ⟨"seed", id 1 5, .bool, .bool true, .bool⟩], by change [id 1 3, id 1 5].Nodup; decide⟩
private def checkedBody := binding "x" (ref "seed") (returned "x")
private def checkedCore : Core.Expr := .letE (.var 0) (.var 0)
private theorem checkedLookup (word : Core.Word) (name : String) :
    ((leftInputs word).names.lookup? name).bind (leftInputs word).environment.lookup? =
      ((rightInputs word).names.lookup? name).bind (rightInputs word).environment.lookup? := by
  by_cases hit : name = "seed"
  · subst name; rfl
  · simp [leftInputs, rightInputs, LocalInputs.names, LocalNameTable.lookup?, Ne.symm hit]
private theorem leftElab (word : Core.Word) : TypedLetReturnTreeElaborates [(["Word"], .word)] (owner 0)
    (leftInputs word).toTypeInputs checkedBody checkedCore .word :=
  .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
    (.single (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem rightElab (word : Core.Word) : TypedLetReturnTreeElaborates [(["Word"], .word)] (owner 1)
    (rightInputs word).toTypeInputs checkedBody checkedCore .word :=
  .binding (.named .head) (by change "x" ∉ ["seed", "seed"]; decide) (.identifier .head) (.var .head) (.var .head)
    (.single (.expression (.identifier .head) (.var .head) (.var .head)))

theorem even_independently_checked_and_aligned_inputs_can_have_different_checkpoints (word : Core.Word) (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? (owner 0) (leftInputs word).names (leftInputs word).environment checkedBody = some (.word word, 4) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 1) (rightInputs word).names (rightInputs word).environment checkedBody = some (.word word, 4) ∧
    (leftInputs word).runTypedLetReturnTree? [(["Word"], .word)] (owner 0) 2 checkedBody store =
      some (.word, .outOfFuel ⟨.ret (.word word), [.letBody (.var 0) [.word word]], store⟩) ∧
    (rightInputs word).runTypedLetReturnTree? [(["Word"], .word)] (owner 1) 2 checkedBody store =
      some (.word, .outOfFuel ⟨.ret (.word word), [.letBody (.var 0) [.word word, .bool true]], store⟩) ∧
    (⟨.ret (.word word), [.letBody (.var 0) [.word word]], store⟩ : Core.State) ≠
      ⟨.ret (.word word), [.letBody (.var 0) [.word word, .bool true]], store⟩ := by
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) (leftInputs word).names (leftInputs word).environment store checkedBody (.word word) store 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head .head
    · exact .single (.expression (.identifier .head .head))
  have output := evaluateTypedLetReturnTreeWithCost?_complete original
  exact ⟨output, (evaluateTypedLetReturnTreeWithCost?_congr_lookup (owner 0) (owner 1) _ _ _ _ (checkedLookup word) _).symm.trans output,
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨checkedCore, (leftElab word).complete, rfl⟩,
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨checkedCore, (rightElab word).complete, rfl⟩,
    by intro impossible; cases impossible⟩

theorem the_same_raw_observation_does_not_preserve_whole_annotation_acceptance (word : Core.Word) :
    let bad : LocalTypeInputs := ⟨[⟨"seed", id 1 3, .bool⟩], by decide⟩
    evaluateTypedLetReturnTreeWithCost? (owner 0) (leftInputs word).names (leftInputs word).environment checkedBody = some (.word word, 4) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 1) bad.names [(id 1 3, .word word)] checkedBody = some (.word word, 4) ∧
    elaborateTypedLetReturnTree? [(["Word"], .word)] (owner 0) (leftInputs word).toTypeInputs checkedBody = some (checkedCore, .word) ∧
    elaborateTypedLetReturnTree? [(["Word"], .word)] (owner 1) bad checkedBody = none := by
  intro bad
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 1) bad.names [(id 1 3, .word word)] [] checkedBody (.word word) [] 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head .head
    · exact .single (.expression (.identifier .head .head))
  have lookup (name : String) : ((leftInputs word).names.lookup? name).bind (leftInputs word).environment.lookup? =
      (bad.names.lookup? name).bind (Resolved.LocalScope.lookup? [(id 1 3, Core.Value.word word)]) := by
    by_cases hit : name = "seed"
    · subst name; rfl
    · simp [leftInputs, LocalInputs.names, bad, LocalTypeInputs.names, LocalNameTable.lookup?, Ne.symm hit]
  have output := evaluateTypedLetReturnTreeWithCost?_complete original
  refine ⟨(evaluateTypedLetReturnTreeWithCost?_congr_lookup (owner 0) (owner 1) _ _ _ _ lookup _).trans output,
    output, (leftElab word).complete, ?_⟩
  have initializer : elaborateLocalExpression? bad.names bad.context (ref "seed") = some (.var 0, .bool) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  have fresh : "x" ∉ bad.names.map Prod.fst := by change "x" ∉ ["seed"]; decide
  simp only [checkedBody, binding, elaborateTypedLetReturnTree?, if_pos fresh, initializer]
  rfl

end Tests.FrontendRawLookup
