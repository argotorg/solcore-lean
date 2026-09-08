import Solcore.Frontend.LocalExpressionCostProperties
import Solcore.Frontend.LocalExpressionCostCorrespondence
import Solcore.Frontend.LocalExpressionCostExecutionProperties
import Solcore.Frontend.LocalInputsExecutionProperties
import Solcore.Core.BitwiseLogic

/-! ADR-0165 consumers count Core transitions, not frontend computation time.
Independent raw cost derivations retain the selected-branch checking boundary. -/

set_option autoImplicit false

namespace Tests.FrontendLocalExpressionCost

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Cost", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "cost.sol"⟩, 0, 1⟩
private def seven : Core.Word := ⟨7, by decide⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def sevenSource : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "7"⟩⟩
private def group (child : Syntax.Expr) : Syntax.Expr := ⟨span, .group child⟩
private def neg (child : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .logicalNot⟩ child⟩
private def complement (child : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .bitNot⟩ child⟩
private def binary (op : Syntax.BinaryOp) (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, op⟩ right⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr := ⟨span, .conditional condition span left span right⟩
private def inputs (choice : Bool) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "w" .word (.word seven) .word).bindFresh owner "c" .bool (.bool choice) .bool
private abbrev Cost (choice : Bool) (store : Core.Store) (source : Syntax.Expr) (value : Core.Value) (cost : Nat) :=
  LocalExpressionEvaluatesWithCost (inputs choice).names (inputs choice).environment store source value store cost
private theorem sevenMeaning : WordLiteralDenotes ⟨span, .decimal "7"⟩ seven :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 7) (by decide) (by decide)) .nil)
private theorem cost_c (choice : Bool) (store : Core.Store) : Cost choice store (ref "c") (.bool choice) 1 :=
  .identifier .head .head
private theorem cost_w (choice : Bool) (store : Core.Store) : Cost choice store (ref "w") (.word seven) 1 :=
  .identifier (.tail (by change "c" ≠ "w"; decide) .head)
    (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
private theorem cost_seven (choice : Bool) (store : Core.Store) : Cost choice store sevenSource (.word seven) 1 :=
  .wordLiteral sevenMeaning

theorem leaves_grouping_unary_and_strict_binary_have_independent_costs (choice : Bool) (store : Core.Store) :
    Cost choice store (ref "c") (.bool choice) 1 ∧ Cost choice store sevenSource (.word seven) 1 ∧
    Cost choice store (group (ref "c")) (.bool choice) 1 ∧
    Cost choice store (neg (ref "c")) (.bool (!choice)) 3 ∧
    Cost choice store (complement sevenSource) (.word seven.bitNot) 3 ∧
    Cost choice store (binary .bitAnd (ref "w") sevenSource) (.word seven) 5 ∧
    Cost choice store (binary .bitOr (ref "w") sevenSource) (.word seven) 5 ∧
    Cost choice store (binary .bitXor (ref "w") sevenSource) (.word Core.Word.zero) 5 := by
  refine ⟨cost_c choice store, cost_seven choice store, .group (cost_c choice store),
    .logicalNot (cost_c choice store), .bitNot (cost_seven choice store), ?_, ?_, ?_⟩
  · simpa [binary] using LocalExpressionEvaluatesWithCost.bitAnd (cost_w choice store) (cost_seven choice store)
  · simpa [binary] using LocalExpressionEvaluatesWithCost.bitOr (cost_w choice store) (cost_seven choice store)
  · simpa [binary] using LocalExpressionEvaluatesWithCost.bitXor (cost_w choice store) (cost_seven choice store)

private def selection : Syntax.Expr := branch (ref "c") (complement sevenSource) sevenSource
private def conjunction : Syntax.Expr := binary .logicalAnd (ref "c") (neg (ref "c"))
private def disjunction : Syntax.Expr := binary .logicalOr (ref "c") (neg (ref "c"))
private def deepConjunction : Syntax.Expr := binary .logicalAnd (ref "c") (neg (neg (ref "c")))
private theorem cost_selection (choice : Bool) (store : Core.Store) :
    Cost choice store selection (.word (if choice then seven.bitNot else seven)) (if choice then 6 else 4) := by
  cases choice
  · exact .ifFalse (cost_c false store) (cost_seven false store)
  · exact .ifTrue (cost_c true store) (.bitNot (cost_seven true store))
private theorem cost_conjunction (choice : Bool) (store : Core.Store) :
    Cost choice store conjunction (.bool false) (if choice then 6 else 4) := by
  cases choice
  · exact .andFalse (cost_c false store)
  · exact .andTrue (cost_c true store) (.logicalNot (cost_c true store))
private theorem cost_disjunction (choice : Bool) (store : Core.Store) :
    Cost choice store disjunction (.bool true) (if choice then 4 else 6) := by
  cases choice
  · exact .orFalse (cost_c false store) (.logicalNot (cost_c false store))
  · exact .orTrue (cost_c true store)
private theorem cost_deep (choice : Bool) (store : Core.Store) :
    Cost choice store deepConjunction (.bool choice) (if choice then 8 else 4) := by
  cases choice
  · exact .andFalse (cost_c false store)
  · exact .andTrue (cost_c true store) (.logicalNot (.logicalNot (cost_c true store)))

theorem selected_and_skipped_branches_have_different_exact_costs (choice : Bool) (store : Core.Store) :
    Cost choice store selection (.word (if choice then seven.bitNot else seven)) (if choice then 6 else 4) ∧
    Cost choice store conjunction (.bool false) (if choice then 6 else 4) ∧
    Cost choice store disjunction (.bool true) (if choice then 4 else 6) ∧
    Cost choice store deepConjunction (.bool choice) (if choice then 8 else 4) :=
  ⟨cost_selection choice store, cost_conjunction choice store, cost_disjunction choice store, cost_deep choice store⟩

private theorem exact_boundaries {choice : Bool} {store : Core.Store} {source : Syntax.Expr}
    {value : Core.Value} {cost : Nat} {type : Core.Ty}
    (counted : Cost choice store source value cost)
    (typing : LocalExpressionHasType (inputs choice).names (inputs choice).context source type) :
    ∀ fuel, ((inputs choice).run? fuel source store = some (type, .done value store) ↔ cost ≤ fuel) ∧
      ((∃ suspended, (inputs choice).run? fuel source store = some (type, .outOfFuel suspended)) ↔ fuel < cost) := by
  obtain ⟨actualValue, actualCost, actualEvaluation, _, boundaries⟩ := LocalInputs.typed_cost_execution typing store
  obtain ⟨rfl, _, rfl⟩ := counted.deterministic actualEvaluation
  exact boundaries

theorem leaf_unary_and_binary_costs_are_actual_completion_and_exhaustion_thresholds
    (choice : Bool) (store : Core.Store) (fuel : Nat) :
    (((inputs choice).run? fuel sevenSource store = some (.word, .done (.word seven) store) ↔ 1 ≤ fuel) ∧
      ((∃ suspended, (inputs choice).run? fuel sevenSource store = some (.word, .outOfFuel suspended)) ↔ fuel < 1)) ∧
    (((inputs choice).run? fuel (neg (ref "c")) store = some (.bool, .done (.bool (!choice)) store) ↔ 3 ≤ fuel) ∧
      ((∃ suspended, (inputs choice).run? fuel (neg (ref "c")) store = some (.bool, .outOfFuel suspended)) ↔ fuel < 3)) ∧
    (((inputs choice).run? fuel (binary .bitXor (ref "w") sevenSource) store = some (.word, .done (.word .zero) store) ↔ 5 ≤ fuel) ∧
      ((∃ suspended, (inputs choice).run? fuel (binary .bitXor (ref "w") sevenSource) store = some (.word, .outOfFuel suspended)) ↔ fuel < 5)) := by
  refine ⟨exact_boundaries (cost_seven choice store) (.wordLiteral sevenMeaning) fuel,
    exact_boundaries (.logicalNot (cost_c choice store)) (.logicalNot (.identifier .head .head)) fuel, ?_⟩
  have wordTyped : LocalExpressionHasType (inputs choice).names (inputs choice).context (ref "w") .word :=
    .identifier (.tail (by change "c" ≠ "w"; decide) .head)
      (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
  simpa [binary] using exact_boundaries (.bitXor (cost_w choice store) (cost_seven choice store))
    (.bitXor wordTyped (.wordLiteral sevenMeaning)) fuel

theorem conditional_and_short_circuit_thresholds_follow_only_selected_costs
    (choice : Bool) (store : Core.Store) (fuel : Nat) :
    ((inputs choice).run? fuel selection store = some (.word, .done (.word (if choice then seven.bitNot else seven)) store) ↔
      (if choice then 6 else 4) ≤ fuel) ∧
    ((inputs choice).run? fuel conjunction store = some (.bool, .done (.bool false) store) ↔ (if choice then 6 else 4) ≤ fuel) ∧
    ((inputs choice).run? fuel disjunction store = some (.bool, .done (.bool true) store) ↔ (if choice then 4 else 6) ≤ fuel) ∧
    ((inputs choice).run? fuel deepConjunction store = some (.bool, .done (.bool choice) store) ↔ (if choice then 8 else 4) ≤ fuel) ∧
    ((∃ suspended, (inputs choice).run? fuel deepConjunction store = some (.bool, .outOfFuel suspended)) ↔
      fuel < (if choice then 8 else 4)) := by
  have cTyped : LocalExpressionHasType (inputs choice).names (inputs choice).context (ref "c") .bool := .identifier .head .head
  have deep := exact_boundaries (cost_deep choice store) (.logicalAnd cTyped (.logicalNot (.logicalNot cTyped))) fuel
  exact ⟨(exact_boundaries (cost_selection choice store)
      (.conditional cTyped (.bitNot (.wordLiteral sevenMeaning)) (.wordLiteral sevenMeaning)) fuel).1,
    (exact_boundaries (cost_conjunction choice store) (.logicalAnd cTyped (.logicalNot cTyped)) fuel).1,
    (exact_boundaries (cost_disjunction choice store) (.logicalOr cTyped (.logicalNot cTyped)) fuel).1,
    deep.1, deep.2⟩

theorem checked_zero_fuel_is_present_exhaustion_with_a_nonempty_store (choice : Bool) (store : Core.Store) :
    (inputs choice).run? 0 sevenSource (.word seven :: store) = some (.word, .outOfFuel
      (Core.State.initial (.word seven) (Resolved.LocalScope.values (inputs choice).environment) (.word seven :: store))) ∧
    (inputs choice).run? 1 sevenSource (.word seven :: store) = some (.word, .done (.word seven) (.word seven :: store)) := by
  have accepted : (inputs choice).check? sevenSource = some (.word seven, .word) :=
    elaborateLocalExpression?_complete (.wordLiteral sevenMeaning) .word .word
  exact ⟨by rw [LocalInputs.run?, accepted]; rfl,
    (exact_boundaries (cost_seven choice (.word seven :: store)) (.wordLiteral sevenMeaning) 1).1.mpr (Nat.le_refl _)⟩

theorem longer_literal_spelling_keeps_transition_cost_one (count : Nat) (store : Core.Store) :
    Cost true store ⟨span, .literal ⟨span, .decimal (String.ofList (List.replicate count '0' ++ ['7']))⟩⟩ (.word seven) 1 := by
  apply LocalExpressionEvaluatesWithCost.wordLiteral
  apply NumericLiteralDenotes.decimal
  · simp
  · have digit : NumericDigitsDenote .decimal ['7'] 0 7 :=
      .cons (.decimal (digit := 7) (by decide) (by decide)) .nil
    simpa [seven] using digit.leading_zeros count

theorem completed_runs_recover_the_unique_independent_source_cost
    (choice : Bool) (store finalStore : Core.Store) (fuel : Nat) (value : Core.Value)
    (completed : (inputs choice).run? fuel conjunction store = some (.bool, .done value finalStore)) :
    ∃ cost, LocalExpressionEvaluatesWithCost (inputs choice).names (inputs choice).environment
      store conjunction value finalStore cost ∧ cost = (if choice then 6 else 4) ∧ cost ≤ fuel ∧
      value = .bool false ∧ finalStore = store := by
  obtain ⟨_, cost, counted, enough⟩ := LocalInputs.run?_done_iff_typed_cost.mp completed
  obtain ⟨sameValue, sameStore, sameCost⟩ := counted.deterministic (cost_conjunction choice store)
  exact ⟨cost, counted, sameCost, enough, sameValue, sameStore⟩

private def skippedMissing : Syntax.Expr := branch (ref "c") sevenSource (ref "missing")
private def selectedWord : Syntax.Expr := binary .logicalAnd (ref "c") sevenSource
private theorem cost_missing (store : Core.Store) : Cost true store skippedMissing (.word seven) 4 :=
  .ifTrue (cost_c true store) (cost_seven true store)
private theorem cost_selected_word (store : Core.Store) : Cost true store selectedWord (.word seven) 4 :=
  .andTrue (cost_c true store) (cost_seven true store)

theorem raw_cost_does_not_imply_whole_checking_or_a_present_run (fuel : Nat) (store : Core.Store) :
    Cost true store skippedMissing (.word seven) 4 ∧ Cost true store selectedWord (.word seven) 4 ∧
    (inputs true).check? skippedMissing = none ∧ (inputs true).check? selectedWord = none ∧
    (inputs true).run? fuel skippedMissing store = none ∧ (inputs true).run? fuel selectedWord store = none := by
  have missingRejected : (inputs true).check? skippedMissing = none := by
    simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, skippedMissing, branch, ref,
      inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  have wordRejected : (inputs true).check? selectedWord = none := by
    apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    cases typing with | logicalAnd _ right => cases right
  exact ⟨cost_missing store, cost_selected_word store, missingRejected, wordRejected,
    (LocalInputs.run?_eq_none_iff fuel store).mpr missingRejected,
    (LocalInputs.run?_eq_none_iff fuel store).mpr wordRejected⟩

theorem existing_raw_evaluation_has_a_unique_positive_cost_without_resolution (store : Core.Store) :
    LocalExpressionEvaluates (inputs true).names (inputs true).environment store skippedMissing (.word seven) store ∧
    (∃ cost, Cost true store skippedMissing (.word seven) cost ∧ 0 < cost ∧ cost = 4) ∧
    ∀ value finalStore cost, LocalExpressionEvaluatesWithCost (inputs true).names (inputs true).environment
      store skippedMissing value finalStore cost → value = .word seven ∧ finalStore = store ∧ cost = 4 := by
  have ordinary : LocalExpressionEvaluates (inputs true).names (inputs true).environment store skippedMissing (.word seven) store :=
    .ifTrue (.identifier .head .head) (.wordLiteral sevenMeaning)
  obtain ⟨cost, counted⟩ := ordinary.exists_cost
  exact ⟨(cost_missing store).erase, ⟨cost, counted, counted.cost_pos, counted.cost_unique (cost_missing store)⟩,
    fun _ _ _ other => other.deterministic (cost_missing store)⟩

theorem unchecked_selected_word_has_an_exact_core_path_when_it_wholly_resolves
    (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 4
      ⟨.eval (.ifE (.var 0) (.word seven) (.bool false)) (Resolved.LocalScope.values (inputs true).environment),
        continuation, store⟩
      ⟨.ret (.word seven), continuation, store⟩ :=
  (cost_selected_word store).toStepsWithContinuation
    (.logicalAnd (.identifier .head) (.wordLiteral sevenMeaning)) (.ifE (.var .head) .word .bool) continuation

private def mismatchedNames : LocalNameTable := [("c", ⟨owner, 1⟩)]
private def mismatchedContext : Resolved.Context := [(⟨owner, 0⟩, .bool), (⟨owner, 1⟩, .bool)]
private def mismatchedEnvironment : Resolved.Environment := [(⟨owner, 1⟩, .bool true), (⟨owner, 0⟩, .bool false)]

theorem positional_boolean_types_do_not_replace_runtime_identity_alignment (store : Core.Store) :
    elaborateLocalExpression? mismatchedNames mismatchedContext (ref "c") = some (.var 1, .bool) ∧
    Core.EnvironmentHasTypes (Resolved.LocalScope.values mismatchedEnvironment) (Resolved.LocalScope.values mismatchedContext) ∧
    Resolved.LocalScope.ids mismatchedEnvironment ≠ Resolved.LocalScope.ids mismatchedContext ∧
    LocalExpressionEvaluatesWithCost mismatchedNames mismatchedEnvironment store (ref "c") (.bool true) store 1 ∧
    Core.runStateful 1 (Core.State.initial (.var 1) (Resolved.LocalScope.values mismatchedEnvironment) store) =
      .done (.bool false) store :=
  ⟨elaborateLocalExpression?_complete (.identifier .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) .head)),
    .cons .bool (.cons .bool .nil), by decide, .identifier .head .head, rfl⟩

end Tests.FrontendLocalExpressionCost
