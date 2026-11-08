import Solcore.Frontend.Fragments.Internal.LocalFunctionApplication
import Solcore.Core.Internal.PrimitiveLaws
import Solcore.Frontend.Fragments.Internal.LocalExpressions
import Solcore.Core.Machine
import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Core.Internal.LocalFragment
import Solcore.Core.Fuel
import Solcore.Frontend.Fragments.Internal.Foundations
import Solcore.Resolved.ExecutionProperties
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Resolved.Eval
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions
import Solcore.Frontend.Fragments.Internal.ReturnBodies

/-!
# Local expression tests

Parsed local expressions: fragments, references, inputs, renaming, negation and short circuits, with
source costs, store independence and resumption.
-/

section
-- leanmerge: from Solcore.Test.FrontendLocalExpressionCostInvarianceProperties
/-! ADR-0166: exact source costs and fixed-fuel observations survive the stated
transformations. Fresh same-name shadowing and suspended-state equality do not. -/

set_option autoImplicit false

namespace Tests.FrontendLocalExpressionCostInvariance

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"CostInvariance", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "cost-invariance.sol"⟩, 0, 1⟩
private def seven : Core.Word := ⟨7, by decide⟩
private def literal (payload : Syntax.CoreLiteralValue) : Syntax.Expr := ⟨span, .literal ⟨span, payload⟩⟩
private def sevenSource : Syntax.Expr := literal (.decimal "7")
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def neg (child : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .logicalNot⟩ child⟩
private def binary (op : Syntax.BinaryOp) (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, op⟩ right⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr := ⟨span, .conditional condition span left span right⟩
private def inputs (choice : Bool) : LocalInputs := LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool
private def extended (choice : Bool) : LocalInputs := (inputs choice).bindFresh owner "extra" .unit .unit .unit
private abbrev Cost (supplied : LocalInputs) (store : Core.Store) (source : Syntax.Expr) (value : Core.Value) (cost : Nat) :=
  LocalExpressionEvaluatesWithCost supplied.names supplied.environment store source value store cost
private theorem meaning : WordLiteralDenotes ⟨span, .decimal "7"⟩ seven :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 7) (by decide) (by decide)) .nil)
private theorem cost_c (choice : Bool) (store : Core.Store) :
    Cost (inputs choice) store (ref "c") (.bool choice) 1 := .identifier .head .head
private theorem cost_seven (supplied : LocalInputs) (store : Core.Store) :
    Cost supplied store sevenSource (.word seven) 1 := .wordLiteral meaning
private def source : Syntax.Expr := branch (binary .logicalAnd (ref "c") (neg (ref "c")))
  (binary .bitOr sevenSource sevenSource) (binary .bitXor sevenSource sevenSource)
private def required (choice : Bool) : Nat := if choice then 13 else 11
private theorem avoids : AvoidsLocalName "extra" source :=
  .conditional (.logicalAnd (.identifier (by decide)) (.logicalNot (.identifier (by decide))))
    (.bitOr .literal .literal) (.bitXor .literal .literal)
private theorem typed (choice : Bool) : LocalExpressionHasType (inputs choice).names (inputs choice).context source .word :=
  .conditional (.logicalAnd (.identifier .head .head) (.logicalNot (.identifier .head .head)))
    (.bitOr (.wordLiteral meaning) (.wordLiteral meaning)) (.bitXor (.wordLiteral meaning) (.wordLiteral meaning))
private theorem counted (choice : Bool) (store : Core.Store) : Cost (inputs choice) store source (.word .zero) (required choice) := by
  have left : LocalExpressionEvaluatesWithCost (inputs choice).names (inputs choice).environment store
      (binary .logicalAnd (ref "c") (neg (ref "c"))) (.bool false) store (if choice then 6 else 4) := by
    cases choice
    · exact .andFalse (cost_c false store)
    · exact .andTrue (cost_c true store) (.logicalNot (cost_c true store))
  have right : Cost (inputs choice) store (binary .bitXor sevenSource sevenSource) (.word (seven.bitXor seven)) 5 :=
    .bitXor (.wordLiteral meaning) (.wordLiteral meaning)
  cases choice <;> simpa [Cost, source, required, binary, branch] using LocalExpressionEvaluatesWithCost.ifFalse left right

theorem independently_counted_conditional_short_circuit_and_word_binary_survive_transformations
    (choice : Bool) (store : Core.Store) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) :
    Cost (inputs choice) store source (.word .zero) (required choice) ∧
    Cost (extended choice) store source (.word .zero) (required choice) ∧
    LocalExpressionEvaluatesWithCost (LocalNameTable.mapIds mapping (inputs choice).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice).environment) store source (.word .zero) store (required choice) :=
  ⟨counted choice store, (avoids.bindFresh_cost_iff (inputs choice) owner .unit .unit .unit).mpr (counted choice store),
    (localExpressionEvaluatesWithCost_mapIds_iff mapping injective).mpr (counted choice store)⟩

theorem arbitrary_values_stores_and_costs_are_preserved_and_reflected
    (choice : Bool) (initialStore finalStore : Core.Store) (value : Core.Value) (cost : Nat)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (LocalExpressionEvaluatesWithCost (extended choice).names (extended choice).environment initialStore source value finalStore cost ↔
      LocalExpressionEvaluatesWithCost (inputs choice).names (inputs choice).environment initialStore source value finalStore cost) ∧
    (LocalExpressionEvaluatesWithCost (LocalNameTable.mapIds mapping (inputs choice).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice).environment) initialStore source value finalStore cost ↔
      LocalExpressionEvaluatesWithCost (inputs choice).names (inputs choice).environment initialStore source value finalStore cost) :=
  ⟨avoids.bindFresh_cost_iff (inputs choice) owner .unit .unit .unit,
    localExpressionEvaluatesWithCost_mapIds_iff mapping injective⟩

theorem same_fuel_completed_values_and_exhaustion_presence_are_preserved
    (choice : Bool) (fuel : Nat) (type : Core.Ty) (value : Core.Value) (store finalStore : Core.Store) :
    ((extended choice).run? fuel source (.word seven :: store) = some (type, .done value finalStore) ↔
      (inputs choice).run? fuel source (.word seven :: store) = some (type, .done value finalStore)) ∧
    ((∃ newState, (extended choice).run? fuel source (.word seven :: store) = some (type, .outOfFuel newState)) ↔
      ∃ oldState, (inputs choice).run? fuel source (.word seven :: store) = some (type, .outOfFuel oldState)) :=
  ⟨avoids.bindFresh_run_done_at_fuel_iff (inputs choice) owner .unit .unit .unit,
    avoids.bindFresh_run_outOfFuel_iff (inputs choice) owner .unit .unit .unit⟩

theorem preserved_exhaustion_has_the_independently_fixed_threshold (choice : Bool) (fuel : Nat) (store : Core.Store) :
    (∃ suspended, (extended choice).run? fuel source store = some (.word, .outOfFuel suspended)) ↔ fuel < required choice := by
  constructor
  · intro exhausted
    have old := (avoids.bindFresh_run_outOfFuel_iff (inputs choice) owner .unit .unit .unit).mp exhausted
    obtain ⟨_, value, cost, evaluation, short⟩ := LocalInputs.run?_outOfFuel_iff_typed_cost.mp old
    have same := evaluation.cost_unique (counted choice store)
    exact same ▸ short
  · intro short
    apply (avoids.bindFresh_run_outOfFuel_iff (inputs choice) owner .unit .unit .unit).mpr
    exact LocalInputs.run?_outOfFuel_iff_typed_cost.mpr ⟨typed choice, .word .zero, required choice, counted choice store, short⟩

private def skippedMissing : Syntax.Expr := branch (ref "c") sevenSource (ref "missing")
private theorem avoids_missing : AvoidsLocalName "extra" skippedMissing :=
  .conditional (.identifier (by decide)) .literal (.identifier (by decide))
private theorem missing_cost (store : Core.Store) : Cost (inputs true) store skippedMissing (.word seven) 4 := by
  exact .ifTrue (cost_c true store) (cost_seven (inputs true) store)

theorem skipped_missing_cost_is_invariant_while_checking_still_fails
    (value : Core.Value) (cost fuel : Nat) (store finalStore : Core.Store)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    Cost (extended true) store skippedMissing (.word seven) 4 ∧
    (LocalExpressionEvaluatesWithCost (extended true).names (extended true).environment store skippedMissing value finalStore cost ↔
      LocalExpressionEvaluatesWithCost (inputs true).names (inputs true).environment store skippedMissing value finalStore cost) ∧
    (LocalExpressionEvaluatesWithCost (LocalNameTable.mapIds mapping (inputs true).names)
      (Resolved.LocalScope.mapIds mapping (inputs true).environment) store skippedMissing value finalStore cost ↔
      LocalExpressionEvaluatesWithCost (inputs true).names (inputs true).environment store skippedMissing value finalStore cost) ∧
    (inputs true).check? skippedMissing = none ∧ (extended true).run? fuel skippedMissing store = none := by
  have rejected : (inputs true).check? skippedMissing = none := by
    simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, skippedMissing, branch, ref,
      inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  have stillRejected : (extended true).check? skippedMissing = none := by
    simpa only [extended, rejected, Option.map_none] using avoids_missing.check_bindFresh_eq (inputs true) owner .unit .unit .unit
  exact ⟨(avoids_missing.bindFresh_cost_iff (inputs true) owner .unit .unit .unit).mpr (missing_cost store),
    avoids_missing.bindFresh_cost_iff (inputs true) owner .unit .unit .unit,
    localExpressionEvaluatesWithCost_mapIds_iff mapping injective, rejected,
    (LocalInputs.run?_eq_none_iff fuel store).mpr stillRejected⟩

theorem every_invalid_literal_avoids_names_but_has_no_cost_or_run
    (payload : Syntax.CoreLiteralValue) (rejected : interpretWordLiteral? ⟨span, payload⟩ = none)
    (value : Core.Value) (cost fuel : Nat) (store finalStore : Core.Store) :
    AvoidsLocalName "extra" (literal payload) ∧
    (LocalExpressionEvaluatesWithCost (extended true).names (extended true).environment store (literal payload) value finalStore cost ↔
      LocalExpressionEvaluatesWithCost (inputs true).names (inputs true).environment store (literal payload) value finalStore cost) ∧
    (¬ ∃ result final count, LocalExpressionEvaluatesWithCost (inputs true).names (inputs true).environment store (literal payload) result final count) ∧
    (extended true).run? fuel (literal payload) store = none := by
  have avoided : AvoidsLocalName "extra" (literal payload) := .literal
  refine ⟨avoided, avoided.bindFresh_cost_iff (inputs true) owner .unit .unit .unit, ?_, ?_⟩
  · rintro ⟨result, final, count, evaluation⟩
    cases evaluation with
    | wordLiteral wordMeaning =>
        have impossible := interpretWordLiteral?_complete wordMeaning
        rw [rejected] at impossible
        cases impossible
  · apply (LocalInputs.run?_eq_none_iff fuel store).mpr
    simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, literal, rejected]

private def shadowed : LocalInputs := (inputs false).bindFresh owner "c" .bool (.bool true) .bool
private def counter : Syntax.Expr := branch (ref "c") (neg (neg (neg (ref "c")))) (ref "c")
private theorem old_counter (store : Core.Store) : Cost (inputs false) store counter (.bool false) 4 := by
  exact .ifFalse (cost_c false store) (cost_c false store)
private theorem new_counter (store : Core.Store) : Cost shadowed store counter (.bool false) 10 := by
  have head : Cost shadowed store (ref "c") (.bool true) 1 := .identifier .head .head
  exact .ifTrue head (.logicalNot (.logicalNot (.logicalNot head)))
private theorem old_typed : LocalExpressionHasType (inputs false).names (inputs false).context counter .bool :=
  .conditional (.identifier .head .head) (.logicalNot (.logicalNot (.logicalNot (.identifier .head .head)))) (.identifier .head .head)
private theorem new_typed : LocalExpressionHasType shadowed.names shadowed.context counter .bool :=
  .conditional (.identifier .head .head) (.logicalNot (.logicalNot (.logicalNot (.identifier .head .head)))) (.identifier .head .head)

theorem same_spelling_fresh_identity_can_keep_value_but_change_cost (store : Core.Store) :
    shadowed.ids = [⟨owner, 1⟩, ⟨owner, 0⟩] ∧
    (¬ AvoidsLocalName "c" counter) ∧ Cost (inputs false) store counter (.bool false) 4 ∧
    Cost shadowed store counter (.bool false) 10 ∧
    (inputs false).run? 4 counter store = some (.bool, .done (.bool false) store) ∧
    (∃ suspended, shadowed.run? 4 counter store = some (.bool, .outOfFuel suspended)) ∧
    shadowed.run? 10 counter store = some (.bool, .done (.bool false) store) := by
  refine ⟨rfl, ?_, old_counter store, new_counter store,
    LocalInputs.run?_done_iff_typed_cost.mpr ⟨old_typed, 4, old_counter store, Nat.le_refl _⟩,
    LocalInputs.run?_outOfFuel_iff_typed_cost.mpr ⟨new_typed, .bool false, 10, new_counter store, by decide⟩,
    LocalInputs.run?_done_iff_typed_cost.mpr ⟨new_typed, 10, new_counter store, Nat.le_refl _⟩⟩
  intro avoidance
  cases avoidance with
  | conditional condition _ _ => cases condition with | identifier different => exact different rfl

private def literalExtended : LocalInputs := LocalInputs.empty.bindFresh owner "extra" .unit .unit .unit
theorem equal_exhaustion_presence_does_not_equate_suspended_states (store : Core.Store) :
    LocalInputs.empty.run? 0 sevenSource store = some (.word, .outOfFuel (Core.State.initial (.word seven) [] store)) ∧
    literalExtended.run? 0 sevenSource store = some (.word, .outOfFuel (Core.State.initial (.word seven) [.unit] store)) ∧
    Core.State.initial (.word seven) [] store ≠ Core.State.initial (.word seven) [.unit] store ∧
    ((∃ newState, literalExtended.run? 0 sevenSource store = some (.word, .outOfFuel newState)) ↔
      ∃ oldState, LocalInputs.empty.run? 0 sevenSource store = some (.word, .outOfFuel oldState)) := by
  have oldChecked : LocalInputs.empty.check? sevenSource = some (.word seven, .word) :=
    elaborateLocalExpression?_complete (.wordLiteral meaning) .word .word
  have newChecked : literalExtended.check? sevenSource = some (.word seven, .word) :=
    elaborateLocalExpression?_complete (.wordLiteral meaning) .word .word
  refine ⟨by rw [LocalInputs.run?, oldChecked]; rfl, by rw [LocalInputs.run?, newChecked]; rfl, ?_,
    (AvoidsLocalName.literal (name := "extra")).bindFresh_run_outOfFuel_iff LocalInputs.empty owner .unit .unit .unit⟩
  intro same
  cases same

end Tests.FrontendLocalExpressionCostInvariance
end

section
-- leanmerge: from Solcore.Test.FrontendLocalExpressionCostProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendLocalExpressionEvaluatorProperties
/-! Independent original-syntax paths fix values and costs before direct execution.
Raw lookup/selected control flow need no typing, and checked paths keep their
separate whole-expression, identity-order and actual-value premises. -/
set_option autoImplicit false
namespace Tests.FrontendLocalExpressionEvaluator
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Direct", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "direct.sol"⟩, 223, 8⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def binary (op : Syntax.BinaryOp) (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, op⟩ right⟩
private def unary (op : Syntax.UnaryOp) (source : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, op⟩ source⟩
private def choose (c t f : Syntax.Expr) : Syntax.Expr := ⟨span, .conditional c span t span f⟩
private def table : LocalNameTable := [("l", id 7), ("r", id 42)]
private def env (left right : Core.Value) : Resolved.Environment := [(id 7, left), (id 42, right)]
private theorem leftRaw (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (env left right) store (ref "l") left store 1 := .identifier .head .head
private theorem rightRaw (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (env left right) store (ref "r") right store 1 :=
  .identifier (.tail (by decide) .head) (.tail (by decide) .head)
private def nest : Nat → Syntax.Expr
  | 0 => ref "r"
  | n + 1 => choose (ref "l") ⟨span, .group (nest n)⟩ (ref "missing")
private theorem nestRaw (n : Nat) {names : LocalNameTable} {values : Resolved.Environment}
    (value : Core.Value) (store : Core.Store)
    (condition : LocalExpressionEvaluatesWithCost names values store (ref "l") (.bool true) store 1)
    (leaf : LocalExpressionEvaluatesWithCost names values store (ref "r") value store 1) :
    LocalExpressionEvaluatesWithCost names values store (nest n) value store (3 * n + 1) := by
  induction n with
  | zero => exact leaf
  | succ n ih =>
      have count : 3 * (n + 1) + 1 = 1 + (3 * n + 1) + 2 := by omega
      rw [count]
      exact .ifTrue condition (.group ih)

theorem arbitrary_depth_selected_paths_keep_original_rows_values_and_exact_cost
    (n : Nat) {names : LocalNameTable} {values : Resolved.Environment} (value : Core.Value) (store : Core.Store)
    (condition : LocalExpressionEvaluatesWithCost names values store (ref "l") (.bool true) store 1)
    (leaf : LocalExpressionEvaluatesWithCost names values store (ref "r") value store 1) :
    evaluateLocalExpressionWithCost? names values (nest n) = some (value, 3 * n + 1) ∧
    ∀ replacement, LocalExpressionEvaluatesWithCost names values replacement (nest n) value replacement (3 * n + 1) := by
  have evaluated := evaluateLocalExpressionWithCost?_complete (nestRaw n value store condition leaf)
  exact ⟨evaluated, fun replacement => evaluateLocalExpressionWithCost?_sound evaluated replacement⟩

theorem duplicate_names_and_ids_keep_first_matches_without_alignment (value hidden : Core.Value) (store final : Core.Store) :
    let names := [("r", id 42), ("r", id 7), ("l", id 7)]
    let values := [(id 42, value), (id 42, hidden), (id 7, .bool true)]
    evaluateLocalExpressionWithCost? names values (ref "r") = some (value, 1) ∧
    (evaluateLocalExpressionWithCost? names values (ref "r")).map Prod.fst = some value ∧
    (LocalExpressionEvaluatesWithCost names values store (ref "r") value final 1 ↔ final = store) := by
  dsimp
  have raw : LocalExpressionEvaluatesWithCost [("r", id 42), ("r", id 7), ("l", id 7)]
      [(id 42, value), (id 42, hidden), (id 7, .bool true)] store (ref "r") value store 1 := .identifier .head .head
  have evaluated := (evaluateLocalExpressionWithCost?_iff store).mpr raw
  exact ⟨evaluated, (evaluateLocalExpressionWithCost?_value_iff store).mpr raw.erase, by
    rw [localExpressionEvaluatesWithCost_iff_evaluate, evaluated]; simp⟩

private inductive Strict where | add | sub | mul | div | mod | band | bor | bxor | gt | lt | eq | ne | le | ge
private def op : Strict → Syntax.BinaryOp
  | .add => .add | .sub => .subtract | .mul => .multiply | .div => .divide | .mod => .modulo
  | .band => .bitAnd | .bor => .bitOr | .bxor => .bitXor | .gt => .greater | .lt => .less
  | .eq => .equal | .ne => .notEqual | .le => .lessEqual | .ge => .greaterEqual
private def answer (kind : Strict) (left right : Core.Word) : Core.Value :=
  match kind with
  | .add => .word (left.add right) | .sub => .word (left.sub right) | .mul => .word (left.mul right)
  | .div => .word (left.udiv right) | .mod => .word (left.umod right)
  | .band => .word (left.bitAnd right) | .bor => .word (left.bitOr right) | .bxor => .word (left.bitXor right)
  | .gt => .bool (decide (left > right)) | .lt => .bool (decide (left < right)) | .eq => .bool (left == right)
  | .ne => .bool (!(left == right)) | .le => .bool (!(decide (left > right))) | .ge => .bool (!(decide (left < right)))
private def overhead : Strict → Nat | .ne | .le => 5 | .lt => 9 | .ge => 11 | _ => 3
private theorem strictRaw (kind : Strict) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (env (.word left) (.word right)) store
      (binary (op kind) (ref "l") (ref "r")) (answer kind left right) store (2 + overhead kind) := by
  have l := leftRaw (.word left) (.word right) store
  have r := rightRaw (.word left) (.word right) store
  cases kind
  · exact .add l r
  · exact .subtract l r
  · exact .multiply l r
  · exact .divide l r
  · exact .modulo l r
  · exact .bitAnd l r
  · exact .bitOr l r
  · exact .bitXor l r
  · exact .greater l r
  · exact .less l r
  · exact .equal l r
  · exact .notEqual l r
  · exact .lessEqual l r
  · exact .greaterEqual l r

theorem all_fourteen_strict_word_operators_have_independent_values_and_overheads
    (kind : Strict) (left right : Core.Word) (store : Core.Store) :
    evaluateLocalWordBinaryWithCost? (op kind) left right = some (answer kind left right, overhead kind) ∧
    LocalExpressionEvaluatesWithCost table (env (.word left) (.word right)) store
      (binary (op kind) (ref "l") (ref "r")) (answer kind left right) store (2 + overhead kind) ∧
    evaluateLocalExpressionWithCost? table (env (.word left) (.word right))
      (binary (op kind) (ref "l") (ref "r")) = some (answer kind left right, 2 + overhead kind) :=
  ⟨by cases kind <;> rfl, strictRaw kind left right store, evaluateLocalExpressionWithCost?_complete (strictRaw kind left right store)⟩

theorem unary_shapes_and_selected_short_circuits_forward_actual_opaque_values
    (flag : Bool) (word : Core.Word) (value : Core.Value) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env (.bool flag) (.word word)) (unary .logicalNot (ref "l")) = some (.bool (!flag), 3) ∧
    evaluateLocalExpressionWithCost? table (env (.bool flag) (.word word)) (unary .bitNot (ref "r")) = some (.word word.bitNot, 3) ∧
    evaluateLocalExpressionWithCost? table (env (.bool true) value) (binary .logicalAnd (ref "l") (ref "r")) = some (value, 4) ∧
    evaluateLocalExpressionWithCost? table (env (.bool false) value) (binary .logicalOr (ref "l") (ref "r")) = some (value, 4) ∧
    elaborateLocalExpression? table [(id 7, .bool), (id 42, .unit)] (binary .logicalAnd (ref "l") (ref "r")) = none ∧
    elaborateLocalExpression? table [(id 7, .bool), (id 42, .unit)] (binary .logicalOr (ref "l") (ref "r")) = none :=
  ⟨evaluateLocalExpressionWithCost?_complete (.logicalNot (leftRaw _ _ store)),
    evaluateLocalExpressionWithCost?_complete (.bitNot (rightRaw _ _ store)),
    evaluateLocalExpressionWithCost?_complete (.andTrue (leftRaw _ _ store) (rightRaw _ _ store)),
    evaluateLocalExpressionWithCost?_complete (.orFalse (leftRaw _ _ store) (rightRaw _ _ store)),
    by simp only [elaborateLocalExpression?, binary, ref, resolveLocalExpression?]; rfl,
    by simp only [elaborateLocalExpression?, binary, ref, resolveLocalExpression?]; rfl⟩

theorem skipped_children_need_no_meaning_but_whole_checking_still_does
    (value : Core.Value) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env (.bool false) value) (binary .logicalAnd (ref "l") (ref "missing")) = some (.bool false, 4) ∧
    evaluateLocalExpressionWithCost? table (env (.bool true) value) (binary .logicalOr (ref "l") (ref "missing")) = some (.bool true, 4) ∧
    evaluateLocalExpressionWithCost? table (env (.bool false) value) (choose (ref "l") (ref "missing") (ref "r")) = some (value, 4) ∧
    resolveLocalExpression? table (choose (ref "l") (ref "missing") (ref "r")) = none :=
  ⟨evaluateLocalExpressionWithCost?_complete (.andFalse (leftRaw _ _ store)),
    evaluateLocalExpressionWithCost?_complete (.orTrue (leftRaw _ _ store)),
    evaluateLocalExpressionWithCost?_complete (.ifFalse (leftRaw _ _ store) (rightRaw _ _ store)),
    by simp [resolveLocalExpression?, choose, ref, table, LocalNameTable.lookup?]⟩

theorem strict_missing_or_wrong_shaped_operands_do_not_gain_a_raw_path
    (kind : Strict) (word : Core.Word) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env .unit (.word word)) (binary (op kind) (ref "l") (ref "r")) = none ∧
    evaluateLocalExpressionWithCost? table (env (.word word) .unit) (binary (op kind) (ref "l") (ref "r")) = none ∧
    ¬ ∃ value cost, LocalExpressionEvaluatesWithCost table (env (.word .zero) (.word .zero)) store
      (binary .divide (ref "missing") (ref "r")) value store cost := by
  refine ⟨?_, ?_, (evaluateLocalExpressionWithCost?_eq_none_iff store).mp (by
    simp [evaluateLocalExpressionWithCost?, binary, ref, table, LocalNameTable.lookup?])⟩
  all_goals cases kind <;> simp [evaluateLocalExpressionWithCost?, binary, op, ref, table, env, id, LocalNameTable.lookup?, Resolved.LocalScope.lookup?]

private def literal (value : Syntax.CoreLiteralValue) : Syntax.Expr := ⟨span, .literal ⟨span, value⟩⟩
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
theorem strict_literal_payloads_and_zero_divisors_do_not_change_source_cost
    (word : Core.Word) (store : Core.Store) :
    evaluateLocalExpressionWithCost? [] [] (literal (.decimal "0")) = some (.word .zero, 1) ∧
    evaluateLocalExpressionWithCost? [] [] (literal (.decimal "12x")) = none ∧
    evaluateLocalExpressionWithCost? [] [] (literal (.hexadecimal "0Xff")) = none ∧
    evaluateLocalExpressionWithCost? [] [] (literal (.string "0")) = none ∧
    evaluateLocalExpressionWithCost? table (env (.word word) (.word .zero)) (binary .divide (ref "l") (ref "r")) = some (.word .zero, 5) ∧
    evaluateLocalExpressionWithCost? table (env (.word word) (.word .zero)) (binary .modulo (ref "l") (ref "r")) = some (.word .zero, 5) := by
  refine ⟨evaluateLocalExpressionWithCost?_complete (.wordLiteral (store := store) zeroMeaning),
    by simp only [evaluateLocalExpressionWithCost?, literal]; decide,
    by simp only [evaluateLocalExpressionWithCost?, literal]; decide,
    by simp only [evaluateLocalExpressionWithCost?, literal]; decide, ?_, ?_⟩
  · simpa [answer, overhead, op, Core.Word.udiv_zero] using evaluateLocalExpressionWithCost?_complete (strictRaw .div word .zero store)
  · simpa [answer, overhead, op, Core.Word.umod_zero] using evaluateLocalExpressionWithCost?_complete (strictRaw .mod word .zero store)

private def context : Resolved.Context := [(id 7, .word), (id 42, .word)]
private def subtraction := binary .subtract (ref "l") (ref "r")
private def subtractionCore : Core.Expr := .binary .wordSub (.var 0) (.var 1)
private theorem checked : elaborateLocalExpression? table context subtraction = some (subtractionCore, .word) :=
  elaborateLocalExpression?_complete (.subtract (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.binary (.var .head) (.var (.tail (by decide) .head))) (.binary (.var .head) (.var (.tail (by decide) .head)))
private theorem subOutput (left right : Core.Word) :
    evaluateLocalExpressionWithCost? table (env (.word left) (.word right)) subtraction = some (.word (left.sub right), 5) :=
  evaluateLocalExpressionWithCost?_complete (strictRaw .sub left right [])

theorem independently_checked_subtraction_retains_continuations_and_all_fuel
    (left right : Core.Word) (store final : Core.Store) (fuel : Nat) (continuation : List Core.Frame) :
    Core.Steps 5 ⟨.eval subtractionCore [.word left, .word right], continuation, store⟩
      ⟨.ret (.word (left.sub right)), continuation, store⟩ ∧
    (Core.runStateful fuel (Core.State.initial subtractionCore [.word left, .word right] store) =
      .done (.word (left.sub right)) store ↔ 5 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (Core.State.initial subtractionCore [.word left, .word right] store) =
      .outOfFuel checkpoint) ↔ fuel < 5) ∧
    (Core.runStateful fuel (Core.State.initial subtractionCore [.word left, .word right] store) =
      .done (.word (left.sub right)) final ↔ final = store ∧ 5 ≤ fuel) := by
  refine ⟨evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation (subOutput left right) checked rfl continuation,
    evaluateLocalExpressionWithCost?_checked_runStateful_done_iff (subOutput left right) checked rfl,
    evaluateLocalExpressionWithCost?_checked_runStateful_outOfFuel_iff (subOutput left right) checked rfl, ?_⟩
  have reflected := elaborateLocalExpression?_run_done_iff_evaluator (environment := env (.word left) (.word right))
      (initialStore := store) (finalStore := final) (value := .word (left.sub right)) (fuel := fuel) checked rfl
  rw [subOutput] at reflected
  simpa [env, Resolved.LocalScope.values] using reflected

private def inputs (left right : Core.Word) : LocalInputs :=
  ⟨[⟨"l", id 7, .word, .word left, .word⟩, ⟨"r", id 42, .word, .word right, .word⟩], by change [id 7, id 42].Nodup; decide⟩
private theorem inputTyped (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context subtraction .word :=
  .subtract (.identifier .head .head) (.identifier (.tail (by change "l" ≠ "r"; decide) .head)
    (.tail (by change id 7 ≠ id 42; decide) .head))

theorem actual_typed_input_wrappers_recover_the_independent_exact_cost
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 5 subtraction store = some (.word, .done (.word (left.sub right)) store) ∧
    (∃ checkpoint, (inputs left right).run? 4 subtraction store = some (.word, .outOfFuel checkpoint)) ∧
    ∀ fuel, ((inputs left right).run? fuel subtraction store = some (.word, .done (.word (left.sub right)) store) ↔ 5 ≤ fuel) ∧
      ((∃ checkpoint, (inputs left right).run? fuel subtraction store = some (.word, .outOfFuel checkpoint)) ↔ fuel < 5) := by
  refine ⟨LocalInputs.run?_done_iff_evaluator.mpr ⟨inputTyped left right, rfl, 5, subOutput left right, by decide⟩,
    LocalInputs.run?_outOfFuel_iff_evaluator.mpr ⟨inputTyped left right, .word (left.sub right), 5, subOutput left right, by decide⟩, ?_⟩
  obtain ⟨value, cost, output, _, thresholds⟩ := LocalInputs.typed_evaluator_execution (inputTyped left right) store
  have exactPair := (subOutput left right).symm.trans output
  cases Option.some.inj exactPair
  exact thresholds

theorem typed_existence_needs_actual_values_and_raw_projection_preserves_them
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) (store : Core.Store) :
    (∃ actual cost, evaluateLocalExpressionWithCost? table (env value .unit) (ref "l") = some (actual, cost) ∧
      Core.ValueHasType actual type) ∧
    (∃ cost, evaluateLocalExpressionWithCost? table (env value .unit) (ref "l") = some (value, cost)) := by
  have accepted : elaborateLocalExpression? table [(id 7, type), (id 42, .unit)] (ref "l") = some (.var 0, type) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  exact ⟨elaborateLocalExpression?_typed_evaluator_exists accepted rfl (.cons typed (.cons .unit .nil)),
    (evaluateLocalExpressionWithCost?_exists_cost_iff store).mpr (leftRaw value .unit store).erase⟩

theorem aligned_untyped_values_are_not_typed_results_and_misalignment_changes_lookup (store : Core.Store) :
    elaborateLocalExpression? table context (ref "l") = some (.var 0, .word) ∧
    evaluateLocalExpressionWithCost? table (env (.bool true) (.word .zero)) (ref "l") = some (.bool true, 1) ∧
    Core.Steps 1 (Core.State.initial (.var 0) [.bool true, .word .zero] store) (Core.State.final (.bool true) store) ∧
    (¬ Core.ValueHasType (.bool true) .word) ∧
    evaluateLocalExpressionWithCost? table [(id 42, .word .zero), (id 7, .word .maximum)] (ref "l") = some (.word .maximum, 1) ∧
    Core.runStateful 1 (Core.State.initial (.var 0) [.word .zero, .word .maximum] store) = .done (.word .zero) store := by
  have accepted : elaborateLocalExpression? table context (ref "l") = some (.var 0, .word) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  have output := evaluateLocalExpressionWithCost?_complete (leftRaw (.bool true) (.word .zero) store)
  exact ⟨accepted, output, evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation output accepted rfl [],
    (by intro bad; cases bad), evaluateLocalExpressionWithCost?_complete
      (.identifier (store := store) .head (.tail (by decide) .head)), rfl⟩

private def pending (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word right), [.binaryApply .wordSub (.word left)], store⟩
theorem actual_ordered_checkpoint_resumes_but_cannot_drop_its_pending_operation
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    Core.runStateful 4 (Core.State.initial subtractionCore [.word left, .word right] store) = .outOfFuel (pending left right store) ∧
    Core.Steps 1 (pending left right store) (Core.State.final (.word (left.sub right)) store) ∧
    Core.runStateful additional (pending left right store) =
      Core.runStateful (4 + additional) (Core.State.initial subtractionCore [.word left, .word right] store) ∧
    Core.runStateful 0 (pending left right store) = .outOfFuel (pending left right store) ∧
    Core.runStateful 0 (Core.State.final (.word right) store) = .done (.word right) store ∧
    Core.HasType [.word, .word] (.binary .wordSub (.var 1) (.var 0)) .word ∧
    elaborateLocalExpression? table context subtraction ≠ some (.binary .wordSub (.var 1) (.var 0), .word) := by
  have exhausted : Core.runStateful 4 (Core.State.initial subtractionCore [.word left, .word right] store) =
      .outOfFuel (pending left right store) := rfl
  refine ⟨exhausted, ((strictRaw .sub left right store).checked_residual_of_outOfFuel checked rfl exhausted).2,
    Core.runStateful_resume exhausted additional, rfl, rfl, .binary (.var rfl) (.var rfl), ?_⟩
  rw [checked]
  intro bad
  cases bad

theorem selected_unsupported_forms_and_wrong_boolean_guards_remain_absent (word : Core.Word) :
    evaluateLocalExpressionWithCost? table (env (.word word) .unit) ⟨span, .call (ref "r") ⟨span, []⟩⟩ = none ∧
    evaluateLocalExpressionWithCost? table (env .unit (.word word)) (choose (ref "l") (ref "r") (ref "r")) = none ∧
    evaluateLocalExpressionWithCost? table (env (.bool true) .unit) (binary .logicalAnd (ref "l") (ref "missing")) = none ∧
    evaluateLocalExpressionWithCost? table (env (.word word) .unit) (unary .logicalNot (ref "l")) = none ∧
    evaluateLocalExpressionWithCost? table (env (.bool true) .unit) (unary .bitNot (ref "l")) = none ∧
    evaluateLocalWordBinaryWithCost? .logicalAnd word word = none ∧
    evaluateLocalWordBinaryWithCost? .logicalOr word word = none := by
  simp [evaluateLocalExpressionWithCost?, evaluateLocalWordBinaryWithCost?, unary, binary, choose, ref, table, env, LocalNameTable.lookup?, Resolved.LocalScope.lookup?]

theorem arbitrary_depth_has_actual_opaque_instances_despite_unselected_rejection
    (depth location : Nat) (captured : Core.Word) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env (.bool true) (.cellRef .word location)) (nest depth) =
      some (.cellRef .word location, 3 * depth + 1) ∧
    evaluateLocalExpressionWithCost? table (env (.bool true) (.closure .bool .word (.var 1) [.word captured])) (nest depth) =
      some (.closure .bool .word (.var 1) [.word captured], 3 * depth + 1) ∧
    resolveLocalExpression? table (nest (depth + 1)) = none := by
  refine ⟨evaluateLocalExpressionWithCost?_complete (nestRaw depth _ store (leftRaw _ _ store) (rightRaw _ _ store)),
    evaluateLocalExpressionWithCost?_complete (nestRaw depth _ store (leftRaw _ _ store) (rightRaw _ _ store)), ?_⟩
  apply resolveLocalExpression?_eq_none_iff.mpr
  rintro ⟨resolved, resolution⟩
  cases resolution with
  | conditional _ _ missing =>
      have impossible := missing.complete
      simp [resolveLocalExpression?, ref, table, LocalNameTable.lookup?] at impossible

end Tests.FrontendLocalExpressionEvaluator
end

section
-- leanmerge: from Solcore.Test.FrontendLocalExpressionProperties
/-! Canonical conditional consumers distinguish whole-expression static checks
from selected-branch evaluation. All names and types remain caller supplied. -/

set_option autoImplicit false

namespace Tests.FrontendLocalExpression

open Solcore Solcore.Frontend

private def modulePath : Workspace.ModulePath := ⟨[⟨"Conditional", by decide⟩], by decide⟩
private def localId (index : Nat) : Resolved.LocalId := ⟨⟨⟨.main, modulePath⟩, 0⟩, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "conditional.sol"⟩, 0, 4⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def group (inner : Syntax.Expr) : Syntax.Expr := ⟨span, .group inner⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .conditional condition span left span right⟩
private def names : LocalNameTable :=
  [("cond", localId 1), ("left", localId 2), ("right", localId 3), ("word", localId 4)]
private def context : Resolved.Context :=
  [(localId 0, .unit), (localId 1, .bool), (localId 2, .bool), (localId 3, .bool), (localId 4, .word)]
private def environment (choice : Bool) : Resolved.Environment :=
  [(localId 0, .unit), (localId 1, .bool choice), (localId 2, .bool false),
    (localId 3, .bool true), (localId 4, .word Core.Word.zero)]
private def simple : Syntax.Expr :=
  group (branch (group (ref "cond")) (group (ref "left")) (ref "right"))
private def resolvedSimple : Resolved.Expr := .ifE (.var (localId 1)) (.var (localId 2)) (.var (localId 3))
private def simpleCore : Core.Expr := .ifE (.var 1) (.var 2) (.var 3)

private theorem left_named : LocalNameTable.Lookup names "left" (localId 2) := .tail (by decide) .head
private theorem right_named : LocalNameTable.Lookup names "right" (localId 3) :=
  .tail (by decide) (.tail (by decide) .head)
private theorem simple_resolved : ResolvesLocalExpression names simple resolvedSimple :=
  .group (.conditional (.group (.identifier .head)) (.group (.identifier left_named)) (.identifier right_named))
private theorem simple_typed : LocalExpressionHasType names context simple .bool :=
  .group (.conditional (.group (.identifier .head (.tail (by decide) .head)))
    (.group (.identifier left_named (.tail (by decide) (.tail (by decide) .head))))
    (.identifier right_named (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem simple_lowered : Resolved.Lowers (Resolved.LocalScope.ids context) resolvedSimple simpleCore :=
  .ifE (.var (.tail (by decide) .head))
    (.var (.tail (by decide) (.tail (by decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))

theorem grouped_conditional_has_exact_static_result :
    ResolvesLocalExpression names simple resolvedSimple ∧
    LocalExpressionHasType names context simple .bool ∧
    elaborateLocalExpression? names context simple = some (simpleCore, .bool) :=
  ⟨simple_resolved, simple_typed, elaborateLocalExpression?_complete simple_resolved
    simple_lowered (simple_resolved.preserves_type simple_typed)⟩

private theorem selected_left (right : Syntax.Expr) (store : Core.Store) :
    LocalExpressionEvaluates names (environment true) store
      (branch (ref "cond") (ref "left") right) (.bool false) store :=
  .ifTrue (.identifier .head (.tail (by decide) .head))
    (.identifier left_named (.tail (by decide) (.tail (by decide) .head)))

theorem both_boolean_conditions_select_the_expected_value (choice : Bool) (store : Core.Store) :
    LocalExpressionEvaluates names (environment choice) store simple (.bool (!choice)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (environment choice)) store simpleCore (.bool (!choice)) store := by
  have evaluation : LocalExpressionEvaluates names (environment choice) store simple (.bool (!choice)) store := by
    cases choice
    · exact .group (.ifFalse (.group (.identifier .head (.tail (by decide) .head)))
        (.identifier right_named (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
    · exact .group (.ifTrue (.group (.identifier .head (.tail (by decide) .head)))
        (.group (.identifier left_named (.tail (by decide) (.tail (by decide) .head)))))
  exact ⟨evaluation, (simple_resolved.core_evaluates_iff
    (environment := environment choice) simple_lowered).mp evaluation⟩

private def wordCondition : Syntax.Expr := branch (ref "word") (ref "left") (ref "right")
private def mismatchedBranches : Syntax.Expr := branch (ref "cond") (ref "left") (ref "word")

private theorem word_condition_rejected : elaborateLocalExpression? names context wordCondition = none := by
  simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
    wordCondition, branch, ref, Resolved.Expr.lower?, Resolved.LocalScope.ids,
    Resolved.LocalScope.values, Resolved.LocalScope.index?, localId]
  intro type inferred
  cases Core.infer_sound inferred with
  | ifE condition _ _ => cases condition with | var found => cases found

private theorem mismatched_branches_rejected :
    elaborateLocalExpression? names context mismatchedBranches = none := by
  simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
    mismatchedBranches, branch, ref, Resolved.Expr.lower?, Resolved.LocalScope.ids,
    Resolved.LocalScope.values, Resolved.LocalScope.index?, localId]
  intro type inferred
  cases Core.infer_sound inferred with
  | ifE _ left right =>
      cases left with
      | var found => cases found; cases right with | var found => cases found

theorem word_condition_and_mismatched_branches_have_no_type :
    elaborateLocalExpression? names context wordCondition = none ∧
    elaborateLocalExpression? names context mismatchedBranches = none ∧
    (¬ ∃ type, LocalExpressionHasType names context wordCondition type) ∧
    (¬ ∃ type, LocalExpressionHasType names context mismatchedBranches type) :=
  ⟨word_condition_rejected, mismatched_branches_rejected,
    elaborateLocalExpression?_eq_none_iff.mp word_condition_rejected,
    elaborateLocalExpression?_eq_none_iff.mp mismatched_branches_rejected⟩

private def unsupported : Syntax.Expr := ⟨span, .literal ⟨span, .string "7"⟩⟩
private def withSkipped (right : Syntax.Expr) : Syntax.Expr := branch (ref "cond") (ref "left") right

/-- Raw dynamic rules inspect only the selected left branch; all three different
right-branch defects still prevent a checked whole-expression result. -/
theorem unselected_bad_branches_are_static_failures (store : Core.Store) :
    elaborateLocalExpression? names context (withSkipped (ref "missing")) = none ∧
    elaborateLocalExpression? names context (withSkipped unsupported) = none ∧
    elaborateLocalExpression? names context (withSkipped wordCondition) = none ∧
    LocalExpressionEvaluates names (environment true) store
      (withSkipped (ref "missing")) (.bool false) store ∧
    LocalExpressionEvaluates names (environment true) store (withSkipped unsupported) (.bool false) store ∧
    LocalExpressionEvaluates names (environment true) store (withSkipped wordCondition) (.bool false) store := by
  refine ⟨?_, ?_, ?_, selected_left _ store, selected_left _ store, selected_left _ store⟩
  all_goals simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
    withSkipped, unsupported, interpretWordLiteral?, numericLiteralValue?,
    wordCondition, branch, ref, Resolved.Expr.lower?, Resolved.LocalScope.ids,
    Resolved.LocalScope.values, Resolved.LocalScope.index?, localId]
  intro type inferred
  cases Core.infer_sound inferred with
  | ifE _ _ right =>
      cases right with
      | ifE condition _ _ => cases condition with | var found => cases found

theorem duplicate_names_select_the_first_conditional_binding :
    elaborateLocalExpression? (("cond", localId 2) :: names) context simple =
      some (.ifE (.var 2) (.var 2) (.var 3), .bool) := by
  simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
    simple, group, branch, ref, Resolved.Expr.lower?, Resolved.LocalScope.ids,
    Resolved.LocalScope.values, Resolved.LocalScope.index?, localId]
  have inferred : Core.infer? [.unit, .bool, .bool, .bool, .word]
      (.ifE (.var 2) (.var 2) (.var 3)) = some .bool :=
    Core.infer_complete (.ifE (.var rfl) (.var rfl) (.var rfl))
  simp only [inferred, Option.bind_some]

theorem conditional_punctuation_and_outer_ranges_do_not_change_elaboration
    (outer question colon : Syntax.SourceSpan) :
    elaborateLocalExpression? names context
      ⟨outer, .conditional (ref "cond") question (ref "left") colon (ref "right")⟩ =
        some (simpleCore, .bool) :=
  elaborateLocalExpression?_complete
    (.conditional (.identifier .head) (.identifier left_named) (.identifier right_named))
    simple_lowered (simple_resolved.preserves_type simple_typed)

/-- The three lookups use nonzero positions. The fourth transition reads the
selected branch; at fuel three its initial state is retained exactly. -/
theorem simple_conditional_exact_fuel (choice : Bool) (store : Core.Store) :
    Core.runStateful 3 (Core.State.initial simpleCore (Resolved.LocalScope.values (environment choice)) store) =
      .outOfFuel (Core.State.initial (.var (if choice then 2 else 3))
        (Resolved.LocalScope.values (environment choice)) store) ∧
    ∀ extra, Core.runStateful (extra + 4)
      (Core.State.initial simpleCore (Resolved.LocalScope.values (environment choice)) store) =
        .done (.bool (!choice)) store := by
  cases choice <;> constructor
  · rfl
  · intro extra; simp [Core.runStateful, Core.State.initial, Core.advance,
      simpleCore, Resolved.LocalScope.values, environment]
  · rfl
  · intro extra; simp [Core.runStateful, Core.State.initial, Core.advance,
      simpleCore, Resolved.LocalScope.values, environment]

private def nested : Syntax.Expr := group (branch (ref "cond") simple (ref "right"))
private def nestedCore : Core.Expr := .ifE (.var 1) simpleCore (.var 3)

theorem unselected_nested_conditionals_add_no_execution_fuel (store : Core.Store) :
    elaborateLocalExpression? names context (withSkipped nested) =
      some (.ifE (.var 1) (.var 2) nestedCore, .bool) ∧
    Core.runStateful 3 (Core.State.initial (.ifE (.var 1) (.var 2) nestedCore)
      (Resolved.LocalScope.values (environment true)) store) =
      .outOfFuel (Core.State.initial (.var 2) (Resolved.LocalScope.values (environment true)) store) ∧
    ∀ extra, Core.runStateful (extra + 4)
      (Core.State.initial (.ifE (.var 1) (.var 2) nestedCore)
        (Resolved.LocalScope.values (environment true)) store) = .done (.bool false) store := by
  refine ⟨?_, rfl, ?_⟩
  · simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
      withSkipped, nested, nestedCore, simple, simpleCore, group, branch, ref, Resolved.Expr.lower?,
      Resolved.LocalScope.ids, Resolved.LocalScope.values, Resolved.LocalScope.index?, localId]
    have inferred : Core.infer? [.unit, .bool, .bool, .bool, .word]
        (.ifE (.var 1) (.var 2) (.ifE (.var 1) simpleCore (.var 3))) = some .bool :=
      Core.infer_complete (.ifE (.var rfl) (.var rfl)
        (.ifE (.var rfl) (.ifE (.var rfl) (.var rfl) (.var rfl)) (.var rfl)))
    simp only [simpleCore] at inferred
    simp only [inferred, Option.bind_some]
  · intro extra
    simp [Core.runStateful, Core.State.initial, Core.advance, Resolved.LocalScope.values, environment]

end Tests.FrontendLocalExpression
end

section
-- leanmerge: from Solcore.Test.FrontendLocalFragmentProperties
/-! Exact original-source witnesses supply membership; independent positional
paths retain values and costs, not identical suspended environments. -/
set_option autoImplicit false
namespace Tests.FrontendLocalFragment
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LocalFragment", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "local-fragment.sol"⟩, 17, 9⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def chain : Bool → List String → String → Syntax.Block
  | _, [], previous => returned previous
  | annotated, name :: rest, previous =>
      ⟨span, ⟨span, .letDecl ⟨span, name⟩ (if annotated then some annotation else none)
        (some (ref previous))⟩ :: (chain (!annotated) rest name).value⟩
private def core : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var index) (core n 0)
private def seed (type : Core.Ty) := LocalTypeInputs.empty.bindFresh owner "seed" type
private theorem chain_eta (flag : Bool) (names : List String) (previous : String) :
    (⟨span, (chain flag names previous).value⟩ : Syntax.Block) = chain flag names previous := by cases names <;> rfl
private theorem elaborated (flag : Bool) (names : List String) (previous : String) (type : Core.Ty)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr) (index : Nat) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var index)) (typed : Resolved.HasType initial.context resolved type) :
    TypedLetReturnTreeElaborates (types type) owner initial (chain flag names previous) (core names.length index) type := by
  induction names generalizing flag previous initial resolved index with
  | nil =>
      simp only [chain, List.length_nil, core]
      exact .single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typed)
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      have tail := ih (!flag) name (initial.bindFresh owner name type) _ 0 parts.2 (by
        intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩)
        (.identifier .head) (.var .head) (.var .head)
      cases flag
      · exact .inferred (fresh name (by simp)) resolution lowered typed (by simpa only [chain_eta] using tail)
      · exact .binding (.named .head) (fresh name (by simp)) resolution lowered typed (by simpa only [chain_eta] using tail)
private theorem seedElab (flag : Bool) (names : List String) (type : Core.Ty)
    (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed type) (chain flag names "seed") (core names.length 0) type := by
  apply elaborated flag names "seed" type (seed type) _ 0 distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head
private theorem path (n index : Nat) (values : Core.Environment) (value : Core.Value)
    (found : values[index]? = some value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*n+1) ⟨.eval (core n index) values, k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing index values k with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      have steps := Core.Steps.cons .enterLet (.cons (.var found) (.cons .bindLet (ih 0 (value :: values) rfl k)))
      simpa [core, Nat.mul_add, Nat.add_assoc] using steps
private theorem typedCore (n index : Nat) (context : Core.Context) (type : Core.Ty)
    (found : context[index]? = some type) (definitions : Core.DataEnvironment) :
    Core.HasType context (core n index) type definitions := by
  induction n generalizing index context with
  | zero => exact .var found
  | succ n ih => exact .letE (.var found) (ih 0 (type :: context) rfl)

theorem original_mixed_lists_determine_fragment_membership
    (flag : Bool) (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed type) (chain flag names "seed") (core names.length 0) type ∧
    Core.Expr.LocalFragment (core names.length 0) ∧
    elaborateTypedLetReturnTree? (types type) owner (seed type) (chain flag names "seed") = some (core names.length 0, type) := by
  have original := seedElab flag names type distinct fresh
  exact ⟨original, original.localFragment, original.complete⟩

theorem expression_singleton_and_terminal_tree_keep_their_exact_children (type : Core.Ty) :
    Core.Expr.LocalFragment (.var 0) ∧ Core.Expr.LocalFragment (.ifE (.var 0) (.var 0) (.var 0)) ∧
    Core.Expr.LocalFragment .unit := by
  have leaf : ReturnBodyElaborates (seed type).names (seed type).context (returned "seed") (.var 0) type :=
    .expression (.identifier .head) (.var .head) (.var .head)
  have expression : elaborateLocalExpression? (seed type).names (seed type).context (ref "seed") = some (.var 0, type) :=
    leaf.complete
  have boolLeaf : ReturnBodyElaborates (seed .bool).names (seed .bool).context (returned "seed") (.var 0) .bool :=
    .expression (.identifier .head) (.var .head) (.var .head)
  have tree : TerminalReturnTreeElaborates (seed .bool).names (seed .bool).context
      ⟨span, [⟨span, .ifThen (ref "seed") (returned "seed") (some (returned "seed"))⟩]⟩
      (.ifE (.var 0) (.var 0) (.var 0)) .bool :=
    .conditional (.identifier .head) (.var .head) (.var .head) (.single boolLeaf) (.single boolLeaf)
  have bare : ReturnBodyElaborates (seed type).names (seed type).context
      ⟨span, [⟨span, .returnStmt none⟩]⟩ .unit .unit := .bare
  exact ⟨elaborateLocalExpression?_localFragment expression, tree.localFragment, bare.localFragment⟩

theorem nominal_static_transport_needs_no_runtime_inhabitant
    (nominal : Core.DataTypeId) (inserted : Core.Ty) (definitions : Core.DataEnvironment) :
    Core.HasType [inserted, .namedData nominal] ((core 2 0).weakenAt 0) (.namedData nominal) definitions ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  have fragment := (seedElab false ["x", "y"] (.namedData nominal) (by decide) (by decide)).localFragment
  refine ⟨(typedCore 2 0 [.namedData nominal] _ rfl definitions).weakenAt_zero_localFragment fragment inserted, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem retained_type_prefix_preserves_and_reflects_full_inference
    (flag : Bool) (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (leading suffix : Core.Context) (inserted result : Core.Ty) (definitions : Core.DataEnvironment) :
    (Core.HasType (leading ++ inserted :: suffix) ((core names.length 0).weakenAt leading.length) result definitions ↔
      Core.HasType (leading ++ suffix) (core names.length 0) result definitions) ∧
    Core.infer? (leading ++ inserted :: suffix) ((core names.length 0).weakenAt leading.length) definitions =
      Core.infer? (leading ++ suffix) (core names.length 0) definitions := by
  have fragment := (seedElab flag names type distinct fresh).localFragment
  exact ⟨fragment.hasType_insert_iff leading suffix inserted, fragment.infer_insert leading suffix inserted definitions⟩

theorem arbitrary_original_positions_transport_exact_paths_both_ways
    (flag : Bool) (names : List String) (previous : String) (type : Core.Ty)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr) (index : Nat) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var index)) (typed : Resolved.HasType initial.context resolved type)
    (leading suffix : Core.Environment) (value inserted : Core.Value)
    (found : (leading ++ suffix)[index]? = some value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*names.length+1)
      ⟨.eval ((core names.length index).weakenAt leading.length) (leading ++ inserted :: suffix), k, store⟩ ⟨.ret value, k, store⟩ ∧
    Core.Steps (3*names.length+1) ⟨.eval (core names.length index) (leading ++ suffix), k, store⟩ ⟨.ret value, k, store⟩ := by
  have fragment := (elaborated flag names previous type initial resolved index distinct fresh resolution lowered typed).localFragment
  have original := path names.length index (leading ++ suffix) value found store []
  have shifted := fragment.steps_insert leading suffix inserted original []
  exact ⟨fragment.steps_insert leading suffix inserted original k, fragment.steps_reflect_insert leading suffix inserted shifted k⟩

theorem a_retained_row_really_shifts_the_original_initializer
    (type : Core.Ty) (value inserted : Core.Value) (choice : Bool) (store : Core.Store) (k : List Core.Frame) :
    TypedLetReturnTreeElaborates (types type) owner ((seed type).bindFresh owner "kept" .bool)
      (chain false ["copy"] "seed") (.letE (.var 1) (.var 0)) type ∧
    ((core 1 1).weakenAt 1) = .letE (.var 2) (.var 0) ∧
    Core.Steps 4 ⟨.eval (.letE (.var 2) (.var 0)) [.bool choice, inserted, value], k, store⟩ ⟨.ret value, k, store⟩ := by
  have original : TypedLetReturnTreeElaborates (types type) owner ((seed type).bindFresh owner "kept" .bool)
      (chain false ["copy"] "seed") (core 1 1) type := by
    apply elaborated false ["copy"] "seed" type _ _ 1 (by decide)
    · intro name member
      have same : name = "copy" := List.mem_singleton.mp member
      subst name
      change "copy" ∉ ["kept", "seed"]
      decide
    · exact .identifier (.tail (by change "kept" ≠ "seed"; decide) .head)
    · exact .var (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
    · exact .var (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
  have shifted := original.localFragment.steps_insert [.bool choice] [value] inserted
    (path 1 1 [.bool choice, value] value rfl store []) k
  exact ⟨original, by simp [core, Core.Expr.weakenAt], by simpa [core, Core.Expr.weakenAt] using shifted⟩

theorem insertion_keeps_arbitrary_final_store_iff_without_asserting_evaluation
    (flag : Bool) (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (leading suffix : Core.Environment) (inserted value : Core.Value) (initialStore finalStore : Core.Store) (cost : Nat) :
    (Core.Evaluates (leading ++ inserted :: suffix) initialStore ((core names.length 0).weakenAt leading.length) value finalStore ↔
      Core.Evaluates (leading ++ suffix) initialStore (core names.length 0) value finalStore) ∧
    (Core.Steps cost (Core.State.initial ((core names.length 0).weakenAt leading.length) (leading ++ inserted :: suffix) initialStore)
      (Core.State.final value finalStore) ↔ Core.Steps cost (Core.State.initial (core names.length 0) (leading ++ suffix) initialStore)
      (Core.State.final value finalStore)) := by
  have fragment := (seedElab flag names type distinct fresh).localFragment
  exact ⟨fragment.evaluates_insert_iff leading suffix inserted, fragment.steps_insert_iff leading suffix inserted⟩

theorem preexisting_cells_and_closures_are_not_created_or_inspected
    (location : Core.Location) (word : Core.Word) (inserted : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    Core.ValueHasType (.cellRef .word location) (.cell .word) ∧
    Core.ValueHasType (.closure .bool .word (.var 1) [.word word]) (.function .bool .word) ∧
    Core.Steps 7 ⟨.eval ((core 2 0).weakenAt 0) [inserted, .cellRef .word location], k, store⟩ ⟨.ret (.cellRef .word location), k, store⟩ ∧
    Core.Steps 7 ⟨.eval ((core 2 0).weakenAt 0) [inserted, .closure .bool .word (.var 1) [.word word]], k, store⟩
      ⟨.ret (.closure .bool .word (.var 1) [.word word]), k, store⟩ := by
  have cellFragment := (seedElab false ["x", "y"] (.cell .word) (by decide) (by decide)).localFragment
  have closureFragment := (seedElab false ["x", "y"] (.function .bool .word) (by decide) (by decide)).localFragment
  exact ⟨.cellRef, .closure (.cons .word .nil) (.var rfl),
    (path 2 0 [_] _ rfl store []).weakenAt_zero_localFragment cellFragment inserted k,
    (path 2 0 [_] _ rfl store []).weakenAt_zero_localFragment closureFragment inserted k⟩

private def checkpoint (value : Core.Value) (environment : Core.Environment) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody (.var 0) environment], store⟩
theorem exact_cost_does_not_identify_suspended_environments
    (value inserted : Core.Value) (store : Core.Store) (additional : Nat) :
    Core.runStateful 2 (Core.State.initial (core 1 0) [value] store) = .outOfFuel (checkpoint value [value] store) ∧
    Core.runStateful 2 (Core.State.initial ((core 1 0).weakenAt 0) [inserted, value] store) =
      .outOfFuel (checkpoint value [inserted, value] store) ∧
    checkpoint value [value] store ≠ checkpoint value [inserted, value] store ∧
    Core.Steps 2 (checkpoint value [value] store) (Core.State.final value store) ∧
    Core.Steps 2 (checkpoint value [inserted, value] store) (Core.State.final value store) ∧
    Core.runStateful (2 + additional) (Core.State.initial ((core 1 0).weakenAt 0) [inserted, value] store) =
      Core.runStateful additional (checkpoint value [inserted, value] store) := by
  have exhausted : Core.runStateful 2 (Core.State.initial ((core 1 0).weakenAt 0) [inserted, value] store) =
      .outOfFuel (checkpoint value [inserted, value] store) := by simp only [core, Core.Expr.weakenAt]; rfl
  refine ⟨rfl, exhausted, ?_, .cons .bindLet (.cons (.var rfl) .refl), .cons .bindLet (.cons (.var rfl) .refl),
    (Core.runStateful_resume exhausted additional).symm⟩
  intro same
  have lengths := congrArg (fun state => state.continuation) same
  simp only [checkpoint, List.cons.injEq, Core.Frame.letBody.injEq] at lengths
  cases lengths.1.2.2

theorem retained_continuation_endpoints_need_not_be_completed_runs (store : Core.Store) :
    Core.Steps 4 ⟨.eval ((core 1 0).weakenAt 0) [.unit, .bool true], [.unaryApply .wordNot], store⟩
      ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ ∧
    Core.runStateful 0 ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot (.bool true)) ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ := by
  have fragment := (seedElab false ["x"] .bool (by decide) (by decide)).localFragment
  exact ⟨(path 1 0 [.bool true] _ rfl store []).weakenAt_zero_localFragment fragment .unit _, rfl⟩

theorem typing_and_membership_do_not_replace_exact_source_provenance (type : Core.Ty) (definitions : Core.DataEnvironment) :
    Core.HasType [type] (.var 0) type definitions ∧ Core.Expr.LocalFragment (.var 0) ∧
    ¬ TypedLetReturnTreeElaborates (types type) owner (seed type) (chain false ["x"] "seed") (.var 0) type ∧
    Core.HasType [type] (.first (.pair (.var 0) .unit)) type definitions ∧
    ¬ Core.Expr.LocalFragment (.first (.pair (.var 0) .unit)) := by
  refine ⟨.var rfl, .var, ?_, .first (.pair (.var rfl) .unit), fun impossible => by cases impossible⟩
  intro competing
  cases (competing.result_unique (seedElab false ["x"] type (by decide) (by decide))).1

private def skipped : Syntax.Block :=
  ⟨span, [⟨span, .ifThen (ref "seed") (returned "seed") (some (returned "missing"))⟩]⟩
theorem a_selected_raw_value_does_not_check_the_other_written_arm (type : Core.Ty) (store : Core.Store) :
    TypedLetReturnTreeEvaluates owner (seed type).names [(Resolved.freshLocalId owner [], .bool true)] store skipped (.bool true) store ∧
    elaborateTypedLetReturnTree? [] owner (seed type) skipped = none ∧
    Core.Expr.LocalFragment (.ifE (.var 0) (.var 0) (.var 99)) ∧
    Core.Evaluates [.bool true] store (.ifE (.var 0) (.var 0) (.var 99)) (.bool true) store ∧
    ¬ Core.Expr.LocalFragment (.ifE (.bool true) (.var 0) (.first (.pair (.var 0) .unit))) := by
  refine ⟨.ifTrue (.identifier .head .head) (.single (.expression (.identifier .head .head))), ?_,
    .ifE .var .var .var, .ifTrue (.var rfl) (.var rfl), ?_⟩
  case refine_2 =>
    intro fragment
    cases fragment with
    | ifE _ _ other => cases other
  apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
  rintro ⟨_, typed⟩
  cases typed with
  | single child => cases child
  | conditional _ _ other =>
      cases other with
      | single child =>
          cases child with
          | expression child =>
              cases child with
              | identifier named _ =>
                  have impossible := LocalNameTable.lookup?_iff.mpr named
                  change none = some _ at impossible
                  cases impossible

theorem fragment_membership_does_not_make_indices_valid (index : Nat) (value : Core.Value) (store finalStore : Core.Store) :
    Core.Expr.LocalFragment (.var index) ∧ Core.infer? [] (.var index) = none ∧
    ¬ Core.Evaluates [] store (.var index) value finalStore := by
  refine ⟨.var, by cases index <;> rfl, ?_⟩
  intro evaluation
  cases evaluation with
  | var found => simp at found

end Tests.FrontendLocalFragment
end

section
-- leanmerge: from Solcore.Test.FrontendLocalIdentityRenamingProperties
/-! Simultaneous identity relabeling leaves spellings, positional Core, values,
and complete machine results unchanged. Injectivity and allocation boundaries
are exercised separately rather than treated as source binding policies. -/

set_option autoImplicit false

namespace Tests.FrontendLocalIdentityRenaming

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"IdentityRenaming", by decide⟩], by decide⟩⟩, 0⟩
private def localId (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def shift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex + 10 }
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  cases left
  cases right
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases owners
  cases indices
  rfl
private def span : Syntax.SourceSpan := ⟨⟨.main, "identity-renaming.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def neg (operand : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .logicalNot⟩ operand⟩
private def andE (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .logicalAnd⟩ right⟩
private def orE (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .logicalOr⟩ right⟩
private def inputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "b" .bool (.bool true) .bool).bindFresh
    owner "a" .bool (.bool (!choice)) .bool).bindFresh owner "a" .bool (.bool choice) .bool
private def renamed (choice : Bool) : LocalInputs := (inputs choice).mapIds shift shift_injective
private def source : Syntax.Expr :=
  ⟨span, .conditional (neg (ref "a")) span (andE (ref "b") (ref "a")) span (orE (ref "a") (ref "b"))⟩
private def core : Core.Expr := .ifE (.unary .boolNot (.var 0))
  (.ifE (.var 2) (.var 0) (.bool false)) (.ifE (.var 0) (.bool true) (.var 2))
private theorem names_ne : "a" ≠ "b" := by decide
private theorem ids20_ne : localId 2 ≠ localId 0 := by decide
private theorem ids10_ne : localId 1 ≠ localId 0 := by decide
private theorem checked (choice : Bool) : (inputs choice).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete
    (.conditional (.logicalNot (.identifier .head))
      (.logicalAnd (.identifier (.tail names_ne (.tail names_ne .head))) (.identifier .head))
      (.logicalOr (.identifier .head) (.identifier (.tail names_ne (.tail names_ne .head)))))
    (.ifE (.unary (.var .head)) (.ifE (.var (.tail ids20_ne (.tail ids10_ne .head))) (.var .head) .bool)
      (.ifE (.var .head) .bool (.var (.tail ids20_ne (.tail ids10_ne .head)))))
    (.ifE (.unary (.var .head)) (.ifE (.var (.tail ids20_ne (.tail ids10_ne .head))) (.var .head) .bool)
      (.ifE (.var .head) .bool (.var (.tail ids20_ne (.tail ids10_ne .head)))))

theorem offset_is_injective_and_keeps_same_name_shadowing (choice : Bool) (store : Core.Store) :
    Function.Injective shift ∧ (inputs choice).ids = [localId 2, localId 1, localId 0] ∧
    (renamed choice).ids = [localId 12, localId 11, localId 10] ∧
    LocalExpressionEvaluates (renamed choice).names (renamed choice).environment store (ref "a") (.bool choice) store :=
  ⟨shift_injective, rfl, rfl, .identifier .head .head⟩

theorem boolean_forms_keep_exact_core_and_typing (choice : Bool) (type : Core.Ty) :
    (inputs choice).check? source = some (core, .bool) ∧
    (renamed choice).check? source = some (core, .bool) ∧
    (LocalExpressionHasType (renamed choice).names (renamed choice).context source type ↔
      LocalExpressionHasType (inputs choice).names (inputs choice).context source type) :=
  ⟨checked choice, ((inputs choice).check?_mapIds shift shift_injective source).trans (checked choice),
    (inputs choice).hasType_mapIds_iff shift shift_injective⟩

theorem same_fuel_preserves_complete_suspended_and_done_results (choice : Bool) (store : Core.Store) :
    (∀ fuel, (renamed choice).run? fuel source store = (inputs choice).run? fuel source store) ∧
    (renamed choice).run? 8 source store = some (.bool, .outOfFuel
      (Core.State.initial (if choice then .bool true else .var 0)
        (Resolved.LocalScope.values (inputs choice).environment) store)) ∧
    (renamed choice).run? 9 source store = some (.bool, .done (.bool choice) store) := by
  refine ⟨fun fuel => (inputs choice).run?_mapIds shift shift_injective fuel source store, ?_, ?_⟩
  · rw [renamed, LocalInputs.run?_mapIds, LocalInputs.run?, checked]; cases choice <;> rfl
  · rw [renamed, LocalInputs.run?_mapIds, LocalInputs.run?, checked]; cases choice <;> rfl

private def unsupported : Syntax.Expr := ⟨span, .literal ⟨span, .string "7"⟩⟩
private def badRights : List Syntax.Expr := [ref "missing", unsupported]
private theorem bad_check (right : Syntax.Expr) (member : right ∈ badRights) :
    (inputs false).check? (andE (ref "a") right) = none := by
  simp only [badRights, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, andE, ref, unsupported,
    interpretWordLiteral?, numericLiteralValue?,
    inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

theorem skipped_failed_syntax_keeps_raw_evaluation_iff_and_check_failure
    (value : Core.Value) (initialStore finalStore : Core.Store) :
    ∀ right ∈ badRights,
      LocalExpressionEvaluates (inputs false).names (inputs false).environment initialStore
        (andE (ref "a") right) (.bool false) initialStore ∧
      (LocalExpressionEvaluates (renamed false).names (renamed false).environment initialStore
        (andE (ref "a") right) value finalStore ↔
        LocalExpressionEvaluates (inputs false).names (inputs false).environment initialStore
          (andE (ref "a") right) value finalStore) ∧
      (inputs false).check? (andE (ref "a") right) = none ∧
      (renamed false).check? (andE (ref "a") right) = none := by
  intro right member
  exact ⟨.andFalse (.identifier .head .head), (inputs false).evaluates_mapIds_iff shift shift_injective,
    bad_check right member,
    ((inputs false).check?_mapIds shift shift_injective _).trans (bad_check right member)⟩

private def aliases : LocalNameTable := [("a", localId 0), ("b", localId 0), ("a", localId 1)]
private def rawContext : Resolved.Context := [(localId 0, .bool), (localId 1, .bool)]
private def aliasValues : Resolved.Environment := [(localId 0, .bool false), (localId 1, .bool true)]

theorem raw_aliases_and_repeated_names_are_preserved (value : Core.Value) (initialStore finalStore : Core.Store) :
    (LocalNameTable.mapIds shift aliases).lookup? "a" = some (localId 10) ∧
    (LocalNameTable.mapIds shift aliases).lookup? "b" = some (localId 10) ∧
    elaborateLocalExpression? (LocalNameTable.mapIds shift aliases)
      (Resolved.LocalScope.mapIds shift rawContext) (ref "b") = some (.var 0, .bool) ∧
    (LocalExpressionEvaluates (LocalNameTable.mapIds shift aliases) (Resolved.LocalScope.mapIds shift aliasValues)
      initialStore (ref "b") value finalStore ↔ LocalExpressionEvaluates aliases aliasValues initialStore (ref "b") value finalStore) := by
  have accepted : elaborateLocalExpression? aliases rawContext (ref "b") = some (.var 0, .bool) :=
    elaborateLocalExpression?_complete (.identifier (.tail names_ne .head)) (.var .head) (.var .head)
  exact ⟨rfl, rfl, (elaborateLocalExpression?_mapIds shift shift_injective aliases rawContext _).trans accepted,
    localExpressionEvaluates_mapIds_iff shift shift_injective⟩

private def merge (_ : Resolved.LocalId) : Resolved.LocalId := localId 0
private def distinctNames : LocalNameTable := [("a", localId 0), ("b", localId 1)]
private def distinctValues : Resolved.Environment := [(localId 0, .bool true), (localId 1, .bool false)]

/-- Positional Boolean typing does not detect identity capture by a merging map. -/
theorem merging_distinct_ids_changes_core_position_and_value (store : Core.Store) :
    (¬ Function.Injective merge) ∧
    Core.EnvironmentHasTypes (Resolved.LocalScope.values (Resolved.LocalScope.mapIds merge distinctValues))
      (Resolved.LocalScope.values (Resolved.LocalScope.mapIds merge rawContext)) ∧
    elaborateLocalExpression? distinctNames rawContext (ref "b") = some (.var 1, .bool) ∧
    elaborateLocalExpression? (LocalNameTable.mapIds merge distinctNames)
      (Resolved.LocalScope.mapIds merge rawContext) (ref "b") = some (.var 0, .bool) ∧
    LocalExpressionEvaluates distinctNames distinctValues store (ref "b") (.bool false) store ∧
    LocalExpressionEvaluates (LocalNameTable.mapIds merge distinctNames)
      (Resolved.LocalScope.mapIds merge distinctValues) store (ref "b") (.bool true) store ∧
    Core.runStateful 1 (Core.State.initial (.var 1) (Resolved.LocalScope.values distinctValues) store) =
      .done (.bool false) store ∧
    Core.runStateful 1 (Core.State.initial (.var 0)
      (Resolved.LocalScope.values (Resolved.LocalScope.mapIds merge distinctValues)) store) = .done (.bool true) store := by
  refine ⟨?_, .cons .bool (.cons .bool .nil), ?_, ?_,
    .identifier (.tail names_ne .head) (.tail (Ne.symm ids10_ne) .head),
    .identifier (.tail names_ne .head) .head, rfl, rfl⟩
  · intro injective
    exact ids10_ne (injective (show merge (localId 1) = merge (localId 0) from rfl))
  · exact elaborateLocalExpression?_complete (.identifier (.tail names_ne .head))
      (.var (.tail (Ne.symm ids10_ne) .head)) (.var (.tail (Ne.symm ids10_ne) .head))
  · exact elaborateLocalExpression?_complete (.identifier (.tail names_ne .head)) (.var .head) (.var .head)

theorem merged_duplicate_ids_cannot_form_a_typed_bundle :
    Resolved.LocalScope.ids (Resolved.LocalScope.mapIds merge rawContext) = [localId 0, localId 0] ∧
    ¬ ∃ bundle : LocalInputs, bundle.ids = Resolved.LocalScope.ids (Resolved.LocalScope.mapIds merge rawContext) := by
  refine ⟨rfl, ?_⟩
  rintro ⟨bundle, same⟩
  have distinct := bundle.ids_nodup
  change bundle.ids.Nodup at distinct
  rw [same] at distinct
  change [localId 0, localId 0].Nodup at distinct
  simp at distinct

private def allocated : LocalInputs := LocalInputs.empty.bindFresh owner "x" .unit .unit .unit
private def mappedThenAllocated : LocalInputs :=
  (LocalInputs.empty.mapIds shift shift_injective).bindFresh owner "x" .unit .unit .unit

theorem allocation_does_not_commute_with_identity_offset :
    (allocated.mapIds shift shift_injective).ids = [localId 10] ∧
    mappedThenAllocated.ids = [localId 0] ∧ allocated.mapIds shift shift_injective ≠ mappedThenAllocated := by
  refine ⟨rfl, rfl, ?_⟩
  intro same
  have different := congrArg LocalInputs.ids same
  change [localId 10] = [localId 0] at different
  exact (by decide : [localId 10] ≠ [localId 0]) different

end Tests.FrontendLocalIdentityRenaming
end

section
-- leanmerge: from Solcore.Test.FrontendLocalInputsExtensionProperties
/-! Adding an unused spelling shifts positional Core references without
changing existing identity-based meanings. Fresh IDs alone do not suffice. -/

set_option autoImplicit false

namespace Tests.FrontendLocalInputsExtension

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"Extension", by decide⟩], by decide⟩⟩, 0⟩
private def localId (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "extension.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .conditional condition span left span right⟩
private def inputs (choice : Bool) : LocalInputs :=
  (((LocalInputs.empty.bindFresh owner "w" .word (.word Core.Word.zero) .word).bindFresh
    owner "e" .bool (.bool true) .bool).bindFresh owner "t" .bool (.bool false) .bool).bindFresh
      owner "c" .bool (.bool choice) .bool
private def extended (choice : Bool) : LocalInputs :=
  (inputs choice).bindFresh owner "extra" .unit .unit .unit
private def names : LocalNameTable :=
  [("c", localId 3), ("t", localId 2), ("e", localId 1), ("w", localId 0)]
private def context : Resolved.Context :=
  [(localId 3, .bool), (localId 2, .bool), (localId 1, .bool), (localId 0, .word)]
private def source : Syntax.Expr := branch (ref "c") (ref "t") (ref "e")
private def resolved : Resolved.Expr :=
  .ifE (.var (localId 3)) (.var (localId 2)) (.var (localId 1))
private def core : Core.Expr := .ifE (.var 0) (.var 1) (.var 2)
private def shifted : Core.Expr := .ifE (.var 1) (.var 2) (.var 3)
private theorem avoids_source : AvoidsLocalName "extra" source :=
  .conditional (.identifier (by decide)) (.identifier (by decide)) (.identifier (by decide))
private theorem resolution (choice : Bool) : ResolvesLocalExpression (inputs choice).names source resolved := by
  change ResolvesLocalExpression names source resolved
  exact .conditional (.identifier .head) (.identifier (.tail (by decide) .head))
    (.identifier (.tail (by decide) (.tail (by decide) .head)))
private theorem checked (choice : Bool) : (inputs choice).check? source = some (core, .bool) := by
  apply elaborateLocalExpression?_complete (resolution choice)
  · change Resolved.Lowers (Resolved.LocalScope.ids context) resolved core
    exact .ifE (.var .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) (.tail (by decide) .head)))
  · change Resolved.HasType context resolved .bool
    exact .ifE (.var .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) (.tail (by decide) .head)))

private theorem checked_extended (choice : Bool) :
    (extended choice).check? source = some (shifted, .bool) := by
  simpa [extended, core, shifted, Core.Expr.weakenAt] using
    avoids_source.check_bindFresh_complete (inputs choice) owner .unit .unit .unit (checked choice)

theorem unused_name_keeps_identities_and_shifts_core (choice : Bool) (store : Core.Store) :
    resolveLocalExpression? (inputs choice).names source = some resolved ∧
    resolveLocalExpression? (extended choice).names source = some resolved ∧
    (inputs choice).check? source = some (core, .bool) ∧
    (extended choice).check? source = some (shifted, .bool) ∧
    (inputs choice).run? 4 source store = some (.bool, .done (.bool (!choice)) store) ∧
    (extended choice).run? 4 source store = some (.bool, .done (.bool (!choice)) store) := by
  refine ⟨(resolution choice).complete,
    (avoids_source.resolves_cons_iff.mpr (resolution choice)).complete,
    checked choice, checked_extended choice, ?_, ?_⟩
  · rw [LocalInputs.run?, checked]; cases choice <;> rfl
  · rw [LocalInputs.run?, checked_extended]; cases choice <;> rfl

theorem unused_name_preserves_type_and_both_evaluation_stores (choice : Bool)
    (type : Core.Ty) (value : Core.Value) (initialStore finalStore : Core.Store) :
    (LocalExpressionHasType (extended choice).names (extended choice).context source type ↔
      LocalExpressionHasType (inputs choice).names (inputs choice).context source type) ∧
    (LocalExpressionEvaluates (extended choice).names (extended choice).environment initialStore source value finalStore ↔
      LocalExpressionEvaluates (inputs choice).names (inputs choice).environment initialStore source value finalStore) ∧
    ((∃ fuel, (extended choice).run? fuel source initialStore = some (type, .done value finalStore)) ↔
      ∃ fuel, (inputs choice).run? fuel source initialStore = some (type, .done value finalStore)) :=
  ⟨avoids_source.bindFresh_hasType_iff (inputs choice) owner .unit .unit .unit,
    avoids_source.bindFresh_evaluates_iff (inputs choice) owner .unit .unit .unit,
    avoids_source.bindFresh_run_done_iff (inputs choice) owner .unit .unit .unit⟩

private def illTyped : Syntax.Expr := branch (ref "w") (ref "t") (ref "e")
private theorem avoids_illTyped : AvoidsLocalName "extra" illTyped :=
  .conditional (.identifier (by decide)) (.identifier (by decide)) (.identifier (by decide))

theorem supported_illtyped_checks_remain_absent :
    AvoidsLocalName "extra" illTyped ∧
    resolveLocalExpression? (inputs true).names illTyped =
      some (.ifE (.var (localId 0)) (.var (localId 2)) (.var (localId 1))) ∧
    (inputs true).check? illTyped = none ∧
      (extended true).check? illTyped = none := by
  have rejected : (inputs true).check? illTyped = none := by
    change elaborateLocalExpression? names context illTyped = none
    simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
      illTyped, branch, ref, Resolved.Expr.lower?, Resolved.LocalScope.ids, Resolved.LocalScope.values,
      Resolved.LocalScope.index?, localId]
    intro type inferred
    cases Core.infer_sound inferred with
    | ifE condition _ _ => cases condition with | var found => cases found
  refine ⟨avoids_illTyped, ?_, rejected, ?_⟩
  · apply ResolvesLocalExpression.complete
    exact .conditional
      (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.identifier (.tail (by decide) .head))
      (.identifier (.tail (by decide) (.tail (by decide) .head)))
  · change ((inputs true).bindFresh owner "extra" .unit .unit .unit).check? illTyped = none
    rw [avoids_illTyped.check_bindFresh_eq, rejected]
    rfl

private def unselectedMissing : Syntax.Expr := branch (ref "c") (ref "t") (ref "missing")
private theorem avoids_missing : AvoidsLocalName "extra" unselectedMissing :=
  .conditional (.identifier (by decide)) (.identifier (by decide)) (.identifier (by decide))

theorem unselected_missing_name_stays_evaluable_but_unchecked (store : Core.Store) :
    LocalExpressionEvaluates (inputs true).names (inputs true).environment store
      unselectedMissing (.bool false) store ∧
    LocalExpressionEvaluates (extended true).names (extended true).environment store
      unselectedMissing (.bool false) store ∧
    (inputs true).check? unselectedMissing = none ∧ (extended true).check? unselectedMissing = none := by
  have evaluation : LocalExpressionEvaluates (inputs true).names (inputs true).environment store
      unselectedMissing (.bool false) store :=
    .ifTrue (.identifier .head .head) (.identifier (.tail (by decide) .head) (.tail (by decide) .head))
  have rejected : (inputs true).check? unselectedMissing = none := by
    change elaborateLocalExpression? names context unselectedMissing = none
    simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?,
      names, unselectedMissing, branch, ref]
  refine ⟨evaluation, (avoids_missing.bindFresh_evaluates_iff (inputs true) owner .unit .unit .unit).mpr evaluation,
    rejected, ?_⟩
  change ((inputs true).bindFresh owner "extra" .unit .unit .unit).check? unselectedMissing = none
  rw [avoids_missing.check_bindFresh_eq, rejected]
  rfl

private def changed : LocalInputs := (inputs true).bindFresh owner "c" .bool (.bool false) .bool
private def changedCore : Core.Expr := .ifE (.var 0) (.var 2) (.var 3)
private theorem checked_changed : changed.check? source = some (changedCore, .bool) := by
  apply elaborateLocalExpression?_complete
    (resolved := .ifE (.var (localId 4)) (.var (localId 2)) (.var (localId 1)))
  · exact .conditional (.identifier .head) (.identifier (.tail (by decide) (.tail (by decide) .head)))
      (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
  · exact .ifE (.var .head) (.var (.tail (by decide) (.tail (by decide) .head)))
      (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
  · exact .ifE (.var .head) (.var (.tail (by decide) (.tail (by decide) .head)))
      (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))

theorem a_used_condition_name_changes_results_despite_fresh_identity (store : Core.Store) :
    Resolved.freshLocalId owner (inputs true).ids ∉ (inputs true).ids ∧
    (¬ AvoidsLocalName "c" source) ∧ changed.check? source = some (changedCore, .bool) ∧
    (inputs true).run? 4 source store = some (.bool, .done (.bool false) store) ∧
    changed.run? 4 source store = some (.bool, .done (.bool true) store) := by
  refine ⟨(inputs true).bindFresh_id_fresh owner, ?_, checked_changed, ?_, ?_⟩
  · intro avoids
    cases avoids with
    | conditional condition _ _ => cases condition with | identifier different => exact different rfl
  · rw [LocalInputs.run?, checked]; rfl
  · rw [LocalInputs.run?, checked_changed]; rfl

end Tests.FrontendLocalInputsExtension
end

section
-- leanmerge: from Solcore.Test.FrontendLocalInputsProperties
/-! Shared typed inputs keep identity order synchronized. Fresh identity
allocation does not prevent deliberate first-match spelling shadowing. -/

set_option autoImplicit false

namespace Tests.FrontendLocalInputs

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"Inputs", by decide⟩], by decide⟩⟩, 0⟩
private def otherOwner : Resolved.DeclarationId := { owner with declarationIndex := 1 }
private def localId (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "inputs.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .conditional condition span left span right⟩
private def base : LocalInputs :=
  LocalInputs.empty.bindFresh owner "word" .word (.word Core.Word.zero) .word
private def inputs (choice : Bool) : LocalInputs :=
  ((base.bindFresh owner "right" .bool (.bool true) .bool).bindFresh
    owner "left" .bool (.bool false) .bool).bindFresh
    owner "cond" .bool (.bool choice) .bool
private def names : LocalNameTable :=
  [("cond", localId 3), ("left", localId 2), ("right", localId 1), ("word", localId 0)]
private def context : Resolved.Context :=
  [(localId 3, .bool), (localId 2, .bool), (localId 1, .bool), (localId 0, .word)]
private def source : Syntax.Expr := branch (ref "cond") (ref "left") (ref "right")
private def resolved : Resolved.Expr :=
  .ifE (.var (localId 3)) (.var (localId 2)) (.var (localId 1))
private def core : Core.Expr := .ifE (.var 0) (.var 1) (.var 2)
private def original : LocalInputs :=
  LocalInputs.empty.bindFresh owner "item" .bool (.bool false) .bool
private def shadowed : LocalInputs := original.bindFresh owner "item" .unit .unit .unit
private def distinct : LocalInputs := original.bindFresh owner "other" .unit .unit .unit

theorem empty_and_owner_relative_fresh_indices (choice : Bool) :
    LocalInputs.empty.ids = [] ∧ base.ids = [localId 0] ∧
    (inputs choice).ids = [localId 3, localId 2, localId 1, localId 0] ∧
    (base.bindFresh otherOwner "external" .unit .unit .unit).ids =
      [⟨otherOwner, 0⟩, localId 0] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem generated_inputs_have_aligned_typed_projections (choice : Bool) :
    (inputs choice).ids.Nodup ∧
    Resolved.LocalScope.ids (inputs choice).environment =
      Resolved.LocalScope.ids (inputs choice).context ∧
    Core.EnvironmentHasTypes (Resolved.LocalScope.values (inputs choice).environment)
      (Resolved.LocalScope.values (inputs choice).context) :=
  ⟨(inputs choice).ids_nodup, (inputs choice).sameIds, (inputs choice).environmentTyped⟩

private theorem checked_conditional (choice : Bool) :
    (inputs choice).check? source = some (core, .bool) := by
  change elaborateLocalExpression? names context source = some (core, .bool)
  apply elaborateLocalExpression?_complete (resolved := resolved)
  · exact .conditional (.identifier .head) (.identifier (.tail (by decide) .head))
      (.identifier (.tail (by decide) (.tail (by decide) .head)))
  · exact .ifE (.var .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) (.tail (by decide) .head)))
  · exact .ifE (.var .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) (.tail (by decide) .head)))

theorem fresh_same_name_shadows_type_and_value (store : Core.Store) :
    original.check? (ref "item") = some (.var 0, .bool) ∧
    shadowed.ids = [localId 1, localId 0] ∧
    shadowed.check? (ref "item") = some (.var 0, .unit) ∧
    original.run? 1 (ref "item") store = some (.bool, .done (.bool false) store) ∧
    shadowed.run? 1 (ref "item") store = some (.unit, .done .unit store) := by
  have oldChecked : original.check? (ref "item") = some (.var 0, .bool) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  have newChecked : shadowed.check? (ref "item") = some (.var 0, .unit) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  refine ⟨oldChecked, rfl, newChecked, ?_, ?_⟩
  · rw [LocalInputs.run?, oldChecked]; rfl
  · rw [LocalInputs.run?, newChecked]; rfl

theorem different_name_keeps_the_existing_identity_and_value (store : Core.Store) :
    ResolvesLocalExpression distinct.names (ref "item") (.var (localId 0)) ∧
    distinct.check? (ref "item") = some (.var 1, .bool) ∧
    distinct.run? 1 (ref "item") store = some (.bool, .done (.bool false) store) := by
  have resolution : ResolvesLocalExpression distinct.names (ref "item") (.var (localId 0)) :=
    .identifier (.tail (by decide) .head)
  have checked : distinct.check? (ref "item") = some (.var 1, .bool) :=
    elaborateLocalExpression?_complete resolution (.var (.tail (by decide) .head))
      (.var (.tail (by decide) .head))
  refine ⟨resolution, checked, ?_⟩
  rw [LocalInputs.run?, checked]
  rfl

/-- Insufficient fuel is a present result retaining the actual checked state,
not the absence used for failed checking. Both Boolean choices complete at four. -/
theorem conditional_check_and_present_execution_boundary (choice : Bool) (store : Core.Store) :
    (inputs choice).check? source = some (core, .bool) ∧
    (inputs choice).run? 0 source store = some (.bool, .outOfFuel
      (Core.State.initial core (Resolved.LocalScope.values (inputs choice).environment) store)) ∧
    (inputs choice).run? 3 source store = some (.bool, .outOfFuel
      (Core.State.initial (.var (if choice then 1 else 2))
        (Resolved.LocalScope.values (inputs choice).environment) store)) ∧
    ∀ extra, (inputs choice).run? (extra + 4) source store =
      some (.bool, .done (.bool (!choice)) store) := by
  refine ⟨checked_conditional choice, ?_, ?_, ?_⟩
  · rw [LocalInputs.run?, checked_conditional]; rfl
  · rw [LocalInputs.run?, checked_conditional]
    cases choice <;> rfl
  · intro extra
    rw [LocalInputs.run?, checked_conditional]
    change some (Core.Ty.bool, Core.runStateful (extra + 4) (Core.State.initial core
      [.bool choice, .bool false, .bool true, .word Core.Word.zero] store)) = _
    cases choice <;> simp [Core.runStateful, Core.State.initial, Core.advance, core]

private def unsupported : Syntax.Expr := ⟨span, .literal ⟨span, .string "7"⟩⟩
private def wordCondition : Syntax.Expr := branch (ref "word") (ref "left") (ref "right")
private def badForms : List Syntax.Expr := [ref "missing", unsupported, wordCondition]

private theorem bad_check (bad : Syntax.Expr) (member : bad ∈ badForms) :
    (inputs true).check? bad = none := by
  change elaborateLocalExpression? names context bad = none
  simp only [badForms, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
    unsupported, interpretWordLiteral?, numericLiteralValue?,
    wordCondition, branch, ref, Resolved.Expr.lower?, Resolved.LocalScope.ids,
    Resolved.LocalScope.values, Resolved.LocalScope.index?, localId]
  intro type inferred
  cases Core.infer_sound inferred with
  | ifE condition _ _ => cases condition with | var found => cases found

theorem failed_checks_are_absent_runs_at_every_fuel (fuel : Nat) (store : Core.Store) :
    ∀ bad ∈ badForms, (inputs true).check? bad = none ∧
      (inputs true).run? fuel bad store = none ∧
      ((inputs true).run? fuel bad store = none ↔ (inputs true).check? bad = none) := by
  intro bad member
  have checked := bad_check bad member
  exact ⟨checked, (LocalInputs.run?_eq_none_iff fuel store).mpr checked,
    LocalInputs.run?_eq_none_iff fuel store⟩

private def unselectedMissing : Syntax.Expr := branch (ref "cond") (ref "left") (ref "missing")

/-- Raw selected-branch evaluation cannot bypass whole-expression checking. -/
theorem raw_evaluation_does_not_make_an_unchecked_run (fuel : Nat) (store : Core.Store) :
    LocalExpressionEvaluates (inputs true).names (inputs true).environment store
      unselectedMissing (.bool false) store ∧
    (inputs true).check? unselectedMissing = none ∧
    (inputs true).run? fuel unselectedMissing store = none := by
  have checked : (inputs true).check? unselectedMissing = none := by
    change elaborateLocalExpression? names context unselectedMissing = none
    simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?,
      names, unselectedMissing, branch, ref]
  refine ⟨?_, checked, (LocalInputs.run?_eq_none_iff fuel store).mpr checked⟩
  exact .ifTrue (.identifier .head .head)
    (.identifier (.tail (by decide) .head) (.tail (by decide) .head))

theorem repeated_identity_cannot_construct_inputs (binding : TypedLocalBinding) :
    ¬ ∃ supplied : LocalInputs, supplied.bindings = [binding, binding] := by
  rintro ⟨supplied, rows⟩
  have unique := supplied.ids_nodup
  simp [rows] at unique

end Tests.FrontendLocalInputs
end

section
-- leanmerge: from Solcore.Test.FrontendLocalNegationProperties
/-! Boolean-only canonical negation: exact syntax, dynamic values, and fuel.
The spellings `true` and `false` remain ordinary caller-supplied names. -/

set_option autoImplicit false

namespace Tests.FrontendLocalNegation

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"Negation", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "negation.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def neg (operand : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .logicalNot⟩ operand⟩
private def group (operand : Syntax.Expr) : Syntax.Expr := ⟨span, .group operand⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .conditional condition span left span right⟩
private def supplied (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "x" type value typed
private def inputs (choice : Bool) : LocalInputs := supplied .bool (.bool choice) .bool
private def source : Syntax.Expr := neg (ref "x")
private def twice : Syntax.Expr := neg source
private def core : Core.Expr := .unary .boolNot (.var 0)
private def twiceCore : Core.Expr := .unary .boolNot core

private theorem checked (choice : Bool) : (inputs choice).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete (.logicalNot (.identifier .head))
    (.unary (.var .head)) (.unary (.var .head))
private theorem checked_twice (choice : Bool) : (inputs choice).check? twice = some (twiceCore, .bool) :=
  elaborateLocalExpression?_complete (.logicalNot (.logicalNot (.identifier .head)))
    (.unary (.unary (.var .head))) (.unary (.unary (.var .head)))
private theorem evaluated (choice : Bool) (store : Core.Store) :
    LocalExpressionEvaluates (inputs choice).names (inputs choice).environment store source (.bool (!choice)) store :=
  .logicalNot (.identifier .head .head)

theorem boolean_and_double_negation_have_exact_meanings (choice : Bool) (store : Core.Store) :
    (inputs choice).check? source = some (core, .bool) ∧
    (inputs choice).check? twice = some (twiceCore, .bool) ∧
    LocalExpressionEvaluates (inputs choice).names (inputs choice).environment store source (.bool (!choice)) store ∧
    LocalExpressionEvaluates (inputs choice).names (inputs choice).environment store twice (.bool choice) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs choice).environment) store core (.bool (!choice)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs choice).environment) store twiceCore (.bool choice) store := by
  have double : LocalExpressionEvaluates (inputs choice).names (inputs choice).environment store twice (.bool choice) store := by
    simpa [twice, neg] using LocalExpressionEvaluates.logicalNot (evaluated choice store)
  exact ⟨checked choice, checked_twice choice, evaluated choice store, double,
    (elaborateLocalExpression?_evaluates_iff (checked choice) (inputs choice).sameIds).mp (evaluated choice store),
    (elaborateLocalExpression?_evaluates_iff (checked_twice choice) (inputs choice).sameIds).mp double⟩

theorem exact_negation_fuel_is_a_present_typed_result (choice : Bool) (store : Core.Store) :
    (inputs choice).run? 2 source store =
      some (.bool, .outOfFuel ⟨.ret (.bool choice), [.unaryApply .boolNot], store⟩) ∧
    ∀ extra, (inputs choice).run? (extra + 3) source store = some (.bool, .done (.bool (!choice)) store) := by
  constructor
  · rw [LocalInputs.run?, checked]; rfl
  · intro extra
    rw [LocalInputs.run?, checked]
    change some (Core.Ty.bool, Core.runStateful (extra + 3)
      (Core.State.initial core [.bool choice] store)) = _
    simp [Core.runStateful, Core.State.initial, Core.advance, core, Core.UnaryOp.apply]

private def nested : Syntax.Expr := neg (group (branch source twice (group (ref "x"))))
private def nestedCore : Core.Expr := .unary .boolNot (.ifE core twiceCore (.var 0))
private theorem checked_nested (choice : Bool) : (inputs choice).check? nested = some (nestedCore, .bool) :=
  elaborateLocalExpression?_complete
    (.logicalNot (.group (.conditional (.logicalNot (.identifier .head))
      (.logicalNot (.logicalNot (.identifier .head))) (.group (.identifier .head)))))
    (.unary (.ifE (.unary (.var .head)) (.unary (.unary (.var .head))) (.var .head)))
    (.unary (.ifE (.unary (.var .head)) (.unary (.unary (.var .head))) (.var .head)))

theorem groups_and_conditionals_keep_exact_negation_core (choice : Bool) (store : Core.Store) :
    (inputs choice).check? nested = some (nestedCore, .bool) ∧
    LocalExpressionEvaluates (inputs choice).names (inputs choice).environment store nested (.bool (!choice)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs choice).environment) store nestedCore (.bool (!choice)) store := by
  have raw : LocalExpressionEvaluates (inputs choice).names (inputs choice).environment store nested (.bool (!choice)) store := by
    cases choice
    · exact .logicalNot (.group (.ifTrue (evaluated false store) (.logicalNot (evaluated false store))))
    · exact .logicalNot (.group (.ifFalse (evaluated true store) (.group (.identifier .head .head))))
  exact ⟨checked_nested choice, raw,
    (elaborateLocalExpression?_evaluates_iff (checked_nested choice) (inputs choice).sameIds).mp raw⟩

private def spellings : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "false" .bool (.bool true) .bool).bindFresh
    owner "true" .bool (.bool false) .bool

theorem true_and_false_spellings_still_use_supplied_values (store : Core.Store) :
    spellings.check? (neg (ref "true")) = some (.unary .boolNot (.var 0), .bool) ∧
    spellings.check? (neg (ref "false")) = some (.unary .boolNot (.var 1), .bool) ∧
    spellings.run? 3 (neg (ref "true")) store = some (.bool, .done (.bool true) store) ∧
    spellings.run? 3 (neg (ref "false")) store = some (.bool, .done (.bool false) store) := by
  have first : spellings.check? (neg (ref "true")) = some (.unary .boolNot (.var 0), .bool) :=
    elaborateLocalExpression?_complete (.logicalNot (.identifier .head))
      (.unary (.var .head)) (.unary (.var .head))
  have second : spellings.check? (neg (ref "false")) = some (.unary .boolNot (.var 1), .bool) :=
    elaborateLocalExpression?_complete (.logicalNot (.identifier (.tail (by decide) .head)))
      (.unary (.var (.tail (by decide) .head))) (.unary (.var (.tail (by decide) .head)))
  refine ⟨first, second, ?_, ?_⟩
  · rw [LocalInputs.run?, first]; rfl
  · rw [LocalInputs.run?, second]; rfl

private theorem non_boolean_rejected (type : Core.Ty) (value : Core.Value)
    (typed : Core.ValueHasType value type) (wrongType : type ≠ .bool)
    (wrongValue : ∀ flag, value ≠ .bool flag) (store : Core.Store) :
    (supplied type value typed).check? source = none ∧ ∀ result finalStore,
      ¬ LocalExpressionEvaluates (supplied type value typed).names (supplied type value typed).environment
        store source result finalStore := by
  constructor
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨resultType, typing⟩
    cases typing with
    | logicalNot operand =>
        have original : LocalExpressionHasType (supplied type value typed).names
            (supplied type value typed).context (ref "x") type := .identifier .head .head
        exact wrongType (original.type_unique operand)
  · intro result finalStore evaluation
    have original : LocalExpressionEvaluates (supplied type value typed).names
        (supplied type value typed).environment store (ref "x") value store := .identifier .head .head
    cases evaluation with
    | logicalNot operand => exact wrongValue _ (original.deterministic operand).1

private def wordInputs : LocalInputs := supplied .word (.word Core.Word.zero) .word
private def opaqueInputs (location : Nat) : LocalInputs := supplied (.cell .word) (.cellRef .word location) .cellRef

theorem word_and_opaque_operands_have_no_truthiness (location : Nat) (store : Core.Store) :
    wordInputs.check? source = none ∧ (opaqueInputs location).check? source = none ∧
    ∀ value finalStore, (¬ LocalExpressionEvaluates wordInputs.names wordInputs.environment store source value finalStore) ∧
      (¬ LocalExpressionEvaluates (opaqueInputs location).names (opaqueInputs location).environment
        store source value finalStore) := by
  have wordBad := non_boolean_rejected .word (.word Core.Word.zero) .word
    (by decide) (by intro flag same; cases same) store
  have opaqueBad := non_boolean_rejected (.cell .word) (.cellRef .word location) .cellRef
    (by decide) (by intro flag same; cases same) store
  exact ⟨wordBad.1, opaqueBad.1, fun value finalStore => ⟨wordBad.2 value finalStore, opaqueBad.2 value finalStore⟩⟩

private def bitNeg : Syntax.Expr := ⟨span, .unary ⟨span, .bitNot⟩ (ref "x")⟩

theorem bitwise_negation_is_not_boolean_negation (choice : Bool) (store : Core.Store) :
    resolveLocalExpression? (inputs choice).names bitNeg =
      some (.unary .wordNot (.var ⟨owner, 0⟩)) ∧ (inputs choice).check? bitNeg = none ∧
    ∀ value finalStore, ¬ LocalExpressionEvaluates (inputs choice).names (inputs choice).environment
      store bitNeg value finalStore := by
  refine ⟨?_, ?_, ?_⟩
  · apply ResolvesLocalExpression.complete
    exact .bitNot (.identifier .head)
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    have original : LocalExpressionHasType (inputs choice).names (inputs choice).context (ref "x") .bool :=
      .identifier .head .head
    cases typing with
    | bitNot operand => cases original.type_unique operand
  · intro value finalStore evaluation
    have original : LocalExpressionEvaluates (inputs choice).names (inputs choice).environment
        store (ref "x") (.bool choice) store := .identifier .head .head
    cases evaluation with
    | bitNot operand => cases (original.deterministic operand).1

private def extended (choice : Bool) : LocalInputs := (inputs choice).bindFresh owner "extra" .unit .unit .unit

theorem unused_input_extension_preserves_negation (choice : Bool) (value : Core.Value)
    (initialStore finalStore : Core.Store) :
    (extended choice).check? source = some (.unary .boolNot (.var 1), .bool) ∧
    (LocalExpressionEvaluates (extended choice).names (extended choice).environment initialStore source value finalStore ↔
      LocalExpressionEvaluates (inputs choice).names (inputs choice).environment initialStore source value finalStore) ∧
    ((∃ fuel, (extended choice).run? fuel source initialStore = some (.bool, .done value finalStore)) ↔
      ∃ fuel, (inputs choice).run? fuel source initialStore = some (.bool, .done value finalStore)) := by
  have avoids : AvoidsLocalName "extra" source := .logicalNot (.identifier (by decide))
  refine ⟨?_, avoids.bindFresh_evaluates_iff (inputs choice) owner .unit .unit .unit,
    avoids.bindFresh_run_done_iff (inputs choice) owner .unit .unit .unit⟩
  simpa [extended, core, Core.Expr.weakenAt] using
    avoids.check_bindFresh_complete (inputs choice) owner .unit .unit .unit (checked choice)

end Tests.FrontendLocalNegation
end

section
-- leanmerge: from Solcore.Test.FrontendLocalReferenceExecutionProperties
/-! Checked canonical references preserve values only when context and runtime
identity order agree. Equal positional types alone do not establish that alignment. -/

set_option autoImplicit false

namespace Tests.FrontendLocalReferenceExecution

open Solcore Solcore.Frontend

private def modulePath : Workspace.ModulePath := ⟨[⟨"ReferenceExec", by decide⟩], by decide⟩
private def idA : Resolved.LocalId := ⟨⟨⟨.main, modulePath⟩, 0⟩, 0⟩
private def idB : Resolved.LocalId := { idA with binderIndex := 1 }
private def span : Syntax.SourceSpan := ⟨⟨.main, "refs.sol"⟩, 0, 4⟩
private def source : Syntax.Expr :=
  ⟨span, .group ⟨span, .identifier ⟨span, "flag"⟩⟩⟩
private def table : LocalNameTable := [("flag", idA)]
private def context : Resolved.Context := [(idA, .bool), (idB, .bool)]
private def aligned : Resolved.Environment := [(idA, .bool false), (idB, .bool true)]
private def reversed : Resolved.Environment := [(idB, .bool true), (idA, .bool false)]

private theorem reference : ResolvesLocalReference table source idA :=
  .group (.identifier .head)

private theorem aligned_typed : Core.EnvironmentHasTypes
    (Resolved.LocalScope.values aligned) (Resolved.LocalScope.values context) :=
  .cons .bool (.cons .bool .nil)

private theorem aligned_evaluates : LocalReferenceEvaluates table aligned source (.bool false) :=
  .reference reference .head

theorem checked_reference_selects_first_position :
    elaborateLocalReference? table context source = some (.var 0, .bool) :=
  elaborateLocalReference?_complete reference .head .head

theorem aligned_typed_execution (store : Core.Store) :
    LocalReferenceEvaluates table aligned source (.bool false) ∧
    Core.ValueHasType (.bool false) .bool ∧
    ∀ fuel, Core.runStateful (fuel + 1)
      (Core.State.initial (.var 0) (Resolved.LocalScope.values aligned) store) =
        .done (.bool false) store := by
  obtain ⟨value, evaluation, valueTyped, enough⟩ :=
    elaborateLocalReference?_typed_execution checked_reference_selects_first_position
      (environment := aligned) rfl aligned_typed store
  cases evaluation.deterministic aligned_evaluates
  exact ⟨aligned_evaluates, valueTyped, enough⟩

theorem aligned_exact_machine_boundary (store : Core.Store) :
    Core.runStateful 0
      (Core.State.initial (.var 0) (Resolved.LocalScope.values aligned) store) =
        .outOfFuel (Core.State.initial (.var 0) (Resolved.LocalScope.values aligned) store) ∧
    ∀ fuel, Core.runStateful (fuel + 1)
      (Core.State.initial (.var 0) (Resolved.LocalScope.values aligned) store) =
        .done (.bool false) store :=
  elaborateLocalReference?_exact_run checked_reference_selects_first_position
    rfl aligned_evaluates store

theorem aligned_checked_evaluation_iff (initialStore finalStore : Core.Store) (value : Core.Value) :
    Core.Evaluates (Resolved.LocalScope.values aligned) initialStore (.var 0) value finalStore ↔
      LocalReferenceEvaluates table aligned source value ∧ finalStore = initialStore :=
  elaborateLocalReference?_evaluates_iff checked_reference_selects_first_position rfl

/-- Reordering preserves all Boolean types and each ID's value, but breaks the
identity alignment required by checked execution. The reference still denotes A. -/
theorem reversed_environment_is_typed_but_misaligned :
    Core.EnvironmentHasTypes (Resolved.LocalScope.values reversed)
      (Resolved.LocalScope.values context) ∧
    Resolved.LocalScope.ids reversed ≠ Resolved.LocalScope.ids context ∧
    LocalReferenceEvaluates table reversed source (.bool false) :=
  ⟨.cons .bool (.cons .bool .nil), by decide,
    .reference reference (.tail (by decide) .head)⟩

/-- Without identity alignment, the checked Core position reads B's true while
the same canonical reference independently reads A's false. -/
theorem reversed_core_reads_the_wrong_reference_value (store : Core.Store) :
    Core.Evaluates (Resolved.LocalScope.values reversed) store (.var 0) (.bool true) store ∧
    (∀ fuel, Core.runStateful (fuel + 1)
      (Core.State.initial (.var 0) (Resolved.LocalScope.values reversed) store) =
        .done (.bool true) store) ∧
    ¬ LocalReferenceEvaluates table reversed source (.bool true) := by
  refine ⟨.var rfl, ?_, ?_⟩
  · intro fuel
    simp [Core.runStateful, Core.State.initial, Core.advance, Resolved.LocalScope.values, reversed]
  · intro evaluation
    have impossible := evaluation.deterministic reversed_environment_is_typed_but_misaligned.2.2
    cases impossible

private def duplicateContext : Resolved.Context := [(idA, .bool), (idA, .bool)]
private def duplicateEnvironment : Resolved.Environment := [(idA, .bool false), (idA, .bool true)]

theorem duplicate_ids_keep_first_typed_value (store : Core.Store) :
    elaborateLocalReference? table duplicateContext source = some (.var 0, .bool) ∧
    LocalReferenceEvaluates table duplicateEnvironment source (.bool false) ∧
    Core.ValueHasType (.bool false) .bool ∧
    ∀ fuel, Core.runStateful (fuel + 1)
      (Core.State.initial (.var 0) (Resolved.LocalScope.values duplicateEnvironment) store) =
        .done (.bool false) store := by
  have accepted : elaborateLocalReference? table duplicateContext source = some (.var 0, .bool) :=
    elaborateLocalReference?_complete reference .head .head
  have environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values duplicateEnvironment) (Resolved.LocalScope.values duplicateContext) :=
    .cons .bool (.cons .bool .nil)
  obtain ⟨value, evaluation, valueTyped, enough⟩ :=
    elaborateLocalReference?_typed_execution accepted
      (environment := duplicateEnvironment) rfl environmentTyped store
  have first : LocalReferenceEvaluates table duplicateEnvironment source (.bool false) :=
    .reference reference .head
  cases evaluation.deterministic first
  exact ⟨accepted, first, valueTyped, enough⟩

end Tests.FrontendLocalReferenceExecution
end

section
-- leanmerge: from Solcore.Test.FrontendLocalReferenceProperties
/-! Canonical-AST consumers for the narrow local-reference adapter. Names are
caller-bound exact strings, not Boolean literals or normalized spellings.
Arbitrary independent source ranges do not participate in identity selection. -/

set_option autoImplicit false

namespace Tests.FrontendLocalReference

open Solcore Solcore.Frontend

private def modulePath : Workspace.ModulePath := ⟨[⟨"References", by decide⟩], by decide⟩
private def selectedId : Resolved.LocalId := ⟨⟨⟨.main, modulePath⟩, 0⟩, 0⟩
private def otherId : Resolved.LocalId := { selectedId with binderIndex := 1 }

private def reference (spelling : String) (expressionSpan nameSpan : Syntax.SourceSpan) : Syntax.Expr :=
  { span := expressionSpan, value := .identifier { span := nameSpan, value := spelling } }

private def grouped (outer inner expressionSpan nameSpan : Syntax.SourceSpan) : Syntax.Expr :=
  { span := outer, value := .group
      { span := inner, value := .group (reference "true" expressionSpan nameSpan) } }

private def booleanNames : LocalNameTable := [("true", selectedId), ("false", otherId)]

theorem occurrence_spans_do_not_select_ids (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? [("local", selectedId)] (reference "local" expressionSpan nameSpan) =
      some (.var selectedId) := by
  simp [resolveLocalReference?, LocalNameTable.lookup?, reference]

theorem true_and_false_remain_references (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? booleanNames (reference "true" expressionSpan nameSpan) = some (.var selectedId) ∧
    resolveLocalReference? booleanNames (reference "false" expressionSpan nameSpan) = some (.var otherId) := by
  simp [resolveLocalReference?, LocalNameTable.lookup?, reference, booleanNames]

theorem unbound_boolean_spellings_are_not_implicit_values (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? [] (reference "true" expressionSpan nameSpan) = none ∧
    resolveLocalReference? [] (reference "false" expressionSpan nameSpan) = none := by
  simp [resolveLocalReference?, LocalNameTable.lookup?, reference]

theorem spelling_is_case_and_space_sensitive (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? [("local", selectedId)] (reference "Local" expressionSpan nameSpan) = none ∧
    resolveLocalReference? [("local", selectedId)] (reference "local " expressionSpan nameSpan) = none := by
  simp [resolveLocalReference?, LocalNameTable.lookup?, reference]

/-- The second spelling uses a separate combining acute accent. -/
theorem spelling_is_not_unicode_normalized (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? [("é", selectedId)] (reference "é" expressionSpan nameSpan) = some (.var selectedId) ∧
    resolveLocalReference? [("é", selectedId)] (reference "é" expressionSpan nameSpan) = none := by
  simp [resolveLocalReference?, LocalNameTable.lookup?, reference]

theorem repeated_names_select_the_first_id (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? [("local", selectedId), ("local", otherId)]
      (reference "local" expressionSpan nameSpan) = some (.var selectedId) ∧
    ResolvesLocalReference [("local", selectedId), ("local", otherId)]
      (reference "local" expressionSpan nameSpan) selectedId := by
  exact ⟨by simp [resolveLocalReference?, LocalNameTable.lookup?, reference], .identifier .head⟩

theorem missing_names_are_unmapped (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? booleanNames (reference "missing" expressionSpan nameSpan) = none := by
  simp [resolveLocalReference?, LocalNameTable.lookup?, reference, booleanNames]

theorem recovered_and_literal_nodes_are_unsupported (span literalSpan : Syntax.SourceSpan) :
    resolveLocalReference? booleanNames { span, value := .error } = none ∧
    resolveLocalReference? booleanNames
      { span, value := .literal { span := literalSpan, value := .decimal "7" } } = none ∧
    resolveLocalReference? booleanNames
      { span, value := .literal { span := literalSpan, value := .string "true" } } = none := by
  simp [resolveLocalReference?]

theorem calls_and_fields_are_not_reference_groups (span nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? booleanNames
      { span, value := .call (reference "true" span nameSpan) { span, elements := [] } } = none ∧
    resolveLocalReference? booleanNames
      { span, value := .field (reference "true" span nameSpan) span { span := nameSpan, value := "false" } } = none := by
  simp [resolveLocalReference?]

theorem nested_groups_preserve_the_selected_identity
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? booleanNames (grouped outer inner expressionSpan nameSpan) = some (.var selectedId) ∧
    ResolvesLocalReference booleanNames (grouped outer inner expressionSpan nameSpan) selectedId := by
  exact ⟨by simp [resolveLocalReference?, LocalNameTable.lookup?, grouped, reference, booleanNames],
    .group (.group (.identifier .head))⟩

private def context : Resolved.Context := [(otherId, .bool), (selectedId, .bool)]
private def environment : Resolved.Environment := [(otherId, .bool true), (selectedId, .bool false)]

private theorem selected_typed : Resolved.HasType context (.var selectedId) .bool :=
  .var (.tail (by decide) .head)

private theorem selected_lowered :
    Resolved.Lowers (Resolved.LocalScope.ids environment) (.var selectedId) (.var 1) :=
  .var (.tail (by decide) .head)

private theorem selected_evaluates (store : Core.Store) :
    Resolved.Evaluates environment store (.var selectedId) (.bool false) store :=
  .var (.tail (by decide) .head)

/-- The source spelling `true` denotes the caller's local Boolean value false.
The leading unrelated ID also checks that lowering selects position 1, not 0. -/
theorem caller_controls_the_referenced_value
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) (store : Core.Store) :
    ∃ resolved, resolveLocalReference? booleanNames (grouped outer inner expressionSpan nameSpan) = some resolved ∧
      Resolved.HasType context resolved .bool ∧
      resolved.lower? (Resolved.LocalScope.ids environment) = some (.var 1) ∧
      Resolved.Evaluates environment store resolved (.bool false) store ∧
      Core.Evaluates (Resolved.LocalScope.values environment) store (.var 1) (.bool false) store := by
  exact ⟨.var selectedId, (nested_groups_preserve_the_selected_identity _ _ _ _).1,
    selected_typed, selected_lowered.complete, selected_evaluates store,
    (selected_evaluates store).toCore selected_lowered⟩

theorem caller_reference_runs_at_sufficient_fuel
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) (store : Core.Store) :
    ∃ resolved required,
      resolveLocalReference? booleanNames (grouped outer inner expressionSpan nameSpan) = some resolved ∧
      resolved.lower? (Resolved.LocalScope.ids environment) = some (.var 1) ∧
      ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (Core.State.initial (.var 1) (Resolved.LocalScope.values environment) store) =
          .done (.bool false) store := by
  obtain ⟨required, enough⟩ := (selected_evaluates store).run_has_sufficient_fuel selected_lowered
  exact ⟨.var selectedId, required, (nested_groups_preserve_the_selected_identity _ _ _ _).1,
    selected_lowered.complete, enough⟩

theorem grouped_reference_elaborates_at_exact_position
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) :
    elaborateLocalReference? booleanNames context (grouped outer inner expressionSpan nameSpan) =
      some (.var 1, .bool) ∧
    LocalReferenceHasType booleanNames context (grouped outer inner expressionSpan nameSpan) .bool := by
  have resolved := (nested_groups_preserve_the_selected_identity outer inner expressionSpan nameSpan).2
  have found : Resolved.LocalScope.Lookup context selectedId .bool := .tail (by decide) .head
  exact ⟨elaborateLocalReference?_complete resolved (.tail (by decide) .head) found,
    .resolved resolved found⟩

theorem mapped_name_with_absent_typed_id_has_no_default
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) :
    elaborateLocalReference? booleanNames [(otherId, .bool)]
      (grouped outer inner expressionSpan nameSpan) = none :=
  elaborateLocalReference?_eq_none_of_missing_id
    (nested_groups_preserve_the_selected_identity outer inner expressionSpan nameSpan).2 (by decide)

theorem grouped_reference_evaluates_independently
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) :
    LocalReferenceEvaluates booleanNames environment
      (grouped outer inner expressionSpan nameSpan) (.bool false) :=
  .reference (nested_groups_preserve_the_selected_identity outer inner expressionSpan nameSpan).2
    (.tail (by decide) .head)

/-- Grouping costs no Core transition: zero fuel retains the input, and every
positive fuel executes the same selected positional variable in one step. -/
theorem grouped_reference_exact_machine_boundary
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) (store : Core.Store) :
    Core.runStateful 0 (Core.State.initial (.var 1) (Resolved.LocalScope.values environment) store) =
      .outOfFuel (Core.State.initial (.var 1) (Resolved.LocalScope.values environment) store) ∧
    ∀ fuel, Core.runStateful (fuel + 1)
      (Core.State.initial (.var 1) (Resolved.LocalScope.values environment) store) = .done (.bool false) store := by
  obtain ⟨id, index, resolved, indexed, zero, enough⟩ :=
    (grouped_reference_evaluates_independently outer inner expressionSpan nameSpan).exact_run store
  have idEq := resolved.id_unique
    (nested_groups_preserve_the_selected_identity outer inner expressionSpan nameSpan).2
  subst id
  have indexEq := indexed.index_unique
    (show Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) selectedId 1 from
      .tail (by decide) .head)
  subst index
  exact ⟨zero, enough⟩

end Tests.FrontendLocalReference
end

section
-- leanmerge: from Solcore.Test.FrontendLocalShortCircuitProperties
/-! ADR-0159 consumers distinguish Boolean checking from selected-value raw
evaluation, and fixed internal constants from caller-controlled spellings. -/

set_option autoImplicit false

namespace Tests.FrontendLocalShortCircuit

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ShortCircuit", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "short-circuit.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def andE (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .logicalAnd⟩ right⟩
private def orE (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .logicalOr⟩ right⟩
private def pair (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "r" rightType right rightTyped).bindFresh owner "l" leftType left leftTyped
private def inputs (left right : Bool) : LocalInputs := pair .bool .bool (.bool left) (.bool right) .bool .bool
private theorem names_ne : "l" ≠ "r" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private def andSource : Syntax.Expr := andE (ref "l") (ref "r")
private def orSource : Syntax.Expr := orE (ref "l") (ref "r")
private def andCore : Core.Expr := .ifE (.var 0) (.var 1) (.bool false)
private def orCore : Core.Expr := .ifE (.var 0) (.bool true) (.var 1)
private theorem checked_and (left right : Bool) : (inputs left right).check? andSource = some (andCore, .bool) :=
  elaborateLocalExpression?_complete (.logicalAnd (.identifier .head) (.identifier (.tail names_ne .head)))
    (.ifE (.var .head) (.var (.tail ids_ne .head)) .bool)
    (.ifE (.var .head) (.var (.tail ids_ne .head)) .bool)
private theorem checked_or (left right : Bool) : (inputs left right).check? orSource = some (orCore, .bool) :=
  elaborateLocalExpression?_complete (.logicalOr (.identifier .head) (.identifier (.tail names_ne .head)))
    (.ifE (.var .head) .bool (.var (.tail ids_ne .head)))
    (.ifE (.var .head) .bool (.var (.tail ids_ne .head)))

theorem all_boolean_pairs_have_exact_checked_expansions (left right : Bool) :
    (inputs left right).check? andSource = some (andCore, .bool) ∧
    (inputs left right).check? orSource = some (orCore, .bool) :=
  ⟨checked_and left right, checked_or left right⟩

theorem all_boolean_pairs_have_exact_source_and_core_values (left right : Bool) (store : Core.Store) :
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment store andSource (.bool (left && right)) store ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment store orSource (.bool (left || right)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs left right).environment) store andCore (.bool (left && right)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs left right).environment) store orCore (.bool (left || right)) store := by
  have conjunction : LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store andSource (.bool (left && right)) store := by
    cases left
    · exact .andFalse (.identifier .head .head)
    · exact .andTrue (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head))
  have disjunction : LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store orSource (.bool (left || right)) store := by
    cases left
    · exact .orFalse (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head))
    · exact .orTrue (.identifier .head .head)
  exact ⟨conjunction, disjunction,
    (elaborateLocalExpression?_evaluates_iff (checked_and left right) (inputs left right).sameIds).mp conjunction,
    (elaborateLocalExpression?_evaluates_iff (checked_or left right) (inputs left right).sameIds).mp disjunction⟩

private def payload : Core.Value := .word (Core.Word.ofNatModulo 7)
private def leftBad : LocalInputs := pair .word .bool payload (.bool true) .word .bool
private def rightBad (left : Bool) : LocalInputs := pair .bool .word (.bool left) payload .bool .word

theorem non_boolean_left_has_neither_checked_nor_raw_result (store : Core.Store) :
    leftBad.check? andSource = none ∧ leftBad.check? orSource = none ∧
    ∀ value finalStore, (¬ LocalExpressionEvaluates leftBad.names leftBad.environment store andSource value finalStore) ∧
      (¬ LocalExpressionEvaluates leftBad.names leftBad.environment store orSource value finalStore) := by
  have typed : LocalExpressionHasType leftBad.names leftBad.context (ref "l") .word := .identifier .head .head
  have evaluated : LocalExpressionEvaluates leftBad.names leftBad.environment store (ref "l") payload store :=
    .identifier .head .head
  refine ⟨?_, ?_, ?_⟩
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    cases typing with | logicalAnd left _ => cases typed.type_unique left
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    cases typing with | logicalOr left _ => cases typed.type_unique left
  · intro value finalStore
    constructor <;> intro evaluation
    · cases evaluation with
      | andTrue left _ | andFalse left => cases (evaluated.deterministic left).1
    · cases evaluation with
      | orTrue left | orFalse left _ => cases (evaluated.deterministic left).1

theorem selected_non_boolean_right_is_forwarded_only_at_the_raw_boundary (left : Bool) (store : Core.Store) :
    (rightBad left).check? andSource = none ∧ (rightBad left).check? orSource = none ∧
    LocalExpressionEvaluates (rightBad true).names (rightBad true).environment store andSource payload store ∧
    LocalExpressionEvaluates (rightBad false).names (rightBad false).environment store orSource payload store ∧
    Core.Evaluates (Resolved.LocalScope.values (rightBad true).environment) store andCore payload store ∧
    Core.Evaluates (Resolved.LocalScope.values (rightBad false).environment) store orCore payload store := by
  have typed : LocalExpressionHasType (rightBad left).names (rightBad left).context (ref "r") .word :=
    .identifier (.tail names_ne .head) (.tail ids_ne .head)
  refine ⟨?_, ?_, .andTrue (.identifier .head .head)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)),
    .orFalse (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head)),
    .ifTrue (.var rfl) (.var rfl), .ifFalse (.var rfl) (.var rfl)⟩
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    cases typing with | logicalAnd _ right => cases typed.type_unique right
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    cases typing with | logicalOr _ right => cases typed.type_unique right

private def unsupported : Syntax.Expr := ⟨span, .literal ⟨span, .string "7"⟩⟩
private def badRights : List Syntax.Expr := [ref "missing", unsupported]
private theorem bad_resolutions (right : Syntax.Expr) (member : right ∈ badRights) :
    resolveLocalExpression? (inputs false true).names (andE (ref "l") right) = none ∧
    resolveLocalExpression? (inputs true false).names (orE (ref "l") right) = none := by
  simp only [badRights, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals constructor <;> simp [resolveLocalExpression?, andE, orE, ref, unsupported,
    interpretWordLiteral?, numericLiteralValue?,
    inputs, pair, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

theorem skipped_missing_or_unsupported_right_still_fails_whole_checking (store : Core.Store) :
    ∀ right ∈ badRights,
      LocalExpressionEvaluates (inputs false true).names (inputs false true).environment store
        (andE (ref "l") right) (.bool false) store ∧
      LocalExpressionEvaluates (inputs true false).names (inputs true false).environment store
        (orE (ref "l") right) (.bool true) store ∧
      resolveLocalExpression? (inputs false true).names (andE (ref "l") right) = none ∧
      resolveLocalExpression? (inputs true false).names (orE (ref "l") right) = none ∧
      (inputs false true).check? (andE (ref "l") right) = none ∧
      (inputs true false).check? (orE (ref "l") right) = none := by
  intro right member
  obtain ⟨andRejected, orRejected⟩ := bad_resolutions right member
  refine ⟨.andFalse (.identifier .head .head), .orTrue (.identifier .head .head),
    andRejected, orRejected, ?_, ?_⟩
  · simp [LocalInputs.check?, elaborateLocalExpression?, andRejected]
  · simp [LocalInputs.check?, elaborateLocalExpression?, orRejected]

private def neg (operand : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .logicalNot⟩ operand⟩
private def nestedRight : Syntax.Expr := ⟨span, .group (neg (neg (ref "r")))⟩
private def nestedSource (isOr : Bool) : Syntax.Expr :=
  if isOr then orE (ref "l") nestedRight else andE (ref "l") nestedRight
private def nestedCore (isOr : Bool) : Core.Expr :=
  let right := Core.Expr.unary .boolNot (.unary .boolNot (.var 1))
  if isOr then .ifE (.var 0) (.bool true) right else .ifE (.var 0) right (.bool false)
private theorem checked_nested (isOr left right : Bool) :
    (inputs left right).check? (nestedSource isOr) = some (nestedCore isOr, .bool) := by
  cases isOr
  · exact elaborateLocalExpression?_complete
      (.logicalAnd (.identifier .head) (.group (.logicalNot (.logicalNot (.identifier (.tail names_ne .head))))))
      (.ifE (.var .head) (.unary (.unary (.var (.tail ids_ne .head)))) .bool)
      (.ifE (.var .head) (.unary (.unary (.var (.tail ids_ne .head)))) .bool)
  · exact elaborateLocalExpression?_complete
      (.logicalOr (.identifier .head) (.group (.logicalNot (.logicalNot (.identifier (.tail names_ne .head))))))
      (.ifE (.var .head) .bool (.unary (.unary (.var (.tail ids_ne .head)))))
      (.ifE (.var .head) .bool (.unary (.unary (.var (.tail ids_ne .head)))))

theorem skipped_and_selected_nested_right_have_different_exact_fuel
    (isOr right : Bool) (store : Core.Store) :
    (inputs isOr right).run? 3 (nestedSource isOr) store = some (.bool, .outOfFuel
      (Core.State.initial (.bool isOr) (Resolved.LocalScope.values (inputs isOr right).environment) store)) ∧
    (inputs isOr right).run? 4 (nestedSource isOr) store = some (.bool, .done (.bool isOr) store) ∧
    (inputs (!isOr) right).run? 7 (nestedSource isOr) store =
      some (.bool, .outOfFuel ⟨.ret (.bool (!right)), [.unaryApply .boolNot], store⟩) ∧
    ∀ extra, (inputs (!isOr) right).run? (extra + 8) (nestedSource isOr) store =
      some (.bool, .done (.bool right) store) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LocalInputs.run?, checked_nested]; cases isOr <;> rfl
  · rw [LocalInputs.run?, checked_nested]; cases isOr <;> rfl
  · rw [LocalInputs.run?, checked_nested]; cases isOr <;> rfl
  · intro extra
    rw [LocalInputs.run?, checked_nested]
    change some (Core.Ty.bool, Core.runStateful (extra + 8)
      (Core.State.initial (nestedCore isOr) [.bool (!isOr), .bool right] store)) = _
    cases isOr <;> simp [Core.runStateful, Core.State.initial, Core.advance, nestedCore, Core.UnaryOp.apply]

private def baseSource (isOr : Bool) : Syntax.Expr := if isOr then orSource else andSource
private def baseCore (isOr : Bool) : Core.Expr := if isOr then orCore else andCore
private theorem checked_base (isOr left right : Bool) :
    (inputs left right).check? (baseSource isOr) = some (baseCore isOr, .bool) := by
  cases isOr
  · exact checked_and left right
  · exact checked_or left right
private theorem avoids_base (isOr : Bool) (name : String) (left : name ≠ "l") (right : name ≠ "r") :
    AvoidsLocalName name (baseSource isOr) := by
  cases isOr
  · exact .logicalAnd (.identifier left) (.identifier right)
  · exact .logicalOr (.identifier left) (.identifier right)
private def reversed (left right : Bool) : LocalInputs :=
  ((inputs left right).bindFresh owner "false" .bool (.bool true) .bool).bindFresh
    owner "true" .bool (.bool false) .bool
private def reversedCore (isOr : Bool) : Core.Expr :=
  if isOr then .ifE (.var 2) (.bool true) (.var 3) else .ifE (.var 2) (.var 3) (.bool false)
private theorem checked_reversed (isOr left right : Bool) :
    (reversed left right).check? (baseSource isOr) = some (reversedCore isOr, .bool) := by
  have first := (avoids_base isOr "false" (by decide) (by decide)).check_bindFresh_complete
    (inputs left right) owner .bool (.bool true) .bool (checked_base isOr left right)
  have second := (avoids_base isOr "true" (by decide) (by decide)).check_bindFresh_complete
    ((inputs left right).bindFresh owner "false" .bool (.bool true) .bool) owner .bool (.bool false) .bool first
  cases isOr <;> simpa [reversed, reversedCore, baseCore, andCore, orCore, Core.Expr.weakenAt] using second

theorem caller_reversed_spellings_cannot_change_inserted_constants (isOr right : Bool) (store : Core.Store) :
    LocalExpressionEvaluates (reversed isOr right).names (reversed isOr right).environment store (ref "true") (.bool false) store ∧
    LocalExpressionEvaluates (reversed isOr right).names (reversed isOr right).environment store (ref "false") (.bool true) store ∧
    (reversed isOr right).check? (baseSource isOr) = some (reversedCore isOr, .bool) ∧
    (reversed isOr right).run? 4 (baseSource isOr) store = some (.bool, .done (.bool isOr) store) := by
  refine ⟨.identifier .head .head, .identifier (.tail ?_ .head) (.tail ?_ .head),
    checked_reversed isOr isOr right, ?_⟩
  · change "true" ≠ "false"; decide
  · change (⟨owner, 3⟩ : Resolved.LocalId) ≠ ⟨owner, 2⟩; decide
  · rw [LocalInputs.run?, checked_reversed]; cases isOr <;> rfl

private def extended (left right : Bool) : LocalInputs := (inputs left right).bindFresh owner "extra" .unit .unit .unit

theorem unused_name_insertion_preserves_short_circuiting (isOr left right : Bool) (value : Core.Value)
    (initialStore finalStore : Core.Store) :
    (extended left right).check? (baseSource isOr) = some ((baseCore isOr).weakenAt 0, .bool) ∧
    (LocalExpressionEvaluates (extended left right).names (extended left right).environment
      initialStore (baseSource isOr) value finalStore ↔
      LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
        initialStore (baseSource isOr) value finalStore) ∧
    ((∃ fuel, (extended left right).run? fuel (baseSource isOr) initialStore = some (.bool, .done value finalStore)) ↔
      ∃ fuel, (inputs left right).run? fuel (baseSource isOr) initialStore = some (.bool, .done value finalStore)) := by
  have avoids := avoids_base isOr "extra" (by decide) (by decide)
  exact ⟨avoids.check_bindFresh_complete (inputs left right) owner .unit .unit .unit (checked_base isOr left right),
    avoids.bindFresh_evaluates_iff (inputs left right) owner .unit .unit .unit,
    avoids.bindFresh_run_done_iff (inputs left right) owner .unit .unit .unit⟩

end Tests.FrontendLocalShortCircuit
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalExpressions
/-! Executable source-text regressions through the existing canonical lexer,
expression parser, explicit-table frontend checker, and Core machine. This is
test wiring, not a new public source parser or external service endpoint. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def localId (index : Nat) : Resolved.LocalId :=
  ⟨⟨⟨.main, ⟨[⟨"Parsed", by decide⟩], by decide⟩⟩, 0⟩, index⟩
private def names : LocalNameTable :=
  [("c", localId 0), ("t", localId 1), ("e", localId 2), ("d", localId 3),
    ("n", localId 4), ("true", localId 5), ("false", localId 6)]
private def context : Resolved.Context :=
  [(localId 99, .unit), (localId 0, .bool), (localId 1, .word), (localId 2, .word),
    (localId 3, .bool), (localId 4, .word), (localId 5, .bool), (localId 6, .bool)]
private def word (value : Nat) : Core.Value := .word (Core.Word.ofNatModulo value)
private def environment (condition nestedCondition : Bool) : Resolved.Environment :=
  [(localId 99, .unit), (localId 0, .bool condition), (localId 1, word 11), (localId 2, word 22),
    (localId 3, .bool nestedCondition), (localId 4, word 0),
    (localId 5, .bool false), (localId 6, .bool true)]
private def store : Core.Store := [word 91, .bool false]

private def relabel (id : Resolved.LocalId) : Resolved.LocalId :=
  { id with binderIndex := id.binderIndex + 10 }
private theorem relabel_injective : Function.Injective relabel := by
  intro left right same
  cases left with
  | mk leftOwner leftIndex =>
      cases right with
      | mk rightOwner rightIndex =>
          have owners := congrArg Resolved.LocalId.owner same
          have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
          cases owners; cases indices; rfl

private def parsedExpression (content : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-local.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  assertTrue lexed.diagnostics.isEmpty s!"{content}: unexpected lexical diagnostic"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      assertTrue next.atEnd s!"{content}: unconsumed source tokens"
      assertTrue next.diagnostics.isEmpty s!"{content}: unexpected parse diagnostic"
      pure source
  | .reject failure _ => throw (IO.userError s!"{content}: rejected expression {reprStr failure}")
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def checkRun (content : String) (expectedCore : Core.Expr)
    (condition nestedCondition : Bool) (expectedValue : Core.Value) (required : Nat)
    (expectedType : Core.Ty := .word) : IO Unit := do
  let source ← parsedExpression content
  let checked := elaborateLocalExpression? names context source
  assertTrue (decide (checked = some (expectedCore, expectedType))) s!"{content}: wrong checked Core expression"
  let some (actualCore, _) := checked
    | throw (IO.userError s!"{content}: no checked expression")
  let initial := Core.State.initial actualCore
    (Resolved.LocalScope.values (environment condition nestedCondition)) store
  assertTrue (decide (Core.runStateful required initial = .done expectedValue store))
    s!"{content}: wrong value or store at sufficient fuel"
  assertTrue (decide (Core.runStateful (required + 5) initial = .done expectedValue store))
    s!"{content}: larger fuel changed result"
  assertTrue (match Core.runStateful (required - 1) initial with
    | .outOfFuel _ => true
    | _ => false) s!"{content}: expected exhaustion just below exact transition count"

private def checkUnsupported (content : String) : IO Unit := do
  let source ← parsedExpression content
  assertTrue (decide (resolveLocalExpression? names source = none))
    s!"{content}: unsupported or unmapped source unexpectedly resolved"
  assertTrue (decide (elaborateLocalExpression? names context source = none))
    s!"{content}: unsupported or unmapped source unexpectedly checked"

private def checkIllTyped (content : String) : IO Unit := do
  let source ← parsedExpression content
  assertTrue (resolveLocalExpression? names source).isSome s!"{content}: expected name resolution"
  assertTrue (decide (elaborateLocalExpression? names context source = none))
    s!"{content}: ill-typed expression unexpectedly checked"

private def bundledInputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh (localId 0).owner "e" .word (word 22) .word).bindFresh
    (localId 0).owner "t" .word (word 11) .word).bindFresh
      (localId 0).owner "c" .bool (.bool choice) .bool

private def checkBundledRun : IO Unit := do
  let source ← parsedExpression "c ? t : e"
  let negatedSource ← parsedExpression "!c ? t : e"
  let conjunction ← parsedExpression "c && !c"
  let disjunction ← parsedExpression "c || !c"
  let complemented ← parsedExpression "~t"
  let literalCondition ← parsedExpression "c ? 7 : ~0xaF"
  let unsupported ← parsedExpression "c ? t : missing"
  for choice in [false, true] do
    let inputs := bundledInputs choice
    let expectedCore : Core.Expr := .ifE (.var 0) (.var 1) (.var 2)
    let expectedValue := if choice then word 11 else word 22
    assertTrue (decide (inputs.check? source = some (expectedCore, .word)))
      "bundled source check returned the wrong Core or type"
    assertTrue (decide (inputs.run? 4 source store = some (.word, .done expectedValue store)))
      "bundled source execution changed the checked type, selected value, or store"
    assertTrue (decide (inputs.run? 0 source store = some (.word,
      .outOfFuel (Core.State.initial expectedCore
        (Resolved.LocalScope.values inputs.environment) store))))
      "bundled source fuel exhaustion was lost or confused with failed checking"
    assertTrue (decide (inputs.run? 4 unsupported store = none))
      "bundled source execution skipped whole-expression checking"
    let extended := inputs.bindFresh (localId 0).owner "extra" .unit .unit .unit
    assertTrue (decide (extended.check? source = some (expectedCore.weakenAt 0, .word)))
      "adding an unused source name did not preserve the checked type and shift free positions"
    assertTrue (decide (extended.run? 4 source store = inputs.run? 4 source store))
      "adding an unused source name changed the completed conditional result"
    assertTrue (decide (inputs.run? 6 negatedSource store =
      some (.word, .done (if choice then word 22 else word 11) store)))
      "bundled source negation did not select the opposite branch"
    assertTrue (decide (extended.run? 6 negatedSource store = inputs.run? 6 negatedSource store))
      "unused input insertion changed a parsed negated condition"
    assertTrue (decide (inputs.run? (if choice then 6 else 4) conjunction store =
      some (.bool, .done (.bool false) store))) "bundled conjunction did not short-circuit correctly"
    assertTrue (decide (inputs.run? (if choice then 4 else 6) disjunction store =
      some (.bool, .done (.bool true) store))) "bundled disjunction did not short-circuit correctly"
    assertTrue (decide (inputs.run? 3 complemented store =
      some (.word, .done (.word (Core.Word.ofNatModulo 11).bitNot) store)))
      "bundled Word complement did not preserve the Word-only result"
    assertTrue (decide (extended.run? 6 conjunction store = inputs.run? 6 conjunction store ∧
      extended.run? 6 disjunction store = inputs.run? 6 disjunction store))
      "unused input insertion changed parsed short-circuit execution"
    let literalValue := if choice then word 7 else .word (Core.Word.ofNatModulo 175).bitNot
    let literalFuel := if choice then 4 else 6
    assertTrue (decide (inputs.run? literalFuel literalCondition store =
      some (.word, .done literalValue store) ∧
      extended.run? literalFuel literalCondition store = inputs.run? literalFuel literalCondition store))
      "parsed literal branches changed under unused input insertion"
    let renamed := extended.mapIds relabel relabel_injective
    for checkedSource in [source, negatedSource, conjunction, disjunction, complemented,
        literalCondition, unsupported] do
      assertTrue (decide (renamed.check? checkedSource = extended.check? checkedSource))
        "identity relabeling changed parsed checked Core or type"
      for fuel in [0, 2, 4, 6] do
        assertTrue (decide (renamed.run? fuel checkedSource store = extended.run? fuel checkedSource store))
          "identity relabeling changed a parsed result or exact suspended state"

private def checkShortCircuitRuns : IO Unit := do
  let conjunction : Core.Expr := .ifE (.var 1) (.var 4) (.bool false)
  let disjunction : Core.Expr := .ifE (.var 1) (.bool true) (.var 4)
  for choice in [false, true] do
    for rightChoice in [false, true] do
      checkRun "c && d" conjunction choice rightChoice (.bool (choice && rightChoice)) 4 .bool
      checkRun "c || d" disjunction choice rightChoice (.bool (choice || rightChoice)) 4 .bool
      checkRun "c && !d ? t : e"
        (.ifE (.ifE (.var 1) (.unary .boolNot (.var 4)) (.bool false)) (.var 2) (.var 3))
        choice rightChoice (if choice && !rightChoice then word 11 else word 22)
        (if choice then 9 else 7)
      checkRun "c || !d ? t : e"
        (.ifE (.ifE (.var 1) (.bool true) (.unary .boolNot (.var 4))) (.var 2) (.var 3))
        choice rightChoice (if choice || !rightChoice then word 11 else word 22)
        (if choice then 7 else 9)
  let precedence : Core.Expr := .ifE
    (.ifE (.var 1) (.bool true) (.ifE (.var 4) (.unary .boolNot (.var 6)) (.bool false)))
    (.var 2) (.var 3)
  checkRun "c || d && !true ? t : e" precedence true false (word 11) 7
  checkRun "c || d && !true ? t : e" precedence false true (word 11) 12
  checkRun "c || d && !true ? t : e" precedence false false (word 22) 10
  checkRun "(c || d) && !false ? t : e"
    (.ifE (.ifE disjunction (.unary .boolNot (.var 7)) (.bool false)) (.var 2) (.var 3))
    true false (word 22) 12
  let nested : Core.Expr := .ifE
    (.ifE (.var 1) (.ifE (.var 4) (.unary .boolNot (.var 1)) (.var 1)) (.bool false))
    (.var 2) (.var 3)
  checkRun "c && (d ? !c : c) ? t : e" nested false true (word 22) 7
  checkRun "c && (d ? !c : c) ? t : e" nested true true (word 22) 12
  checkRun "c && (d ? !c : c) ? t : e" nested true false (word 11) 10
  checkUnsupported "c && missing"
  checkIllTyped "c || 7"
  checkUnsupported "c || \"7\""
  checkIllTyped "c & d"
  checkIllTyped "c | d"
  checkIllTyped "c ^ d"
  checkIllTyped "c && n"
  checkIllTyped "n || c"

private def checkWordComplementRuns : IO Unit := do
  checkRun "~n" (.unary .wordNot (.var 5)) false false (.word Core.Word.maximum) 3
  checkRun "~~n" (.unary .wordNot (.unary .wordNot (.var 5))) true true (word 0) 5
  checkRun "~((t))" (.unary .wordNot (.var 2)) false false
    (.word (Core.Word.ofNatModulo 11).bitNot) 3
  for choice in [false, true] do
    checkRun "~(c ? t : e)" (.unary .wordNot (.ifE (.var 1) (.var 2) (.var 3)))
      choice false (.word (Core.Word.ofNatModulo (if choice then 11 else 22)).bitNot) 6
    checkRun "c ? t : ~e" (.ifE (.var 1) (.var 2) (.unary .wordNot (.var 3)))
      choice true (if choice then word 11 else .word (Core.Word.ofNatModulo 22).bitNot)
      (if choice then 4 else 6)
  checkUnsupported "~missing"
  checkRun "~7" (.unary .wordNot (.word (Core.Word.ofNatModulo 7)))
    false false (.word (Core.Word.ofNatModulo 7).bitNot) 3
  checkRun "~~((0007))" (.unary .wordNot (.unary .wordNot (.word (Core.Word.ofNatModulo 7))))
    false false (word 7) 5
  checkUnsupported "~\"7\""
  checkIllTyped "!7"
  checkIllTyped "!~n"
  checkIllTyped "~(!c)"
  checkIllTyped "(~n) ? t : e"

def frontendParsedLocalExpressionTests : IO Unit := do
  let simple : Core.Expr := .ifE (.var 1) (.var 2) (.var 3)
  checkRun "c ? t : e" simple true false (word 11) 4
  checkRun "c ? t : e" simple false true (word 22) 4
  checkRun "(c) ? ((t)) : e" simple true false (word 11) 4
  checkRun " /* before */ c ? /* branch */ t : e " simple false false (word 22) 4
  let rightNested : Core.Expr := .ifE (.var 1) (.var 2) (.ifE (.var 4) (.var 3) (.var 5))
  checkRun "c ? t : d ? e : n" rightNested true false (word 11) 4
  checkRun "c ? t : d ? e : n" rightNested false true (word 22) 7
  checkRun "c ? t : d ? e : n" rightNested false false (word 0) 7
  checkRun "c ? d ? t : e : n"
    (.ifE (.var 1) (.ifE (.var 4) (.var 2) (.var 3)) (.var 5)) true false (word 22) 7
  checkRun "(c ? d : false) ? t : e"
    (.ifE (.ifE (.var 1) (.var 4) (.var 7)) (.var 2) (.var 3)) false false (word 11) 7
  checkRun "true ? t : e" (.ifE (.var 6) (.var 2) (.var 3)) true true (word 22) 4
  checkRun "false ? t : e" (.ifE (.var 7) (.var 2) (.var 3)) false false (word 11) 4
  let negatedCondition : Core.Expr := .ifE (.unary .boolNot (.var 1)) (.var 2) (.var 3)
  checkRun "!c ? t : e" negatedCondition false false (word 11) 6
  checkRun "(!c) ? t : e" negatedCondition true true (word 22) 6
  checkRun "!!c ? t : e"
    (.ifE (.unary .boolNot (.unary .boolNot (.var 1))) (.var 2) (.var 3)) true false (word 11) 8
  checkRun "c ? t : (!d ? e : n)"
    (.ifE (.var 1) (.var 2) (.ifE (.unary .boolNot (.var 4)) (.var 3) (.var 5)))
    false false (word 22) 9
  checkRun "!true ? t : e"
    (.ifE (.unary .boolNot (.var 6)) (.var 2) (.var 3)) true true (word 11) 6
  checkRun "!false ? t : e"
    (.ifE (.unary .boolNot (.var 7)) (.var 2) (.var 3)) false false (word 22) 6
  checkUnsupported "c ? t : missing"
  for choice in [false, true] do
    checkRun "c ? t : 7" (.ifE (.var 1) (.var 2) (.word (Core.Word.ofNatModulo 7)))
      choice false (if choice then word 11 else word 7) 4
    checkRun "c ? 7 : 0xaF"
      (.ifE (.var 1) (.word (Core.Word.ofNatModulo 7)) (.word (Core.Word.ofNatModulo 175)))
      choice true (if choice then word 7 else word 175) 4
  checkUnsupported "c ? t : \"7\""
  checkIllTyped "7 ? t : e"
  checkIllTyped "c ? 7 : d"
  checkRun "t + e" (.binary .wordAdd (.var 2) (.var 3)) false false (word 33) 5
  checkRun "t - e" (.binary .wordSub (.var 2) (.var 3)) false false
    (.word ((Core.Word.ofNatModulo 11).sub (Core.Word.ofNatModulo 22))) 5
  checkRun "t * e" (.binary .wordMul (.var 2) (.var 3)) false false (word 242) 5
  checkUnsupported "t(e)"
  checkIllTyped "~c"
  checkIllTyped "n ? t : e"
  checkIllTyped "c ? t : d"
  checkIllTyped "c ? t : (d ? e : c)"
  checkIllTyped "(!n) ? t : e"
  let rejectsTrailingTokens ← try
    let _ ← parsedExpression "t e"
    pure false
  catch error => pure (error.toString == "t e: unconsumed source tokens")
  assertTrue rejectsTrailingTokens "source-text test helper accepted an incomplete expression parse"
  checkBundledRun
  checkShortCircuitRuns
  checkWordComplementRuns

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalFragmentEntries
/-! Exact parsed entry provenance feeds structural insertion laws. Independent
Core paths fix costs; transported suspended states need not be identical. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace LocalFragmentEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LocalFragmentEntry", by decide⟩], by decide⟩⟩, 17⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def table (type : Core.Ty) : TypeNameTable := [(["T"], type), (["Bool"], .bool)]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "local-fragment-entry.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, content.utf8ByteSize⟩) && source.span.contains source.value.body.span) "original complete ranges changed"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent type leaf missing")
  | ⟨_, .tuple [left, right]⟩ =>
      let a ← meaning types left; let b ← meaning types right
      return ⟨.product a.type b.type, by rw [atSource]; exact .pair a.evidence b.evidence⟩
  | _ => throw (IO.userError "outside independent annotation grammar")
termination_by sizeOf source
private structure Parameters (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types owner initial params inputs
private def parameters (types : TypeNameTable) (initial : LocalTypeInputs)
    (params : List Syntax.FunctionParameter) : IO (Parameters types initial params) := do
  match atParams : params with
  | [] => return ⟨initial, by rw [atParams]; exact .nil⟩
  | ⟨span, .typed none name annotation⟩ :: rest =>
      check (span.contains name.span && span.contains annotation.span) "original parameter range changed"
      let m ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← parameters types (initial.bindFresh owner name.value m.type) rest
        return ⟨tail.inputs, by rw [atParams]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate parameter")
  | _ => throw (IO.userError "unsupported original parameter")
private structure Expression (s : LocalTypeInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.ids resolved core
  typing : Resolved.HasType s.context resolved type
private def expression (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Expression s source) := do
  match atSource : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "independent context row missing")
      | none => throw (IO.userError "independent name missing")
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← expression s left; let b ← expression s right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        by rw [atSource]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing⟩
  | _ => throw (IO.userError "outside independent expression grammar")
termination_by sizeOf source
private structure Body (types : TypeNameTable) (s : LocalTypeInputs) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : TypedLetReturnTreeElaborates types owner s source core type
private def body (types : TypeNameTable) (s : LocalTypeInputs) (source : Syntax.Block) : IO (Body types s source) := do
  match atSource : source with
  | ⟨_, [⟨_, .returnStmt (some returned)⟩]⟩ =>
      let a ← expression s returned
      return ⟨a.core, a.type, by rw [atSource]; exact .single (.expression a.resolution
        (by simpa only [LocalTypeInputs.context_ids] using a.lowered) a.typing)⟩
  | ⟨span, ⟨ls, .letDecl name none (some initializer)⟩ :: rest⟩ =>
      check (ls.contains name.span && ls.contains initializer.span) "original none annotation spans changed"
      if unused : name.value ∉ s.names.map Prod.fst then
        let a ← expression s initializer
        let b ← body types (s.bindFresh owner name.value a.type) ⟨span, rest⟩
        return ⟨.letE a.core b.core, b.type, by rw [atSource]; exact .inferred unused a.resolution a.lowered a.typing b.evidence⟩
      else throw (IO.userError "ancestor name reused")
  | ⟨span, ⟨_, .expression source true⟩ :: rest⟩ =>
      let a ← expression s source; let b ← body types s ⟨span, rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0), b.type,
        by rw [atSource]; exact .discard a.resolution a.lowered a.typing b.evidence⟩
  | ⟨_, [⟨_, .ifThen guard yes (some no)⟩]⟩ =>
      let c ← expression s guard; let a ← body types s yes; let b ← body types s no
      if ct : c.type = .bool then
        if bt : b.type = a.type then
          return ⟨.ifE c.core a.core b.core, a.type, by rw [atSource]; exact .conditional c.resolution c.lowered (ct ▸ c.typing) a.evidence (bt ▸ b.evidence)⟩
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "guard is not Bool")
  | _ => throw (IO.userError "outside independent body grammar")
termination_by sizeOf source
private structure Compilation (types : TypeNameTable) (source : Syntax.FunctionDecl) where
  compiled : CompiledRuntimeFunction
  evidence : RuntimeFunctionCompiles types owner source compiled
private def compile (types : TypeNameTable) (source : Syntax.FunctionDecl) : IO (Compilation types source) := do
  let ps ← parameters types .empty source.value.signature.parameters.elements
  let b ← body types ps.inputs source.value.body
  match atClause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [returned]⟩⟩ =>
      let m ← meaning types returned
      if same : m.type = b.type then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          return ⟨⟨ps.inputs, b.core, b.type⟩, ⟨⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2,
            by rw [atClause]; exact .single (same ▸ m.evidence)⟩, ps.evidence, b.evidence⟩⟩
        else throw (IO.userError "header policy rejected")
      else throw (IO.userError "return contract differs")
  | _ => throw (IO.userError "return clause is not singleton")
private def core : Core.Expr := .letE (.var 2) (.ifE (.var 1)
  (.letE (.var 2) (.pair (.var 1) (.var 0))) (.pair (.var 2) (.var 0)))
private def cost (c : Bool) : Nat := if c then 14 else 11
private def result (x y : Core.Value) (c : Bool) : Core.Value := if c then .pair x y else .pair y x
private theorem paths (x y : Core.Value) (c : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (cost c) ⟨.eval core [.bool c, y, x], k, store⟩ ⟨.ret (result x y c), k, store⟩ := by
  cases c <;> simp only [cost, result, Bool.false_eq_true, ↓reduceIte]
  · exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterIf (.cons (.var rfl)
      (.cons .chooseFalse (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl))))))))))
  · exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterIf (.cons (.var rfl)
      (.cons .chooseTrue (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterPair (.cons (.var rfl)
        (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))))))))))
private def content := "function choose(x: T,y: T,c: Bool) returns((T,T)){let z=x;if(c){let q=y;return (z,q);}else{return (y,z);}}"
private def verify (x y : TypedRuntimeArgument) (same : y.type = x.type) (c : Bool) : IO Unit := do
  let source ← parsed content; let proof ← compile (table x.type) source
  check (decide (proof.compiled.core = core ∧ proof.compiled.returnType = .product x.type x.type ∧
    proof.compiled.inputs.names = [("c", ⟨owner, 2⟩), ("y", ⟨owner, 1⟩), ("x", ⟨owner, 0⟩)] ∧
    proof.compiled.inputs.context.values = [.bool, x.type, x.type])) "independent Core/type/parameter layout changed"
  let fragment := proof.evidence.localFragment
  have _ := compileRuntimeFunction?_localFragment proof.evidence.complete
  let args := [x, y, (⟨.bool, .bool c, .bool⟩ : TypedRuntimeArgument)]
  have _ : args.map (·.type) = [x.type, x.type, .bool] := by simp only [args, List.map_cons, List.map_nil, same]
  match accepted : prepareRuntimeFunction? (table x.type) owner source args with
  | none => throw (IO.userError "typed actual preparation failed")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound accepted
      have _ := preparation.localFragment
      have _ := prepareRuntimeFunction?_localFragment accepted
      check (decide (prepared.core = core ∧ prepared.returnType = .product x.type x.type ∧
        prepared.inputs.ids = proof.compiled.inputs.ids ∧ prepared.inputs.names = proof.compiled.inputs.names ∧
        prepared.inputs.environment.values = [.bool c, y.value, x.value])) "original arguments/parameter-only record changed"
      have _ := preparation.compiles.result_unique proof.evidence
      let forged : PreparedRuntimeFunction := { prepared with core := .letE (.lambda .word .word (.var 0)) (prepared.core.weakenAt 0) }
      have _ : ¬ RuntimeFunctionPrepares (table x.type) owner source args forged := by
        intro impossible
        cases impossible.localFragment with
        | letE nonlocal _ => cases nonlocal
      if exactCore : proof.compiled.core = core then
        have localCore : core.LocalFragment := exactCore ▸ fragment
        for store in [[], [w 91, .cellRef .word 999]] do
          let original := Core.State.initial core [.bool c, y.value, x.value] store
          let expected := result x.value y.value c
          for split in [0, 1, 2, 3] do
            let leading := [.bool c, y.value, x.value].take split
            let suffix := [.bool c, y.value, x.value].drop split
            have full : leading ++ suffix = [.bool c, y.value, x.value] := List.take_append_drop split _
            for inserted in [Core.Value.unit, .cellRef .word 707, .closure .word .word (.var 90) [], .pair (w 7) .unit] do
              let shifted := Core.State.initial (core.weakenAt leading.length) (leading ++ inserted :: suffix) store
              have path : Core.Steps (cost c) (.initial core (leading ++ suffix) store) (.final expected store) := by
                simpa only [full, Core.State.initial, Core.State.final, expected] using paths x.value y.value c store []
              have moved := localCore.steps_insert leading suffix inserted path []
              have _ := localCore.steps_reflect_insert leading suffix inserted moved []
              have _ := (localCore.steps_insert_iff leading suffix inserted).mpr path
              have _ := (localCore.evaluates_insert_iff leading suffix inserted).mpr (Core.steps_from_initial_sound path)
              have _ := (localCore.evaluates_insert_iff leading suffix inserted).mp (Core.steps_from_initial_sound moved)
              for k in [[], [.letBody (.var 0) [w 9]], [.unaryApply .wordNot]] do
                have _ := localCore.steps_insert leading suffix inserted path k
                pure ()
              for fuel in List.range (cost c + 3) do
                check (decide (runRuntimeFunction? (table x.type) owner source args fuel store =
                  some (.product x.type x.type, Core.runStateful fuel original)))
                  "whole runtime entry differs from the original machine"
                check (match Core.runStateful fuel original, Core.runStateful fuel shifted with
                  | .done a st, .done b tt => decide (cost c ≤ fuel ∧ a = expected ∧ b = expected ∧ st = store ∧ tt = store)
                  | .outOfFuel _, .outOfFuel _ => decide (fuel < cost c)
                  | _, _ => false) "transported threshold/value/own store changed"
              for spent in List.range (cost c) do
                match left : Core.runStateful spent original, right : Core.runStateful spent shifted with
                | .outOfFuel lc, .outOfFuel rc =>
                    have _ := (paths x.value y.value c store []).residual_of_outOfFuel left
                    have _ := moved.residual_of_outOfFuel right
                    have _ := Core.runStateful_resume left (cost c - spent)
                    have _ := Core.runStateful_resume right (cost c - spent)
                    check (decide (Core.runStateful (cost c - spent) lc = .done expected store ∧
                      Core.runStateful (cost c - spent) rc = .done expected store)) "genuine saved states or exact residual changed"
                    if spent = 2 then check (decide (lc ≠ rc)) "saved environments were incorrectly equated"
                    if spent = cost c - 1 then check (decide (lc = rc)) "final value-only frames did not coalesce"
                | _, _ => throw (IO.userError "genuine paired checkpoints missing")
          check (decide (Core.runStateful 2 original = .outOfFuel ⟨.ret x.value,
            [.letBody (.ifE (.var 1) (.letE (.var 2) (.pair (.var 1) (.var 0))) (.pair (.var 2) (.var 0))) [.bool c, y.value, x.value]], store⟩))
            "explicit old-scope let frame changed"
      else throw (IO.userError "exact independent Core changed")
private theorem typedInsertion {source : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} {types : TypeNameTable}
    (evidence : RuntimeFunctionCompiles types owner source compiled) (leading suffix : Core.Context) (inserted : Core.Ty)
    (definitions : Core.DataEnvironment) :
    Core.infer? (leading ++ inserted :: suffix) (compiled.core.weakenAt leading.length) definitions =
      Core.infer? (leading ++ suffix) compiled.core definitions :=
  evidence.localFragment.infer_insert leading suffix inserted definitions
private theorem forgedNotLocal (body : Core.Expr) :
    ¬ (Core.Expr.letE (.lambda .word .word (.var 0)) body).LocalFragment := by
  intro localBody
  cases localBody with
  | letE value _ => cases value
private theorem copyPaths (value : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 4 ⟨.eval (.letE (.var 0) (.var 1)) [value], k, store⟩ ⟨.ret value, k, store⟩ :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))
private def discardedCopy : IO Unit := do
  let source ← parsed "function f(x:T) returns(T){x;return x;}"
  let proof ← compile (table .word) source
  check (decide (proof.compiled.core = .letE (.var 0) (.var 1) ∧ proof.compiled.returnType = .word ∧
    proof.compiled.inputs.names = [("x", ⟨owner, 0⟩)])) "original discard copy provenance changed"
  have _ := proof.evidence.localFragment
  for store in [[], [w 91]] do
    for fuel in List.range 7 do
      have _ := copyPaths (w 9) store []
      check (match runRuntimeFunction? (table .word) owner source [⟨.word, w 9, .word⟩] fuel store with
        | some (.word, .done value final) => decide (4 ≤ fuel ∧ value = w 9 ∧ final = store)
        | some (.word, .outOfFuel checkpoint) => decide (fuel < 4 ∧ Core.runStateful (4 - fuel) checkpoint = .done (w 9) store)
        | _ => false) "original discarded copy is not strict cost four"
end LocalFragmentEntries
open LocalFragmentEntries

def frontendParsedLocalFragmentEntryTests : IO Unit := do
  discardedCopy
  verify ⟨.word, w 9, .word⟩ ⟨.word, w 2, .word⟩ rfl true
  verify ⟨.word, w 9, .word⟩ ⟨.word, w 2, .word⟩ rfl false
  for c in [false, true] do
    verify ⟨.cell .word, .cellRef .word 900, .cellRef⟩ ⟨.cell .word, .cellRef .word 901, .cellRef⟩ rfl c
    verify ⟨.function .word .word, .closure .word .word (.var 0) [], .closure .nil (.var rfl)⟩
      ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩ rfl c
  let source ← parsed content
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨99⟩) (.cell (.namedData ⟨13⟩)), .word] do
    let proof ← compile (table type) source
    let fragment := proof.evidence.localFragment
    for inserted in [Core.Ty.unit, .namedData ⟨101⟩, .function (.namedData ⟨7⟩) (.cell .word)] do
      have _ := typedInsertion proof.evidence [.bool] [type, type] inserted
      have forward := (fragment.hasType_insert_iff [] proof.compiled.inputs.context.values inserted).mpr proof.evidence.core_hasType
      have _ := (fragment.hasType_insert_iff [] proof.compiled.inputs.context.values inserted).mp forward
      check (decide (Core.infer? (inserted :: proof.compiled.inputs.context.values) (proof.compiled.core.weakenAt 0) =
        some (.product type type))) "value-free nominal type insertion changed"
    let forged : CompiledRuntimeFunction := { proof.compiled with core := .letE (.lambda .word .word (.var 0)) (proof.compiled.core.weakenAt 0) }
    have _ : ¬ RuntimeFunctionCompiles (table type) owner source forged := fun impossible => forgedNotLocal _ impossible.localFragment
    check (decide (Core.infer? forged.inputs.context.values forged.core = some forged.returnType)) "same-typed forged record contrast became trivial"
  for text in ["function f(x:T,c:Bool) returns(T){if(c){return x;}else{return missing;}}",
      "function f(x:T,x:T) returns(T){return x;}",
      "function f(x:T) returns(Bool){return x;}", "function f<T>(x:T) returns(T){return x;}"] do
    check ((compileRuntimeFunction? (table .word) owner (← parsed text)).isNone) "whole guard or unchanged statement boundary disappeared"
  have _ : Core.HasType [.cell .word] (.loadCell (.var 0)) .word := .loadCell (.var rfl)
  have _ : ¬ (Core.Expr.loadCell (.var 0)).LocalFragment := by intro impossible; cases impossible
  let invalid ← parsed "function f(x:T,c:Bool) returns(T){if(c){return x;}else{return missing;}}"
  let some actual := bindRuntimeParameters? (table .word) owner invalid.value.signature.parameters.elements
    [⟨.word, w 9, .word⟩, ⟨.bool, .bool true, .bool⟩] | throw (IO.userError "original invalid body parameter binding failed")
  check (decide (evaluateTypedLetReturnTreeWithCost? owner actual.names actual.environment invalid.value.body = some (w 9, 4) ∧
    compileRuntimeFunction? (table .word) owner invalid = none)) "raw selected success replaced whole-source membership evidence"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalFragments
/-! Exact parsed provenance supplies fragment membership, then existing insertion
laws transport independently hand-composed paths. Suspensions are not equated. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace LocalFragments
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Inferred", by decide⟩], by decide⟩⟩, 17⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def inputs (type : Core.Ty) : LocalTypeInputs := ⟨[
  ⟨"c", ⟨other, 999⟩, .bool⟩, ⟨"r", id 2, .word⟩, ⟨"x", id 7, type⟩, ⟨"x", id 3, .bool⟩], by
    change ([⟨other, 999⟩, id 2, id 7, id 3] : List Resolved.LocalId).Nodup; decide⟩
private def env (value : Core.Value) (choice : Bool) : Resolved.Environment :=
  [(⟨other, 999⟩, .bool choice), (id 2, w 2), (id 7, value), (id 3, .bool false)]
private def stores : List Core.Store := [[], [w 91, .cellRef .word 40, .bool false]]
private def parsed (content : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main, "inferred.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok body next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"complete block rejected: {content}")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (body.span = ⟨file.id, 0, content.utf8ByteSize⟩)) "original block/range changed"
  return body
private structure Expression (s : LocalTypeInputs) (e : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.ids resolved core
  typing : Resolved.HasType s.context resolved type
  raw : LocalExpressionEvaluatesWithCost s.names e store source value store cost
  paths : ∀ k, Core.Steps cost ⟨.eval core e.values, k, store⟩ ⟨.ret value, k, store⟩
private def expression (s : LocalTypeInputs) (e : Resolved.Environment) (aligned : e.ids = s.ids)
    (store : Core.Store) (source : Syntax.Expr) : IO (Expression s e store source) := do
  match atSource : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | none => throw (IO.userError "independent name absent")
      | some binder =>
          match typed : s.context.lookup? binder, found : e.lookup? binder, indexed : Resolved.LocalScope.index? s.ids binder with
          | some type, some value, some index =>
              let position := Resolved.LocalScope.index?_iff.mp indexed
              return ⟨.var binder, .var index, type, value, 1,
                by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named), .var position,
                .var (Resolved.LocalScope.lookup?_iff.mp typed),
                by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found),
                fun _ => .cons (.var ((Resolved.LocalScope.lookup_iff_getElem? (aligned.symm ▸ position)).mp
                  (Resolved.LocalScope.lookup?_iff.mp found))) .refl⟩
          | _, _, _ => throw (IO.userError "independent row absent")
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, .unit, .unit, .unit, 1,
      by rw [atSource]; exact .unit, .unit, .unit, by rw [atSource]; exact .unit, fun _ => .cons .unit .refl⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← expression s e aligned store left; let b ← expression s e aligned store right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type, .pair a.value b.value, a.cost + b.cost + 3,
        by rw [atSource]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing,
        by rw [atSource]; exact .pair a.raw b.raw, fun k => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core e.values :: k)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← expression s e aligned store left; let b ← expression s e aligned store right
      match av : a.value, bv : b.value with
      | .word x, .word y =>
          if leftType : a.type = .word then
            if rightType : b.type = .word then
            return ⟨.binary .wordSub a.resolved b.resolved, .binary .wordSub a.core b.core, .word, .word (x.sub y), a.cost + b.cost + 3,
              by rw [atSource]; exact .subtract a.resolution b.resolution, .binary a.lowered b.lowered,
              .binary (show Resolved.HasType s.context a.resolved .word from leftType ▸ a.typing)
                (show Resolved.HasType s.context b.resolved .word from rightType ▸ b.typing),
              by rw [atSource]; exact .subtract (av ▸ a.raw) (bv ▸ b.raw), fun k => by
                have path := Core.Steps.cons .enterBinary ((av ▸ a.paths (.binaryRight .wordSub b.core e.values :: k)).trans
                  (.cons .enterBinaryRight ((bv ▸ b.paths _).trans (.cons (.applyBinary rfl) .refl))))
                simpa only [Nat.add_assoc] using path⟩
            else throw (IO.userError "right is not Word")
          else throw (IO.userError "left is not Word")
      | _, _ => throw (IO.userError "actual operand not Word")
  | _ => throw (IO.userError "outside independent expression script")
termination_by sizeOf source
private structure Certificate (s : LocalTypeInputs) (e : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  elaboration : TypedLetReturnTreeElaborates types owner s body core type
  raw : TypedLetReturnTreeEvaluatesWithCost owner s.names e store body value store cost
  paths : ∀ k, Core.Steps cost ⟨.eval core e.values, k, store⟩ ⟨.ret value, k, store⟩
private def certify (s : LocalTypeInputs) (e : Resolved.Environment) (aligned : e.ids = s.ids)
    (store : Core.Store) (body : Syntax.Block) : IO (Certificate s e store body) := do
  match atBody : body with
  | ⟨_, [⟨_, .returnStmt (some source)⟩]⟩ =>
      let a ← expression s e aligned store source
      return ⟨a.core, a.type, a.value, a.cost,
        by rw [atBody]; exact .single (.expression a.resolution (by simpa only [LocalTypeInputs.context_ids] using a.lowered) a.typing),
        by rw [atBody]; exact .single (.expression a.raw), a.paths⟩
  | ⟨span, ⟨_, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      if unused : name.value ∉ s.names.map Prod.fst then
        let a ← expression s e aligned store initializer
        let next := s.bindFresh owner name.value a.type
        let b ← certify next ((Resolved.freshLocalId owner s.ids, a.value) :: e)
          (by simpa only [next, LocalTypeInputs.bindFresh_ids, Resolved.LocalScope.ids, List.map_cons]
            using congrArg (List.cons _) aligned) store ⟨span, rest⟩
        let rawTail := by simpa only [next, LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using b.raw
        let common := fun elaboration raw => (⟨.letE a.core b.core, b.type, b.value, a.cost + b.cost + 2, elaboration, raw, fun k => by
          have path := Core.Steps.cons .enterLet ((a.paths (.letBody b.core e.values :: k)).trans (.cons .bindLet (b.paths k)))
          simpa only [Resolved.LocalScope.values, List.map_cons, Nat.add_assoc] using path⟩ : Certificate s e store body)
        match atAnnotation : annotation with
        | none => return (common (by rw [atBody, atAnnotation]; exact .inferred unused a.resolution a.lowered a.typing b.elaboration)
            (by rw [atBody, atAnnotation]; exact .inferred a.raw (by simpa only [LocalTypeInputs.names_ids] using rawTail)))
        | some written =>
            match atWritten : written with
            | ⟨_, .named name none⟩ =>
                if meaning : types.lookup? (qualifiedTypeNameKey name) = some a.type then
                  return (common (by rw [atBody, atAnnotation, atWritten]; exact .binding (.named (TypeNameTable.lookup?_iff.mp meaning)) unused a.resolution a.lowered a.typing b.elaboration)
                    (by rw [atBody, atAnnotation]; exact .binding a.raw (by simpa only [LocalTypeInputs.names_ids] using rawTail)))
                else throw (IO.userError "written annotation disagrees")
            | _ => throw (IO.userError "outside independent annotation script")
      else throw (IO.userError "written name is already used")
  | ⟨span, ⟨_, .expression source true⟩ :: rest⟩ =>
      let a ← expression s e aligned store source
      let b ← certify s e aligned store ⟨span, rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0), b.type, b.value, a.cost + b.cost + 2,
        by rw [atBody]; exact .discard a.resolution a.lowered a.typing b.elaboration,
        by rw [atBody]; exact .discard a.raw b.raw, fun k => by
          have tail := (b.paths []).weakenAt_zero_localFragment b.elaboration.localFragment a.value k
          have path := Core.Steps.cons .enterLet ((a.paths (.letBody (b.core.weakenAt 0) e.values :: k)).trans
            (.cons .bindLet tail))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨_, [⟨_, .ifThen guard yes (some no)⟩]⟩ =>
      let c ← expression s e aligned store guard
      let a ← certify s e aligned store yes; let b ← certify s e aligned store no
      if ct : c.type = .bool then
        if bt : b.type = a.type then
        have elaboration : TypedLetReturnTreeElaborates types owner s body (.ifE c.core a.core b.core) a.type := by
          rw [atBody]; exact .conditional c.resolution c.lowered (ct ▸ c.typing) a.elaboration (bt ▸ b.elaboration)
        match cv : c.value with
        | .bool true => return ⟨.ifE c.core a.core b.core, a.type, a.value, c.cost + a.cost + 2, elaboration,
            by rw [atBody]; exact .ifTrue (cv ▸ c.raw) a.raw, fun k => by
              have path := Core.Steps.cons .enterIf ((cv ▸ c.paths (.ifBranches a.core b.core e.values :: k)).trans (.cons .chooseTrue (a.paths k)))
              simpa only [Nat.add_assoc] using path⟩
        | .bool false => return ⟨.ifE c.core a.core b.core, a.type, b.value, c.cost + b.cost + 2, elaboration,
            by rw [atBody]; exact .ifFalse (cv ▸ c.raw) b.raw, fun k => by
              have path := Core.Steps.cons .enterIf ((cv ▸ c.paths (.ifBranches a.core b.core e.values :: k)).trans (.cons .chooseFalse (b.paths k)))
              simpa only [Nat.add_assoc] using path⟩
        | _ => throw (IO.userError "actual guard not Bool")
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "guard type not Bool")
  | _ => throw (IO.userError "outside independent body script")
termination_by sizeOf body
private def checked (content : String) (inputType : Core.Ty) (actual : Core.Value) (choice : Bool)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let body ← parsed content; let s := inputs inputType; let e := env actual choice
  for store in stores do
    let cert ← certify s e rfl store body
    check (decide (cert.core = core ∧ cert.type = type ∧ cert.value = value ∧ cert.cost = cost))
      "independent original-source certificate disagreed"
    let fragment := cert.elaboration.localFragment
    check (decide (elaborateTypedLetReturnTree? types owner s body = some (core, type) ∧
      evaluateTypedLetReturnTreeWithCost? owner s.names e body = some (value, cost)))
      "original exact acceptance or raw result changed"
    for cutoff in List.range (e.values.length + 1) do
      let leading := e.values.take cutoff; let suffix := e.values.drop cutoff
      have original : Core.Steps cert.cost
          (Core.State.initial cert.core (leading ++ suffix) store) (Core.State.final cert.value store) := by
        simpa only [leading, suffix, List.take_append_drop, Core.State.initial, Core.State.final] using cert.paths []
      for inserted in [Core.Value.unit, w 81, .cellRef .word 999,
          .closure .word .word (.var 1) [w 23]] do
        let shifted := cert.core.weakenAt leading.length
        let expanded := leading ++ inserted :: suffix
        let start := Core.State.initial shifted expanded store
        let path := fragment.steps_insert leading suffix inserted original []
        have _ := fragment.steps_reflect_insert leading suffix inserted path []
        have _ := (fragment.evaluates_insert_iff leading suffix inserted).mpr
          (Core.steps_from_initial_sound original)
        for k in [[], [.letBody (.var 0) [w 17]], [.unaryApply .wordNot]] do
          have _ := fragment.steps_insert leading suffix inserted original k
          have _ := fragment.steps_reflect_insert leading suffix inserted path k
          pure ()
        for fuel in List.range (cost + 3) do
          check (match Core.runStateful fuel start with
            | .done v st => decide (cost ≤ fuel ∧ v = value ∧ st = store)
            | .outOfFuel cp => decide (fuel < cost ∧ cp.store = store)
            | _ => false) "inserted exact cost/value/store changed"
        for spent in List.range cost do
          match exhausted : Core.runStateful spent start,
              unshifted : Core.runStateful spent (.initial cert.core e.values store) with
          | .outOfFuel cp, .outOfFuel originalCp =>
              have _ := path.residual_of_outOfFuel exhausted
              have _ := (cert.paths []).residual_of_outOfFuel unshifted
              for remaining in [0, 1, cost - spent, cost - spent + 2] do
                have _ := Core.runStateful_resume exhausted remaining
                check (decide (Core.runStateful remaining cp = Core.runStateful (spent + remaining) start))
                  "inserted checkpoint was restarted"
              check (decide (Core.runStateful (cost - spent) cp = .done value store ∧
                Core.runStateful (cost - spent) originalCp = .done value store))
                "separate original/inserted residuals changed"
              if cost - spent > 1 then
                let .outOfFuel next := Core.runStateful 1 cp | throw (IO.userError "second chunk absent")
                check (decide (Core.runStateful (cost - spent - 1) next = .done value store))
                  "third inserted chunk lost its environment"
          | _, _ => throw (IO.userError "genuine original or inserted checkpoint absent")
      for insertedType in [Core.Ty.word, .namedData ⟨99⟩, .function (.namedData ⟨13⟩) (.namedData ⟨99⟩)] do
        have _ := fragment.infer_insert (s.context.values.take cutoff) (s.context.values.drop cutoff) insertedType
        check (decide (Core.infer? (s.context.values.take cutoff ++ insertedType :: s.context.values.drop cutoff)
          (cert.core.weakenAt cutoff) = some type)) "value-free type insertion changed"
private def spine (n level : Nat) : String × Core.Expr :=
  match n with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 2 else 0))
  | n + 1 =>
      let (tail, core) := spine n (level + 1)
      (s!"let z{level}" ++ (if level % 2 = 0 then "" else ": Word") ++ "=" ++
        (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail, .letE (.var (if level = 0 then 2 else 0)) core)
end LocalFragments
open LocalFragments

def frontendParsedLocalFragmentTests : IO Unit := do
  checked "{x;return x;}" .word (w 9) true (.letE (.var 2) (.var 3)) .word (w 9) 4
  checked "{return x;}" .word (w 9) true (.var 2) .word (w 9) 1
  checked "{return (x,r);}" .word (w 9) true (.pair (.var 2) (.var 1))
    (.product .word .word) (.pair (w 9) (w 2)) 5
  checked "{let z=x - r;return r;}" .word (w 9) true
    (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 2)) .word (w 2) 8
  for depth in [1, 3, 9, 20] do
    let (source, core) := spine depth 0
    checked ("{" ++ source ++ "}") .word (w 9) true core .word (w 9) (3 * depth + 1)
  for c in [false, true] do
    checked "{if(c){let z=x;return z;}else{return r;}}" .word (w 9) c
      (.ifE (.var 0) (.letE (.var 2) (.var 0)) (.var 1))
      .word (if c then w 9 else w 2) (if c then 7 else 4)
  checked "{let z=();return z;}" .word (w 9) false (.letE .unit (.var 0)) .unit .unit 4
  checked "{let z=x;return z;}" (.cell .word) (.cellRef .word 999) true
    (.letE (.var 2) (.var 0)) (.cell .word) (.cellRef .word 999) 4
  checked "{let z=x;return z;}" (.function .word .word) (.closure .word .word (.var 1) [w 7]) true
    (.letE (.var 2) (.var 0)) (.function .word .word) (.closure .word .word (.var 1) [w 7]) 4
  let body ← parsed "{let z=x;return z;}"
  match body.value with
  | [⟨span, .letDecl name none (some initializer)⟩, _] =>
      check (decide (span.startByte = 1 ∧ span.endByte = 9 ∧ name.value = "z" ∧
        initializer.span.startByte = 7 ∧ initializer.span.endByte = 8)) "original optional annotation/ranges changed"
  | _ => throw (IO.userError "original inferred-let shape changed")
  for store in stores do
    let values := (env (w 9) true).values
    let original := Core.State.initial (.letE (.var 2) (.var 0)) values store
    let shifted := Core.State.initial ((Core.Expr.letE (.var 2) (.var 0)).weakenAt 0) (.unit :: values) store
    check (decide (Core.runStateful 2 original = .outOfFuel ⟨.ret (w 9), [.letBody (.var 0) values], store⟩ ∧
      Core.runStateful 2 shifted = .outOfFuel ⟨.ret (w 9), [.letBody (.var 0) (.unit :: values)], store⟩ ∧
      Core.runStateful 2 original ≠ Core.runStateful 2 shifted)) "different captured environments were identified"
  for source in ["{let z;return x;}", "{let z=z;return x;}",
      "{let x=r;return x;}", "{return f(x);}", "{if(c){return x;}else{return missing;}}"] do
    check ((elaborateTypedLetReturnTree? types owner (inputs .word) (← parsed source)).isNone)
      "structural bridge changed a source rejection"
  let skipped ← parsed "{if(c){return x;}else{return missing;}}"
  check (decide (evaluateTypedLetReturnTreeWithCost? owner (inputs .word).names (env (w 9) true) skipped = some (w 9, 4)))
    "raw selected execution was confused with whole provenance"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendLocalExpressionExecutionProperties
/-! Open typed conditional execution, opaque values, and the identity-order boundary. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def localId_variant (index : Nat) : Resolved.LocalId :=
  ⟨⟨⟨.main, ⟨[⟨"Execution", by decide⟩], by decide⟩⟩, 0⟩, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "execution.sol"⟩, 0, 1⟩
private def name (text : String) : Syntax.Expr := ⟨span, .identifier ⟨span, text⟩⟩
private def source : Syntax.Expr := ⟨span, .conditional (name "c") span (name "l") span (name "r")⟩
private def names_variant : LocalNameTable := [("c", localId_variant 0), ("l", localId_variant 1), ("r", localId_variant 2)]
private def context_variant (type : Core.Ty) : Resolved.Context :=
  [(localId_variant 0, .bool), (localId_variant 1, type), (localId_variant 2, type)]
private def environment_variant (decision : Bool) (left right : Core.Value) : Resolved.Environment :=
  [(localId_variant 0, .bool decision), (localId_variant 1, left), (localId_variant 2, right)]
private def core : Core.Expr := .ifE (.var 0) (.var 1) (.var 2)

private theorem checked (type : Core.Ty) :
    elaborateLocalExpression? names_variant (context_variant type) source = some (core, type) := by
  apply elaborateLocalExpression?_complete
    (resolved := .ifE (.var (localId_variant 0)) (.var (localId_variant 1)) (.var (localId_variant 2)))
  · exact .conditional (.identifier .head) (.identifier (.tail (by decide) .head))
      (.identifier (.tail (by decide) (.tail (by decide) .head)))
  · exact .ifE (.var .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) (.tail (by change localId_variant 1 ≠ localId_variant 2; decide) .head)))
  · exact .ifE (.var .head) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) (.tail (by decide) .head)))

private theorem environmentTyped (decision : Bool) {left right : Core.Value} {type : Core.Ty}
    (leftTyped : Core.ValueHasType left type) (rightTyped : Core.ValueHasType right type) :
    Core.EnvironmentHasTypes (Resolved.LocalScope.values (environment_variant decision left right))
      (Resolved.LocalScope.values (context_variant type)) :=
  .cons .bool (.cons leftTyped (.cons rightTyped .nil))

theorem localConditional_typed_execution (decision : Bool) {left right : Core.Value} {type : Core.Ty}
    (leftTyped : Core.ValueHasType left type) (rightTyped : Core.ValueHasType right type)
    (store : Core.Store) :
    ∃ value required, LocalExpressionEvaluates names_variant (environment_variant decision left right) store source value store ∧
      Core.ValueHasType value type ∧ ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (Core.State.initial core
          (Resolved.LocalScope.values (environment_variant decision left right)) store) = .done value store :=
  elaborateLocalExpression?_typed_execution (checked type) rfl
    (environmentTyped decision leftTyped rightTyped) store

theorem localConditional_evaluation_iff (decision : Bool) (left right value : Core.Value)
    (type : Core.Ty) (initialStore finalStore : Core.Store) :
    LocalExpressionEvaluates names_variant (environment_variant decision left right) initialStore source value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values (environment_variant decision left right))
        initialStore core value finalStore :=
  elaborateLocalExpression?_evaluates_iff (checked type) rfl

theorem localConditional_never_faults (decision : Bool) {left right : Core.Value} {type : Core.Ty}
    (leftTyped : Core.ValueHasType left type) (rightTyped : Core.ValueHasType right type)
    (store : Core.Store) (fuel : Nat) (error : Core.MachineFault) (faultState : Core.State) :
    Core.runStateful fuel (Core.State.initial core
      (Resolved.LocalScope.values (environment_variant decision left right)) store) ≠ .fault error faultState :=
  elaborateLocalExpression?_run_never_faults (checked type) rfl
    (environmentTyped decision leftTyped rightTyped) store fuel error faultState

/-- Merely returning a cell reference needs no valid location or typed store. -/
theorem localConditional_opaque_cell (location : Nat) (store : Core.Store) :
    ∃ required, ∀ fuel, required ≤ fuel → Core.runStateful fuel
      (Core.State.initial core (Resolved.LocalScope.values
        (environment_variant true (.cellRef .word location) (.cellRef .word (location + 1)))) store) =
      .done (.cellRef .word location) store := by
  obtain ⟨value, required, evaluation, _, enough⟩ :=
    localConditional_typed_execution true (left := .cellRef .word location)
      (right := .cellRef .word (location + 1)) Core.ValueHasType.cellRef Core.ValueHasType.cellRef store
  have expected : LocalExpressionEvaluates names_variant
      (environment_variant true (.cellRef .word location) (.cellRef .word (location + 1)))
      store source (.cellRef .word location) store :=
    .ifTrue (.identifier .head .head)
      (.identifier (.tail (by decide) .head) (.tail (by decide) .head))
  obtain ⟨rfl, _⟩ := evaluation.deterministic expected
  exact ⟨required, enough⟩

private def reordered : Resolved.Environment :=
  [(localId_variant 1, .bool false), (localId_variant 0, .bool true), (localId_variant 2, .bool true)]

/-- Positional Boolean typing survives this reorder, but the compiled condition reads another ID. -/
theorem localConditional_identity_order_required (store : Core.Store) :
    Core.EnvironmentHasTypes (Resolved.LocalScope.values reordered) (Resolved.LocalScope.values (context_variant .bool)) ∧
    Resolved.LocalScope.ids reordered ≠ Resolved.LocalScope.ids (context_variant .bool) ∧
    LocalExpressionEvaluates names_variant reordered store source (.bool false) store ∧
    Core.runStateful 4 (Core.State.initial core (Resolved.LocalScope.values reordered) store) =
      .done (.bool true) store := by
  refine ⟨.cons .bool (.cons .bool (.cons .bool .nil)), by decide, ?_, rfl⟩
  exact .ifTrue (.identifier .head (.tail (by decide) .head))
    (.identifier (.tail (by decide) .head) .head)

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalExpressionEvaluator
/-! Original parsed expressions, independently specified values/Core/costs, and
actual first-match inputs. Raw selected success is not whole-source acceptance. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"DirectEvaluator", by decide⟩], by decide⟩⟩, 17⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def word_variant (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word_variant n)
private def literal (n : Nat) : Core.Expr := .word (word_variant n)
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def inputs (l r : Nat) (c d : Bool) : LocalInputs := ⟨[
  ⟨"c", ⟨owner, 2⟩, .bool, .bool c, .bool⟩, ⟨"d", ⟨other, 5⟩, .bool, .bool d, .bool⟩,
  ⟨"r", ⟨other, 999⟩, .word, w r, .word⟩, ⟨"l", ⟨owner, 7⟩, .word, w l, .word⟩], by
    change ([⟨owner, 2⟩, ⟨other, 5⟩, ⟨other, 999⟩, ⟨owner, 7⟩] : List Resolved.LocalId).Nodup
    decide⟩
private def parsed? (content : String) : IO (Option Syntax.Expr) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "direct-evaluator.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"lexer invariant: {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span.source = file.id ∧ source.span.startByte < source.span.endByte ∧
        source.span.endByte ≤ content.utf8ByteSize)) "parsed source range changed"
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")
private def parsed (content : String) : IO Syntax.Expr := do
  let some source ← parsed? content | throw (IO.userError s!"incomplete expression: {content}")
  return source

private def raw (table : LocalNameTable) (environment : Resolved.Environment)
    (source : Syntax.Expr) (expected : Option (Core.Value × Nat)) : IO Unit := do
  assertTrue (decide (evaluateLocalExpressionWithCost? table environment source = expected))
    s!"independent raw value/cost disagreed: {reprStr source.value}"
  for store in stores do
    match evaluated : evaluateLocalExpressionWithCost? table environment source with
    | none => have _ := (evaluateLocalExpressionWithCost?_eq_none_iff store).mp evaluated; pure ()
    | some (_, cost) =>
        let evidence := evaluateLocalExpressionWithCost?_sound evaluated store
        have _ := evaluateLocalExpressionWithCost?_complete evidence
        have _ := (evaluateLocalExpressionWithCost?_iff store).mpr evidence
        have _ := localExpressionEvaluatesWithCost_iff_evaluate.mp evidence
        have _ := (evaluateLocalExpressionWithCost?_exists_cost_iff store).mp ⟨cost, evaluated⟩
        have _ := (evaluateLocalExpressionWithCost?_value_iff store).mpr evidence.erase
        pure ()

private def checked_variant (content : String) (actual : LocalInputs) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let source ← parsed content
  raw actual.names actual.environment source (some (value, cost))
  assertTrue (decide (actual.check? source = some (core, type) ∧
    Core.infer? actual.context.values core = some type)) s!"wrong independent Core/type: {content}"
  match accepted : actual.check? source, evaluated : evaluateLocalExpressionWithCost? actual.names actual.environment source with
  | some (checkedCore, checkedType), some (found, steps) =>
      let typing := LocalInputs.check?_iff_hasType.mp ⟨checkedCore, accepted⟩
      have _ := elaborateLocalExpression?_typed_evaluator_exists accepted actual.sameIds actual.environmentTyped
      for store in stores do
        have _ := actual.typed_evaluator_execution typing store
        for continuation in [[], [.letBody (.var 0) []], [.unaryApply .wordNot]] do
          have _ := evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation
            (store := store) evaluated accepted actual.sameIds continuation
          pure () -- An endpoint before the continuation runs is not a whole-run guarantee.
        for fuel in List.range (cost + 3) do
          have _ := evaluateLocalExpressionWithCost?_checked_runStateful_done_iff
            (fuel := fuel) (store := store) evaluated accepted actual.sameIds
          have _ := evaluateLocalExpressionWithCost?_checked_runStateful_outOfFuel_iff
            (fuel := fuel) (store := store) evaluated accepted actual.sameIds
          have _ := elaborateLocalExpression?_run_done_iff_evaluator (value := found)
            (fuel := fuel) (initialStore := store) (finalStore := store) accepted actual.sameIds
          have _ := LocalInputs.run?_done_iff_evaluator (inputs := actual) (source := source)
            (type := checkedType) (value := found) (fuel := fuel) (initialStore := store) (finalStore := store)
          have _ := LocalInputs.run?_outOfFuel_iff_evaluator (inputs := actual) (source := source)
            (type := checkedType) (fuel := fuel) (store := store)
          assertTrue (decide (actual.run? fuel source store =
            some (type, Core.runStateful fuel (Core.State.initial core actual.environment.values store))))
            "full actual-Core result changed"
          assertTrue (match actual.run? fuel source store with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "wrong independent threshold/value/own store"
        for spent in List.range cost do
          let some (_, .outOfFuel checkpoint) := actual.run? spent source store
            | throw (IO.userError "genuine checkpoint missing")
          assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store))
            "actual checkpoint did not finish at the independently specified remainder"
        match core with
        | .binary op (.var left) (.var right) =>
            let some l := actual.environment.values[left]? | throw (IO.userError "left fixture value missing")
            let some r := actual.environment.values[right]? | throw (IO.userError "right fixture value missing")
            assertTrue (decide (actual.run? 2 source store = some (type, .outOfFuel
              ⟨.ret l, [.binaryRight op (.var right) actual.environment.values], store⟩) ∧
              actual.run? 4 source store = some (type, .outOfFuel ⟨.ret r, [.binaryApply op l], store⟩)))
              "strict original left/right checkpoints changed"
        | _ => pure ()
      assertTrue (steps == cost) "proof-derived cost replaced the independent expected cost"
  | _, _ => throw (IO.userError "positive raw or whole evidence disappeared")

private def contrast (content : String) (actual : LocalInputs) (expected : Option (Core.Value × Nat)) : IO Unit := do
  let source ← parsed content
  raw actual.names actual.environment source expected
  assertTrue (actual.check? source).isNone s!"raw success bypassed whole checking: {content}"
  for store in stores do
    for fuel in [0, 1, 30] do
      assertTrue (actual.run? fuel source store).isNone "whole rejection exposed execution"

private def checkOpaque (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : IO Unit := do
  for c in [false, true] do
    let actual := (LocalInputs.empty.bindFresh owner "x" type value typed).bindFresh other "c" .bool (.bool c) .bool
    checked_variant "x" actual (.var 1) type value 1
    checked_variant "c ? x : x" actual (.ifE (.var 0) (.var 1) (.var 1)) type value 4
    contrast "c && x" actual (some (if c then value else .bool false, 4))
    contrast "c || x" actual (some (if c then .bool true else value, 4))
    for store in stores do
      let continuation : List Core.Frame := [.unaryApply .wordNot]
      assertTrue (match Core.runStateful 1 ⟨.eval (.var 1) actual.environment.values, continuation, store⟩ with
        | .fault _ checkpoint => decide (checkpoint = ⟨.ret value, continuation, store⟩)
        | _ => false) "retained Word continuation was incorrectly guaranteed to exhaust for opaque values"

private def operators (l r : Nat) : List (String × Syntax.BinaryOp × Core.Expr × Core.Ty × Core.Value × Nat) :=
  let a : Core.Expr := .var 3
  let b : Core.Expr := .var 2
  let lt : Core.Expr := .letE a (.letE (.var 3) (.binary .wordGt (.var 0) (.var 1)))
  [("+", .add, .binary .wordAdd a b, .word, w (l + r), 3),
   ("-", .subtract, .binary .wordSub a b, .word, w (l + Core.wordModulus - r), 3),
   ("*", .multiply, .binary .wordMul a b, .word, w (l * r), 3),
   ("/", .divide, .binary .wordDiv a b, .word, w (if r == 0 then 0 else l / r), 3),
   ("%", .modulo, .binary .wordMod a b, .word, w (if r == 0 then 0 else l % r), 3),
   ("&", .bitAnd, .binary .wordAnd a b, .word, w (l &&& r), 3),
   ("|", .bitOr, .binary .wordOr a b, .word, w (l ||| r), 3),
   ("^", .bitXor, .binary .wordXor a b, .word, w (l ^^^ r), 3),
   (">", .greater, .binary .wordGt a b, .bool, .bool (decide (l > r)), 3),
   ("<", .less, lt, .bool, .bool (decide (l < r)), 9),
   ("==", .equal, .binary .wordEq a b, .bool, .bool (l == r), 3),
   ("!=", .notEqual, .unary .boolNot (.binary .wordEq a b), .bool, .bool (l != r), 5),
   ("<=", .lessEqual, .unary .boolNot (.binary .wordGt a b), .bool, .bool (decide (l ≤ r)), 5),
   (">=", .greaterEqual, .unary .boolNot lt, .bool, .bool (decide (l ≥ r)), 11)]

def frontendParsedLocalExpressionEvaluatorTests : IO Unit := do
  let numbers := [0, 1, 3, 7, 2 ^ 255, Core.wordModulus - 1]
  for l in numbers do
    for r in numbers do
      for (symbol, op, core, type, value, overhead) in operators l r do
        let content := s!"l {symbol} r"
        let source ← parsed content
        assertTrue (match source.value with
          | .binary ⟨_, .identifier left⟩ ⟨span, actualOp⟩ ⟨_, .identifier right⟩ =>
              actualOp == op && left.value == "l" && right.value == "r" &&
                decide (left.span.endByte ≤ span.startByte ∧ span.endByte ≤ right.span.startByte)
          | _ => false) "original operand order/operator range changed"
        assertTrue (decide (evaluateLocalWordBinaryWithCost? op (word_variant l) (word_variant r) = some (value, overhead)))
          "strict operator helper changed result/overhead"
        checked_variant content (inputs l r true false) core type value (overhead + 2)
    checked_variant "~l" (inputs l 0 true false) (.unary .wordNot (.var 3)) .word (w (Core.wordModulus - 1 - l)) 3
  for c in [false, true] do
    for d in [false, true] do
      let actual := inputs 7 3 c d
      checked_variant "!c" actual (.unary .boolNot (.var 0)) .bool (.bool (!c)) 3
      checked_variant "c && !d" actual (.ifE (.var 0) (.unary .boolNot (.var 1)) (.bool false))
        .bool (.bool (c && !d)) (if c then 6 else 4)
      checked_variant "c || !d" actual (.ifE (.var 0) (.bool true) (.unary .boolNot (.var 1)))
        .bool (.bool (c || !d)) (if c then 4 else 6)
      checked_variant "(c ? (l - r) : r)" actual (.ifE (.var 0) (.binary .wordSub (.var 3) (.var 2)) (.var 2))
        .word (w (if c then 4 else 3)) (if c then 8 else 4)
      contrast "c && missing" actual (if c then none else some (.bool false, 4))
      contrast "c || missing" actual (if c then some (.bool true, 4) else none)
      contrast "c ? l : missing" actual (if c then some (w 7, 4) else none)
      contrast "c ? f(l) : r" actual (if c then none else some (w 3, 4))
    for depth in [0, 1, 3, 7] do
      let content := (List.range depth).foldl (fun inner _ => "c ? (" ++ inner ++ ") : r") "l - r"
      let core := (List.range depth).foldl (fun inner _ => Core.Expr.ifE (.var 0) inner (.var 2))
        (.binary .wordSub (.var 3) (.var 2))
      checked_variant content (inputs 7 3 c false) core .word (w (if c || depth == 0 then 4 else 3))
        (if c || depth == 0 then 5 + 3 * depth else 4)
  let actual := inputs 7 3 true false
  for (symbol, op) in [("/", Core.BinaryOp.wordDiv), ("%", .wordMod)] do
    checked_variant s!"~l {symbol} 0" actual (.binary op (.unary .wordNot (.var 3)) (literal 0)) .word (w 0) 7
    checked_variant s!"l {symbol} (r - r)" actual (.binary op (.var 3) (.binary .wordSub (.var 2) (.var 2))) .word (w 0) 9
    contrast s!"missing {symbol} 0" actual none
    contrast s!"0 {symbol} missing" actual none
    contrast s!"0 {symbol} c" actual none
    contrast s!"l {symbol} (c ? 0 : missing)" actual (some (w 0, 8))
  checked_variant "(l,r)" actual (.pair (.var 3) (.var 2)) (.product .word .word) (.pair (w 7) (w 3)) 5
  for content in ["!l", "~c", "l + c", "c - r", "l && missing", "missing", "f(l)", "l.x", "l[0]", "[l]", "\"7\""] do
    contrast content actual none
  for op in [Syntax.BinaryOp.logicalAnd, .logicalOr] do
    assertTrue (evaluateLocalWordBinaryWithCost? op (word_variant 1) (word_variant 0)).isNone "short circuit acquired strict Word meaning"
  for (content, n) in [("0", 0), (" /*a*/ ((0007)) /*b*/ ", 7), ("0xaBcD", 43981),
      (toString (Core.wordModulus - 1), Core.wordModulus - 1)] do
    checked_variant content LocalInputs.empty (literal n) .word (w n) 1
  for content in [toString Core.wordModulus, "0x1" ++ String.ofList (List.replicate 64 '0')] do
    contrast content LocalInputs.empty none
  checkOpaque (.cell .word) (.cellRef .word 999) .cellRef
  checkOpaque (.function .word .word) (.closure .word .word (.var 0) []) (.closure .nil (.var rfl))
  for value in [Core.Value.cellRef .word 999, .closure .word .bool (.var 999) [w 12],
      .constructed ⟨⟨81⟩, 4⟩ (.pair .unit (w 8)), .unit] do
    let table : LocalNameTable := [("x", ⟨owner, 7⟩), ("c", ⟨other, 999⟩)]
    for c in [false, true] do
      let environment : Resolved.Environment := [(⟨owner, 7⟩, value), (⟨other, 999⟩, .bool c)]
      for content in ["x", "((x))"] do raw table environment (← parsed content) (some (value, 1))
      raw table environment (← parsed "c ? x : x") (some (value, 4))
      raw table environment (← parsed "c && x") (some (if c then value else .bool false, 4))
      raw table environment (← parsed "c || x") (some (if c then .bool true else value, 4))
      let context : Resolved.Context := [(⟨owner, 7⟩, .cell .word), (⟨other, 999⟩, .bool)]
      assertTrue ((elaborateLocalExpression? table context (← parsed "c && x")).isNone &&
        (elaborateLocalExpression? table context (← parsed "c || x")).isNone) "raw forwarded value became a Bool typing rule"
  let id : Resolved.LocalId := ⟨owner, 7⟩
  let second : Resolved.LocalId := ⟨other, 999⟩
  let source ← parsed "x"
  let table : LocalNameTable := [("x", id), ("x", second)]
  raw table [(id, w 9), (id, w 2), (second, w 5)] source (some (w 9, 1))
  raw table [(id, w 2), (id, w 9), (second, w 5)] source (some (w 2, 1))
  raw table [(id, .bool true), (id, w 9)] (← parsed "x - x") none
  raw table [(second, w 5)] source none
  raw [("x", second), ("x", id)] [(id, w 9)] source none
  let unaligned : Resolved.Environment := [(second, w 2), (id, w 9)]
  raw table unaligned source (some (w 9, 1))
  assertTrue (decide (elaborateLocalExpression? table [(id, .word), (second, .word)] source = some (.var 0, .word) ∧
    unaligned.ids ≠ [id, second] ∧ Core.runStateful 1 (Core.State.initial (.var 0) unaligned.values []) = .done (w 2) []))
    "unaligned raw lookup was incorrectly replaced by positional Core execution"
  let span : Syntax.SourceSpan := ⟨⟨.main, "not-lexed.sol"⟩, 900, 2⟩
  let manual := fun payload => (⟨span, .literal ⟨⟨⟨.main, "other.sol"⟩, 33, 1⟩, payload⟩⟩ : Syntax.Expr)
  raw [] [] (manual (.decimal "0007")) (some (w 7, 1))
  for payload in [Syntax.CoreLiteralValue.decimal "", .decimal "-1", .decimal "1_0", .decimal "٤",
      .hexadecimal "0x", .hexadecimal "0X1", .hexadecimal "0xg", .string "7", .decimal (toString Core.wordModulus)] do
    raw [] [] (manual payload) none
  for content in ["", "l +", "c ? l", "c ? l :", "7 8", "0x", "0Xff", "1_000", "0x1g", "-1", "٤"] do
    assertTrue (← parsed? content).isNone s!"malformed complete source parsed: {content}"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedResumption
/-! Resume only genuine fuel-exhaustion states from fully parsed entries.
Every control, continuation, captured value, and store remains observable. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def parsed_variant? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "resumption.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner_variant : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedResume", by decide⟩], by decide⟩⟩, 21⟩
private def types : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool)]
private def word_variant2 (value : Nat) := Core.Word.ofNatModulo value
private def wordArg (value : Nat) : TypedRuntimeArgument := ⟨.word, .word (word_variant2 value), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def stores_variant : List Core.Store := [[], [.word (word_variant2 7), .bool false, .cellRef .word 40]]

private def accepted (content : String) (parameterTypes : List Core.Ty)
    (expectedCore : Core.Expr) (returnType : Core.Ty) :
    IO (Syntax.FunctionDecl × CompiledRuntimeFunction) := do
  let some declaration ← parsed_variant? content | throw (IO.userError s!"{content}: incomplete declaration")
  let some compiled := compileRuntimeFunction? types owner_variant declaration
    | throw (IO.userError s!"{content}: compilation failed")
  assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = returnType ∧
    compiled.inputs.context.values = parameterTypes.reverse)) "wrong exact static compilation"
  assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some returnType))
    "actual open Core failed typing"
  return (declaration, compiled)

private def runCase (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (initialStore : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) :=
  runRuntimeFunction? types owner_variant declaration arguments fuel initialStore

private def checkpoints (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) (value : Core.Value) (cost : Nat) : IO Unit := do
  assertTrue (cost > 0) "checkpoint fixture needs a positive known path cost"
  assertTrue (decide (arguments.map (·.type) = compiled.inputs.context.values.reverse))
    "checkpoint case did not pass the exact argument guard"
  for initialStore in stores_variant do
    let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore
    assertTrue (decide (runCase declaration arguments cost initialStore =
      some (compiled.returnType, .done value initialStore))) "wrong original completion threshold"
    assertTrue (decide (Core.runStateful 0 (Core.State.final value initialStore) =
      .done value initialStore)) "final recognition charged a transition"
    for spent in List.range cost do
      let some (type, .outOfFuel checkpoint) := runCase declaration arguments spent initialStore
        | throw (IO.userError "source did not yield the expected genuine checkpoint")
      assertTrue (decide (type = compiled.returnType ∧ checkpoint.store = initialStore ∧
        Core.runStateful spent initial = .outOfFuel checkpoint))
        "checkpoint lost its actual compiled origin, type, or store"
      assertTrue (decide (Core.runStateful 0 checkpoint = .outOfFuel checkpoint))
        "a genuine pre-terminal checkpoint became done without another transition"
      if spent = 0 then
        assertTrue (decide (checkpoint = initial)) "zero-spent checkpoint changed actual argument values"
      let residual := cost - spent
      for additional in List.range (residual + 3) do
        let resumed := Core.runStateful additional checkpoint
        assertTrue (decide (runCase declaration arguments (spent + additional) initialStore =
          some (compiled.returnType, resumed))) "resumption changed the full same-total-fuel result"
        assertTrue (decide (resumed = Core.runStateful (spent + additional) initial))
          "resumption differed from the actual compiled machine"
        assertTrue (match resumed with
          | .done result finalStore => decide (residual ≤ additional ∧ result = value ∧ finalStore = initialStore)
          | .outOfFuel suspended => decide (additional < residual ∧ suspended.store = initialStore)
          | _ => false) "resumption lost the exact residual threshold, value, or own store"
      for middle in List.range residual do
        let .outOfFuel second := Core.runStateful middle checkpoint
          | throw (IO.userError "second genuine checkpoint unexpectedly terminated")
        assertTrue (decide (runCase declaration arguments (spent + middle) initialStore =
          some (compiled.returnType, .outOfFuel second))) "second checkpoint lost its source provenance"
        for last in List.range (residual - middle + 3) do
          let resumed := Core.runStateful last second
          assertTrue (decide (resumed = Core.runStateful (middle + last) checkpoint ∧
            runCase declaration arguments (spent + middle + last) initialStore =
              some (compiled.returnType, resumed))) "three-chunk execution changed the full result"

private def pendingSubtraction (declaration : Syntax.FunctionDecl)
    (left right : Nat) : IO Unit := do
  let arguments := [wordArg left, wordArg right]
  for initialStore in stores_variant do
    let some (.word, .outOfFuel checkpoint) := runCase declaration arguments 4 initialStore
      | throw (IO.userError "subtraction did not yield its fuel-four checkpoint")
    let expected : Core.State :=
      ⟨.ret (.word (word_variant2 right)), [.binaryApply .wordSub (.word (word_variant2 left))], initialStore⟩
    assertTrue (decide (checkpoint = expected)) "noncommutative pending frame lost ordered argument values"
    assertTrue (decide (Core.runStateful 0 checkpoint = .outOfFuel expected ∧
      Core.runStateful 1 checkpoint = .done (.word ((word_variant2 left).sub (word_variant2 right))) initialStore))
      "pending binary application did not cost exactly one remaining transition"

private def rejectedArguments (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ compiled.inputs.context.values.reverse))
    "rejection case accidentally satisfied the exact argument guard"
  assertTrue (prepareRuntimeFunction? types owner_variant declaration arguments).isNone
    "mismatched actual arguments prepared"
  for initialStore in stores_variant do
    for fuel in List.range 20 do
      assertTrue (runCase declaration arguments fuel initialStore).isNone
        "an argument-guard failure exposed a resumable checkpoint"

def frontendParsedResumptionTests : IO Unit := do
  let (bare, bareCompiled) ← accepted "function bare() { return; }" [] .unit .unit
  checkpoints bare bareCompiled [] .unit 1
  rejectedArguments bare bareCompiled [boolArg false]
  let (subtraction, subtractionCompiled) ← accepted
    "function subtraction(x: Word, y: Word) returns (Word) { return ((x)) - y; }"
    [.word, .word] (.binary .wordSub (.var 1) (.var 0)) .word
  for (left, right) in [(7, 9), (9, 7), (0, 1), (1, 0), (2 ^ 256 - 1, 7)] do
    checkpoints subtraction subtractionCompiled [wordArg left, wordArg right]
      (.word ((word_variant2 left).sub (word_variant2 right))) 5
    pendingSubtraction subtraction left right
  for initialStore in stores_variant do
    let some (_, .outOfFuel genuine) := runCase subtraction [wordArg 9, wordArg 7] 4 initialStore
      | throw (IO.userError "continuation counterexample has no genuine checkpoint")
    let dropped : Core.State := ⟨genuine.control, [], genuine.store⟩
    assertTrue (decide (Core.runStateful 0 genuine = .outOfFuel genuine ∧
      Core.runStateful 0 dropped = .done (.word (word_variant2 7)) initialStore ∧
      Core.runStateful 1 genuine = .done (.word (word_variant2 2)) initialStore ∧
      Core.runStateful 1 dropped ≠ Core.runStateful 1 genuine))
      "dropping the pending frame failed to change both cost and result"
  let (negation, negationCompiled) ← accepted
    "function negation(c: Bool) returns (Bool) { return !c; }"
    [.bool] (.unary .boolNot (.var 0)) .bool
  for choice in [false, true] do
    checkpoints negation negationCompiled [boolArg choice] (.bool (!choice)) 3
    for initialStore in stores_variant do
      let pending : Core.State := ⟨.ret (.bool choice), [.unaryApply .boolNot], initialStore⟩
      assertTrue (decide (runCase negation [boolArg choice] 2 initialStore =
        some (.bool, .outOfFuel pending))) "pending unary frame or actual Bool changed"
  for (symbol, expectedCore) in [("&&", Core.Expr.ifE (.var 0)
      (.unary .boolNot (.var 0)) (.bool false)),
      ("||", Core.Expr.ifE (.var 0) (.bool true) (.unary .boolNot (.var 0)))] do
    let (declaration, compiled) ← accepted
      ("function short(c: Bool) returns (Bool) { return c " ++ symbol ++ " !c; }")
      [.bool] expectedCore .bool
    for choice in [false, true] do
      let isAnd := symbol == "&&"
      checkpoints declaration compiled [boolArg choice] (.bool (!isAnd))
        (if choice == isAnd then 6 else 4)
  let (branch, branchCompiled) ← accepted
    "function branch(c: Bool, x: Word, y: Word) returns (Word) { return c ? x * y : x; }"
    [.bool, .word, .word] (.ifE (.var 2) (.binary .wordMul (.var 1) (.var 0)) (.var 1)) .word
  for choice in [false, true] do
    checkpoints branch branchCompiled [boolArg choice, wordArg 7, wordArg 9]
      (.word (word_variant2 (if choice then 63 else 7))) (if choice then 8 else 4)
  for arguments in [[], [boolArg false, wordArg 7], [wordArg 7, boolArg true, wordArg 9],
      [boolArg true, wordArg 7, boolArg false], [boolArg true, wordArg 7, wordArg 9, wordArg 1]] do
    rejectedArguments branch branchCompiled arguments
  let (arithmetic, arithmeticCompiled) ← accepted
    "function arithmetic(x: Word, y: Word) returns (Word) { return x * y > y ? x - y : x; }"
    [.word, .word] (.ifE (.binary .wordGt (.binary .wordMul (.var 1) (.var 0)) (.var 0))
      (.binary .wordSub (.var 1) (.var 0)) (.var 1)) .word
  for (left, right) in [(0, 9), (7, 9), (2 ^ 256 - 1, 1)] do
    let selected := decide ((word_variant2 left).mul (word_variant2 right) > word_variant2 right)
    checkpoints arithmetic arithmeticCompiled [wordArg left, wordArg right]
      (.word (if selected then (word_variant2 left).sub (word_variant2 right) else word_variant2 left)) (if selected then 16 else 12)
  let identity : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  for (name, argument) in [("Fn", identity), ("Cell", cell)] do
    let (declaration, compiled) ← accepted
      (s!"function identity(x: {name}) returns ({name})" ++ " { return x; }")
      [argument.type] (.var 0) argument.type
    checkpoints declaration compiled [argument] argument.value 1
  for content in ["function empty() {}", "function multiple() { return; return; }",
      "function missing() returns (Word) { return missing; }",
      "function skipped(c: Bool) returns (Bool) { return c && missing; }",
      "function skipped(c: Bool, x: Word) returns (Bool) { return c || x / x; }",
      "function skipped(c: Bool, x: Word) returns (Word) { return c ? x : x(c); }",
      "function wrong(c: Bool, x: Word) returns (Word) { return c ? x : c; }"] do
    let some declaration ← parsed_variant? content | throw (IO.userError "whole-rejection fixture failed parsing")
    assertTrue (compileRuntimeFunction? types owner_variant declaration).isNone "invalid whole declaration compiled"
    for arguments in [[], [boolArg false], [boolArg true], [wordArg 7],
        [boolArg false, wordArg 7], [boolArg true, wordArg 7], [boolArg false, boolArg true]] do
      assertTrue (prepareRuntimeFunction? types owner_variant declaration arguments).isNone
        "an invalid whole declaration prepared"
      for initialStore in stores_variant do
        for fuel in List.range 20 do
          assertTrue (runCase declaration arguments fuel initialStore).isNone
            "whole rejection exposed a resumable checkpoint"
  for content in ["", "function incomplete()", "function f() { return;",
      "function f() { return; } trailing", "function f() { return; } /*"] do
    assertTrue (← parsed_variant? content).isNone "incomplete input entered source checkpoint tests"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedStoreIndependence
/-! Fully parsed restricted entries retain values and exact fuel boundaries
across unrelated stores. Every concrete result still carries its own store;
supplied references and closures are returned, never dereferenced or called. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def parsed_variant2? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "store-independence.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner_variant2 : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"StoreIndependent", by decide⟩], by decide⟩⟩, 18⟩
private def types_variant : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def cellArg (address : Nat) : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word address, .cellRef⟩
private def identityClosure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
private def constantClosure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.bool false) [], .closure .nil .bool⟩
private def stores_variant2 : List Core.Store :=
  [[], [.word (word_variant2 7), .bool false], [.bool true, .word (word_variant2 99), .cellRef .word 40]]

private def accepted_variant (content : String) (parameterTypes : List Core.Ty)
    (expectedCore : Core.Expr) (returnType : Core.Ty) : IO (Syntax.FunctionDecl × CompiledRuntimeFunction) := do
  let some declaration ← parsed_variant2? content | throw (IO.userError s!"{content}: incomplete declaration")
  let some compiled := compileRuntimeFunction? types_variant owner_variant2 declaration
    | throw (IO.userError s!"{content}: compilation failed")
  assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = returnType ∧
    compiled.inputs.context.values = parameterTypes.reverse)) "wrong exact static compilation"
  assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some returnType))
    "actual open Core failed typing"
  return (declaration, compiled)

private def runCase_variant (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (initialStore : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) :=
  runRuntimeFunction? types_variant owner_variant2 declaration arguments fuel initialStore

/-- Only the type, terminal value, and exhaustion kind are compared between
stores. Neither suspended states nor complete stateful results are identified. -/
private def sameObservation (left right : Option (Core.Ty × Core.StatefulRunResult)) : Bool :=
  match left, right with
  | some (leftType, .done leftValue _), some (rightType, .done rightValue _) =>
      decide (leftType = rightType ∧ leftValue = rightValue)
  | some (leftType, .outOfFuel _), some (rightType, .outOfFuel _) => decide (leftType = rightType)
  | none, none => true
  | _, _ => false

private def completed (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) (value : Core.Value) (cost : Nat) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) = compiled.inputs.context.values.reverse))
    "completion case did not pass the exact argument guard"
  for fuel in List.range (cost + 3) do
    let reference := runCase_variant declaration arguments fuel []
    for initialStore in stores_variant2 do
      let observed := runCase_variant declaration arguments fuel initialStore
      let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore
      assertTrue (decide (observed = some (compiled.returnType, Core.runStateful fuel initial)))
        s!"runtime entry changed its actual compiled execution at fuel {fuel}"
      assertTrue (sameObservation reference observed) s!"store changed the observation at fuel {fuel}"
      assertTrue (match observed with
        | some (type, .done result finalStore) =>
            decide (cost ≤ fuel ∧ type = compiled.returnType ∧ result = value ∧ finalStore = initialStore)
        | some (type, .outOfFuel suspended) =>
            decide (fuel < cost ∧ type = compiled.returnType ∧ suspended.store = initialStore)
        | _ => false) s!"wrong value, per-store preservation, or exact cost at fuel {fuel}"
      if fuel = 0 then
        assertTrue (decide (observed = some (compiled.returnType, .outOfFuel initial)))
          "zero fuel lost the actual store or arguments"

private def rejectedArguments_variant (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ compiled.inputs.context.values.reverse))
    "rejection case accidentally satisfied the exact argument guard"
  for initialStore in stores_variant2 do
    assertTrue (prepareRuntimeFunction? types_variant owner_variant2 declaration arguments).isNone
      "mismatched arguments prepared independently of the store"
    for fuel in List.range 20 do
      assertTrue (runCase_variant declaration arguments fuel initialStore).isNone
        "a replacement store bypassed the argument guard"

def frontendParsedStoreIndependenceTests : IO Unit := do
  assertTrue (decide (stores_variant2.length = 3 ∧ stores_variant2[0]! ≠ stores_variant2[1]! ∧
    stores_variant2[0]! ≠ stores_variant2[2]! ∧ stores_variant2[1]! ≠ stores_variant2[2]!)) "store fixtures must be distinct"
  let (bare, bareCompiled) ← accepted_variant "function bare() { return; }" [] .unit .unit
  completed bare bareCompiled [] .unit 1
  rejectedArguments_variant bare bareCompiled [boolArg false]
  let (arithmetic, arithmeticCompiled) ← accepted_variant
    "function arithmetic(x: Word, y: Word) returns (Word) { return x * y > y ? x - y : x; }"
    [.word, .word] (.ifE (.binary .wordGt (.binary .wordMul (.var 1) (.var 0)) (.var 0))
      (.binary .wordSub (.var 1) (.var 0)) (.var 1)) .word
  for left in [0, 1, 7, 2 ^ 256 - 1] do
    for right in [0, 1, 9] do
      let selected := decide ((word_variant2 left).mul (word_variant2 right) > word_variant2 right)
      completed arithmetic arithmeticCompiled [wordArg left, wordArg right]
        (.word (if selected then (word_variant2 left).sub (word_variant2 right) else word_variant2 left)) (if selected then 16 else 12)
  let (branch, branchCompiled) ← accepted_variant
    "function branch(c: Bool, x: Word, y: Word) returns (Word) { return c ? x * y : x; }"
    [.bool, .word, .word] (.ifE (.var 2) (.binary .wordMul (.var 1) (.var 0)) (.var 1)) .word
  for choice in [false, true] do
    completed branch branchCompiled [boolArg choice, wordArg 7, wordArg 9]
      (.word (word_variant2 (if choice then 63 else 7))) (if choice then 8 else 4)
  for arguments in [[], [boolArg false, wordArg 7], [wordArg 7, boolArg true, wordArg 9],
      [boolArg true, wordArg 7, boolArg false], [boolArg true, wordArg 7, wordArg 9, wordArg 1]] do
    rejectedArguments_variant branch branchCompiled arguments
  let (short, shortCompiled) ← accepted_variant
    "function short(c: Bool) returns (Bool) { return c && !c; }"
    [.bool] (.ifE (.var 0) (.unary .boolNot (.var 0)) (.bool false)) .bool
  for choice in [false, true] do
    completed short shortCompiled [boolArg choice] (.bool false) (if choice then 6 else 4)
  for (typeName, type, supplied) in
      [("Cell", Core.Ty.cell .word, [cellArg 0, cellArg 40, cellArg 91]),
       ("Fn", Core.Ty.function .bool .bool, [identityClosure, constantClosure])] do
    let (declaration, compiled) ← accepted_variant
      (s!"function identity(x: {typeName}) returns ({typeName})" ++ " { return ((x)); }")
      [type] (.var 0) type
    for argument in supplied do
      completed declaration compiled [argument] argument.value 1
    rejectedArguments_variant declaration compiled []
    rejectedArguments_variant declaration compiled [wordArg 7]
  let (nominal, nominalCompiled) ← accepted_variant
    "function nominal(x: Opaque) returns (Opaque) { return x; }"
    [.namedData ⟨91⟩] (.var 0) (.namedData ⟨91⟩)
  for arguments in [[], [boolArg false], [wordArg 0], [cellArg 0], [identityClosure]] do
    rejectedArguments_variant nominal nominalCompiled arguments
  for content in ["function invalid(c: Bool) returns (Bool) { return c || missing; }",
      "function invalid(c: Bool) returns (Bool) { return c && missing; }",
      "function invalid(c: Bool, x: Word) returns (Word) { return c ? x : missing; }",
      "function invalid(c: Bool, x: Word) returns (Word) { return c ? x : c; }",
      "function invalid(x: Word) returns (Word) { return x > 0; }",
      "function duplicate(x: Bool, x: Bool) { return; }", "function empty() {}"] do
    let some declaration ← parsed_variant2? content | throw (IO.userError "whole-rejection fixture failed parsing")
    assertTrue (compileRuntimeFunction? types_variant owner_variant2 declaration).isNone "invalid whole declaration compiled"
    for arguments in [[], [boolArg false], [boolArg true], [wordArg 7],
        [boolArg false, wordArg 7], [boolArg true, wordArg 7], [boolArg false, boolArg true]] do
      assertTrue (prepareRuntimeFunction? types_variant owner_variant2 declaration arguments).isNone
        "a skipped invalid branch bypassed whole preparation"
      for initialStore in stores_variant2 do
        for fuel in [0, 1, 4, 6, 20] do
          assertTrue (runCase_variant declaration arguments fuel initialStore).isNone
            "a replacement store bypassed whole declaration rejection"
  for content in ["", "function incomplete()", "function f() { return;",
      "function f() { return; } trailing", "function f() { return; } /*"] do
    assertTrue (← parsed_variant2? content).isNone "incomplete input entered store observation tests"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendResumptionProperties
/-! Independent source costs and actual machine frames witness exact suffix
execution. Resuming is not reinitializing or discarding a pending continuation. -/

set_option autoImplicit false

namespace Tests.FrontendResumption

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"Resumption", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "resumption.sol"⟩, 17, 2⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def body (source : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some source)⟩]⟩
private def subtraction : Syntax.Expr := ⟨span, .binary (ref "l") ⟨span, .subtract⟩ (ref "r")⟩
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := .binary .wordSub (.var 1) (.var 0)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem checked (left right : Core.Word) :
    (inputs left right).check? subtraction = some (core, .word) :=
  elaborateLocalExpression?_complete
    (.subtract (.identifier (.tail names_ne .head)) (.identifier .head))
    (.binary (.var (.tail ids_ne .head)) (.var .head))
    (.binary (.var (.tail ids_ne .head)) (.var .head))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store subtraction (.word (left.sub right)) store 5 :=
  .subtract (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private def beforeRight (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.binaryRight .wordSub (.var 0) [.word right, .word left]], store⟩
private def pending (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word right), [.binaryApply .wordSub (.word left)], store⟩

theorem genuine_binary_checkpoint_retains_exactly_one_transition
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    Core.runStateful 4 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (pending left right store) ∧
    Core.Steps 1 (pending left right store) (Core.State.final (.word (left.sub right)) store) ∧
    (Core.runStateful additional (pending left right store) = .done (.word (left.sub right)) store ↔
      1 ≤ additional) ∧
    ((∃ checkpoint, Core.runStateful additional (pending left right store) = .outOfFuel checkpoint) ↔
      additional < 1) := by
  have exhausted : Core.runStateful 4 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (pending left right store) := rfl
  have path := (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds
  exact ⟨exhausted, (path.residual_of_outOfFuel exhausted).2,
    path.resumed_done_iff exhausted, path.resumed_outOfFuel_iff exhausted⟩

theorem checked_local_and_singleton_return_resume_the_actual_pending_frame
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    4 < 5 ∧ Core.Steps 1 (pending left right store) (Core.State.final (.word (left.sub right)) store) ∧
    (inputs left right).run? (4 + additional) subtraction store =
      some (.word, Core.runStateful additional (pending left right store)) ∧
    (inputs left right).runReturnBody? (4 + additional) (body subtraction) store =
      some (.word, Core.runStateful additional (pending left right store)) ∧
    (Core.runStateful additional (pending left right store) = .done (.word (left.sub right)) store ↔
      1 ≤ additional) := by
  have exhausted := (genuine_binary_checkpoint_retains_exactly_one_transition left right store additional).1
  have checkedResidual := (costed left right store).checked_residual_of_outOfFuel
    (checked left right) (inputs left right).sameIds exhausted
  have rawResidual := (costed left right store).residual_of_outOfFuel
    (.subtract (.identifier (.tail names_ne .head)) (.identifier .head))
    (.binary (.var (.tail ids_ne .head)) (.var .head)) exhausted
  have bodyCost : ReturnBodyEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (body subtraction) (.word (left.sub right)) store 5 := .expression (costed left right store)
  have bodyChecked : (inputs left right).checkReturnBody? (body subtraction) = some (core, .word) :=
    checked left right
  have bodyResidual := bodyCost.checked_residual_of_outOfFuel bodyChecked (inputs left right).sameIds exhausted
  have localExhausted : (inputs left right).run? 4 subtraction store =
      some (.word, .outOfFuel (pending left right store)) := by
    rw [LocalInputs.run?, checked]; rfl
  have bodyExhausted : (inputs left right).runReturnBody? 4 (body subtraction) store =
      some (.word, .outOfFuel (pending left right store)) := by
    rw [LocalInputs.runReturnBody?, bodyChecked]; rfl
  exact ⟨checkedResidual.1, rawResidual.2, LocalInputs.run?_resume localExhausted additional,
    LocalInputs.runReturnBody?_resume bodyExhausted additional, bodyResidual.2.runStateful_done_iff⟩

theorem two_chunk_continuation_equals_one_larger_run_including_suspended_states
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    Core.runStateful 2 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (beforeRight left right store) ∧
    Core.runStateful 2 (beforeRight left right store) = .outOfFuel (pending left right store) ∧
    Core.runStateful additional (pending left right store) =
      Core.runStateful (2 + additional) (beforeRight left right store) ∧
    Core.runStateful additional (pending left right store) =
      Core.runStateful (4 + additional) (Core.State.initial core [.word right, .word left] store) := by
  have first : Core.runStateful 2 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (beforeRight left right store) := rfl
  have second : Core.runStateful 2 (beforeRight left right store) = .outOfFuel (pending left right store) := rfl
  refine ⟨first, second, Core.runStateful_resume second additional, ?_⟩
  simpa only [← Nat.add_assoc] using (Core.runStateful_resume second additional).trans
    (Core.runStateful_resume first (2 + additional))

theorem dropping_the_binary_frame_changes_zero_fuel_recognition_and_the_value
    (left right : Core.Word) (different : left.sub right ≠ right) (store : Core.Store) :
    Core.runStateful 0 (pending left right store) = .outOfFuel (pending left right store) ∧
    Core.runStateful 0 ⟨.ret (.word right), [], store⟩ = .done (.word right) store ∧
    Core.runStateful 1 (pending left right store) = .done (.word (left.sub right)) store ∧
    Core.runStateful 0 ⟨.ret (.word right), [], store⟩ ≠ Core.runStateful 1 (pending left right store) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro same
  exact different (Core.Value.word.inj (Core.StatefulRunResult.done.inj same).1).symm

private def booleanInputs (choice : Bool) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool
private def booleanSource : Syntax.Expr :=
  ⟨span, .binary (ref "c") ⟨span, .logicalAnd⟩ ⟨span, .unary ⟨span, .logicalNot⟩ (ref "c")⟩⟩
private def booleanCore : Core.Expr := .ifE (.var 0) (.unary .boolNot (.var 0)) (.bool false)
private theorem booleanChecked (choice : Bool) :
    (booleanInputs choice).check? booleanSource = some (booleanCore, .bool) :=
  elaborateLocalExpression?_complete (.logicalAnd (.identifier .head) (.logicalNot (.identifier .head)))
    (.ifE (.var .head) (.unary (.var .head)) .bool)
    (.ifE (.var .head) (.unary (.var .head)) .bool)
private theorem booleanCost (choice : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (booleanInputs choice).names (booleanInputs choice).environment
      store booleanSource (.bool false) store (if choice then 6 else 4) := by
  cases choice
  · exact .andFalse (.identifier .head .head)
  · have leaf : LocalExpressionEvaluatesWithCost (booleanInputs true).names (booleanInputs true).environment
        store (ref "c") (.bool true) store 1 := .identifier .head .head
    exact .andTrue leaf (.logicalNot leaf)
private def booleanCheckpoint (choice : Bool) (store : Core.Store) : Core.State :=
  if choice then ⟨.ret (.bool true), [.unaryApply .boolNot], store⟩
  else ⟨.eval (.bool false) [.bool false], [], store⟩

theorem short_circuit_paths_retain_different_checkpoints_with_the_same_remaining_cost
    (choice : Bool) (store : Core.Store) (additional : Nat) :
    LocalExpressionEvaluatesWithCost (booleanInputs choice).names (booleanInputs choice).environment
      store booleanSource (.bool false) store (if choice then 6 else 4) ∧
    Core.runStateful (if choice then 5 else 3) (Core.State.initial booleanCore [.bool choice] store) =
      .outOfFuel (booleanCheckpoint choice store) ∧
    Core.Steps 1 (booleanCheckpoint choice store) (Core.State.final (.bool false) store) ∧
    (Core.runStateful additional (booleanCheckpoint choice store) = .done (.bool false) store ↔
      1 ≤ additional) := by
  have exhausted : Core.runStateful (if choice then 5 else 3)
      (Core.State.initial booleanCore [.bool choice] store) = .outOfFuel (booleanCheckpoint choice store) := by
    cases choice <;> rfl
  have path := (booleanCost choice store).checked_toSteps (booleanChecked choice) (booleanInputs choice).sameIds
  have residual := (path.residual_of_outOfFuel exhausted).2
  have remaining : (if choice then 6 else 4) - (if choice then 5 else 3) = 1 := by cases choice <;> rfl
  rw [remaining] at residual
  exact ⟨booleanCost choice store, exhausted, residual, residual.runStateful_done_iff⟩

private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "T"⟩, []⟩⟩⟩ none⟩
private def parameter : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, "x"⟩ annotation⟩
private def declaration : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "identity"⟩, none, ⟨span, [parameter]⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation]⟩⟩, none⟩, body (ref "x")⟩⟩
private def types (type : Core.Ty) : TypeNameTable := [(["T"], type)]
private def argument (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    TypedRuntimeArgument := ⟨type, value, typed⟩
private def compiled (type : Core.Ty) : CompiledRuntimeFunction :=
  ⟨LocalTypeInputs.empty.bindFresh owner "x" type, .var 0, type⟩
private def prepared (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    PreparedRuntimeFunction := ⟨LocalInputs.empty.bindFresh owner "x" type value typed, .var 0, type⟩
private theorem compilation (type : Core.Ty) : RuntimeFunctionCompiles (types type) owner declaration (compiled type) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩
private theorem preparation (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    RuntimeFunctionPrepares (types type) owner declaration [argument type value typed] (prepared type value typed) :=
  ⟨(compilation type).header,
    .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil, (compilation type).body⟩

theorem independent_entry_and_compilation_resume_the_actual_argument_from_zero_spent
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (store : Core.Store) (additional : Nat) :
    RuntimeFunctionEvaluatesWithCost (types type) owner declaration [argument type value typed]
      store type value store 1 ∧
    runRuntimeFunction? (types type) owner declaration [argument type value typed] 0 store =
      some (type, .outOfFuel (Core.State.initial (.var 0) [value] store)) ∧
    Core.Steps 1 (Core.State.initial (.var 0) [value] store) (Core.State.final value store) ∧
    (Core.runStateful additional (Core.State.initial (.var 0) [value] store) = .done value store ↔
      1 ≤ additional) ∧
    runRuntimeFunction? (types type) owner declaration [argument type value typed] additional store =
      some (type, Core.runStateful additional (Core.State.initial (.var 0) [value] store)) := by
  have evaluated : RuntimeFunctionEvaluatesWithCost (types type) owner declaration [argument type value typed]
      store type value store 1 := .intro (preparation type value typed) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.identifier .head .head))
  have exhausted : runRuntimeFunction? (types type) owner declaration [argument type value typed] 0 store =
      some (type, .outOfFuel (Core.State.initial (.var 0) [value] store)) := by
    rw [runRuntimeFunction?, (preparation type value typed).complete]; rfl
  have sourceResidual := evaluated.residual_of_outOfFuel exhausted
  have compiledResidual := evaluated.compiled_residual_of_outOfFuel (compilation type)
    (show Core.runStateful 0 (Core.State.initial (.var 0) [value] store) =
      .outOfFuel (Core.State.initial (.var 0) [value] store) from rfl)
  refine ⟨evaluated, exhausted, sourceResidual.2, compiledResidual.2.runStateful_done_iff, ?_⟩
  simpa only [Nat.zero_add] using runRuntimeFunction?_resume exhausted additional

private def illTypedCore : Core.Expr := .binary .wordSub (.bool true) (.word .zero)
private def beforeFault (store : Core.Store) : Core.State :=
  ⟨.eval (.word .zero) [], [.binaryApply .wordSub (.bool true)], store⟩
private def faultState (store : Core.Store) : Core.State :=
  ⟨.ret (.word .zero), [.binaryApply .wordSub (.bool true)], store⟩

theorem generic_core_resumption_also_preserves_faults_without_frontend_acceptance
    (store : Core.Store) (additional : Nat) :
    Core.runStateful 3 (Core.State.initial illTypedCore [] store) = .outOfFuel (beforeFault store) ∧
    Core.runStateful 1 (beforeFault store) =
      .fault (.invalidBinaryOperands .wordSub (.bool true) (.word .zero)) (faultState store) ∧
    Core.runStateful additional (beforeFault store) =
      Core.runStateful (3 + additional) (Core.State.initial illTypedCore [] store) :=
  ⟨rfl, rfl, Core.runStateful_resume rfl additional⟩

end Tests.FrontendResumption
end

section
-- leanmerge: from Solcore.Test.FrontendStoreIndependenceProperties
/-! Independent source derivations replay on arbitrary stores. Whole contracts,
actual values, per-store results, and effectful Core remain separate boundaries. -/

set_option autoImplicit false

namespace Tests.FrontendStoreIndependence

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"StoreIndependence", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "store-independence.sol"⟩, 9, 2⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def names : LocalNameTable := [("x", ⟨owner, 0⟩)]
private def environment (value : Core.Value) : Resolved.Environment := [(⟨owner, 0⟩, value)]
private def body (source : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some source)⟩]⟩

theorem arbitrary_values_replay_without_typing_or_allocation
    (value : Core.Value) (first replacement : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment value) replacement (ref "x") value replacement 1 ∧
    LocalExpressionEvaluates names (environment value) replacement (ref "x") value replacement ∧
    (LocalExpressionEvaluatesWithCost names (environment value) first (ref "x") value first 1 ↔
      first = first ∧ LocalExpressionEvaluatesWithCost names (environment value)
        replacement (ref "x") value replacement 1) ∧
    (LocalExpressionEvaluates names (environment value) first (ref "x") value first ↔
      first = first ∧ LocalExpressionEvaluates names (environment value)
        replacement (ref "x") value replacement) := by
  have evaluated : LocalExpressionEvaluatesWithCost names (environment value) first (ref "x") value first 1 :=
    .identifier .head .head
  exact ⟨evaluated.change_store replacement, evaluated.erase.change_store replacement,
    localExpressionEvaluatesWithCost_store_iff, localExpressionEvaluates_store_iff⟩

private def skipped : Syntax.Expr := ⟨span, .binary (ref "x") ⟨span, .logicalAnd⟩ (ref "missing")⟩

theorem skipped_invalid_branch_replays_but_still_fails_whole_resolution
    (first replacement : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment (.bool false))
      replacement skipped (.bool false) replacement 4 ∧
    ReturnBodyEvaluates names (environment (.bool false)) replacement (body skipped) (.bool false) replacement ∧
    ReturnBodyEvaluatesWithCost names (environment (.bool false))
      replacement (body skipped) (.bool false) replacement 4 ∧
    resolveLocalExpression? names skipped = none := by
  have evaluated : LocalExpressionEvaluatesWithCost names (environment (.bool false))
      first skipped (.bool false) first 4 := .andFalse (.identifier .head .head)
  have rawBody : ReturnBodyEvaluates names (environment (.bool false)) first (body skipped) (.bool false) first :=
    .expression evaluated.erase
  have costBody : ReturnBodyEvaluatesWithCost names (environment (.bool false))
      first (body skipped) (.bool false) first 4 := .expression evaluated
  refine ⟨evaluated.change_store replacement, rawBody.change_store replacement,
    costBody.change_store replacement, ?_⟩
  simp [skipped, ref, resolveLocalExpression?, names, LocalNameTable.lookup?]

theorem bare_return_replays_with_one_transition (first replacement : Core.Store) :
    ReturnBodyEvaluates names (environment .unit) replacement ⟨span, [⟨span, .returnStmt none⟩]⟩ .unit replacement ∧
    ReturnBodyEvaluatesWithCost names (environment .unit) replacement
      ⟨span, [⟨span, .returnStmt none⟩]⟩ .unit replacement 1 := by
  have raw : ReturnBodyEvaluates names (environment .unit) first
      ⟨span, [⟨span, .returnStmt none⟩]⟩ .unit first := .bare
  have costed : ReturnBodyEvaluatesWithCost names (environment .unit) first
      ⟨span, [⟨span, .returnStmt none⟩]⟩ .unit first 1 := .bare
  exact ⟨raw.change_store replacement, costed.change_store replacement⟩

private def branchNames : LocalNameTable := [("c", ⟨owner, 0⟩), ("x", ⟨owner, 1⟩)]
private def branchEnvironment (choice : Bool) (value : Core.Word) : Resolved.Environment :=
  [(⟨owner, 0⟩, .bool choice), (⟨owner, 1⟩, .word value)]
private def product : Syntax.Expr := ⟨span, .binary (ref "x") ⟨span, .multiply⟩ (ref "x")⟩
private def branch : Syntax.Expr := ⟨span, .conditional (ref "c") span product span (ref "x")⟩
private theorem branchCost (choice : Bool) (value : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost branchNames (branchEnvironment choice value) store branch
      (.word (if choice then value.mul value else value)) store (if choice then 8 else 4) := by
  have leaf : LocalExpressionEvaluatesWithCost branchNames (branchEnvironment choice value)
      store (ref "x") (.word value) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have condition : LocalExpressionEvaluatesWithCost branchNames (branchEnvironment choice value)
      store (ref "c") (.bool choice) store 1 := .identifier .head .head
  cases choice
  · exact .ifFalse condition leaf
  · have multiplied : LocalExpressionEvaluatesWithCost branchNames (branchEnvironment true value)
        store product (.word (value.mul value)) store 5 :=
      .multiply (leftValue := value) (rightValue := value) (leftCost := 1) (rightCost := 1) leaf leaf
    exact .ifTrue condition multiplied

theorem conditional_arithmetic_keeps_its_selected_cost_across_stores
    (choice : Bool) (value : Core.Word) (first replacement : Core.Store) :
    LocalExpressionEvaluatesWithCost branchNames (branchEnvironment choice value) first branch
      (.word (if choice then value.mul value else value)) first (if choice then 8 else 4) ∧
    LocalExpressionEvaluatesWithCost branchNames (branchEnvironment choice value) replacement branch
      (.word (if choice then value.mul value else value)) replacement (if choice then 8 else 4) :=
  ⟨branchCost choice value first, (branchCost choice value first).change_store replacement⟩

private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "T"⟩, []⟩⟩⟩ none⟩
private def parameter : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, "x"⟩ annotation⟩
private def declaration : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "identity"⟩, none, ⟨span, [parameter]⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation]⟩⟩, none⟩, body (ref "x")⟩⟩
private def types (type : Core.Ty) : TypeNameTable := [(["T"], type)]
private def argument (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    TypedRuntimeArgument := ⟨type, value, typed⟩
private def compiled (type : Core.Ty) : CompiledRuntimeFunction :=
  ⟨LocalTypeInputs.empty.bindFresh owner "x" type, .var 0, type⟩
private theorem compilation (type : Core.Ty) : RuntimeFunctionCompiles (types type) owner declaration (compiled type) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩
private def prepared (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    PreparedRuntimeFunction := ⟨LocalInputs.empty.bindFresh owner "x" type value typed, .var 0, type⟩
private theorem identityCost (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (store : Core.Store) : RuntimeFunctionEvaluatesWithCost (types type) owner declaration
      [argument type value typed] store type value store 1 := by
  have preparation : RuntimeFunctionPrepares (types type) owner declaration
      [argument type value typed] (prepared type value typed) :=
    ⟨(compilation type).header,
      .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil, (compilation type).body⟩
  exact .intro preparation (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.identifier .head .head))

theorem independently_prepared_identity_keeps_value_type_and_exact_cost
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (first replacement : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (types type) owner declaration
      [argument type value typed] replacement type value replacement 1 ∧
    (RuntimeFunctionEvaluatesWithCost (types type) owner declaration [argument type value typed]
      first type value first 1 ↔ first = first ∧ RuntimeFunctionEvaluatesWithCost (types type) owner declaration
        [argument type value typed] replacement type value replacement 1) :=
  ⟨(identityCost type value typed first).change_store replacement, runtimeFunctionEvaluatesWithCost_store_iff⟩

theorem same_fuel_preserves_terminal_and_exhaustion_observations_not_stores
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (fuel : Nat) (first replacement : Core.Store) :
    (runRuntimeFunction? (types type) owner declaration [argument type value typed] fuel first =
      some (type, .done value first) ↔ runRuntimeFunction? (types type) owner declaration
        [argument type value typed] fuel replacement = some (type, .done value replacement)) ∧
    ((∃ state, runRuntimeFunction? (types type) owner declaration [argument type value typed]
        fuel first = some (type, .outOfFuel state)) ↔
      (∃ state, runRuntimeFunction? (types type) owner declaration [argument type value typed]
        fuel replacement = some (type, .outOfFuel state))) ∧
    (Core.runStateful fuel (Core.State.initial (.var 0) [value] first) = .done value first ↔
      Core.runStateful fuel (Core.State.initial (.var 0) [value] replacement) = .done value replacement) ∧
    ((∃ state, Core.runStateful fuel (Core.State.initial (.var 0) [value] first) = .outOfFuel state) ↔
      (∃ state, Core.runStateful fuel (Core.State.initial (.var 0) [value] replacement) = .outOfFuel state)) :=
  ⟨runRuntimeFunction?_done_store_iff _ _ _ _ _ _ _ _ _,
    runRuntimeFunction?_outOfFuel_store_iff _ _ _ _ _ _ _ _,
    (compilation type).compiled_done_store_iff [argument type value typed] rfl fuel first replacement value,
    (compilation type).compiled_outOfFuel_store_iff [argument type value typed] rfl fuel first replacement⟩

theorem distinct_stores_prevent_literal_result_equality
    (value : Core.Value) (first replacement : Core.Store) (different : first ≠ replacement) :
    Core.runStateful 0 (Core.State.initial (.var 0) [value] first) ≠
      Core.runStateful 0 (Core.State.initial (.var 0) [value] replacement) ∧
    Core.runStateful 1 (Core.State.initial (.var 0) [value] first) ≠
      Core.runStateful 1 (Core.State.initial (.var 0) [value] replacement) := by
  constructor
  · intro same
    exact different (congrArg Core.State.store (Core.StatefulRunResult.outOfFuel.inj same))
  · intro same
    exact different (Core.StatefulRunResult.done.inj same).2

theorem reading_core_can_preserve_each_store_but_return_different_values
    (left right : Core.Word) (different : left ≠ right) :
    Core.runStateful 3 (Core.State.initial (.loadCell (.var 0)) [.cellRef .word 0] [.word left]) =
      .done (.word left) [.word left] ∧
    Core.runStateful 3 (Core.State.initial (.loadCell (.var 0)) [.cellRef .word 0] [.word right]) =
      .done (.word right) [.word right] ∧ Core.Value.word left ≠ .word right :=
  ⟨rfl, rfl, fun same => different (Core.Value.word.inj same)⟩

end Tests.FrontendStoreIndependence
end
