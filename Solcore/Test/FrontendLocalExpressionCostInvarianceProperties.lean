import Solcore.Frontend.LocalInputsCostInvariance
import Solcore.Frontend.LocalInputsExtensionProperties
import Solcore.Core.BitwiseLogic

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
