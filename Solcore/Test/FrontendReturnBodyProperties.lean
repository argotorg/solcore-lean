import Solcore.Frontend.ReturnBody
import Solcore.Core.BitwiseLogic

/-! ADR-0169: singleton return wrappers preserve the checked expression and its
independent transition count. Other statements are never silently discarded. -/

set_option autoImplicit false

namespace Tests.FrontendReturnBody

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "return-body.sol"⟩, 0, 4⟩
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ReturnBody", by decide⟩], by decide⟩⟩, 0⟩
private def returned (source : Option Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt source⟩]⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def unary (op : Syntax.UnaryOp) (child : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, op⟩ child⟩
private def binary (op : Syntax.BinaryOp) (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, op⟩ right⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr := ⟨span, .conditional condition span left span right⟩
private def seven : Core.Word := ⟨7, by decide⟩
private def literal : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "7"⟩⟩
private theorem meaning : WordLiteralDenotes ⟨span, .decimal "7"⟩ seven :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 7) (by decide) (by decide)) .nil)
private def inputs (choice : Bool) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool

theorem bare_return_has_unit_meaning_and_exact_zero_one_fuel_boundary
    (supplied : LocalInputs) (store : Core.Store) (blockSpan returnSpan : Syntax.SourceSpan) :
    let body : Syntax.Block := ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩
    ReturnBodyHasType supplied.names supplied.context body .unit ∧
    ReturnBodyEvaluates supplied.names supplied.environment store body .unit store ∧
    ReturnBodyEvaluatesWithCost supplied.names supplied.environment store body .unit store 1 ∧
    supplied.checkReturnBody? body = some (.unit, .unit) ∧
    supplied.runReturnBody? 0 body store = some (.unit, .outOfFuel
      (Core.State.initial .unit (Resolved.LocalScope.values supplied.environment) store)) ∧
    supplied.runReturnBody? 1 body store = some (.unit, .done .unit store) := by
  intro body
  exact ⟨.bare, .bare, .bare, rfl, rfl, rfl⟩

theorem expression_return_retains_the_actual_checker_and_independent_child_meaning
    (supplied : LocalInputs) (source : Syntax.Expr) (type : Core.Ty)
    (value : Core.Value) (initialStore finalStore : Core.Store) (cost : Nat)
    (blockSpan returnSpan : Syntax.SourceSpan) :
    let body : Syntax.Block := ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩
    supplied.checkReturnBody? body = supplied.check? source ∧
    (ReturnBodyHasType supplied.names supplied.context body type ↔
      LocalExpressionHasType supplied.names supplied.context source type) ∧
    (ReturnBodyEvaluates supplied.names supplied.environment initialStore body value finalStore ↔
      LocalExpressionEvaluates supplied.names supplied.environment initialStore source value finalStore) ∧
    (ReturnBodyEvaluatesWithCost supplied.names supplied.environment initialStore body value finalStore cost ↔
      LocalExpressionEvaluatesWithCost supplied.names supplied.environment initialStore source value finalStore cost) := by
  intro body
  dsimp only [body]
  refine ⟨rfl, ⟨?_, ReturnBodyHasType.expression⟩,
    ⟨?_, ReturnBodyEvaluates.expression⟩, ⟨?_, ReturnBodyEvaluatesWithCost.expression⟩⟩
  all_goals intro derived; cases derived with | expression child => exact child

private def source : Syntax.Expr :=
  branch (binary .logicalAnd (unary .logicalNot (ref "c")) (unary .logicalNot (ref "c")))
    (unary .bitNot literal) (unary .bitNot (binary .bitOr literal literal))
private def required (choice : Bool) : Nat := if choice then 15 else 13
private abbrev Cost (choice : Bool) (store : Core.Store) (source : Syntax.Expr) (value : Core.Value) (cost : Nat) :=
  LocalExpressionEvaluatesWithCost (inputs choice).names (inputs choice).environment store source value store cost
private theorem cost_c (choice : Bool) (store : Core.Store) : Cost choice store (ref "c") (.bool choice) 1 :=
  .identifier .head .head
private theorem cost_seven (choice : Bool) (store : Core.Store) : Cost choice store literal (.word seven) 1 :=
  .wordLiteral meaning
private theorem sourceTyped (choice : Bool) : LocalExpressionHasType (inputs choice).names (inputs choice).context source .word :=
  .conditional (.logicalAnd (.logicalNot (.identifier .head .head)) (.logicalNot (.identifier .head .head)))
    (.bitNot (.wordLiteral meaning)) (.bitNot (.bitOr (.wordLiteral meaning) (.wordLiteral meaning)))
private theorem sourceCost (choice : Bool) (store : Core.Store) :
    Cost choice store source (.word seven.bitNot) (required choice) := by
  have left : Cost choice store (unary .bitNot literal) (.word seven.bitNot) 3 := .bitNot (cost_seven choice store)
  have right : Cost choice store (unary .bitNot (binary .bitOr literal literal)) (.word seven.bitNot) 7 := by
    simpa [Cost, unary, binary, Core.Word.bitOr_self] using
      (LocalExpressionEvaluatesWithCost.bitNot (.bitOr (cost_seven choice store) (cost_seven choice store)))
  cases choice
  · exact .ifTrue (.andTrue (.logicalNot (cost_c false store)) (.logicalNot (cost_c false store))) left
  · exact .ifFalse (.andFalse (.logicalNot (cost_c true store))) right

theorem returned_negation_complement_bitwise_conditional_and_short_circuit_keep_their_cost
    (choice : Bool) (store : Core.Store) (fuel : Nat) :
    ReturnBodyHasType (inputs choice).names (inputs choice).context (returned (some source)) .word ∧
    ReturnBodyEvaluatesWithCost (inputs choice).names (inputs choice).environment store
      (returned (some source)) (.word seven.bitNot) store (required choice) ∧
    ((inputs choice).runReturnBody? fuel (returned (some source)) store =
      some (.word, .done (.word seven.bitNot) store) ↔ required choice ≤ fuel) ∧
    ((∃ suspended, (inputs choice).runReturnBody? fuel (returned (some source)) store =
      some (.word, .outOfFuel suspended)) ↔ fuel < required choice) := by
  have typed : ReturnBodyHasType (inputs choice).names (inputs choice).context (returned (some source)) .word :=
    .expression (sourceTyped choice)
  have evaluated : ReturnBodyEvaluatesWithCost (inputs choice).names (inputs choice).environment store
      (returned (some source)) (.word seven.bitNot) store (required choice) := .expression (sourceCost choice store)
  obtain ⟨value, cost, other, _, boundaries⟩ := LocalInputs.returnBody_typed_cost_execution typed store
  obtain ⟨sameValue, _, sameCost⟩ := other.deterministic evaluated
  refine ⟨typed, evaluated, by simpa only [sameValue, sameCost] using (boundaries fuel).1, ?_⟩
  rw [LocalInputs.runReturnBody?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨_, otherValue, otherCost, otherEvaluation, short⟩
    exact (otherEvaluation.deterministic evaluated).2.2 ▸ short
  · intro short
    exact ⟨typed, .word seven.bitNot, required choice, evaluated, short⟩

private def missing : Syntax.Expr := branch (ref "c") literal (ref "missing")
theorem raw_return_of_a_skipped_missing_branch_does_not_bypass_checking
    (store : Core.Store) (fuel : Nat) :
    ReturnBodyEvaluates (inputs true).names (inputs true).environment store (returned (some missing)) (.word seven) store ∧
    ReturnBodyEvaluatesWithCost (inputs true).names (inputs true).environment store (returned (some missing)) (.word seven) store 4 ∧
    (inputs true).checkReturnBody? (returned (some missing)) = none ∧
    (inputs true).runReturnBody? fuel (returned (some missing)) store = none := by
  have counted : Cost true store missing (.word seven) 4 := .ifTrue (cost_c true store) (cost_seven true store)
  have rejected : (inputs true).checkReturnBody? (returned (some missing)) = none := by
    simp [LocalInputs.checkReturnBody?, elaborateReturnBody?, returned, elaborateLocalExpression?,
      resolveLocalExpression?, missing, branch, ref, inputs, LocalInputs.names, LocalInputs.bindFresh,
      LocalInputs.empty, LocalNameTable.lookup?]
  exact ⟨.expression counted.erase, .expression counted, rejected,
    by simp only [LocalInputs.runReturnBody?, rejected, bind, Option.bind_none]⟩

private def unsupported : List (List Syntax.Statement) :=
  [[], [⟨span, .returnStmt none⟩, ⟨span, .returnStmt none⟩],
   [⟨span, .block [⟨span, .returnStmt none⟩]⟩],
   [⟨span, .expression literal false⟩], [⟨span, .expression literal true⟩],
   [⟨span, .letDecl ⟨span, "x"⟩ none (some literal)⟩],
   [⟨span, .returnStmt (some literal)⟩, ⟨span, .expression (ref "missing") true⟩]]

theorem other_statements_are_not_dropped_even_after_return
    (supplied : LocalInputs) (statements : List Syntax.Statement) (present : statements ∈ unsupported)
    (outer : Syntax.SourceSpan) (store finalStore : Core.Store) (value : Core.Value) (type : Core.Ty) (cost fuel : Nat) :
    supplied.checkReturnBody? ⟨outer, statements⟩ = none ∧
    supplied.runReturnBody? fuel ⟨outer, statements⟩ store = none ∧
    ¬ ReturnBodyHasType supplied.names supplied.context ⟨outer, statements⟩ type ∧
    ¬ ReturnBodyEvaluates supplied.names supplied.environment store ⟨outer, statements⟩ value finalStore ∧
    ¬ ReturnBodyEvaluatesWithCost supplied.names supplied.environment store ⟨outer, statements⟩ value finalStore cost := by
  simp only [unsupported, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> intro impossible <;> cases impossible

theorem raw_cost_derivations_determine_value_store_and_positive_cost_without_checking
    (table : LocalNameTable) (environment : Resolved.Environment) (body : Syntax.Block)
    (initialStore leftStore rightStore : Core.Store) (left right : Core.Value) (leftCost rightCost : Nat)
    (first : ReturnBodyEvaluatesWithCost table environment initialStore body left leftStore leftCost)
    (second : ReturnBodyEvaluatesWithCost table environment initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost ∧
    leftStore = initialStore ∧ 0 < leftCost ∧
    ReturnBodyEvaluates table environment initialStore body left leftStore ∧
    (ReturnBodyEvaluates table environment initialStore body right rightStore ↔
      ∃ cost, ReturnBodyEvaluatesWithCost table environment initialStore body right rightStore cost) := by
  obtain ⟨sameValue, sameStore, sameCost⟩ := first.deterministic second
  exact ⟨sameValue, sameStore, sameCost, first.store_eq, first.cost_pos, first.erase,
    returnBodyEvaluates_iff_exists_cost⟩

private def singleton (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "item" type value typed

theorem structurally_typed_input_values_are_returned_with_one_transition
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) (store : Core.Store) :
    let supplied := singleton type value typed
    let body := returned (some (ref "item"))
    ReturnBodyHasType supplied.names supplied.context body type ∧
    ReturnBodyEvaluates supplied.names supplied.environment store body value store ∧
    ReturnBodyEvaluatesWithCost supplied.names supplied.environment store body value store 1 ∧
    supplied.checkReturnBody? body = some (.var 0, type) ∧
    Core.Evaluates [value] store (.var 0) value store ∧
    supplied.runReturnBody? 1 body store = some (type, .done value store) := by
  intro supplied body
  have typing : ReturnBodyHasType supplied.names supplied.context body type := .expression (.identifier .head .head)
  have counted : ReturnBodyEvaluatesWithCost supplied.names supplied.environment store body value store 1 :=
    .expression (.identifier .head .head)
  have checked : supplied.checkReturnBody? body = some (.var 0, type) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  exact ⟨typing, counted.erase, counted, checked, .var rfl,
    LocalInputs.runReturnBody?_done_iff_typed_cost.mpr ⟨typing, 1, counted, Nat.le_refl _⟩⟩

private def closure : Core.Value := .closure .bool .bool (.var 0) []
private theorem closureTyped : Core.ValueHasType closure (.function .bool .bool) := .closure .nil (.var rfl)
theorem returning_closures_and_cell_references_neither_calls_nor_allocates
    (location : Core.Location) (store : Core.Store) :
    (singleton (.function .bool .bool) closure closureTyped).runReturnBody? 1
      (returned (some (ref "item"))) (.unit :: store) =
      some (.function .bool .bool, .done closure (.unit :: store)) ∧
    (singleton (.cell .word) (.cellRef .word location) .cellRef).runReturnBody? 1
      (returned (some (ref "item"))) [] = some (.cell .word, .done (.cellRef .word location) []) ∧
    ([] : Core.Store)[location]? = none :=
  ⟨(structurally_typed_input_values_are_returned_with_one_transition
      (.function .bool .bool) closure closureTyped (.unit :: store)).2.2.2.2.2,
    (structurally_typed_input_values_are_returned_with_one_transition
      (.cell .word) (.cellRef .word location) .cellRef []).2.2.2.2.2, by simp⟩

end Tests.FrontendReturnBody
