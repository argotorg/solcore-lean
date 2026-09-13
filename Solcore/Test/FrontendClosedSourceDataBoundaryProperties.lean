import Solcore.Frontend.ClosedSourceDataExpression
import Solcore.Frontend.ClosedSourceEvaluation
import Solcore.Frontend.LocalExpressionEvaluationRules
import Solcore.Frontend.RuntimeValueProperties

/- Independent shape/image/alignment counterexamples, not failures inferred from a budget. -/
set_option autoImplicit false
namespace Tests.ClosedSourceDataBoundaries
open Solcore Solcore.Frontend

private def embedded (environment : Resolved.Environment) : Resolved.LocalScope RuntimeValue :=
  environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2))

private def unit (span : Syntax.SourceSpan) : Syntax.Expr := ⟨span, .tuple ⟨span, []⟩⟩
private def reference (span : Syntax.SourceSpan) : Syntax.Expr := ⟨span, .identifier ⟨span, "c"⟩⟩
private def negated (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span, .unary ⟨span, .logicalNot⟩ (reference span)⟩
private def singleton (span : Syntax.SourceSpan) : Syntax.Expr := ⟨span, .tuple ⟨span, [unit span]⟩⟩
private def unary (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span, .lambda span ⟨span, [⟨span, .inferred ⟨span, "x"⟩⟩]⟩ none
    ⟨span, [⟨span, .returnStmt none⟩]⟩⟩
private def applied (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span, .call (unary span) ⟨span, [unit span]⟩⟩
private def skipped (span : Syntax.SourceSpan) (choice : Bool) : Syntax.Expr :=
  ⟨span, .conditional (reference span) span
    (if choice then unit span else unary span) span
    (if choice then unary span else unit span)⟩

private theorem unary_outside (span : Syntax.SourceSpan) :
    ¬ ClosedSourceDataExpression (unary span) := by
  intro fragment
  cases fragment

variable (span : Syntax.SourceSpan) (owner : Resolved.DeclarationId)
  (names : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)

/-- Shape admission of any string spelling establishes neither old nor closed evaluation. -/
theorem string_admission_has_no_evaluation (spelling : String) :
    ClosedSourceDataExpression ⟨span, .literal ⟨span, .string spelling⟩⟩ ∧
    (∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) ⟨span, .literal ⟨span, .string spelling⟩⟩ actual final) ∧
    (∀ value final, ¬ LocalExpressionEvaluates names environment store
      ⟨span, .literal ⟨span, .string spelling⟩⟩ value final) := by
  refine ⟨.literal, ?_, ?_⟩
  · intro actual final evaluated
    cases evaluated with
    | wordLiteral meaning => cases meaning
    | creation shape => cases shape
  · intro value final evaluated
    cases evaluated with
    | wordLiteral meaning => cases meaning

/-- Singleton tuples remain excluded, while negation is admitted and evaluates successfully. -/
theorem singleton_and_negation_are_outside_data (id : Resolved.LocalId) (choice : Bool) :
    ¬ ClosedSourceDataExpression (singleton span) ∧
    ClosedSourceDataExpression (negated span) ∧
    ResolvesLocalExpression [("c", id)] (negated span) (.unary .boolNot (.var id)) ∧
    LocalExpressionEvaluates [("c", id)] [(id, .bool choice)] store
      (negated span) (.bool (!choice)) store ∧
    ClosedSourceExpressionEvaluates owner [("c", id)]
      (embedded [(id, .bool choice)]) (store.map RuntimeValue.ofCore) (negated span)
      (.bool (!choice)) (store.map RuntimeValue.ofCore) := by
  refine ⟨?_, ?_, .logicalNot (.identifier .head), .logicalNot (.identifier .head .head), ?_⟩
  · intro fragment; cases fragment
  · exact .logicalNot .reference
  · simp only [embedded, List.map_cons, List.map_nil, RuntimeValue.ofCore]
    exact .logicalNot (.reference .head .head)

/-- A directly created original closure from embedded inputs has no Core-value preimage. -/
theorem creation_from_core_inputs_is_not_core_data :
    ¬ ClosedSourceDataExpression (unary span) ∧
    ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (unary span)
      (.sourceClosure (unary span) owner names (embedded environment)) (store.map RuntimeValue.ofCore) ∧
    ¬ ∃ value, RuntimeValue.sourceClosure (unary span) owner names (embedded environment) =
      RuntimeValue.ofCore value := by
  refine ⟨unary_outside span, .creation .inferred, ?_⟩
  rintro ⟨value, same⟩
  have impossible := congrArg RuntimeValue.toCore? same
  simp only [RuntimeValue.toCore?, RuntimeValue.toCore?_ofCore, reduceCtorEq] at impossible

/-- An embedded endpoint alone cannot recover a missing old source-call rule. -/
theorem embedded_unit_call_still_has_no_local_rule :
    ¬ ClosedSourceDataExpression (applied span) ∧
    ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (applied span) (RuntimeValue.ofCore .unit)
      (store.map RuntimeValue.ofCore) ∧
    (∀ value final, ¬ LocalExpressionEvaluates names environment store (applied span) value final) := by
  refine ⟨?_, ?_, ?_⟩
  · intro fragment; cases fragment
  · simp only [RuntimeValue.ofCore]
    exact .call .inferred (.creation .inferred) .unit .bare
  · intro value final evaluated
    cases evaluated

/-- Either actual Boolean choice can skip an original lambda outside the whole syntax gate. -/
theorem unselected_lambda_allows_raw_overlap (id : Resolved.LocalId) (choice : Bool) :
    ¬ ClosedSourceDataExpression (skipped span choice) ∧
    ClosedSourceExpressionEvaluates owner [("c", id)] (embedded [(id, .bool choice)])
      (store.map RuntimeValue.ofCore) (skipped span choice) .unit (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates [("c", id)] [(id, .bool choice)] store (skipped span choice) .unit store := by
  have outside : ¬ ClosedSourceDataExpression (skipped span choice) := by
    cases choice with
    | false =>
        intro fragment
        cases fragment with
        | conditional _ thenSyntax _ => exact unary_outside span thenSyntax
    | true =>
        intro fragment
        cases fragment with
        | conditional _ _ elseSyntax => exact unary_outside span elseSyntax
  have guard : ClosedSourceExpressionEvaluates owner [("c", id)] (embedded [(id, .bool choice)])
      (store.map RuntimeValue.ofCore) (reference span) (.bool choice) (store.map RuntimeValue.ofCore) := by
    simp only [embedded, List.map_cons, List.map_nil, RuntimeValue.ofCore]
    exact .reference .head .head
  refine ⟨outside, ?_, ?_⟩
  · cases choice with
    | false => exact .conditionalFalse guard .unit
    | true => exact .conditionalTrue guard .unit
  · cases choice with
    | false => exact .ifFalse (.identifier .head .head) .unit
    | true => exact .ifTrue (.identifier .head .head) .unit

private def ordered (first second : Resolved.LocalId) : Resolved.Environment :=
  [(first, .bool true), (second, .bool false)]
private def reordered (first second : Resolved.LocalId) : Resolved.Environment :=
  [(second, .bool false), (first, .bool true)]

/-- Reusing index zero after a same-length reordering changes Core's value, not the named value. -/
theorem equal_lengths_do_not_align_runtime_ids (first second : Resolved.LocalId)
    (different : second ≠ first) :
    (ordered first second).length = (reordered first second).length ∧
    ResolvesLocalExpression [("c", first)] (reference span) (.var first) ∧
    Resolved.Lowers (Resolved.LocalScope.ids (ordered first second)) (.var first) (.var 0) ∧
    Resolved.Lowers (Resolved.LocalScope.ids (reordered first second)) (.var first) (.var 1) ∧
    LocalExpressionEvaluates [("c", first)] (reordered first second) store
      (reference span) (.bool true) store ∧
    ClosedSourceExpressionEvaluates owner [("c", first)] (embedded (reordered first second))
      (store.map RuntimeValue.ofCore) (reference span) (.bool true) (store.map RuntimeValue.ofCore) ∧
    Core.Evaluates (Resolved.LocalScope.values (ordered first second)) store (.var 0) (.bool true) store ∧
    Core.Evaluates (Resolved.LocalScope.values (reordered first second)) store (.var 0) (.bool false) store ∧
    Core.Evaluates (Resolved.LocalScope.values (reordered first second)) store (.var 1) (.bool true) store ∧
    ¬ Resolved.Lowers (Resolved.LocalScope.ids (reordered first second)) (.var first) (.var 0) := by
  refine ⟨rfl, .identifier .head, .var .head, .var (.tail different .head),
    .identifier .head (.tail different .head), ?_, .var rfl, .var rfl, .var rfl, ?_⟩
  · simp only [embedded, reordered, List.map_cons, List.map_nil, RuntimeValue.ofCore]
    exact .reference .head (.tail different .head)
  · intro lowered
    cases lowered with
    | var found =>
        cases found with
        | head => exact different rfl

end Tests.ClosedSourceDataBoundaries
