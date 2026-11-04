import Solcore.Syntax.Grammar.Statements
import Solcore.Syntax.Parser.CoreAssignmentStatementDiagnosticReflectionProperties
import Solcore.Syntax.Parser.Internal.Basics

/-!
Exact declarative soundness for assignment operators and optional assignment
tails, together with the pure endpoint bridge used by statement construction.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

namespace StatementSimpleInternals

/-- Forget the executable tail wrapper while retaining its source payload. -/
def AssignmentTail.declarative : AssignmentTail →
    DeclarativeGrammar.CoreAssignmentTail
  | .value operator right => .value operator right
  | .bitNot operator => .bitNot operator

@[simp] theorem assignmentEnd_eq_declarative (tail : AssignmentTail) :
    assignmentEnd tail =
      DeclarativeGrammar.assignmentEnd tail.declarative := by
  cases tail <;> rfl

@[simp] theorem statementEnd_eq_declarative (left : Expr)
    (tail : Option AssignmentTail) (semicolon : Option SourceSpan) :
    statementEnd left tail semicolon =
      DeclarativeGrammar.statementEnd left
        (tail.map AssignmentTail.declarative) semicolon := by
  cases semicolon <;> cases tail <;> simp [statementEnd,
    DeclarativeGrammar.statementEnd]

/-- One successful value-assignment operator is its exact source tokens. -/
theorem valueAssignOperator_success_sound {input next : State}
    {operator : Located ValueAssignOp}
    (result : valueAssignOperator input = .ok operator next) :
    DeclarativeGrammar.ValueAssignOperatorParses
      input.declarativeRemainder operator next.declarativeRemainder := by
  unfold valueAssignOperator at result
  cases decoded : valueAssignAt? input with
  | none => simp [decoded, rejectAt] at result
  | some value =>
      simp only [decoded] at result
      cases result
      exact ⟨decoded, rfl⟩

private theorem valueAssignOperatorAbsentAt_of_lookahead_false
    {input : State}
    (absent : (valueAssignAt? input).isSome = false) :
    DeclarativeGrammar.ValueAssignOperatorAbsentAt
      input.declarativeRemainder := by
  unfold DeclarativeGrammar.ValueAssignOperatorAbsentAt
  cases decoded : valueAssignAt? input with
  | none => exact decoded
  | some _ => simp [decoded] at absent

private theorem assignmentTailAbsentAt_of_start_false {input : State}
    (absent : (isSymbol input .tildeEqual ||
      (valueAssignAt? input).isSome) = false) :
    DeclarativeGrammar.AssignmentTailAbsentAt
      input.declarativeRemainder := by
  rcases Bool.or_eq_false_iff.mp absent with ⟨tildeAbsent, valueAbsent⟩
  exact ⟨symbolAbsentAt_of_isSymbol_eq_false .tildeEqual tildeAbsent,
    valueAssignOperatorAbsentAt_of_lookahead_false valueAbsent⟩

/-- Every diagnostic-free assignment-tail success follows the prioritized grammar. -/
theorem assignmentTail_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {tail : AssignmentTail}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : assignmentTail expression input = .ok tail next) :
    DeclarativeGrammar.AssignmentTailParses expressionParses
      input.declarativeRemainder tail.declarative
        next.declarativeRemainder := by
  unfold assignmentTail at result
  by_cases bitNot : isSymbol input .tildeEqual
  · simp only [bitNot, if_true] at result
    rcases bind_ok_components result with
      ⟨operator, afterOperator, operatorResult, finished⟩
    cases finished
    exact .bitNot operator.span
      (symbol_success_exactTokenParses .tildeEqual .statement operatorResult)
  · have bitNotFalse : isSymbol input .tildeEqual = false :=
      Bool.eq_false_iff.mpr bitNot
    simp only [bitNotFalse, Bool.false_eq_true, if_false] at result
    cases decoded : valueAssignAt? input with
    | none => rw [decoded] at result; unfold rejectAt at result; contradiction
    | some operator =>
        rw [decoded] at result
        rcases bind_ok_components result with
          ⟨located, afterOperator, operatorResult, rest⟩
        rcases bind_ok_components rest with
          ⟨right, afterRight, rightResult, finished⟩
        cases finished
        exact .value
          (symbolAbsentAt_of_isSymbol_eq_false .tildeEqual bitNotFalse)
          (valueAssignOperator_success_sound operatorResult)
          (expressionSound diagnosticFree rightResult)

/-- Optional-tail success is maximal and preserves exact absence evidence. -/
theorem optionalAssignmentTail_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {tail : Option AssignmentTail}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalAssignmentTail expression input = .ok tail next) :
    DeclarativeGrammar.OptionalAssignmentTailParses expressionParses
      input.declarativeRemainder (tail.map AssignmentTail.declarative)
        next.declarativeRemainder := by
  unfold optionalAssignmentTail at result
  by_cases starts : (isSymbol input .tildeEqual ||
      (valueAssignAt? input).isSome) = true
  · simp only [starts, if_true] at result
    rcases bind_ok_components result with
      ⟨value, afterTail, tailResult, finished⟩
    cases finished
    exact .present (assignmentTail_success_sound expression expressionParses
      expressionSound diagnosticFree tailResult)
  · have startsFalse : (isSymbol input .tildeEqual ||
        (valueAssignAt? input).isSome) = false :=
      Bool.eq_false_iff.mpr starts
    simp only [startsFalse, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (assignmentTailAbsentAt_of_start_false startsFalse)

end StatementSimpleInternals

end Solcore.Syntax.Parser
