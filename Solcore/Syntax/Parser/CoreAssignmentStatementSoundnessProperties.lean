import Solcore.Syntax.Parser.CoreAssignmentTailSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementSimpleSoundnessProperties

/-!
Exact diagnostic-free soundness for Core assignment-or-expression statements.
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

/--
Every diagnostic-free fallback success follows the exact independent grammar.
In particular, assignment successes without a semicolon are excluded because
that executable branch emits `assignmentRequiresSemicolon`.
-/
theorem assignmentOrExpressionStatement_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {statement : Statement}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : assignmentOrExpressionStatement expression input =
      .ok statement next) :
    DeclarativeGrammar.AssignmentOrExpressionStatementParses
      expressionParses input.declarativeRemainder statement
        next.declarativeRemainder := by
  unfold assignmentOrExpressionStatement at result
  rcases bind_ok_components result with
    ⟨left, afterLeft, leftResult, tailStage⟩
  rcases bind_ok_components tailStage with
    ⟨tail, afterTail, tailResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  have afterSemicolonFree : afterSemicolon.diagnosticsRev = [] := by
    cases tail with
    | none => cases finished; exact diagnosticFree
    | some tail =>
        cases tail with
        | value operator right =>
            cases semicolon with
            | none =>
                simp only [Option.isNone_none, if_true, emitDiagnostic,
                  modifyState, bind, pure] at finished
                cases finished
                simp [State.emit] at diagnosticFree
            | some marker =>
                simp only [Option.isNone_some, Bool.false_eq_true, if_false,
                  pure] at finished
                cases finished
                exact diagnosticFree
        | bitNot operator =>
            cases semicolon with
            | none =>
                simp only [Option.isNone_none, if_true, emitDiagnostic,
                  modifyState, bind, pure] at finished
                cases finished
                simp [State.emit] at diagnosticFree
            | some marker =>
                simp only [Option.isNone_some, Bool.false_eq_true, if_false,
                  pure] at finished
                cases finished
                exact diagnosticFree
  have afterTailFree :=
    StatementSimpleInternals.optionalSemicolon_reflectsDiagnosticFreeOnSuccess
      afterTail semicolon afterSemicolon semicolonResult afterSemicolonFree
  have afterLeftFree :=
    StatementSimpleInternals.optionalAssignmentTail_reflectsDiagnosticFreeOnSuccess
      expression expressionReflects afterLeft tail afterTail tailResult
        afterTailFree
  have leftGrammar := expressionSound afterLeftFree leftResult
  have tailGrammar :=
    StatementSimpleInternals.optionalAssignmentTail_success_sound expression
      expressionParses expressionSound afterTailFree tailResult
  have semicolonGrammar :=
    StatementSimpleInternals.optionalSemicolon_success_sound semicolonResult
  cases tail with
  | none =>
      cases finished
      exact ⟨left, afterLeft.declarativeRemainder, none,
        afterTail.declarativeRemainder, semicolon, leftGrammar, tailGrammar,
        semicolonGrammar, by
          simpa only [StatementSimpleInternals.statementEnd_eq_declarative,
            Option.map_none] using
              (DeclarativeGrammar.AssignmentOrExpressionBuilds.expression
                left semicolon)⟩
  | some tail =>
      cases tail with
      | value operator right =>
          cases semicolon with
          | none =>
              simp only [Option.isNone_none, if_true, emitDiagnostic,
                modifyState, bind, pure] at finished
              cases finished
              simp [State.emit] at diagnosticFree
          | some marker =>
              simp only [Option.isNone_some, Bool.false_eq_true, if_false,
                pure] at finished
              cases finished
              exact ⟨left, afterLeft.declarativeRemainder,
                some (.value operator right), afterTail.declarativeRemainder,
                some marker, leftGrammar, tailGrammar, semicolonGrammar,
                by
                  simpa only [
                    StatementSimpleInternals.statementEnd_eq_declarative,
                    StatementSimpleInternals.AssignmentTail.declarative,
                    Option.map_some] using
                    (DeclarativeGrammar.AssignmentOrExpressionBuilds.value
                      left right operator marker)⟩
      | bitNot operator =>
          cases semicolon with
          | none =>
              simp only [Option.isNone_none, if_true, emitDiagnostic,
                modifyState, bind, pure] at finished
              cases finished
              simp [State.emit] at diagnosticFree
          | some marker =>
              simp only [Option.isNone_some, Bool.false_eq_true, if_false,
                pure] at finished
              cases finished
              exact ⟨left, afterLeft.declarativeRemainder,
                some (.bitNot operator), afterTail.declarativeRemainder,
                some marker, leftGrammar, tailGrammar, semicolonGrammar,
                by
                  simpa only [
                    StatementSimpleInternals.statementEnd_eq_declarative,
                    StatementSimpleInternals.AssignmentTail.declarative,
                    Option.map_some] using
                    (DeclarativeGrammar.AssignmentOrExpressionBuilds.bitNot
                      left operator marker)⟩

end Solcore.Syntax.Parser
