import Solcore.Syntax.Parser.CoreAssignmentTailOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementSimpleSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-!
Executable ordinary-success and exact-rejection bridges for the terminal Core
assignment-or-expression statement parser.
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

private theorem optionalSemicolon_eq_ok (input : State) :
    ∃ semicolon output,
      StatementSimpleInternals.optionalSemicolon input =
        .ok semicolon output := by
  unfold StatementSimpleInternals.optionalSemicolon getState
  simp only [bind]
  by_cases present : isSymbol input .semicolon
  · rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .statement present
      with ⟨token, tokenResult⟩
    exact ⟨some token.span, { input with cursor := input.cursor + 1 }, by
      simp only [present, if_true, tokenResult, pure]⟩
  · have absent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr present
    exact ⟨none, input, by
      simp only [absent, Bool.false_eq_true, if_false, pure]⟩

/-- Every executable fallback success follows the ordinary grammar, including
diagnosed assignment successes whose semicolon is absent. -/
theorem assignmentOrExpressionStatement_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {statement : Statement}
    (result : assignmentOrExpressionStatement expression input =
      .ok statement output) :
    DeclarativeGrammar.AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary input.declarativeRemainder statement
        output.declarativeRemainder := by
  unfold assignmentOrExpressionStatement at result
  rcases bind_ok_components result with
    ⟨left, afterLeft, leftResult, tailStage⟩
  rcases bind_ok_components tailStage with
    ⟨tail, afterTail, tailResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  have leftParsed := expressionSuccessSound leftResult
  have tailParsed :=
    StatementSimpleInternals.optionalAssignmentTail_success_ordinary_sound
      expression expressionOrdinary expressionSuccessSound tailResult
  have semicolonParsed :=
    StatementSimpleInternals.optionalSemicolon_success_sound semicolonResult
  cases tail with
  | none =>
      cases finished
      exact ⟨left, afterLeft.declarativeRemainder, none,
        afterTail.declarativeRemainder, semicolon, leftParsed, tailParsed,
        semicolonParsed, by
          simpa only [StatementSimpleInternals.statementEnd_eq_declarative,
            Option.map_none] using
              (DeclarativeGrammar.AssignmentOrExpressionOrdinaryBuilds.expression
                left semicolon)⟩
  | some tail =>
      cases tail with
      | value operator right =>
          cases semicolon with
          | none =>
              simp only [Option.isNone_none, if_true, emitDiagnostic,
                modifyState, bind, pure] at finished
              cases finished
              exact ⟨left, afterLeft.declarativeRemainder,
                some (.value operator right), afterTail.declarativeRemainder,
                none, leftParsed, tailParsed, semicolonParsed, by
                  simpa only [
                    StatementSimpleInternals.statementEnd_eq_declarative,
                    StatementSimpleInternals.AssignmentTail.declarative,
                    Option.map_some] using
                    (DeclarativeGrammar.AssignmentOrExpressionOrdinaryBuilds.value
                      left right operator none)⟩
          | some marker =>
              simp only [Option.isNone_some, Bool.false_eq_true, if_false,
                pure] at finished
              cases finished
              exact ⟨left, afterLeft.declarativeRemainder,
                some (.value operator right), afterTail.declarativeRemainder,
                some marker, leftParsed, tailParsed, semicolonParsed, by
                  simpa only [
                    StatementSimpleInternals.statementEnd_eq_declarative,
                    StatementSimpleInternals.AssignmentTail.declarative,
                    Option.map_some] using
                    (DeclarativeGrammar.AssignmentOrExpressionOrdinaryBuilds.value
                      left right operator (some marker))⟩
      | bitNot operator =>
          cases semicolon with
          | none =>
              simp only [Option.isNone_none, if_true, emitDiagnostic,
                modifyState, bind, pure] at finished
              cases finished
              exact ⟨left, afterLeft.declarativeRemainder,
                some (.bitNot operator), afterTail.declarativeRemainder,
                none, leftParsed, tailParsed, semicolonParsed, by
                  simpa only [
                    StatementSimpleInternals.statementEnd_eq_declarative,
                    StatementSimpleInternals.AssignmentTail.declarative,
                    Option.map_some] using
                    (DeclarativeGrammar.AssignmentOrExpressionOrdinaryBuilds.bitNot
                      left operator none)⟩
          | some marker =>
              simp only [Option.isNone_some, Bool.false_eq_true, if_false,
                pure] at finished
              cases finished
              exact ⟨left, afterLeft.declarativeRemainder,
                some (.bitNot operator), afterTail.declarativeRemainder,
                some marker, leftParsed, tailParsed, semicolonParsed, by
                  simpa only [
                    StatementSimpleInternals.statementEnd_eq_declarative,
                    StatementSimpleInternals.AssignmentTail.declarative,
                    Option.map_some] using
                    (DeclarativeGrammar.AssignmentOrExpressionOrdinaryBuilds.bitNot
                      left operator (some marker))⟩

/-- Every executable fallback rejection is exactly the initial expression or
the right expression of a committed value assignment. -/
theorem assignmentOrExpressionStatement_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : assignmentOrExpressionStatement expression input =
      .reject failure rejected) :
    DeclarativeGrammar.AssignmentOrExpressionStatementRejects
      expressionOrdinary expressionRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold assignmentOrExpressionStatement at result
  cases leftResult : expression input with
  | invariant error => simp [bind, leftResult] at result
  | reject leftFailure leftRejected =>
      simp only [bind, leftResult] at result
      cases result
      exact .leftRejected (expressionRejectSound leftResult)
  | ok left afterLeft =>
      simp only [bind, leftResult] at result
      cases tailResult : StatementSimpleInternals.optionalAssignmentTail
          expression afterLeft with
      | invariant error => simp [tailResult] at result
      | reject tailFailure tailRejected =>
          simp only [tailResult] at result
          cases result
          rcases
              StatementSimpleInternals.optionalAssignmentTail_reject_ordinary_sound
                expression expressionRejects expressionRejectSound tailResult
            with ⟨afterOperator, operator, tildeAbsent, operatorParsed,
              rightRejected⟩
          exact .rightRejected (expressionSuccessSound leftResult)
            tildeAbsent operatorParsed rightRejected
      | ok tail afterTail =>
          simp only [tailResult] at result
          rcases optionalSemicolon_eq_ok afterTail with
            ⟨semicolon, afterSemicolon, semicolonResult⟩
          simp only [semicolonResult] at result
          cases tail with
          | none => simp [pure] at result
          | some tail =>
              cases tail <;> cases semicolon <;>
                simp [emitDiagnostic, modifyState, pure] at result

/-- Public accessor for the parser-independent deterministic outcome contract
used by this executable bridge. -/
theorem assignmentOrExpressionStatement_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (outcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.AssignmentOrExpressionStatementOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.AssignmentOrExpressionStatementRejects
        expressionOrdinary expressionRejects) :=
  DeclarativeGrammar.assignmentOrExpressionStatementDeterministicOutcomeSpec
    outcomes

end Solcore.Syntax.Parser
