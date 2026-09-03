import Solcore.Syntax.DeclarativeCoreMatchCasesValueProperties
import Solcore.Syntax.DeclarativeCoreMatchStatementOutcomeProperties

/-! Exact success values for diagnostic-inclusive Core match statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact child outcomes fix all scrutinees, forward case arms, optional
default, retained spans, and the complete ordinary match statement AST. -/
theorem MatchStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input left afterLeft)
    (rightParsed : MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftClosingSpan leftMarker
        leftValues leftRequired leftOpening leftCases leftDefault leftClosing =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightClosingSpan rightMarker
            rightValues rightRequired rightOpening rightCases rightDefault
            rightClosing =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          rcases MatchScrutineeListOrdinaryParses.result_unique
              expressionOutcomes leftValues rightValues with
            ⟨valuesEq, inputEq⟩
          subst valuesEq
          subst inputEq
          rcases RequireScrutineesOrdinaryParses.result_unique leftRequired
              rightRequired with ⟨requiredEq, inputEq⟩
          subst requiredEq
          subst inputEq
          rcases leftOpening.result_unique rightOpening with
            ⟨openingEq, inputEq⟩
          subst openingEq
          subst inputEq
          rcases leftCases.result_unique statementOutcomes patternOutcomes
              rightCases with ⟨casesEq, inputEq⟩
          subst casesEq
          subst inputEq
          rcases leftDefault.result_unique statementOutcomes rightDefault with
            ⟨defaultEq, inputEq⟩
          subst defaultEq
          subst inputEq
          have closingEq := leftClosing.span_unique rightClosing
          subst closingEq
          rfl

/-- A complete ordinary match success fixes its exact AST and remainder;
diagnostic-only arity or missing-arm validation does not weaken the result. -/
theorem MatchStatementOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input left afterLeft)
    (rightParsed : MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique statementOutcomes expressionOutcomes patternOutcomes
      rightParsed,
    leftParsed.output_unique statementOutcomes.toDeterministicOutcomeSpec
      expressionOutcomes.toDeterministicOutcomeSpec
      patternOutcomes.toDeterministicOutcomeSpec rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
