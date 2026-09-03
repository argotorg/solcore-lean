import Solcore.Syntax.DeclarativeCoreBlockExactnessProperties
import Solcore.Syntax.DeclarativeCoreStatementIfOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementWhileOutcomeProperties

/-! Exact success values for Core `if`, optional `else`, and `while`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact recursive statements fix a prioritized optional else body. -/
theorem OptionalElseBodyOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Option Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalElseBodyOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : OptionalElseBodyOrdinaryParses statementOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present rightSpan rightToken rightBody =>
          exact False.elim (leftAbsent ⟨rightSpan, rightToken.1⟩)
  | present leftSpan leftToken leftBody =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (rightAbsent ⟨leftSpan, leftToken.1⟩)
      | present rightSpan rightToken rightBody =>
          have afterMarkerEq := leftToken.output_unique rightToken
          subst afterMarkerEq
          rcases leftBody.result_unique statementOutcomes rightBody with
            ⟨bodyEq, outputEq⟩
          exact ⟨congrArg some bodyEq, outputEq⟩

/-- Exact expression and recursive statement outcomes fix the condition,
branches, covering source span, and full Core if AST. -/
theorem IfStatementOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input left afterLeft)
    (rightParsed : IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftClosingSpan leftMarker
        leftOpening leftCondition leftClosing leftThen leftElse =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightClosingSpan rightMarker
            rightOpening rightCondition rightClosing rightThen rightElse =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          have inputEq := leftOpening.output_unique rightOpening
          subst inputEq
          rcases expressionOutcomes.successResultUnique leftCondition
              rightCondition with ⟨conditionEq, inputEq⟩
          subst conditionEq
          subst inputEq
          have inputEq := leftClosing.output_unique rightClosing
          subst inputEq
          rcases leftThen.result_unique statementOutcomes rightThen with
            ⟨thenEq, inputEq⟩
          subst thenEq
          subst inputEq
          have elseEq := (OptionalElseBodyOrdinaryParses.result_unique
            statementOutcomes leftElse rightElse).1
          subst elseEq
          rfl

/-- Core if success fixes both its AST and final remainder. -/
theorem IfStatementOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input left afterLeft)
    (rightParsed : IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨IfStatementOrdinaryParses.value_unique expressionOutcomes statementOutcomes
      leftParsed rightParsed,
    IfStatementOrdinaryParses.output_unique
      expressionOutcomes.toDeterministicOutcomeSpec
      statementOutcomes.toDeterministicOutcomeSpec leftParsed rightParsed⟩

/-- Exact expression and recursive statement outcomes fix the condition,
body, covering source span, and full contextual while AST. -/
theorem WhileStatementOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input left afterLeft)
    (rightParsed : WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftClosingSpan leftMarker
        leftOpening leftCondition leftClosing leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightClosingSpan rightMarker
            rightOpening rightCondition rightClosing rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          have inputEq := leftOpening.output_unique rightOpening
          subst inputEq
          rcases expressionOutcomes.successResultUnique leftCondition
              rightCondition with ⟨conditionEq, inputEq⟩
          subst conditionEq
          subst inputEq
          have inputEq := leftClosing.output_unique rightClosing
          subst inputEq
          have bodyEq := leftBody.value_unique statementOutcomes rightBody
          subst bodyEq
          rfl

/-- Contextual Core while success fixes both its AST and final remainder. -/
theorem WhileStatementOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input left afterLeft)
    (rightParsed : WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨WhileStatementOrdinaryParses.value_unique expressionOutcomes
      statementOutcomes leftParsed rightParsed,
    WhileStatementOrdinaryParses.output_unique
      expressionOutcomes.toDeterministicOutcomeSpec
      statementOutcomes.toDeterministicOutcomeSpec leftParsed rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
