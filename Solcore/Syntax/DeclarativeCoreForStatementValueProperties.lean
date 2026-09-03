import Solcore.Syntax.DeclarativeCoreBlockExactnessProperties
import Solcore.Syntax.DeclarativeCoreForItemsValueProperties
import Solcore.Syntax.DeclarativeCoreForStatementOutcomeProperties

/-! Exact success values for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact child statements and expressions fix a complete for statement,
including retained header delimiters, forward item order, and body spans. -/
theorem ForStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input left afterLeft)
    (rightParsed : ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftFirstSemicolonSpan
        leftSecondSemicolonSpan leftClosingSpan leftMarker leftOpening
        leftInitializer leftFirstSemicolon leftCondition leftSecondSemicolon
        leftPost leftClosing leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightFirstSemicolonSpan
            rightSecondSemicolonSpan rightClosingSpan rightMarker rightOpening
            rightInitializer rightFirstSemicolon rightCondition
            rightSecondSemicolon rightPost rightClosing rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          rcases leftOpening.result_unique rightOpening with
            ⟨openingEq, inputEq⟩
          subst openingEq
          subst inputEq
          rcases ForItemsOrdinaryParses.result_unique expressionOutcomes
              .semicolon leftInitializer rightInitializer with
            ⟨initializerEq, inputEq⟩
          subst initializerEq
          subst inputEq
          have inputEq := leftFirstSemicolon.output_unique rightFirstSemicolon
          subst inputEq
          rcases expressionOutcomes.successResultUnique leftCondition
              rightCondition with ⟨conditionEq, inputEq⟩
          subst conditionEq
          subst inputEq
          have inputEq := leftSecondSemicolon.output_unique rightSecondSemicolon
          subst inputEq
          rcases ForItemsOrdinaryParses.result_unique expressionOutcomes
              .rightParen leftPost rightPost with ⟨postEq, inputEq⟩
          subst postEq
          subst inputEq
          rcases leftClosing.result_unique rightClosing with
            ⟨closingEq, inputEq⟩
          subst closingEq
          subst inputEq
          have bodyEq := leftBody.value_unique statementOutcomes rightBody
          subst bodyEq
          rfl

/-- A successful complete Core for statement fixes its AST and remainder. -/
theorem ForStatementOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input left afterLeft)
    (rightParsed : ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨ForStatementOrdinaryParses.value_unique statementOutcomes expressionOutcomes
      leftParsed rightParsed,
    ForStatementOrdinaryParses.output_unique
      statementOutcomes.toDeterministicOutcomeSpec
      expressionOutcomes.toDeterministicOutcomeSpec leftParsed rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
