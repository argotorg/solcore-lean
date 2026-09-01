import Solcore.Syntax.DeclarativeCoreStatementLayerOutcomeProperties
import Solcore.Syntax.Parser.CoreAssignmentStatementOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.RecognizedCoreStatementFallbackOrdinaryOutcomeSoundnessProperties

/-! Shared guarded-success machinery for the Core statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals.StatementLayerSuccessInternals

theorem keyword_guard_of_true (value : HardKeyword) {input : State}
    (present : isKeyword input value = true) :
    DeclarativeGrammar.StatementLayerTokenAt input.declarativeRemainder
      (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .statement present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .statement result).1⟩

theorem contextual_guard_of_true (value : ContextualKeyword)
    {input : State} (present : isContextual input value = true) :
    DeclarativeGrammar.StatementLayerTokenAt input.declarativeRemainder
      (.identifier value.spelling) := by
  rcases contextual_eq_ok_of_isContextual_eq_true value .statement present with
    ⟨token, result⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses value .statement result).1⟩

theorem symbol_guard_of_true (value : Symbol) {input : State}
    (present : isSymbol input value = true) :
    DeclarativeGrammar.StatementLayerTokenAt input.declarativeRemainder
      (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .statement present with
    ⟨token, result⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .statement result).1⟩

theorem selected_guarded_success
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expression : Parser Expr)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (stage : DeclarativeGrammar.StatementLayerStage)
    (notFallback : stage ≠ .fallback)
    {input output : State} {value : Statement}
    (priority : DeclarativeGrammar.StatementLayerPrefixAbsent
      input.declarativeRemainder stage)
    (guard : DeclarativeGrammar.StatementLayerGuardAt
      input.declarativeRemainder stage)
    (primary : Parser Statement)
    (primaryOutcome :
      (∀ {branchInput branchOutput : State} {branchValue : Statement},
        primary branchInput = .ok branchValue branchOutput →
          DeclarativeGrammar.StatementLayerPrimaryOrdinaryParses
            statementOrdinary expressionOrdinary patternOrdinary stage
              branchInput.declarativeRemainder branchValue
                branchOutput.declarativeRemainder) ∧
      (∀ {branchInput branchRejected : State} {failure : Failure},
        primary branchInput = .reject failure branchRejected →
          DeclarativeGrammar.StatementLayerPrimaryRejects statementOrdinary
            statementRejects expressionOrdinary expressionRejects
              patternOrdinary patternRejects stage
                branchInput.declarativeRemainder
                  branchRejected.declarativeRemainder))
    (result : recognizedStatementOrFallback primary
      (assignmentOrExpressionStatement expression) input = .ok value output) :
    DeclarativeGrammar.StatementLayerOrdinaryParses statementOrdinary
      statementRejects expressionOrdinary expressionRejects patternOrdinary
        patternRejects input.declarativeRemainder value
          output.declarativeRemainder := by
  have fallbackSuccess : ∀ {fallbackInput fallbackOutput : State}
      {fallbackValue : Statement},
      assignmentOrExpressionStatement expression fallbackInput =
          .ok fallbackValue fallbackOutput →
        DeclarativeGrammar.AssignmentOrExpressionStatementOrdinaryParses
          expressionOrdinary fallbackInput.declarativeRemainder fallbackValue
            fallbackOutput.declarativeRemainder :=
    assignmentOrExpressionStatement_success_ordinary_sound expression
      expressionOrdinary expressionSuccessSound
  have fallbackReject : ∀ {fallbackInput fallbackRejected : State}
      {failure : Failure},
      assignmentOrExpressionStatement expression fallbackInput =
          .reject failure fallbackRejected →
        DeclarativeGrammar.AssignmentOrExpressionStatementRejects
          expressionOrdinary expressionRejects
            fallbackInput.declarativeRemainder
              fallbackRejected.declarativeRemainder :=
    assignmentOrExpressionStatement_reject_ordinary_sound expression
      expressionOrdinary expressionRejects expressionSuccessSound
        expressionRejectSound
  exact ⟨stage, .guarded notFallback priority guard
    ((recognizedStatementOrFallback_ordinaryOutcome_sound primary
      (assignmentOrExpressionStatement expression)
      (DeclarativeGrammar.StatementLayerPrimaryOrdinaryParses
        statementOrdinary expressionOrdinary patternOrdinary stage)
      (DeclarativeGrammar.AssignmentOrExpressionStatementOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.StatementLayerPrimaryRejects statementOrdinary
        statementRejects expressionOrdinary expressionRejects patternOrdinary
          patternRejects stage)
      (DeclarativeGrammar.AssignmentOrExpressionStatementRejects
        expressionOrdinary expressionRejects) primaryOutcome.1
          primaryOutcome.2 fallbackSuccess fallbackReject).1 result)⟩

end Solcore.Syntax.Parser.TermInternals.StatementLayerSuccessInternals
