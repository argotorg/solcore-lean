import Solcore.Syntax.DeclarativeCoreStatementLayerOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.RecognizedCoreStatementFallbackOrdinaryOutcomeSoundnessProperties

/-! Primitive bridges used by the ordered Core statement rejection proof. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

abbrev StatementLayerExecutableOutcomeSound {α : Type} (parser : Parser α)
    (ordinary : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (rejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop) : Prop :=
  (∀ {input output : State} {value : α}, parser input = .ok value output →
    ordinary input.declarativeRemainder value output.declarativeRemainder) ∧
  (∀ {input rejected : State} {failure : Failure},
    parser input = .reject failure rejected →
      rejects input.declarativeRemainder rejected.declarativeRemainder)

theorem statementLayerKeywordTokenAt_of_isKeyword_eq_true
    (value : HardKeyword) {input : State}
    (present : isKeyword input value = true) :
    DeclarativeGrammar.StatementLayerTokenAt input.declarativeRemainder
      (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .statement present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .statement parsed).1⟩

theorem statementLayerContextualTokenAt_of_isContextual_eq_true
    (value : ContextualKeyword) {input : State}
    (present : isContextual input value = true) :
    DeclarativeGrammar.StatementLayerTokenAt input.declarativeRemainder
      (.identifier value.spelling) := by
  rcases contextual_eq_ok_of_isContextual_eq_true value .statement present
    with ⟨token, parsed⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses value .statement parsed).1⟩

theorem statementLayerSymbolTokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    DeclarativeGrammar.StatementLayerTokenAt input.declarativeRemainder
      (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .statement present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .statement parsed).1⟩

theorem statementLayerSelectedGuarded_reject
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects expressionRejects patternRejects :
      DeclarativeGrammar.Remainder → DeclarativeGrammar.Remainder → Prop}
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    (stage : DeclarativeGrammar.StatementLayerStage)
    (notFallback : stage ≠ .fallback)
    {input rejected : State} {failure : Failure}
    (priority : DeclarativeGrammar.StatementLayerPrefixAbsent
      input.declarativeRemainder stage)
    (guard : DeclarativeGrammar.StatementLayerGuardAt
      input.declarativeRemainder stage)
    (primary fallback : Parser Statement)
    (primarySound : StatementLayerExecutableOutcomeSound primary
      (DeclarativeGrammar.StatementLayerPrimaryOrdinaryParses
        statementOrdinary expressionOrdinary patternOrdinary stage)
      (DeclarativeGrammar.StatementLayerPrimaryRejects statementOrdinary
        statementRejects expressionOrdinary expressionRejects patternOrdinary
          patternRejects stage))
    (fallbackSound : StatementLayerExecutableOutcomeSound fallback
      (DeclarativeGrammar.AssignmentOrExpressionStatementOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.AssignmentOrExpressionStatementRejects
        expressionOrdinary expressionRejects))
    (result : recognizedStatementOrFallback primary fallback input =
      .reject failure rejected) :
    DeclarativeGrammar.StatementLayerRejects statementOrdinary
      statementRejects expressionOrdinary expressionRejects patternOrdinary
        patternRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  refine ⟨stage, .guarded notFallback priority guard ?_⟩
  exact (recognizedStatementOrFallback_ordinaryOutcome_sound primary fallback
    (DeclarativeGrammar.StatementLayerPrimaryOrdinaryParses
      statementOrdinary expressionOrdinary patternOrdinary stage)
    (DeclarativeGrammar.AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary)
    (DeclarativeGrammar.StatementLayerPrimaryRejects statementOrdinary
      statementRejects expressionOrdinary expressionRejects patternOrdinary
        patternRejects stage)
    (DeclarativeGrammar.AssignmentOrExpressionStatementRejects
      expressionOrdinary expressionRejects)
    primarySound.1 primarySound.2 fallbackSound.1 fallbackSound.2).2 result

end Solcore.Syntax.Parser.TermInternals
