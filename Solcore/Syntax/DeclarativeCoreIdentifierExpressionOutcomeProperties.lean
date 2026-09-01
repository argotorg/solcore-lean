import Solcore.Syntax.DeclarativeCoreExpressionNameOutcomeProperties
import Solcore.Syntax.DeclarativeCoreIdentifierExpressionOutcomeGrammar

/-! Deterministic ordinary outcomes for a Core identifier expression. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Identifier-expression output is the unique output of its name. -/
theorem IdentifierExpressionOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : IdentifierExpressionOrdinaryParses input left afterLeft)
    (rightParsed : IdentifierExpressionOrdinaryParses input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftName =>
      cases rightParsed with
      | parsed rightName =>
          exact ExpressionNameOrdinaryParses.output_unique leftName rightName

/-- Rejected expression names exclude identifier-expression success. -/
theorem IdentifierExpressionRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : IdentifierExpressionRejects input rejected) :
    ¬ ∃ expression output,
      IdentifierExpressionOrdinaryParses input expression output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | nameRejected nameRejected =>
      cases successful with
      | parsed nameParsed =>
          exact nameRejected.disjointOrdinary ⟨_, _, nameParsed⟩

/-- Identifier-expression leaves have deterministic ordinary outcomes. -/
theorem identifierExpressionDeterministicOutcomeSpec :
    DeterministicOutcomeSpec IdentifierExpressionOrdinaryParses
      IdentifierExpressionRejects where
  successOutputUnique := IdentifierExpressionOrdinaryParses.output_unique
  successRejectDisjoint := IdentifierExpressionRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
