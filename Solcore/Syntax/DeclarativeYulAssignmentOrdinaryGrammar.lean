import Solcore.Syntax.DeclarativeYulExpressionFuelGrammar
import Solcore.Syntax.DeclarativeYulNameOutcomeGrammar

/-!
Parser-independent ordinary-success grammar for public inline-Yul assignment.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary assignment success, retaining diagnosed names and ordinary
recursive expression success while preserving forward name order and AST
spans. -/
inductive YulAssignmentOrdinaryParses :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterNames afterOperator output : Remainder}
      {names : YulNamesOrdinaryValue} {value : Syntax.YulExpr}
      (operatorSpan : SourceSpan)
      (namesParsed : YulNamesOrdinaryParses input names afterNames)
      (operatorParsed : ExactTokenParses (.symbol .colonEqual) afterNames
        operatorSpan afterOperator)
      (valueParsed : YulExpressionOrdinaryParses afterOperator value output) :
      YulAssignmentOrdinaryParses input {
        span := SourceSpan.cover names.span value.span
        value := .assign names.names value
      } output

end Solcore.Syntax.DeclarativeGrammar
