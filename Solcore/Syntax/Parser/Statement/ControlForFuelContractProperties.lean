import Solcore.Syntax.Parser.Statement.ControlForFuelTotalityProperties

/-! Complete recursive-fuel contract for canonical Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem forStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality :
      FuelElementTotalityContract expression expressionFuel) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      (forStatement statement expression)
      (Nat.min (expressionFuel + 2) (statementFuel + 7)) := by
  let initializerContract :=
    ControlInternals.forItems_fuelTotalityContract expression .semicolon
      expressionFuel expressionSyntax expressionTotality
  let postContract :=
    ControlInternals.forItems_fuelTotalityContract expression .rightParen
      expressionFuel expressionSyntax expressionTotality
  let blockContract := coreBlock_fuelTotalityContract statement .require
    statementFuel statementContract statementStrict
      (fun _ _ valid => valid.span_valid)
  exact {
    validFor := forStatement_validFor (Expr.ValidFor statementValid)
      patternValueValid YulStmt.ValidFor statement expression
        statementContract.validFor statementContract.preservesTokensOnSuccess
        expressionSyntax.validFor (fun _ _ valid => valid.span_valid)
          expressionSyntax.preservesTokenWindow
            expressionSyntax.cursorLtOnSuccess
              expressionSyntax.startsAtCurrentTokenOnSuccess
    preservesTokenWindow := forStatement_preservesTokenWindow statement
      expression statementContract.preservesTokenWindow
        expressionSyntax.preservesTokenWindow
    cursorMonotoneOnSuccess := forStatement_cursorMonotoneOnSuccess statement
      expression expressionSyntax.cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      forStatement_startsAtCurrentTokenOnSuccess statement expression
    ordinary := forStatement_ordinary_of_fuels statement expression
      statementFuel expressionFuel initializerContract postContract
        expressionTotality blockContract
  }

end Solcore.Syntax.Parser
