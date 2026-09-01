import Solcore.Syntax.Parser.Statement.MatchStatementFuelTotalityProperties
import Solcore.Syntax.Parser.TermRecursiveProperties

/-! Complete fuel contract for canonical Core `match` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Adequate outer fuel excludes every complete-match invariant. -/
theorem matchStatement_ne_invariant_of_fuels
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    {caseValueValid : SourceFile → MatchCase → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern) (statementFuel expressionFuel caseFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionContract : FuelElementTotalityContract
      expression expressionFuel)
    (caseContract : MatchInternals.FuelCaseListTotalityContract caseValueValid
      (fun input => MatchInternals.matchCases statement pattern
        (input.remainingCount + 1) [] input) caseFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      MatchInternals.matchStatementFuel expressionFuel caseFuel
        statementFuel)
    (error : ParserInvariantError) :
    matchStatement statement expression pattern input ≠ .invariant error := by
  intro failed
  rcases matchStatement_ordinary_of_fuels expressionValueValid
      patternValueValid yulValueValid statement expression pattern
      statementFuel expressionFuel caseFuel statementContract
      statementStrict expressionContract caseContract input inputValid
      adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/--
Package production `match` syntax, including its dynamically fueled case
loop, under the independent expression, pattern, and statement bounds.
-/
theorem matchStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern) (statementFuel expressionFuel patternFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (TermInternals.RecursiveStatementValid statementValid)
      statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality : FuelElementTotalityContract
      expression expressionFuel)
    (patternSyntax :
      TermInternals.PatternParserContract statementValid pattern)
    (patternTotality : FuelElementTotalityContract pattern patternFuel) :
    TermInternals.FuelStatementTotalityContract
      (TermInternals.RecursiveStatementValid statementValid)
      (matchStatement statement expression pattern)
      (MatchInternals.matchStatementFuel expressionFuel
        (Nat.min (patternFuel + 1) (statementFuel + 3))
        statementFuel) := by
  let caseContract :=
    MatchInternals.matchCases_production_fuelTotalityContract
      (Expr.ValidFor statementValid)
      (Pattern.ValidFor (Expr.ValidFor statementValid)) YulStmt.ValidFor
      statement pattern statementFuel patternFuel statementContract
      statementStrict patternSyntax.validFor patternTotality
  exact {
    validFor := matchStatement_validFor (Expr.ValidFor statementValid)
      (Pattern.ValidFor (Expr.ValidFor statementValid)) YulStmt.ValidFor
      statement expression pattern statementContract.validFor
      statementContract.preservesTokenWindow expressionSyntax.validFor
      expressionSyntax.preservesTokensOnSuccess patternSyntax.validFor
      patternSyntax.preservesTokenWindow
      patternSyntax.cursorMonotoneOnSuccess
    preservesTokenWindow := matchStatement_preservesTokenWindow statement
      expression pattern statementContract.preservesTokenWindow
      expressionSyntax.preservesTokenWindow patternSyntax.preservesTokenWindow
    cursorMonotoneOnSuccess :=
      matchStatement_cursorMonotoneOnSuccess statement expression pattern
    startsAtCurrentTokenOnSuccess :=
      matchStatement_startsAtCurrentTokenOnSuccess statement expression pattern
    ordinary := matchStatement_ordinary_of_fuels
      (Expr.ValidFor statementValid)
      (Pattern.ValidFor (Expr.ValidFor statementValid)) YulStmt.ValidFor
      statement expression pattern statementFuel expressionFuel
      (Nat.min (patternFuel + 1) (statementFuel + 3)) statementContract
      statementStrict expressionTotality caseContract
  }

end Solcore.Syntax.Parser
