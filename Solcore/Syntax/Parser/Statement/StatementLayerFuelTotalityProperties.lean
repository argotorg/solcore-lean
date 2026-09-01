import Solcore.Syntax.Parser.Statement.AssemblyTotalityProperties
import Solcore.Syntax.Parser.Statement.ChoiceFuelTotalityProperties
import Solcore.Syntax.Parser.Statement.ControlBlockFuelTotalityProperties
import Solcore.Syntax.Parser.Statement.ControlForFuelContractProperties
import Solcore.Syntax.Parser.Statement.ControlIfFuelTotalityProperties
import Solcore.Syntax.Parser.Statement.ControlLeafTotalityProperties
import Solcore.Syntax.Parser.Statement.MatchStatementFuelContractProperties
import Solcore.Syntax.Parser.Statement.SimpleBranchFuelTotalityProperties

/-! Fuel totality for the complete ordered Core statement dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/--
The fallback, complete `match`, and recursive block are the three tight
constraints on the ordered statement layer. All other branches support this
common smaller bound.
-/
def statementLayerFuel
    (statementFuel expressionFuel patternFuel : Nat) : Nat :=
  Nat.min expressionFuel
    (Nat.min
      (MatchInternals.matchStatementFuel expressionFuel
        (Nat.min (patternFuel + 1) (statementFuel + 3)) statementFuel)
      (statementFuel + 1))

private theorem recognized_sameFuel_contract
    {valueValid : SourceFile → Statement → Prop}
    (primary fallback : Parser Statement) (fuel : Nat)
    (primaryContract : FuelStatementTotalityContract
      valueValid primary fuel)
    (fallbackContract : FuelStatementTotalityContract
      valueValid fallback fuel) :
    FuelStatementTotalityContract valueValid
      (recognizedStatementOrFallback primary fallback) fuel := by
  simpa using recognizedStatementOrFallback_fuelTotalityContract
    primary fallback fuel fuel primaryContract fallbackContract

private theorem stateChoice_sameFuel_contract
    {valueValid : SourceFile → Statement → Prop}
    (condition : State → Bool) (first second : Parser Statement) (fuel : Nat)
    (firstContract : FuelStatementTotalityContract valueValid first fuel)
    (secondContract : FuelStatementTotalityContract valueValid second fuel) :
    FuelStatementTotalityContract valueValid
      (fun input => if condition input then first input else second input)
      fuel := by
  simpa using stateChoice_fuelTotalityContract condition first second fuel fuel
    firstContract secondContract

/-- Every branch of `statementLayer` is ordinary at one reusable fuel bound. -/
theorem statementLayer_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementFuel expressionFuel patternFuel : Nat)
    (statementContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      nestedStatement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      nestedStatement input = .ok value next → input.cursor < next.cursor)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality :
      FuelElementTotalityContract expression expressionFuel)
    (patternSyntax : PatternParserContract statementValid pattern)
    (patternTotality : FuelElementTotalityContract pattern patternFuel) :
    FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (statementLayer nestedStatement expression pattern)
      (statementLayerFuel statementFuel expressionFuel patternFuel) := by
  let patternValid := Pattern.ValidFor (Expr.ValidFor statementValid)
  let commonFuel := statementLayerFuel statementFuel expressionFuel patternFuel
  let matchFuel := MatchInternals.matchStatementFuel expressionFuel
    (Nat.min (patternFuel + 1) (statementFuel + 3)) statementFuel
  have commonLeExpression : commonFuel ≤ expressionFuel := by
    dsimp only [commonFuel]
    exact Nat.min_le_left _ _
  have commonLeMatch : commonFuel ≤ matchFuel := by
    dsimp only [commonFuel, matchFuel]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
  have commonLeStatement : commonFuel ≤ statementFuel + 1 := by
    dsimp only [commonFuel]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
  have commonLeControl :
      commonFuel ≤ Nat.min (expressionFuel + 2) (statementFuel + 5) := by
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  have commonLeFor :
      commonFuel ≤ Nat.min (expressionFuel + 2) (statementFuel + 7) := by
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  have fallbackContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (assignmentOrExpressionStatement expression) commonFuel :=
    (assignmentOrExpressionStatement_fuelTotalityContract patternValid
      YulStmt.ValidFor expression expressionFuel expressionSyntax
      expressionTotality).weaken commonLeExpression
  have letContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (letStatement expression) commonFuel :=
    (letStatement_fuelTotalityContract patternValid expression expressionFuel
      expressionSyntax expressionTotality).weaken (by omega)
  have returnContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (returnStatement expression) commonFuel :=
    (returnStatement_fuelTotalityContract patternValid expression
      expressionFuel expressionSyntax expressionTotality).weaken (by omega)
  have matchContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (matchStatement nestedStatement expression pattern) commonFuel :=
    (matchStatement_fuelTotalityContract nestedStatement expression pattern
      statementFuel expressionFuel patternFuel statementContract
      statementStrict expressionSyntax expressionTotality patternSyntax
      patternTotality).weaken commonLeMatch
  have forContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (forStatement nestedStatement expression) commonFuel :=
    (forStatement_fuelTotalityContract patternValid nestedStatement expression
      statementFuel expressionFuel statementContract statementStrict
      expressionSyntax expressionTotality).weaken commonLeFor
  have whileContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (whileStatement nestedStatement expression) commonFuel :=
    (whileStatement_fuelTotalityContract patternValid nestedStatement
      expression statementFuel expressionFuel statementContract
      statementStrict expressionSyntax expressionTotality).weaken
        commonLeControl
  have ifContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (ifStatement nestedStatement expression) commonFuel :=
    (ifStatement_fuelTotalityContract patternValid nestedStatement expression
      statementFuel expressionFuel statementContract statementStrict
      expressionSyntax expressionTotality).weaken commonLeControl
  have assemblyContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid) assemblyStatement commonFuel :=
    assemblyStatement_fuelTotalityContract (Expr.ValidFor statementValid)
      patternValid YulStmt.ValidFor (fun _ _ valid => valid) commonFuel
  have blockContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid)
      (blockStatement nestedStatement) commonFuel :=
    (blockStatement_fuelTotalityContract patternValid nestedStatement
      statementFuel statementContract statementStrict).weaken
        commonLeStatement
  have breakContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid) breakStatement commonFuel :=
    FuelStatementTotalityContract.ofTotality
      (breakStatement_totalityContract (Expr.ValidFor statementValid)
        patternValid YulStmt.ValidFor) commonFuel
  have continueContract : FuelStatementTotalityContract
      (RecursiveStatementValid statementValid) continueStatement commonFuel :=
    FuelStatementTotalityContract.ofTotality
      (continueStatement_totalityContract (Expr.ValidFor statementValid)
        patternValid YulStmt.ValidFor) commonFuel
  change FuelStatementTotalityContract
    (RecursiveStatementValid statementValid)
    (statementLayer nestedStatement expression pattern) commonFuel
  unfold statementLayer
  apply stateChoice_sameFuel_contract
  · exact recognized_sameFuel_contract _ _ commonFuel letContract
      fallbackContract
  · apply stateChoice_sameFuel_contract
    · exact recognized_sameFuel_contract _ _ commonFuel returnContract
        fallbackContract
    · apply stateChoice_sameFuel_contract
      · exact recognized_sameFuel_contract _ _ commonFuel matchContract
          fallbackContract
      · apply stateChoice_sameFuel_contract
        · exact recognized_sameFuel_contract _ _ commonFuel forContract
            fallbackContract
        · apply stateChoice_sameFuel_contract
          · exact recognized_sameFuel_contract _ _ commonFuel whileContract
              fallbackContract
          · apply stateChoice_sameFuel_contract
            · exact recognized_sameFuel_contract _ _ commonFuel ifContract
                fallbackContract
            · apply stateChoice_sameFuel_contract
              · exact recognized_sameFuel_contract _ _ commonFuel
                  assemblyContract fallbackContract
              · apply stateChoice_sameFuel_contract
                · exact recognized_sameFuel_contract _ _ commonFuel
                    blockContract fallbackContract
                · apply stateChoice_sameFuel_contract
                  · exact recognized_sameFuel_contract _ _ commonFuel
                      breakContract fallbackContract
                  · apply stateChoice_sameFuel_contract
                    · exact recognized_sameFuel_contract _ _ commonFuel
                        continueContract fallbackContract
                    · exact fallbackContract

end Solcore.Syntax.Parser.TermInternals
