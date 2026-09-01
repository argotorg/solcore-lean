import Solcore.Syntax.DeclarativeCoreTermFuelEquationProperties
import Solcore.Syntax.Parser.CoreBlockIsolationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionStepOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreLambdaParameterOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CorePatternStepOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementLayerOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTermFuelOrdinaryOutcomeSoundnessContract
import Solcore.Syntax.Parser.CoreTermFuelOrdinaryShapeProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties

/-! One-step construction of mutual Core fuel outcome reflection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

private theorem isolatedBlockWindow (fuel : Nat) :
    Parser.PreservesTokenWindow
      (isolateBlock (coreBlock (coreStatementWithFuel fuel) .require)) :=
  isolateBlock_preservesTokenWindow
    (coreBlock (coreStatementWithFuel fuel) .require)
    (coreBlock_preservesTokenWindow (coreStatementWithFuel fuel) .require
      (coreStatementWithFuel_ordinary_preservesTokenWindow fuel))

private theorem expressionSuccessorOutcome
    (fuel : Nat) (previous : CoreTermFuelOrdinaryOutcomeSoundness fuel) :
    (∀ {input output : State} {value : Expr},
      coreExpressionWithFuel (fuel + 1) input = .ok value output →
        DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel (fuel + 1)
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      coreExpressionWithFuel (fuel + 1) input = .reject failure rejected →
        DeclarativeGrammar.CoreExpressionRejectsWithFuel (fuel + 1)
          input.declarativeRemainder rejected.declarativeRemainder) := by
  have parameterOutcome := lambdaParameter_ordinaryOutcome_sound
    DeclarativeGrammar.TypeExprOrdinaryParses
    DeclarativeGrammar.TypeExprRejects typeExpr_ordinaryOutcome_sound.1
      typeExpr_ordinaryOutcome_sound.2
  have blockOutcome := isolatedCoreBlock_ordinaryOutcome_sound
    (coreStatementWithFuel fuel) .require
    (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
    (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)
    previous.statement.1 previous.statement.2
  have stepOutcome := coreExpressionStep_ordinaryOutcome_sound
    (coreExpressionWithFuel fuel)
    (isolateBlock (coreBlock (coreStatementWithFuel fuel) .require))
    (DeclarativeGrammar.coreExpressionStepRelationsWithFuel fuel)
    previous.expression.1 previous.expression.2
    (coreExpressionWithFuel_ordinary_preservesTokenWindow fuel)
    parameterOutcome.1 parameterOutcome.2 typeExpr_ordinaryOutcome_sound.1
    typeExpr_ordinaryOutcome_sound.2 blockOutcome.1 blockOutcome.2
    (isolatedBlockWindow fuel)
  constructor
  · intro input output value result
    apply DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel.succ_iff.mpr
    exact stepOutcome.1 (by
      simpa only [coreExpressionWithFuel] using result)
  · intro input rejected failure result
    apply DeclarativeGrammar.CoreExpressionRejectsWithFuel.succ_iff.mpr
    exact stepOutcome.2 (by
      simpa only [coreExpressionWithFuel] using result)

private theorem patternSuccessorOutcome
    (fuel : Nat) (previous : CoreTermFuelOrdinaryOutcomeSoundness fuel) :
    (∀ {input output : State} {value : Pattern},
      corePatternWithFuel (fuel + 1) input = .ok value output →
        DeclarativeGrammar.CorePatternOrdinaryParsesWithFuel (fuel + 1)
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      corePatternWithFuel (fuel + 1) input = .reject failure rejected →
        DeclarativeGrammar.CorePatternRejectsWithFuel (fuel + 1)
          input.declarativeRemainder rejected.declarativeRemainder) := by
  have stepOutcome := corePatternStep_ordinaryOutcome_sound
    (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
    (DeclarativeGrammar.corePatternStepRelationsWithFuel fuel)
    previous.pattern.1 previous.pattern.2
    (corePatternWithFuel_ordinary_preservesTokenWindow fuel)
    previous.expression.1 previous.expression.2
    (coreExpressionWithFuel_ordinary_preservesTokenWindow fuel)
  constructor
  · intro input output value result
    apply DeclarativeGrammar.CorePatternOrdinaryParsesWithFuel.succ_iff.mpr
    exact stepOutcome.1 (by simpa only [corePatternWithFuel] using result)
  · intro input rejected failure result
    apply DeclarativeGrammar.CorePatternRejectsWithFuel.succ_iff.mpr
    exact stepOutcome.2 (by simpa only [corePatternWithFuel] using result)

private theorem statementSuccessorOutcome
    (fuel : Nat) (previous : CoreTermFuelOrdinaryOutcomeSoundness fuel) :
    (∀ {input output : State} {value : Statement},
      coreStatementWithFuel (fuel + 1) input = .ok value output →
        DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel (fuel + 1)
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      coreStatementWithFuel (fuel + 1) input = .reject failure rejected →
        DeclarativeGrammar.CoreStatementRejectsWithFuel (fuel + 1)
          input.declarativeRemainder rejected.declarativeRemainder) := by
  have layerOutcome := statementLayer_ordinaryOutcome_sound
    (coreStatementWithFuel fuel) (coreExpressionWithFuel fuel)
    (corePatternWithFuel fuel)
    (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
    (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)
    (DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel)
    (DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel)
    (DeclarativeGrammar.CorePatternOrdinaryParsesWithFuel fuel)
    (DeclarativeGrammar.CorePatternRejectsWithFuel fuel)
    previous.statement.1 previous.statement.2 previous.expression.1
    previous.expression.2
    (coreExpressionWithFuel_ordinary_preservesTokenWindow fuel)
    (coreExpressionWithFuel_ordinary_cursor_lt_onSuccess fuel)
    previous.pattern.1 previous.pattern.2
  constructor
  · intro input output value result
    apply DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel.succ_iff.mpr
    exact layerOutcome.1 (by simpa only [coreStatementWithFuel] using result)
  · intro input rejected failure result
    apply DeclarativeGrammar.CoreStatementRejectsWithFuel.succ_iff.mpr
    exact layerOutcome.2 (by simpa only [coreStatementWithFuel] using result)

/-- Advance all six executable reflection callbacks from one shared fuel. -/
theorem CoreTermFuelOrdinaryOutcomeSoundness.succ
    {fuel : Nat} (previous : CoreTermFuelOrdinaryOutcomeSoundness fuel) :
    CoreTermFuelOrdinaryOutcomeSoundness (fuel + 1) := {
  expression := expressionSuccessorOutcome fuel previous
  pattern := patternSuccessorOutcome fuel previous
  statement := statementSuccessorOutcome fuel previous
}

end Solcore.Syntax.Parser.TermInternals
