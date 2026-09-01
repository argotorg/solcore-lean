import Solcore.Syntax.DeclarativeCoreTermLevelOutcomeProperties
import Solcore.Syntax.Parser.Term

/-! Executable reflection contracts for one mutual Core recursion fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Success and exact rejection reflection for all three mutually recursive
Core parsers at one shared fuel. -/
structure CoreTermFuelOrdinaryOutcomeSoundness (fuel : Nat) : Prop where
  expression :
    (∀ {input output : State} {value : Expr},
      coreExpressionWithFuel fuel input = .ok value output →
        DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      coreExpressionWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder)
  pattern :
    (∀ {input output : State} {value : Pattern},
      corePatternWithFuel fuel input = .ok value output →
        DeclarativeGrammar.CorePatternOrdinaryParsesWithFuel fuel
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      corePatternWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.CorePatternRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder)
  statement :
    (∀ {input output : State} {value : Statement},
      coreStatementWithFuel fuel input = .ok value output →
        DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      coreStatementWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.CoreStatementRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder)

end Solcore.Syntax.Parser.TermInternals
