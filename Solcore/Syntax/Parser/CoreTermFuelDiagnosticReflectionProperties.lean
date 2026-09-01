import Solcore.Syntax.Parser.CoreExpressionSoundnessProperties
import Solcore.Syntax.Parser.CorePatternSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementLayerDiagnosticReflectionProperties
import Solcore.Syntax.Parser.IsolatedCoreBlockSoundnessProperties
import Solcore.Syntax.Parser.YulBlockDiagnosticReflectionProperties
import Solcore.Syntax.Parser.YulStatementRecursiveDiagnosticReflectionProperties

/-! Diagnostic reflection for mutually recursive and public Core terms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TermInternals

/-- Diagnostic reflection for all three mutually recursive parsers at one
shared fuel. -/
structure CoreTermFuelDiagnosticReflection (fuel : Nat) : Prop where
  expression : Parser.ReflectsDiagnosticFreeOnSuccess
    (coreExpressionWithFuel fuel)
  pattern : Parser.ReflectsDiagnosticFreeOnSuccess
    (corePatternWithFuel fuel)
  statement : Parser.ReflectsDiagnosticFreeOnSuccess
    (coreStatementWithFuel fuel)

private theorem yulBodyReflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulBody := by
  simpa only [yulBody] using
    yulBlock_reflectsDiagnosticFreeOnSuccess yulStatement
      yulStatement_reflectsDiagnosticFreeOnSuccess

/-- Every mutual recursion fuel reflects diagnostic freedom in all three
categories using the same preceding fuel. -/
theorem coreRecursiveWithFuel_reflectsDiagnosticFreeOnSuccess :
    ∀ fuel, CoreTermFuelDiagnosticReflection fuel := by
  intro fuel
  induction fuel with
  | zero =>
      exact {
        expression := by
          intro input value output result diagnosticFree
          simp [coreExpressionWithFuel] at result
        pattern := by
          intro input value output result diagnosticFree
          simp [corePatternWithFuel] at result
        statement := by
          intro input value output result diagnosticFree
          simp [coreStatementWithFuel] at result
      }
  | succ fuel previous =>
      exact {
        expression := by
          simpa only [coreExpressionWithFuel] using
            coreExpressionStep_reflectsDiagnosticFreeOnSuccess
              (coreExpressionWithFuel fuel)
              (isolateBlock
                (coreBlock (coreStatementWithFuel fuel) .require))
              previous.expression
              (isolatedCoreBlock_reflectsDiagnosticFreeOnSuccess
                (coreStatementWithFuel fuel) .require previous.statement)
        pattern := by
          simpa only [corePatternWithFuel] using
            patternLayer_reflectsDiagnosticFreeOnSuccess_of_components
              (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
              previous.pattern previous.expression
        statement := by
          simpa only [coreStatementWithFuel] using
            statementLayer_reflectsDiagnosticFreeOnSuccess
              (coreStatementWithFuel fuel) (coreExpressionWithFuel fuel)
              (corePatternWithFuel fuel) previous.statement
              previous.expression previous.pattern
              yulBodyReflectsDiagnosticFreeOnSuccess
      }

/-- Fuel-bounded Core expressions reflect diagnostic freedom. -/
theorem coreExpressionWithFuel_reflectsDiagnosticFreeOnSuccess (fuel : Nat) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (coreExpressionWithFuel fuel) :=
  (coreRecursiveWithFuel_reflectsDiagnosticFreeOnSuccess fuel).expression

/-- Fuel-bounded Core patterns reflect diagnostic freedom. -/
theorem corePatternWithFuel_reflectsDiagnosticFreeOnSuccess (fuel : Nat) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (corePatternWithFuel fuel) :=
  (coreRecursiveWithFuel_reflectsDiagnosticFreeOnSuccess fuel).pattern

/-- Fuel-bounded Core statements reflect diagnostic freedom. -/
theorem coreStatementWithFuel_reflectsDiagnosticFreeOnSuccess (fuel : Nat) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (coreStatementWithFuel fuel) :=
  (coreRecursiveWithFuel_reflectsDiagnosticFreeOnSuccess fuel).statement

end TermInternals

/-- The public Core expression parser reflects diagnostic freedom. -/
theorem expression_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess expression := by
  intro input value output result diagnosticFree
  unfold expression at result
  exact TermInternals.coreExpressionWithFuel_reflectsDiagnosticFreeOnSuccess
    (input.remainingCount + 1) input value output result diagnosticFree

/-- The public Core pattern parser reflects diagnostic freedom. -/
theorem pattern_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess pattern := by
  intro input value output result diagnosticFree
  unfold pattern at result
  exact TermInternals.corePatternWithFuel_reflectsDiagnosticFreeOnSuccess
    (input.remainingCount + 1) input value output result diagnosticFree

/-- The public Core statement parser reflects diagnostic freedom. -/
theorem statement_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess statement := by
  intro input value output result diagnosticFree
  unfold statement at result
  exact TermInternals.coreStatementWithFuel_reflectsDiagnosticFreeOnSuccess
    (input.remainingCount + 2) input value output result diagnosticFree

/-- A public Core block with either tail policy reflects diagnostic freedom. -/
theorem block_reflectsDiagnosticFreeOnSuccess
    (policy : TailExpressionPolicy) :
    Parser.ReflectsDiagnosticFreeOnSuccess (block policy) := by
  intro input value output result diagnosticFree
  unfold block at result
  exact coreBlock_reflectsDiagnosticFreeOnSuccess
    (TermInternals.coreStatementWithFuel (input.remainingCount + 1)) policy
    (TermInternals.coreStatementWithFuel_reflectsDiagnosticFreeOnSuccess
      (input.remainingCount + 1)) input value output result diagnosticFree

/-- Isolating a public Core block also reflects diagnostic freedom. -/
theorem isolatedPublicCoreBlock_reflectsDiagnosticFreeOnSuccess
    (policy : TailExpressionPolicy) :
    Parser.ReflectsDiagnosticFreeOnSuccess (isolateBlock (block policy)) :=
  isolateBlock_reflectsDiagnosticFreeOnSuccess (block policy)
    (block_reflectsDiagnosticFreeOnSuccess policy)

end Solcore.Syntax.Parser
