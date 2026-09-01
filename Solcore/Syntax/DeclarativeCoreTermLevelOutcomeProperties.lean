import Solcore.Syntax.DeclarativeCoreExpressionLevelOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternLevelOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementLayerOutcomeProperties

/-!
Parser-independent fuel levels for mutually recursive Core terms.

Each successor level is built solely from the three relations at the preceding
fuel, matching the executable expression, pattern, and statement recursion.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One complete ordinary/rejection approximation of recursive statements. -/
structure CoreStatementLevel where
  ordinaryParses : Remainder → Syntax.Statement → Remainder → Prop
  rejects : Remainder → Remainder → Prop
  outcomes : DeterministicOutcomeSpec ordinaryParses rejects

namespace CoreStatementLevel

/-- Fuel zero recognizes no statement success or rejection outcome. -/
def empty : CoreStatementLevel where
  ordinaryParses := fun _ _ _ => False
  rejects := fun _ _ => False
  outcomes := {
    successOutputUnique := by
      intro input left right afterLeft afterRight leftParsed
      exact False.elim leftParsed
    successRejectDisjoint := by
      intro input rejected rejection
      exact False.elim rejection
  }

/-- Add one concrete prioritized statement-dispatch layer using the expression,
pattern, and recursive-statement outcomes at the preceding fuel. -/
def next (previous : CoreStatementLevel)
    (expression : CoreExpressionLevel) (pattern : CorePatternLevel) :
    CoreStatementLevel where
  ordinaryParses := StatementLayerOrdinaryParses previous.ordinaryParses
    previous.rejects expression.ordinaryParses expression.rejects
      pattern.ordinaryParses pattern.rejects
  rejects := StatementLayerRejects previous.ordinaryParses previous.rejects
    expression.ordinaryParses expression.rejects pattern.ordinaryParses
      pattern.rejects
  outcomes := statementLayerDeterministicOutcomeSpec previous.outcomes
    expression.outcomes pattern.outcomes

end CoreStatementLevel

/-- Same-fuel ordinary/rejection approximations of all three mutually recursive
Core term categories. -/
structure CoreTermLevel where
  expression : CoreExpressionLevel
  pattern : CorePatternLevel
  statement : CoreStatementLevel

namespace CoreTermLevel

/-- Fuel zero recognizes no Core term success or rejection outcome. -/
def empty : CoreTermLevel where
  expression := .empty
  pattern := .empty
  statement := .empty

/-- Advance all three Core term categories from the same preceding fuel. -/
def next (previous : CoreTermLevel) : CoreTermLevel where
  expression := previous.expression.next previous.statement.ordinaryParses
    previous.statement.rejects previous.statement.outcomes
  pattern := previous.pattern.next previous.expression.ordinaryParses
    previous.expression.rejects previous.expression.outcomes
  statement := previous.statement.next previous.expression previous.pattern

/-- Declarative mutually recursive Core outcomes at exactly `fuel`. -/
def atFuel : Nat → CoreTermLevel
  | 0 => .empty
  | fuel + 1 => (atFuel fuel).next

@[simp] theorem atFuel_zero : atFuel 0 = .empty := rfl

@[simp] theorem atFuel_succ (fuel : Nat) :
    atFuel (fuel + 1) = (atFuel fuel).next := rfl

end CoreTermLevel

/-- Ordinary recursive Core-expression successes at one fuel. -/
def CoreExpressionOrdinaryParsesWithFuel (fuel : Nat) :
    Remainder → Syntax.Expr → Remainder → Prop :=
  (CoreTermLevel.atFuel fuel).expression.ordinaryParses

/-- Exact recursive Core-expression rejection at one fuel. -/
def CoreExpressionRejectsWithFuel (fuel : Nat) :
    Remainder → Remainder → Prop :=
  (CoreTermLevel.atFuel fuel).expression.rejects

/-- Ordinary recursive Core-pattern successes at one fuel. -/
def CorePatternOrdinaryParsesWithFuel (fuel : Nat) :
    Remainder → Syntax.Pattern → Remainder → Prop :=
  (CoreTermLevel.atFuel fuel).pattern.ordinaryParses

/-- Exact recursive Core-pattern rejection at one fuel. -/
def CorePatternRejectsWithFuel (fuel : Nat) :
    Remainder → Remainder → Prop :=
  (CoreTermLevel.atFuel fuel).pattern.rejects

/-- Ordinary recursive Core-statement successes at one fuel. -/
def CoreStatementOrdinaryParsesWithFuel (fuel : Nat) :
    Remainder → Syntax.Statement → Remainder → Prop :=
  (CoreTermLevel.atFuel fuel).statement.ordinaryParses

/-- Exact recursive Core-statement rejection at one fuel. -/
def CoreStatementRejectsWithFuel (fuel : Nat) :
    Remainder → Remainder → Prop :=
  (CoreTermLevel.atFuel fuel).statement.rejects

/-- Concrete relations supplied to the expression parser one fuel later. -/
def coreExpressionStepRelationsWithFuel (fuel : Nat) :
    CoreExpressionStepRelations :=
  (CoreTermLevel.atFuel fuel).expression.stepRelations
    (CoreStatementOrdinaryParsesWithFuel fuel)
    (CoreStatementRejectsWithFuel fuel)

/-- Concrete relations supplied to the pattern parser one fuel later. -/
def corePatternStepRelationsWithFuel (fuel : Nat) :
    CorePatternStepRelations :=
  (CoreTermLevel.atFuel fuel).pattern.stepRelations
    (CoreExpressionOrdinaryParsesWithFuel fuel)
    (CoreExpressionRejectsWithFuel fuel)

/-- Deterministic Core-expression outcomes at one mutual-recursion fuel. -/
theorem coreExpressionOutcomeSpecWithFuel (fuel : Nat) :
    DeterministicOutcomeSpec
      (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel) :=
  (CoreTermLevel.atFuel fuel).expression.outcomes

/-- Deterministic Core-pattern outcomes at one mutual-recursion fuel. -/
theorem corePatternOutcomeSpecWithFuel (fuel : Nat) :
    DeterministicOutcomeSpec
      (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel) :=
  (CoreTermLevel.atFuel fuel).pattern.outcomes

/-- Deterministic Core-statement outcomes at one mutual-recursion fuel. -/
theorem coreStatementOutcomeSpecWithFuel (fuel : Nat) :
    DeterministicOutcomeSpec
      (CoreStatementOrdinaryParsesWithFuel fuel)
      (CoreStatementRejectsWithFuel fuel) :=
  (CoreTermLevel.atFuel fuel).statement.outcomes

end Solcore.Syntax.DeclarativeGrammar
