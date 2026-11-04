import Solcore.Syntax.DeclarativeCoreBlockOutcomeProperties
import Solcore.Syntax.DeclarativeCoreBlockIsolationOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionStepOutcomeProperties
import Solcore.Syntax.DeclarativeCoreLambdaParameterPublicOutcomeProperties
import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternStepOutcomeProperties
import Solcore.Syntax.Grammar.StatementLayer

/-!
Fuel levels of the mutually recursive Core terms, and the public term grammar.

Each level is built from the relations one fuel below, as the executable recursion is.
Main declarations: `CoreTermLevel`, `CoreExpressionOrdinaryParses`,
`CorePatternOrdinaryParses`,
`CoreStatementOrdinaryParses`, `CoreBlockPublicOrdinaryParses`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionLevelOutcomeProperties
/-! Reusable declarative levels for recursive Core expression outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One complete ordinary/rejection approximation of recursive expressions. -/
structure CoreExpressionLevel where
  ordinaryParses : Remainder → Syntax.Expr → Remainder → Prop
  rejects : Remainder → Remainder → Prop
  outcomes : DeterministicOutcomeSpec ordinaryParses rejects

namespace CoreExpressionLevel

/-- Fuel zero recognizes no expression success or rejection outcome. -/
def empty : CoreExpressionLevel where
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

/-- Relations supplied to one expression step by the preceding expression
level, fixed public type and lambda-parameter outcomes, and one statement
outcome for isolated required-tail blocks. -/
def stepRelations (previous : CoreExpressionLevel)
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    CoreExpressionStepRelations where
  nestedOrdinary := previous.ordinaryParses
  nestedRejects := previous.rejects
  parameterOrdinary := LambdaParameterOrdinaryParses
    TypeExprOrdinaryParses TypeExprRejects
  parameterRejects := LambdaParameterRejects TypeExprRejects
  typeOrdinary := TypeExprOrdinaryParses
  typeRejects := TypeExprRejects
  blockOrdinary := IsolatedCoreBlockOrdinaryParses
    (CoreBlockOrdinaryParses statementOrdinary .require)
    (CoreBlockRejects statementOrdinary statementRejects .require)
  blockRejects := IsolatedCoreBlockRejects
    (CoreBlockRejects statementOrdinary statementRejects .require)

/-- Add one public recursive expression layer using one supplied statement
outcome for isolated required-tail blocks at this recursion depth. -/
def next (previous : CoreExpressionLevel)
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) : CoreExpressionLevel where
  ordinaryParses := CoreExpressionStepOrdinaryParses
    (previous.stepRelations statementOrdinary statementRejects)
  rejects := CoreExpressionStepRejects
    (previous.stepRelations statementOrdinary statementRejects)
  outcomes := coreExpressionStepDeterministicOutcomeSpec
    (previous.stepRelations statementOrdinary statementRejects)
      previous.outcomes
      (lambdaParameterDeterministicOutcomeSpec
        typeExprDeterministicOutcomeSpec)
      typeExprDeterministicOutcomeSpec
      (isolatedCoreBlockDeterministicOutcomeSpec
        (coreBlockDeterministicOutcomeSpec .require statementOutcomes))

end CoreExpressionLevel

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternLevelOutcomeProperties
/-! Reusable declarative levels for recursive Core pattern outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One complete ordinary/rejection approximation of recursive patterns. -/
structure CorePatternLevel where
  ordinaryParses : Remainder → Syntax.Pattern → Remainder → Prop
  rejects : Remainder → Remainder → Prop
  outcomes : DeterministicOutcomeSpec ordinaryParses rejects

namespace CorePatternLevel

/-- Fuel zero recognizes no pattern success or rejection outcome. -/
def empty : CorePatternLevel where
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

/-- Relations supplied to one pattern step by the previous pattern level and
one expression outcome. -/
def stepRelations (previous : CorePatternLevel)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :
    CorePatternStepRelations where
  nestedOrdinary := previous.ordinaryParses
  nestedRejects := previous.rejects
  expressionOrdinary := expressionOrdinary
  expressionRejects := expressionRejects

/-- Add one public recursive pattern layer using one supplied expression
outcome at the preceding recursion depth. -/
def next (previous : CorePatternLevel)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) : CorePatternLevel where
  ordinaryParses := CorePatternStepOrdinaryParses
    (previous.stepRelations expressionOrdinary expressionRejects)
  rejects := CorePatternStepRejects
    (previous.stepRelations expressionOrdinary expressionRejects)
  outcomes := corePatternStepDeterministicOutcomeSpec
    (previous.stepRelations expressionOrdinary expressionRejects)
      previous.outcomes expressionOutcomes

end CorePatternLevel

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTermLevelOutcomeProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTermFuelEquationProperties
/-! Equations for the parser-independent mutually recursive Core fuel levels. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

@[simp] theorem CoreExpressionOrdinaryParsesWithFuel.zero
    {input output : Remainder} {expression : Syntax.Expr} :
    ¬ CoreExpressionOrdinaryParsesWithFuel 0 input expression output := by
  simp [CoreExpressionOrdinaryParsesWithFuel, CoreTermLevel.empty,
    CoreExpressionLevel.empty]

@[simp] theorem CoreExpressionRejectsWithFuel.zero
    {input rejected : Remainder} :
    ¬ CoreExpressionRejectsWithFuel 0 input rejected := by
  simp [CoreExpressionRejectsWithFuel, CoreTermLevel.empty,
    CoreExpressionLevel.empty]

@[simp] theorem CorePatternOrdinaryParsesWithFuel.zero
    {input output : Remainder} {pattern : Syntax.Pattern} :
    ¬ CorePatternOrdinaryParsesWithFuel 0 input pattern output := by
  simp [CorePatternOrdinaryParsesWithFuel, CoreTermLevel.empty,
    CorePatternLevel.empty]

@[simp] theorem CorePatternRejectsWithFuel.zero
    {input rejected : Remainder} :
    ¬ CorePatternRejectsWithFuel 0 input rejected := by
  simp [CorePatternRejectsWithFuel, CoreTermLevel.empty,
    CorePatternLevel.empty]

@[simp] theorem CoreStatementOrdinaryParsesWithFuel.zero
    {input output : Remainder} {statement : Syntax.Statement} :
    ¬ CoreStatementOrdinaryParsesWithFuel 0 input statement output := by
  simp [CoreStatementOrdinaryParsesWithFuel, CoreTermLevel.empty,
    CoreStatementLevel.empty]

@[simp] theorem CoreStatementRejectsWithFuel.zero
    {input rejected : Remainder} :
    ¬ CoreStatementRejectsWithFuel 0 input rejected := by
  simp [CoreStatementRejectsWithFuel, CoreTermLevel.empty,
    CoreStatementLevel.empty]

@[simp] theorem CoreExpressionOrdinaryParsesWithFuel.succ_iff
    {fuel : Nat} {input output : Remainder} {expression : Syntax.Expr} :
    CoreExpressionOrdinaryParsesWithFuel (fuel + 1) input expression output ↔
      CoreExpressionStepOrdinaryParses
        (coreExpressionStepRelationsWithFuel fuel) input expression output := by
  simp only [CoreExpressionOrdinaryParsesWithFuel,
    CoreStatementOrdinaryParsesWithFuel, CoreStatementRejectsWithFuel,
    coreExpressionStepRelationsWithFuel, CoreTermLevel.atFuel,
    CoreTermLevel.next, CoreExpressionLevel.next]

@[simp] theorem CoreExpressionRejectsWithFuel.succ_iff
    {fuel : Nat} {input rejected : Remainder} :
    CoreExpressionRejectsWithFuel (fuel + 1) input rejected ↔
      CoreExpressionStepRejects
        (coreExpressionStepRelationsWithFuel fuel) input rejected := by
  simp only [CoreExpressionRejectsWithFuel,
    CoreStatementOrdinaryParsesWithFuel, CoreStatementRejectsWithFuel,
    coreExpressionStepRelationsWithFuel, CoreTermLevel.atFuel,
    CoreTermLevel.next, CoreExpressionLevel.next]

@[simp] theorem CorePatternOrdinaryParsesWithFuel.succ_iff
    {fuel : Nat} {input output : Remainder} {pattern : Syntax.Pattern} :
    CorePatternOrdinaryParsesWithFuel (fuel + 1) input pattern output ↔
      CorePatternStepOrdinaryParses
        (corePatternStepRelationsWithFuel fuel) input pattern output := by
  simp only [CorePatternOrdinaryParsesWithFuel,
    CoreExpressionOrdinaryParsesWithFuel, CoreExpressionRejectsWithFuel,
    corePatternStepRelationsWithFuel, CoreTermLevel.atFuel,
    CoreTermLevel.next, CorePatternLevel.next]

@[simp] theorem CorePatternRejectsWithFuel.succ_iff
    {fuel : Nat} {input rejected : Remainder} :
    CorePatternRejectsWithFuel (fuel + 1) input rejected ↔
      CorePatternStepRejects
        (corePatternStepRelationsWithFuel fuel) input rejected := by
  simp only [CorePatternRejectsWithFuel,
    CoreExpressionOrdinaryParsesWithFuel, CoreExpressionRejectsWithFuel,
    corePatternStepRelationsWithFuel, CoreTermLevel.atFuel,
    CoreTermLevel.next, CorePatternLevel.next]

@[simp] theorem CoreStatementOrdinaryParsesWithFuel.succ_iff
    {fuel : Nat} {input output : Remainder} {statement : Syntax.Statement} :
    CoreStatementOrdinaryParsesWithFuel (fuel + 1) input statement output ↔
      StatementLayerOrdinaryParses
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel)
        (CorePatternOrdinaryParsesWithFuel fuel)
        (CorePatternRejectsWithFuel fuel) input statement output := by
  simp only [CoreStatementOrdinaryParsesWithFuel,
    CoreStatementRejectsWithFuel, CoreExpressionOrdinaryParsesWithFuel,
    CoreExpressionRejectsWithFuel, CorePatternOrdinaryParsesWithFuel,
    CorePatternRejectsWithFuel, CoreTermLevel.atFuel, CoreTermLevel.next,
    CoreStatementLevel.next]

@[simp] theorem CoreStatementRejectsWithFuel.succ_iff
    {fuel : Nat} {input rejected : Remainder} :
    CoreStatementRejectsWithFuel (fuel + 1) input rejected ↔
      StatementLayerRejects
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel)
        (CorePatternOrdinaryParsesWithFuel fuel)
        (CorePatternRejectsWithFuel fuel) input rejected := by
  simp only [CoreStatementOrdinaryParsesWithFuel,
    CoreStatementRejectsWithFuel, CoreExpressionOrdinaryParsesWithFuel,
    CoreExpressionRejectsWithFuel, CorePatternOrdinaryParsesWithFuel,
    CorePatternRejectsWithFuel, CoreTermLevel.atFuel, CoreTermLevel.next,
    CoreStatementLevel.next]

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTermPublicOutcomeProperties
/-! Declarative public-fuel outcomes for mutually recursive Core terms. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Fuel selected for a public Core expression from its input remainder. -/
def coreExpressionPublicFuel (input : Remainder) : Nat :=
  input.endIndex - input.cursor + 1

/-- Fuel selected for a public Core pattern from its input remainder. -/
def corePatternPublicFuel (input : Remainder) : Nat :=
  input.endIndex - input.cursor + 1

/-- Fuel selected for a public Core statement from its input remainder. -/
def coreStatementPublicFuel (input : Remainder) : Nat :=
  input.endIndex - input.cursor + 2

/-- Fixed statement fuel selected once at a public Core-block boundary. -/
def coreBlockPublicStatementFuel (input : Remainder) : Nat :=
  input.endIndex - input.cursor + 1

/-- Ordinary Core-expression success at the exact public fuel. -/
def CoreExpressionOrdinaryParses (input : Remainder)
    (expression : Syntax.Expr) (output : Remainder) : Prop :=
  CoreExpressionOrdinaryParsesWithFuel (coreExpressionPublicFuel input)
    input expression output

/-- Exact Core-expression rejection at the public fuel. -/
def CoreExpressionPublicRejects (input rejected : Remainder) : Prop :=
  CoreExpressionRejectsWithFuel (coreExpressionPublicFuel input) input
    rejected

/-- Ordinary Core-pattern success at the exact public fuel. -/
def CorePatternOrdinaryParses (input : Remainder)
    (pattern : Syntax.Pattern) (output : Remainder) : Prop :=
  CorePatternOrdinaryParsesWithFuel (corePatternPublicFuel input) input
    pattern output

/-- Exact Core-pattern rejection at the public fuel. -/
def CorePatternPublicRejects (input rejected : Remainder) : Prop :=
  CorePatternRejectsWithFuel (corePatternPublicFuel input) input rejected

/-- Ordinary Core-statement success at the exact public fuel. -/
def CoreStatementOrdinaryParses (input : Remainder)
    (statement : Syntax.Statement) (output : Remainder) : Prop :=
  CoreStatementOrdinaryParsesWithFuel (coreStatementPublicFuel input) input
    statement output

/-- Exact Core-statement rejection at the public fuel. -/
def CoreStatementPublicRejects (input rejected : Remainder) : Prop :=
  CoreStatementRejectsWithFuel (coreStatementPublicFuel input) input rejected

/-- Ordinary public Core-block success with one fixed recursive statement
fuel and a declarative tail policy. -/
def CoreBlockPublicOrdinaryParses (policy : CoreBlockTailPolicy)
    (input : Remainder) (block : Syntax.Block) (output : Remainder) : Prop :=
  CoreBlockOrdinaryParses
    (CoreStatementOrdinaryParsesWithFuel
      (coreBlockPublicStatementFuel input)) policy input block output

/-- Exact public Core-block rejection with the same fixed statement fuel. -/
def CoreBlockPublicRejects (policy : CoreBlockTailPolicy)
    (input rejected : Remainder) : Prop :=
  CoreBlockRejects
    (CoreStatementOrdinaryParsesWithFuel
      (coreBlockPublicStatementFuel input))
    (CoreStatementRejectsWithFuel
      (coreBlockPublicStatementFuel input)) policy input rejected

/-- Deterministic ordinary outcomes of public Core expressions. -/
theorem coreExpressionPublicOutcomeSpec :
    DeterministicOutcomeSpec CoreExpressionOrdinaryParses
      CoreExpressionPublicRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (coreExpressionOutcomeSpecWithFuel
      (coreExpressionPublicFuel input)).successOutputUnique leftParsed
        rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    exact (coreExpressionOutcomeSpecWithFuel
      (coreExpressionPublicFuel input)).successRejectDisjoint rejection

/-- Deterministic ordinary outcomes of public Core patterns. -/
theorem corePatternPublicOutcomeSpec :
    DeterministicOutcomeSpec CorePatternOrdinaryParses
      CorePatternPublicRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (corePatternOutcomeSpecWithFuel
      (corePatternPublicFuel input)).successOutputUnique leftParsed rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    exact (corePatternOutcomeSpecWithFuel
      (corePatternPublicFuel input)).successRejectDisjoint rejection

/-- Deterministic ordinary outcomes of public Core statements. -/
theorem coreStatementPublicOutcomeSpec :
    DeterministicOutcomeSpec CoreStatementOrdinaryParses
      CoreStatementPublicRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (coreStatementOutcomeSpecWithFuel
      (coreStatementPublicFuel input)).successOutputUnique leftParsed
        rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    exact (coreStatementOutcomeSpecWithFuel
      (coreStatementPublicFuel input)).successRejectDisjoint rejection

/-- Deterministic ordinary outcomes of public Core blocks under either
declarative tail policy. -/
theorem coreBlockPublicOutcomeSpec (policy : CoreBlockTailPolicy) :
    DeterministicOutcomeSpec (CoreBlockPublicOrdinaryParses policy)
      (CoreBlockPublicRejects policy) where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (coreBlockDeterministicOutcomeSpec policy
      (coreStatementOutcomeSpecWithFuel
        (coreBlockPublicStatementFuel input))).successOutputUnique leftParsed
          rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    exact (coreBlockDeterministicOutcomeSpec policy
      (coreStatementOutcomeSpecWithFuel
        (coreBlockPublicStatementFuel input))).successRejectDisjoint rejection

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreBlockPublicIsolationOutcomeProperties
/-! Public ordinary outcomes for isolated Core blocks. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary isolated-block success over the public raw-block outcomes. -/
abbrev IsolatedCoreBlockPublicOrdinaryParses
    (policy : CoreBlockTailPolicy) :=
  IsolatedCoreBlockOrdinaryParses
    (CoreBlockPublicOrdinaryParses policy)
    (CoreBlockPublicRejects policy)

/-- Exact external rejection of a public isolated block. -/
abbrev IsolatedCoreBlockPublicRejects (policy : CoreBlockTailPolicy) :=
  IsolatedCoreBlockRejects (CoreBlockPublicRejects policy)

/-- Deterministic ordinary outcomes of public block isolation. -/
theorem isolatedCoreBlockPublicOutcomeSpec (policy : CoreBlockTailPolicy) :
    DeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses policy)
      (IsolatedCoreBlockPublicRejects policy) :=
  isolatedCoreBlockDeterministicOutcomeSpec
    (coreBlockPublicOutcomeSpec policy)

end Solcore.Syntax.DeclarativeGrammar
end
