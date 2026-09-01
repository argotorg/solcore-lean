import Solcore.Syntax.DeclarativeCoreBlockOutcomeProperties
import Solcore.Syntax.DeclarativeCoreTermLevelOutcomeProperties

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
