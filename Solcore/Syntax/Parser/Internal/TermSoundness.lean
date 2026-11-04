import Solcore.Syntax.Grammar.TermLevels
import Solcore.Syntax.Parser.Internal.BlockSoundness
import Solcore.Syntax.Parser.Internal.ExpressionAtomSoundness
import Solcore.Syntax.Parser.Internal.SignatureSoundness
import Solcore.Syntax.Parser.Internal.PatternStepSoundness
import Solcore.Syntax.Parser.Internal.ForStatementSoundness
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Syntax.Internal.StatementValues
import Solcore.Syntax.Internal.BlockExactness
import Solcore.Syntax.Parser.Internal.PatternCoreSoundness
import Solcore.Syntax.Parser.Internal.YulBlockSoundness
import Solcore.Syntax.Parser.Internal.YulSwitchSoundness
import Solcore.Syntax.Parser.Internal.StatementTotality
import Solcore.Syntax.Parser.OrdinaryOutcomeCompletenessProperties
import Solcore.Syntax.Parser.Internal.PublicTermTotality

/-!
Soundness of the parsers of terms at fuel and public blocks: each success and each
rejection has its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTermFuelOrdinarySuccessorSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTermFuelOrdinaryOutcomeSoundnessProperties
/-! Same-fuel ordinary outcome reflection for all recursive Core terms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

private theorem coreTermFuel_zero_ordinaryOutcome_sound :
    CoreTermFuelOrdinaryOutcomeSoundness 0 := {
  expression := by
    constructor
    · intro input output value result
      simp [coreExpressionWithFuel] at result
    · intro input rejected failure result
      simp [coreExpressionWithFuel] at result
  pattern := by
    constructor
    · intro input output value result
      simp [corePatternWithFuel] at result
    · intro input rejected failure result
      simp [corePatternWithFuel] at result
  statement := by
    constructor
    · intro input output value result
      simp [coreStatementWithFuel] at result
    · intro input rejected failure result
      simp [coreStatementWithFuel] at result
}

/-- All six executable Core outcomes reflect the parser-independent relations
at the same mutual-recursion fuel. -/
theorem coreRecursiveWithFuel_ordinaryOutcome_sound : ∀ fuel,
    CoreTermFuelOrdinaryOutcomeSoundness fuel := by
  intro fuel
  induction fuel with
  | zero => exact coreTermFuel_zero_ordinaryOutcome_sound
  | succ fuel inductionHypothesis =>
      simpa only [Nat.succ_eq_add_one] using inductionHypothesis.succ

/-- Package executable expression success and rejection at explicit fuel. -/
theorem coreExpressionWithFuel_ordinaryOutcome_sound (fuel : Nat) :
    (∀ {input output : State} {value : Expr},
      coreExpressionWithFuel fuel input = .ok value output →
        DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      coreExpressionWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder) :=
  (coreRecursiveWithFuel_ordinaryOutcome_sound fuel).expression

/-- Package executable pattern success and rejection at explicit fuel. -/
theorem corePatternWithFuel_ordinaryOutcome_sound (fuel : Nat) :
    (∀ {input output : State} {value : Pattern},
      corePatternWithFuel fuel input = .ok value output →
        DeclarativeGrammar.CorePatternOrdinaryParsesWithFuel fuel
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      corePatternWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.CorePatternRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder) :=
  (coreRecursiveWithFuel_ordinaryOutcome_sound fuel).pattern

/-- Package executable statement success and rejection at explicit fuel. -/
theorem coreStatementWithFuel_ordinaryOutcome_sound (fuel : Nat) :
    (∀ {input output : State} {value : Statement},
      coreStatementWithFuel fuel input = .ok value output →
        DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      coreStatementWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.CoreStatementRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder) :=
  (coreRecursiveWithFuel_ordinaryOutcome_sound fuel).statement

/-- Project ordinary expression success at explicit fuel. -/
theorem coreExpressionWithFuel_success_ordinary_sound (fuel : Nat)
    {input output : State} {value : Expr}
    (result : coreExpressionWithFuel fuel input = .ok value output) :
    DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel
      input.declarativeRemainder value output.declarativeRemainder :=
  (coreExpressionWithFuel_ordinaryOutcome_sound fuel).1 result

/-- Project exact expression rejection at explicit fuel. -/
theorem coreExpressionWithFuel_reject_ordinary_sound (fuel : Nat)
    {input rejected : State} {failure : Failure}
    (result : coreExpressionWithFuel fuel input = .reject failure rejected) :
    DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel
      input.declarativeRemainder rejected.declarativeRemainder :=
  (coreExpressionWithFuel_ordinaryOutcome_sound fuel).2 result

/-- Project ordinary pattern success at explicit fuel. -/
theorem corePatternWithFuel_success_ordinary_sound (fuel : Nat)
    {input output : State} {value : Pattern}
    (result : corePatternWithFuel fuel input = .ok value output) :
    DeclarativeGrammar.CorePatternOrdinaryParsesWithFuel fuel
      input.declarativeRemainder value output.declarativeRemainder :=
  (corePatternWithFuel_ordinaryOutcome_sound fuel).1 result

/-- Project exact pattern rejection at explicit fuel. -/
theorem corePatternWithFuel_reject_ordinary_sound (fuel : Nat)
    {input rejected : State} {failure : Failure}
    (result : corePatternWithFuel fuel input = .reject failure rejected) :
    DeclarativeGrammar.CorePatternRejectsWithFuel fuel
      input.declarativeRemainder rejected.declarativeRemainder :=
  (corePatternWithFuel_ordinaryOutcome_sound fuel).2 result

/-- Project ordinary statement success at explicit fuel. -/
theorem coreStatementWithFuel_success_ordinary_sound (fuel : Nat)
    {input output : State} {value : Statement}
    (result : coreStatementWithFuel fuel input = .ok value output) :
    DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel
      input.declarativeRemainder value output.declarativeRemainder :=
  (coreStatementWithFuel_ordinaryOutcome_sound fuel).1 result

/-- Project exact statement rejection at explicit fuel. -/
theorem coreStatementWithFuel_reject_ordinary_sound (fuel : Nat)
    {input rejected : State} {failure : Failure}
    (result : coreStatementWithFuel fuel input = .reject failure rejected) :
    DeclarativeGrammar.CoreStatementRejectsWithFuel fuel
      input.declarativeRemainder rejected.declarativeRemainder :=
  (coreStatementWithFuel_ordinaryOutcome_sound fuel).2 result

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTermFuelExactnessProperties
/-! Exact executable Core outcomes at an explicitly shared recursion fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- The declarative expression outcome is exact at every fixed fuel. -/
theorem coreExpressionWithFuel_exactOutcomeSpec (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel)
      (DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel) :=
  DeclarativeGrammar.coreExpressionExactOutcomeSpecWithFuel fuel

/-- Fixed-fuel expression successes agree on the complete AST and remainder. -/
theorem coreExpressionWithFuel_success_result_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {left right : Expr}
    (leftResult : coreExpressionWithFuel fuel input = .ok left leftOutput)
    (rightResult : coreExpressionWithFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (coreExpressionWithFuel_exactOutcomeSpec fuel).successResultUnique
    (coreExpressionWithFuel_success_ordinary_sound fuel leftResult)
    (coreExpressionWithFuel_success_ordinary_sound fuel rightResult)

/-- Fixed-fuel expression rejections agree on the complete remainder. -/
theorem coreExpressionWithFuel_reject_output_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : coreExpressionWithFuel fuel input = .reject leftFailure leftOutput)
    (rightResult : coreExpressionWithFuel fuel input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (coreExpressionWithFuel_exactOutcomeSpec fuel).rejectOutputUnique
    (coreExpressionWithFuel_reject_ordinary_sound fuel leftResult)
    (coreExpressionWithFuel_reject_ordinary_sound fuel rightResult)

/-- The declarative pattern outcome is exact at every fixed fuel. -/
theorem corePatternWithFuel_exactOutcomeSpec (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.CorePatternOrdinaryParsesWithFuel fuel)
      (DeclarativeGrammar.CorePatternRejectsWithFuel fuel) :=
  DeclarativeGrammar.corePatternExactOutcomeSpecWithFuel fuel

/-- Fixed-fuel pattern successes agree on the complete AST and remainder. -/
theorem corePatternWithFuel_success_result_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {left right : Pattern}
    (leftResult : corePatternWithFuel fuel input = .ok left leftOutput)
    (rightResult : corePatternWithFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (corePatternWithFuel_exactOutcomeSpec fuel).successResultUnique
    (corePatternWithFuel_success_ordinary_sound fuel leftResult)
    (corePatternWithFuel_success_ordinary_sound fuel rightResult)

/-- Fixed-fuel pattern rejections agree on the complete remainder. -/
theorem corePatternWithFuel_reject_output_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : corePatternWithFuel fuel input = .reject leftFailure leftOutput)
    (rightResult : corePatternWithFuel fuel input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (corePatternWithFuel_exactOutcomeSpec fuel).rejectOutputUnique
    (corePatternWithFuel_reject_ordinary_sound fuel leftResult)
    (corePatternWithFuel_reject_ordinary_sound fuel rightResult)

/-- The declarative statement outcome is exact at every fixed fuel. -/
theorem coreStatementWithFuel_exactOutcomeSpec (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
      (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel) :=
  DeclarativeGrammar.coreStatementExactOutcomeSpecWithFuel fuel

/-- Fixed-fuel statement successes agree on the complete AST and remainder. -/
theorem coreStatementWithFuel_success_result_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {left right : Statement}
    (leftResult : coreStatementWithFuel fuel input = .ok left leftOutput)
    (rightResult : coreStatementWithFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (coreStatementWithFuel_exactOutcomeSpec fuel).successResultUnique
    (coreStatementWithFuel_success_ordinary_sound fuel leftResult)
    (coreStatementWithFuel_success_ordinary_sound fuel rightResult)

/-- Fixed-fuel statement rejections agree on the complete remainder. -/
theorem coreStatementWithFuel_reject_output_unique (fuel : Nat)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : coreStatementWithFuel fuel input = .reject leftFailure leftOutput)
    (rightResult : coreStatementWithFuel fuel input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (coreStatementWithFuel_exactOutcomeSpec fuel).rejectOutputUnique
    (coreStatementWithFuel_reject_ordinary_sound fuel leftResult)
    (coreStatementWithFuel_reject_ordinary_sound fuel rightResult)

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTermPublicOrdinaryOutcomeSoundnessProperties
/-! Ordinary outcome reflection for the public Core term parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The executable expression fuel equals the public declarative fuel. -/
@[simp] theorem coreExpression_executableFuel_eq_publicFuel (input : State) :
    input.remainingCount + 1 =
      DeclarativeGrammar.coreExpressionPublicFuel
        input.declarativeRemainder := by
  rfl

/-- The executable pattern fuel equals the public declarative fuel. -/
@[simp] theorem corePattern_executableFuel_eq_publicFuel (input : State) :
    input.remainingCount + 1 =
      DeclarativeGrammar.corePatternPublicFuel input.declarativeRemainder := by
  rfl

/-- The executable statement fuel equals the public declarative fuel. -/
@[simp] theorem coreStatement_executableFuel_eq_publicFuel (input : State) :
    input.remainingCount + 2 =
      DeclarativeGrammar.coreStatementPublicFuel
        input.declarativeRemainder := by
  rfl

/-- The executable block's fixed statement fuel equals its public fuel. -/
@[simp] theorem coreBlock_executableFuel_eq_publicFuel (input : State) :
    input.remainingCount + 1 =
      DeclarativeGrammar.coreBlockPublicStatementFuel
        input.declarativeRemainder := by
  rfl

/-- Every public Core-expression success follows its ordinary public relation. -/
theorem expression_success_ordinary_sound
    {input output : State} {value : Expr}
    (result : expression input = .ok value output) :
    DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold expression at result
  unfold DeclarativeGrammar.CoreExpressionOrdinaryParses
  rw [← coreExpression_executableFuel_eq_publicFuel input]
  exact TermInternals.coreExpressionWithFuel_success_ordinary_sound
    (input.remainingCount + 1) result

/-- Every public Core-expression rejection follows its exact public relation. -/
theorem expression_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : expression input = .reject failure rejected) :
    DeclarativeGrammar.CoreExpressionPublicRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold expression at result
  unfold DeclarativeGrammar.CoreExpressionPublicRejects
  rw [← coreExpression_executableFuel_eq_publicFuel input]
  exact TermInternals.coreExpressionWithFuel_reject_ordinary_sound
    (input.remainingCount + 1) result

/-- Package both public Core-expression outcomes. -/
theorem expression_ordinaryOutcome_sound :
    (∀ {input output : State} {value : Expr},
      expression input = .ok value output →
        DeclarativeGrammar.CoreExpressionOrdinaryParses
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected →
        DeclarativeGrammar.CoreExpressionPublicRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨expression_success_ordinary_sound, expression_reject_ordinary_sound⟩

/-- Every public Core-pattern success follows its ordinary public relation. -/
theorem pattern_success_ordinary_sound
    {input output : State} {value : Pattern}
    (result : pattern input = .ok value output) :
    DeclarativeGrammar.CorePatternOrdinaryParses input.declarativeRemainder
      value output.declarativeRemainder := by
  unfold pattern at result
  unfold DeclarativeGrammar.CorePatternOrdinaryParses
  rw [← corePattern_executableFuel_eq_publicFuel input]
  exact TermInternals.corePatternWithFuel_success_ordinary_sound
    (input.remainingCount + 1) result

/-- Every public Core-pattern rejection follows its exact public relation. -/
theorem pattern_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : pattern input = .reject failure rejected) :
    DeclarativeGrammar.CorePatternPublicRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold pattern at result
  unfold DeclarativeGrammar.CorePatternPublicRejects
  rw [← corePattern_executableFuel_eq_publicFuel input]
  exact TermInternals.corePatternWithFuel_reject_ordinary_sound
    (input.remainingCount + 1) result

/-- Package both public Core-pattern outcomes. -/
theorem pattern_ordinaryOutcome_sound :
    (∀ {input output : State} {value : Pattern},
      pattern input = .ok value output →
        DeclarativeGrammar.CorePatternOrdinaryParses input.declarativeRemainder
          value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected →
        DeclarativeGrammar.CorePatternPublicRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨pattern_success_ordinary_sound, pattern_reject_ordinary_sound⟩

/-- Every public Core-statement success follows its ordinary public relation. -/
theorem statement_success_ordinary_sound
    {input output : State} {value : Statement}
    (result : statement input = .ok value output) :
    DeclarativeGrammar.CoreStatementOrdinaryParses input.declarativeRemainder
      value output.declarativeRemainder := by
  unfold statement at result
  unfold DeclarativeGrammar.CoreStatementOrdinaryParses
  rw [← coreStatement_executableFuel_eq_publicFuel input]
  exact TermInternals.coreStatementWithFuel_success_ordinary_sound
    (input.remainingCount + 2) result

/-- Every public Core-statement rejection follows its exact public relation. -/
theorem statement_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : statement input = .reject failure rejected) :
    DeclarativeGrammar.CoreStatementPublicRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold statement at result
  unfold DeclarativeGrammar.CoreStatementPublicRejects
  rw [← coreStatement_executableFuel_eq_publicFuel input]
  exact TermInternals.coreStatementWithFuel_reject_ordinary_sound
    (input.remainingCount + 2) result

/-- Package both public Core-statement outcomes. -/
theorem statement_ordinaryOutcome_sound :
    (∀ {input output : State} {value : Statement},
      statement input = .ok value output →
        DeclarativeGrammar.CoreStatementOrdinaryParses
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        DeclarativeGrammar.CoreStatementPublicRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨statement_success_ordinary_sound, statement_reject_ordinary_sound⟩

/-- Every public Core-block success uses the statement fuel fixed at its
outer input and the parser policy's declarative counterpart. -/
theorem block_success_ordinary_sound (policy : TailExpressionPolicy)
    {input output : State} {value : Block}
    (result : block policy input = .ok value output) :
    DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold block at result
  unfold DeclarativeGrammar.CoreBlockPublicOrdinaryParses
  rw [← coreBlock_executableFuel_eq_publicFuel input]
  exact (coreBlock_ordinaryOutcome_sound
    (TermInternals.coreStatementWithFuel (input.remainingCount + 1)) policy
    (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel
      (input.remainingCount + 1))
    (DeclarativeGrammar.CoreStatementRejectsWithFuel
      (input.remainingCount + 1))
    (TermInternals.coreStatementWithFuel_success_ordinary_sound
      (input.remainingCount + 1))
    (TermInternals.coreStatementWithFuel_reject_ordinary_sound
      (input.remainingCount + 1))).1 result

/-- Every public Core-block rejection uses the same outer-input statement
fuel and the parser policy's declarative counterpart. -/
theorem block_reject_ordinary_sound (policy : TailExpressionPolicy)
    {input rejected : State} {failure : Failure}
    (result : block policy input = .reject failure rejected) :
    DeclarativeGrammar.CoreBlockPublicRejects policy.declarative
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold block at result
  unfold DeclarativeGrammar.CoreBlockPublicRejects
  rw [← coreBlock_executableFuel_eq_publicFuel input]
  exact (coreBlock_ordinaryOutcome_sound
    (TermInternals.coreStatementWithFuel (input.remainingCount + 1)) policy
    (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel
      (input.remainingCount + 1))
    (DeclarativeGrammar.CoreStatementRejectsWithFuel
      (input.remainingCount + 1))
    (TermInternals.coreStatementWithFuel_success_ordinary_sound
      (input.remainingCount + 1))
    (TermInternals.coreStatementWithFuel_reject_ordinary_sound
      (input.remainingCount + 1))).2 result

/-- Package both public Core-block outcomes under an explicit parser policy. -/
theorem block_ordinaryOutcome_sound (policy : TailExpressionPolicy) :
    (∀ {input output : State} {value : Block},
      block policy input = .ok value output →
        DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      block policy input = .reject failure rejected →
        DeclarativeGrammar.CoreBlockPublicRejects policy.declarative
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨block_success_ordinary_sound policy, block_reject_ordinary_sound policy⟩

/-- Re-export public raw-block exactness from exact fixed-fuel statement
outcomes. -/
theorem block_exactOutcomeSpec_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    (policy : TailExpressionPolicy) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative)
      (DeclarativeGrammar.CoreBlockPublicRejects policy.declarative) :=
  DeclarativeGrammar.coreBlockPublicExactOutcomeSpecOfStatementFuel
    statementOutcomes policy.declarative

/-- Under exact fixed-fuel statements, two successful public raw blocks have
the same AST and final declarative remainder. -/
theorem block_success_result_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State} {left right : Block}
    (leftResult : block policy input = .ok left leftOutput)
    (rightResult : block policy input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (block_exactOutcomeSpec_of_statementFuel statementOutcomes policy)
    |>.successResultUnique (block_success_ordinary_sound policy leftResult)
      (block_success_ordinary_sound policy rightResult)

/-- Under exact fixed-fuel statements, two public raw-block rejections have
the same declarative endpoint. -/
theorem block_reject_output_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : block policy input = .reject leftFailure leftOutput)
    (rightResult : block policy input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (block_exactOutcomeSpec_of_statementFuel statementOutcomes policy)
    |>.rejectOutputUnique (block_reject_ordinary_sound policy leftResult)
      (block_reject_ordinary_sound policy rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTermPublicExactnessProperties
/-! Unconditional exact executable outcomes for public Core terms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public expression exactness needs no recursive outcome assumptions. -/
theorem expression_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.CoreExpressionOrdinaryParses
      DeclarativeGrammar.CoreExpressionPublicRejects :=
  DeclarativeGrammar.coreExpressionPublicExactOutcomeSpec

/-- Public expression successes agree on the complete AST and remainder. -/
theorem expression_success_result_unique
    {input leftOutput rightOutput : State} {left right : Expr}
    (leftResult : expression input = .ok left leftOutput)
    (rightResult : expression input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  expression_exactOutcomeSpec.successResultUnique
    (expression_success_ordinary_sound leftResult)
    (expression_success_ordinary_sound rightResult)

/-- Public expression rejections agree on the complete declarative endpoint. -/
theorem expression_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : expression input = .reject leftFailure leftOutput)
    (rightResult : expression input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  expression_exactOutcomeSpec.rejectOutputUnique
    (expression_reject_ordinary_sound leftResult)
    (expression_reject_ordinary_sound rightResult)

/-- Public pattern exactness needs no recursive outcome assumptions. -/
theorem pattern_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.CorePatternOrdinaryParses
      DeclarativeGrammar.CorePatternPublicRejects :=
  DeclarativeGrammar.corePatternPublicExactOutcomeSpec

/-- Public pattern successes agree on the complete AST and remainder. -/
theorem pattern_success_result_unique
    {input leftOutput rightOutput : State} {left right : Pattern}
    (leftResult : pattern input = .ok left leftOutput)
    (rightResult : pattern input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  pattern_exactOutcomeSpec.successResultUnique
    (pattern_success_ordinary_sound leftResult)
    (pattern_success_ordinary_sound rightResult)

/-- Public pattern rejections agree on the complete declarative endpoint. -/
theorem pattern_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : pattern input = .reject leftFailure leftOutput)
    (rightResult : pattern input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  pattern_exactOutcomeSpec.rejectOutputUnique
    (pattern_reject_ordinary_sound leftResult)
    (pattern_reject_ordinary_sound rightResult)

/-- Public statement exactness needs no recursive outcome assumptions. -/
theorem statement_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.CoreStatementOrdinaryParses
      DeclarativeGrammar.CoreStatementPublicRejects :=
  DeclarativeGrammar.coreStatementPublicExactOutcomeSpec

/-- Public statement successes agree on the complete AST and remainder. -/
theorem statement_success_result_unique
    {input leftOutput rightOutput : State} {left right : Statement}
    (leftResult : statement input = .ok left leftOutput)
    (rightResult : statement input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  statement_exactOutcomeSpec.successResultUnique
    (statement_success_ordinary_sound leftResult)
    (statement_success_ordinary_sound rightResult)

/-- Public statement rejections agree on the complete declarative endpoint. -/
theorem statement_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : statement input = .reject leftFailure leftOutput)
    (rightResult : statement input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  statement_exactOutcomeSpec.rejectOutputUnique
    (statement_reject_ordinary_sound leftResult)
    (statement_reject_ordinary_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockPublicIsolationOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for public Core block isolation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package public isolated-block success and exact external rejection. -/
theorem isolatedCoreBlockPublic_ordinaryOutcome_sound
    (policy : TailExpressionPolicy) :
    (∀ {input output : State} {body : Block},
      isolateBlock (block policy) input = .ok body output →
        DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses
          policy.declarative input.declarativeRemainder body
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isolateBlock (block policy) input = .reject failure rejected →
        DeclarativeGrammar.IsolatedCoreBlockPublicRejects policy.declarative
          input.declarativeRemainder rejected.declarativeRemainder) :=
  isolateBlock_ordinaryOutcome_sound (block policy)
    (DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative)
    (DeclarativeGrammar.CoreBlockPublicRejects policy.declarative)
    (block_ordinaryOutcome_sound policy).1
    (block_ordinaryOutcome_sound policy).2

/-- Every public isolated-block success follows the capture-aware ordinary
relation. -/
theorem isolatedCoreBlockPublic_success_ordinary_sound
    (policy : TailExpressionPolicy) {input output : State} {body : Block}
    (result : isolateBlock (block policy) input = .ok body output) :
    DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses
      policy.declarative input.declarativeRemainder body
        output.declarativeRemainder :=
  (isolatedCoreBlockPublic_ordinaryOutcome_sound policy).1 result

/-- Every public isolated-block rejection is the exact uncaptured raw-block
rejection. -/
theorem isolatedCoreBlockPublic_reject_ordinary_sound
    (policy : TailExpressionPolicy) {input rejected : State}
    {failure : Failure}
    (result : isolateBlock (block policy) input = .reject failure rejected) :
    DeclarativeGrammar.IsolatedCoreBlockPublicRejects policy.declarative
      input.declarativeRemainder rejected.declarativeRemainder :=
  (isolatedCoreBlockPublic_ordinaryOutcome_sound policy).2 result

/-- Re-export exact public isolation from exact fixed-fuel statement
outcomes. -/
theorem isolatedCoreBlockPublic_exactOutcomeSpec_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    (policy : TailExpressionPolicy) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses
        policy.declarative)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects
        policy.declarative) :=
  DeclarativeGrammar.isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel
    statementOutcomes policy.declarative

/-- Under exact fixed-fuel statements, two isolated public successes have the
same block AST and final declarative remainder. -/
theorem isolatedCoreBlockPublic_success_result_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State} {left right : Block}
    (leftResult : isolateBlock (block policy) input = .ok left leftOutput)
    (rightResult : isolateBlock (block policy) input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (isolatedCoreBlockPublic_exactOutcomeSpec_of_statementFuel
      statementOutcomes policy)
    |>.successResultUnique
      (isolatedCoreBlockPublic_success_ordinary_sound policy leftResult)
      (isolatedCoreBlockPublic_success_ordinary_sound policy rightResult)

/-- Under exact fixed-fuel statements, two isolated public rejections have the
same declarative endpoint. -/
theorem isolatedCoreBlockPublic_reject_output_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : isolateBlock (block policy) input =
      .reject leftFailure leftOutput)
    (rightResult : isolateBlock (block policy) input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (isolatedCoreBlockPublic_exactOutcomeSpec_of_statementFuel
      statementOutcomes policy)
    |>.rejectOutputUnique
      (isolatedCoreBlockPublic_reject_ordinary_sound policy leftResult)
      (isolatedCoreBlockPublic_reject_ordinary_sound policy rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockPublicExactnessProperties
/-! Exact public raw and isolated blocks under both tail-expression policies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public raw block exactness no longer assumes statement exactness. -/
theorem block_exactOutcomeSpec (policy : TailExpressionPolicy) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative)
      (DeclarativeGrammar.CoreBlockPublicRejects policy.declarative) :=
  block_exactOutcomeSpec_of_statementFuel
    DeclarativeGrammar.coreStatementExactOutcomeSpecWithFuel policy

/-- Public raw block successes agree on their full AST and remainder. -/
theorem block_success_result_unique (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State} {left right : Block}
    (leftResult : block policy input = .ok left leftOutput)
    (rightResult : block policy input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (block_exactOutcomeSpec policy).successResultUnique
    (block_success_ordinary_sound policy leftResult)
    (block_success_ordinary_sound policy rightResult)

/-- Public raw block rejections agree on their complete endpoint. -/
theorem block_reject_output_unique (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : block policy input = .reject leftFailure leftOutput)
    (rightResult : block policy input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (block_exactOutcomeSpec policy).rejectOutputUnique
    (block_reject_ordinary_sound policy leftResult)
    (block_reject_ordinary_sound policy rightResult)

/-- Public isolated block exactness no longer assumes statement exactness. -/
theorem isolatedCoreBlockPublic_exactOutcomeSpec (policy : TailExpressionPolicy) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses policy.declarative)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects policy.declarative) :=
  isolatedCoreBlockPublic_exactOutcomeSpec_of_statementFuel
    DeclarativeGrammar.coreStatementExactOutcomeSpecWithFuel policy

/-- Public isolated block successes agree on their full AST and remainder. -/
theorem isolatedCoreBlockPublic_success_result_unique (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State} {left right : Block}
    (leftResult : isolateBlock (block policy) input = .ok left leftOutput)
    (rightResult : isolateBlock (block policy) input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (isolatedCoreBlockPublic_exactOutcomeSpec policy).successResultUnique
    (isolatedCoreBlockPublic_success_ordinary_sound policy leftResult)
    (isolatedCoreBlockPublic_success_ordinary_sound policy rightResult)

/-- Public isolated block rejections agree on their complete endpoint. -/
theorem isolatedCoreBlockPublic_reject_output_unique (policy : TailExpressionPolicy)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : isolateBlock (block policy) input = .reject leftFailure leftOutput)
    (rightResult : isolateBlock (block policy) input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (isolatedCoreBlockPublic_exactOutcomeSpec policy).rejectOutputUnique
    (isolatedCoreBlockPublic_reject_ordinary_sound policy leftResult)
    (isolatedCoreBlockPublic_reject_ordinary_sound policy rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTermFuelDiagnosticReflectionProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreBlockPublicCompletenessProperties
/-! Complete ordinary grammar correspondence for raw and isolated public
Core blocks, retaining either supplied tail-expression policy. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Raw public block grammar success is exactly execution with the same AST
and declarative remainder on a valid input, under the supplied policy. -/
theorem block_ordinary_success_iff (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {value : Block} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CoreBlockPublicOrdinaryParses policy.declarative
      input.declarativeRemainder value remainder ↔
      ∃ output, block policy input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (block policy) (block_exactOutcomeSpec policy)
    ((block_invariantFreeOnValid policy).ne_invariant input inputValid)
    (block_success_ordinary_sound policy) (block_reject_ordinary_sound policy)

/-- Raw public block grammar rejection is exactly execution at the same
declarative endpoint on a valid input, under the supplied policy. -/
theorem block_ordinary_reject_iff (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CoreBlockPublicRejects policy.declarative
      input.declarativeRemainder rejected ↔
      ∃ failure output, block policy input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject (block policy) (block_exactOutcomeSpec policy)
    ((block_invariantFreeOnValid policy).ne_invariant input inputValid)
    (block_success_ordinary_sound policy) (block_reject_ordinary_sound policy)

/-- Isolated public block grammar success is exactly capture-aware execution
with the same AST and external declarative remainder on a valid input. -/
theorem isolatedCoreBlockPublic_ordinary_success_iff
    (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {value : Block} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses policy.declarative
      input.declarativeRemainder value remainder ↔
      ∃ output, isolateBlock (block policy) input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok (isolateBlock (block policy))
    (isolatedCoreBlockPublic_exactOutcomeSpec policy)
    ((BlockInternals.isolateBlock_invariantFreeOnValid (block policy)
      (block_invariantFreeOnValid policy)).ne_invariant input inputValid)
    (isolatedCoreBlockPublic_success_ordinary_sound policy)
    (isolatedCoreBlockPublic_reject_ordinary_sound policy)

/-- Isolated public block grammar rejection is exactly execution at the same
external declarative endpoint on a valid input, under the supplied policy. -/
theorem isolatedCoreBlockPublic_ordinary_reject_iff
    (policy : TailExpressionPolicy)
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.IsolatedCoreBlockPublicRejects policy.declarative
      input.declarativeRemainder rejected ↔
      ∃ failure output, isolateBlock (block policy) input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject (isolateBlock (block policy))
    (isolatedCoreBlockPublic_exactOutcomeSpec policy)
    ((BlockInternals.isolateBlock_invariantFreeOnValid (block policy)
      (block_invariantFreeOnValid policy)).ne_invariant input inputValid)
    (isolatedCoreBlockPublic_success_ordinary_sound policy)
    (isolatedCoreBlockPublic_reject_ordinary_sound policy)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTermPublicCompletenessProperties
/-! Complete ordinary grammar correspondence for public Core term parsers
on valid states, at the AST and declarative remainder boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public expression grammar success is equivalent to execution with the
same AST and declarative remainder on a valid input. -/
theorem expression_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : Expr} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CoreExpressionOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, expression input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok expression expression_exactOutcomeSpec
    (expression_invariantFreeOnValid.ne_invariant input inputValid)
    expression_success_ordinary_sound expression_reject_ordinary_sound

/-- Public expression grammar rejection is equivalent to execution at the
same declarative endpoint on a valid input. -/
theorem expression_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CoreExpressionPublicRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, expression input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject expression expression_exactOutcomeSpec
    (expression_invariantFreeOnValid.ne_invariant input inputValid)
    expression_success_ordinary_sound expression_reject_ordinary_sound

/-- Public pattern grammar success is equivalent to execution with the
same AST and declarative remainder on a valid input. -/
theorem pattern_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : Pattern} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CorePatternOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, pattern input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok pattern pattern_exactOutcomeSpec
    (pattern_invariantFreeOnValid.ne_invariant input inputValid)
    pattern_success_ordinary_sound pattern_reject_ordinary_sound

/-- Public pattern grammar rejection is equivalent to execution at the
same declarative endpoint on a valid input. -/
theorem pattern_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CorePatternPublicRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, pattern input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject pattern pattern_exactOutcomeSpec
    (pattern_invariantFreeOnValid.ne_invariant input inputValid)
    pattern_success_ordinary_sound pattern_reject_ordinary_sound

/-- Public statement grammar success is equivalent to execution with the
same AST and declarative remainder on a valid input. -/
theorem statement_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : Statement} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CoreStatementOrdinaryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, statement input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok statement statement_exactOutcomeSpec
    (statement_invariantFreeOnValid.ne_invariant input inputValid)
    statement_success_ordinary_sound statement_reject_ordinary_sound

/-- Public statement grammar rejection is equivalent to execution at the
same declarative endpoint on a valid input. -/
theorem statement_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.CoreStatementPublicRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, statement input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject statement statement_exactOutcomeSpec
    (statement_invariantFreeOnValid.ne_invariant input inputValid)
    statement_success_ordinary_sound statement_reject_ordinary_sound

end Solcore.Syntax.Parser
end
