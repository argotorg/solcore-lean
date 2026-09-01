import Solcore.Syntax.DeclarativeCoreTermPublicOutcomeProperties
import Solcore.Syntax.Parser.CoreBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTermFuelOrdinaryOutcomeSoundnessProperties

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

end Solcore.Syntax.Parser
