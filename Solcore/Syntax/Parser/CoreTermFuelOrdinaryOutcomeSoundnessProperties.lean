import Solcore.Syntax.Parser.CoreTermFuelOrdinarySuccessorSoundnessProperties

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
