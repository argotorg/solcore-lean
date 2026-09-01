import Solcore.Syntax.DeclarativeYulStatementFuelGrammar
import Solcore.Syntax.Parser.YulStatementCoreOrdinaryRejectSoundnessProperties
import Solcore.Syntax.Parser.YulStatementLayerOrdinarySoundnessProperties
import Solcore.Syntax.Parser.YulStatementTerminatedOrdinarySoundnessProperties

/-! Ordinary outcome reflection for recursive fuel-indexed Yul statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Success and rejection reflection are proved together because one
recursive core layer needs both outcomes of its preceding fuel. -/
theorem yulStatementWithFuel_ordinaryOutcome_sound : ∀ fuel,
    (∀ {input output : State} {statement : YulStmt},
      yulStatementWithFuel fuel input = .ok statement output →
        DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel
          input.declarativeRemainder statement output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      yulStatementWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.YulStatementRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro input output statement result
        simp [yulStatementWithFuel] at result
      · intro input rejected failure result
        simp [yulStatementWithFuel] at result
  | succ fuel inductionHypothesis =>
      have nestedShape := yulStatementWithFuel_preservesTokenWindow fuel
      have coreShape := yulStatementCore_preservesTokenWindow
        (yulStatementWithFuel fuel) nestedShape
      have terminatedShape := yulStatementTerminated_preservesTokenWindow
        (yulStatementWithFuel fuel) coreShape
      have coreSuccessSound : ∀ {input output : State}
          {statement : YulStmt},
          yulStatementCore (yulStatementWithFuel fuel) input =
              .ok statement output →
            DeclarativeGrammar.YulStatementCoreOrdinaryParses
              (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
              (DeclarativeGrammar.YulStatementRejectsWithFuel fuel)
              input.declarativeRemainder statement
                output.declarativeRemainder := by
        intro input output statement coreResult
        exact yulStatementCore_success_ordinary_sound
          (yulStatementWithFuel fuel)
          (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
          (DeclarativeGrammar.YulStatementRejectsWithFuel fuel)
          inductionHypothesis.1 inductionHypothesis.2 coreResult
      have coreRejectSound : ∀ {input rejected : State} {failure : Failure},
          yulStatementCore (yulStatementWithFuel fuel) input =
              .reject failure rejected →
            DeclarativeGrammar.YulStatementCoreRejects
              (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
              (DeclarativeGrammar.YulStatementRejectsWithFuel fuel)
              input.declarativeRemainder rejected.declarativeRemainder := by
        intro input rejected failure coreResult
        exact yulStatementCore_reject_ordinary_sound
          (yulStatementWithFuel fuel)
          (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
          (DeclarativeGrammar.YulStatementRejectsWithFuel fuel)
          inductionHypothesis.1 inductionHypothesis.2 coreResult
      have terminatedSuccessSound : ∀ {input output : State}
          {statement : YulStmt},
          yulStatementTerminated (yulStatementWithFuel fuel) input =
              .ok statement output →
            DeclarativeGrammar.YulStatementTerminatedOrdinaryParses
              (DeclarativeGrammar.YulStatementCoreOrdinaryParses
                (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
                (DeclarativeGrammar.YulStatementRejectsWithFuel fuel))
              input.declarativeRemainder statement
                output.declarativeRemainder := by
        intro input output statement terminatedResult
        exact yulStatementTerminated_success_ordinary_sound
          (yulStatementWithFuel fuel)
          (DeclarativeGrammar.YulStatementCoreOrdinaryParses
            (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
            (DeclarativeGrammar.YulStatementRejectsWithFuel fuel))
          coreSuccessSound terminatedResult
      have terminatedRejectSound : ∀ {input rejected : State}
          {failure : Failure},
          yulStatementTerminated (yulStatementWithFuel fuel) input =
              .reject failure rejected →
            DeclarativeGrammar.YulStatementCoreRejects
              (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
              (DeclarativeGrammar.YulStatementRejectsWithFuel fuel)
              input.declarativeRemainder rejected.declarativeRemainder := by
        intro input rejected failure terminatedResult
        exact yulStatementTerminated_reject_ordinary_sound
          (yulStatementWithFuel fuel)
          (DeclarativeGrammar.YulStatementCoreRejects
            (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
            (DeclarativeGrammar.YulStatementRejectsWithFuel fuel))
          coreRejectSound terminatedResult
      constructor
      · intro input output statement result
        apply (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel.succ_iff).2
        exact yulStatementLayer_success_ordinary_sound
          (yulStatementWithFuel fuel)
          (DeclarativeGrammar.YulStatementTerminatedOrdinaryParses
            (DeclarativeGrammar.YulStatementCoreOrdinaryParses
              (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
              (DeclarativeGrammar.YulStatementRejectsWithFuel fuel)))
          (DeclarativeGrammar.YulStatementCoreRejects
            (DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel)
            (DeclarativeGrammar.YulStatementRejectsWithFuel fuel))
          terminatedSuccessSound terminatedRejectSound terminatedShape result
      · intro input rejected failure result
        apply (DeclarativeGrammar.YulStatementRejectsWithFuel.succ_iff).2
        exact yulStatementLayer_reject_sound (yulStatementWithFuel fuel)
          terminatedShape result

/-- Every successful executable statement at explicit fuel follows the
ordinary declarative relation at that same fuel. -/
theorem yulStatementWithFuel_success_ordinary_sound (fuel : Nat)
    {input output : State} {statement : YulStmt}
    (result : yulStatementWithFuel fuel input = .ok statement output) :
    DeclarativeGrammar.YulStatementOrdinaryParsesWithFuel fuel
      input.declarativeRemainder statement output.declarativeRemainder :=
  (yulStatementWithFuel_ordinaryOutcome_sound fuel).1 result

/-- Every executable rejection at explicit fuel follows the exact declarative
rejection at that same fuel. -/
theorem yulStatementWithFuel_reject_ordinary_sound (fuel : Nat)
    {input rejected : State} {failure : Failure}
    (result : yulStatementWithFuel fuel input = .reject failure rejected) :
    DeclarativeGrammar.YulStatementRejectsWithFuel fuel
      input.declarativeRemainder rejected.declarativeRemainder :=
  (yulStatementWithFuel_ordinaryOutcome_sound fuel).2 result

end Solcore.Syntax.Parser
