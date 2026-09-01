import Solcore.Syntax.DeclarativeCoreAssemblyStatementOutcomeProperties
import Solcore.Syntax.Parser.Statement.Control
import Solcore.Syntax.Parser.YulBodyPublicSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Executable ordinary outcomes for Core `assembly`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable assembly success retains its exact marker and public Yul
body ordinary outcome. -/
theorem assemblyStatement_success_ordinary_sound
    {input output : State} {statement : Statement}
    (result : assemblyStatement input = .ok statement output) :
    DeclarativeGrammar.AssemblyStatementOrdinaryParses
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold assemblyStatement at result
  cases markerResult : keyword .assemblyKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases bodyResult : yulBody afterMarker with
      | invariant error => simp [bodyResult] at result
      | reject failure rejected => simp [bodyResult] at result
      | ok body afterBody =>
          simp only [bodyResult, pure] at result
          cases result
          exact .parsed marker.span
            (keyword_success_exactTokenParses .assemblyKw .statement
              markerResult)
            (yulBody_success_ordinary_sound bodyResult)

/-- Every executable assembly rejection records its first failing stage. -/
theorem assemblyStatement_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : assemblyStatement input = .reject failure rejected) :
    DeclarativeGrammar.AssemblyStatementRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold assemblyStatement at result
  cases markerResult : keyword .assemblyKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq .assemblyKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .assemblyKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases bodyResult : yulBody afterMarker with
      | invariant error => simp [bodyResult] at result
      | ok body output => simp [bodyResult, pure] at result
      | reject bodyFailure bodyRejected =>
          simp only [bodyResult] at result
          cases result
          exact .bodyRejected marker.span
            (keyword_success_exactTokenParses .assemblyKw .statement
              markerResult)
            (yulBody_reject_ordinary_sound bodyResult)

/-- Package both executable Core assembly outcomes. -/
theorem assemblyStatement_ordinaryOutcome_sound :
    (∀ {input output : State} {statement : Statement},
      assemblyStatement input = .ok statement output →
        DeclarativeGrammar.AssemblyStatementOrdinaryParses
          input.declarativeRemainder statement output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      assemblyStatement input = .reject failure rejected →
        DeclarativeGrammar.AssemblyStatementRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨assemblyStatement_success_ordinary_sound,
    assemblyStatement_reject_ordinary_sound⟩

/-- Re-export deterministic Core assembly outcomes. -/
theorem assemblyStatement_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.AssemblyStatementOrdinaryParses
      DeclarativeGrammar.AssemblyStatementRejects :=
  DeclarativeGrammar.assemblyStatementDeterministicOutcomeSpec

end Solcore.Syntax.Parser
