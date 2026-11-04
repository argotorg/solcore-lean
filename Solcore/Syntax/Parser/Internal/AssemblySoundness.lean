import Solcore.Syntax.Internal.StatementOutcomes
import Solcore.Syntax.Parser.Internal.ControlSoundness
import Solcore.Syntax.Parser.Internal.YulPublicSoundness
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Grammar.Statements

/-!
Soundness of the parser of inline `assembly` statements: each success and each rejection has its
declarative derivation. This stays apart from the other control statements because it needs the
public Yul results, and their `@[simp]` lemma on `remainingCount` must stay out of the statement
totality proofs.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.CoreAssemblyStatementOrdinaryOutcomeSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreAssemblyStatementDiagnosticReflectionProperties
/-!
Diagnostic reflection for the Core wrapper around an inline-Yul body.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem assemblyStatement_reflectsDiagnosticFreeOnSuccess
    (yulBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess yulBody) :
    Parser.ReflectsDiagnosticFreeOnSuccess assemblyStatement := by
  unfold assemblyStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .assemblyKw .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess yulBodyReflects
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreAssemblyStatementSoundnessProperties
/-!
Exact diagnostic-free soundness for the Core wrapper around an abstract Yul
body grammar.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

theorem assemblyStatement_success_sound
    (yulBodyParses : DeclarativeGrammar.Remainder → SourceSpan →
      List YulStmt → DeclarativeGrammar.Remainder → Prop)
    (yulBodySound : ∀ {input next : State} {body : YulParsedBlock},
      next.diagnosticsRev = [] → yulBody input = .ok body next →
      yulBodyParses input.declarativeRemainder body.span body.body
        next.declarativeRemainder)
    {input next : State} {statement : Statement}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : assemblyStatement input = .ok statement next) :
    DeclarativeGrammar.AssemblyStatementParses yulBodyParses
      input.declarativeRemainder statement next.declarativeRemainder := by
  unfold assemblyStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses .assemblyKw .statement markerResult)
    (yulBodySound diagnosticFree bodyResult)

end Solcore.Syntax.Parser
end
