import Solcore.Syntax.DeclarativeCoreAssemblyStatementGrammar
import Solcore.Syntax.Parser.CoreAssemblyStatementDiagnosticReflectionProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

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
