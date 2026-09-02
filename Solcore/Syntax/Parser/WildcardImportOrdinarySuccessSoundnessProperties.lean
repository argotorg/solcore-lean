import Solcore.Syntax.DeclarativeWildcardImportOutcomeGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.HidingClauseOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.ImportTerminatorOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.ModulePathOrdinarySuccessSoundnessProperties

/-! Broad ordinary-success reflection for wildcard import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_success_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every executable wildcard-import success preserves its fixed prefix,
module path, optional hiding, explicit-or-recovered terminator, AST, span, and
final remainder. -/
theorem wildcardImport_success_ordinaryOutcome_sound (start : SourceSpan)
    {input output : State} {declaration : ImportDecl}
    (result : ImportInternals.wildcardImport start input =
      .ok declaration output) :
    DeclarativeGrammar.WildcardImportOrdinaryParses start
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold ImportInternals.wildcardImport at result
  rcases bind_success_components result with
    ⟨star, afterStar, starResult, rest⟩
  rcases bind_success_components rest with
    ⟨fromToken, afterFrom, fromResult, rest⟩
  rcases bind_success_components rest with
    ⟨path, afterPath, pathResult, rest⟩
  rcases bind_success_components rest with
    ⟨hidden, afterHiding, hidingResult, finishResult⟩
  cases hidden with
  | none =>
      have normalized : ImportInternals.finish start path.span
          (.wildcard path none) afterHiding = .ok declaration output := by
        simpa using finishResult
      unfold ImportInternals.finish at normalized
      rcases bind_success_components normalized with
        ⟨endSpan, afterTerminator, terminatorResult, finished⟩
      cases finished
      exact .parsed star.span fromToken.span
        (symbol_success_exactTokenParses .star .importDecl starResult)
        (contextual_success_exactTokenParses .from .importDecl fromResult)
        (modulePath_success_ordinaryOutcome_sound .importDecl pathResult)
        (optionalHiding_success_ordinaryOutcome_sound hidingResult)
        (importTerminator_success_ordinaryOutcome_sound path.span
          terminatorResult)
  | some clause =>
      have normalized : ImportInternals.finish start clause.span
          (.wildcard path (some clause)) afterHiding =
            .ok declaration output := by
        simpa using finishResult
      unfold ImportInternals.finish at normalized
      rcases bind_success_components normalized with
        ⟨endSpan, afterTerminator, terminatorResult, finished⟩
      cases finished
      exact .parsed star.span fromToken.span
        (symbol_success_exactTokenParses .star .importDecl starResult)
        (contextual_success_exactTokenParses .from .importDecl fromResult)
        (modulePath_success_ordinaryOutcome_sound .importDecl pathResult)
        (optionalHiding_success_ordinaryOutcome_sound hidingResult)
        (importTerminator_success_ordinaryOutcome_sound clause.span
          terminatorResult)

end Solcore.Syntax.Parser
