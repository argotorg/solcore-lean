import Solcore.Syntax.DeclarativeNamespaceImportOutcomeGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.ImportTerminatorOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.ModulePathOrdinarySuccessSoundnessProperties

/-! Broad ordinary-success reflection for namespace-import payloads. -/

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

/-- Every executable namespace-import success preserves the exact fixed
prefix, alias, module path, recovered-or-explicit terminator, AST, span, and
final remainder. -/
theorem namespaceImport_success_ordinaryOutcome_sound (start : SourceSpan)
    {input output : State} {declaration : ImportDecl}
    (result : ImportInternals.namespaceImport start input =
      .ok declaration output) :
    DeclarativeGrammar.NamespaceImportOrdinaryParses start
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold ImportInternals.namespaceImport at result
  rcases bind_success_components result with
    ⟨star, afterStar, starResult, rest⟩
  rcases bind_success_components rest with
    ⟨asToken, afterAs, asResult, rest⟩
  rcases bind_success_components rest with
    ⟨alias, afterAlias, aliasResult, rest⟩
  rcases bind_success_components rest with
    ⟨fromToken, afterFrom, fromResult, rest⟩
  rcases bind_success_components rest with
    ⟨path, afterPath, pathResult, finishResult⟩
  unfold ImportInternals.finish at finishResult
  rcases bind_success_components finishResult with
    ⟨endSpan, afterTerminator, terminatorResult, finished⟩
  cases finished
  exact .parsed star.span asToken.span fromToken.span endSpan
    (symbol_success_exactTokenParses .star .importDecl starResult)
    (keyword_success_exactTokenParses .asKw .importDecl asResult)
    (identifier_success_sound .importDecl aliasResult)
    (contextual_success_exactTokenParses .from .importDecl fromResult)
    (modulePath_success_ordinaryOutcome_sound .importDecl pathResult)
    (importTerminator_success_ordinaryOutcome_sound path.span
      terminatorResult)

end Solcore.Syntax.Parser
