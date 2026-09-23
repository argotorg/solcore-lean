import Solcore.Syntax.DeclarativeWildcardImportOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.HidingClauseOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.HidingClauseOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.Import
import Solcore.Syntax.Parser.ImportTerminatorOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ModulePath

/-! Exact executable rejection reflection for wildcard-import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextual_reject_tokenKindAbsentAt
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) := by
  by_cases present : isContextual input value = true
  · rcases contextual_eq_ok_of_isContextual_eq_true value context present
      with ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact contextualAbsentAt_of_isContextual_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem contextual_reject_state_eq
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.contextual value) context
    (·.isContextual value) result

private theorem finish_reject_ordinaryOutcome_sound
    (start last : SourceSpan) (value : ImportDeclValue)
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.finish start last value input =
      .reject failure rejected) :
    DeclarativeGrammar.ImportTerminatorRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.finish at result
  cases terminatorResult : ImportInternals.terminator last input with
  | invariant error => simp [bind, terminatorResult] at result
  | ok endSpan output => simp [bind, terminatorResult, pure] at result
  | reject terminatorFailure terminatorRejected =>
      simp only [bind, terminatorResult] at result
      cases result
      exact importTerminator_reject_ordinaryOutcome_sound last
        terminatorResult

/-- Every executable wildcard-import rejection records its exact first
rejecting stage among `*`, `from`, path, optional hiding, and terminator. -/
theorem wildcardImport_reject_ordinaryOutcome_sound (start : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.wildcardImport start input =
      .reject failure rejected) :
    DeclarativeGrammar.WildcardImportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.wildcardImport at result
  cases starResult : symbol .star .importDecl input with
  | invariant error => simp [bind, starResult] at result
  | reject starFailure starRejected =>
      have starRejectedEq := symbol_reject_state_eq .star .importDecl
        starResult
      subst starRejected
      simp only [bind, starResult] at result
      cases result
      exact .starMissing
        (symbol_reject_tokenKindAbsentAt .star .importDecl starResult)
  | ok star afterStar =>
      simp only [bind, starResult] at result
      have starParsed := symbol_success_exactTokenParses .star .importDecl
        starResult
      cases fromResult : contextual .from .importDecl afterStar with
      | invariant error => simp [fromResult] at result
      | reject fromFailure fromRejected =>
          have fromRejectedEq := contextual_reject_state_eq .from .importDecl
            fromResult
          subst fromRejected
          simp only [fromResult] at result
          cases result
          exact .fromMissing star.span starParsed
            (contextual_reject_tokenKindAbsentAt .from .importDecl fromResult)
      | ok fromToken afterFrom =>
          simp only [fromResult] at result
          have fromParsed := contextual_success_exactTokenParses .from
            .importDecl fromResult
          cases pathResult : modulePath .importDecl afterFrom with
          | invariant error => simp [pathResult] at result
          | reject pathFailure pathRejected =>
              simp only [pathResult] at result
              cases result
              exact .pathRejected star.span fromToken.span starParsed
                fromParsed
                (modulePath_reject_ordinaryOutcome_sound .importDecl
                  pathResult)
          | ok path afterPath =>
              simp only [pathResult] at result
              have pathParsed := modulePath_success_ordinaryOutcome_sound
                .importDecl pathResult
              cases hidingResult : ImportInternals.optionalHiding afterPath with
              | invariant error => simp [hidingResult] at result
              | reject hidingFailure hidingRejected =>
                  simp only [hidingResult] at result
                  cases result
                  exact .hidingRejected star.span fromToken.span starParsed
                    fromParsed pathParsed
                    (optionalHiding_reject_ordinaryOutcome_sound hidingResult)
              | ok hidden afterHiding =>
                  simp only [hidingResult] at result
                  have hidingParsed :=
                    optionalHiding_success_ordinaryOutcome_sound hidingResult
                  cases hidden with
                  | none =>
                      exact .terminatorRejected star.span fromToken.span
                        starParsed fromParsed pathParsed hidingParsed
                        (finish_reject_ordinaryOutcome_sound start path.span
                          (.wildcard path none) result)
                  | some clause =>
                      exact .terminatorRejected star.span fromToken.span
                        starParsed fromParsed pathParsed hidingParsed
                        (finish_reject_ordinaryOutcome_sound start clause.span
                          (.wildcard path (some clause)) result)

end Solcore.Syntax.Parser
