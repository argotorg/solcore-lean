import Solcore.Syntax.DeclarativeNamespaceImportOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Import
import Solcore.Syntax.Parser.ImportTerminatorOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImportTerminatorOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.ModulePath

/-! Exact executable rejection reflection for namespace-import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem keyword_reject_tokenKindAbsentAt
    (value : HardKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.keyword value) := by
  by_cases present : isKeyword input value = true
  · rcases keyword_eq_ok_of_isKeyword_eq_true value context present with
      ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact keywordAbsentAt_of_isKeyword_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem keyword_reject_state_eq
    (value : HardKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.keyword value) context
    (· == .keyword value) result

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

/-- Every executable namespace-import rejection records its exact first
rejecting stage among `*`, `as`, alias, `from`, path, and terminator. -/
theorem namespaceImport_reject_ordinaryOutcome_sound (start : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.namespaceImport start input =
      .reject failure rejected) :
    DeclarativeGrammar.NamespaceImportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.namespaceImport at result
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
      cases asResult : keyword .asKw .importDecl afterStar with
      | invariant error => simp [asResult] at result
      | reject asFailure asRejected =>
          have asRejectedEq := keyword_reject_state_eq .asKw .importDecl
            asResult
          subst asRejected
          simp only [asResult] at result
          cases result
          exact .asMissing star.span starParsed
            (keyword_reject_tokenKindAbsentAt .asKw .importDecl asResult)
      | ok asToken afterAs =>
          simp only [asResult] at result
          have asParsed := keyword_success_exactTokenParses .asKw .importDecl
            asResult
          cases aliasResult : identifier .importDecl afterAs with
          | invariant error => simp [aliasResult] at result
          | reject aliasFailure aliasRejected =>
              simp only [aliasResult] at result
              cases result
              exact .aliasRejected star.span asToken.span starParsed asParsed
                (identifier_reject_sound .importDecl aliasResult)
          | ok alias afterAlias =>
              simp only [aliasResult] at result
              have aliasParsed := identifier_success_sound .importDecl
                aliasResult
              cases fromResult : contextual .from .importDecl afterAlias with
              | invariant error => simp [fromResult] at result
              | reject fromFailure fromRejected =>
                  have fromRejectedEq := contextual_reject_state_eq .from
                    .importDecl fromResult
                  subst fromRejected
                  simp only [fromResult] at result
                  cases result
                  exact .fromMissing star.span asToken.span starParsed asParsed
                    aliasParsed
                    (contextual_reject_tokenKindAbsentAt .from .importDecl
                      fromResult)
              | ok fromToken afterFrom =>
                  simp only [fromResult] at result
                  have fromParsed := contextual_success_exactTokenParses
                    .from .importDecl fromResult
                  cases pathResult : modulePath .importDecl afterFrom with
                  | invariant error => simp [pathResult] at result
                  | reject pathFailure pathRejected =>
                      simp only [pathResult] at result
                      cases result
                      exact .pathRejected star.span asToken.span fromToken.span
                        starParsed asParsed aliasParsed fromParsed
                        (modulePath_reject_ordinaryOutcome_sound .importDecl
                          pathResult)
                  | ok path afterPath =>
                      simp only [pathResult] at result
                      have pathParsed :=
                        modulePath_success_ordinaryOutcome_sound .importDecl
                          pathResult
                      unfold ImportInternals.finish at result
                      cases terminatorResult :
                          ImportInternals.terminator path.span afterPath with
                      | invariant error => simp [bind, terminatorResult] at result
                      | ok endSpan output =>
                          simp [bind, terminatorResult, pure] at result
                      | reject terminatorFailure terminatorRejected =>
                          simp only [bind, terminatorResult] at result
                          cases result
                          exact .terminatorRejected star.span asToken.span
                            fromToken.span starParsed asParsed aliasParsed
                            fromParsed pathParsed
                            (importTerminator_reject_ordinaryOutcome_sound
                              path.span terminatorResult)

end Solcore.Syntax.Parser
