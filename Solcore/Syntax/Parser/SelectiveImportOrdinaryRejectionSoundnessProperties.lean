import Solcore.Syntax.DeclarativeSelectiveImportOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.HidingClauseOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.HidingClauseOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.Import
import Solcore.Syntax.Parser.ImportTerminatorOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ModulePathOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ModulePathOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.SelectedImportsOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.SelectedImportsOrdinarySuccessSoundnessProperties

/-! Exact executable rejection reflection for selective-import payloads. -/

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

/-- Every executable selective-import rejection records its exact first
rejecting stage among selection, `from`, path, optional hiding, and
terminator. -/
theorem selectiveImport_reject_ordinaryOutcome_sound (start : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.selectiveImport start input =
      .reject failure rejected) :
    DeclarativeGrammar.SelectiveImportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.selectiveImport at result
  cases selectionResult : ImportInternals.selectedImports input with
  | invariant error => simp [bind, selectionResult] at result
  | reject selectionFailure selectionRejected =>
      simp only [bind, selectionResult] at result
      cases result
      exact .selectionRejected
        (selectedImports_reject_ordinaryOutcome_sound selectionResult)
  | ok selection afterSelection =>
      simp only [bind, selectionResult] at result
      have selectionParsed :=
        selectedImports_success_ordinaryOutcome_sound selectionResult
      cases fromResult : contextual .from .importDecl afterSelection with
      | invariant error => simp [fromResult] at result
      | reject fromFailure fromRejected =>
          have fromRejectedEq := contextual_reject_state_eq .from .importDecl
            fromResult
          subst fromRejected
          simp only [fromResult] at result
          cases result
          exact .fromMissing selectionParsed
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
              exact .pathRejected fromToken.span selectionParsed fromParsed
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
                  exact .hidingRejected fromToken.span selectionParsed
                    fromParsed pathParsed
                    (optionalHiding_reject_ordinaryOutcome_sound hidingResult)
              | ok hidden afterHiding =>
                  simp only [hidingResult] at result
                  have hidingParsed :=
                    optionalHiding_success_ordinaryOutcome_sound hidingResult
                  cases hidden with
                  | none =>
                      exact .terminatorRejected fromToken.span selectionParsed
                        fromParsed pathParsed hidingParsed
                        (finish_reject_ordinaryOutcome_sound start path.span
                          (.selected selection path none) result)
                  | some clause =>
                      exact .terminatorRejected fromToken.span selectionParsed
                        fromParsed pathParsed hidingParsed
                        (finish_reject_ordinaryOutcome_sound start clause.span
                          (.selected selection path (some clause)) result)

end Solcore.Syntax.Parser
