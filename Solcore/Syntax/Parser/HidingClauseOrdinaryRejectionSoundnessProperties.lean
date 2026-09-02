import Solcore.Syntax.DeclarativeHidingClauseOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.Import
import Solcore.Syntax.Parser.SelectorNameOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.SelectorNameOrdinarySuccessSoundnessProperties

/-! Exact executable rejection reflection for required and optional hiding. -/

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

/-- Every required hiding-clause rejection is either the missing contextual
marker or the exact nested nonempty allow-trailing selector-list rejection. -/
theorem hidingClause_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.hidingClause input =
      .reject failure rejected) :
    DeclarativeGrammar.HidingClauseRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.hidingClause at result
  cases markerResult : contextual .hiding .importDecl input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := contextual_reject_state_eq .hiding .importDecl
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (contextual_reject_tokenKindAbsentAt .hiding .importDecl markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := contextual_success_exactTokenParses .hiding
        .importDecl markerResult
      cases valuesResult : delimited .leftBrace .rightBrace false
          (selectorName .importDecl) .importDecl .topLevel afterMarker with
      | invariant error => simp [valuesResult] at result
      | reject valuesFailure valuesRejected =>
          simp only [valuesResult] at result
          cases result
          exact .namesRejected marker.span markerParsed
            (delimited_reject_sound .leftBrace .rightBrace false
              (selectorName .importDecl)
              DeclarativeGrammar.SelectorNameOrdinaryParses
              DeclarativeGrammar.SelectorNameRejects .importDecl .topLevel
              (selectorName_success_ordinaryOutcome_sound .importDecl)
              (selectorName_reject_ordinaryOutcome_sound .importDecl)
              valuesResult)
      | ok values afterValues =>
          simp only [valuesResult] at result
          cases namesResult : ImportInternals.requireSelectorNames values
              afterValues with
          | invariant error => simp [namesResult] at result
          | reject namesFailure namesRejected =>
              unfold ImportInternals.requireSelectorNames at namesResult
              cases elements : values.elements <;>
                simp [elements, pure] at namesResult
          | ok names afterNames => simp [namesResult, pure] at result

/-- Optional hiding can reject only after its positive contextual guard commits
to a required hiding clause. -/
theorem optionalHiding_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.optionalHiding input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalHidingRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.optionalHiding getState at result
  simp only [bind] at result
  by_cases present : isContextual input .hiding = true
  · simp only [present, if_true] at result
    rcases contextual_eq_ok_of_isContextual_eq_true .hiding .importDecl
        present with
      ⟨marker, markerResult⟩
    cases clauseResult : ImportInternals.hidingClause input with
    | invariant error => simp [clauseResult] at result
    | ok clause output => simp [clauseResult, pure] at result
    | reject clauseFailure clauseRejected =>
        simp only [clauseResult] at result
        cases result
        exact .present
          ⟨marker.span,
            (contextual_success_exactTokenParses .hiding .importDecl
              markerResult).1⟩
          (hidingClause_reject_ordinaryOutcome_sound clauseResult)
  · have absent : isContextual input .hiding = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

end Solcore.Syntax.Parser
