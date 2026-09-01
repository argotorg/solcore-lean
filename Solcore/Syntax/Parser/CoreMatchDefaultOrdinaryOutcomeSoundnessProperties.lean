import Solcore.Syntax.DeclarativeCoreMatchDefaultOutcomeProperties
import Solcore.Syntax.Parser.CoreBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.Statement.Match

/-! Executable ordinary outcomes for prioritized optional Core default. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Optional default success follows its negative guard or exact marker and
raw required-block outcome. -/
theorem optionalDefaultBody_success_ordinary_sound
    (statement : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input output : State} {body : Option Block}
    (result : optionalDefaultBody statement input = .ok body output) :
    DeclarativeGrammar.OptionalDefaultBodyOrdinaryParses statementOrdinary
      input.declarativeRemainder body output.declarativeRemainder := by
  unfold optionalDefaultBody getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    cases markerResult : keyword .defaultKw .statement input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected =>
        rcases keyword_eq_ok_of_isKeyword_eq_true .defaultKw .statement
          present with ⟨marker, parsed⟩
        rw [parsed] at markerResult
        contradiction
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases bodyResult : coreBlock statement .require afterMarker with
        | invariant error => simp [bodyResult] at result
        | reject failure rejected => simp [bodyResult] at result
        | ok value afterBody =>
            simp only [bodyResult, pure] at result
            cases result
            exact .present marker.span
              (keyword_success_exactTokenParses .defaultKw .statement
                markerResult)
              ((coreBlock_ordinaryOutcome_sound statement .require
                statementOrdinary statementRejects statementSuccessSound
                  statementRejectSound).1 bodyResult)
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (keywordAbsentAt_of_isKeyword_eq_false .defaultKw absent)

/-- Optional default rejection is possible only through its positively
guarded raw required body. -/
theorem optionalDefaultBody_reject_ordinary_sound
    (statement : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalDefaultBody statement input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalDefaultBodyRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalDefaultBody getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    cases markerResult : keyword .defaultKw .statement input with
    | invariant error => simp [markerResult] at result
    | reject markerFailure markerRejected =>
        rcases keyword_eq_ok_of_isKeyword_eq_true .defaultKw .statement
          present with ⟨marker, parsed⟩
        rw [parsed] at markerResult
        contradiction
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases bodyResult : coreBlock statement .require afterMarker with
        | invariant error => simp [bodyResult] at result
        | ok body output => simp [bodyResult, pure] at result
        | reject bodyFailure bodyRejected =>
            simp only [bodyResult] at result
            cases result
            exact .bodyRejected marker.span
              (keyword_success_exactTokenParses .defaultKw .statement
                markerResult)
              ((coreBlock_ordinaryOutcome_sound statement .require
                statementOrdinary statementRejects statementSuccessSound
                  statementRejectSound).2 bodyResult)
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package both executable optional-default outcomes. -/
theorem optionalDefaultBody_ordinaryOutcome_sound
    (statement : Parser Statement)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {body : Option Block},
      optionalDefaultBody statement input = .ok body output →
        DeclarativeGrammar.OptionalDefaultBodyOrdinaryParses
          statementOrdinary input.declarativeRemainder body
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      optionalDefaultBody statement input = .reject failure rejected →
        DeclarativeGrammar.OptionalDefaultBodyRejects statementOrdinary
          statementRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨optionalDefaultBody_success_ordinary_sound statement statementOrdinary
      statementRejects statementSuccessSound statementRejectSound,
    optionalDefaultBody_reject_ordinary_sound statement statementOrdinary
      statementRejects statementSuccessSound statementRejectSound⟩

/-- Re-export deterministic optional-default outcomes. -/
theorem optionalDefaultBody_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.OptionalDefaultBodyOrdinaryParses
        statementOrdinary)
      (DeclarativeGrammar.OptionalDefaultBodyRejects statementOrdinary
        statementRejects) :=
  DeclarativeGrammar.optionalDefaultBodyDeterministicOutcomeSpec
    statementOutcomes

end Solcore.Syntax.Parser.MatchInternals
