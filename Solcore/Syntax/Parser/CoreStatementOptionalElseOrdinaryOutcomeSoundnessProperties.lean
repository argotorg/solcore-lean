import Solcore.Syntax.DeclarativeCoreStatementOptionalElseOutcomeProperties
import Solcore.Syntax.Parser.CoreBlockOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.Statement.Control

/-! Executable ordinary outcomes for prioritized optional Core `else`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- Optional `else` success follows the negative guard or the exact marker and
raw required-block outcome. -/
theorem optionalElseBody_success_ordinary_sound
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
    (result : optionalElseBody statement input = .ok body output) :
    DeclarativeGrammar.OptionalElseBodyOrdinaryParses statementOrdinary
      input.declarativeRemainder body output.declarativeRemainder := by
  unfold optionalElseBody getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .elseKw
  · simp only [present, if_true] at result
    cases markerResult : keyword .elseKw .statement input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected =>
        rcases keyword_eq_ok_of_isKeyword_eq_true .elseKw .statement present
          with ⟨marker, parsed⟩
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
              (keyword_success_exactTokenParses .elseKw .statement
                markerResult)
              ((coreBlock_ordinaryOutcome_sound statement .require
                statementOrdinary statementRejects statementSuccessSound
                  statementRejectSound).1 bodyResult)
  · have absent : isKeyword input .elseKw = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (keywordAbsentAt_of_isKeyword_eq_false .elseKw absent)

/-- Optional `else` rejection is possible only after its positive guard and
exact marker, through the raw required block. -/
theorem optionalElseBody_reject_ordinary_sound
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
    (result : optionalElseBody statement input = .reject failure rejected) :
    DeclarativeGrammar.OptionalElseBodyRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalElseBody getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .elseKw
  · simp only [present, if_true] at result
    cases markerResult : keyword .elseKw .statement input with
    | invariant error => simp [markerResult] at result
    | reject markerFailure markerRejected =>
        rcases keyword_eq_ok_of_isKeyword_eq_true .elseKw .statement present
          with ⟨marker, parsed⟩
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
              (keyword_success_exactTokenParses .elseKw .statement
                markerResult)
              ((coreBlock_ordinaryOutcome_sound statement .require
                statementOrdinary statementRejects statementSuccessSound
                  statementRejectSound).2 bodyResult)
  · have absent : isKeyword input .elseKw = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package both executable optional-else outcomes. -/
theorem optionalElseBody_ordinaryOutcome_sound
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
      optionalElseBody statement input = .ok body output →
        DeclarativeGrammar.OptionalElseBodyOrdinaryParses statementOrdinary
          input.declarativeRemainder body output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      optionalElseBody statement input = .reject failure rejected →
        DeclarativeGrammar.OptionalElseBodyRejects statementOrdinary
          statementRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨optionalElseBody_success_ordinary_sound statement statementOrdinary
      statementRejects statementSuccessSound statementRejectSound,
    optionalElseBody_reject_ordinary_sound statement statementOrdinary
      statementRejects statementSuccessSound statementRejectSound⟩

/-- Re-export deterministic optional-else outcomes. -/
theorem optionalElseBody_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.OptionalElseBodyOrdinaryParses statementOrdinary)
      (DeclarativeGrammar.OptionalElseBodyRejects statementOrdinary
        statementRejects) :=
  DeclarativeGrammar.optionalElseBodyDeterministicOutcomeSpec
    statementOutcomes

end Solcore.Syntax.Parser.ControlInternals
