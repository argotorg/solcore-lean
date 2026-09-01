import Solcore.Syntax.Parser.YulSwitchCaseArmOrdinaryOutcomeSoundnessProperties

/-!
Executable ordinary-success and rejection bridges for the prioritized
optional `default` arm of a Yul switch.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.YulControl

private theorem keyword_eq_ok_of_isKeyword_eq_true (value : HardKeyword)
    (context : ParseContext) {input : State}
    (present : isKeyword input value = true) :
    ∃ token, keyword value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isKeyword State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .keyword value) = true at present
      refine ⟨token, ?_⟩
      unfold keyword acceptToken
      simp only [found, present, if_true]

/-- Every optional-default success retains exact keyword priority and its
ordinary recursive block. -/
theorem optionalDefault_success_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {defaultBody : Option YulParsedBlock}
    (result : optionalDefault statement input = .ok defaultBody output) :
    DeclarativeGrammar.OptionalYulDefaultOrdinaryParses statementOrdinary
      input.declarativeRemainder (defaultBody.map (fun body => body.span))
        (defaultBody.map (fun body => body.body))
          output.declarativeRemainder := by
  unfold optionalDefault getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    cases markerResult : keyword .defaultKw .yulStatement input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected =>
        rcases keyword_eq_ok_of_isKeyword_eq_true .defaultKw .yulStatement
            present with ⟨marker, successfulMarker⟩
        rw [successfulMarker] at markerResult
        contradiction
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases bodyResult : yulBlock statement afterMarker with
        | invariant error => simp [bodyResult] at result
        | reject failure rejected => simp [bodyResult] at result
        | ok body afterBody =>
            simp only [bodyResult, pure] at result
            cases result
            exact .present marker.span body.span
              (keyword_success_exactTokenParses .defaultKw .yulStatement
                markerResult)
              (yulBlock_success_ordinary_sound statement statementOrdinary
                statementSuccessSound bodyResult)
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (keywordAbsentAt_of_isKeyword_eq_false .defaultKw absent)

/-- The guarded optional default rejects exactly when its braced body
rejects, retaining that body's rejected remainder. -/
theorem optionalDefault_reject_ordinary_sound
    (statement : Parser YulStmt)
    (statementOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : YulStmt},
      statement input = .ok value output →
        statementOrdinary input.declarativeRemainder value
          output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected →
        statementRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalDefault statement input = .reject failure rejected) :
    DeclarativeGrammar.OptionalYulDefaultRejects statementOrdinary
      statementRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalDefault getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    cases markerResult : keyword .defaultKw .yulStatement input with
    | invariant error => simp [markerResult] at result
    | reject markerFailure markerRejected =>
        rcases keyword_eq_ok_of_isKeyword_eq_true .defaultKw .yulStatement
            present with ⟨marker, successfulMarker⟩
        rw [successfulMarker] at markerResult
        contradiction
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases bodyResult : yulBlock statement afterMarker with
        | invariant error => simp [bodyResult] at result
        | reject bodyFailure bodyRejected =>
            simp only [bodyResult] at result
            cases result
            exact .bodyRejected marker.span
              (keyword_success_exactTokenParses .defaultKw .yulStatement
                markerResult)
              (yulBlock_reject_ordinary_sound statement statementOrdinary
                statementRejects statementSuccessSound statementRejectSound
                bodyResult)
        | ok body afterBody => simp [bodyResult, pure] at result
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

end Solcore.Syntax.Parser.YulControl
