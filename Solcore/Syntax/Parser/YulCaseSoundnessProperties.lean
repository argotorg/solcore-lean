import Solcore.Syntax.DeclarativeYulSwitchGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.YulBlockSoundnessProperties
import Solcore.Syntax.Parser.YulExpressionLeafSoundnessProperties
import Solcore.Syntax.Parser.YulSwitchDiagnosticReflectionProperties

/-!
Exact diagnostic-free soundness for Yul switch arms, the reverse-accumulating
case loop, and the prioritized optional default.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.YulControl

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

/-- One diagnostic-free case arm has its exact marker, literal, block, span,
AST, and remainder. -/
theorem caseArm_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {arm : YulCase}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : caseArm statement input = .ok arm next) :
    DeclarativeGrammar.YulCaseArmParses statementParses
      input.declarativeRemainder arm next.declarativeRemainder := by
  unfold caseArm at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, literalStage⟩
  rcases bind_ok_components literalStage with
    ⟨literal, afterLiteral, literalResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span body.span
    (keyword_success_exactTokenParses .caseKw .yulStatement markerResult)
    (yulLiteral_success_sound literalResult)
    (yulBlock_success_sound statement statementParses statementReflects
      statementSound diagnosticFree bodyResult)

/-- The executable reverse accumulator is the prefix of the returned cases;
the declarative relation is the remaining forward, maximal suffix. -/
theorem caseList_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder) :
    ∀ fuel casesRev input cases next,
      next.diagnosticsRev = [] →
      caseList statement fuel casesRev input = .ok cases next →
      ∃ suffix,
        cases = casesRev.reverse ++ suffix ∧
        DeclarativeGrammar.YulCaseListParses statementParses
          input.declarativeRemainder suffix next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input cases next diagnosticFree result
      simp [caseList] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input cases next diagnosticFree result
      unfold caseList at result
      cases casePresent : isKeyword input .caseKw with
      | false =>
          simp only [casePresent, Bool.false_eq_true, if_false] at result
          cases result
          exact ⟨[], by simp,
            .done (keywordAbsentAt_of_isKeyword_eq_false .caseKw casePresent),
            diagnosticFree⟩
      | true =>
          simp only [casePresent, if_true] at result
          cases armResult : caseArm statement input with
          | invariant error => simp [armResult] at result
          | reject failure rejected => simp [armResult] at result
          | ok arm afterArm =>
              simp only [armResult] at result
              by_cases progress : afterArm.cursor > input.cursor
              · simp only [progress, if_true] at result
                rcases inductionHypothesis (arm :: casesRev) afterArm cases
                    next diagnosticFree result with
                  ⟨suffix, casesEq, tailGrammar, afterArmFree⟩
                have armGrammar := caseArm_success_sound statement
                  statementParses statementReflects statementSound
                    afterArmFree armResult
                have inputFree := caseArm_reflectsDiagnosticFreeOnSuccess
                  statement statementReflects input arm afterArm armResult
                    afterArmFree
                refine ⟨arm :: suffix, ?_,
                  .next armGrammar (by
                    simpa [State.declarativeRemainder] using progress)
                    tailGrammar,
                  inputFree⟩
                simpa [List.reverse_cons, List.append_assoc] using casesEq
              · simp only [progress, if_false] at result
                contradiction

/-- Optional default success retains exact keyword priority and its block. -/
theorem optionalDefault_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {defaultBody : Option YulParsedBlock}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalDefault statement input = .ok defaultBody next) :
    DeclarativeGrammar.OptionalYulDefaultParses statementParses
      input.declarativeRemainder (defaultBody.map (fun body => body.span))
        (defaultBody.map (fun body => body.body))
          next.declarativeRemainder := by
  unfold optionalDefault getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨marker, afterMarker, markerResult, bodyStage⟩
    rcases bind_ok_components bodyStage with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    exact .present marker.span body.span
      (keyword_success_exactTokenParses .defaultKw .yulStatement markerResult)
      (yulBlock_success_sound statement statementParses statementReflects
        statementSound diagnosticFree bodyResult)
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (keywordAbsentAt_of_isKeyword_eq_false .defaultKw absent)

end Solcore.Syntax.Parser.YulControl
