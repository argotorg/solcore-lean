import Solcore.Syntax.Parser.ContractEntryDiagnosticReflectionProperties
import Solcore.Syntax.Parser.ContractEntryProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.FunctionParametersSoundnessProperties

/-! Diagnostic-free soundness for constructor and fallback modifiers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractEntryInternals

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

/-- Contract-entry parameters reuse the exact function-parameter grammar. -/
theorem entryParameters_success_sound {input next : State}
    {parameters : DelimitedList FunctionParameter}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : entryParameters input = .ok parameters next) :
    DeclarativeGrammar.FunctionParametersParses input.declarativeRemainder
      parameters next.declarativeRemainder := by
  simpa only [entryParameters, functionParameters] using
    functionParameters_success_sound diagnosticFree result

/-- Parameter grammar soundness composes with retained-source validity. -/
theorem entryParameters_success_sound_and_validFor {input next : State}
    {parameters : DelimitedList FunctionParameter} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : entryParameters input = .ok parameters next) :
    DeclarativeGrammar.FunctionParametersParses input.declarativeRemainder
        parameters next.declarativeRemainder ∧
      DelimitedList.ValidFor FunctionParameter.ValidFor input.file
        parameters := by
  refine ⟨entryParameters_success_sound diagnosticFree result, ?_⟩
  have valid := entryParameters_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- One optional contract-entry modifier preserves exact keyword priority. -/
theorem optionalModifier_success_sound (modifier : HardKeyword)
    {input next : State} {marker : Option SourceSpan}
    (result : optionalModifier modifier input = .ok marker next) :
    DeclarativeGrammar.OptionalFunctionModifierParses modifier
      input.declarativeRemainder marker next.declarativeRemainder := by
  unfold optionalModifier getState at result
  simp only [bind] at result
  by_cases present : isKeyword input modifier
  · simp only [present, if_true] at result
    cases markerResult : keyword modifier .contractMember input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok token afterMarker =>
        simp only [markerResult, pure] at result
        cases result
        exact .present token.span
          (keyword_success_exactTokenParses modifier .contractMember
            markerResult)
  · have absent : isKeyword input modifier = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (keywordAbsentAt_of_isKeyword_eq_false modifier absent)

private theorem optionalModifier_none_success
    (modifier : HardKeyword) {input next : State}
    (result : optionalModifier modifier input = .ok none next) :
    next = input ∧
      DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.keyword modifier) := by
  unfold optionalModifier getState at result
  simp only [bind] at result
  by_cases present : isKeyword input modifier
  · simp only [present, if_true] at result
    cases markerResult : keyword modifier .contractMember input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok token afterMarker =>
        simp only [markerResult, pure] at result
        injection result with valueEq stateEq
        contradiction
  · have absent : isKeyword input modifier = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact ⟨rfl, keywordAbsentAt_of_isKeyword_eq_false modifier absent⟩

/--
Diagnostic-free implicit-public handling excludes `public` and retains the
exact optional `payable` token.
-/
theorem implicitPublicModifiers_success_sound (declaration : HardKeyword)
    {input next : State} {payableMarker : Option SourceSpan}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implicitPublicModifiers declaration input =
      .ok payableMarker next) :
    DeclarativeGrammar.ContractEntryModifiersParses
      input.declarativeRemainder payableMarker next.declarativeRemainder := by
  unfold implicitPublicModifiers at result
  rcases bind_ok_components result with
    ⟨publicMarker, afterPublic, publicResult, rest⟩
  cases publicMarker with
  | none =>
      rcases optionalModifier_none_success .publicKw publicResult with
        ⟨rfl, publicAbsent⟩
      have payableGrammar := optionalModifier_success_sound .payableKw rest
      exact ⟨publicAbsent, payableGrammar⟩
  | some publicSpan =>
      rcases bind_ok_components rest with
        ⟨emitted, afterDiagnostic, diagnosticResult, payableResult⟩
      have afterDiagnosticFree :=
        optionalModifier_reflectsDiagnosticFreeOnSuccess .payableKw
          afterDiagnostic payableMarker next payableResult diagnosticFree
      unfold emitDiagnostic modifyState at diagnosticResult
      cases diagnosticResult
      simp [State.emit] at afterDiagnosticFree

/-- Modifier grammar soundness composes with retained-source validity. -/
theorem implicitPublicModifiers_success_sound_and_validFor
    (declaration : HardKeyword) {input next : State}
    {payableMarker : Option SourceSpan} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implicitPublicModifiers declaration input =
      .ok payableMarker next) :
    DeclarativeGrammar.ContractEntryModifiersParses
        input.declarativeRemainder payableMarker next.declarativeRemainder ∧
      Option.ValidFor (fun file span => span.ValidFor file) input.file
        payableMarker := by
  refine ⟨implicitPublicModifiers_success_sound declaration diagnosticFree
    result, ?_⟩
  have valid := implicitPublicModifiers_validFor declaration input inputValid
  rw [result] at valid
  exact valid.1

end ContractEntryInternals
end Solcore.Syntax.Parser
