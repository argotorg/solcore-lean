import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Signature

/-! Success soundness for ordered function modifiers and location policy. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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

/-- One optional modifier preserves keyword priority and exact state. -/
theorem optionalFunctionModifier_success_sound (keywordValue : HardKeyword)
    {input next : State} {marker : Option SourceSpan}
    (result : optionalFunctionModifier keywordValue input = .ok marker next) :
    DeclarativeGrammar.OptionalFunctionModifierParses keywordValue
      input.declarativeRemainder marker next.declarativeRemainder := by
  unfold optionalFunctionModifier getState at result
  simp only [bind] at result
  by_cases present : isKeyword input keywordValue
  · simp only [present, if_true] at result
    cases markerResult : keyword keywordValue .parameter input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok token afterMarker =>
        simp only [markerResult, pure] at result
        cases result
        exact .present token.span
          (keyword_success_exactTokenParses keywordValue .parameter
            markerResult)
  · have absent : isKeyword input keywordValue = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (keywordAbsentAt_of_isKeyword_eq_false keywordValue absent)

/-- Ordered modifier grammar soundness composes with source validity. -/
theorem optionalFunctionModifier_success_sound_and_validFor
    (keywordValue : HardKeyword) {input next : State}
    {marker : Option SourceSpan} (inputValid : input.ValidFor)
    (result : optionalFunctionModifier keywordValue input = .ok marker next) :
    DeclarativeGrammar.OptionalFunctionModifierParses keywordValue
        input.declarativeRemainder marker next.declarativeRemainder ∧
      Option.ValidFor (fun file span => span.ValidFor file) input.file
        marker := by
  refine ⟨optionalFunctionModifier_success_sound keywordValue result, ?_⟩
  have valid := optionalFunctionModifier_validFor keywordValue input inputValid
  rw [result] at valid
  exact valid.1

/-- Every success retains the fixed optional `public`-then-`payable` order. -/
theorem functionModifiers_success_sound (location : FunctionLocation)
    {input next : State} {modifiers : FunctionModifiers}
    (result : functionModifiers location input = .ok modifiers next) :
    DeclarativeGrammar.FunctionModifiersParses input.declarativeRemainder
      modifiers next.declarativeRemainder := by
  unfold functionModifiers at result
  rcases bind_ok_components result with
    ⟨publicMarker, afterPublic, publicResult, rest⟩
  rcases bind_ok_components rest with
    ⟨payableMarker, afterPayable, payableResult, finished⟩
  have publicGrammar := optionalFunctionModifier_success_sound .publicKw
    publicResult
  have payableGrammar := optionalFunctionModifier_success_sound .payableKw
    payableResult
  cases location <;> cases publicMarker <;> cases payableMarker <;>
    cases finished <;>
    exact ⟨afterPublic.declarativeRemainder, publicGrammar,
      by simpa only [State.declarativeRemainder, State.emit]
        using payableGrammar⟩

/-- Function-modifier grammar soundness composes with source validity. -/
theorem functionModifiers_success_sound_and_validFor
    (location : FunctionLocation) {input next : State}
    {modifiers : FunctionModifiers} (inputValid : input.ValidFor)
    (result : functionModifiers location input = .ok modifiers next) :
    DeclarativeGrammar.FunctionModifiersParses input.declarativeRemainder
        modifiers next.declarativeRemainder ∧
      FunctionModifiers.ValidFor input.file modifiers := by
  refine ⟨functionModifiers_success_sound location result, ?_⟩
  have valid := functionModifiers_validFor location input inputValid
  rw [result] at valid
  exact valid.1

/-- Diagnostic-free module modifier success contains no contract marker. -/
theorem functionModifiers_module_success_allowed {input next : State}
    {modifiers : FunctionModifiers} (diagnosticFree : next.diagnosticsRev = [])
    (result : functionModifiers .module input = .ok modifiers next) :
    DeclarativeGrammar.ModuleFunctionModifiersAllowed modifiers := by
  unfold functionModifiers at result
  rcases bind_ok_components result with
    ⟨publicMarker, afterPublic, publicResult, rest⟩
  rcases bind_ok_components rest with
    ⟨payableMarker, afterPayable, payableResult, finished⟩
  cases publicMarker with
  | none =>
      cases payableMarker with
      | none =>
          cases finished
          exact ⟨rfl, rfl⟩
      | some payableSpan =>
          cases finished
          simp [State.emit] at diagnosticFree
  | some publicSpan =>
      cases payableMarker <;> cases finished <;>
        simp [State.emit] at diagnosticFree

/-- Every contract modifier success satisfies the contract location policy. -/
theorem functionModifiers_contract_success_allowed {input next : State}
    {modifiers : FunctionModifiers}
    (_result : functionModifiers .contract input = .ok modifiers next) :
    DeclarativeGrammar.ContractFunctionModifiersAllowed modifiers := by
  trivial

end Solcore.Syntax.Parser
