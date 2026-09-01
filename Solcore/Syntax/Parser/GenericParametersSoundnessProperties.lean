import Solcore.Syntax.Parser.DelimitedSoundnessProperties
import Solcore.Syntax.Parser.Signature

/-! Success soundness for shared generic-parameter syntax. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Requiring nonempty generic parameters preserves span, state, and order. -/
theorem requireGenericParameters_success_shape
    {values : DelimitedList Identifier}
    {input next : State} {parameters : GenericParameters}
    (result : requireGenericParameters values input = .ok parameters next) :
    next = input ∧ parameters.span = values.span ∧
      parameters.elements.toList = values.elements := by
  unfold requireGenericParameters at result
  cases elements : values.elements with
  | nil => rw [elements] at result; contradiction
  | cons head tail =>
      rw [elements] at result
      cases result
      exact ⟨rfl, rfl, by simp [NonemptyList.toList]⟩

/-- Every successful generic parameter list follows its exact grammar. -/
theorem genericParameters_success_sound {input next : State}
    {parameters : GenericParameters}
    (result : genericParameters input = .ok parameters next) :
    DeclarativeGrammar.GenericParametersParses input.declarativeRemainder
      parameters next.declarativeRemainder := by
  unfold genericParameters at result
  cases valuesResult : delimited .less .greater false
      (identifier .parameter) .parameter .topLevel input with
  | invariant error =>
      simp [bind, valuesResult] at result
  | reject failure rejected =>
      simp [bind, valuesResult] at result
  | ok values afterValues =>
      have valuesGrammar := delimited_nonempty_trailing_success_sound
        .less .greater (identifier .parameter)
        DeclarativeGrammar.IdentifierParses .parameter .topLevel
        (identifier_success_sound .parameter)
        (identifier_preservesTokenWindow .parameter) valuesResult
      simp only [bind, valuesResult] at result
      have shape := requireGenericParameters_success_shape result
      rw [shape.1]
      unfold DeclarativeGrammar.GenericParametersParses
      simpa only [shape.2.1, shape.2.2] using valuesGrammar

/-- Generic-parameter grammar soundness composes with source validity. -/
theorem genericParameters_success_sound_and_validFor {input next : State}
    {parameters : GenericParameters} (inputValid : input.ValidFor)
    (result : genericParameters input = .ok parameters next) :
    DeclarativeGrammar.GenericParametersParses input.declarativeRemainder
        parameters next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor Located.ValidFor input.file
        parameters := by
  refine ⟨genericParameters_success_sound result, ?_⟩
  have valid := genericParameters_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Optional generic parameters preserve their leading-`<` branch priority. -/
theorem optionalGenericParameters_success_sound {input next : State}
    {parameters : Option GenericParameters}
    (result : optionalGenericParameters input = .ok parameters next) :
    DeclarativeGrammar.OptionalGenericParametersParses
      input.declarativeRemainder parameters next.declarativeRemainder := by
  unfold optionalGenericParameters getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .less
  · simp only [present, if_true] at result
    cases parametersResult : genericParameters input with
    | invariant error => simp [parametersResult] at result
    | reject failure rejected => simp [parametersResult] at result
    | ok values afterValues =>
        simp only [parametersResult, pure] at result
        cases result
        exact .present (genericParameters_success_sound parametersResult)
  · have absent : isSymbol input .less = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .less absent)

/-- Optional generic grammar soundness composes with source validity. -/
theorem optionalGenericParameters_success_sound_and_validFor
    {input next : State} {parameters : Option GenericParameters}
    (inputValid : input.ValidFor)
    (result : optionalGenericParameters input = .ok parameters next) :
    DeclarativeGrammar.OptionalGenericParametersParses
        input.declarativeRemainder parameters next.declarativeRemainder ∧
      Option.ValidFor
        (NonemptyDelimitedList.ValidFor Located.ValidFor)
        input.file parameters := by
  refine ⟨optionalGenericParameters_success_sound result, ?_⟩
  have valid := optionalGenericParameters_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
