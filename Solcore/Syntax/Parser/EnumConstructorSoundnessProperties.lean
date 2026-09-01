import Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.EnumProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-! Success soundness for enum constructors and their optional payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

private theorem bind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
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
  | reject failure rejected =>
      rw [firstResult] at parsed
      contradiction
  | invariant error =>
      rw [firstResult] at parsed
      contradiction

/-- Optional constructor fields follow their prioritized no-trailing grammar. -/
theorem enumConstructorFields_success_sound {input next : State}
    {fields : Option (DelimitedList TypeExpr)}
    (result : enumConstructorFields input = .ok fields next) :
    DeclarativeGrammar.OptionalEnumConstructorFieldsParses
      input.declarativeRemainder fields next.declarativeRemainder := by
  unfold enumConstructorFields getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · simp only [present, if_true] at result
    cases fieldsResult : delimitedNoTrailing .leftParen .rightParen true
        typeExpr .typeExpr .topLevel input with
    | invariant error =>
        simp [fieldsResult] at result
    | reject failure rejected =>
        simp [fieldsResult] at result
    | ok values afterValues =>
        have fieldsGrammar := delimitedNoTrailing_allowEmpty_success_sound
          .leftParen .rightParen typeExpr
          DeclarativeGrammar.TypeExprParses .typeExpr .topLevel
          typeExpr_success_sound typeExpr_preservesTokenWindow fieldsResult
        simp only [fieldsResult, pure] at result
        cases result
        exact .present fieldsGrammar
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .leftParen absent)

/-- Optional-field grammar soundness composes with source validity. -/
theorem enumConstructorFields_success_sound_and_validFor
    {input next : State} {fields : Option (DelimitedList TypeExpr)}
    (inputValid : input.ValidFor)
    (result : enumConstructorFields input = .ok fields next) :
    DeclarativeGrammar.OptionalEnumConstructorFieldsParses
        input.declarativeRemainder fields next.declarativeRemainder ∧
      Option.ValidFor (DelimitedList.ValidFor TypeExpr.ValidFor)
        input.file fields := by
  refine ⟨enumConstructorFields_success_sound result, ?_⟩
  have valid := enumConstructorFields_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Every successful enum constructor follows its exact retained grammar. -/
theorem enumConstructor_success_sound {input next : State}
    {constructor : EnumConstructor}
    (result : enumConstructor input = .ok constructor next) :
    DeclarativeGrammar.EnumConstructorParses input.declarativeRemainder
      constructor next.declarativeRemainder := by
  unfold enumConstructor at result
  rcases bind_ok_components result with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨fields, afterFields, fieldsResult, finished⟩
  cases finished
  exact .parsed (identifier_success_sound .topItem nameResult)
    (enumConstructorFields_success_sound fieldsResult)

/-- Constructor grammar soundness composes with source validity. -/
theorem enumConstructor_success_sound_and_validFor {input next : State}
    {constructor : EnumConstructor} (inputValid : input.ValidFor)
    (result : enumConstructor input = .ok constructor next) :
    DeclarativeGrammar.EnumConstructorParses input.declarativeRemainder
        constructor next.declarativeRemainder ∧
      EnumConstructor.ValidFor input.file constructor := by
  refine ⟨enumConstructor_success_sound result, ?_⟩
  have valid := enumConstructor_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.EnumInternals
