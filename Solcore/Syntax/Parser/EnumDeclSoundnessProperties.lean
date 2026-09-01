import Solcore.Syntax.Parser.EnumBodySoundnessProperties
import Solcore.Syntax.Parser.GenericParametersSoundnessProperties

/-! Success soundness for complete algebraic enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem enumDeclBind_success_components {alpha beta : Type}
    {first : Parser alpha} {nextParser : alpha → Parser beta}
    {input final : State} {value : beta}
    (result : (first >>= nextParser) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        nextParser firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => nextParser firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected =>
      rw [firstResult] at result
      contradiction
  | invariant error =>
      rw [firstResult] at result
      contradiction

/-- Every successful enum declaration follows its exact retained grammar. -/
theorem enumDecl_success_sound (deriveAttribute : Option DeriveAttribute)
    {input next : State} {declaration : EnumDecl}
    (result : enumDecl deriveAttribute input = .ok declaration next) :
    DeclarativeGrammar.EnumDeclParses deriveAttribute
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold enumDecl at result
  rcases enumDeclBind_success_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases enumDeclBind_success_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases enumDeclBind_success_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases enumDeclBind_success_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (contextual_success_exactTokenParses .enum .topItem markerResult)
    (identifier_success_sound .topItem nameResult)
    (optionalGenericParameters_success_sound parametersResult)
    (EnumInternals.enumBody_success_sound bodyResult)

/-- Enum grammar soundness composes with the supplied derive contract. -/
theorem enumDecl_success_sound_and_validFor
    (deriveAttribute : Option DeriveAttribute)
    {input next : State} {declaration : EnumDecl}
    (inputValid : input.ValidFor)
    (deriveValid : Option.ValidFor DeriveAttribute.ValidFor input.file
      deriveAttribute)
    (deriveStartsBeforeCurrent : ∀ derive ∈ deriveAttribute,
      derive.span.startByte ≤ input.currentSpan.startByte)
    (result : enumDecl deriveAttribute input = .ok declaration next) :
    DeclarativeGrammar.EnumDeclParses deriveAttribute
        input.declarativeRemainder declaration next.declarativeRemainder ∧
      EnumDecl.ValidFor input.file declaration := by
  refine ⟨enumDecl_success_sound deriveAttribute result, ?_⟩
  have valid := enumDecl_validFor deriveAttribute inputValid deriveValid
    deriveStartsBeforeCurrent
  rw [result] at valid
  exact valid.1

/-- The no-derive enum parser has unconditional grammar and validity soundness. -/
theorem enumDecl_none_success_sound_and_validFor
    {input next : State} {declaration : EnumDecl}
    (inputValid : input.ValidFor)
    (result : enumDecl none input = .ok declaration next) :
    DeclarativeGrammar.EnumDeclParses none input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      EnumDecl.ValidFor input.file declaration := by
  exact enumDecl_success_sound_and_validFor none inputValid
    (by trivial) (by simp) result

end Solcore.Syntax.Parser
