import Solcore.Syntax.Parser.ContractEntryModifierSoundnessProperties

/-! Parametric diagnostic-free soundness for constructors and fallbacks. -/

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

/--
Every diagnostic-free constructor success retains its exact marker,
parameters, strict modifier policy, and parser-independent required body.
-/
theorem constructorDecl_success_sound
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ConstructorDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : constructorDecl input = .ok declaration next) :
    DeclarativeGrammar.ConstructorDeclParses bodyParses
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold constructorDecl at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases bind_ok_components rest with
    ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
  rcases bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterModifiersFree := bodyReflects afterModifiers body next
    bodyResult diagnosticFree
  have afterParametersFree :=
    ContractEntryInternals.implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
      .constructorKw afterParameters payableMarker afterModifiers
      modifiersResult afterModifiersFree
  exact .parsed marker.span
    (keyword_success_exactTokenParses .constructorKw .contractMember
      markerResult)
    (ContractEntryInternals.entryParameters_success_sound
      afterParametersFree parametersResult)
    (ContractEntryInternals.implicitPublicModifiers_success_sound
      .constructorKw afterModifiersFree modifiersResult)
    (bodySound diagnosticFree bodyResult)

/-- Constructor grammar soundness composes with retained-source validity. -/
theorem constructorDecl_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyValid : (block .require).ValidFor
      (Block.ValidFor statementValid))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ConstructorDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : constructorDecl input = .ok declaration next) :
    DeclarativeGrammar.ConstructorDeclParses bodyParses
        input.declarativeRemainder declaration next.declarativeRemainder ∧
      ConstructorDecl.ValidFor statementValid input.file declaration := by
  refine ⟨constructorDecl_success_sound bodyParses bodyReflects bodySound
    diagnosticFree result, ?_⟩
  have valid := constructorDecl_validFor statementValid bodyValid input
    inputValid
  rw [result] at valid
  exact valid.1

/--
Every diagnostic-free fallback success uses an empty parameter list and
retains the exact strict modifier and required-body grammar.
-/
theorem fallbackDecl_success_sound
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : FallbackDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : fallbackDecl input = .ok declaration next) :
    DeclarativeGrammar.FallbackDeclParses bodyParses
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold fallbackDecl at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  by_cases empty : parameters.elements.isEmpty
  · simp only [empty, if_true] at rest
    rcases bind_ok_components rest with
      ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
    rcases bind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    have afterModifiersFree := bodyReflects afterModifiers body next
      bodyResult diagnosticFree
    have afterParametersFree :=
      ContractEntryInternals.implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
        .fallbackKw afterParameters payableMarker afterModifiers
        modifiersResult afterModifiersFree
    exact .parsed marker.span
      (keyword_success_exactTokenParses .fallbackKw .contractMember
        markerResult)
      (ContractEntryInternals.entryParameters_success_sound
        afterParametersFree parametersResult)
      (List.nil_of_isEmpty empty)
      (ContractEntryInternals.implicitPublicModifiers_success_sound
        .fallbackKw afterModifiersFree modifiersResult)
      (bodySound diagnosticFree bodyResult)
  · simp only [empty, Bool.false_eq_true, if_false] at rest
    rcases bind_ok_components rest with
      ⟨validation, afterValidation, validationResult, rest⟩
    rcases bind_ok_components rest with
      ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
    rcases bind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    have afterModifiersFree := bodyReflects afterModifiers body next
      bodyResult diagnosticFree
    have afterValidationFree :=
      ContractEntryInternals.implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
        .fallbackKw afterValidation payableMarker afterModifiers
        modifiersResult afterModifiersFree
    unfold emitDiagnostic modifyState at validationResult
    cases validationResult
    simp [State.emit] at afterValidationFree

/-- Fallback grammar soundness composes with retained-source validity. -/
theorem fallbackDecl_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyValid : (block .require).ValidFor
      (Block.ValidFor statementValid))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : FallbackDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : fallbackDecl input = .ok declaration next) :
    DeclarativeGrammar.FallbackDeclParses bodyParses
        input.declarativeRemainder declaration next.declarativeRemainder ∧
      FallbackDecl.ValidFor statementValid input.file declaration := by
  refine ⟨fallbackDecl_success_sound bodyParses bodyReflects bodySound
    diagnosticFree result, ?_⟩
  have valid := fallbackDecl_validFor statementValid bodyValid input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
