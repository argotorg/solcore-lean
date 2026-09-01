import Solcore.Syntax.Parser.GenericParametersSoundnessProperties
import Solcore.Syntax.Parser.SignatureLeafDiagnosticReflectionProperties
import Solcore.Syntax.Parser.TraitBodySoundnessProperties
import Solcore.Syntax.Parser.WhereClauseSoundnessProperties

/-! Diagnostic-free success soundness for complete trait declarations. -/

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

/-- Trait declaration parsing cannot erase an incoming diagnostic. -/
theorem traitDecl_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess traitDecl := by
  unfold traitDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .trait .topItem)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .topItem)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    genericParameters_reflectsDiagnosticFreeOnSuccess
  intro genericParameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    whereClause_reflectsDiagnosticFreeOnSuccess
  intro whereClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    TraitInternals.traitBody_reflectsDiagnosticFreeOnSuccess
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Every diagnostic-free trait success follows its exact declaration grammar. -/
theorem traitDecl_success_sound {input next : State} {declaration : TraitDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitDecl input = .ok declaration next) :
    DeclarativeGrammar.TraitDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder := by
  unfold traitDecl at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨whereClause, afterWhere, whereResult, rest⟩
  rcases bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (contextual_success_exactTokenParses .trait .topItem markerResult)
    (identifier_success_sound .topItem nameResult)
    (genericParameters_success_sound genericsResult)
    (whereClause_success_sound whereResult)
    (TraitInternals.traitBody_success_sound diagnosticFree bodyResult)

/-- Trait declaration grammar soundness composes with source validity. -/
theorem traitDecl_success_sound_and_validFor {input next : State}
    {declaration : TraitDecl} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitDecl input = .ok declaration next) :
    DeclarativeGrammar.TraitDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      TraitDecl.ValidFor input.file declaration := by
  refine ⟨traitDecl_success_sound diagnosticFree result, ?_⟩
  have valid := traitDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
