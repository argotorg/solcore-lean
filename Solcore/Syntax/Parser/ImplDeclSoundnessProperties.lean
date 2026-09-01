import Solcore.Syntax.Parser.GenericParametersSoundnessProperties
import Solcore.Syntax.Parser.ImplBodySoundnessProperties
import Solcore.Syntax.Parser.ImplHeadSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseSoundnessProperties

/-! Parametric diagnostic-free soundness for implementation declarations. -/

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

/-!
Implementation parsing reflects diagnostic freedom whenever the isolated block
parser used by its methods does.  The nonempty-head refinement is included
explicitly so the whole executable bind chain remains visible.
-/
theorem implDecl_reflectsDiagnosticFreeOnSuccess
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow))) :
    Parser.ReflectsDiagnosticFreeOnSuccess implDecl := by
  unfold implDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    ImplInternals.implDefaultMarker_reflectsDiagnosticFreeOnSuccess
  intro defaultMarker
  unfold ImplInternals.implDeclAfterDefault
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .impl .topItem)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalGenericParameters_reflectsDiagnosticFreeOnSuccess
  intro genericParameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .topItem)
  intro traitName
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .less .greater false typeExpr
      .typeExpr .topLevel typeExpr_reflectsDiagnosticFreeOnSuccess)
  intro arguments
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (ImplInternals.requireImplArguments_reflectsDiagnosticFreeOnSuccess
      arguments)
  intro headArguments
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    whereClause_reflectsDiagnosticFreeOnSuccess
  intro parsedWhereClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (ImplInternals.implBody_reflectsDiagnosticFreeOnSuccess bodyReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-!
Every diagnostic-free implementation success follows the exact optional
`default`, marker, head, where-clause, and method-body grammar.  Function bodies
remain abstract behind `bodyParses`.
-/
theorem implDecl_success_sound
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ImplDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implDecl input = .ok declaration next) :
    DeclarativeGrammar.ImplDeclParses bodyParses
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold implDecl at result
  rcases bind_ok_components result with
    ⟨defaultMarker, afterDefault, defaultResult, suffix⟩
  unfold ImplInternals.implDeclAfterDefault at suffix
  rcases bind_ok_components suffix with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨traitName, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨arguments, afterValues, valuesResult, rest⟩
  rcases bind_ok_components rest with
    ⟨headArguments, afterArguments, argumentsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨parsedWhereClause, afterWhere, whereResult, rest⟩
  rcases bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (ImplInternals.implDefaultMarker_success_sound defaultResult)
    (contextual_success_exactTokenParses .impl .topItem markerResult)
    (optionalGenericParameters_success_sound genericsResult)
    (identifier_success_sound .topItem nameResult)
    (ImplInternals.implHeadArguments_success_sound valuesResult
      argumentsResult)
    (whereClause_success_sound whereResult)
    (ImplInternals.implBody_success_sound bodyParses bodyReflects bodySound
      diagnosticFree bodyResult)

/-! Parametric implementation grammar soundness composes with source validity. -/
theorem implDecl_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ImplDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implDecl input = .ok declaration next) :
    DeclarativeGrammar.ImplDeclParses bodyParses input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      ImplDecl.ValidFor statementValid input.file declaration := by
  refine ⟨implDecl_success_sound bodyParses bodyReflects bodySound
    diagnosticFree result, ?_⟩
  have valid := implDecl_validFor statementValid bodyValid bodyWindow
    input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
