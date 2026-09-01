import Solcore.Syntax.Parser.FunctionProperties
import Solcore.Syntax.Parser.FunctionSignatureDiagnosticReflectionProperties
import Solcore.Syntax.Parser.FunctionSignatureSoundnessProperties

/-! Parametric diagnostic-free soundness for ordinary function declarations. -/

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
Function-declaration parsing reflects diagnostic freedom whenever its isolated
body parser does.  This keeps the executable block implementation out of the
declarative grammar while exposing the exact composition boundary.
-/
theorem functionDecl_reflectsDiagnosticFreeOnSuccess
    (location : FunctionLocation)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow))) :
    Parser.ReflectsDiagnosticFreeOnSuccess (functionDecl location) := by
  unfold functionDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (functionSignature_reflectsDiagnosticFreeOnSuccess location)
  intro signature
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess bodyReflects
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/--
Every diagnostic-free function success follows the exact location-specific
signature policy and the supplied parser-independent body grammar.
-/
theorem functionDecl_success_sound
    (location : FunctionLocation)
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : FunctionDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionDecl location input = .ok declaration next) :
    DeclarativeGrammar.FunctionDeclParses bodyParses
      (match location with
      | .module => DeclarativeGrammar.ModuleFunctionModifiersAllowed
      | .contract => DeclarativeGrammar.ContractFunctionModifiersAllowed)
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold functionDecl at result
  rcases bind_ok_components result with
    ⟨signature, afterSignature, signatureResult, rest⟩
  rcases bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterSignatureFree := bodyReflects afterSignature body next
    bodyResult diagnosticFree
  cases location with
  | module =>
      exact .parsed
        (functionSignature_module_success_sound afterSignatureFree
          signatureResult)
        (bodySound diagnosticFree bodyResult)
  | contract =>
      exact .parsed
        (functionSignature_contract_success_sound afterSignatureFree
          signatureResult)
        (bodySound diagnosticFree bodyResult)

/-- Parametric function grammar soundness composes with source validity. -/
theorem functionDecl_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    (location : FunctionLocation)
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : FunctionDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionDecl location input = .ok declaration next) :
    DeclarativeGrammar.FunctionDeclParses bodyParses
        (match location with
        | .module => DeclarativeGrammar.ModuleFunctionModifiersAllowed
        | .contract => DeclarativeGrammar.ContractFunctionModifiersAllowed)
        input.declarativeRemainder declaration next.declarativeRemainder ∧
      FunctionDecl.ValidFor statementValid input.file declaration := by
  refine ⟨functionDecl_success_sound location bodyParses bodyReflects
    bodySound diagnosticFree result, ?_⟩
  have valid := functionDecl_validFor statementValid location bodyValid
    input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
