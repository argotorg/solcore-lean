import Solcore.Syntax.Parser.FunctionDeclSoundnessProperties
import Solcore.Syntax.Parser.ImplProperties

/-! Parametric diagnostic-free soundness for one implementation method. -/

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

namespace ImplInternals

/-- One implementation method reflects diagnostic freedom through its body. -/
theorem implMethod_reflectsDiagnosticFreeOnSuccess
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow))) :
    Parser.ReflectsDiagnosticFreeOnSuccess implMethod := by
  unfold implMethod
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (functionDecl_reflectsDiagnosticFreeOnSuccess .module bodyReflects)
  intro declaration
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/--
Every diagnostic-free method success is an exact module-policy function over
the supplied parser-independent block grammar.
-/
theorem implMethod_success_sound
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {method : ImplMethod}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implMethod input = .ok method next) :
    DeclarativeGrammar.ImplMethodParses bodyParses
      input.declarativeRemainder method next.declarativeRemainder := by
  unfold implMethod at result
  rcases bind_ok_components result with
    ⟨declaration, afterDeclaration, declarationResult, finished⟩
  cases finished
  exact .parsed (functionDecl_success_sound .module bodyParses bodyReflects
    bodySound diagnosticFree declarationResult)

/-- Parametric method grammar soundness composes with source validity. -/
theorem implMethod_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
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
    {input next : State} {method : ImplMethod}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implMethod input = .ok method next) :
    DeclarativeGrammar.ImplMethodParses bodyParses
        input.declarativeRemainder method next.declarativeRemainder ∧
      ImplMethod.ValidFor statementValid input.file method := by
  refine ⟨implMethod_success_sound bodyParses bodyReflects bodySound
    diagnosticFree result, ?_⟩
  have valid := implMethod_validFor statementValid bodyValid input inputValid
  rw [result] at valid
  exact valid.1

end ImplInternals

end Solcore.Syntax.Parser
