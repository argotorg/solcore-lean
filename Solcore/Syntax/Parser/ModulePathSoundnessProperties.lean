import Solcore.Syntax.Parser.ModulePath
import Solcore.Syntax.Parser.QualifiedNameSoundnessProperties

/-! Success soundness of canonical module-path parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful module-path parse follows the independent token grammar. -/
theorem modulePath_success_sound (context : ParseContext)
    {input next : State} {path : ModulePath}
    (result : modulePath context input = .ok path next) :
    DeclarativeGrammar.ModulePathParses input.declarativeRemainder path
      next.declarativeRemainder := by
  unfold modulePath at result
  split at result
  · cases markerResult : symbol .at context input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        have markerSound := symbol_ok_tokenAt .at context markerResult
        simp only [markerResult] at result
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name final =>
            have nameSound := qualifiedName_success_sound context .topLevel
              nameResult
            simp only [nameResult] at result
            cases result
            apply DeclarativeGrammar.ModulePathParses.externalPackage
              marker.span markerSound.1
            simpa only [markerSound.2, State.declarativeRemainder,
              State.tokens, State.window, State.cursor] using nameSound
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name final =>
        have nameSound := qualifiedName_success_sound context .topLevel
          nameResult
        simp only [nameResult] at result
        cases result
        exact DeclarativeGrammar.ModulePathParses.local nameSound

/-- Success soundness composes with the established source-provenance contract. -/
theorem modulePath_success_sound_and_validFor (context : ParseContext)
    {input next : State} {path : ModulePath} (inputValid : input.ValidFor)
    (result : modulePath context input = .ok path next) :
    DeclarativeGrammar.ModulePathParses input.declarativeRemainder path
        next.declarativeRemainder ∧
      path.ValidFor input.file := by
  refine ⟨modulePath_success_sound context result, ?_⟩
  have valid := modulePath_validFor context input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
