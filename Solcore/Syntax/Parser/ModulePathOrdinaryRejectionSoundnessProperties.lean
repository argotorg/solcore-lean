import Solcore.Syntax.DeclarativeModulePathOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeQualifiedNameRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.ModulePath

/-! Exact executable rejection reflection for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable module-path rejection comes from the qualified name in
the prioritized local or exact-marker external-package branch. -/
theorem modulePath_reject_ordinaryOutcome_sound (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : modulePath context input = .reject failure rejected) :
    DeclarativeGrammar.ModulePathRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold modulePath at result
  by_cases markerPresent : isSymbol input .at = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .at context markerPresent with
      ⟨marker, markerResult⟩
    simp only [markerPresent, if_true, markerResult] at result
    cases nameResult : qualifiedName context .topLevel
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [nameResult] at result
    | ok name output => simp [nameResult] at result
    | reject nameFailure nameRejected =>
        simp only [nameResult] at result
        cases result
        exact .externalRejected marker.span
          (symbol_success_exactTokenParses .at context markerResult)
          (qualifiedName_reject_type_sound context .topLevel nameResult)
  · have markerAbsent : isSymbol input .at = false :=
      Bool.eq_false_iff.mpr markerPresent
    simp only [markerAbsent, Bool.false_eq_true, if_false] at result
    cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | ok name output => simp [nameResult] at result
    | reject nameFailure nameRejected =>
        simp only [nameResult] at result
        cases result
        exact .localRejected
          (symbolAbsentAt_of_isSymbol_eq_false .at markerAbsent)
          (qualifiedName_reject_type_sound context .topLevel nameResult)

end Solcore.Syntax.Parser
