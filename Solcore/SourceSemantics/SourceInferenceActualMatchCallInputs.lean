import Solcore.SourceSemantics.SourceInferenceActualCallProperties

/-! Actual pattern and arm computations supply the next match-call inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ChildStep

theorem inputs_matchCases
    {fuel : Nat} {context : SourceInference.Context} {scrutinee expected : Ty}
    {saved : LexicalScope} {sources : List Syntax.MatchCase}
    {initial : State} {result : MatchCasesResult} {child : CallIndex}
    (inputs : (CallIndex.matchCases fuel context scrutinee expected saved sources initial result).Inputs)
    (step : ChildStep (.matchCases fuel context scrutinee expected saved sources initial result) child) : child.Inputs := by
  cases step with
  | matchCases_body _ patternAccepted _ =>
      have patternProperties := inferMatchPatternFuel_inferenceProperties inputs.ready inputs.bounds.1 inputs.catalog.formation patternAccepted
      exact ⟨patternProperties.2.1, (inferMatchPatternFuel_direct_progress patternAccepted).wellFormed inputs.wellFormed,
        inputs.catalog, inputs.bounds.2.1.weaken patternProperties.1.next_le⟩
  | matchCases_tail _ patternAccepted bodyAccepted _ =>
      have patternProperties := inferMatchPatternFuel_inferenceProperties inputs.ready inputs.bounds.1 inputs.catalog.formation patternAccepted
      have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1 inputs.catalog.formation inputs.catalog.canonical
        (inputs.bounds.2.1.weaken patternProperties.1.next_le) bodyAccepted
      have through := patternProperties.1.trans bodyProperties.1
      have restoredReady := (State.restoreLexicalScope_inferenceProperties inputs.ready through).2
      simp only [CallIndex.initial] at restoredReady
      rw [inputs.bounds.2.2] at restoredReady
      exact ⟨restoredReady, (inferStatementsFuel_direct_progress bodyAccepted).wellFormed
        ((inferMatchPatternFuel_direct_progress patternAccepted).wellFormed inputs.wellFormed),
        inputs.catalog, inputs.bounds.1.weaken through.next_le,
        inputs.bounds.2.1.weaken through.next_le, rfl⟩

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
