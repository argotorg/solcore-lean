import Solcore.SourceSemantics.SourceCompiledBodyCallIndex
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionContracts
import Solcore.SourceSemantics.SourceInferenceActualCallProperties

/-! Actual inference descent preserves the selected declaration's static
checking context. Changes to loop depth do not introduce a different catalog,
generic owner, type-parameter scope or assumption set. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics
open Frontend SourceInference TypeSystem
open SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness

namespace SourceInferenceExecution
theorem ChildStep.checkingScope
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {parent child : CallIndex}
    (step : ChildStep parent child)
    (scope : CheckingScope selected parent.context) :
    CheckingScope selected child.context := by
  cases step <;> exact ⟨scope.signatures, scope.owner, scope.parameters, scope.assumptions⟩
end SourceInferenceExecution

namespace SourceCompiledLocalFinalization.BodySelection
open SourceInferenceExecution

theorem actualCall_scope
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    {call : CallIndex} (here : selected.InferenceCall call) :
    CheckingScope selected call.context := by
  induction here with
  | root _ => exact CheckingScope.refl selected
  | child _ step ih => exact step.checkingScope ih

end SourceCompiledLocalFinalization.BodySelection
end Solcore.SourceSemantics
