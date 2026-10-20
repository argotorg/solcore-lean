import Solcore.SourceSemantics.SourceCompiledBodySelection
import Solcore.SourceSemantics.SourceInferenceActualCallGraph

/-! A selected ordinary or method body supplies the exact root inference call
from its successful checker receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution

namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

def inferenceCall (selected : BodySelection compiled row fuel) : CallIndex :=
  .statements fuel
    (context compiled.program.environment compiled.program.signatures
      selected.signature selected.body.declaration)
    selected.signature.source.value.body.value
    (Ty.productMany selected.signature.returnTypes)
    (initial selected.signature selected.body.declaration)
    selected.body.body

theorem inferenceCall_accepted (selected : BodySelection compiled row fuel) :
    selected.inferenceCall.Accepted :=
  selected.body.inferred

def InferenceCall (selected : BodySelection compiled row fuel) : CallIndex → Prop :=
  CallOccurrence selected.inferenceCall

theorem inferenceCall_root (selected : BodySelection compiled row fuel) :
    selected.InferenceCall selected.inferenceCall :=
  .root selected.inferenceCall_accepted

theorem inferenceCall_closed (selected : BodySelection compiled row fuel) :
    ChildClosed selected.InferenceCall :=
  CallOccurrence.childClosed selected.inferenceCall

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
