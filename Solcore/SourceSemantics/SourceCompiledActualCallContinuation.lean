import Solcore.SourceSemantics.SourceCompiledActualBodyInputs
import Solcore.SourceSemantics.SourceInferenceActualSuffixProgress

/-! The selected checker receipt supplies the continuation of every reached
inference call through the final return check and source finalization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution

namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem actualCall_continuation (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    call.final.InferenceProgress selected.body.body.state :=
  here.suffixProgress (selected.inferenceCall_inputs checked)

theorem actualCall_final_extension (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    selected.body.finalized.substitution.SemanticallyExtends call.final.inference.substitution :=
  (selected.inferenceProgress checked).final_substitution.trans
    (selected.actualCall_continuation checked here).substitution_extends

theorem actualCall_initial_extension (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    selected.body.finalized.substitution.SemanticallyExtends call.initial.inference.substitution :=
  (selected.actualCall_final_extension checked here).trans
    ((selected.actualCall_inputs checked here).progress here.accepted).1.substitution_extends

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
