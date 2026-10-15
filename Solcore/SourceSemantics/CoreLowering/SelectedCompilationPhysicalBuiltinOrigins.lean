import Solcore.SourceSemantics.CoreLowering.SelectedCompilationBuiltinFunctionOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinArgumentRows

/-! A builtin leaf retains its original compiler receipt inside the prepared
physical model. Projection uses the actual source value and preserves wrappers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBuiltinOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}

theorem builtin_member {sourceType : TypeSystem.Ty} {sourceValue : Dynamic.Value}
    {carrier : Value} {type : Ty}
    (represented : CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry faults profile mapping world sourceType sourceValue carrier type) :
    ∀ function, sourceValue = .builtin function →
      CallableIndexedBuiltinValues.Represents compiled.indexed world
        function.id.type (.builtin function) carrier type := by
  intro function same
  cases same
  exact CallableIndexedOwnedPreparedStagedBuiltinArgumentRows.builtin_member
    (SelectedCompilationBuiltinFunctionOrigins.ErasesBuiltinsToContextual.erase
      (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (profile := profile) represented) function rfl

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBuiltinOrigins
