import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProxyBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProxyLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds Staging.Recursive.Lifting
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  (unique : NodeOccurrencesUnique invocation.source)

include unique in
/-- A proxy leaf preserves its independent ordinary result and exact heap.
Its original source form has no stage guard or child execution. -/
theorem lifts (size : Nat) :
    LiftsAt bridge context (CompatibleAmbientHeap.payloadModel values.checked rawRegistry functions)
      registry invocation (CompatibleExpressionProxies.Certificate values invocation.source) size := by
  intro scope id lowered certificate node found typed
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  cases certificate with
  | proxy receipt =>
    exact .completed (Staging.Recursive.Lifting.atomic_nonlocal unique
      (lookupExpression?_sound receipt.metadata.found)
      (by rw [receipt.form]; exact .proxy _)
      receipt.metadata.coercions (by intros; simp [receipt.form]) trace.sound)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProxyLifting
