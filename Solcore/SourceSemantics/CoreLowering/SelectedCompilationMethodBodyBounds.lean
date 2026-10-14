import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodInvocationBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodies
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodTerminalBounds

/-! Static method packet dispatch preserves the same genuine parameter entry
and current physical authority in either body form. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open SelectedCompilationMethodBodies (Packet Support)
open SelectedCompilationMixedRootBounds
open SelectedCompilationMethodInvocationBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (support : Support principal packet headers stages semanticFaults)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure principal.sourceFunction child)
  {administrative : Core.Context} {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : CallablePreparedMethodRuntimeMeaning.Installed principal.cached.compilation
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := principal.sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped principal.sourceFunction.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes principal.sourceFunction.context before arguments packet.sourceAt.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)


variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
include support certified selected keyPhysical beforeTyped argumentsTyped stable semantic in
theorem source_continuation
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    SourceContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  cases packet with
  | terminal packet =>
    exact SelectedCompilationMethodTerminalBounds.source_continuation
      principal packet support certified functions selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable budget
      (fun size smaller _context _invocation _scope _expression _lowered root owner physical =>
        children size smaller
          (SelectedCompilationMixedRootSupport.RootAt.ofMethod root) owner physical)
  | «scoped» packet =>
    exact SelectedCompilationMethodScopedBounds.source_continuation (semantic := semantic)
      principal packet support certified functions selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable extension budget children

include support certified selected keyPhysical beforeTyped argumentsTyped stable semantic in
theorem native_continuation
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    NativeContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  cases packet with
  | terminal packet =>
    exact SelectedCompilationMethodTerminalBounds.native_continuation
      principal packet support certified functions selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable budget
      (fun size smaller _context _invocation _scope _expression _lowered root owner physical =>
        children size smaller
          (SelectedCompilationMixedRootSupport.RootAt.ofMethod root) owner physical)
  | «scoped» packet =>
    exact SelectedCompilationMethodScopedBounds.native_continuation (semantic := semantic)
      principal packet support certified functions selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable extension budget children

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodyBounds
