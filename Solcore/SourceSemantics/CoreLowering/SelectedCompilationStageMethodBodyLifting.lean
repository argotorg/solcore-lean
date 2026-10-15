import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodInvocationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodies
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodScopedLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodTerminalLifting

/-! Static method packet dispatch preserves the same genuine parameter entry
and current physical authority in either body form. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodBodyLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open SelectedCompilationMethodBodies (Packet Support)
open SelectedCompilationMixedRootBounds
open SelectedCompilationStageLiftBounds (LiftsRootsAt)
open SelectedCompilationStageMethodInvocationLifting

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod} (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (support : Support principal packet headers stages semanticFaults)
  (certified : SelectedCompilationMethodBodySupport.Certified principal packet.sourceAt)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
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

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled registry
    (fun reason token => faults (.semantic reason) token))

include support certified selected keyPhysical beforeTyped argumentsTyped stable semantic faithful observations assignmentInterpretation in
theorem source_continuation
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (budget : Nat)
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults size)
    (preservation : ∀ size, PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    LiftContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  cases packet with
  | terminal packet =>
    exact SelectedCompilationStageMethodTerminalLifting.source_continuation
      principal packet support certified functions selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable budget
      children
  | «scoped» packet =>
    exact SelectedCompilationStageMethodScopedLifting.source_continuation (semantic := semantic) (assignmentInterpretation := assignmentInterpretation)
      principal packet support certified functions faithful observations selected installed owner keyPhysical caller
      beforeTyped argumentsTyped stable extension budget children preservation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodBodyLifting
