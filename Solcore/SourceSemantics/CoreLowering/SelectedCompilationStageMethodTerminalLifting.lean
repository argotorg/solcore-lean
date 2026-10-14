import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageTerminalInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodInvocationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodySupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRootBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodInvocationLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaParameterAdmission

/-! The genuine method parameter entry supplies admission and the complete
physical cache. Strict expression induction closes the actual terminal body;
the static support carries neither body execution nor a semantic callback. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodTerminalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationMethodBodySupport (Packet Support)
open SelectedCompilationStageLiftBounds (LiftsAt LiftsRootsAt)
open SelectedCompilationStageBodyLiftBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
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
local notation "bodyBridge" => CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
  (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)
local notation "point" => Point (CallablePreparedMethodRuntimeProfileFactory.scope (named := principal.named)) packet.expression packet.receipt.child

include certified beforeTyped argumentsTyped in
private theorem heap_at_parameters {environment : Dynamic.Environment} {after : Dynamic.Heap}
    (allocation : Dynamic.BindersAllocate [] before principal.sourceFunction.parameters arguments environment after) :
    Dynamic.HeapWellTyped packet.sourceAt.context after := by
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq packet.sourceAt.extended
  have rawArguments : Dynamic.ValuesHaveTypes principal.sourceBody.context before arguments
      (principal.sourceBody.source.inputs.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes, principal.source_frame.context] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping
    (principal.source_frame.context ▸ beforeTyped) rawArguments (principal.source_frame.parameters ▸ allocation)
  obtain ⟨_, typed⟩ := SelectedCompilationMethodBodySupport.source_typing principal packet.sourceAt certified
  have runtime := typed.sourceRuntimeValid
  have fields := RecursiveNamedInitialContextValidity.mono_fields packet.sourceAt.extended
  exact allocated.transportClosed fields.signatures runtime.closed (fields.targetClosed runtime.closed)
    runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)

include support certified selected keyPhysical beforeTyped argumentsTyped stable in
/-- The actual method parameter frame supplies heap typing and retained
callable origins before lifting the strictly smaller terminal expression. -/
theorem source_continuation (budget : Nat)
    (children : ∀ size, size < budget → LiftsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults size) :
    LiftContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata _owned history _emitted entry _added _length _spine reached _related physical slots
  intro size finalContext bodyOutcome after trace within
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨_, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := ⟨⟨reached, slots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet certified beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ packet.sourceAt.unique
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal child.source
      packet.expression principal.cached.compilation.statements := sourceEq ▸ packet.receipt.terminal
  obtain ⟨childSize, plain, strict, finalEq, outcomeEq, evaluated⟩ :=
    SelectedCompilationStageTerminalInversion.child_of_body unique terminal trace
  subst finalContext
  subst bodyOutcome
  obtain ⟨node, found, _rawType, typed⟩ := SelectedCompilationMethodBodySupport.child_typed
    principal packet certified selected
  obtain ⟨root⟩ := support.roots child selected
  have meaning : LiftsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots packet.sourceAt.context model stages child point childSize :=
    children childSize (Nat.lt_trans strict within)
      (SelectedCompilationMixedRootSupport.RootAt.ofMethod root.toRootAt) owner keyPhysical
  rw [root.prefixLength] at meaning
  have lifted := meaning ⟨rfl, rfl, rfl⟩ found typed entry.environments entry.heaps entry.locals
    entry.lookups entry.actualTyped initial admitted evaluated
  exact terminal_expression (packet.receipt.head child sourceEq) lifted

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodTerminalLifting
