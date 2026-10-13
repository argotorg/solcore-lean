import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodInvocationBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodySupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRootBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaParameterAdmission

/-! The genuine method parameter entry supplies admission and the complete
physical cache. Strict expression induction closes the actual terminal body;
the static support carries neither body execution nor a semantic callback. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodTerminalBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationMethodBodySupport (Packet Support)
open SelectedCompilationMethodRootBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
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

include support selected keyPhysical in
private theorem preserves_children (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow bodyBridge packet.sourceAt.context
      model stages child point faults budget := by
  obtain ⟨root⟩ := support.roots child selected
  intro size within
  have bound : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots packet.sourceAt.context model stages child point faults size :=
    children size within root.toRootAt owner keyPhysical
  rw [root.prefixLength] at bound
  intro current id code
  exact bound

include support selected keyPhysical in
private theorem reflects_children (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow bodyBridge packet.sourceAt.context
      model stages child point faults budget := by
  obtain ⟨root⟩ := support.roots child selected
  intro size within
  have bound : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots packet.sourceAt.context model stages child point faults size :=
    children size within root.toRootAt owner keyPhysical
  rw [root.prefixLength] at bound
  intro current id code
  exact bound

include support certified selected keyPhysical beforeTyped argumentsTyped stable in
/-- The genuine installed frame and marked allocation establish every body
admission field before the strict expression law is used. -/
theorem source_continuation (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    SourceContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata _owned history _emitted entry _added _length _spine reached _related physical slots
  intro size finalContext bodyOutcome outcome after trace matched within
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨_, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := ⟨⟨reached, slots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet certified beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  have view : LambdaMetadataViews.MetadataView child.source principal.sourceBody.source := sourceEq ▸ .refl _
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    SelectedCompilationMethodBodySupport.statements principal packet certified
  rw [← sourceEq] at bodyTyped
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ packet.sourceAt.unique
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
      frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.preserves_body
      (receipt := packet.receipt) (view := view) (bridge := bodyBridge)
      (bodyTyped := bodyTyped) (complete := completes) (certifies := fun lowered accepted =>
        show point _ _ lowered from ⟨rfl, rfl, Except.ok.inj (accepted.symm.trans packet.receipt.generated)⟩)
      (environments := entry.environments) (heaps := entry.heaps) (locals := entry.locals)
      (agrees := entry.lookups) (typed := entry.actualTyped) (initial := initial) (admitted := admitted)
      unique budget (preserves_children principal packet support functions selected owner keyPhysical budget children)
      trace matched (Nat.le_of_lt within)
  refine ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, ⟨returned.base.val, related⟩, ?_⟩
  intro value same
  cases same
  exact SelectedCompilationMethodPostAdmission.preserved principal packet.sourceAt certified
    post.at_value.1 post.at_value.2.heap metadata

include support certified selected keyPhysical beforeTyped argumentsTyped stable in
/-- Reflection uses the measured native body grade and constructs an
independently sized original Source body at the same reached entry. -/
theorem native_continuation (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size) :
    NativeContinuation (registry := registry) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys) (owner := owner) (caller := caller)
      (arguments := arguments) (payloads := payloads) (stages := stages) (child := child) (faults := faults)
      principal.cached.compilation packet.sourceAt functions installed budget := by
  intro originId index metadata prefixSize bodyStore _owned history _prefixWithin value finalStore _restored
    entry _added _length _spine reached _related physical slots within
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨_, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := ⟨⟨reached, slots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet certified beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  have view : LambdaMetadataViews.MetadataView child.source principal.sourceBody.source := sourceEq ▸ .refl _
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    SelectedCompilationMethodBodySupport.statements principal packet certified
  rw [← sourceEq] at bodyTyped
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ packet.sourceAt.unique
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, result, heaps, maps, worlds,
      frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.reflects_body
      (receipt := packet.receipt) (view := view) (bridge := bodyBridge)
      (bodyTyped := bodyTyped) (complete := completes) (certifies := fun lowered accepted =>
        show point _ _ lowered from ⟨rfl, rfl, Except.ok.inj (accepted.symm.trans packet.receipt.generated)⟩)
      (environments := entry.environments) (heaps := entry.heaps) (locals := entry.locals)
      (agrees := entry.lookups) (typed := entry.actualTyped) (initial := initial) (admitted := admitted)
      unique budget (reflects_children principal packet support functions selected owner keyPhysical budget children)
      entry.completed (Nat.le_of_lt within)
  refine ⟨sourceSize, packet.sourceAt.context, CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome,
    outcome, after, finalMap, finalWorld, trace, matched, result, heaps, maps, worlds,
    frame, metadata, ⟨returned.base.val, related⟩, ?_⟩
  intro value same
  cases same
  exact SelectedCompilationMethodPostAdmission.preserved principal packet.sourceAt certified
    post.at_value.1 post.at_value.2.heap metadata

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodTerminalBounds
