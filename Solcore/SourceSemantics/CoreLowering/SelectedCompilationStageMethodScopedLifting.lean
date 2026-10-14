import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodScopedSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodInvocationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageImperativeLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativeFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaParameterAdmission

/-! The actual installed method and marked parameter entry supply admission,
physical cache slots and the frame used by the existing scoped flow engine.
Every reached expression is discharged by the strict mixed root family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodScopedLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationMethodScopedSupport (Packet Support parameterScope nativePrefix)
open SelectedCompilationMixedRootBounds
open SelectedCompilationStageLiftBounds (LiftsAt LiftsRootsAt)
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

include packet in
private theorem prefix_agrees
    {localScope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {map : LocationMap} {typing : StoreTyping} {environment : Dynamic.Environment}
    {administrative : Core.Context} {location : Location}
    (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 localScope canonical)
    (reference : canonical[localScope.length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      map typing (SourceCoreCompatibleCatalog.packTypes (principal.named.inputs.map Prod.snd) :: administrative)
      localScope environment canonical compiled.indexed.layouts.definitions) :
    NativeExpressionContextSupport.Agrees (nativePrefix principal).length (nativePrefix principal)
      (SourceCoreCompatibleCatalog.packTypes (principal.named.inputs.map Prod.snd) :: administrative) := by
  have typed := related.runtime_hasTypes.type_tags
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (SourceCoreLocalCell.coreContext localScope ++
        SourceCoreCompatibleCatalog.packTypes (principal.named.inputs.map Prod.snd) :: administrative)[index]? = some value.type := by
    rw [← typed]
    simp [found]
  intro index smaller
  cases index with
  | zero => simp [nativePrefix, packet.sourceAt.parameterType]
  | succ slot =>
    have bound : slot < compiled.indexed.base.globals.length + 1 := by
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil] at smaller
      omega
    by_cases globalSlot : slot < compiled.indexed.base.globals.length
    · let signature := compiled.indexed.base.globals[slot]
      have selected : compiled.indexed.base.globals[slot]? = some signature :=
        List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
      have atType := tag (slots slot signature selected)
      have outside : ¬ localScope.length + 1 + slot < localScope.length := by omega
      have offset : localScope.length + 1 + slot - localScope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        globalSlot, selected, signature, SourceCoreCalls.Signature.referenceType,
        OptionalCell.referenceType, Value.type] using atType
    · have last : slot = compiled.indexed.base.globals.length := by omega
      have atType := tag reference
      have outside : ¬ localScope.length + 1 + compiled.indexed.base.globals.length < localScope.length := by omega
      have offset : localScope.length + 1 + compiled.indexed.base.globals.length - localScope.length =
          compiled.indexed.base.globals.length + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        last, Value.type] using atType

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)

include support certified selected keyPhysical beforeTyped argumentsTyped stable semantic in
/-- Actual parameter allocation supplies the entire Source body entry. -/
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
  intro originId index metadata _owned history _emitted entry _added _length _spine reached _related physical slots
  intro size finalContext bodyOutcome after trace within
  have prefixAgreement := prefix_agrees principal packet slots entry.reference entry.environments
  have environments := RecursiveNamedLambdaFormationHeads.environments_prefix entry.environments (nativePrefix principal) prefixAgreement
  have agrees : EnvironmentsAgree entry.embedding
      (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)) entry.actualBody :=
    RecursiveNamedLambdaFormationHeads.agrees_prefix entry.lookups
    ((parameterScope principal).length + (nativePrefix principal).length)
  have retainedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 (parameterScope principal)
      (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)) := by
    intro slot signature found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [List.getElem?_take, if_pos]
    · exact slots slot signature found
    · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
  have reference : (entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length))[
      (parameterScope principal).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [List.getElem?_take, if_pos]
    · exact entry.reference
    · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 1).State
      ⟨parameterScope principal, entry.mapping, entry.world, entry.heap, entry.store,
        entry.canonical.take ((parameterScope principal).length + (nativePrefix principal).length)⟩ :=
    ⟨⟨reached, retainedSlots⟩, physical⟩
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable history entry.frame
  have admitted : Admission bodyBridge packet.sourceAt.context initial :=
    ⟨heap_at_parameters principal packet certified beforeTyped argumentsTyped entry.allocation, rows⟩
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨staticFinal, facts, bodyTyped, _completes⟩ :=
    SelectedCompilationMethodScopedSupport.statements principal packet certified
  rw [← sourceEq] at bodyTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source packet.sourceAt.context
      principal.cached.compilation.statements := ⟨_, _, _, bodyTyped⟩
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ packet.sourceAt.unique
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true
      principal.cached.compilation.statements := sourceEq ▸ packet.shape
  obtain ⟨expressionSyntax, collected⟩ := support.tree child selected
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position history
  exact
    SelectedCompilationStageImperativeLifting.lifts_at
      bodyBridge (CallableIndexedOwnedPhysicalCanonicalState.bindings 1)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport 1)
      functions extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer model 1)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner (headers := headers) model 1 stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : LiftsAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages child
            (Point scope id lowered) size := children size smaller root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      (fun context size scope id lowered certified => by
        obtain ⟨root, samePrefix⟩ := certified
        have meaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
              root.compilation.administrativePrefix).forgetSlots context model stages child
            (Point scope id lowered) faults size := preservation size root owner keyPhysical
        rw [samePrefix] at meaning
        intro node
        exact meaning ⟨rfl, rfl, rfl⟩ (node := node))
      unique collected.tree (collected.sites registry) semantic rfl shape originalTyping packet.sourceAt.projection
      (Nat.le_of_lt within) environments entry.heaps entry.locals agrees entry.actualTyped reference entry.read entry.unmapped
      initial conditioned admitted trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodScopedLifting
