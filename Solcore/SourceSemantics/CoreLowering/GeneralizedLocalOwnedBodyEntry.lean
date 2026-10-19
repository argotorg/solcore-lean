import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntry
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCellAllocationProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission

/-! The live public authority pool supplies the actual materialized-call entry.
The transient read frame is replaced by the child frame certified by the real
read recipe. Marked parameters retain the same pool and mixed cell relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOwnedBodyEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedParameterMeaning
open GeneralizedLocalDescriptorOrigin

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
  {lexical : TypeSystem.Substitution} (origin : Origin compiled.indexed descriptor binding lexical)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {cells : GenericHeap.CellModel compiled.indexed.layouts.definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) cells)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (callerState : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id : Word}
  (callerCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    callerNative callerGhost (some caller))
  (recipe : CallableAppliedViewProvenance.Recipe compiled.indexed.ancestry.graph.inputs callerGhost
    origin.ghost caller origin.metadata id code.descriptor.id)

include ordinaryCells represented callerCarried in
/-- The selected row is allowed to contain the genuine transient read frame.
Only the installed child must be stable before marked allocation begins. -/
theorem parameters_with_state
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
    (read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))) :
    ∃ entry : GeneralizedLocalBodyEntry.Entry (values := .initial compiled.compatible.checked)
      origin captured code inputs functions registry cells arguments nativeArguments before store
      owner.key.frameLocation callerNative callerGhost caller id recipe,
    ∃ added : Environment, added.length = code.receipt.loweredParameters.length ∧
      entry.entry.canonical = added ++ captured.canonical ∧
      ProtectedStateTransition.Transition (protocol headers keys) callerState
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := by
  have physical : (callerState.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
    (callerState.rows owner.position).frame_eq
  have unmapped : owner.key.frameLocation ∉ mapping := by
    simpa only [physical] using (callerState.rows owner.position).authority.unmapped
  have nextHistory := GeneralizedLocalCallPrefix.applied_history origin callerCarried recipe
  let next := SourceCoreCallableIndexedDispatch.selectedFrame compiled.indexed.ancestry.graph.table
    code.descriptor.id origin.native (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative)
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) headers keys cells
  let installed := install callerState owner.position (.stable nextHistory)
  let initial : State headers keys ⟨scope, mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame next), captured.canonical⟩ := installed
  have readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer owner.key.frameLocation next := by
    intro index reached read
    exact CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position read nextHistory
  obtain ⟨entry, added, length, spine, reached, parameterRelated⟩ :=
    GeneralizedLocalBodyEntry.Stateful.entry_exists_with_spine (values := .initial compiled.compatible.checked)
      origin captured code inputs functions ordinaryCells (protocol headers keys) producer represented callerCarried recipe
      heaps locals reference read unmapped initial readyAt
  have installedRelated : Relates callerState initial := install_related callerState owner.position (.stable nextHistory)
  exact ⟨entry, added, length, spine, reached, installedRelated.trans parameterRelated⟩

/-- Original Source typing and the actual allocation produce body admission.
No source type is recovered from an erased native payload type. -/
theorem source_admission
    (entry : GeneralizedLocalBodyEntry.Entry (values := .initial compiled.compatible.checked)
      origin captured code inputs functions registry cells arguments nativeArguments before store
      owner.key.frameLocation callerNative callerGhost caller id recipe)
    (frame : Dynamic.ClosureFrame program function)
    (beforeTyped : Dynamic.HeapWellTyped function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types) :
    Dynamic.SourceRuntimeValid program inputs.context function.source ∧
      function.evidence.Covers inputs.context ∧
      Dynamic.HeapWellTyped inputs.context entry.entry.heap ∧
      Dynamic.EnvironmentAgrees entry.entry.heap inputs.context.locals entry.entry.environment ∧
      ∃ finalContext facts,
        StatementsHaveType function.source { returnType := function.resultType } inputs.context function.body finalContext facts ∧
        BodyCompletes function.resultType facts := by
  have runtime := CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have actualArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have reached := Dynamic.BindersAllocate.preservesHeapTyping beforeTyped actualArguments entry.entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have typed := reached.transportClosed fields.signatures frame.code.closed (fields.targetClosed frame.code.closed)
    frame.code.variables_closed (fields.targetResidualVariablesOpen frame.code.residual_variables_open)
  exact ⟨runtime.1, runtime.2, typed, entry.entry.locals,
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame inputs.extended⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOwnedBodyEntry
