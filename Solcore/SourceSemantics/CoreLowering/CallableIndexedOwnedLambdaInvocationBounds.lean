import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestoration
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyStaticOrigins

/-! Anonymous invocation uses the real selected pool row, its original caller
history and the full stored captures. Actual frame installation and marked
parameter allocation produce the reached pool consumed by the body. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallableIndexedOwnedFunctionState
open RecursiveNamedCatalogInvocationBounds (Below)

/-- The original static lambda body is aligned with its exact invocation
context, complete capture scope and emitted code. No execution is a field. -/
structure BodyOrigin {compiled : SourceCoreUnifiedCompilation.Compiled}
    {program : Program} {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults
  frame : Dynamic.ClosureFrame program function
  function_eq : origin.function = function
  context_eq : origin.context = inputs.context
  administrative_eq : origin.administrative = administrative
  scope_eq : origin.scope = code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope
  frame_eq : origin.frameLayout = compiled.indexed.ancestry.layout.frame
  globals_eq : origin.globals = compiled.indexed.base.globals.length
  output_eq : origin.output = code.receipt.resultCore
  code_eq : origin.code = code.receipt.body

private theorem binders_context_eq {owner : Resolved.DeclarationId} {before left right : SourceSemantics.Context}
    {parameters : List TypedBinder} {leftTypes rightTypes : List TypeSystem.Ty}
    (first : MonoBindersExtend owner before parameters leftTypes left)
    (second : MonoBindersExtend owner before parameters rightTypes right) : left = right := by
  have same := first.bodyTypes_eq.symm.trans second.bodyTypes_eq
  subst rightTypes
  exact first.functional second

/-- The actual named lambda profile supplies every static alignment receipt. -/
def BodyOrigin.named {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : CallableIndexedLambdaNamedRuntimeBodyMeaning.Body (values := .initial compiled.compatible.checked)
      headers code program registry faults)
    (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
    BodyOrigin (program := program) code inputs registry faults :=
  ⟨CallableRuntimeBodyStaticOrigins.lambda_named code body escaped, body.frame, rfl,
    binders_context_eq body.extended inputs.extended, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Ranked nested support retains the same dynamic function, evidence and
captured scope as its original body profile. -/
def BodyOrigin.nested {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {caller : CallableIndexedOwnedFunctionValues.Header compiled program} {rank : Nat}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : CallableIndexedLambdaNestedRuntimeBodyMeaning.Body (values := .initial compiled.compatible.checked)
      headers caller registry faults rank code)
    (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
    BodyOrigin (program := program) code inputs registry faults :=
  ⟨CallableRuntimeBodyStaticOrigins.lambda_nested code body escaped, body.body.frame, rfl,
    binders_context_eq body.body.extended inputs.extended, rfl, rfl, rfl, rfl, rfl, rfl⟩

section Prefix
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)

include captured code history inputs functions represented caller heaps locals reference currentCarried allowed in
/-- The actual installed pool feeds the real marked prefix. The entire original
entry and capture spine accompany its reached pool. -/
theorem parameters_with_state :
    ∃ entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked) captured code history inputs functions registry arguments nativeArguments
      before store owner.key.frameLocation (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost,
    ∃ added : Environment, added.length = code.receipt.loweredParameters.length ∧
      entry.entry.canonical = added ++ captured.canonical ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation =
      some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [physical] using authority.unmapped
  have nextHistory := ordinary_complete compiled.indexed.ancestry.graph history.carried currentCarried allowed
  let next := SourceCoreCallableIndexedDispatch.selectedFrame compiled.indexed.ancestry.graph.table
    code.descriptor.id history.native authority.current
  let producer := CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  let installed := install caller owner.position (.stable nextHistory)
  let initial : State headers keys ⟨scope, mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame next), captured.canonical⟩ := installed
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary owner.key.frameLocation next :=
    CallableIndexedOwnedAllocationProducer.readyAt_of_stable_read
    (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    owner.position nextHistory
  obtain ⟨entry, added, length, spine, reached, parameterRelated⟩ :=
    CallableIndexedLambdaEntryPrefix.Stateful.entry_exists_for_with_spine (values := .initial compiled.compatible.checked) captured code history inputs functions
      (protocol headers keys) producer represented heaps locals reference read currentCarried unmapped allowed initial readyAt
  have installedRelated : Relates caller initial := install_related caller owner.position (.stable nextHistory)
  exact ⟨entry, added, length, spine, reached, installedRelated.trans parameterRelated⟩

include captured code history inputs functions represented caller heaps locals reference currentCarried allowed in
/-- The original native lambda completion selects a strict body child and its
actual parameter pool. Its final store is the original frame restoration. -/
theorem body_prefix_with_state {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked) captured code history inputs functions registry arguments before store
        owner.key.frameLocation (caller.rows owner.position).authority.current,
    ∃ child bodyStore, child < size ∧ EvaluationSize child reached.actual reached.store
      (code.receipt.body.rename reached.embedding) result bodyStore ∧
      finalStore = bodyStore.set owner.key.frameLocation
        (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          reached.mapping, reached.world, reached.heap, reached.store, reached.canonical⟩ := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  have read : store.read? owner.key.frameLocation =
      some (encode compiled.indexed.ancestry.layout.frame authority.current) := by
    simpa only [physical] using authority.frame.read
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [physical] using authority.unmapped
  have nextHistory := ordinary_complete compiled.indexed.ancestry.graph history.carried currentCarried allowed
  let next := SourceCoreCallableIndexedDispatch.selectedFrame compiled.indexed.ancestry.graph.table
    code.descriptor.id history.native authority.current
  let producer := CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
  let installed := install caller owner.position (.stable nextHistory)
  let initial : State headers keys ⟨scope, mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame next), captured.canonical⟩ := installed
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary owner.key.frameLocation next :=
    CallableIndexedOwnedAllocationProducer.readyAt_of_stable_read
    (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    owner.position nextHistory
  obtain ⟨reached, child, bodyStore, smaller, bodyCompleted, restored, post, parameterRelated⟩ :=
    CallableIndexedLambdaEntryBounds.Stateful.body_prefix_for (values := .initial compiled.compatible.checked) captured code history inputs functions
      represented heaps locals reference read currentCarried unmapped allowed
      (protocol headers keys) producer initial readyAt completed
  have installedRelated : Relates caller initial := install_related caller owner.position (.stable nextHistory)
  exact ⟨reached, child, bodyStore, smaller, bodyCompleted, restored, post, installedRelated.trans parameterRelated⟩

include captured code history inputs functions represented caller heaps locals reference currentCarried allowed in
/-- Stored payload application adds its genuine strict apply edge while
retaining the same full captured environment and reached prefix pool. -/
theorem application_prefix_with_state {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked) captured code history inputs functions registry arguments before store
        owner.key.frameLocation (caller.rows owner.position).authority.current,
    ∃ child bodyStore, child < size ∧ EvaluationSize child reached.actual reached.store
      (code.receipt.body.rename reached.embedding) result bodyStore ∧
      finalStore = bodyStore.set owner.key.frameLocation
        (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current) ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          reached.mapping, reached.world, reached.heap, reached.store, reached.canonical⟩ := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  obtain ⟨reached, child, bodyStore, childLess, evaluated, restored, transition⟩ :=
    body_prefix_with_state captured code history inputs functions represented owner caller heaps locals reference currentCarried allowed applied
  exact ⟨reached, child, bodyStore, Nat.lt_trans childLess smaller, evaluated, restored, transition⟩

variable {faults : FunctionCalls.FaultRep}
  (body : BodyOrigin (program := program) code inputs registry faults)

/-- Only original Source closure rules select this strict body child. The
independent monomorphic parameter receipt fixes its actual call context. -/
private theorem source_body {size : Nat} {callContext : SourceSemantics.Context}
    {callerEvidence : Dynamic.EvidenceEnvironment} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (arity : function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) :
    ∃ child environment heap,
      Dynamic.BindersAllocate function.captured before function.parameters arguments environment heap ∧
      RecursiveNamedCallBounds.BodyTrace program child function inputs.context environment heap outcome after ∧ child < size := by
  cases trace with
  | value executed =>
    cases executed with
    | closure _ _ extended allocated executed returned =>
      have same := binders_context_eq extended inputs.extended
      subst same
      subst returned
      exact ⟨_, _, _, allocated, .returned executed, SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | closureUnit _ _ resultUnit extended allocated executed fellThrough =>
      have same := binders_context_eq extended inputs.extended
      subst same
      obtain ⟨_, rfl⟩ := fellThrough
      exact ⟨_, _, _, allocated, .unit resultUnit executed, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | closureArity mismatch => exact False.elim (mismatch arity)
    | closureBody _ _ extended allocated failed =>
      have same := binders_context_eq extended inputs.extended
      subst same
      exact ⟨_, _, _, allocated, .fault failed, SourceExecutionSize.child_lt_stepSize (by simp)⟩
    | closureControlEscape _ _ extended allocated executed escaped =>
      have same := binders_context_eq extended inputs.extended
      subst same
      exact ⟨_, _, _, allocated, .escaped executed escaped, SourceExecutionSize.child_lt_stepSize (by simp)⟩

include body in
/-- Native reflection reconstructs the original four closure exit receipts at
its independent Source grade, using the authentic full parameter allocation. -/
private theorem call_of_body {size : Nat} {callContext : SourceSemantics.Context}
    {callerEvidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {heap after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate function.captured before function.parameters arguments environment heap)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function inputs.context environment heap outcome after) :
    RecursiveNamedCallBounds.CallOutcome program (SourceExecutionSize.stepSize [size]) callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after := by
  cases trace with
  | returned executed => exact .value (.closure rfl body.frame inputs.extended allocated executed rfl)
  | unit same executed => exact .value (.closureUnit rfl body.frame same inputs.extended allocated executed ⟨_, rfl⟩)
  | fault failed => exact .fault (.closureBody rfl body.frame inputs.extended allocated failed)
  | escaped executed escape => exact .fault (.closureControlEscape rfl body.frame inputs.extended allocated executed escape)

/-- The source-produced entry is packaged without changing its reached pool,
captured canonical spine or selected physical frame. -/
def source_entry
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) body.origin functions where
  mapping := entry.entry.mapping
  world := entry.entry.world
  environment := entry.entry.environment
  canonical := entry.entry.canonical
  actual := entry.entry.actualBody
  heap := entry.entry.heap
  store := entry.entry.store
  embedding := entry.entry.embedding
  actualContext := CallableIndexedParameterTyped.prefixContext code.receipt.loweredParameters entry.actualContext
  frameLocation := owner.key.frameLocation
  native := entry.next
  environments := by simpa only [body.administrative_eq, body.scope_eq, CallableIndexedAmbient.ambientDefinitions] using entry.entry.environments
  heaps := entry.entry.heaps
  locals := by simpa only [body.context_eq] using entry.entry.locals
  lookups := entry.entry.lookups
  actualTyped := entry.entry.actualTyped
  reference := by simpa only [body.scope_eq, body.globals_eq, body.frame_eq] using entry.entry.reference
  read := by simpa only [body.frame_eq] using entry.entry.read
  unmapped := entry.entry.unmapped
  initial := reached
  gate := ⟨owner.position, _, _, rfl, entry.nextHistory⟩

/-- The measured native prefix has its own actual environment and pool. Its
packaging preserves those witnesses rather than selecting an older entry. -/
def native_entry
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) body.origin functions where
  mapping := entry.mapping
  world := entry.world
  environment := entry.environment
  canonical := entry.canonical
  actual := entry.actual
  heap := entry.heap
  store := entry.store
  embedding := entry.embedding
  actualContext := entry.actualContext
  frameLocation := owner.key.frameLocation
  native := entry.next
  environments := by simpa only [body.administrative_eq, body.scope_eq, CallableIndexedAmbient.ambientDefinitions] using entry.environments
  heaps := entry.heaps
  locals := by simpa only [body.context_eq] using entry.locals
  lookups := entry.lookups
  actualTyped := entry.actualTyped
  reference := by simpa only [body.scope_eq, body.globals_eq, body.frame_eq] using entry.reference
  read := by simpa only [body.frame_eq] using entry.read
  unmapped := entry.unmapped
  initial := reached
  gate := ⟨owner.position, _, _, rfl, entry.nextHistory⟩


include body inputs represented heaps locals reference currentCarried allowed in
/-- The original strict Source child is proved by the shared actual body
family, then the saved caller frame is restored in that exact reached pool. -/
theorem invocation_preserves_bounded_with (budget : Nat)
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program body.origin))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
        store (code.body.rename captured.embedding.lift.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  have arity : function.parameters.length = arguments.length := by
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code, List.length_map]
    exact represented.length.1
  obtain ⟨child, environment, bound, allocated, bodyTrace, smaller⟩ := source_body captured code inputs arity trace
  obtain ⟨entry, _added, _length, _spine, parameterState, parameterRelated⟩ :=
    parameters_with_state captured code history inputs functions represented owner caller heaps locals reference currentCarried allowed
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  let actualEntry := source_entry captured code history inputs functions owner caller body entry parameterState
  have actualTrace : RecursiveNamedCallBounds.BodyTrace program child body.origin.function body.origin.context
      actualEntry.environment actualEntry.heap outcome after := by
    simpa only [body.function_eq, body.context_eq, actualEntry, source_entry] using bodyTrace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
      bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, _exit, bodyState, bodyRelated⟩ :=
    bodyMeaning child (Nat.lt_of_lt_of_le smaller within) actualEntry actualTrace
  have originalBody : Evaluates entry.entry.actualBody entry.entry.store
      (code.receipt.body.rename entry.entry.embedding) value bodyStore := by
    simpa only [body.code_eq, actualEntry, source_entry] using bodyEvaluation
  have representedResult : FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value := by
    rw [body.function_eq, body.output_eq] at result
    exact result
  have maps := entry.entry.maps.trans bodyMaps
  have worlds := entry.entry.worlds.trans bodyWorlds
  have frame := entry.entry.frame.trans bodyFrame
  have sourceMetadata := entry.entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position
      (CallableIndexedAmbient.frame_registered compiled.indexed) finalHeaps worlds frame related
  exact ⟨value, _, finalMap, finalWorld, entry.wrap originalBody, representedResult,
    restoredHeaps, maps, worlds, restoredFrame, sourceMetadata, returned⟩

include body inputs represented heaps locals reference currentCarried allowed in
/-- The original native completion exposes a strict body child. Its actual
post pool is restored, while the Source call grade is reconstructed separately. -/
theorem invocation_reflects_bounded_with (budget : Nat)
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program body.origin))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨entry, child, bodyStore, smaller, bodyCompleted, restored, parameterState, parameterRelated⟩ :=
    body_prefix_with_state captured code history inputs functions represented owner caller heaps locals reference currentCarried allowed completed
  let actualEntry := native_entry captured code history inputs functions owner caller body entry parameterState
  have actualCompleted : EvaluationSize child actualEntry.actual actualEntry.store
      (body.origin.code.rename actualEntry.embedding) value bodyStore := by
    simpa only [body.code_eq, actualEntry, native_entry] using bodyCompleted
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps,
      bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, _exit, bodyState, bodyRelated⟩ :=
    bodyMeaning child (Nat.lt_of_lt_of_le smaller within) actualEntry actualCompleted
  have originalTrace : RecursiveNamedCallBounds.BodyTrace program sourceSize function inputs.context
      entry.environment entry.heap outcome after := by
    simpa only [body.function_eq, body.context_eq, actualEntry, native_entry] using bodyTrace
  have representedResult : FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value := by
    rw [body.function_eq, body.output_eq] at result
    exact result
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, _callerRelated, _records, returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position
      (CallableIndexedAmbient.frame_registered compiled.indexed) finalHeaps worlds frame related
  subst finalStore
  exact ⟨_, outcome, after, finalMap, finalWorld, call_of_body captured code inputs body entry.allocation originalTrace,
    representedResult, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata, returned⟩


include body inputs represented heaps locals reference currentCarried allowed in
/-- Applying the authentic stored lambda payload retains the same actual
parameter/body pool and saved caller restoration. -/
theorem application_preserves_bounded_with (budget : Nat)
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program body.origin))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    invocation_preserves_bounded_with captured code history inputs functions represented owner caller heaps locals
      reference currentCarried allowed body budget bodyMeaning trace within
  exact ⟨value, finalStore, finalMap, finalWorld,
    .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result, finalHeaps, maps, worlds, frame, metadata, transition⟩

include body inputs represented heaps locals reference currentCarried allowed in
/-- The real apply edge keeps native decrease separate from the independently
reconstructed Source call grade and its actual returned pool. -/
theorem application_reflects_bounded_with (budget : Nat)
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program body.origin))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact invocation_reflects_bounded_with captured code history inputs functions represented owner caller heaps locals
    reference currentCarried allowed body budget bodyMeaning applied (Nat.le_trans (Nat.le_of_lt smaller) within)

end Prefix

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds
