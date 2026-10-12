import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedChildBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.BuiltinNamedCallMeaning

/-! The original staged global application selects its authentic retained
Header body, Source allocation and child scope. The native parameter producer
runs without a completed-body premise. Strict staged body preservation then
constructs the native invocation and restores the actual returned caller pool.
Source and native grades remain independent, including nested stage failures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

section Source
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
local notation "program" => Program.ofChecked compiled.sourceProgram
variable {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {function : Dynamic.GlobalFunction}

private theorem roots_functional {nodes : List NodeId} {left right : List StatementId}
    (first : Dynamic.StatementRoots nodes left) (second : Dynamic.StatementRoots nodes right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | @cons id nodes left first ih => cases second with
    | cons remaining => exact congrArg (List.cons id) (ih remaining)

/-- Inversion uses the retained global instantiation and actual selected scope.
It preserves the original staged body outcome instead of wrapping an ordinary
execution. Source arity excludes only the separate pre-allocation fault. -/
theorem body_prefix {header : Header compiled program} (sourceAt : NamedSourceAt header rawD function)
    (wellFormed : ProgramWellFormed program)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {before after : Dynamic.Heap}
    {arguments : List Dynamic.Value} {outcome : Staging.Recursive.Outcome} {size : Nat}
    (arity : header.function.parameters.length = arguments.length)
    (trace : Staging.Recursive.Size.Applies program stages size invocation context before
      (.global function) arguments outcome after) :
    ∃ bodySize child environment bound finalContext bodyOutcome,
      stages.Closure header.function child ∧
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements program stages bodySize child header.context environment bound
        header.function.body finalContext bodyOutcome after ∧
      Staging.Recursive.BodyResult header.function.resultType bodyOutcome outcome ∧ bodySize < size := by
  have bodyUnique : ∀ actual, Dynamic.FunctionInstantiates program function.instantiation actual →
      RecursiveNamedCatalog.Header.sourceBody header = actual := by
    intro actual instantiated
    exact BuiltinNamedCalls.instantiation_unique_of_wellFormed wellFormed
      sourceAt.frame.instantiated instantiated
  cases trace with
  | @globalArity _ _ _ _ _ bodyInstance instantiates mismatch =>
    have same := bodyUnique bodyInstance instantiates
    cases same
    exact False.elim (mismatch (by simpa only [sourceAt.frame.parameters] using arity))
  | @global bodySize _ _ _ bound _ _ _ environment parameterTypes bodyContext finalContext
      bodyInstance roots child bodyOutcome _ instantiates covers rootsEq selected parameters allocate body converted =>
    have same := bodyUnique bodyInstance instantiates
    cases same
    have sameRoots := roots_functional rootsEq sourceAt.frame.roots
    subst_vars
    have actualParameters : MonoBindersExtend header.function.source.owner header.function.context
        header.function.parameters parameterTypes bodyContext := by
      simpa only [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] using parameters
    have sameTypes := header.extended.bodyTypes_eq.symm.trans actualParameters.bodyTypes_eq
    subst_vars
    have sameContext := (header.extended.functional actualParameters).symm
    subst_vars
    have actualSelected : stages.Closure header.function child := by
      simpa only [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] using selected
    exact ⟨_, _, _, _, _, _, actualSelected, sourceAt.frame.parameters.symm ▸ allocate,
      body, sourceAt.frame.result.symm ▸ converted,
      Staging.Recursive.Size.child_lt_stepSize (by simp)⟩
end Source

section Native
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (index : Int) (actual : Environment) (store : Store) (saved : Value) :
    Evaluates (saved :: actual) store
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

private theorem related_cast_frame
    {initial : ProtectedStateTransition.Index} (saved : State headers keys initial)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {first second : Location} {next : Value} (same : first = second)
    (state : State headers keys ⟨scope, mapping, world, heap, store.set first next, canonical⟩)
    (related : Relates saved state) :
    Relates saved (Eq.mp (congrArg (fun location => State headers keys
      ⟨scope, mapping, world, heap, store.set location next, canonical⟩) same) state) := by
  cases same
  exact related

private theorem readyAt_cast
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {expression : ExpressionId}
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (certifies : ∀ lowered,
    header.policy.lowerExpression terminal.childFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
    certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include functions owner caller header capture sourceAt terminal certifies in
/-- Authentic Source allocation and the strict staged body child construct the
native parameter/body continuation before literal caller restoration. The
returned state retains full representation, relates and caller PostAdmission. -/
theorem preserves_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
        header model stages child certificate faults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
      size invocation context heap (.global function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld faults := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  have liveLocals : Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
    obtain ⟨original⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner member
    exact original.locals
  have liveReference : capture.canonical[header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using capture.reference
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨childSize, child, environment, bound, finalContext, bodyOutcome,
    selected, allocated, bodyTrace, converted, smaller⟩ := body_prefix sourceAt wellFormed arity trace
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  let installed := CallableIndexedOwnedFunctionState.install caller owner.position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
      (DataPatternValues.packValues payloads :: capture.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift capture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped capture.typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts compiled.indexed.ancestry.layout.frame model :=
    sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys model
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) := by
    exact readyAt_cast sameLayouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      model owner.position physical.symm history)
  let parameterInitial : State headers keys
      ⟨[], mapping, world, heap, store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), capture.canonical⟩ :=
    Eq.mp (congrArg (fun location => State headers keys
      ⟨[], mapping, world, heap, store.set location (encode compiled.indexed.ancestry.layout.frame (.state index)), capture.canonical⟩)
      physical.symm) installed
  obtain ⟨entry, parameterTransition, agreement⟩ := parameters_with_state installedAuthority
    capture.environments liveLocals liveReference capture.coherent represented installedHeaps
    layout actualTyped producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner caller header arguments :=
    ⟨origin, index, metadata, capture.administrative, _,
      .unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured,
      Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift),
      authority.frameLocation, (caller.rows owner.position).frame_eq, owned, history, emitted,
      entry, parameterState, installedRelated.trans parameterRelated, stable, heapTyped, argumentsTyped⟩
  have admitted : Admission poolBridge header.context parameterState := ⟨(receipt.source wellFormed).heapTyped, receipt.rows⟩
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated, bodyPost⟩ :=
    CallableIndexedOwnedPreparedStagedNamedChildBounds.preserves_body
      (owner := owner) (packet := fun zero globals => receipt.packet zero globals) (selected := selected) (wellFormed := wellFormed)
      (terminal := terminal) (certifies := certifies)
      (environments := entry.environments) (heaps := entry.heaps) (locals := entry.locals)
      (agrees := entry.lookups) (typed := entry.actualTyped) (initial := parameterState) (admitted := admitted)
      budget (children selected) bodyTrace converted (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
  have prefixEvaluation := agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  have reference : (DataPatternValues.packValues payloads :: capture.captured)[capture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ, physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using capture.capturedReference
  have evaluation := CallableContextFrames.withFrame_evaluates (.var reference) authority.frame.read
    (next_evaluates index (DataPatternValues.packValues payloads :: capture.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current)) prefixEvaluation
  have renamed : header.code.rename capture.embedding.lift = withFrame
      (.var (capture.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (header.parameterCode.rename capture.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := installedRelated.trans (parameterRelated.trans bodyRelated)
  obtain ⟨restoredHeaps, restoredFrame, _cell, _fromBody, restoredRelated, _records, _transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using frame) related
  have restoredPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨value, _, finalMap, finalWorld, ?_, result, restoredHeaps, maps, worlds,
    restoredFrame, sourceMetadata, CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position,
    restoredRelated, restoredPost⟩
  simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using
    (renamed.symm ▸ evaluation)
end Native
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
