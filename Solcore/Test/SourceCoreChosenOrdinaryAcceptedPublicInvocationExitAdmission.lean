import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicBodyExitReceipts
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedInvocationAdmission

/-! The actual accepted fixture's
strong body families retain lexical exit and admission inside the invocation's
original parameter/body witnesses. Caller admission concerns the same restored
pool; the body exit keeps its full original administrative context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState RecursiveNamedCatalog
open CallableIndexedOwnedSourceAdmission
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
    registry world store)

/-- Both contexts are the same actual closed declaration type world. Its
residual inference flag remains true, as in the original runtime context. -/
theorem caller_supports (atHeader : HeaderAt fixture caller) :
    Dynamic.TypeContextSupports caller.context caller.function.context := by
  rw [atHeader.context, atHeader.functionContext]
  exact Dynamic.TypeContextSupports.ofClosed rfl rfl rfl rfl rfl

/-- The six original returned effects accompany a single causal receipt.
Its extra retains the full body exit/post and the actual restored caller post. -/
def ResultAtWithExit (sourceParent : Nat) (nativeBudget : Option Nat)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults))
    finalMap finalWorld caller.function.resultType caller.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
    finalMap finalWorld after finalStore ∧
  LocationMap.Extends [] finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved [] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
  NamedInvocationFaultPostContracts.ReturnedAtWithExtra
    (functions := SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
    (registry := registry) (header := caller)
    NamedInvocationFaultPostContracts.Trivial
    (CallableIndexedOwnedPreparedNamedInvocationAdmission.restored_exit_admission_extra
      (functions := SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
      (registry := registry) (header := caller) initial.state caller.function.context
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).position)
    sourceParent nativeBudget (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
    initial.state [] outcome after value finalMap finalWorld finalStore

/-- Select only the caller state retained in the causal body/restoration
receipt. The actual final store equation transports that same witness. -/
theorem ResultAtWithExit.to_post {sourceParent : Nat} {nativeBudget : Option Nat}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ResultAtWithExit fixture root inventory initial sourceParent nativeBudget
      outcome after value finalStore finalMap finalWorld) :
    SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission.ResultAt fixture root inventory initial
      outcome after value finalStore finalMap finalWorld := by
  obtain ⟨represented, heaps, maps, worlds, frame, metadata, causal⟩ := result
  obtain ⟨origin, index, bodyMetadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, selected, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords, extra, restoredFrame⟩ := causal
  have callerPost :
      PostAdmission CallableIndexedOwnedBodyRestorationAdmission.bridge
        caller.function.context caller.function.resultType outcome
        (CallableIndexedOwnedBodyRestoration.returned initial.state bodyState
          (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).position) := extra.2
  subst finalStore
  exact ⟨represented, heaps, maps, worlds, frame, metadata,
    CallableIndexedOwnedBodyRestoration.returned initial.state bodyState
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).position,
    fromCaller, callerPost⟩

/-- The legacy result is projected through the same bound returned state. -/
theorem ResultAtWithExit.forget {sourceParent : Nat} {nativeBudget : Option Nat}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ResultAtWithExit fixture root inventory initial sourceParent nativeBudget
      outcome after value finalStore finalMap finalWorld) :
    SourceCoreChosenOrdinaryAcceptedPublicInvocation.ResultAt fixture root inventory initial
      outcome after value finalStore finalMap finalWorld :=
  SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission.ResultAt.forget
    fixture root inventory initial (ResultAtWithExit.to_post fixture root inventory initial result)

variable (prepared : PublicRecipeReceipt fixture) (bootstrap : BootstrapEvidence fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
  (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)

include prepared bootstrap shape typing checked chosen outer extension in
/-- Each genuine invocation parameter receipt receives the proved strong
body family once. The original invocation restores its saved caller once. -/
theorem preserves_at_initial (budget : Nat) {size : Nat}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues ([] : List Value) :: initial.capture.captured) store
        (caller.code.rename initial.capture.embedding.lift) value finalStore ∧
      ResultAtWithExit fixture root inventory initial size none
        outcome after value finalStore finalMap finalWorld := by
  have represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults))
      [] world caller.bindings [] [] := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.bindings_empty fixture bootstrap.toHeaderAt]
    exact .nil
  have heapTyped : Dynamic.HeapWellTyped caller.function.context ⟨[]⟩ := by
    intro cell member
    cases member
  have argumentsTyped : Dynamic.ValuesHaveTypes caller.function.context ⟨[]⟩ [] caller.types := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.types_empty fixture bootstrap.toHeaderAt]
    exact .nil
  have bodies : CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
      (functions := SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
      (owner := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
      (registry := registry) (faults := faults) caller budget :=
    SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts.source_bodies_for
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete fixture prepared bootstrap.toHeaderAt)
      rfl extension budget
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, _transition, causal⟩ :=
    CallableIndexedOwnedPreparedNamedInvocationAdmission.invocation_preserves_bounded_at_with_admission
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) bootstrap.layouts
      (CallableIndexedOwnedNamedCanonicalEntries.condition
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller)
      (CallableIndexedOwnedNamedCanonicalEntries.authorized
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller)
      budget initial.state (List.mem_singleton_self caller)
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.capture_at_initial fixture root inventory initial)
      represented initial.heaps caller.function.context initial.stable heapTyped argumentsTyped
      (caller_supports fixture bootstrap.toHeaderAt) bodies trace within
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, causal⟩

include prepared bootstrap shape typing checked chosen outer extension in
/-- Native reflection keeps its actual strict body child and an independent
Source grade, with the same original body exit and returned caller admission. -/
theorem reflects_at_initial (budget : Nat) {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues ([] : List Value) :: initial.capture.captured)
      store (caller.code.rename initial.capture.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      ResultAtWithExit fixture root inventory initial sourceSize (some size)
        outcome after value finalStore finalMap finalWorld := by
  have represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults))
      [] world caller.bindings [] [] := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.bindings_empty fixture bootstrap.toHeaderAt]
    exact .nil
  have heapTyped : Dynamic.HeapWellTyped caller.function.context ⟨[]⟩ := by
    intro cell member
    cases member
  have argumentsTyped : Dynamic.ValuesHaveTypes caller.function.context ⟨[]⟩ [] caller.types := by
    rw [SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.types_empty fixture bootstrap.toHeaderAt]
    exact .nil
  have bodies : CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
      (functions := SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
      (owner := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
      (registry := registry) (faults := faults) caller budget :=
    SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts.native_bodies_for
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete fixture prepared bootstrap.toHeaderAt)
      rfl extension budget
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, _transition, causal⟩ :=
    CallableIndexedOwnedPreparedNamedInvocationAdmission.invocation_reflects_bounded_at_with_admission
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) bootstrap.layouts
      (CallableIndexedOwnedNamedCanonicalEntries.condition
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller)
      (CallableIndexedOwnedNamedCanonicalEntries.authorized
        (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) caller)
      budget initial.state (List.mem_singleton_self caller)
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.capture_at_initial fixture root inventory initial)
      represented initial.heaps caller.function.context initial.stable heapTyped argumentsTyped
      (caller_supports fixture bootstrap.toHeaderAt) bodies completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, causal⟩

/-- Both directions concern this one actual initial state and the original
parameter/body/restoration witnesses retained by each invocation. -/
structure InvocationAtInitialWithExit : Prop where
  preserves : ∀ (budget : Nat) {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after → size ≤ budget →
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues ([] : List Value) :: initial.capture.captured) store
        (caller.code.rename initial.capture.embedding.lift) value finalStore ∧
      ResultAtWithExit fixture root inventory initial size none
        outcome after value finalStore finalMap finalWorld
  reflects : ∀ (budget : Nat) {size : Nat} {value : Value} {finalStore : Store},
    EvaluationSize size (DataPatternValues.packValues ([] : List Value) :: initial.capture.captured)
      store (caller.code.rename initial.capture.embedding.lift) value finalStore → size ≤ budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.sourceBody caller.function.evidence ⟨[]⟩ [] outcome after ∧
      ResultAtWithExit fixture root inventory initial sourceSize (some size)
        outcome after value finalStore finalMap finalWorld

/-- The low pair is a projection at the same input and returned witnesses. -/
theorem InvocationAtInitialWithExit.forget
    (meaning : InvocationAtInitialWithExit fixture root inventory initial) :
    SourceCoreChosenOrdinaryAcceptedPublicInvocation.InvocationAtInitial fixture root inventory initial := by
  constructor
  · intro budget size outcome after trace within
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result⟩ := meaning.preserves budget trace within
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated,
      ResultAtWithExit.forget fixture root inventory initial result⟩
  · intro budget size value finalStore completed within
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ := meaning.reflects budget completed within
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
      ResultAtWithExit.forget fixture root inventory initial result⟩

include prepared bootstrap shape typing checked chosen outer extension in
/-- Static accepted body families construct both strong directions at the
supplied authentic initial state; no public action is replayed. -/
theorem at_initial : InvocationAtInitialWithExit fixture root inventory initial := by
  constructor
  · intro budget size outcome after trace within
    exact preserves_at_initial fixture root inventory initial prepared bootstrap shape typing checked chosen outer extension budget trace within
  · intro budget size value finalStore completed within
    exact reflects_at_initial fixture root inventory initial prepared bootstrap shape typing checked chosen outer extension budget completed within

include bootstrap shape typing checked chosen outer extension in
/-- One original initial-state factory consumes the same completed-bootstrap
proof. All body, parameter and restoration work remains in its invocation. -/
theorem at_completed {fuel : Nat} (completed : CompletedBootstrap prepared fuel) :
    ∃ nextWorld,
    ∃ first : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
      (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults)
      registry nextWorld completed.store,
      InvocationAtInitialWithExit fixture root inventory first := by
  obtain ⟨nextWorld, ⟨first⟩⟩ := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.initial_at_completed
    fixture prepared completed bootstrap
    (SourceCoreChosenOrdinaryAcceptedPublicInvocation.functions fixture root inventory registry faults) registry
  exact ⟨nextWorld, first,
    at_initial fixture root inventory first prepared bootstrap shape typing checked chosen outer extension⟩

end Tests.SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission
