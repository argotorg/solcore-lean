import Solcore.Test.SourceCoreChosenOrdinaryAcceptedHeader
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol

/-! The authentic empty public Source heap and the real singleton named hook
supply admission at the unchanged nested body state. Empty parameter allocation
preserves the original Source heap; hook installation covers every actual row.
No body meaning, whole-program well-formedness or runtime value inverse is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedInitialBodyAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

/-- Finite inversion retains the original empty public heap and Source entry. -/
theorem empty_parameters (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (atHeader : HeaderAt fixture header)
    {before heap : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    (beforeEmpty : before = ⟨[]⟩)
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment heap) :
    arguments = [] ∧ environment = [] ∧ heap = ⟨[]⟩ ∧
      Dynamic.HeapWellTyped (runtimeContext fixture.packet) heap := by
  rw [atHeader.parameters] at allocated
  cases allocated
  subst before
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro cell member
  cases member

section Singleton
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {key : CallableIndexedOwnedFunctionValues.Key compiled program}
  {index : ProtectedStateTransition.Index}

/-- The authentic hook updates every row of the actual singleton physical pool. -/
theorem rows_after_singleton_install (first : State headers [key] index)
    (selected : Fin [key].length) {next : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next ghost metadata) :
    StableRows (CallableIndexedOwnedFunctionState.install first selected (.stable carried)) := by
  intro row
  have same : row = selected := by
    apply Fin.ext
    have left := row.isLt
    have right := selected.isLt
    simp only [List.length_singleton] at left right
    omega
  subst row
  have current := CallableIndexedAuthorityPool.Pool.install_current first selected selected (.stable carried)
  have history := CallableIndexedAuthorityPool.Pool.install_ghost first selected selected (.stable carried)
  simp only [ite_true] at current history
  refine ⟨metadata, ?_⟩
  change Carries _ _
    ((first.install selected (.stable carried)).rows selected).authority.current
    ((first.install selected (.stable carried)).rows selected).authority.ghost metadata
  rw [current, history]
  exact carried

variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey [key])
  (header : CallableIndexedOwnedFunctionValues.Header compiled program)
  {arguments : List Dynamic.Value} {administrative actualContext : Core.Context}
  {actual : Environment} {embedding : Renaming} {frameLocation : Location}
  {current : NativeFrame} {ghost : GhostFrame}
  (first : State headers [key] index)
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments index.heap
    (index.store.set frameLocation (encode compiled.indexed.ancestry.layout.frame current))
    index.mapping index.world administrative actualContext actual embedding frameLocation current ghost)
  (reached : State headers [key] ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)

include first in
/-- Actual parameter effects carry every installed row to the same reached pool. -/
theorem rows_at_parameters (physical : frameLocation = owner.key.frameLocation)
    {metadata : Option MetadataState}
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table current ghost metadata) :
    StableRows reached := by
  have parameterFrame : AdministrativePreserved index.mapping
      (index.store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame current))
      entry.mapping entry.store := by
    simpa only [physical] using entry.frame
  exact StableRows.after_administrative
    (CallableIndexedOwnedFunctionState.install first owner.position (.stable carried)) reached
    (rows_after_singleton_install first owner.position carried) parameterFrame

end Singleton

section Fixture
variable (fixture : AcceptedFixture) {header : ActualHeader fixture}
  (atHeader : HeaderAt fixture header)
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {key : CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram)}
  (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey [key])
  {index : ProtectedStateTransition.Index} (first : State headers [key] index)
  {arguments : List Dynamic.Value} {administrative actualContext : Core.Context}
  {actual : Environment} {embedding : Renaming} {frameLocation : Location}
  {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := fixture.packet.compiled.indexed.ancestry)
    (values := .initial fixture.packet.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments index.heap
    (index.store.set frameLocation (encode fixture.packet.compiled.indexed.ancestry.layout.frame current))
    index.mapping index.world administrative actualContext actual embedding frameLocation current ghost)
  (reached : State headers [key] ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)

include atHeader first in
/-- The actual principal packet accompanies the same deeply typed, all-row pool. -/
theorem nested_admission (beforeEmpty : index.heap = ⟨[]⟩)
    (prefixZero : owner.key.capturePrefix = 0)
    (globals : header.globals = fixture.packet.compiled.indexed.base.globals.length)
    (allowed : CallableIndexedOwnedNamedCanonicalEntries.condition functions owner header entry) :
    Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
      (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner header))
      (runtimeContext fixture.packet)
      (CallableIndexedOwnedNamedCanonicalEntries.wrap functions owner header entry reached prefixZero globals allowed) := by
  obtain ⟨_, _, _, heapTyped⟩ := empty_parameters fixture atHeader beforeEmpty entry.allocation
  have rows := rows_at_parameters functions owner header first entry reached allowed.1 allowed.2
  exact ⟨heapTyped, rows⟩

end Fixture
end Tests.SourceCoreChosenOrdinaryAcceptedInitialBodyAdmission
