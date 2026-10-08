import Solcore.Frontend.SourceCoreUnifiedRuntime
import Solcore.SourceSemantics.Dynamic.ProgramOutcome
import Solcore.SourceSemantics.CoreLowering.GenericHeap

/-! Joint observations retain the original Source reason and reached heap,
the actual native failure token, and the exact public diagnostic. The receiver
is the existing failed-token branch of Execution.observe. These receipts do
not identify other public boundary or validation errors with Source faults,
and do not supply a category-wide FunctionCalls.FaultRep. Actual read/place
origin witnesses and their issued-table decoding remain independent inputs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultObservation
open Core Frontend SourceInference GeneralHeap

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {nativeProgram : SourceCoreUnifiedRuntime.Program checked}
  {prepared : SourceCoreUnifiedRuntime.Prepared nativeProgram}
  (execution : SourceCoreUnifiedRuntime.Execution prepared)
  {token : Word} {store : Store} {diagnostic : SourceCoreFaultSites.Diagnostic}

/-- This is the exact table carried by the actual native completion. -/
def DecodedAt (token : Word) (diagnostic : SourceCoreFaultSites.Diagnostic) : Prop :=
  execution.completion.result.diagnostics.diagnostic? token = some diagnostic

/-- A real failed observation is decoded after exporting that same completion.
The exported heap is retained literally, including the original inert prefix. -/
theorem observe_failed {exportFuel : Option Nat}
    {exported : SourceCoreCallableIndexedHeapOutputs.Export prepared.output
      execution.completion execution.initial.heap}
    (heapExport : SourceCoreCallableIndexedHeapOutputs.exportHeap prepared.output
      execution.completion execution.initial.heap
      (exportFuel.getD execution.exportFuel) = .ok exported)
    (failed : execution.completion.result.native.observation = .failed token store)
    (decoded : DecodedAt execution token diagnostic) :
    execution.observe exportFuel = .ok (.fault diagnostic.error ⟨exported.heap⟩) := by
  simp only [SourceCoreUnifiedRuntime.Execution.observe, heapExport, Except.mapError,
    bind, Except.bind, failed, DecodedAt] at *
  rw [decoded]
  rfl

/-- An accepted public failure observation supplies its actual heap export
and exact diagnostic. Native failure is explicit, so successful-native deep
validation faults and initial boundary faults are not classified here. -/
theorem observe_failed_receipts {exportFuel : Option Nat}
    {error : SourceTypedRuntime.RuntimeError} {final : SourceTypedRuntime.RuntimeState}
    (failed : execution.completion.result.native.observation = .failed token store)
    (observed : execution.observe exportFuel = .ok (.fault error final)) :
    ∃ exported : SourceCoreCallableIndexedHeapOutputs.Export prepared.output
        execution.completion execution.initial.heap,
      SourceCoreCallableIndexedHeapOutputs.exportHeap prepared.output execution.completion
        execution.initial.heap (exportFuel.getD execution.exportFuel) = .ok exported ∧
      ∃ diagnostic, DecodedAt execution token diagnostic ∧ diagnostic.error = error ∧
        final = ⟨exported.heap⟩ := by
  cases exportedAt : SourceCoreCallableIndexedHeapOutputs.exportHeap prepared.output
      execution.completion execution.initial.heap (exportFuel.getD execution.exportFuel) with
  | error problem =>
    simp only [SourceCoreUnifiedRuntime.Execution.observe, exportedAt, Except.mapError,
      bind, Except.bind] at observed
    cases observed
  | ok exported =>
    simp only [SourceCoreUnifiedRuntime.Execution.observe, exportedAt, Except.mapError,
      bind, Except.bind, failed] at observed
    cases decoded : execution.completion.result.diagnostics.diagnostic? token with
    | none => simp only [decoded] at observed; cases observed
    | some diagnostic =>
      simp only [decoded] at observed
      cases observed
      exact ⟨exported, rfl, diagnostic, decoded, rfl, rfl⟩

/-- The Source and native heaps are related at the original same reached
store/map/world. No Source reason or location is replaced by the public error. -/
structure Packet {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : SourceSemantics.Program) (entry : Dynamic.ProgramEntry)
    (before after : Dynamic.Heap) (reason : Dynamic.SemanticFault)
    (mapping : LocationMap) (world : StoreTyping)
    (token : Word) (store : Store) (diagnostic : SourceCoreFaultSites.Diagnostic) : Prop where
  sourceFault : Dynamic.ProgramFaults program entry before reason after
  reachedHeap : GenericHeap.HeapRepresents model mapping world after store
  nativeFault : execution.completion.result.native.observation = .failed token store
  decoded : DecodedAt execution token diagnostic

variable {catalog : SourceCoreDataCatalog.Catalog}
  {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : SourceSemantics.Program} {entry : Dynamic.ProgramEntry}
  {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
  {mapping : LocationMap} {world : StoreTyping}

/-- Genuine paired completion receipts construct the observation packet.
The diagnostic equation concerns only its actual receiver table. -/
theorem packet_of_receipts
    (sourceFault : Dynamic.ProgramFaults program entry before reason after)
    (reachedHeap : GenericHeap.HeapRepresents model mapping world after store)
    (nativeFault : execution.completion.result.native.observation = .failed token store)
    (decoded : DecodedAt execution token diagnostic) :
    Packet execution model program entry before after reason mapping world token store diagnostic :=
  ⟨sourceFault, reachedHeap, nativeFault, decoded⟩

/-- The complete joint packet survives the public decoder unchanged. An
accepted export is required; exporter errors retain their actual public type. -/
theorem Packet.observe
    (packet : Packet execution model program entry before after reason mapping world token store diagnostic)
    {exportFuel : Option Nat}
    {exported : SourceCoreCallableIndexedHeapOutputs.Export prepared.output
      execution.completion execution.initial.heap}
    (heapExport : SourceCoreCallableIndexedHeapOutputs.exportHeap prepared.output
      execution.completion execution.initial.heap
      (exportFuel.getD execution.exportFuel) = .ok exported) :
    Packet execution model program entry before after reason mapping world token store diagnostic ∧
      execution.observe exportFuel = .ok (.fault diagnostic.error ⟨exported.heap⟩) :=
  ⟨packet, observe_failed execution heapExport packet.nativeFault packet.decoded⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultObservation
