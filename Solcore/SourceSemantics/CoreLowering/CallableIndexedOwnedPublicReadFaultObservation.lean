import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultObservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceiverTables
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadFaultPolicies
import Solcore.SourceSemantics.CoreLowering.CompatibleHeap

/-! An ordinary read observation keeps the actual Source location and the
binder selected by the same read certificate. The receiver is the real indexed
completion table, rebuilt at its own registry. Issuer lookup, priority and range
receipts remain explicit until their genuine preparation producers supply them.
This packet is indexed by the reached heap; it defines no blanket FaultRep.
The whole Source failure and primitive read receipt are retained independently.
Their occurrence path through the whole fault must come from the existing
semantic fold; same-location equality alone does not identify that path. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicReadFaultObservation
open Core Frontend SourceInference GeneralHeap CompatibleExpressionReads CompatiblePayload
open CallableIndexedOwnedPublicFaultObservation CallableIndexedOwnedPublicFaultReceiverTables

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {nativeProgram : SourceCoreUnifiedRuntime.Program checked}
  {prepared : SourceCoreUnifiedRuntime.Prepared nativeProgram}
  (execution : SourceCoreUnifiedRuntime.Execution prepared)
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {program : SourceSemantics.Program} {entry : Dynamic.ProgramEntry}
  {before after : Dynamic.Heap} {mapping : LocationMap} {world : StoreTyping}
  {location : Dynamic.Location} {cell : Dynamic.Cell} {store : Store}
  {fuel : Nat} {values : ValuesContext} {source : TypedSource} {scope : Scope}
  {id : ExpressionId} {reason : Word} {code : Expr}
  (certificate : CompatibleExpressionReads.Certificate fuel values source scope id reason code)
  (context : SourceSemantics.Context) (environment : Dynamic.Environment)
  (site : SourceCoreFaultSites.ReadSite)

/-- The observation retains the exact read witness at the original fault's
reached heap. Its binder, occurrence and span are the issued diagnostic row. -/
structure Packet
    (functions : FunctionModel checked.catalog ambient)
    (program : SourceSemantics.Program) (entry : Dynamic.ProgramEntry)
    (before after : Dynamic.Heap) (mapping : LocationMap) (world : StoreTyping)
    (location : Dynamic.Location) (cell : Dynamic.Cell) (store : Store) : Prop where
  observation : CallableIndexedOwnedPublicFaultObservation.Packet execution
    (CompatibleHeap.payloadModel checked execution.completion.result.context.registry functions) program entry
    before after (.uninitializedLocation location) mapping world site.reason store {
      error := .uninitializedLocal site.binder
      site := .occurrence site.expression.occurrence
      span := some site.span}
  read : CompatibleExpressionReads.UninitializedWitness certificate context environment after location cell
  checkedExact : values.checked = checked
  ambientExact : ambient.definitions = nativeProgram.layouts.definitions
  expression : site.expression = id
  binder : site.binder = certificate.binder
  span : site.span = certificate.node.span
  token : site.reason = reason

/-- Actual base preparation and the actual completion's issued table derive
the decoder equation internally. The Source failure and read witness still
retain their same location and heap, and native failure retains its real store. -/
theorem packet_of_issued
    (sourceFault : Dynamic.ProgramFaults program entry before (.uninitializedLocation location) after)
    (reachedHeap : CompatibleHeap.HeapRepresents checked execution.completion.result.context.registry
      functions mapping world after store)
    (nativeFault : execution.completion.result.native.observation = .failed site.reason store)
    (read : CompatibleExpressionReads.UninitializedWitness certificate context environment after location cell)
    (checkedExact : values.checked = checked)
    (ambientExact : ambient.definitions = nativeProgram.layouts.definitions)
    (expression : site.expression = id) (binder : site.binder = certificate.binder)
    (span : site.span = certificate.node.span) (token : site.reason = reason)
    (receiver : IssuedAt nativeProgram execution.completion.entry
      execution.completion.result.context.registry execution.completion.result.extension
      execution.completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (SourceCoreCompatibleValues.Context.initial checked)}
    (present : nativeProgram.base.diagnostics = some issued)
    {base : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry execution.completion.result.context.registry
      execution.completion.result.extension = .ok base)
    (positive : site.reason ≠ Word.zero) (ordinary : site.reason ≠ base.escapedReason)
    (noBoundary : base.additional.find? (fun candidate => decide (candidate.1 = site.reason)) = none)
    (found : base.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site)
    (below : BelowCallable nativeProgram site.reason) :
    Packet execution certificate context environment site functions program entry before after mapping world location cell store := by
  have decoded := read_diagnostic_of_issued receiver present rebuilt positive ordinary noBoundary found below
  exact ⟨⟨sourceFault, reachedHeap, nativeFault, decoded⟩,
    read, checkedExact, ambientExact, expression, binder, span, token⟩

/-- The real read packet survives public observation beside the exact exported
heap. Export acceptance is independent of Source/native heap representation;
no equality between the two heap formats is inferred here. -/
theorem Packet.observe
    (packet : Packet execution certificate context environment site functions program entry before after mapping world location cell store)
    {exportFuel : Option Nat}
    {exported : SourceCoreCallableIndexedHeapOutputs.Export prepared.output
      execution.completion execution.initial.heap}
    (heapExport : SourceCoreCallableIndexedHeapOutputs.exportHeap prepared.output
      execution.completion execution.initial.heap
      (exportFuel.getD execution.exportFuel) = .ok exported) :
    Packet execution certificate context environment site functions program entry before after mapping world location cell store ∧
      execution.observe exportFuel = .ok (.fault (.uninitializedLocal site.binder) ⟨exported.heap⟩) :=
  ⟨packet, CallableIndexedOwnedPublicFaultObservation.observe_failed execution heapExport
    packet.observation.nativeFault packet.observation.decoded⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicReadFaultObservation
