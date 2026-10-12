import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedAssignmentFaults
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicCallableAllocationReceipts

/-! The accepted compatible issuer bounds every token decoded by its actual
receiving-registry table. The sealed callable allocation and genuine completion
retain that same lookup in the public filtered append. Missing-default and
projected-uninitialized interpretation therefore follow from the literal public
decoder. No FaultRep inclusion, hypothetical decoder law, registry inverse or
execution is supplied. Source occurrence ownership remains independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReceivingPreparedShapeInterpretations
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites
open CompatiblePlaceMissingReservedReceipts
open CallableIndexedOwnedPublicFaultReceiverTables
open CallableIndexedOwnedPublicDecodedAssignmentFaults
universe u v

private theorem extra_token_below
    {context : SourceCoreCompatibleDataPlaceFaultSites.Context} {plan : Plan} {root : Key}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {base : SourceCoreProgramFaultSites.Program} {initialExtra : List (Word × Diagnostic)}
    (reserved : ReservedAt context plan root issued base initialExtra)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends issued.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry registry extension = .ok table)
    {row : Word × Diagnostic} (origin : MissingDiagnosticOrigin registry issued.missing row) :
    row.1.val < issued.nextReason := by
  obtain ⟨site, member, rawKey, rawValue, header, lookup, _keys, _values, within, token, _diagnostic⟩ :=
    origin.mapping_header
  have metadata : MetadataRep registry (.mapping rawKey rawValue) header := ⟨lookup⟩
  have bounded := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound metadata)
    (CompatiblePlaceMissingDiagnosticRows.tableForRegistry_budget rebuilt)
  have limits : registry.limits.maxEntries = context.registry.limits.maxEntries :=
    congrArg SourceCoreRawMetadata.Limits.maxEntries extension.limits
  rw [limits] at bounded
  have number : row.1.val = site.base.val + header.val := by
    rw [← token]
    change (site.base.val + header.val) % wordModulus = site.base.val + header.val
    exact Nat.mod_eq_of_lt within
  have below := reserved.missingBelow site member
  rw [number]
  omega

/-- Decode the actual table's existing priority branches. Original fixed rows,
reads, escaped control and zero retain their producer bounds; expanded rows
use their authentic receiving header and reserved range. -/
theorem decoded_token_below
    {context : SourceCoreCompatibleDataPlaceFaultSites.Context} {plan : Plan} {root : Key}
    {sources : List (Key × TypedSource)}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok issued)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends issued.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry registry extension = .ok table)
    {token : Word} {diagnostic : Diagnostic}
    (decoded : table.diagnostic? token = some diagnostic) : token.val < issued.nextReason := by
  obtain ⟨base, initialExtra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  obtain ⟨extra, _extraAccepted, tableEq, origins⟩ := issued.tableForRegistry_receipt rebuilt
  by_cases zero : token = Word.zero
  · rw [zero]
    exact reserved.positive
  · by_cases escaped : token = table.escapedReason
    · have same : table.escapedReason = base.rootTable.escapedReason := by
        rw [tableEq, reserved.sameRoot]
      rw [escaped, same]
      exact reserved.escapedBelow
    · simp only [SourceCoreFaultSites.Table.diagnostic?, zero, escaped, ↓reduceIte] at decoded
      cases first : table.additional.find? (fun row => decide (row.1 = token)) with
      | some row =>
        have matched : row.1 = token := of_decide_eq_true (List.find?_some
          (p := fun candidate : Word × Diagnostic => decide (candidate.1 = token)) first)
        have member : row ∈ issued.fixed ++ extra := by
          simpa only [tableEq] using List.mem_of_find?_eq_some first
        rw [← matched]
        rcases List.mem_append.mp member with fixed | expanded
        · exact reserved.fixedBelow row fixed
        · exact extra_token_below reserved rebuilt (origins row expanded)
      | none =>
        simp only [first] at decoded
        cases found : table.reads.find? (fun read => decide (read.reason = token)) with
        | none => simp [found] at decoded
        | some read =>
          have matched : read.reason = token := of_decide_eq_true (List.find?_some
            (p := fun candidate : SourceCoreFaultSites.ReadSite => decide (candidate.reason = token)) found)
          have member : read ∈ base.rootTable.reads := by
            simpa only [tableEq, reserved.sameRoot] using List.mem_of_find?_eq_some found
          rw [← matched]
          exact reserved.readsBelow read member

/-- The sealed compiler supplies compatible preparation and callable allocation.
The actual completion supplies the receiving rebuild and exact public append;
the separately named preappend table is identified by that same successful action. -/
theorem receiver_lookup (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {table : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry completion.result.context.registry completion.result.extension = .ok table)
    {token : Word} {diagnostic : Diagnostic}
    (decoded : table.diagnostic? token = some diagnostic) :
    completion.result.diagnostics.diagnostic? token = some diagnostic := by
  obtain ⟨root, sources, accepted⟩ :=
    CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  obtain ⟨actual, actualRebuilt, tableEq⟩ := receiver
  rw [present] at actualRebuilt
  have same : actual = table := Except.ok.inj (actualRebuilt.symm.trans rebuilt)
  subst actual
  rw [tableEq, appendCallable_diagnostic_of_below
    ((CompatiblePublicCallableAllocationReceipts.of_compiled compiled present).below
      (decoded_token_below accepted rebuilt decoded))]
  exact decoded

/-- Both reached-place fields are constructed internally from the same exact
preappend decoder and public receiver. The actual reached state, prepared place
and runtime location are retained; no Source fault or execution is manufactured. -/
theorem reached_interpretation (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {table : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry completion.result.context.registry completion.result.extension = .ok table)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    {functions : FunctionModel compiled.compatible.checked.catalog ambient} {Records : Type v}
    {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {environment : Dynamic.Environment} {place : PlaceResolution}
    {prepared : SourceCoreCompatibleDataPlaces.Prepared}
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex) :
    CallableIndexedOwnedPublicPreparedShapeDiagnostics.ReachedTableInterpretation
      compiled.compatible.checked completion.result.context.registry functions protocol
      environment place prepared initial table (faults completion.result.diagnostics) := by
  constructor
  · intro rawValue token diagnostic decoded error
    refine ⟨diagnostic, receiver_lookup compiled receiver present rebuilt decoded, ?_⟩
    rw [error]
    exact .missing rawValue
  · intro reachedIndex reached location related witness diagnostic decoded error
    refine ⟨diagnostic, receiver_lookup compiled receiver present rebuilt decoded, ?_⟩
    rw [error]
    exact .projectedUninitialized location

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReceivingPreparedShapeInterpretations
