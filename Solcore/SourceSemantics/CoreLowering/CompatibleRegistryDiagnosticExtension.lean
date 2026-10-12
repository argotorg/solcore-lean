import Solcore.SourceSemantics.CoreLowering.CompatibleMissingDiagnosticExtension
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedStagedCallFaults
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicDiagnosticPriority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicCallableAllocationReceipts

/-! Authentic diagnostic receivers preserve previously decoded errors when the
actual raw metadata registry extends. The fixed function model is unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CompatiblePlaceMissingReservedReceipts
open CallableIndexedOwnedPublicFaultReceiverTables

private theorem extra_below {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {base : SourceCoreProgramFaultSites.Program} {initialExtra : List (Word × Diagnostic)}
    (reserved : ReservedAt context plan root program base initialExtra)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table)
    {row : Word × Diagnostic} (origin : MissingDiagnosticOrigin registry program.missing row) :
    row.1.val < program.nextReason := by
  obtain ⟨site, member, rawKey, rawValue, header, lookup, _keys, _values, _within, token, _diagnostic⟩ :=
    origin.mapping_header
  have belowBound := CompatiblePublicDiagnosticPriority.missing_token_below reserved rebuilt member
    (show MetadataRep registry (.mapping rawKey rawValue) header from ⟨lookup⟩)
  simpa only [token] using belowBound

private theorem suffix_preserved {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (prepared : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program)
    {registry future : SourceCoreRawMetadata.Registry}
    {leftExtension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {rightExtension : SourceCoreRawMetadata.Extends program.context.registry future}
    {left right : SourceCoreFaultSites.Table}
    (leftBuilt : program.tableForRegistry registry leftExtension = .ok left)
    (rightBuilt : program.tableForRegistry future rightExtension = .ok right)
    (preserves : ∀ {oldRows newRows},
      missingDiagnostics registry program.missing = .ok oldRows →
      missingDiagnostics future program.missing = .ok newRows →
      ∀ {token row}, oldRows.find? (fun item => decide (item.1 = token)) = some row →
        newRows.find? (fun item => decide (item.1 = token)) = some row)
    (suffix : List (Word × Diagnostic))
    (above : ∀ row, row ∈ suffix → program.nextReason ≤ row.1.val)
    {token : Word} {diagnostic : Diagnostic}
    (decoded : {left with additional := left.additional ++ suffix}.diagnostic? token = some diagnostic) :
    {right with additional := right.additional ++ suffix}.diagnostic? token = some diagnostic := by
  obtain ⟨base, initialExtra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt prepared
  obtain ⟨oldRows, oldBuilt, oldShape, _oldOrigins⟩ := program.tableForRegistry_receipt leftBuilt
  obtain ⟨newRows, newBuilt, newShape, newOrigins⟩ := program.tableForRegistry_receipt rightBuilt
  rw [oldShape, reserved.sameRoot] at decoded
  rw [newShape, reserved.sameRoot]
  by_cases zero : token = Word.zero
  · simpa only [SourceCoreFaultSites.Table.diagnostic?, zero, if_pos] using decoded
  by_cases escaped : token = base.rootTable.escapedReason
  · simpa only [SourceCoreFaultSites.Table.diagnostic?, zero, escaped, if_false, if_pos] using decoded
  simp only [SourceCoreFaultSites.Table.diagnostic?, zero, escaped, if_false, List.find?_append] at decoded ⊢
  cases fixed : program.fixed.find? (fun item => decide (item.1 = token)) with
  | some row => simpa only [fixed, Option.some_or] using decoded
  | none =>
    simp only [fixed, Option.none_or] at decoded ⊢
    cases old : oldRows.find? (fun item => decide (item.1 = token)) with
    | some row =>
      have current := preserves oldBuilt newBuilt old
      simpa only [old, current, Option.some_or] using decoded
    | none =>
      simp only [old, Option.none_or] at decoded
      cases appended : suffix.find? (fun item => decide (item.1 = token)) with
      | some row =>
        have rowMember := List.mem_of_find?_eq_some appended
        have same : row.1 = token := of_decide_eq_true (List.find?_some (p := fun item : Word × Diagnostic => decide (item.1 = token)) appended)
        have threshold := above row rowMember
        have absent : newRows.find? (fun item => decide (item.1 = token)) = none := by
          apply List.find?_eq_none.mpr
          intro added member matched
          have addedEq : added.1 = token := of_decide_eq_true matched
          have belowBound := extra_below reserved rightBuilt (newOrigins added member)
          rw [addedEq] at belowBound
          rw [same] at threshold
          omega
        simpa only [absent, Option.none_or, appended] using decoded
      | none =>
        simp only [appended] at decoded
        cases readAt : base.rootTable.reads.find? (fun site => decide (site.reason = token)) with
        | none => simp only [readAt, Option.map_none] at decoded; cases decoded
        | some read =>
          have member := List.mem_of_find?_eq_some readAt
          have same : read.reason = token := of_decide_eq_true (List.find?_some (p := fun site : SourceCoreFaultSites.ReadSite => decide (site.reason = token)) readAt)
          have absent : newRows.find? (fun item => decide (item.1 = token)) = none := by
            apply List.find?_eq_none.mpr
            intro added addedMember matched
            have addedEq : added.1 = token := of_decide_eq_true matched
            exact CompatiblePublicDiagnosticPriority.read_extra_different reserved rightBuilt member
              (newOrigins added addedMember) (same.trans addedEq.symm)
          simpa only [absent, Option.none_or, appended, readAt] using decoded

private theorem issued_preserved_of_rows (compiled : SourceCoreUnifiedCompilation.Compiled)
    {left right : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (leftIssued : IssuedAt compiled.indexed left.entry left.result.context.registry
      left.result.extension left.result.diagnostics)
    (rightIssued : IssuedAt compiled.indexed right.entry right.result.context.registry
      right.result.extension right.result.diagnostics)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some program)
    (preserves : ∀ {oldRows newRows},
      missingDiagnostics left.result.context.registry program.missing = .ok oldRows →
      missingDiagnostics right.result.context.registry program.missing = .ok newRows →
      ∀ {token row}, oldRows.find? (fun item => decide (item.1 = token)) = some row →
        newRows.find? (fun item => decide (item.1 = token)) = some row)
    {token : Word} {diagnostic : Diagnostic}
    (decoded : left.result.diagnostics.diagnostic? token = some diagnostic) :
    right.result.diagnostics.diagnostic? token = some diagnostic := by
  obtain ⟨root, sources, prepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  obtain ⟨leftBase, leftBuilt, leftTable⟩ := leftIssued
  obtain ⟨rightBase, rightBuilt, rightTable⟩ := rightIssued
  rw [present] at leftBuilt rightBuilt
  rw [leftTable] at decoded
  rw [rightTable]
  cases callableAt : compiled.indexed.base.callableDiagnostics with
  | none =>
    have result := suffix_preserved prepared leftBuilt rightBuilt preserves [] (by simp)
      (by simpa only [appendCallable, callableAt, List.append_nil] using decoded)
    simpa only [appendCallable, callableAt, List.append_nil] using result
  | some callable =>
    have allocation := CompatiblePublicCallableAllocationReceipts.of_compiled compiled present
    obtain ⟨contracts, allocated⟩ := (by
      simpa only [CompatiblePublicCallableAllocationReceipts.AllocationAt, callableAt] using allocation :
      ∃ contracts, SourceCoreCallableFaultSites.prepare compiled.indexed.base.plan contracts
        program.program.rootTable program.nextReason = .ok callable)
    let suffix := callable.rootTable.additional.filter (fun item => callable.unknown.val ≤ item.1.val)
    have above : ∀ row, row ∈ suffix → program.nextReason ≤ row.1.val := by
      intro row member
      have bound : callable.unknown.val ≤ row.1.val := of_decide_eq_true (List.mem_filter.mp member).2
      exact Nat.le_trans (CompatibleCallableDiagnosticBounds.prepare_unknown allocated).2 bound
    have result := suffix_preserved prepared leftBuilt rightBuilt preserves suffix above
      (by simpa only [appendCallable, callableAt, suffix] using decoded)
    simpa only [appendCallable, callableAt, suffix] using result

/-- The same compiled issuer preserves the complete previously selected
public diagnostic at a genuine extension of its raw metadata registry. -/
theorem diagnostic_preserved (compiled : SourceCoreUnifiedCompilation.Compiled)
    {left right : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (leftIssued : IssuedAt compiled.indexed left.entry left.result.context.registry
      left.result.extension left.result.diagnostics)
    (rightIssued : IssuedAt compiled.indexed right.entry right.result.context.registry
      right.result.extension right.result.diagnostics)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some program)
    (extension : SourceCoreRawMetadata.Extends left.result.context.registry right.result.context.registry)
    {token : Word} {diagnostic : Diagnostic}
    (decoded : left.result.diagnostics.diagnostic? token = some diagnostic) :
    right.result.diagnostics.diagnostic? token = some diagnostic := by
  obtain ⟨root, sources, prepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  have limits : left.result.context.registry.limits.maxEntries =
      compiled.compatible.checked.staticRegistry.limits.maxEntries :=
    congrArg SourceCoreRawMetadata.Limits.maxEntries left.result.extension.limits
  have ranges := (CompatiblePlaceMissingPreparationRanges.prepare_ranges prepared).1
  apply issued_preserved_of_rows compiled leftIssued rightIssued present (decoded := decoded)
  intro oldRows newRows oldBuilt newBuilt token row found
  exact CompatibleMissingDiagnosticExtension.missingDiagnostics_find_preserved extension
    (limits.symm ▸ ranges) oldBuilt newBuilt found

/-- A fixed semantic function model remains meaningful at the actual next
receiver. Only the diagnostic table changes, following real metadata extension. -/
theorem semantic_preserved (compiled : SourceCoreUnifiedCompilation.Compiled)
    {left right : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (leftIssued : IssuedAt compiled.indexed left.entry left.result.context.registry
      left.result.extension left.result.diagnostics)
    (rightIssued : IssuedAt compiled.indexed right.entry right.result.context.registry
      right.result.extension right.result.diagnostics)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some program)
    (extension : SourceCoreRawMetadata.Extends left.result.context.registry right.result.context.registry)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : CallableIndexedOwnedPublicDecodedCallFaults.faults left.result.diagnostics reason token) :
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults right.result.diagnostics (.semantic reason) token := by
  obtain ⟨diagnostic, decoded, view⟩ := represented
  exact ⟨diagnostic, diagnostic_preserved compiled leftIssued rightIssued present extension decoded, view⟩

/-- Stage-tagged failures preserve the same original call site and error view
as well as the exact decoded diagnostic. -/
theorem staged_preserved (compiled : SourceCoreUnifiedCompilation.Compiled)
    {left right : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (leftIssued : IssuedAt compiled.indexed left.entry left.result.context.registry
      left.result.extension left.result.diagnostics)
    (rightIssued : IssuedAt compiled.indexed right.entry right.result.context.registry
      right.result.extension right.result.diagnostics)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some program)
    (extension : SourceCoreRawMetadata.Extends left.result.context.registry right.result.context.registry)
    {failure : Staging.Recursive.Failure} {token : Word}
    (represented : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults left.result.diagnostics failure token) :
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults right.result.diagnostics failure token := by
  cases failure with
  | semantic reason => exact semantic_preserved compiled leftIssued rightIssued present extension represented
  | stage invocation call reason =>
    obtain ⟨diagnostic, decoded, view⟩ := represented
    exact ⟨diagnostic, diagnostic_preserved compiled leftIssued rightIssued present extension decoded, view⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
