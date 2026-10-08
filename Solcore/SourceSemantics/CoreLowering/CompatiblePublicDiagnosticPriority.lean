import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationRanges
import Solcore.SourceSemantics.CoreLowering.CompatibleCallableDiagnosticBounds

/-! Actual preparation and table rebuilding retain the diagnostic priorities
for original reads and authenticated missing-default tokens. Source occurrence
association and successful public compiler preparation remain separate receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePublicDiagnosticPriority
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CompatiblePlaceMissingReservedReceipts
open CallableIndexedOwnedPublicFaultReceiverTables

/-- Rebuilding against the actual receiving registry cannot let an expanded
mapping diagnostic shadow an original read. -/
theorem read_extra_different {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {base : SourceCoreProgramFaultSites.Program} {initialExtra : List (Word × Diagnostic)}
    (reserved : ReservedAt context plan root program base initialExtra)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table)
    {read : SourceCoreFaultSites.ReadSite} (readMember : read ∈ base.rootTable.reads)
    {row : Word × Diagnostic} (origin : MissingDiagnosticOrigin registry program.missing row) :
    read.reason ≠ row.1 := by
  obtain ⟨site, siteMember, rawKey, rawValue, header, lookup, _keys, _values, within, token, _diagnostic⟩ :=
    origin.mapping_header
  have metadata : MetadataRep registry (.mapping rawKey rawValue) header := ⟨lookup⟩
  have limits : registry.limits.maxEntries = context.registry.limits.maxEntries :=
    congrArg SourceCoreRawMetadata.Limits.maxEntries extension.limits
  have bounded := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound metadata)
    (CompatiblePlaceMissingDiagnosticRows.tableForRegistry_budget rebuilt)
  have positive : 0 < header.val := by
    by_cases zero : header.val = 0
    · exact False.elim (metadata.nonzero (Fin.ext zero))
    · omega
  have number : (site.base.add header).val = site.base.val + header.val := by
    change (site.base.val + header.val) % wordModulus = site.base.val + header.val
    exact Nat.mod_eq_of_lt within
  intro same
  have equal := congrArg Fin.val (same.trans token.symm)
  rw [number] at equal
  have outside := reserved.readsOutside site siteMember read readMember
  rw [limits] at bounded
  rcases outside with before | after <;> omega

/-- The base producer's exact binder, occurrence and span remain selected
through the actual fixed prefix and receiving-registry expansion. -/
theorem read_diagnostic {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {base : SourceCoreProgramFaultSites.Program} {initialExtra : List (Word × Diagnostic)}
    (reserved : ReservedAt context plan root program base initialExtra)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table)
    {read : SourceCoreFaultSites.ReadSite} (member : read ∈ base.rootTable.reads) :
    table.diagnostic? read.reason = some {
      error := .uninitializedLocal read.binder
      site := .occurrence read.expression.occurrence
      span := some read.span } := by
  obtain ⟨positive, ordinary, _initialBoundary, found, _initialDecoded⟩ :=
    SourceCoreProgramFaultSites.prepare_read_diagnostic reserved.baseAccepted member
  obtain ⟨extra, _extraAccepted, actual, origins⟩ := program.tableForRegistry_receipt rebuilt
  have absent : (program.fixed ++ extra).find? (fun item => decide (item.1 = read.reason)) = none := by
    apply List.find?_eq_none.mpr
    intro row rowMember matched
    have same : read.reason = row.1 := (of_decide_eq_true matched).symm
    rcases List.mem_append.mp rowMember with fixed | missing
    · exact reserved.readSafe read member row fixed same
    · exact read_extra_different reserved rebuilt member (origins row missing) same
  rw [actual, reserved.sameRoot]
  exact SourceCoreFaultSites.Table.read_diagnostic positive ordinary absent found

/-- The actual reserved endpoint bounds every genuine receiving metadata
header, so its emitted missing-default token precedes the callable minimum. -/
theorem missing_token_below {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {base : SourceCoreProgramFaultSites.Program} {initialExtra : List (Word × Diagnostic)}
    (reserved : ReservedAt context plan root program base initialExtra)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table)
    {site : MissingSite} (member : site ∈ program.missing)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header) :
    (site.base.add header).val < program.nextReason := by
  have limits : registry.limits.maxEntries = context.registry.limits.maxEntries :=
    congrArg SourceCoreRawMetadata.Limits.maxEntries extension.limits
  have bounded := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound metadata)
    (CompatiblePlaceMissingDiagnosticRows.tableForRegistry_budget rebuilt)
  rw [limits] at bounded
  rw [token_nonWrapping _ _ _ (reserved.legacy.1.reserved site member) bounded]
  have below := reserved.missingBelow site member
  omega

/-- Public fault observation uses the actual rebuilt base and the actual
callable allocation at the preparation's final reason boundary. -/
theorem receiver_read_diagnostic {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {completion : SourceCoreCallableIndexedPrograms.Completion prepared}
    (receiver : IssuedAt prepared completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (SourceCoreCompatibleValues.Context.initial checked)}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare (SourceCoreCompatibleValues.Context.initial checked)
      plan root sources = .ok issued)
    (present : prepared.base.diagnostics = some issued)
    {callablePlan : SourceCoreStageCodebook.Plan} {contracts : SourceCoreStageCodebook.Table}
    {callable : SourceCoreCallableFaultSites.Program}
    (allocated : SourceCoreCallableFaultSites.prepare callablePlan contracts issued.program.rootTable issued.nextReason = .ok callable)
    (callablePresent : prepared.base.callableDiagnostics = some callable)
    {read : SourceCoreFaultSites.ReadSite} (member : read ∈ issued.program.rootTable.reads) :
    completion.result.diagnostics.diagnostic? read.reason = some {
      error := .uninitializedLocal read.binder
      site := .occurrence read.expression.occurrence
      span := some read.span } := by
  obtain ⟨actual, rebuilt, table⟩ := receiver
  rw [present] at rebuilt
  obtain ⟨base, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  have member : read ∈ base.rootTable.reads := by simpa only [reserved.sameRoot] using member
  rw [table, CompatibleCallableDiagnosticBounds.append_diagnostic allocated callablePresent
    (reserved.readsBelow read member)]
  exact read_diagnostic reserved rebuilt member

/-- A genuine missing site and raw metadata retain their error through the
same public receiver. Duplicate tokens keep the producer's selected span. -/
theorem receiver_missing_diagnostic {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {completion : SourceCoreCallableIndexedPrograms.Completion prepared}
    (receiver : IssuedAt prepared completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (SourceCoreCompatibleValues.Context.initial checked)}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare (SourceCoreCompatibleValues.Context.initial checked)
      plan root sources = .ok issued)
    (present : prepared.base.diagnostics = some issued)
    {callablePlan : SourceCoreStageCodebook.Plan} {contracts : SourceCoreStageCodebook.Table}
    {callable : SourceCoreCallableFaultSites.Program}
    (allocated : SourceCoreCallableFaultSites.prepare callablePlan contracts issued.program.rootTable issued.nextReason = .ok callable)
    (callablePresent : prepared.base.callableDiagnostics = some callable)
    {site : MissingSite} (member : site ∈ issued.missing)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep completion.result.context.registry (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType) :
    ∃ diagnostic, completion.result.diagnostics.diagnostic? (site.base.add header) = some diagnostic ∧
      diagnostic.error = .typeMismatch rawValue none := by
  obtain ⟨actual, rebuilt, table⟩ := receiver
  rw [present] at rebuilt
  obtain ⟨base, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  rw [table, CompatibleCallableDiagnosticBounds.append_diagnostic allocated callablePresent
    (missing_token_below reserved rebuilt member metadata)]
  exact CompatiblePlaceMissingPreparationRanges.table_diagnostic accepted rebuilt member metadata keyView valueView

end Solcore.SourceSemantics.CoreLowering.CompatiblePublicDiagnosticPriority
