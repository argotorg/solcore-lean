import Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticMissingOrigins
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicCallableAllocationReceipts

/-! Actual canonical missing rows identify the first received diagnostic's
occurrence and span. Raw receiving metadata and its canonical base view remain
independent certificates. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualMissingDiagnosticObservations
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites
open CompatibleExpressionMissingSourceReceipts
open CallableIndexedOwnedContextualDiagnosticSources
open CallableIndexedOwnedPublicFaultReceiverTables

abbrev Key := SourceSpecialization.SpecializationKey

/-- This is the genuine base lookup and raw mapping view at the canonical
Source. Receiving metadata does not supply this association. -/
def CanonicalMappingView (source : TypedSource) (base : ExpressionId)
    (rawKey rawValue : TypeSystem.Ty) : Prop :=
  ∃ node, source.lookupExpression? base = some node ∧
    SourceCoreRawMetadata.runtimeType node.type =
      .mapping (SourceCoreRawMetadata.runtimeType rawKey) (SourceCoreRawMetadata.runtimeType rawValue)

/-- The same accepted suffix and actual canonical lookup supply its two
runtime views, preserving the independent receiving raw types. -/
theorem ExpressionAt.receiving_views {indices : List SourceCoreDataFaultSites.IndexSite}
    {owner : Key} {source : TypedSource} {node : ExpressionNode} {missing : MissingSite}
    (receipt : ExpressionAt indices owner source node missing)
    {base key : ExpressionId} (form : node.form = .index base key)
    {rawKey rawValue : TypeSystem.Ty} (view : CanonicalMappingView source base rawKey rawValue) :
    SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType missing.keyType ∧
    SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType missing.valueType := by
  obtain ⟨actualBase, actualKey, baseNode, keyType, valueType, selected,
    actualForm, found, mappingView, valueView, _selected, rowEq⟩ := receipt
  obtain ⟨rfl, rfl⟩ := ExpressionForm.index.inj (actualForm.symm.trans form)
  obtain ⟨canonicalBase, canonicalFound, canonicalView⟩ := view
  have sameNode := Option.some.inj (found.symm.trans canonicalFound)
  subst canonicalBase
  have components := TypeSystem.Ty.mapping.inj (mappingView.symm.trans canonicalView)
  rw [rowEq]
  refine ⟨?_, components.2.symm.trans valueView.symm⟩
  rw [components.1]
  exact (SourceCoreRawMetadata.runtimeType_idempotent rawKey).symm

/-- The actual FIRST matching row is an expanded missing row. Its genuine
Source ownership identifies the exact occurrence and span. -/
theorem FactoryAt.table_expression_missing_diagnostic
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : FactoryAt prepared issued) {owner : Key} {function : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok function)
    (unique : NodeOccurrencesUnique function.function.typedBody)
    {node : ExpressionNode} {base key : ExpressionId}
    (contains : ContainsExpression function.function.typedBody node.id node)
    (form : node.form = .index base key)
    {registry : SourceCoreRawMetadata.Registry} {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (view : CanonicalMappingView function.function.typedBody base rawKey rawValue)
    {extension : SourceCoreRawMetadata.Extends issued.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : issued.tableForRegistry registry extension = .ok table)
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header) :
    ∃ missing, missing ∈ issued.missing ∧
      ExpressionAt issued.program.expressions.indices owner function.function.typedBody node missing ∧
      missing.base = issued.program.reasonAt owner node.id ∧
      table.diagnostic? (missing.base.add header) = some {
        error := .typeMismatch rawValue none,
        site := .occurrence node.id.occurrence, span := some node.span } := by
  obtain ⟨missing, member, receipt, providerBase⟩ :=
    CompatibleContextualDiagnosticMissingOrigins.FactoryAt.expression_missing_at factory record contains form
  obtain ⟨keyView, valueView⟩ := ExpressionAt.receiving_views receipt form view
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  obtain ⟨ranges, positive, fixed, escaped⟩ := CompatiblePlaceMissingPreparationRanges.prepare_ranges accepted
  have limits : registry.limits.maxEntries =
      (SourceCoreCompatibleValues.Context.initial checked).registry.limits.maxEntries :=
    congrArg SourceCoreRawMetadata.Limits.maxEntries extension.limits
  have actualRanges : CompatiblePlaceMissingDiagnosticAssociation.Ranges registry.limits.maxEntries issued.missing :=
    limits.symm ▸ ranges
  have budget := CompatiblePlaceMissingDiagnosticRows.tableForRegistry_budget rebuilt
  have bounded := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound metadata) budget
  have reserved := actualRanges.reserved missing member
  obtain ⟨cover, coverMember, coverToken, _coverOrigin⟩ :=
    CompatiblePlaceMissingDiagnosticRows.tableForRegistry_contains rebuilt member metadata keyView valueView reserved
  have covered : (table.additional.find? (fun candidate => decide (candidate.1 = missing.base.add header))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨cover, coverMember, by simp only [coverToken, decide_true]⟩
  have sameEscape : table.escapedReason = issued.program.rootTable.escapedReason := by
    obtain ⟨extra, _produced, tableEq, _origins⟩ := issued.tableForRegistry_receipt rebuilt
    rw [tableEq]
  have number := SourceCoreCompatibleDataPlaceFaultSites.token_nonWrapping
    missing.base header registry.limits.maxEntries reserved bounded
  have headerPositive : 0 < header.val := by
    by_cases zero : header.val = 0
    · exact False.elim (metadata.nonzero (Fin.ext zero))
    · omega
  have nonzero : missing.base.add header ≠ Word.zero := by
    intro zero
    have numbers := congrArg Fin.val zero
    rw [number] at numbers
    change missing.base.val + header.val = 0 at numbers
    omega
  have ordinary : missing.base.add header ≠ table.escapedReason := by
    intro same
    have numbers := congrArg Fin.val same
    rw [number, sameEscape] at numbers
    have separated := escaped missing member
    rw [← limits] at separated
    rcases separated with before | after <;> omega
  cases found : table.additional.find? (fun candidate => decide (candidate.1 = missing.base.add header)) with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at covered
  | some selected =>
    have selectedMember := List.mem_of_find?_eq_some found
    have selectedToken : selected.1 = missing.base.add header :=
      of_decide_eq_true (List.find?_some
        (p := fun candidate : Word × Diagnostic => decide (candidate.1 = missing.base.add header)) found)
    have origin : CompatiblePlaceMissingDiagnosticRows.MissingRow registry issued.missing selected := by
      rcases CompatiblePlaceMissingDiagnosticRows.tableForRegistry_rows rebuilt selectedMember with old | missingRow
      · exact False.elim (CompatiblePlaceMissingDiagnosticAssociation.fixed_different metadata budget reserved
          (by simpa only [limits] using fixed missing member selected old) selectedToken)
      · exact missingRow
    have fields := CompatibleContextualDiagnosticMissingOrigins.FactoryAt.expanded_row_fields
      factory record unique contains member receipt limits budget metadata origin selectedToken
    have diagnosticEq : selected.2 = {
        error := .typeMismatch rawValue none,
        site := .occurrence node.id.occurrence, span := some node.span } := by
      cases actual : selected.2 with
      | mk error site span =>
        rw [actual] at fields
        obtain ⟨rfl, rfl, rfl⟩ := fields
        rfl
    refine ⟨missing, member, receipt, providerBase, ?_⟩
    simp only [SourceCoreFaultSites.Table.diagnostic?, nonzero, ordinary, found, if_false]
    exact congrArg some diagnosticEq

/-- Sealed compilation supplies actual contextual preparation and callable
allocation. The canonical row and its base are derived internally. -/
theorem receiver_index_missing_diagnostic (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {owner : Key} {function : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok function)
    (unique : NodeOccurrencesUnique function.function.typedBody)
    {node : ExpressionNode} {base key : ExpressionId}
    (contains : ContainsExpression function.function.typedBody node.id node)
    (form : node.form = .index base key)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (view : CanonicalMappingView function.function.typedBody base rawKey rawValue)
    (metadata : MetadataRep completion.result.context.registry (.mapping rawKey rawValue) header) :
    completion.result.diagnostics.diagnostic? ((issued.program.reasonAt owner node.id).add header) = some {
      error := .typeMismatch rawValue none,
      site := .occurrence node.id.occurrence, span := some node.span } := by
  have factory := CallableIndexedOwnedContextualDiagnosticSources.of_compiled compiled present
  have allocation := CompatiblePublicCallableAllocationReceipts.of_compiled compiled present
  obtain ⟨actual, rebuilt, tableEq⟩ := receiver
  rw [present] at rebuilt
  obtain ⟨missing, member, _receipt, providerBase, decoded⟩ :=
    FactoryAt.table_expression_missing_diagnostic factory record unique contains form view rebuilt metadata
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  obtain ⟨baseProgram, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  have below : BelowCallable compiled.indexed ((issued.program.reasonAt owner node.id).add header) := by
    simpa only [providerBase] using allocation.below
      (CompatiblePublicDiagnosticPriority.missing_token_below reserved rebuilt member metadata)
  rw [tableEq, appendCallable_diagnostic_of_below below]
  simpa only [providerBase] using decoded

end Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualMissingDiagnosticObservations
