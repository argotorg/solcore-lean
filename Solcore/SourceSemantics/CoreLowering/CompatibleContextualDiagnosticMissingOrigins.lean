import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationRanges
import Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticIndexOrigins

/-! Missing-row ownership follows actual accepted suffixes. Query views and
canonical uniqueness identify the same occurrence and span only after genuine
reason ownership has selected the expression class and full specialization key. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticMissingOrigins
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CallableIndexedOwnedContextualDiagnosticSources
open CompatibleExpressionMissingSourceReceipts
abbrev Key := SourceSpecialization.SpecializationKey

/-- The literal supplied source receives its actual appended expression row. -/
theorem Inventory.expression_missing_at {sources : List (Key × TypedSource)} {indices : List IndexSite}
    {places : List PlaceSite} {missing : List MissingSite} (inventory : Inventory sources sources indices places missing)
    {owner : Key} {source : TypedSource} (member : (owner, source) ∈ sources)
    {node : ExpressionNode} {mapping key : ExpressionId}
    (contains : SourceSemantics.ContainsExpression source node.id node) (form : node.form = .index mapping key) :
    ∃ row, row ∈ missing ∧ ExpressionAt indices owner source node row :=
  inventory.covered owner source member node contains.1 mapping key form

/-- The appended row uses exactly the reason selected by the original lookup. -/
theorem ExpressionAt.reason_at {program : SourceCoreDataPlaceFaultSites.Program}
    {owner : Key} {source : TypedSource} {node : ExpressionNode} {row : MissingSite}
    (receipt : ExpressionAt program.expressions.indices owner source node row) :
    row.base = program.reasonAt owner node.id := by
  obtain ⟨mapping, key, base, keyType, valueType, selected, _form, _lookup, _mappingView, _valueView, found, rowEq⟩ := receipt
  rw [rowEq]
  simp only [SourceCoreDataPlaceFaultSites.Program.reasonAt, SourceCoreDataFaultSites.Program.reasonAt, found]

/-- A row at this genuine selected reason cannot belong to a place allocation
or to a different expression key. Its issuer raw type stays independent. -/
theorem Inventory.row_site_span {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    {places : List PlaceSite} {missing : List MissingSite} (inventory : Inventory sources visited indices places missing)
    {owner : Key} {canonical : TypedSource} (views : QuerySourceViews owner canonical sources)
    (unique : SourceSemantics.NodeOccurrencesUnique canonical) {node : ExpressionNode}
    (contains : SourceSemantics.ContainsExpression canonical node.id node)
    {selected : IndexSite}
    (found : indices.find? (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = some selected)
    {row : MissingSite} (member : row ∈ missing) (sameReason : row.base = selected.reason) :
    row.owner = owner ∧ row.site = .occurrence node.id.occurrence ∧ row.binder = none ∧ row.span = node.span := by
  have selectedMember := List.mem_of_find?_eq_some found
  have hit : selected.owner = owner ∧ selected.expression = node.id :=
    of_decide_eq_true (List.find?_some (p := fun site : IndexSite => decide (site.owner = owner ∧ site.expression = node.id)) found)
  rcases inventory.origins row member with ⟨actualOwner, source, issuer, sourceMember, owns, issuerContains, receipt⟩ |
    ⟨actualOwner, source, issuer, assignment, _sourceMember, _owns, _issuerContains, receipt⟩
  · obtain ⟨mapping, key, base, keyType, valueType, actualIndex, issuerForm, _lookup, _mappingView, _valueView, actualFound, rowEq⟩ := receipt
    have actualHit : actualIndex.owner = actualOwner ∧ actualIndex.expression = issuer.id :=
      of_decide_eq_true (List.find?_some (p := fun site : IndexSite => decide (site.owner = actualOwner ∧ site.expression = issuer.id)) actualFound)
    have reasonEq : selected.reason = actualIndex.reason := by simpa only [rowEq] using sameReason.symm
    have sameKey := inventory.ownership.index selected selectedMember actualIndex
      (List.mem_of_find?_eq_some actualFound) reasonEq
    have ownerEq : actualOwner = owner := actualHit.1.symm.trans (sameKey.1.symm.trans hit.1)
    have idEq : issuer.id = node.id := actualHit.2.symm.trans (sameKey.2.symm.trans hit.2)
    have view := views actualOwner source sourceMember ownerEq
    rw [idEq] at issuerContains
    obtain ⟨_canonicalForm, span⟩ := view.index_span_at unique contains issuerContains issuerForm
    simp only [rowEq, ownerEq, idEq, span, and_self]
  · obtain ⟨place, key, keyNode, valueType, placeMember, _owner, _location, _binder, kind, _lookup, rowEq⟩ := receipt
    have reasonEq : selected.reason = place.reason := by simpa only [rowEq] using sameReason.symm
    exact False.elim (inventory.ownership.separate selected selectedMember place placeMember valueType kind reasonEq)

/-- Public source coverage retains the suffix from that literal canonical row;
no receiving metadata or runtime value supplies this static acceptance. -/
theorem FactoryAt.expression_missing_at {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : FactoryAt prepared diagnostics) {owner : Key} {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok row)
    {node : ExpressionNode} {mapping key : ExpressionId}
    (contains : SourceSemantics.ContainsExpression row.function.typedBody node.id node)
    (form : node.form = .index mapping key) :
    ∃ missing, missing ∈ diagnostics.missing ∧
      ExpressionAt diagnostics.program.expressions.indices owner row.function.typedBody node missing ∧
      missing.base = diagnostics.program.reasonAt owner node.id := by
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  have inventory := (CompatiblePlaceMissingPreparationRanges.prepare_missing_origins accepted).2
  have member : (owner, row.function.typedBody) ∈ (prepared.plan.specializations.map
      (fun row => (row.key, row.function.typedBody)) ++ prepared.contexts.map (fun item => (item.caller.key, item.source))) := by
    apply List.mem_append_left
    have filtered : row ∈ prepared.plan.specializations.filter (fun actual => decide (actual.key = owner)) := by
      rw [selected_filter record]
      exact List.mem_singleton_self _
    exact List.mem_map.mpr ⟨row, (List.mem_filter.mp filtered).1, by rw [selected_key record]⟩
  obtain ⟨missing, missingMember, receipt⟩ := Inventory.expression_missing_at inventory member contains form
  exact ⟨missing, missingMember, receipt, ExpressionAt.reason_at receipt⟩

/-- Same-token actual expanded rows have the same genuine base; ownership and
Source views then determine occurrence and span independently of raw types. -/
theorem FactoryAt.expanded_row_fields {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : FactoryAt prepared diagnostics) {owner : Key} {function : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok function)
    (unique : SourceSemantics.NodeOccurrencesUnique function.function.typedBody)
    {node : ExpressionNode} (contains : SourceSemantics.ContainsExpression function.function.typedBody node.id node)
    {site : MissingSite} (member : site ∈ diagnostics.missing)
    (receipt : ExpressionAt diagnostics.program.expressions.indices owner function.function.typedBody node site)
    {registry : SourceCoreRawMetadata.Registry}
    (limits : registry.limits.maxEntries = diagnostics.context.registry.limits.maxEntries)
    (budget : registry.length ≤ registry.limits.maxEntries)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    {row : Word × Diagnostic}
    (origin : CompatiblePlaceMissingDiagnosticRows.MissingRow registry diagnostics.missing row)
    (same : row.1 = site.base.add header) :
    row.2.error = .typeMismatch rawValue none ∧ row.2.site = .occurrence node.id.occurrence ∧ row.2.span = some node.span := by
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  have inventory := (CompatiblePlaceMissingPreparationRanges.prepare_missing_origins accepted).2
  have ranges := (CompatiblePlaceMissingPreparationRanges.prepare_ranges accepted).1
  have actualRanges : CompatiblePlaceMissingDiagnosticAssociation.Ranges registry.limits.maxEntries diagnostics.missing :=
    limits.symm ▸ ranges
  obtain ⟨actual, actualMember, actualKey, actualValue, actualHeader, actualMetadata, _keyView, _valueView,
    actualToken, _actualBound, actualDiagnostic⟩ := origin.metadata
  have leftBound := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound metadata) budget
  have rightBound := Nat.le_trans (CompatiblePlaceMissingDiagnosticRows.metadata_headerBound actualMetadata) budget
  have leftReserved := actualRanges.reserved site member
  have rightReserved := actualRanges.reserved actual actualMember
  have tokens : site.base.add header = actual.base.add actualHeader := same.symm.trans actualToken
  have baseEq : actual.base = site.base := by
    rcases actualRanges.separated site member actual actualMember with equal | before | after
    · exact equal.symm
    · exact False.elim (token_ranges_disjoint _ _ _ _ _ _ leftReserved rightReserved leftBound rightBound before tokens)
    · exact False.elim (token_ranges_disjoint _ _ _ _ _ _ rightReserved leftReserved rightBound leftBound after tokens.symm)
  obtain ⟨mapping, key, base, keyType, valueType, selected, _form, _lookup, _mappingView, _valueView, found, rowEq⟩ := receipt
  have reasonEq : actual.base = selected.reason := by simpa only [rowEq] using baseEq
  have fields := Inventory.row_site_span inventory (factory.source_views record) unique contains found actualMember reasonEq
  refine ⟨CompatiblePlaceMissingDiagnosticAssociation.row_error actualRanges budget member metadata origin same, ?_, ?_⟩
  · rw [actualDiagnostic]
    exact fields.2.1
  · rw [actualDiagnostic, fields.2.2.2]

end Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticMissingOrigins
