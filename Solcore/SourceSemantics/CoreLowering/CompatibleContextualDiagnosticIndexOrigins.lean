import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationRanges
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources

/-! The unconditional issuer receipt combines with actual contextual Source
views only at the queried key. Canonical uniqueness fixes the owning occurrence
and span; raw substituted types remain the issuer's original types. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticIndexOrigins
open Core Frontend SourceInference
open CompatibleExpressionIndexSourceReceipts CallableIndexedOwnedContextualDiagnosticSources
abbrev Key := SourceSpecialization.SpecializationKey

/-- A genuine local read cannot have an index issuer at that same unique
canonical occurrence among the actual supplied Source views. -/
theorem Inventory.no_index_at_read {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    (inventory : Inventory sources visited indices) {owner : Key} {canonical : TypedSource}
    (views : QuerySourceViews owner canonical sources) (unique : SourceSemantics.NodeOccurrencesUnique canonical)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (contains : SourceSemantics.ContainsExpression canonical id node)
    (form : node.form = .reference name (.local binder)) :
    indices.find? (fun site => decide (site.owner = owner ∧ site.expression = id)) = none := by
  apply List.find?_eq_none.mpr
  intro site member matched
  have hit : site.owner = owner ∧ site.expression = id := of_decide_eq_true matched
  obtain ⟨actual, issuer, base, key, actualMember, _owns, issuerContains, issuerForm, _diagnostic⟩ :=
    inventory.origins site member
  have view := views site.owner actual actualMember hit.1
  rw [hit.2] at issuerContains
  exact view.no_index_at_read unique contains form issuerContains issuerForm

/-- The selected row comes from a literal actual issuer, while the genuine
query views identify the canonical index form and the exact span. -/
theorem Inventory.selected_origin {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    (inventory : Inventory sources visited indices) {owner : Key} {canonical : TypedSource}
    (views : QuerySourceViews owner canonical sources) (unique : SourceSemantics.NodeOccurrencesUnique canonical)
    {id : ExpressionId} {node : ExpressionNode} (contains : SourceSemantics.ContainsExpression canonical id node)
    {site : IndexSite} (found : indices.find? (fun site => decide (site.owner = owner ∧ site.expression = id)) = some site) :
    site.owner = owner ∧ site.expression = id ∧
    ∃ actual issuer base key,
      (owner, actual) ∈ sources ∧ actual.owner = owner.declaration ∧
      SourceSemantics.ContainsExpression actual id issuer ∧ issuer.form = .index base key ∧
      node.form = .index base key ∧ issuer.span = node.span ∧
      site.diagnostic = ⟨.typeMismatch issuer.type none, .occurrence id.occurrence, some node.span⟩ := by
  have hit : site.owner = owner ∧ site.expression = id := of_decide_eq_true
    (List.find?_some (p := fun site : IndexSite => decide (site.owner = owner ∧ site.expression = id)) found)
  obtain ⟨actual, issuer, base, key, member, owns, retained, form, diagnostic⟩ :=
    inventory.origins site (List.mem_of_find?_eq_some found)
  have view := views site.owner actual member hit.1
  rw [hit.1] at member owns
  rw [hit.2] at retained
  obtain ⟨canonicalForm, span⟩ := view.index_span_at unique contains retained form
  refine ⟨hit.1, hit.2, actual, issuer, base, key, member, owns, retained, form, canonicalForm, span, ?_⟩
  rw [diagnostic, retained.2, span]

/-- Actual coverage selects an index row for a supplied canonical source;
this uses its literal member and form rather than a type or decoder guess. -/
theorem Inventory.index_selected {sources : List (Key × TypedSource)} {indices : List IndexSite}
    (inventory : Inventory sources sources indices) {owner : Key} {canonical : TypedSource}
    (member : (owner, canonical) ∈ sources) {node : ExpressionNode} {base key : ExpressionId}
    (contains : SourceSemantics.ContainsExpression canonical node.id node) (form : node.form = .index base key) :
    Selected indices owner node.id :=
  inventory.covered owner canonical member node contains.1 base key form

theorem FactoryAt.no_index_at_read {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : FactoryAt prepared diagnostics) {owner : Key} {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok row)
    (unique : SourceSemantics.NodeOccurrencesUnique row.function.typedBody)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (contains : SourceSemantics.ContainsExpression row.function.typedBody id node)
    (form : node.form = .reference name (.local binder)) :
    diagnostics.program.expressions.indices.find? (fun site => decide (site.owner = owner ∧ site.expression = id)) = none := by
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  exact Inventory.no_index_at_read (CompatiblePlaceMissingPreparationRanges.prepare_index_origins accepted).2
    (factory.source_views record) unique contains form

theorem FactoryAt.index_selected_origin {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : FactoryAt prepared diagnostics) {owner : Key} {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok row)
    (unique : SourceSemantics.NodeOccurrencesUnique row.function.typedBody)
    {node : ExpressionNode} {base key : ExpressionId}
    (contains : SourceSemantics.ContainsExpression row.function.typedBody node.id node)
    (form : node.form = .index base key) :
    ∃ site, diagnostics.program.expressions.indices.find?
        (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = some site ∧
      site.owner = owner ∧ site.expression = node.id ∧
      ∃ actual issuer actualBase actualKey,
        (owner, actual) ∈ (prepared.plan.specializations.map (fun row => (row.key, row.function.typedBody)) ++
          prepared.contexts.map (fun item => (item.caller.key, item.source))) ∧
        actual.owner = owner.declaration ∧ SourceSemantics.ContainsExpression actual node.id issuer ∧
        issuer.form = .index actualBase actualKey ∧ node.form = .index actualBase actualKey ∧
        issuer.span = node.span ∧
        site.diagnostic = ⟨.typeMismatch issuer.type none, .occurrence node.id.occurrence, some node.span⟩ := by
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  have inventory := (CompatiblePlaceMissingPreparationRanges.prepare_index_origins accepted).2
  have member : (owner, row.function.typedBody) ∈ (prepared.plan.specializations.map
      (fun row => (row.key, row.function.typedBody)) ++ prepared.contexts.map (fun item => (item.caller.key, item.source))) := by
    apply List.mem_append_left
    have filtered : row ∈ prepared.plan.specializations.filter (fun actual => decide (actual.key = owner)) := by
      rw [selected_filter record]
      exact List.mem_singleton_self _
    exact List.mem_map.mpr ⟨row, (List.mem_filter.mp filtered).1, by rw [selected_key record]⟩
  obtain ⟨site, found⟩ := Inventory.index_selected inventory member contains form
  exact ⟨site, found, Inventory.selected_origin inventory (factory.source_views record) unique contains found⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticIndexOrigins
