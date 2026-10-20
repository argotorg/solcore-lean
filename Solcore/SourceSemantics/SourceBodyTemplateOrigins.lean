import Solcore.SourceSemantics.SourceCachedTemplateScope
import Solcore.SourceSemantics.SourceCompiledBodySelection

/-! The same finalizer and preparation receipts identify local template owners
inside ordinary functions and implementation methods. Catalog separation is
used for each emitted callee; it does not constrain the caller's body origin. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceBodyTemplateOrigins
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceSpecializationWorklist SourceCompiledLocalFinalization
open CoreLowering SourceCachedTemplateReceipts

theorem selected_unique {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : BodySelection compiled row fuel) : NodeOccurrencesUnique row.function.typedBody := by
  have unique := receipt.body.resources.graph_closed.wellFormed.nodeOccurrencesUnique
  rw [receipt.source]
  change (nodeOccurrenceIds (SourceSpecialization.applyTypedSource row.parameterSubstitution receipt.body.finalized.typedSource)).Nodup
  have occurrences : nodeOccurrenceIds (SourceSpecialization.applyTypedSource row.parameterSubstitution receipt.body.finalized.typedSource) =
      nodeOccurrenceIds receipt.body.finalized.typedSource := by
    simp only [nodeOccurrenceIds, SourceSpecialization.applyTypedSource, List.map_map]
    congr 1
    funext node
    cases node <;> rfl
  rw [occurrences]
  exact unique

theorem selected_ownership {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) :
    LocalIdentityOwnership row.function.typedBody ∧ LocalSchemeTemplateOwnership row.function.typedBody := by
  rw [selected.source]
  exact ⟨StructuralSubstitution.LocalIdentityOwnership.applyParameters _
      selected.body.resources.local_identity_ownership,
    StructuralSubstitution.LocalSchemeTemplateOwnership.applyParameters _
      selected.body.resources.ledger.templateOwnership⟩

theorem cached_open_call_owner {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : BodySelection compiled named.specialized fuel)
    {node : ExpressionNode} (present : .expression node ∈ named.specialized.function.typedBody.nodes)
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (cataloged : instantiation.declaration ∈ compiled.program.signatures.functions.map (·.id))
    (opened : SourcePreparedOpenCallEdges.InstantiationClosed instantiation = false) :
    Nonempty (SourceCompiledTemplateCallOwner.PreparedContextual compiled named.specialized node instantiation) := by
  obtain ⟨programEq, planEq, _⟩ := compiled.artifact_fields artifact
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached
  rw [programEq, planEq] at prepared
  obtain ⟨growth, covered⟩ := SourcePreparedOpenCallEdges.of_default_preparation prepared
  have member := RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  obtain ⟨edge⟩ := covered named.specialized member node present callee arguments instantiation form opened
  have origin := SourcePreparedFinalCallEdgeOrigins.of_default_preparation prepared
    edge.edge (edge.retained edge.present)
  have source := final_source_origin (SignatureCatalogWellFormed.ofCheckProgram checked) growth
    (cached_exact cached position) origin edge.callerEq (edge.declarationEq.symm ▸ cataloged)
  obtain ⟨contextual⟩ := SourcePreparedOpenCallOwner.contextual_of_open
    (selected_unique selected) present form opened source edge.occurrenceEq
  obtain ⟨bodyNodes, bodyAccepted, nodeInBody, templates⟩ :=
    contextual.body (selected_unique selected) present
  exact ⟨⟨cached.indexed.base.plan, prepared, edge, contextual,
    bodyNodes, bodyAccepted, nodeInBody, templates⟩⟩

end Solcore.SourceSemantics.SourceBodyTemplateOrigins
