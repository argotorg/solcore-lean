import Solcore.SourceSemantics.CoreLowering.ReachedExpressionFaultOrigins
import Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualMissingDiagnosticObservations

/-! A reached unavailable mapping supplies the receiving metadata and canonical
mapping view from its own fields. Its exact specialization and issued reason
remain static provenance receipts; observations do not infer a whole public
execution or identify a restored store with the primitive store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedIndexMissingDiagnosticObservations
open Core Frontend SourceInference CompatiblePayload GeneralHeap
open ReachedExpressionFaultOrigins
open CompatiblePublicContextualMissingDiagnosticObservations
open CallableIndexedOwnedPublicFaultReceiverTables

/-- Literal source and reason associations at one actual specialized issuer. -/
def IssuerAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked))
    (owner : SourceSpecialization.SpecializationKey) (leaf : IndexLeaf) : Prop :=
  ∃ function, SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok function ∧
    leaf.source = function.function.typedBody ∧
    leaf.reason = issued.program.reasonAt owner leaf.id

/-- The real base lookup and both raw runtime views are already in the leaf. -/
theorem IndexLeaf.mapping_view (leaf : IndexLeaf) (unique : NodeOccurrencesUnique leaf.source) :
    CanonicalMappingView leaf.source leaf.base leaf.rawKey leaf.rawValue := by
  refine ⟨leaf.baseNode, lookupExpression?_complete unique leaf.baseContains, ?_⟩
  rw [leaf.sourceType, SourceCoreRawMetadata.runtimeType, leaf.keyView, leaf.valueView]

/-- Transport the original mapping metadata only along the actual registry. -/
theorem IndexLeaf.receiving_metadata (leaf : IndexLeaf)
    {registry : SourceCoreRawMetadata.Registry}
    (extension : SourceCoreRawMetadata.Extends leaf.registry registry) :
    MetadataRep registry (.mapping leaf.rawKey leaf.rawValue) leaf.tag :=
  leaf.fields.metadata.extend extension

/-- The actual first receiving row decodes this primitive's literal token. -/
theorem IndexLeaf.table_diagnostic (leaf : IndexLeaf)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (factory : CallableIndexedOwnedContextualDiagnosticSources.FactoryAt prepared issued)
    {owner : SourceSpecialization.SpecializationKey}
    (issuer : IssuerAt prepared issued owner leaf)
    (unique : NodeOccurrencesUnique leaf.source)
    {registry : SourceCoreRawMetadata.Registry}
    (extension : SourceCoreRawMetadata.Extends leaf.registry registry)
    {issuedExtension : SourceCoreRawMetadata.Extends issued.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry registry issuedExtension = .ok table) :
    table.diagnostic? (leaf.reason.add leaf.tag) = some {
      error := .typeMismatch leaf.rawValue none,
      site := .occurrence leaf.id.occurrence, span := some leaf.node.span } := by
  obtain ⟨function, record, sourceEq, reasonEq⟩ := issuer
  have canonicalUnique : NodeOccurrencesUnique function.function.typedBody := sourceEq ▸ unique
  have contains : ContainsExpression function.function.typedBody leaf.node.id leaf.node := by
    rw [← sourceEq, leaf.contains.2]
    exact leaf.contains
  have view := sourceEq ▸ IndexLeaf.mapping_view leaf unique
  obtain ⟨missing, _member, _receipt, base, decoded⟩ :=
    FactoryAt.table_expression_missing_diagnostic factory record canonicalUnique contains leaf.form view rebuilt
      (IndexLeaf.receiving_metadata leaf extension)
  simpa only [base, leaf.contains.2, ← reasonEq] using decoded

/-- Actual public rebuilding and callable append retain the same origin token. -/
theorem IndexLeaf.public_diagnostic (leaf : IndexLeaf)
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {owner : SourceSpecialization.SpecializationKey}
    (issuer : IssuerAt compiled.indexed.base issued owner leaf)
    (unique : NodeOccurrencesUnique leaf.source)
    (extension : SourceCoreRawMetadata.Extends leaf.registry completion.result.context.registry) :
    completion.result.diagnostics.diagnostic? (leaf.reason.add leaf.tag) = some {
      error := .typeMismatch leaf.rawValue none,
      site := .occurrence leaf.id.occurrence, span := some leaf.node.span } := by
  obtain ⟨function, record, sourceEq, reasonEq⟩ := issuer
  have canonicalUnique : NodeOccurrencesUnique function.function.typedBody := sourceEq ▸ unique
  have contains : ContainsExpression function.function.typedBody leaf.node.id leaf.node := by
    rw [← sourceEq, leaf.contains.2]
    exact leaf.contains
  have view := sourceEq ▸ IndexLeaf.mapping_view leaf unique
  have decoded := receiver_index_missing_diagnostic compiled receiver present record canonicalUnique contains
    leaf.form view (IndexLeaf.receiving_metadata leaf extension)
  simpa only [leaf.contains.2, ← reasonEq] using decoded

/-- Session metadata comes from the same reached leaf and real extension. -/
theorem IndexLeaf.session_diagnostic (leaf : IndexLeaf)
    {artifact : SourceCoreIndexedSession.Artifact}
    (session : SourceCoreIndexedSession.Session artifact)
    {rootKey : SourceSpecialization.SpecializationKey} {table : SourceCoreFaultSites.Table}
    (receiver : session.DiagnosticTableAt rootKey table)
    {registry : SourceCoreRawMetadata.Registry} (registryAt : session.RegistryAt registry)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial _)}
    (present : artifact.program.base.diagnostics = some issued)
    {owner : SourceSpecialization.SpecializationKey}
    (issuer : IssuerAt artifact.program.base issued owner leaf)
    (unique : NodeOccurrencesUnique leaf.source)
    (extension : SourceCoreRawMetadata.Extends leaf.registry registry) :
    table.diagnostic? (leaf.reason.add leaf.tag) = some {
      error := .typeMismatch leaf.rawValue none,
      site := .occurrence leaf.id.occurrence, span := some leaf.node.span } := by
  obtain ⟨function, record, sourceEq, reasonEq⟩ := issuer
  have canonicalUnique : NodeOccurrencesUnique function.function.typedBody := sourceEq ▸ unique
  have contains : ContainsExpression function.function.typedBody leaf.node.id leaf.node := by
    rw [← sourceEq, leaf.contains.2]
    exact leaf.contains
  have view := sourceEq ▸ IndexLeaf.mapping_view leaf unique
  obtain ⟨actual, actualPresent, decoded⟩ :=
    CompatibleSessionContextualMissingDiagnosticObservations.session_index_missing_observation session receiver
      registry registryAt present record canonicalUnique contains leaf.form view (IndexLeaf.receiving_metadata leaf extension)
  have same := Option.some.inj (actualPresent.symm.trans present)
  cases same
  simpa only [leaf.contains.2, ← reasonEq] using decoded

end Solcore.SourceSemantics.CoreLowering.ReachedIndexMissingDiagnosticObservations
