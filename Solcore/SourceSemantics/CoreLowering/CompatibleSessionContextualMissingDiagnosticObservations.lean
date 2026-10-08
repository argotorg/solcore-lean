import Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualMissingDiagnosticObservations
import Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualDiagnosticObservations

/-! The canonical expression row and actual receiving registry retain the
exact Session diagnostic. Factory authority comes from the sealed artifact
in a proof goal, and the original filtered callable append is unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualMissingDiagnosticObservations
open Core Frontend SourceInference CompatiblePayload
open CallableIndexedOwnedPublicFaultReceiverTables
open CallableIndexedOwnedContextualDiagnosticSources
open CompatibleSessionContextualDiagnosticObservations (artifact_factory_receipts)
open CompatiblePublicContextualMissingDiagnosticObservations

abbrev Key := SourceSpecialization.SpecializationKey

/-- The optional actual issuer identity stays with the exact decoded
occurrence and span. Primitive Source failure paths remain independent. -/
def CanonicalMissingObservationAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (owner : Key) (node : ExpressionNode) (rawValue : TypeSystem.Ty) (header : Word)
    (table : SourceCoreFaultSites.Table) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    prepared.base.diagnostics = some issued ∧
    table.diagnostic? ((issued.program.reasonAt owner node.id).add header) = some {
      error := .typeMismatch rawValue none,
      site := .occurrence node.id.occurrence, span := some node.span }

/-- The real rebuilt Session table identifies the canonical missing row
internally; only receiving metadata and its actual Source base view remain. -/
theorem session_index_missing_observation {artifact : SourceCoreIndexedSession.Artifact}
    (session : SourceCoreIndexedSession.Session artifact)
    {rootKey : Key} {table : SourceCoreFaultSites.Table}
    (receiver : session.DiagnosticTableAt rootKey table)
    (registry : SourceCoreRawMetadata.Registry) (registryAt : session.RegistryAt registry)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial _)}
    (present : artifact.program.base.diagnostics = some issued)
    {owner : Key} {function : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization artifact.program.base.plan owner = .ok function)
    (unique : NodeOccurrencesUnique function.function.typedBody)
    {node : ExpressionNode} {base key : ExpressionId}
    (contains : ContainsExpression function.function.typedBody node.id node)
    (form : node.form = .index base key)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (view : CanonicalMappingView function.function.typedBody base rawKey rawValue)
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header) :
    CanonicalMissingObservationAt artifact.program owner node rawValue header table := by
  obtain ⟨factory, allocation⟩ := artifact_factory_receipts artifact issued present
  obtain ⟨actualRegistry, actualAt, extension, selectedRoot, actual,
    _found, _key, rebuilt, tableEq⟩ := receiver.rebuild
  have sameRegistry : actualRegistry = registry := actualAt.symm.trans registryAt
  have actualMetadata : MetadataRep actualRegistry (.mapping rawKey rawValue) header := by
    rw [sameRegistry]
    exact metadata
  rw [present] at rebuilt
  obtain ⟨missing, member, _receipt, providerBase, decoded⟩ :=
    CompatiblePublicContextualMissingDiagnosticObservations.FactoryAt.table_expression_missing_diagnostic
      factory record unique contains form view rebuilt actualMetadata
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  obtain ⟨baseProgram, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  have below : BelowCallable artifact.program ((issued.program.reasonAt owner node.id).add header) := by
    simpa only [providerBase] using allocation.below
      (CompatiblePublicDiagnosticPriority.missing_token_below reserved rebuilt member actualMetadata)
  have append : table = appendCallable artifact.program actual := by
    rw [tableEq]
    unfold appendCallable
    cases artifact.program.base.callableDiagnostics <;> rfl
  refine ⟨issued, present, ?_⟩
  rw [append, appendCallable_diagnostic_of_below below]
  simpa only [providerBase] using decoded

end Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualMissingDiagnosticObservations
