import Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualDiagnosticObservations
import Solcore.Frontend.SourceCoreIndexedSession

/-! The Session table receipt retains its actual raw registry and filtered
callable append. Static factory authority follows from the artifact's genuine
sealed compiler in a proof goal. Primitive paths and heap associations remain
independent receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualDiagnosticObservations
open Core Frontend SourceInference
open CallableIndexedOwnedPublicFaultReceiverTables
open CallableIndexedOwnedContextualDiagnosticSources

abbrev Key := SourceSpecialization.SpecializationKey

/-- Static receipts for the actual prepared program. No recipe or code getter
is added to the public session interface. -/
def FactoryReceiptsFor {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) : Prop :=
  ∀ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    prepared.base.diagnostics = some issued → FactoryAt prepared.base issued ∧
      CompatiblePublicCallableAllocationReceipts.AllocationAt prepared.base issued

/-- Existing structure elimination is used only in this proof goal. Its actual
retained sealed compiler supplies the genuine Source and allocation factories. -/
theorem artifact_factory_receipts (artifact : SourceCoreIndexedSession.Artifact) :
    FactoryReceiptsFor artifact.program := by
  unfold FactoryReceiptsFor
  cases artifact
  rename_i authority recipe
  dsimp only [SourceCoreIndexedSession.Artifact.program, SourceCoreIndexedSession.Recipe.program]
  intro issued present
  exact ⟨CallableIndexedOwnedContextualDiagnosticSources.of_compiled recipe.compiled present,
    CompatiblePublicCallableAllocationReceipts.of_compiled recipe.compiled present⟩

/-- The actual optional issuer and selected own row are static inputs. -/
def ReadInputs {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) (owner : Key) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    ∃ own : SourceCoreProgramFaultSites.Function,
      prepared.base.diagnostics = some issued ∧ issued.program.base.find? owner = some own

/-- The receiving registry and actual metadata are kept with the missing row.
Neither its source owner nor its requested span follows from a raw type. -/
def MissingInputs {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (owner : Key) (id : ExpressionId) (registry : SourceCoreRawMetadata.Registry)
    (rawKey rawValue : TypeSystem.Ty) (header : Word) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    ∃ missing : SourceCoreCompatibleDataPlaceFaultSites.MissingSite,
      prepared.base.diagnostics = some issued ∧ missing ∈ issued.missing ∧
      missing.base = issued.program.reasonAt owner id ∧
      CompatiblePayload.MetadataRep registry (.mapping rawKey rawValue) header ∧
      SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType missing.keyType ∧
      SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType missing.valueType

/-- The exact globally issued read and actual table observation stay together. -/
def ReadObservationAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (owner : Key) (id : ExpressionId) (binder : Resolved.LocalId) (span : Syntax.SourceSpan)
    (table : SourceCoreFaultSites.Table) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    ∃ read : SourceCoreFaultSites.ReadSite,
      prepared.base.diagnostics = some issued ∧ read.expression = id ∧
      read.binder = binder ∧ read.span = span ∧
      issued.program.reasonAt owner id = read.reason ∧ read ∈ issued.program.rootTable.reads ∧
      table.diagnostic? read.reason = some {
        error := .uninitializedLocal binder, site := .occurrence id.occurrence, span := some span }

/-- The first actual index issuer is retained beside the missing row and decoded
raw error. The decoded diagnostic's span is deliberately not identified here. -/
def IndexObservationAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (owner : Key) (node : ExpressionNode) (rawValue : TypeSystem.Ty) (header : Word)
    (table : SourceCoreFaultSites.Table) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    ∃ missing : SourceCoreCompatibleDataPlaceFaultSites.MissingSite,
    ∃ site : SourceCoreDataFaultSites.IndexSite,
      prepared.base.diagnostics = some issued ∧ missing ∈ issued.missing ∧
      missing.base = site.reason ∧
      issued.program.expressions.indices.find?
        (fun candidate => decide (candidate.owner = owner ∧ candidate.expression = node.id)) = some site ∧
      site.owner = owner ∧ site.expression = node.id ∧
      issued.program.reasonAt owner node.id = site.reason ∧
      (∃ actual issuer actualBase actualKey,
        (owner, actual) ∈ (prepared.base.plan.specializations.map
          (fun row => (row.key, row.function.typedBody)) ++
          prepared.base.contexts.map (fun item => (item.caller.key, item.source))) ∧
        actual.owner = owner.declaration ∧ ContainsExpression actual node.id issuer ∧
        issuer.form = .index actualBase actualKey ∧ node.form = .index actualBase actualKey ∧
        issuer.span = node.span ∧
        site.diagnostic = ⟨.typeMismatch issuer.type none, .occurrence node.id.occurrence, some node.span⟩) ∧
      ∃ diagnostic, table.diagnostic? (site.reason.add header) = some diagnostic ∧
        diagnostic.error = .typeMismatch rawValue none

/-- The genuine ordinary-root lookup table decodes a real canonical local read.
The nested primitive owner remains independent of that selected root key. -/
theorem session_read_observation {artifact : SourceCoreIndexedSession.Artifact}
    (session : SourceCoreIndexedSession.Session artifact) {rootKey : Key} {table : SourceCoreFaultSites.Table}
    (receiver : session.DiagnosticTableAt rootKey table) {owner : Key}
    (inputs : ReadInputs artifact.program owner) {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization artifact.program.base.plan owner = .ok row)
    (unique : NodeOccurrencesUnique row.function.typedBody)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (contains : ContainsExpression row.function.typedBody id node)
    (form : node.form = .reference name (.local binder)) :
    ∃ registry, session.RegistryAt registry ∧
      ReadObservationAt artifact.program owner id binder node.span table := by
  obtain ⟨issued, own, present, ownFound⟩ := inputs
  obtain ⟨factory, allocation⟩ := artifact_factory_receipts artifact issued present
  have noIndex := CompatibleContextualDiagnosticIndexOrigins.FactoryAt.no_index_at_read
    factory record unique contains form
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  obtain ⟨base, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  have baseAccepted := CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base accepted
  obtain ⟨read, _ownRead, expression, binderEq, spanEq, ownReason, rootMember,
    _positive, _ordinary, _noAdditional, _byReason, _baseDecoded⟩ :=
    SourceCoreProgramFaultSites.prepare_local_read baseAccepted record ownFound contains.1 form
  have expressionEq : read.expression = id := expression.trans contains.2
  have sameExpressionBase : issued.program.expressions.base = issued.program.base :=
    reserved.sameExpressionBase.trans reserved.sameBase.symm
  have token : issued.program.reasonAt owner id = read.reason := by
    unfold SourceCoreDataPlaceFaultSites.Program.reasonAt SourceCoreDataFaultSites.Program.reasonAt
    rw [noIndex, sameExpressionBase, ownFound]
    simpa only [contains.2] using ownReason
  have readsSame : issued.program.rootTable.reads = issued.program.base.rootTable.reads := by
    rw [reserved.sameRoot, reserved.sameBase]
  have member : read ∈ issued.program.rootTable.reads := by rw [readsSame]; exact rootMember
  have baseMember : read ∈ base.rootTable.reads := by simpa only [reserved.sameRoot] using member
  obtain ⟨registry, registryAt, extension, selectedRoot, actual, _found, _key, rebuilt, tableEq⟩ := receiver.rebuild
  rw [present] at rebuilt
  have append : table = appendCallable artifact.program actual := by
    rw [tableEq]
    unfold appendCallable
    cases artifact.program.base.callableDiagnostics <;> rfl
  have decoded : table.diagnostic? read.reason = some {
      error := .uninitializedLocal binder, site := .occurrence id.occurrence, span := some node.span } := by
    rw [append, appendCallable_diagnostic_of_below (allocation.below (reserved.readsBelow read baseMember))]
    simpa only [expressionEq, binderEq, spanEq] using
      CompatiblePublicDiagnosticPriority.read_diagnostic reserved rebuilt baseMember
  exact ⟨registry, registryAt, issued, read, present, expressionEq, binderEq, spanEq, token, member, decoded⟩

/-- The actual Session registry fixes receiving metadata. Its rebuilt table and
filtered callable append preserve the exact missing-default error. -/
theorem session_index_missing_observation {artifact : SourceCoreIndexedSession.Artifact}
    (session : SourceCoreIndexedSession.Session artifact) {rootKey : Key} {table : SourceCoreFaultSites.Table}
    (receiver : session.DiagnosticTableAt rootKey table)
    (registry : SourceCoreRawMetadata.Registry) (registryAt : session.RegistryAt registry)
    {owner : Key} {row : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {base key : ExpressionId} {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (inputs : MissingInputs artifact.program owner node.id registry rawKey rawValue header)
    (record : SourceCompilationPlan.exactSpecialization artifact.program.base.plan owner = .ok row)
    (unique : NodeOccurrencesUnique row.function.typedBody)
    (contains : ContainsExpression row.function.typedBody node.id node)
    (form : node.form = .index base key) :
    IndexObservationAt artifact.program owner node rawValue header table := by
  obtain ⟨issued, missing, present, member, providerBase, metadata, keyView, valueView⟩ := inputs
  obtain ⟨factory, allocation⟩ := artifact_factory_receipts artifact issued present
  obtain ⟨site, found, ownerEq, expressionEq, origin⟩ :=
    CompatibleContextualDiagnosticIndexOrigins.FactoryAt.index_selected_origin
      factory record unique contains form
  have reason : issued.program.reasonAt owner node.id = site.reason := by
    unfold SourceCoreDataPlaceFaultSites.Program.reasonAt SourceCoreDataFaultSites.Program.reasonAt
    rw [found]
  have baseEq : missing.base = site.reason := providerBase.trans reason
  obtain ⟨locals0, root, remaining, _roots, _contexts, accepted⟩ := factory.actual
  obtain ⟨baseProgram, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  obtain ⟨actualRegistry, actualAt, extension, selectedRoot, actual, _found, _key, rebuilt, tableEq⟩ := receiver.rebuild
  have sameRegistry : actualRegistry = registry := actualAt.symm.trans registryAt
  have actualMetadata : CompatiblePayload.MetadataRep actualRegistry (.mapping rawKey rawValue) header := by
    rw [sameRegistry]
    exact metadata
  rw [present] at rebuilt
  have append : table = appendCallable artifact.program actual := by
    rw [tableEq]
    unfold appendCallable
    cases artifact.program.base.callableDiagnostics <;> rfl
  obtain ⟨diagnostic, decoded, error⟩ :=
    CompatiblePlaceMissingPreparationRanges.table_diagnostic accepted rebuilt member actualMetadata keyView valueView
  have below : BelowCallable artifact.program (site.reason.add header) := by
    simpa only [baseEq] using
      allocation.below (CompatiblePublicDiagnosticPriority.missing_token_below reserved rebuilt member actualMetadata)
  have decodedAt : table.diagnostic? (site.reason.add header) = some diagnostic := by
    rw [append, appendCallable_diagnostic_of_below below]
    simpa only [baseEq] using decoded
  exact ⟨issued, missing, site, present, member, baseEq, found, ownerEq, expressionEq,
    reason, origin, diagnostic, decodedAt, error⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualDiagnosticObservations
