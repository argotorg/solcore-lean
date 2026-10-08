import Solcore.SourceSemantics.CoreLowering.CompatibleContextualDiagnosticIndexOrigins
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicCallableAllocationReceipts

/-! Finite public decoder compositions use the actual contextual source
inventory and receiving table. Primitive failure paths and reached heap
associations remain independent receipts. Issuer raw types are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualDiagnosticObservations
open Core Frontend SourceInference
open CallableIndexedOwnedPublicFaultReceiverTables
open CallableIndexedOwnedContextualDiagnosticSources

abbrev Key := SourceSpecialization.SpecializationKey

/-- A genuine canonical local occurrence uses its actual globally issued read
token. The sealed factory supplies contextual no-index priority and the actual
receiving table supplies the same binder, occurrence and span. -/
theorem receiver_local_read_diagnostic (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {owner : Key} {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row)
    (unique : SourceSemantics.NodeOccurrencesUnique row.function.typedBody)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (contains : SourceSemantics.ContainsExpression row.function.typedBody id node)
    (form : node.form = .reference name (.local binder))
    {own : SourceCoreProgramFaultSites.Function}
    (ownFound : issued.program.base.find? owner = some own) :
    ∃ read : SourceCoreFaultSites.ReadSite,
      read.expression = id ∧ read.binder = binder ∧ read.span = node.span ∧
      issued.program.reasonAt owner id = read.reason ∧
      read ∈ issued.program.rootTable.reads ∧
      completion.result.diagnostics.diagnostic? read.reason = some {
        error := .uninitializedLocal binder
        site := .occurrence id.occurrence
        span := some node.span } := by
  have factory := CallableIndexedOwnedContextualDiagnosticSources.of_compiled compiled present
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
  have decoded := CompatiblePublicCallableAllocationReceipts.receiver_read_diagnostic
    compiled receiver present member
  exact ⟨read, expressionEq, binderEq, spanEq, token, member,
    by simpa only [expressionEq, binderEq, spanEq] using decoded⟩

/-- The selected index retains its literal issuer independently of missing
mapping metadata and decoding. The actual provider base equals the invoked
reason; no decoded span or issuer raw type equality is inferred. -/
theorem receiver_index_missing_diagnostic (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {owner : Key} {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row)
    (unique : SourceSemantics.NodeOccurrencesUnique row.function.typedBody)
    {node : ExpressionNode} {base key : ExpressionId}
    (contains : SourceSemantics.ContainsExpression row.function.typedBody node.id node)
    (form : node.form = .index base key)
    {missing : SourceCoreCompatibleDataPlaceFaultSites.MissingSite}
    (member : missing ∈ issued.missing)
    (providerBase : missing.base = issued.program.reasonAt owner node.id)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : CompatiblePayload.MetadataRep completion.result.context.registry
      (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType missing.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType missing.valueType) :
    ∃ site : SourceCoreDataFaultSites.IndexSite,
      issued.program.expressions.indices.find?
        (fun candidate => decide (candidate.owner = owner ∧ candidate.expression = node.id)) = some site ∧
      site.owner = owner ∧ site.expression = node.id ∧
      issued.program.reasonAt owner node.id = site.reason ∧
      (∃ actual issuer actualBase actualKey,
        (owner, actual) ∈ (compiled.indexed.base.plan.specializations.map
          (fun row => (row.key, row.function.typedBody)) ++
          compiled.indexed.base.contexts.map (fun item => (item.caller.key, item.source))) ∧
        actual.owner = owner.declaration ∧ SourceSemantics.ContainsExpression actual node.id issuer ∧
        issuer.form = .index actualBase actualKey ∧ node.form = .index actualBase actualKey ∧
        issuer.span = node.span ∧
        site.diagnostic = ⟨.typeMismatch issuer.type none, .occurrence node.id.occurrence, some node.span⟩) ∧
      ∃ diagnostic,
        completion.result.diagnostics.diagnostic? (site.reason.add header) = some diagnostic ∧
        diagnostic.error = .typeMismatch rawValue none := by
  have factory := CallableIndexedOwnedContextualDiagnosticSources.of_compiled compiled present
  obtain ⟨site, found, ownerEq, expressionEq, origin⟩ :=
    CompatibleContextualDiagnosticIndexOrigins.FactoryAt.index_selected_origin
      factory record unique contains form
  have reason : issued.program.reasonAt owner node.id = site.reason := by
    unfold SourceCoreDataPlaceFaultSites.Program.reasonAt SourceCoreDataFaultSites.Program.reasonAt
    rw [found]
  obtain ⟨diagnostic, decoded, error⟩ :=
    CompatiblePublicCallableAllocationReceipts.receiver_missing_diagnostic
      compiled receiver present member metadata keyView valueView
  have baseEq : missing.base = site.reason := providerBase.trans reason
  exact ⟨site, found, ownerEq, expressionEq, reason, origin, diagnostic,
    by simpa only [baseEq] using decoded, error⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualDiagnosticObservations
