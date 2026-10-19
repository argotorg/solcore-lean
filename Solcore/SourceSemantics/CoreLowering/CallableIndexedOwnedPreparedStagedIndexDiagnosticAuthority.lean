import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualMissingDiagnosticObservations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedReadDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexFaultPolicies

/-! Exact index diagnostic ownership is static. The receiving table and its
raw metadata are supplied only when the reached lookup requests its missing
mapping default; old receiver tables need no rows for future metadata. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedOwnedPublicFaultReceiverTables

structure Port (compiled : SourceCoreUnifiedCompilation.Compiled)
    {source : TypedSource} {id base : ExpressionId} {node baseNode : ExpressionNode}
    {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (header : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
      source id base node baseNode layout comparison first second) (reason : Word) where
  owner : SourceSpecialization.SpecializationKey
  row : SourceSpecialization.SpecializedFunction
  record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row
  sourceEq : source = row.function.typedBody
  unique : NodeOccurrencesUnique source
  issuer : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)
  present : compiled.indexed.base.diagnostics = some issuer
  token : reason = issuer.program.reasonAt owner id

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {source : TypedSource} {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode}
  {layout : Core.OrderedMapping.Layout}
  {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
  {first second : SourceCoreBasic.LoweredExpr}
  {header : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
    source id base node baseNode layout comparison first second} {reason : Word}

/-- Static ownership decodes against the actual current registry. -/
theorem Port.missing (port : Port compiled header reason)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    (functions : FunctionModel compiled.compatible.checked.catalog ambient)
    (_keyFound : source.lookupExpression? key = some keyNode)
    (form : node.form = .index base key)
    (mapping : LocationMap) (world : StoreTyping)
    (baseSource keySource : Dynamic.Value) (baseValue : Value) :
    CompatibleExpressionIndices.MissingPolicy (keyNode := keyNode)
      (registry := completion.result.context.registry) header functions mapping world
      baseSource keySource baseValue reason
      (fun error token => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        completion.result.diagnostics (.semantic error) token) := by
  intro rawKey rawValue sources tag entries fallback witness
  have contains : ContainsExpression port.row.function.typedBody node.id node := by
    rw [← port.sourceEq, witness.contains.2]
    exact witness.contains
  have view : CompatiblePublicContextualMissingDiagnosticObservations.CanonicalMappingView
      port.row.function.typedBody base rawKey rawValue := by
    rw [← port.sourceEq]
    refine ⟨baseNode, lookupExpression?_complete port.unique witness.baseContains, ?_⟩
    rw [witness.sourceType, SourceCoreRawMetadata.runtimeType, witness.keyView, witness.valueView]
  have decoded := CompatiblePublicContextualMissingDiagnosticObservations.receiver_index_missing_diagnostic
    compiled receiver port.present port.record (port.sourceEq ▸ port.unique) contains form view witness.fields.metadata
  apply CallableIndexedOwnedPublicDecodedStagedCallFaults.of_semantic
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  apply CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded (diagnostic := {
    error := .typeMismatch rawValue none
    site := .occurrence id.occurrence
    span := some node.span })
  · simpa only [← witness.contains.2, port.token] using decoded
  · exact .missing rawValue

/-- The finite certificate selects the actual diagnostic authority. -/
def IndexReady {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {rootId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
      source context reasonAt scope rootId lowered) : Prop :=
  ∀ {indexScope indexId base key node baseNode keyNode layout comparison first second}
    (indexed : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
      source indexId base node baseNode layout comparison first second)
    (keyFound : source.lookupExpression? key = some keyNode)
    (form : node.form = .index base key)
    (sourceType : baseNode.type = .mapping keyNode.type node.type),
    Indexes (indexScope := indexScope) indexed keyFound form sourceType root →
    Nonempty (Port compiled indexed (reasonAt indexId))

/-- A legacy tree needs no new diagnostic evidence. -/
theorem IndexReady.of_no_indexes {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {rootId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
      source context reasonAt scope rootId lowered} (none : NoIndexes root) : IndexReady root := by
  intro _ _ _ _ _ _ _ _ _ _ _ indexed found form sourceType path
  exact False.elim (none indexed found form sourceType path)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
