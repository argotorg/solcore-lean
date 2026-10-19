import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax

/-! Actual named compilation and ordinary lambda provenance retain the exact
index issuer. Receivers are not selected here: each invocation later supplies
its current registry to the static authority. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaProvenance

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {source : TypedSource} {id base : ExpressionId} {node baseNode : ExpressionNode}
  {layout : Core.OrderedMapping.Layout}
  {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
  {first second : SourceCoreBasic.LoweredExpr}

/-- The authentic prepared header gives the issuer and original Source row. -/
theorem of_prepared {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (sameSource : source = header.function.source)
    (indexed : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
      source id base node baseNode layout comparison first second) :
    Nonempty (Port compiled indexed (header.reasonAt id)) := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  have original : header.function.source = prepared.named.specialized.function.typedBody := by
    rw [aligned.function]; rfl
  refine ⟨{
    owner := prepared.named.signature.key
    row := prepared.named.specialized
    record := CallableIndexedActualNamedSourceReceipts.cached_record compiled prepared.selected prepared.compilation.hook
    sourceEq := sameSource.trans original
    unique := sameSource ▸ header.unique
    issuer := issued
    present := present
    token := ?_ }⟩
  rw [aligned.reasonAt, lowered]
  cases compiled.indexed.base.callableContext <;> rfl

/-- Every actual index in a named root has the same genuine source issuer. -/
theorem named_ready {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (sameSource : source = header.function.source)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
      source context header.reasonAt scope rootId lowered) : IndexReady root := by
  intro _ _ _ _ _ _ _ _ _ _ _ indexed _ _ _ _
  exact of_prepared prepared diagnostic aligned sameSource indexed

/-- A reached ordinary lambda occurrence retains its original named issuer. -/
theorem of_ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
    (reasons : BodyReasons code support.caller.named)
    (sameSource : source = function.source)
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression id))
    (indexed : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
      source id base node baseNode layout comparison first second) :
    Nonempty (Port compiled indexed (code.reasonAt id)) := by
  obtain ⟨issued, present, token⟩ := reasons id reached
  exact ⟨{
    owner := support.caller.named.signature.key
    row := support.caller.named.specialized
    record := CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller
    sourceEq := sameSource.trans support.source
    unique := sameSource ▸ support.unique
    issuer := issued
    present := present
    token := token }⟩

/-- Actual certificate paths restrict the retained body issuer to used indices. -/
theorem ordinary_ready {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
    (reasons : BodyReasons code support.caller.named)
    (sameSource : source = function.source)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression rootId))
    (root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
      source context code.reasonAt rootScope rootId lowered) : IndexReady root := by
  intro _ _ _ _ _ _ _ _ _ _ _ indexed _ _ _ path
  have actualReached := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.indexes_reached
    path (sameSource ▸ reached)
  exact of_ordinary support reasons sameSource (sameSource ▸ actualReached) indexed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
