import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticProducers

/-! The original prepared Site retains compiler provenance, Source declarations,
and authentic read and index issuers without a uniform-error body package. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering
namespace CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaProvenance
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative} {support : Support code}

theorem PreparedAt.policy_recipe (receipt : PreparedAt code support) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained support.caller.named code := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact compilerPolicy

theorem PreparedAt.issued_recipe (receipt : PreparedAt code support) :
    CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained support.caller.named code := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact issuedRecipe

theorem PreparedAt.body_view (receipt : PreparedAt code support) :
    BodyView code := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact bodyView

theorem PreparedAt.body_reasons (receipt : PreparedAt code support) :
    BodyReasons code support.caller.named := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact bodyReasons

theorem PreparedAt.scope_declarations (receipt : PreparedAt code support) :
    CompatibleExpressionReads.ScopeDeclarations function.source scope function.context := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact declarations

end CallableIndexedOwnedPreparedOrdinaryLambdaSupport

namespace CallableIndexedOwnedContextualLambdaReadDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaProvenance
open CallableIndexedOwnedPublicFaultReceiverTables
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}
theorem prepared_uninitialized
    (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
    (reasons : BodyReasons code support.caller.named)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {fuel : Nat} {context : SourceSemantics.Context} {readScope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression id))
    (receipt : CompatibleExpressionReads.LoweredRead fuel
      (.initial compiled.compatible.checked) function.source context code.reasonAt readScope id lowered)
    (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (code.reasonAt id) := by
  obtain ⟨certificate, _type, _binding⟩ := receipt
  obtain ⟨issued, present, token⟩ := reasons id reached
  obtain ⟨actual, namedCode, actualPresent, _cached, compiledCode⟩ :=
    NamedCalls.compiled_at compiled.indexed support.caller.selected
  have sameIssuer : actual = issued := Option.some.inj (actualPresent.symm.trans present)
  subst actual
  obtain ⟨compilation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed compiledCode
  have ownFound : issued.program.base.find? support.caller.named.signature.key = some compilation.own := by
    have selected := compilation.diagnostic
    have sameBase : (match compiled.indexed.base.callableContext with
        | none => issued.program
        | some native => { issued.program with rootTable := native.diagnostics.rootTable }).base =
        issued.program.base := by cases compiled.indexed.base.callableContext <;> rfl
    exact (congrArg (fun base => base.find? support.caller.named.signature.key) sameBase).symm.trans selected
  have original : function.source = support.caller.named.specialized.function.typedBody := support.source
  have unique : NodeOccurrencesUnique support.caller.named.specialized.function.typedBody := original ▸ support.unique
  have contains : ContainsExpression support.caller.named.specialized.function.typedBody id certificate.node :=
    original ▸ lookupExpression?_sound certificate.metadata.found
  obtain ⟨read, _expression, _binder, _span, readToken, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver present
      (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)
      unique contains certificate.form ownFound
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  apply CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
    (by simpa only [← readToken, ← token] using decoded)
  exact .readUninitialized location certificate.binder

end CallableIndexedOwnedContextualLambdaReadDiagnostics

namespace CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaProvenance
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {source : TypedSource} {id base : ExpressionId} {node baseNode : ExpressionNode}
  {layout : Core.OrderedMapping.Layout}
  {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
  {first second : SourceCoreBasic.LoweredExpr}
theorem of_prepared_ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
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
theorem prepared_ordinary_ready {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
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
  intro _ _ _ _ _ _ _ _ _ _ _ indexed _ _ _ _ path
  have actualReached := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.indexes_reached
    path (sameSource ▸ reached)
  exact of_prepared_ordinary support reasons sameSource (sameSource ▸ actualReached) indexed

end CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
end Solcore.SourceSemantics.CoreLowering
