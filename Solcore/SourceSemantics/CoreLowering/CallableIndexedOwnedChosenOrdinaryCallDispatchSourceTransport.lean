import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchReceipts

/-! Dispatch provenance across a genuine equality of the caller's Source.
The receipt keeps the original compiler and Prepared endpoints, including the
chosen lambda origin and selected row. Its producer transports the equality
and uses the existing dispatch producer once under the same root policy. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}
  {actualSource : TypedSource}
  {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {call callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt root.selected.policy root.selected.lowerBody fuel
    (context compiled.indexed caller.named) actualSource scope call callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)

/-- Static dispatch fields at the original Source-indexed parent endpoints.
The actual Source equality and contextual lambda-origin alternatives remain
available; association with an executed callee is a separate runtime fact. -/
structure Receipt where
  source_eq : actualSource = source caller.named
  chosen : ChosenAt root expressionSyntax headers keys registry faults i history
  sidecar : SourceCoreStageContracts.Sidecar
  sidecarPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
    (context compiled.indexed caller.named).owner = .ok sidecar
  sidecarCaller : sidecar.caller = caller.named.specialized
  sidecarSource : sidecar.source = actualSource
  sidecarPlan : sidecar.plan = compiled.indexed.base.plan
  lambdaSite : AuthenticatedCallableLedger.LambdaSite compiled.indexed.base.plan
    compiled.indexed.ancestry.graph.inputs.callable.table i.code.compilation.owner i.code.id i.code.active i.code.descriptor.id
  lambdaOrigin : CallableLedger.LambdaOrigin compiled.indexed.base.plan i.code.compilation.owner
    i.code.id i.code.active i.function lambdaSite.contract
  origin : CallableLedger.OriginRep sidecar.plan prepared.site.table (.closure i.function)
    (value i.code i.captured.embedding history.native i.capturedActual)
  rows : CallableLedger.Rows sidecar prepared.site prepared.site.call ids
  dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site call ids (.closure i.function)
    (value i.code i.captured.embedding history.native i.capturedActual)
  selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site
    callee ids metadata compiler.original dispatch.row

/-- Transport the genuine Source equality before invoking the original
producer. The output retains this compiler, Prepared site, chosen closure and
root; it supplies no execution, guard verdict or called-body law. -/
theorem at_chosen_parent (sameSource : actualSource = source caller.named)
    (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    Nonempty (Receipt root expressionSyntax compiler prepared (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) (i := i) (history := history)) := by
  cases sameSource
  obtain ⟨receipt⟩ := CallableIndexedOwnedChosenOrdinaryCallDispatchReceipts.at_chosen_parent
    root expressionSyntax compiler prepared member
  exact ⟨⟨rfl, receipt.chosen, receipt.sidecar, receipt.sidecarPrepared, receipt.sidecarCaller,
    receipt.sidecarSource, receipt.sidecarPlan, receipt.lambdaSite, receipt.lambdaOrigin,
    receipt.origin, receipt.rows, receipt.dispatch, receipt.selected⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport
