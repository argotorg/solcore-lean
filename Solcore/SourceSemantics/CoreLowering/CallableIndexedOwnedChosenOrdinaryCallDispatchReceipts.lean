import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredMembers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallCodebookReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes

/-! The known chosen ordinary closure selects its actual source sidecar,
lambda origin and parent codebook row. Original and contextual lambda origins
remain available, including contextual origins whose substitution is empty.
This static receipt retains the literal capture/history carrier; association
with an actual callee read or value post remains a runtime input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchReceipts
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

/-- The positive constructor identifies the actual owning Header. -/
theorem chosen_caller (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    i.support.caller = caller := by
  have factory := member.factory
  cases factory with
  | formed receipt chosen environment captured prefixContext => rfl

variable {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {call callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt root.selected.policy root.selected.lowerBody fuel
    (context compiled.indexed caller.named) (source caller.named) scope call callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)

/-- Every field is tied to the same known closure and original parent receipt.
The selected row records its genuine guard provenance without assuming a
stage verdict, argument execution or called-body meaning. -/
structure Receipt where
  chosen : ChosenAt root expressionSyntax headers keys registry faults i history
  sidecar : SourceCoreStageContracts.Sidecar
  sidecarPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
    (context compiled.indexed caller.named).owner = .ok sidecar
  sidecarCaller : sidecar.caller = caller.named.specialized
  sidecarSource : sidecar.source = source caller.named
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

/-- Actual public preparation and the known positive member construct the
sidecar, both lambda-origin alternatives, complete rows and exact selection.
The original parent policy, scope, children and budget are preserved. -/
theorem at_chosen_parent (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    Nonempty (Receipt root expressionSyntax compiler prepared (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) (i := i) (history := history)) := by
  have sameCaller := chosen_caller root expressionSyntax member
  have actual := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  obtain ⟨lambdaSite⟩ := RecursiveStageProjection.lambda_site_of_descriptor actual.accepted i.code.descriptor
  obtain ⟨sidecar, sidecarPrepared, _⟩ := LambdaSourceAlignment.LambdaSource.canonical lambdaSite.original
  have sourceReceipt := i.support.source_receipt
  have sameSource := sourceReceipt.source sidecarPrepared
  rw [i.support.active, EmptySourceSubstitution.source] at sameSource
  have owner : i.code.compilation.owner = (context compiled.indexed caller.named).owner := by
    rw [i.support.compilation, sameCaller]
  have callerPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      (context compiled.indexed caller.named).owner = .ok sidecar := by
    rwa [owner] at sidecarPrepared
  have sidecarCaller := RecursiveNamedPreparedStageScopes.sidecar_caller callerPrepared
    (CallableIndexedActualNamedSourceReceipts.header_record compiled caller)
  have source : sidecar.source = CallableIndexedNamedGeneration.source caller.named := by
    rw [← sameSource, i.support.source, sameCaller]
  have sidecarPlan := (CallContractCertificates.sidecar_of_accepted callerPrepared).1
  have lambdaOrigin := LambdaMetadataViews.lambda_origin sourceReceipt lambdaSite.original
    i.code.viewOfSource i.support.unique i.code.found (i.code.form.trans i.code.sourceForm)
  have codeOrigin : CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual) := by
    have represented := CallableLedger.OriginRep.closure
      (raw := .pair (.inLeft .word .unit)
        (.closure i.code.receipt.parameterCore (LanguageResult.resultType i.code.receipt.resultCore)
          (i.code.body.rename i.captured.embedding.lift.lift)
          (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)))
      lambdaSite.member lambdaSite.origin lambdaSite.retained lambdaOrigin
    simpa only [value, lambdaSite.id_eq] using represented
  have parentContains : ContainsExpression sidecar.source prepared.site.call compiler.original := by
    rw [source, prepared.call]
    exact lookupExpression?_sound compiler.found
  have atSite := actual.accepted
  rw [← prepared.table] at atSite
  have atCaller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar := by
    rwa [prepared.caller]
  have rows := CallCodebookCertificates.rows_of_prepareWithProjection atSite atCaller
    parentContains compiler.originalForm
  have origin : CallableLedger.OriginRep sidecar.plan prepared.site.table (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual) := by
    rw [sidecarPlan, prepared.table]
    exact codeOrigin
  have bound : (CallableLedger.frame sidecar).Binds (.closure i.function)
      (CallContractCertificates.semanticContract lambdaSite.contract) := by
    change CallableLedger.Binds sidecar.plan (.closure i.function)
      (CallContractCertificates.semanticContract lambdaSite.contract)
    rw [sidecarPlan]
    exact lambdaOrigin.binds
  obtain ⟨dispatch⟩ := CallableLedger.dispatch rows origin bound
  have dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site call ids
      (.closure i.function) (value i.code i.captured.embedding history.native i.capturedActual) := by
    rwa [prepared.call] at dispatch
  have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared actual prepared.table
    atCaller parentContains compiler.originalForm (by rw [← sameSource]; exact i.support.unique) dispatch.found
  exact ⟨⟨member, sidecar, callerPrepared, sidecarCaller, source, sidecarPlan, lambdaSite,
    lambdaOrigin, origin, rows, dispatch, selected⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchReceipts
