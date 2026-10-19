import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectFirstGateBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingFirstCallGateRejection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedStagedCallFaults
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageBoundary

/-! Whole-parent reflection joins the genuine callee, first-gate and ordered-argument fault prefixes. The authentic successful argument suffix remains available for its concrete application producer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectFaultDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CellAwareScopeIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {certificate : GenericExpressionMeaning.Certificate}
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel)
    (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (ownerFrame : owner.key.frameLocation = physical.location)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

/-- A fault branch of the actual native parent, with its independently sized
Source derivation and the exact token, reached state and failure tag. -/
def FaultResult (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize failure after token finalMap finalWorld,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before id (.fault failure) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CellAwareScopeIndirectCalleeFaultBounds.ResultAt
      (registry := completion.result.context.registry) (faults := callFaults) (context := context)
      (actual := actual) (ξ := ξ) bridge functions compiler initial
      failure after token finalStore finalMap finalWorld

include positive receiver prepared stagePrepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
  environments heaps locals agrees typed admitted authority physical ownerFrame caller view originalUnique guardFrame
  sourceParent tree unique parentTyped in
/-- The actual whole parent is inverted once. Every reached callee, first-gate
or ordered-argument failure becomes its exact parent result. Successful
arguments retain the authentic application suffix for its concrete producer. -/
theorem reflects_fault_or_application (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow
      bridge context model named stages invocation certificate callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    FaultResult (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ)
      bridge compiler initial profile value finalStore ∨
    CellAwareScopeIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner budget value finalStore := by
  rcases CellAwareScopeIndirectArgumentPrefix.reflects_arguments
      bridge profile compiler prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
      environments heaps locals agrees typed initial admitted authority physical owner ownerFrame caller view originalUnique
      guardFrame sourceParent tree unique parentTyped budget calleeMeaning children completed within with
    calleeFault | stageRejected | argumentFault | application
  · obtain ⟨_nativeSize, sourceSize, failure, token, after, finalMap, finalWorld,
      _native, _strict, _child, parentTrace, valueEq, post⟩ := calleeFault
    exact .inl ⟨Staging.Recursive.Size.stepSize [sourceSize], failure, after, token,
      finalMap, finalWorld, parentTrace, valueEq, post⟩
  · obtain ⟨sourceSize, reason, after, token, finalMap, finalWorld,
      parentTrace, valueEq, post⟩ :=
      CellAwareScopeIndirectFirstGateBounds.reflects_rejected_prefix
        bridge receiver compiler prepared stagePrepared sourceEq occurrence initial owner
        view guardFrame profile budget stageRejected
    exact .inl ⟨sourceSize, .stage invocation id reason, after, token,
      finalMap, finalWorld, parentTrace, valueEq, post⟩
  · obtain ⟨calleeSize, argumentsSize, sourceValue, calleeHeap, failure, after,
      token, finalMap, finalWorld, _callee, _accepted, _arguments,
      parentTrace, valueEq, post⟩ := argumentFault
    exact .inl ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize],
      failure, after, token, finalMap, finalWorld, parentTrace, valueEq, post⟩
  · exact .inr application

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectFaultDispatch
