import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectSiteSuccess
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceResultReceipts

/-! The actual successful Source callee trace and genuine empty output
coercions identify the Source parent result internally. Four finite adapters
reuse the frozen same-Site continuation, preserving the actual callee post,
returned pool and independent Source/native grades. Physical binder count,
authentic contextual binder policy, strong ordinary/principal provenance and
accepted stage gates remain explicit. Rejection, nonempty coercions and other
origin branches remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectResultSuccess
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedStoredIndirectCalleePost (ValuePost)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
  {calleeNode : ExpressionNode}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  (firstAdmission : Admission bridge context first)
  {named : CallableIndexedNamedGeneration.Named} {parameters : List TypedBinder}
  {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {sourceEvidence : Dynamic.EvidenceEnvironment}
  {capturedEnvironment : Dynamic.Environment} {captureScope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captured : Captures compiled.indexed mapping world captureScope capturedEnvironment capturedActual)
  (site : Site compiled.indexed named parameters result statements sourceContext sourceEvidence capturedEnvironment
    captureScope captured.administrative)
  (history : History site.code)
  (binderPolicy : site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
    compiled.indexed.base.locals named.signature.key [])
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

section Ordinary
variable (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support site.code registry faults)
  (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin support history)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 captureScope captured.canonical owner.key.frameLocation)
  (referenceIndex : site.code.referenceIndex = captureScope.length + 1 + compiled.indexed.base.globals.length)
  (nativeTyped : RuntimeValueHasType world (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
    (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (escaped : faults .controlEscapedFunction site.code.compilation.internalReason)
  (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source named) (support.expressionSyntax (CallableIndexedNamedGeneration.source named))
    support.body.context (.statements true statements) result)
  (post : ValuePost (registry := registry) (faults := faults) (actual := actual) (ξ := ξ)
    (calleeNode := calleeNode) (context := context) bridge profile compiler first
    (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) calleeHeap (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual) store mapping world)
  (binderCount : ids.length = site.code.receipt.loweredParameters.length)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual))
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) calleeHeap)

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured site history binderPolicy actualFunctionType support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree post
  binderCount stages caller sidecarSource dispatch accepted calleeTrace in
/-- The concrete ordinary receipt continues at exactly the strict child's
returned pool; the original argument and body bounds are unchanged. -/
theorem preserves_ordinary (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals firstAdmission.heap calleeTrace)
  exact CallableIndexedOwnedStoredIndirectSiteSuccess.preserves_ordinary
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission owner captured site history binderPolicy actualFunctionType support origin prefixContext observed referenceIndex
    nativeTyped escaped syntaxTree post binderCount rawResult stages caller sidecarSource dispatch accepted calleeTrace
    budget children below suffix argumentsWithin callWithin

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured site history binderPolicy actualFunctionType support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree post
  binderCount stages caller sidecarSource dispatch accepted calleeTrace in
/-- Native ordinary continuation keeps the real callee store and complete
application bound, then reflects an independently sized Source parent. -/
theorem reflects_ordinary (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals firstAdmission.heap calleeTrace)
  exact CallableIndexedOwnedStoredIndirectSiteSuccess.reflects_ordinary
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission owner captured site history binderPolicy actualFunctionType support origin prefixContext observed referenceIndex
    nativeTyped escaped syntaxTree post binderCount rawResult stages caller sidecarSource dispatch accepted calleeTrace
    budget children below completed within

end Ordinary

section Principal
variable (support : CallableIndexedOwnedMethodLambdaSupport.Support site.code registry faults)
  (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 captureScope captured.canonical owner.key.frameLocation)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
  (referenceIndex : site.code.referenceIndex = captureScope.length + 1 + compiled.indexed.base.globals.length)
  (nativeTyped : RuntimeValueHasType world (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
    (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (escaped : faults .controlEscapedFunction site.code.compilation.internalReason)
  (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source named) (support.expressionSyntax (CallableIndexedNamedGeneration.source named))
    support.body.context (.statements true statements) result)
  (post : ValuePost (registry := registry) (faults := faults) (actual := actual) (ξ := ξ)
    (calleeNode := calleeNode) (context := context) bridge profile compiler first
    (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) calleeHeap (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual) store mapping world)
  (binderCount : ids.length = site.code.receipt.loweredParameters.length)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual))
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) calleeHeap)

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured site history binderPolicy actualFunctionType support origin observed leading referenceIndex nativeTyped escaped syntaxTree post
  binderCount stages caller sidecarSource dispatch accepted calleeTrace in
/-- The concrete principal receipt continues at exactly the strict child's
returned pool; the original argument and body bounds are unchanged. -/
theorem preserves_principal (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals firstAdmission.heap calleeTrace)
  exact CallableIndexedOwnedStoredIndirectSiteSuccess.preserves_principal
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission owner captured site history binderPolicy actualFunctionType support origin observed leading referenceIndex
    nativeTyped escaped syntaxTree post binderCount rawResult stages caller sidecarSource dispatch accepted calleeTrace
    budget children below suffix argumentsWithin callWithin

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured site history binderPolicy actualFunctionType support origin observed leading referenceIndex nativeTyped escaped syntaxTree post
  binderCount stages caller sidecarSource dispatch accepted calleeTrace in
/-- Native principal continuation keeps the real callee store and complete
application bound, then reflects an independently sized Source parent. -/
theorem reflects_principal (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals firstAdmission.heap calleeTrace)
  exact CallableIndexedOwnedStoredIndirectSiteSuccess.reflects_principal
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission owner captured site history binderPolicy actualFunctionType support origin observed leading referenceIndex
    nativeTyped escaped syntaxTree post binderCount rawResult stages caller sidecarSource dispatch accepted calleeTrace
    budget children below completed within

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectResultSuccess
