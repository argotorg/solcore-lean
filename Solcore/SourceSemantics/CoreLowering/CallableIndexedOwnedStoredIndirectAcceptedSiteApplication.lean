import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectAcceptedApplication

/-! Concrete accepted suffix adapters retain the exact chosen contextual Site,
full Source origin and captured history. Its real binder policy derives the
native binder pack internally; the existing accepted suffix derives raw
Source admission and both result types from authentic traces. The actual
ordered argument receipt and whole fourth-bind grade are kept unchanged.
These endpoints accept strong ordinary/principal origins with empty coercions;
other origins and rejected gates retain their separate prefix outcomes. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectAcceptedSiteApplication
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedStoredIndirectCalleePost (ValuePost)
open CallableIndexedOwnedStoredClosureInvocation (Association)
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
  (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source named)
    (support.expressionSyntax (CallableIndexedNamedGeneration.source named)) support.body.context
    (.statements true statements) result)
  (post : ValuePost (registry := registry) (faults := faults) (actual := actual) (ξ := ξ)
    (calleeNode := calleeNode) (context := context) bridge profile compiler first
    (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) calleeHeap
    (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual) store mapping world)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment))
    (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual))
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids
    (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee
    (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) calleeHeap)

include parent tree unique parentTyped wellFormed runtime covers locals firstAdmission
  owner captured site history binderPolicy actualFunctionType support origin prefixContext
  observed referenceIndex nativeTyped escaped syntaxTree post dispatch accepted calleeTrace in
/-- The concrete same-Site ordinary suffix uses the retained real argument
post and intermediate effects, with only strict shared-family body IH. -/
theorem reflects_ordinary (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.SuccessPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap)
      (calleeNative := CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
      (calleeStore := store) bridge profile compiler prepared first budget value finalStore)
    (step : CallableIndexedOwnedStoredIndirectSuccessStep.SuccessStep
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap)
      (calleeNative := CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
      (calleeStore := store) (calleeMap := mapping) (calleeWorld := world)
      bridge profile compiler prepared first budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    CallableIndexedOwnedStoredIndirectAcceptedApplication.ResultAt
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap)
      (calleeNative := CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
      (calleeStore := store) (calleeMap := mapping) (calleeWorld := world) (sidecar := sidecar)
      bridge profile compiler prepared first dispatch budget value finalStore := by
  have association : Association headers keys registry faults mapping world
      (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)
      (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
      site.code.receipt.loweredParameters site.code.receipt.parameterCore site.code.receipt.resultCore :=
    Association.ordinary
      (headers := headers) (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (function := closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)
      (scope := captureScope) (actual := capturedActual)
      owner captured site.code history support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree
  have bindingPack := CallableIndexedOwnedContextualLambdaPackReceipts.Site.binding_pack
    site profile binderPolicy support.body.extended
  exact CallableIndexedOwnedStoredIndirectAcceptedApplication.reflects_selected
    bridge profile compiler prepared parentTyped wellFormed runtime covers locals first firstAdmission tree unique parent
    actualFunctionType calleeTrace post dispatch accepted association bindingPack budget below original step passed

end Ordinary
section Principal
variable (support : CallableIndexedOwnedMethodLambdaSupport.Support site.code registry faults)
  (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 captureScope captured.canonical owner.key.frameLocation)
  (referenceIndex : site.code.referenceIndex = captureScope.length + 1 + compiled.indexed.base.globals.length)
  (nativeTyped : RuntimeValueHasType world (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
    (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (escaped : faults .controlEscapedFunction site.code.compilation.internalReason)
  (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source named)
    (support.expressionSyntax (CallableIndexedNamedGeneration.source named)) support.body.context
    (.statements true statements) result)
  (post : ValuePost (registry := registry) (faults := faults) (actual := actual) (ξ := ξ)
    (calleeNode := calleeNode) (context := context) bridge profile compiler first
    (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) calleeHeap
    (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual) store mapping world)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment))
    (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual))
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids
    (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee
    (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) calleeHeap)

include parent tree unique parentTyped wellFormed runtime covers locals firstAdmission
  owner captured site history binderPolicy actualFunctionType support origin leading
  observed referenceIndex nativeTyped escaped syntaxTree post dispatch accepted calleeTrace in
/-- The concrete same-Site principal suffix uses the retained real argument
post and intermediate effects, with only strict shared-family body IH. -/
theorem reflects_principal (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.SuccessPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap)
      (calleeNative := CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
      (calleeStore := store) bridge profile compiler prepared first budget value finalStore)
    (step : CallableIndexedOwnedStoredIndirectSuccessStep.SuccessStep
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap)
      (calleeNative := CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
      (calleeStore := store) (calleeMap := mapping) (calleeWorld := world)
      bridge profile compiler prepared first budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    CallableIndexedOwnedStoredIndirectAcceptedApplication.ResultAt
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap)
      (calleeNative := CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
      (calleeStore := store) (calleeMap := mapping) (calleeWorld := world) (sidecar := sidecar)
      bridge profile compiler prepared first dispatch budget value finalStore := by
  have association : Association headers keys registry faults mapping world
      (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)
      (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
      site.code.receipt.loweredParameters site.code.receipt.parameterCore site.code.receipt.resultCore :=
    Association.principal
      (headers := headers) (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (function := closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)
      (scope := captureScope) (actual := capturedActual)
      owner captured site.code history support origin observed leading referenceIndex nativeTyped escaped syntaxTree
  have bindingPack := CallableIndexedOwnedContextualLambdaPackReceipts.Site.binding_pack
    site profile binderPolicy support.body.extended
  exact CallableIndexedOwnedStoredIndirectAcceptedApplication.reflects_selected
    bridge profile compiler prepared parentTyped wellFormed runtime covers locals first firstAdmission tree unique parent
    actualFunctionType calleeTrace post dispatch accepted association bindingPack budget below original step passed

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectAcceptedSiteApplication
