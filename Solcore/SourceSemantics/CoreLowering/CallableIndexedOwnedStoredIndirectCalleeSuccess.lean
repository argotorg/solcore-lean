import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCalleePost

/-! Success continues from the actual callee post constructed by the strict
child producer. Concrete unrestricted ordinary or principal witnesses retain
same-Code body Syntax and authentic invocation prefixes. These finite adapters
construct the association internally and reuse the unchanged whole-call proof.
They retain accepted empty-coercion stages and independent raw/native bundles.
Legacy prefixes, other selected origins and rejection routes remain separate.
No completed callee or body family law is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCalleeSuccess
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues
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
  {function : Dynamic.Closure} {captureScope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captured : Captures compiled.indexed mapping world captureScope function.captured capturedActual)
  (code : Code compiled.indexed function captureScope captured.administrative) (history : History code)

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

section Ordinary
variable (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
  (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin support history)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 captureScope captured.canonical owner.key.frameLocation)
  (referenceIndex : code.referenceIndex = captureScope.length + 1 + compiled.indexed.base.globals.length)
  (nativeTyped : RuntimeValueHasType world (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual)
    (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType)
  (post : ValuePost (registry := registry) (faults := faults) (actual := actual) (ξ := ξ)
    (calleeNode := calleeNode) (context := context) bridge profile compiler first
    (.closure function) calleeHeap (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual) store mapping world)
  (binderCount : ids.length = code.receipt.loweredParameters.length)
  (sourceBundle : TypeSystem.Ty.productMany sourceTypes = TypeSystem.Ty.productMany (code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)))
  (nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) = SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd))
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType)
  (nativeResult : compiler.resultType = code.receipt.resultCore)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual))
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured code history support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree post
  binderCount sourceBundle nativeBundle rawResult nativeResult stages caller sidecarSource dispatch accepted calleeTrace in
/-- The concrete ordinary receipt continues at exactly the strict child's
returned pool; the original argument and body bounds are unchanged. -/
theorem preserves_ordinary (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, _represented, heaps, maps, worlds, frame, metadata, reached, related, _admitted⟩ := post
  have selected : CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
      function (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual) code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore :=
    .ordinary owner captured code history support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree
  exact CallableIndexedOwnedStoredIndirectCallBounds.preserves_selected
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission reached related maps worlds frame metadata
    selected heaps binderCount sourceBundle nativeBundle rawResult nativeResult
    stages caller sidecarSource dispatch accepted calleeTrace calleeEvaluation budget children below suffix argumentsWithin callWithin

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured code history support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree post
  binderCount sourceBundle nativeBundle rawResult nativeResult stages caller sidecarSource dispatch accepted calleeTrace in
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
  obtain ⟨calleeEvaluation, _represented, heaps, maps, worlds, frame, metadata, reached, related, _admitted⟩ := post
  have selected : CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
      function (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual) code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore :=
    .ordinary owner captured code history support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree
  exact CallableIndexedOwnedStoredIndirectCallBounds.reflects_selected
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission reached related maps worlds frame metadata
    selected heaps binderCount sourceBundle nativeBundle rawResult nativeResult
    stages caller sidecarSource dispatch accepted calleeTrace calleeEvaluation budget children below completed within
end Ordinary

section Principal
variable (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
  (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 captureScope captured.canonical owner.key.frameLocation)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
  (referenceIndex : code.referenceIndex = captureScope.length + 1 + compiled.indexed.base.globals.length)
  (nativeTyped : RuntimeValueHasType world (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual)
    (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType)
  (post : ValuePost (registry := registry) (faults := faults) (actual := actual) (ξ := ξ)
    (calleeNode := calleeNode) (context := context) bridge profile compiler first
    (.closure function) calleeHeap (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual) store mapping world)
  (binderCount : ids.length = code.receipt.loweredParameters.length)
  (sourceBundle : TypeSystem.Ty.productMany sourceTypes = TypeSystem.Ty.productMany (code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)))
  (nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) = SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd))
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType)
  (nativeResult : compiler.resultType = code.receipt.resultCore)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual))
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured code history support origin observed leading referenceIndex nativeTyped escaped syntaxTree post
  binderCount sourceBundle nativeBundle rawResult nativeResult stages caller sidecarSource dispatch accepted calleeTrace in
/-- The concrete principal receipt continues at exactly the strict child's
returned pool; the original argument and body bounds are unchanged. -/
theorem preserves_principal (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, _represented, heaps, maps, worlds, frame, metadata, reached, related, _admitted⟩ := post
  have selected : CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
      function (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual) code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore :=
    .principal owner captured code history support origin observed leading referenceIndex nativeTyped escaped syntaxTree
  exact CallableIndexedOwnedStoredIndirectCallBounds.preserves_selected
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission reached related maps worlds frame metadata
    selected heaps binderCount sourceBundle nativeBundle rawResult nativeResult
    stages caller sidecarSource dispatch accepted calleeTrace calleeEvaluation budget children below suffix argumentsWithin callWithin

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured code history support origin observed leading referenceIndex nativeTyped escaped syntaxTree post
  binderCount sourceBundle nativeBundle rawResult nativeResult stages caller sidecarSource dispatch accepted calleeTrace in
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
  obtain ⟨calleeEvaluation, _represented, heaps, maps, worlds, frame, metadata, reached, related, _admitted⟩ := post
  have selected : CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
      function (CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual) code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore :=
    .principal owner captured code history support origin observed leading referenceIndex nativeTyped escaped syntaxTree
  exact CallableIndexedOwnedStoredIndirectCallBounds.reflects_selected
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission reached related maps worlds frame metadata
    selected heaps binderCount sourceBundle nativeBundle rawResult nativeResult
    stages caller sidecarSource dispatch accepted calleeTrace calleeEvaluation budget children below completed within
end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCalleeSuccess
