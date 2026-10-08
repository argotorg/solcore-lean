import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectParentPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectAcceptedSiteApplication

/-! The whole parent produces one actual callee post. Concrete same-Site
provenance is consumed only at that post. Earlier outcomes retain their original
receipts; the passed branch uses actual intermediate effects and strict body
IH. The conditional callback supplies no classifier for other values. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectParentApplication
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaGeneration
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
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
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)

variable {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) calleeNative)

/-- Each alternative retains its genuine outcome at the actual reached post.
Accepted arguments retain the entire original receipt, actual intermediate
effects and fourth-bind grade. -/
def ResolvedAt (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  (∃ reason, value = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧
    CallableIndexedOwnedStoredIndirectStageBoundary.ResultAt
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (mapping := calleeMap) (world := calleeWorld)
      (calleeHeap := calleeHeap) (store := calleeStore)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize)
      bridge profile compiler prepared initial dispatch reason (dispatch.reason reason) finalStore) ∨
  (Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function) ∧
    (CallableIndexedOwnedStoredIndirectArgumentPrefix.FaultPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge profile compiler initial budget value finalStore ∨
    (CallableIndexedOwnedStoredIndirectArgumentPrefix.SuccessPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge profile compiler prepared initial budget value finalStore ∧
      CallableIndexedOwnedStoredIndirectSuccessStep.SuccessStep
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
        (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
        (calleeMap := calleeMap) (calleeWorld := calleeWorld)
        bridge profile compiler prepared initial budget value finalStore ∧
      (CallableIndexedOwnedStoredIndirectApplicationPrefix.RejectedAt
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (sidecar := sidecar) bridge profile compiler prepared initial dispatch value finalStore ∨
      CallableIndexedOwnedStoredIndirectAcceptedApplication.ResultAt
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
        (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
        (calleeMap := calleeMap) (calleeWorld := calleeWorld) (sidecar := sidecar)
        bridge profile compiler prepared initial dispatch budget value finalStore))))


variable {named : CallableIndexedNamedGeneration.Named} {parameters : List TypedBinder}
  {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {sourceEvidence : Dynamic.EvidenceEnvironment}
  {capturedEnvironment : Dynamic.Environment} {captureScope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

/-- The retained prefix and its same actual post accept only genuine
constructor-specific static provenance. No classifier existence is asserted. -/
def OrdinaryValueAt (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  CallableIndexedOwnedStoredIndirectParentPrefix.ValuePrefixWithEffects
    (registry := registry) (faults := faults) (context := context) (evidence := evidence)
    (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
    (sourceTypes := sourceTypes) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore ∧
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before callee sourceValue after ∧
    CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge profile compiler initial sourceValue after carrier calleeStore finalMap finalWorld ∧
    ∀ (captured : Captures compiled.indexed finalMap finalWorld captureScope capturedEnvironment capturedActual)
      (site : Site compiled.indexed named parameters result statements sourceContext sourceEvidence capturedEnvironment
        captureScope captured.administrative) (history : History site.code),
      sourceValue = .closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment) →
      carrier = CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual →
      site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
        ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
        compiled.indexed.base.locals named.signature.key [] →
      ∀ (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support site.code registry faults),
        CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin support history →
        captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
          (values := .initial compiled.compatible.checked) support.caller →
        CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations 1 captureScope captured.canonical owner.key.frameLocation →
        site.code.referenceIndex = captureScope.length + 1 + compiled.indexed.base.globals.length →
        RuntimeValueHasType finalWorld
          (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
          (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) compiled.indexed.layouts.definitions →
        faults .controlEscapedFunction site.code.compilation.internalReason →
        GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source named)
          (support.expressionSyntax (CallableIndexedNamedGeneration.source named)) support.body.context
          (.statements true statements) result →
        ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
            (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment))
            (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual))
          (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
            compiler.original dispatch.row),
          ResolvedAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
            (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
            (calleeMap := finalMap) (calleeWorld := finalWorld) (calleeHeap := after)
            (calleeStore := calleeStore) (calleeSize := sourceSize) (sourceTypes := sourceTypes)
            bridge profile compiler prepared initial dispatch budget value finalStore

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource tree unique parent
  owner actualFunctionType in
/-- Reflect the whole parent once; invoke only the actual accepted callable
through strict body IH and genuine same-Site provenance at its produced post. -/
theorem reflects_ordinary (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (CallableIndexedOwnedStoredIndirectNativePrefix.FaultPrefix
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        bridge profile compiler initial budget value finalStore ∨
      OrdinaryValueAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (named := named) (parameters := parameters) (result := result) (statements := statements)
        (sourceContext := sourceContext) (sourceEvidence := sourceEvidence) (capturedEnvironment := capturedEnvironment)
        (captureScope := captureScope) (capturedActual := capturedActual)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
        (sourceTypes := sourceTypes) (sidecar := sidecar)
        bridge profile compiler prepared initial owner budget value finalStore) := by
  obtain ⟨sameCaller, sameSource, producedPrefix⟩ :=
    CallableIndexedOwnedStoredIndirectParentPrefix.reflects_parent_with_effects bridge profile compiler prepared
      certified found sourceTyped parentTyped wellFormed runtime covers environments heaps locals agrees typed
      initial admitted caller sidecarSource tree unique parent budget children completed within
  refine ⟨sameCaller, sameSource, ?_⟩
  rcases producedPrefix with failed | succeeded
  · exact Or.inl failed
  · right
    refine ⟨succeeded, ?_⟩
    obtain ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, _gate, resolver⟩ := succeeded
    refine ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, ?_⟩
    intro captured site history sameClosure sameNative binderPolicy support origin prefixFacts observed referenceIndex nativeTyped escaped syntaxTree dispatch selected
    cases sameClosure
    cases sameNative
    have resolution := resolver _ rfl dispatch selected
    rcases resolution with rejected | ⟨accepted, arguments⟩
    · exact Or.inl rejected
    · refine Or.inr ⟨accepted, ?_⟩
      rcases arguments with failed | ⟨original, step, verdict⟩
      · exact Or.inl failed
      · right
        refine ⟨original, step, ?_⟩
        rcases verdict with rejected | passed
        · exact Or.inl rejected
        · right
          exact CallableIndexedOwnedStoredIndirectAcceptedSiteApplication.reflects_ordinary
            bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers
            locals initial admitted owner captured site history binderPolicy actualFunctionType support origin prefixFacts
            observed referenceIndex nativeTyped escaped syntaxTree post dispatch accepted trace budget below original step passed

/-- The retained prefix and its same actual post accept only genuine
constructor-specific static provenance. No classifier existence is asserted. -/
def PrincipalValueAt (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  CallableIndexedOwnedStoredIndirectParentPrefix.ValuePrefixWithEffects
    (registry := registry) (faults := faults) (context := context) (evidence := evidence)
    (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
    (sourceTypes := sourceTypes) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore ∧
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before callee sourceValue after ∧
    CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge profile compiler initial sourceValue after carrier calleeStore finalMap finalWorld ∧
    ∀ (captured : Captures compiled.indexed finalMap finalWorld captureScope capturedEnvironment capturedActual)
      (site : Site compiled.indexed named parameters result statements sourceContext sourceEvidence capturedEnvironment
        captureScope captured.administrative) (history : History site.code),
      sourceValue = .closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment) →
      carrier = CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual →
      site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
        ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
        compiled.indexed.base.locals named.signature.key [] →
      ∀ (support : CallableIndexedOwnedMethodLambdaSupport.Support site.code registry faults),
        CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history →
        captured.administrative[0]? = some support.principal.named.signature.parameterType →
        CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations 1 captureScope captured.canonical owner.key.frameLocation →
        site.code.referenceIndex = captureScope.length + 1 + compiled.indexed.base.globals.length →
        RuntimeValueHasType finalWorld
          (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
          (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) compiled.indexed.layouts.definitions →
        faults .controlEscapedFunction site.code.compilation.internalReason →
        GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source named)
          (support.expressionSyntax (CallableIndexedNamedGeneration.source named)) support.body.context
          (.statements true statements) result →
        ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
            (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment))
            (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual))
          (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
            compiler.original dispatch.row),
          ResolvedAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
            (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
            (calleeMap := finalMap) (calleeWorld := finalWorld) (calleeHeap := after)
            (calleeStore := calleeStore) (calleeSize := sourceSize) (sourceTypes := sourceTypes)
            bridge profile compiler prepared initial dispatch budget value finalStore

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource tree unique parent
  owner actualFunctionType in
/-- Reflect the whole parent once; invoke only the actual accepted callable
through strict body IH and genuine same-Site provenance at its produced post. -/
theorem reflects_principal (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (CallableIndexedOwnedStoredIndirectNativePrefix.FaultPrefix
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        bridge profile compiler initial budget value finalStore ∨
      PrincipalValueAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (named := named) (parameters := parameters) (result := result) (statements := statements)
        (sourceContext := sourceContext) (sourceEvidence := sourceEvidence) (capturedEnvironment := capturedEnvironment)
        (captureScope := captureScope) (capturedActual := capturedActual)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
        (sourceTypes := sourceTypes) (sidecar := sidecar)
        bridge profile compiler prepared initial owner budget value finalStore) := by
  obtain ⟨sameCaller, sameSource, producedPrefix⟩ :=
    CallableIndexedOwnedStoredIndirectParentPrefix.reflects_parent_with_effects bridge profile compiler prepared
      certified found sourceTyped parentTyped wellFormed runtime covers environments heaps locals agrees typed
      initial admitted caller sidecarSource tree unique parent budget children completed within
  refine ⟨sameCaller, sameSource, ?_⟩
  rcases producedPrefix with failed | succeeded
  · exact Or.inl failed
  · right
    refine ⟨succeeded, ?_⟩
    obtain ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, _gate, resolver⟩ := succeeded
    refine ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, ?_⟩
    intro captured site history sameClosure sameNative binderPolicy support origin prefixFacts observed referenceIndex nativeTyped escaped syntaxTree dispatch selected
    cases sameClosure
    cases sameNative
    have resolution := resolver _ rfl dispatch selected
    rcases resolution with rejected | ⟨accepted, arguments⟩
    · exact Or.inl rejected
    · refine Or.inr ⟨accepted, ?_⟩
      rcases arguments with failed | ⟨original, step, verdict⟩
      · exact Or.inl failed
      · right
        refine ⟨original, step, ?_⟩
        rcases verdict with rejected | passed
        · exact Or.inl rejected
        · right
          exact CallableIndexedOwnedStoredIndirectAcceptedSiteApplication.reflects_principal
            bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers
            locals initial admitted owner captured site history binderPolicy actualFunctionType support origin prefixFacts
            observed referenceIndex nativeTyped escaped syntaxTree post dispatch accepted trace budget below original step passed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectParentApplication
