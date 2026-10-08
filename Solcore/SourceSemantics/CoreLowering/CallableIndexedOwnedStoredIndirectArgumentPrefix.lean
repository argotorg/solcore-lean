import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectSuccessStep
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectNativePrefix

/-! Finite argument-prefix reflection after the actual first guard passed.
The same callee post supplies Source admission and runtime representations to
the existing ordered sequence proof. Its true Source typing row stays separate
from compiler parameter rows. Argument failure retains the real reached pool
and original parent fault; argument success retains the complete fourth bind's
gate and application traces at their original strict budget. No body or guard
classification is manufactured from packed values or types. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectArgumentPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
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

/-- The fourth original bind retains the entire application grade. Neither
argument packing nor a Source product type supplies its guard verdict. -/
inductive ApplicationPrefix (budget : Nat) (site : SourceCoreCallableContracts.Callsite) (unknown : Word)
    (result : Ty) (actual : Environment) (argumentStore : Store) (carrier packed : Value) :
    Value → Store → Prop where
  | failed {size : Nat} {input : Ty} {payload : Value} {after : Store}
      (gate : EvaluationSize size (packed :: .unit :: carrier :: actual) argumentStore
        (CallableContract.dispatch site.gates .beforeApplication unknown (.second (.var 2)))
        (.inLeft input payload) after)
      (strict : size < budget) :
      ApplicationPrefix budget site unknown result actual argumentStore carrier packed (.inLeft result payload) after
  | passed {gateSize applicationSize : Nat} {input : Ty} {payload value : Value} {middle after : Store}
      (gate : EvaluationSize gateSize (packed :: .unit :: carrier :: actual) argumentStore
        (CallableContract.dispatch site.gates .beforeApplication unknown (.second (.var 2)))
        (.inRight input payload) middle)
      (application : EvaluationSize applicationSize (payload :: packed :: .unit :: carrier :: actual) middle
        (.apply (.second (.first (.var 3))) (.var 1)) value after)
      (gateStrict : gateSize < budget) (applicationStrict : applicationSize < budget) :
      ApplicationPrefix budget site unknown result actual argumentStore carrier packed value after

variable {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value} {sourceValue : Dynamic.Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee sourceValue calleeHeap)
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge profile compiler initial sourceValue calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids sourceValue)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)

/-- Argument failure stops at its actual reached witness. The genuine Source
parent and staged semanticFault retain independent Source grades and effects. -/
def FaultPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize parentSize reason token after finalMap finalWorld,
    EvaluationSize nativeSize (.unit :: calleeNative :: actual) calleeStore
      ((((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0).weakenAt 0)
      (.inLeft (SourceCoreCalls.packArguments compiler.codes).type (.word token)) finalStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionsFault (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment calleeHeap ids reason after ∧
    Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
      context evidence source environment before id callee ids metadata (.semanticFault reason) after ∧
    RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) parentSize
      context evidence source environment before id (.fault reason) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
      bridge profile compiler initial (.fault reason) after value finalStore finalMap finalWorld

/-- The real successful argument sequence retains its complete Source/native
row, actual cumulative pool and admission, and the original fourth bind. -/
def SuccessPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sources values after argumentStore finalMap finalWorld,
    EvaluationSize nativeSize (.unit :: calleeNative :: actual) calleeStore
      ((((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0).weakenAt 0)
      (.inRight .word (DataPatternValues.packValues values)) argumentStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment calleeHeap ids sources after ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after argumentStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentStore ∧ Dynamic.HeapMetadataExtend before after ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, argumentStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
    (∃ remainingSize,
      EvaluationSize remainingSize (DataPatternValues.packValues values :: .unit :: calleeNative :: actual) argumentStore
        (LanguageResult.bind compiler.resultType
          (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
          (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧
      remainingSize < budget ∧
      ApplicationPrefix budget prepared.site native.diagnostics.unknown compiler.resultType actual
        argumentStore calleeNative (DataPatternValues.packValues values) value finalStore)

include caller sidecarSource parentTyped wellFormed runtime covers environments locals agrees typed admitted
  calleeTrace post accepted tree unique in
/-- Use the existing ordered sequence proof at the same admitted callee post.
Two further original bind projections retain actual argument failure or the
complete beforeApplication gate and application trace, with no body IH. -/
theorem reflects_suffix_with_effects (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (.unit :: calleeNative :: actual) calleeStore
      (CallableIndexedOwnedStoredIndirectNativePrefix.suffix prepared.site native.diagnostics.unknown compiler.resultType
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore)
    (smaller : size < budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (FaultPrefix (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
        bridge profile compiler initial budget value finalStore ∨
      (SuccessPrefix (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
        (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
        bridge profile compiler prepared initial budget value finalStore ∧
      CallableIndexedOwnedStoredIndirectSuccessStep.SuccessStep (registry := registry) (faults := faults)
        (context := context) (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
        (sourceTypes := sourceTypes) (calleeHeap := calleeHeap) (calleeNative := calleeNative)
        (calleeStore := calleeStore) (calleeMap := calleeMap) (calleeWorld := calleeWorld)
        bridge profile compiler prepared initial budget value finalStore)) := by
  obtain ⟨_parameter, _sourceResult, rawTypes, _calleeTyped, argumentsTyped, _application⟩ :=
    CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts unique compiler.found compiler.originalForm parentTyped
  obtain ⟨calleeEvaluation, calleeRepresentation, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
    calleeMetadata, calleeReached, calleeRelated, calleePost⟩ := post
  have calleeAdmission := calleePost.at_value.2
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ))
      canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons calleeRepresentation.runtime_hasType (typed.weaken calleeWorlds))
  refine ⟨caller, sidecarSource, ?_⟩
  cases CallableIndirectCallBounds.bind_completed completed (Nat.le_of_lt smaller) with
  | failed argumentTrace argumentStrict =>
    have originalArguments := argumentTrace
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentTrace
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyped children
        (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) layout actualTyped
        calleeReached calleeAdmission argumentTrace argumentStrict
    cases represented with
    | @fault reason token matched =>
      cases trace with
      | fault failed =>
        have original : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram)
            (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, sourceSize]])
            context evidence source environment before id (.fault reason) after := by
          refine .fault (.form (size_fault := SourceExecutionSize.stepSize [calleeSize, sourceSize])
            (lookupExpression?_sound compiler.found) ?_)
          rw [compiler.originalForm]
          exact .indirectArguments calleeTrace accepted.callable failed
        have staged : Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
            context evidence source environment before id callee ids metadata (.semanticFault reason) after :=
          .argumentsFault calleeTrace.sound (by simpa only [prepared.call] using accepted) failed.sound
        have loweredType : lowered.type = compiler.resultType :=
          (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
        left
        refine ⟨_, sourceSize, _, reason, token, after, finalMap, finalWorld, originalArguments, argumentStrict,
          failed, staged, original, ?_, ?_⟩
        · rw [loweredType]
        · rw [← loweredType]
          exact ⟨.fault matched, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
            calleeFrame.trans frame, calleeMetadata.trans heapMetadata, reached,
            callerProtocol.trans calleeRelated related,
            after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped original (calleeFrame.trans frame)⟩
  | continued argumentTrace remaining argumentStrict remainingStrict =>
    have originalArguments := argumentTrace
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentTrace
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, argumentPost⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyped children
        (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) layout actualTyped
        calleeReached calleeAdmission argumentTrace argumentStrict
    cases represented with
    | values represented =>
      cases trace with
      | values evaluated =>
        right
        constructor
        · refine ⟨_, sourceSize, _, _, after, _, finalMap, finalWorld, originalArguments, argumentStrict,
            evaluated, represented, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
            calleeFrame.trans frame, calleeMetadata.trans heapMetadata,
            ⟨reached, callerProtocol.trans calleeRelated related, argumentPost.at_values⟩, ?_⟩
          refine ⟨_, remaining, remainingStrict, ?_⟩
          cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
          | failed gate gateStrict => exact .failed gate gateStrict
          | continued gate application gateStrict applicationStrict => exact .passed gate application gateStrict applicationStrict
        · exact ⟨_, sourceSize, _, _, after, _, finalMap, finalWorld, originalArguments, argumentStrict,
            evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata,
            calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
            calleeMetadata.trans heapMetadata,
            ⟨reached, callerProtocol.trans calleeRelated related, argumentPost.at_values⟩,
            ⟨_, remaining, remainingStrict⟩⟩


include caller sidecarSource parentTyped wellFormed runtime covers environments locals agrees typed admitted
  calleeTrace post accepted tree unique in
/-- Use the existing ordered sequence proof at the same admitted callee post.
Two further original bind projections retain actual argument failure or the
complete beforeApplication gate and application trace, with no body IH. -/
theorem reflects_suffix (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (.unit :: calleeNative :: actual) calleeStore
      (CallableIndexedOwnedStoredIndirectNativePrefix.suffix prepared.site native.diagnostics.unknown compiler.resultType
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore)
    (smaller : size < budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (FaultPrefix (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
        bridge profile compiler initial budget value finalStore ∨
      SuccessPrefix (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
        (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
        bridge profile compiler prepared initial budget value finalStore) := by
  obtain ⟨sameCaller, sameSource, result⟩ := reflects_suffix_with_effects bridge profile compiler prepared
    parentTyped wellFormed runtime covers environments locals agrees typed initial admitted caller sidecarSource
    calleeTrace post accepted tree unique budget children completed smaller
  exact ⟨sameCaller, sameSource, result.elim Or.inl (fun success => Or.inr success.1)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectArgumentPrefix
