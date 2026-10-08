import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectApplicationPrefix

/-! Finite parent-prefix composition for the accepted empty-coercion stored
call route. Strict generic child IH constructs one actual callee post from the
full native parent. Only that witness accepts a concrete closure identity and
its genuine attached Dispatch/Selected receipts. The finite resolver keeps
semantic faults, stage rejection and physical arity rejection separate, and
passes the original successful argument receipt and whole fourth-bind bound
forward. It promises no closure or dispatch classifier for other values and
invokes no callable body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectParentPrefix
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

variable {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
    compiler.original dispatch.row)

/-- Each alternative retains its genuine outcome at the actual reached post.
Accepted arguments retain the entire original receipt and fourth-bind grade. -/
def ClosureResolution (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
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
      (CallableIndexedOwnedStoredIndirectApplicationPrefix.RejectedAt
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (sidecar := sidecar) bridge profile compiler prepared initial dispatch value finalStore ∨
      CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
        compiler prepared dispatch budget value finalStore))))


/-- Each alternative retains its genuine outcome at the actual reached post.
Accepted arguments retain the entire original receipt, actual intermediate
effects and fourth-bind grade. -/
def ClosureResolutionWithEffects (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
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
      CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
        compiler prepared dispatch budget value finalStore))))

variable (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge profile compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)

include caller sidecarSource parentTyped wellFormed runtime covers environments locals agrees typed admitted
  calleeTrace post tree unique parent selected in
/-- Consume static dispatch receipts only at the one actual closure post.
The existing prefix proofs handle both guards and the ordered children. -/
theorem resolve_closure_with_effects (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {value : Value} {finalStore : Store}
    (receipt : CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site
      native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore calleeNative value finalStore) :
    ClosureResolutionWithEffects (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld) (calleeHeap := calleeHeap)
      (calleeStore := calleeStore) (calleeSize := calleeSize) (sourceTypes := sourceTypes)
      bridge profile compiler prepared initial dispatch budget value finalStore := by
  rcases CallableIndexedOwnedStoredIndirectNativePrefix.resolve_at_post bridge profile compiler prepared initial
      caller sidecarSource calleeTrace post dispatch receipt with rejected | ⟨accepted, suffixSize, suffix, smaller⟩
  · exact Or.inl rejected
  · right
    refine ⟨accepted, ?_⟩
    obtain ⟨_caller, _source, arguments⟩ :=
      CallableIndexedOwnedStoredIndirectArgumentPrefix.reflects_suffix_with_effects bridge profile compiler prepared parentTyped
        wellFormed runtime covers environments locals agrees typed initial admitted caller sidecarSource calleeTrace post
        accepted tree unique budget children suffix smaller
    rcases arguments with failed | succeeded
    · exact Or.inl failed
    · right
      obtain ⟨sameSuccess, verdict⟩ := CallableIndexedOwnedStoredIndirectApplicationPrefix.resolve_success
        bridge profile compiler prepared parentTyped wellFormed runtime covers locals initial admitted
        calleeTrace post accepted unique parent dispatch selected budget succeeded.1
      exact ⟨sameSuccess, succeeded.2, verdict⟩


include caller sidecarSource parentTyped wellFormed runtime covers environments locals agrees typed admitted
  calleeTrace post tree unique parent selected in
/-- Consume static dispatch receipts only at the one actual closure post.
The existing prefix proofs handle both guards and the ordered children. -/
theorem resolve_closure (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {value : Value} {finalStore : Store}
    (receipt : CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site
      native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore calleeNative value finalStore) :
    ClosureResolution (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld) (calleeHeap := calleeHeap)
      (calleeStore := calleeStore) (calleeSize := calleeSize) (sourceTypes := sourceTypes)
      bridge profile compiler prepared initial dispatch budget value finalStore := by
  have resolution := resolve_closure_with_effects bridge profile compiler prepared parentTyped wellFormed runtime
    covers environments locals agrees typed initial admitted caller sidecarSource tree unique parent
    dispatch selected calleeTrace post budget children receipt
  rcases resolution with rejected | ⟨accepted, arguments⟩
  · exact Or.inl rejected
  · refine Or.inr ⟨accepted, ?_⟩
    exact arguments.elim Or.inl (fun succeeded => Or.inr ⟨succeeded.1, succeeded.2.2⟩)

/-- A produced value preserves one concrete callee post and a resolver whose
closure and attached-row inputs are indexed by precisely that same witness.
Existence of those static inputs remains a separate provenance obligation. -/
def ValuePrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before callee sourceValue after ∧
    CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge profile compiler initial sourceValue after carrier calleeStore finalMap finalWorld ∧
    CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore ∧
    ∀ (function : Dynamic.Closure), sourceValue = .closure function →
      ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
          (.closure function) carrier)
        (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
          compiler.original dispatch.row),
        ClosureResolution (registry := registry) (faults := faults) (context := context) (evidence := evidence)
          (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
          (calleeMap := finalMap) (calleeWorld := finalWorld) (calleeHeap := after)
          (calleeStore := calleeStore) (calleeSize := sourceSize) (sourceTypes := sourceTypes)
          bridge profile compiler prepared initial dispatch budget value finalStore


/-- A produced value preserves one concrete callee post and a resolver whose
closure and attached-row inputs are indexed by precisely that same witness.
The successful resolver retains its true intermediate argument effects.
Existence of those static inputs remains a separate provenance obligation. -/
def ValuePrefixWithEffects (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before callee sourceValue after ∧
    CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge profile compiler initial sourceValue after carrier calleeStore finalMap finalWorld ∧
    CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore ∧
    ∀ (function : Dynamic.Closure), sourceValue = .closure function →
      ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
          (.closure function) carrier)
        (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
          compiler.original dispatch.row),
        ClosureResolutionWithEffects (registry := registry) (faults := faults) (context := context) (evidence := evidence)
          (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
          (calleeMap := finalMap) (calleeWorld := finalWorld) (calleeHeap := after)
          (calleeStore := calleeStore) (calleeSize := sourceSize) (sourceTypes := sourceTypes)
          bridge profile compiler prepared initial dispatch budget value finalStore

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource tree unique parent in
/-- Reflect the whole native parent through its actual strict children. Callee
faults are closed internally; one successful post carries the finite resolver
for genuine closure/dispatch receipts, with no successful child premise. -/
theorem reflects_parent_with_effects (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (CallableIndexedOwnedStoredIndirectNativePrefix.FaultPrefix
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        bridge profile compiler initial budget value finalStore ∨
      ValuePrefixWithEffects (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
        (sourceTypes := sourceTypes) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) := by
  obtain ⟨sameCaller, sameSource, producedPrefix⟩ :=
    CallableIndexedOwnedStoredIndirectNativePrefix.reflects_prefix bridge profile compiler prepared certified found
      sourceTyped parentTyped wellFormed runtime covers environments heaps locals agrees typed initial admitted
      caller sidecarSource budget children completed within
  refine ⟨sameCaller, sameSource, ?_⟩
  rcases producedPrefix with failed | succeeded
  · exact Or.inl failed
  · right
    obtain ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate⟩ := succeeded
    refine ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, ?_⟩
    intro function sameClosure dispatch selected
    cases sameClosure
    exact resolve_closure_with_effects bridge profile compiler prepared parentTyped wellFormed runtime covers environments locals
      agrees typed initial admitted caller sidecarSource tree unique parent dispatch selected trace post budget children gate


include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource tree unique parent in
/-- Reflect the whole native parent through its actual strict children. Callee
faults are closed internally; one successful post carries the finite resolver
for genuine closure/dispatch receipts, with no successful child premise. -/
theorem reflects_parent (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (CallableIndexedOwnedStoredIndirectNativePrefix.FaultPrefix
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        bridge profile compiler initial budget value finalStore ∨
      ValuePrefix (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
        (sourceTypes := sourceTypes) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) := by
  obtain ⟨sameCaller, sameSource, producedPrefix⟩ := reflects_parent_with_effects bridge profile compiler prepared
    certified found sourceTyped parentTyped wellFormed runtime covers environments heaps locals agrees typed
    initial admitted caller sidecarSource tree unique parent budget children completed within
  refine ⟨sameCaller, sameSource, ?_⟩
  rcases producedPrefix with failed | succeeded
  · exact Or.inl failed
  · right
    obtain ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, resolver⟩ := succeeded
    refine ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, ?_⟩
    intro function sameClosure dispatch selected
    have resolution := resolver function sameClosure dispatch selected
    rcases resolution with rejected | ⟨accepted, arguments⟩
    · exact Or.inl rejected
    · refine Or.inr ⟨accepted, ?_⟩
      exact arguments.elim Or.inl (fun succeeded => Or.inr ⟨succeeded.1, succeeded.2.2⟩)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectParentPrefix
