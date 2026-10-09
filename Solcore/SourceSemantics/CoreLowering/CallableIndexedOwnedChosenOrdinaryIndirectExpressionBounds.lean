import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCalleePosts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectParentPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaExpressionHeads

/-! A strict child produces the actual callee post before any chosen route is
used. Genuine positive members can close the accepted parent at that same
post; prior and unclassified values remain in the original selection/prefix.
No whole callee, body or expression meaning is supplied to these ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryIndirectExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedChosenOrdinaryLambdaInvocation (ChosenFor)
open RecursiveNamedCatalogInvocationBounds (Below)
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
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)


variable
  {owning : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {rootCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed owning.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
    (compiled := compiled) owning.named diagnostics namedCode rootCompilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)


variable (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
  (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile) mapping world before store)


local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)

section Source
variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeSize : Nat}

/-- Only static route receipts, a genuine positive member and the actual Source
suffix are supplied after the strict child has produced this literal post. -/
def SourceAcceptedAt (outer budget : Nat) (calleeNative : Value) (_calleeStore : Store)
    (calleeMap : LocationMap) (calleeWorld : StoreTyping) : Prop :=
  ∀ (i : OrdinaryIndex compiled) (history : History i.code)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (_member : ChosenFor (headers := headers) root expressionSyntax owner i history),
    function = i.function → calleeMap = i.mapping → calleeWorld = i.world →
    calleeNative = value i.code i.captured.embedding history.native i.capturedActual →
    CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ModelRuntimeInputs
      (headers := headers) (registry := registry) (faults := faults) root expressionSyntax i owner functions →
    (∀ context, CallableIndexedOwnedChosenOrdinaryLambdaInvocation.Validity i context → RequirementIdsUnique context) →
    ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
        (.closure i.function) calleeNative),
    CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
      compiler.original dispatch.row →
    CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.AcceptedAt dispatch native.diagnostics.unknown →
    (∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner index)) →
    ∀ {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids i.function
      argumentsSize callSize outcome after → argumentsSize ≤ budget → callSize ≤ budget →
    ∃ sourceSize result finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      Evaluates actual store (lowered.expression.rename ξ) result finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge functions compiler initial outcome after result finalStore finalMap finalWorld

include certified found sourceTyped parentTyped runtime covers environments heaps locals agrees typed admitted
  tree unique parent actualFunctionType owners in
/-- Construct the callee post once from the actual strict child. Its complete
selection keeps prior alternatives. The positive accepted continuation derives
its own body and ordered argument producer through the existing parent core. -/
theorem preserves_closure_parent (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment before callee (.closure function) calleeHeap)
    (smaller : calleeSize < budget) :
    ∃ calleeNative calleeStore calleeMap calleeWorld,
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge functions compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld ∧
      CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := calleeMap) (world := calleeWorld) (raw := calleeNode.type)
        (function := function) (native := calleeNative) (type := compiler.calleeCode.type) root expressionSyntax ∧
      SourceAcceptedAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar) (function := function) (calleeHeap := calleeHeap)
        (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
        (compiler := compiler) (prepared := prepared) (initial := initial) outer budget calleeNative calleeStore calleeMap calleeWorld := by
  obtain ⟨calleeNative, calleeStore, calleeMap, calleeWorld, post, selection⟩ :=
    CallableIndexedOwnedChosenOrdinaryCalleePosts.source_closure_at_callee
      (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile) (compiler := compiler)
      (certified := certified) (found := found) (sourceTyped := sourceTyped) (environments := environments)
      (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
      budget children trace smaller
  refine ⟨calleeNative, calleeStore, calleeMap, calleeWorld, post, selection, ?_⟩
  intro i history owner member sameFunction sameMap sameWorld sameNative inputs bodyIds dispatch selected accepted ih
    argumentsSize callSize outcome after suffix argumentsWithin callWithin
  cases sameFunction
  cases sameMap
  cases sameWorld
  exact CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ForModel.preserves_accepted_for_model
    (receiving := functions)
    (members := CallableIndexedOwnedChosenOrdinaryLambdaExpressionHeads.members owning root expressionSyntax profile)
    (functionTypes := CallableIndexedOwnedChosenOrdinaryLambdaValues.runtime_views
      (root := root) (expressionSyntax := expressionSyntax) headers keys registry faults profile)
    (genericInputs := inputs) (genericPost := post) (root := root) (expressionSyntax := expressionSyntax)
    (i := i) (history := history) (profile := profile) (owner := owner) (member := member)
    (bridge := bridge) (compiler := compiler) (prepared := prepared) (initial := initial)
    (calleeTrace := trace) (sameNative := sameNative) (parentTyped := parentTyped) (tree := tree)
    (unique := unique) (parent := parent) (runtime := runtime) (covers := covers) (locals := locals)
    (admitted := admitted) (actualFunctionType := actualFunctionType) (dispatch := dispatch)
    (selected := selected) (accepted := accepted) (owners := owners) (idsUnique := bodyIds)
    (environments := environments) (agrees := agrees) (typed := typed)
    outer budget within ih children suffix argumentsWithin callWithin

include prepared certified found sourceTyped parentTyped wellFormed runtime covers environments heaps locals agrees typed admitted in
/-- A genuine strict callee fault closes the semantic parent before arguments.
It requires no selected positive member or callable body receipt. -/
theorem preserves_fault_parent (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (failed : SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment before callee reason after)
    (smaller : calleeSize < budget) :
    ∃ sourceSize token finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id (.fault reason) after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge functions compiler initial (.fault reason) after
        (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld :=
  CallableIndexedOwnedChosenOrdinaryCalleePosts.source_fault_at_callee
    (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
    (compiler := compiler) (prepared := prepared) (certified := certified) (found := found)
    (sourceTyped := sourceTyped) (parentTyped := parentTyped) (wellFormed := wellFormed)
    (runtime := runtime) (covers := covers) (environments := environments) (heaps := heaps)
    (locals := locals) (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    budget children failed smaller

end Source

section Native
variable {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}

/-- Original stage, argument and arity failures remain explicit. The accepted
positive branch now retains the completed body and actual full parent result. -/
def NativeChosenResult (i : OrdinaryIndex compiled)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
      (.closure i.function) calleeNative)
    (budget : Nat) (result : Value) (finalStore : Store) : Prop :=
  (∃ reason, result = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧
    CallableIndexedOwnedStoredIndirectStageBoundary.ForModel.ResultAt
      (registry := registry) (context := context) (evidence := evidence) (calleeNode := calleeNode)
      (mapping := i.mapping) (world := i.world) (calleeHeap := calleeHeap) (store := calleeStore)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize)
      bridge functions compiler prepared initial dispatch reason (dispatch.reason reason) finalStore) ∨
  CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.FaultPrefix
    (registry := registry) (faults := faults) (context := context) (evidence := evidence)
    (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
    (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
    bridge functions compiler initial budget result finalStore ∨
  CallableIndexedOwnedStoredIndirectApplicationPrefix.ForModel.RejectedAt
    (registry := registry) (faults := faults) (context := context) (evidence := evidence)
    (environment := environment) (sidecar := sidecar)
    bridge functions compiler prepared initial dispatch result finalStore ∨
  CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ForModel.ReflectedResultAt
    (receiving := functions) (registry := registry) (faults := faults) (context := context) (evidence := evidence)
    (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
    (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
    i bridge compiler prepared initial dispatch budget result finalStore

/-- This is a finite static resolver at the actual callee tuple. It receives no
successful argument or application trace: the whole parent prefix derives both. -/
def NativeAcceptedAt (function : Dynamic.Closure) (outer budget : Nat)
    (calleeNative : Value) (calleeStore : Store) (calleeMap : LocationMap) (calleeWorld : StoreTyping)
    (result : Value) (finalStore : Store) : Prop :=
  ∀ (i : OrdinaryIndex compiled) (history : History i.code)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (_member : ChosenFor (headers := headers) root expressionSyntax owner i history),
    function = i.function → calleeMap = i.mapping → calleeWorld = i.world →
    calleeNative = value i.code i.captured.embedding history.native i.capturedActual →
    CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ModelRuntimeInputs
      (headers := headers) (registry := registry) (faults := faults) root expressionSyntax i owner functions →
    ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
        (.closure i.function) calleeNative),
    CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
      compiler.original dispatch.row →
    CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.AcceptedAt dispatch native.diagnostics.unknown →
    (∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner index)) →
    NativeChosenResult (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
      (sidecar := sidecar) (sourceTypes := sourceTypes) (calleeHeap := calleeHeap) (calleeStore := calleeStore)
      (calleeNative := calleeNative) (calleeSize := calleeSize)
      (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
      (compiler := compiler) (prepared := prepared) (initial := initial) i dispatch budget result finalStore

include certified found sourceTyped parentTyped wellFormed runtime covers environments heaps locals agrees typed admitted
  caller sidecarSource tree unique parent actualFunctionType in
/-- The original native parent prefix invokes the strict callee child once.
Its actual value retains all alternatives; only a genuine positive receipt at
that same tuple can enter the accepted body resolver. -/
theorem reflects_parent (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) result finalStore)
    (bounded : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (CallableIndexedOwnedStoredIndirectNativePrefix.ForModel.FaultPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
      bridge functions compiler initial budget result finalStore ∨
    ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
      EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      nativeSize < budget ∧
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize context evidence
        source environment before callee sourceValue after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge functions compiler initial sourceValue after carrier calleeStore finalMap finalWorld ∧
      CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier result finalStore ∧
      ∀ function, sourceValue = .closure function →
        CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
          (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          (mapping := finalMap) (world := finalWorld) (raw := calleeNode.type)
          (function := function) (native := carrier) (type := compiler.calleeCode.type) root expressionSyntax ∧
        NativeAcceptedAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
          (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
          (sidecar := sidecar) (sourceTypes := sourceTypes) (calleeHeap := after) (calleeSize := sourceSize)
          (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
          (compiler := compiler) (prepared := prepared) (initial := initial)
          function outer budget carrier calleeStore finalMap finalWorld result finalStore) := by
  obtain ⟨sameCaller, sameSource, producedPrefix⟩ :=
    CallableIndexedOwnedStoredIndirectParentPrefix.ForModel.reflects_parent_with_effects
      (bridge := bridge) (functionModel := functions) (compiler := compiler) (prepared := prepared)
      (certified := certified) (found := found) (sourceTyped := sourceTyped) (parentTyped := parentTyped)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (environments := environments)
      (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed) (initial := initial)
      (admitted := admitted) (caller := caller) (sidecarSource := sidecarSource)
      (tree := tree) (unique := unique) (parent := parent) budget children completed bounded
  refine ⟨sameCaller, sameSource, ?_⟩
  rcases producedPrefix with failed | succeeded
  · exact Or.inl failed
  · right
    obtain ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, resolve⟩ := succeeded
    refine ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, ?_⟩
    intro function sameClosure
    cases sameClosure
    refine ⟨CallableIndexedOwnedChosenOrdinaryCalleePosts.selected_at_value_post
      (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
      (compiler := compiler) (initial := initial) post, ?_⟩
    intro i history owner member sameFunction sameMap sameWorld sameNative inputs dispatch selected accepted ih
    cases sameFunction
    cases sameMap
    cases sameWorld
    rcases resolve i.function rfl dispatch selected with rejected | ⟨_stage, arguments⟩
    · exact Or.inl rejected
    · rcases arguments with failed | ⟨original, step, rejected | passed⟩
      · exact Or.inr (Or.inl failed)
      · exact Or.inr (Or.inr (Or.inl rejected))
      · right; right; right
        exact CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ForModel.reflects_accepted_for_model
          (receiving := functions)
          (members := CallableIndexedOwnedChosenOrdinaryLambdaExpressionHeads.members owning root expressionSyntax profile)
          (functionTypes := CallableIndexedOwnedChosenOrdinaryLambdaValues.runtime_views
            (root := root) (expressionSyntax := expressionSyntax) headers keys registry faults profile)
          (genericInputs := inputs) (genericPost := post) (root := root) (expressionSyntax := expressionSyntax)
          (i := i) (history := history) (profile := profile) (owner := owner) (member := member)
          (bridge := bridge) (compiler := compiler) (prepared := prepared) (initial := initial)
          (calleeTrace := trace) (sameNative := sameNative) (parentTyped := parentTyped) (tree := tree)
          (unique := unique) (parent := parent) (runtime := runtime) (covers := covers) (locals := locals)
          (admitted := admitted) (actualFunctionType := actualFunctionType) (dispatch := dispatch)
          (accepted := accepted) outer budget within ih original step passed

end Native
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryIndirectExpressionBounds
