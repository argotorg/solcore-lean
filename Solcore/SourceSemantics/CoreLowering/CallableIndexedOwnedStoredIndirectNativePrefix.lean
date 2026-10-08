import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageChildren

/-! Finite native prefix projection for the original two-guard call.
The first strict admitted child receives its actual generic outcome; its
result relation determines the Source/native value or fault annotations.
A successful child retains one real callee post and the second bind's actual
gate and remaining trace. A concrete Dispatch is consumed only at that post.
Semantic and stage faults remain distinct, and a passed guard retains the
original suffix grade for later argument/application inversion. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectNativePrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

section

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

/-- The exact suffix after the original first guard. Its measured grade is
retained whole for subsequent argument and application bind projections. -/
def suffix (site : SourceCoreCallableContracts.Callsite) (unknown : Word) (result : Ty)
    (arguments : Expr) : Expr :=
  LanguageResult.bind result ((arguments.weakenAt 0).weakenAt 0)
    (LanguageResult.bind result
      (CallableContract.dispatch site.gates .beforeApplication unknown (.second (.var 2)))
      (.apply (.second (.first (.var 3))) (.var 1)))

/-- The original second bind, with both its exact outcomes still generic.
No Dispatch is asserted to exist at an arbitrary child post. -/
inductive GatePrefix (budget : Nat) (site : SourceCoreCallableContracts.Callsite) (unknown : Word)
    (result : Ty) (arguments : Expr) (actual : Environment) (calleeStore : Store) (carrier : Value) :
    Value → Store → Prop where
  | failed {size : Nat} {input : Ty} {payload : Value} {after : Store}
      (gate : EvaluationSize size (carrier :: actual) calleeStore
        (CallableContract.dispatch site.gates .beforeArguments unknown (.second (.var 0)))
        (.inLeft input payload) after)
      (strict : size < budget) :
      GatePrefix budget site unknown result arguments actual calleeStore carrier (.inLeft result payload) after
  | passed {gateSize suffixSize : Nat} {input : Ty} {payload value : Value} {middle after : Store}
      (gate : EvaluationSize gateSize (carrier :: actual) calleeStore
        (CallableContract.dispatch site.gates .beforeArguments unknown (.second (.var 0)))
        (.inRight input payload) middle)
      (remaining : EvaluationSize suffixSize (payload :: carrier :: actual) middle
        (suffix site unknown result arguments) value after)
      (gateStrict : gateSize < budget) (suffixStrict : suffixSize < budget) :
      GatePrefix budget site unknown result arguments actual calleeStore carrier value after

/-- A concrete attached row at this one carrier fixes the exact gate verdict.
Acceptance retains the full original suffix trace and its strict grade. -/
theorem GatePrefix.resolve
    {budget : Nat} {site : SourceCoreCallableContracts.Callsite} {unknown : Word}
    {result : Ty} {arguments : Expr} {actual : Environment} {calleeStore finalStore : Store}
    {carrier value : Value} {frame : Staging.CallBoundary.Frame} {call : ExpressionId}
    {ids : List ExpressionId} {sourceValue : Dynamic.Value}
    (receipt : GatePrefix budget site unknown result arguments actual calleeStore carrier value finalStore)
    (dispatch : CallStageBoundary.Dispatch frame site call ids sourceValue carrier) :
    (∃ reason, Staging.CallBoundary.GuardRejects frame call ids sourceValue reason ∧
      value = .inLeft result (.word (dispatch.reason reason)) ∧ finalStore = calleeStore ∧
      CallStageBoundary.ReasonRepresents site reason (dispatch.reason reason)) ∨
    (Staging.CallBoundary.GuardAccepts frame call ids sourceValue ∧
      ∃ size, EvaluationSize size (.unit :: carrier :: actual) calleeStore
        (suffix site unknown result arguments) value finalStore ∧ size < budget) := by
  have read : Evaluates (carrier :: actual) calleeStore (.second (.var 0)) (.word dispatch.contract) calleeStore :=
    .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have original := site.dispatch_known .beforeArguments unknown dispatch.contract dispatch.row dispatch.found read
  cases receipt with
  | failed gate strict =>
    cases answer : dispatch.row.beforeArguments with
    | ok unitValue =>
      cases unitValue
      rw [SourceCoreCallableContracts.reason_accepted dispatch.row site.reasonAt .beforeArguments answer] at original
      have same := (evaluation_deterministic gate.sound original).1
      cases same
    | error diagnostic =>
      rw [SourceCoreCallableContracts.reason_rejected dispatch.row site.reasonAt .beforeArguments diagnostic answer] at original
      obtain ⟨same, stores⟩ := evaluation_deterministic gate.sound original
      cases same
      subst stores
      obtain ⟨reason, rejected, errorEq⟩ := dispatch.rejected_of_error diagnostic answer
      left
      refine ⟨reason, rejected, ?_, rfl, dispatch.reason_represents reason⟩
      simp only [CallStageBoundary.Dispatch.reason, errorEq]
  | passed gate remaining gateStrict suffixStrict =>
    cases answer : dispatch.row.beforeArguments with
    | ok unitValue =>
      cases unitValue
      rw [SourceCoreCallableContracts.reason_accepted dispatch.row site.reasonAt .beforeArguments answer] at original
      obtain ⟨same, stores⟩ := evaluation_deterministic gate.sound original
      cases same
      subst stores
      exact Or.inr ⟨dispatch.accepted_iff.mp answer, _, remaining, suffixStrict⟩
    | error diagnostic =>
      rw [SourceCoreCallableContracts.reason_rejected dispatch.row site.reasonAt .beforeArguments diagnostic answer] at original
      have same := (evaluation_deterministic gate.sound original).1
      cases same

end

namespace ForModel

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
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
    functionModel mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)

/-- A failed first child keeps its own Source grade and actual reached pool,
plus the genuine semanticFault parent. It precedes both stage guards. -/
def FaultPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize parentSize reason token after finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before callee reason after ∧
    Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
      context evidence source environment before id callee ids metadata (.semanticFault reason) after ∧
    RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) parentSize
      context evidence source environment before id (.fault reason) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults) (context := context)
      bridge functionModel compiler initial (.fault reason) after value finalStore finalMap finalWorld

/-- A successful first child retains exactly one Source/native post, its real
strict native child and the original second bind and remaining suffix. -/
def ValuePrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before callee sourceValue after ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge functionModel compiler initial sourceValue after carrier calleeStore finalMap finalWorld ∧
    GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource in
/-- Reflect the actual generic first child once. The original two finite bind
inversions expose either its semantic fault or the exact successful post and
second-bind receipt; no successful child evaluation is an endpoint premise. -/
theorem reflects_prefix (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (FaultPrefix (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        bridge functionModel compiler initial budget value finalStore ∨
      ValuePrefix (registry := registry) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
        bridge functionModel compiler prepared initial budget value finalStore) := by
  have full := completed
  rw [prepared.lowered_rename compiler ξ] at full
  refine ⟨caller, sidecarSource, ?_⟩
  cases CallableIndirectCallBounds.bind_completed full within with
  | failed child childStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
      children _ childStrict certified found sourceTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | @fault reason token matched =>
      cases trace with
      | fault failed =>
        have original : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram)
            (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [sourceSize]]) context evidence source environment
            before id (.fault reason) after := by
          refine .fault (.form (size_fault := SourceExecutionSize.stepSize [sourceSize]) (lookupExpression?_sound compiler.found) ?_)
          rw [compiler.originalForm]
          exact .indirectCallee failed
        have loweredType : lowered.type = compiler.resultType :=
          (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
        left
        refine ⟨_, sourceSize, _, reason, _, after, finalMap, finalWorld, child, childStrict,
          failed, .calleeFault failed.sound, original, ?_, ?_⟩
        · rw [loweredType]
        · rw [← loweredType]
          exact ⟨.fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related,
            after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped original frame⟩
  | continued child remaining childStrict remainingStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
      children _ childStrict certified found sourceTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | value represented =>
      cases trace with
      | value trace =>
        right
        refine ⟨_, sourceSize, _, after, _, _, finalMap, finalWorld, child, childStrict, trace,
          ⟨child.sound, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩, ?_⟩
        cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
        | failed gate gateStrict => exact .failed gate gateStrict
        | continued gate suffixTrace gateStrict suffixStrict => exact .passed gate suffixTrace gateStrict suffixStrict

variable {sourceValue : Dynamic.Value} {after : Dynamic.Heap} {carrier : Value} {calleeStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {sourceSize budget : Nat}
  (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
    context evidence source environment before callee sourceValue after)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge functionModel compiler initial sourceValue after carrier calleeStore finalMap finalWorld)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue carrier)

include caller sidecarSource post trace in
/-- At the single produced value post, an actual attached Dispatch resolves
the retained second bind. Rejection keeps the full staged result; acceptance
keeps the original remaining trace at the original strict budget. -/
theorem resolve_at_post {value : Value} {finalStore : Store}
    (receipt : GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore) :
    (∃ reason, value = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧
      CallableIndexedOwnedStoredIndirectStageBoundary.ForModel.ResultAt
        (registry := registry) (context := context) (evidence := evidence)
        (calleeNode := calleeNode) (mapping := finalMap) (world := finalWorld) (calleeHeap := after) (store := calleeStore)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := sourceSize)
        bridge functionModel compiler prepared initial dispatch reason (dispatch.reason reason) finalStore) ∨
    (Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids sourceValue ∧
      ∃ size, EvaluationSize size (.unit :: carrier :: actual) calleeStore
        (suffix prepared.site native.diagnostics.unknown compiler.resultType
          ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore ∧ size < budget) := by
  cases receipt.resolve dispatch with
  | inl rejected =>
    obtain ⟨reason, rejected, same, stores, _reasonRep⟩ := rejected
    subst finalStore
    exact Or.inl ⟨reason, same,
      CallableIndexedOwnedStoredIndirectStageBoundary.ForModel.preserves_rejected bridge functionModel compiler prepared initial post
        caller sidecarSource dispatch rejected trace⟩
  | inr accepted => exact Or.inr accepted

end ForModel

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

/-- A failed first child keeps its own Source grade and actual reached pool,
plus the genuine semanticFault parent. It precedes both stage guards. -/
def FaultPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize parentSize reason token after finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before callee reason after ∧
    Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
      context evidence source environment before id callee ids metadata (.semanticFault reason) after ∧
    RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) parentSize
      context evidence source environment before id (.fault reason) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
      bridge profile compiler initial (.fault reason) after value finalStore finalMap finalWorld

/-- A successful first child retains exactly one Source/native post, its real
strict native child and the original second bind and remaining suffix. -/
def ValuePrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before callee sourceValue after ∧
    CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge profile compiler initial sourceValue after carrier calleeStore finalMap finalWorld ∧
    GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource in
/-- Reflect the actual generic first child once. The original two finite bind
inversions expose either its semantic fault or the exact successful post and
second-bind receipt; no successful child evaluation is an endpoint premise. -/
theorem reflects_prefix (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (FaultPrefix (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        bridge profile compiler initial budget value finalStore ∨
      ValuePrefix (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
        bridge profile compiler prepared initial budget value finalStore) := by
  exact ForModel.reflects_prefix (functionModel := functions) (bridge := bridge) (compiler := compiler) (prepared := prepared) (certified := certified) (found := found) (sourceTyped := sourceTyped) (parentTyped := parentTyped) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted) (caller := caller) (sidecarSource := sidecarSource) (children := children) (completed := completed) (within := within) budget

variable {sourceValue : Dynamic.Value} {after : Dynamic.Heap} {carrier : Value} {calleeStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {sourceSize budget : Nat}
  (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
    context evidence source environment before callee sourceValue after)
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge profile compiler initial sourceValue after carrier calleeStore finalMap finalWorld)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue carrier)

include caller sidecarSource post trace in
/-- At the single produced value post, an actual attached Dispatch resolves
the retained second bind. Rejection keeps the full staged result; acceptance
keeps the original remaining trace at the original strict budget. -/
theorem resolve_at_post {value : Value} {finalStore : Store}
    (receipt : GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore) :
    (∃ reason, value = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧
      CallableIndexedOwnedStoredIndirectStageBoundary.ResultAt
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (calleeNode := calleeNode) (mapping := finalMap) (world := finalWorld) (calleeHeap := after) (store := calleeStore)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := sourceSize)
        bridge profile compiler prepared initial dispatch reason (dispatch.reason reason) finalStore) ∨
    (Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids sourceValue ∧
      ∃ size, EvaluationSize size (.unit :: carrier :: actual) calleeStore
        (suffix prepared.site native.diagnostics.unknown compiler.resultType
          ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore ∧ size < budget) := by
  exact ForModel.resolve_at_post (functionModel := functions) (bridge := bridge) (compiler := compiler) (prepared := prepared) (initial := initial) (trace := trace) (post := post) (dispatch := dispatch) (caller := caller) (sidecarSource := sidecarSource) receipt

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectNativePrefix
