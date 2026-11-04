import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectCalls
import Solcore.SourceSemantics.CoreLowering.CallableFaultDiagnosticPreparation
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures

/-!
# Owned callables: stored indirect application

Application of stored closures: prefixes, stage children, arity boundaries and accepted site application.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageChildren
/-! Strict callee IH constructs one actual successful post internally. Only
that produced witness accepts its genuine attached Dispatch and GuardRejects;
no classifier or law promising those static receipts for arbitrary posts is
supplied. Native reflection consumes the actual strict callee child receipt,
then the original two-bind boundary retains the full parent budget. Callee
semantic faults remain a separate genuine staged outcome at their own post. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageChildren
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

include certified found sourceTyped environments heaps locals agrees typed admitted caller sidecarSource in
/-- The Source child IH produces one real post; concrete dispatch evidence is
consumed only at that single produced carrier. It is never manufactured. -/
theorem preserves_child (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee sourceValue after)
    (smaller : size < budget) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge profile compiler initial sourceValue after value finalStore finalMap finalWorld ∧
      ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
          prepared.site prepared.site.call ids sourceValue value)
        (reason : Staging.CallGuard.Fault),
        Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) prepared.site.call ids sourceValue reason →
        CallableIndexedOwnedStoredIndirectStageBoundary.ResultAt
          (registry := registry) (faults := faults) (context := context) (evidence := evidence)
          (calleeNode := calleeNode) (mapping := finalMap) (world := finalWorld) (calleeHeap := after) (store := finalStore)
          (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := size)
          bridge profile compiler prepared initial dispatch reason (dispatch.reason reason) finalStore := by
  obtain ⟨value, finalStore, finalMap, finalWorld, post⟩ :=
    CallableIndexedOwnedStoredIndirectCalleePost.preserves_value bridge profile compiler certified found sourceTyped
      environments heaps locals agrees typed initial admitted budget children trace smaller
  refine ⟨value, finalStore, finalMap, finalWorld, post, ?_⟩
  intro dispatch reason rejected
  exact CallableIndexedOwnedStoredIndirectStageBoundary.preserves_rejected bridge profile compiler prepared initial post
    caller sidecarSource dispatch rejected trace

include certified found sourceTyped environments heaps locals agrees typed admitted caller sidecarSource in
/-- Reflection derives the independent Source callee grade and actual post
from the real strict native child. A genuine rejected receipt at that witness
then uses the full original parent completion, including its real budget. -/
theorem reflects_child (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {calleeSize size : Nat} {value calleeNative : Value} {calleeStore finalStore : Store}
    (child : EvaluationSize calleeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word calleeNative) calleeStore)
    (childStrict : calleeSize < budget)
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize sourceValue after finalMap finalWorld,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before callee sourceValue after ∧
      CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge profile compiler initial sourceValue after calleeNative calleeStore finalMap finalWorld ∧
      ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
          prepared.site prepared.site.call ids sourceValue calleeNative)
        (reason : Staging.CallGuard.Fault),
        Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) prepared.site.call ids sourceValue reason →
        ∃ token, value = .inLeft compiler.resultType (.word token) ∧
          CallableIndexedOwnedStoredIndirectStageBoundary.ResultAt
            (registry := registry) (faults := faults) (context := context) (evidence := evidence)
            (calleeNode := calleeNode) (mapping := finalMap) (world := finalWorld) (calleeHeap := after) (store := calleeStore)
            (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := sourceSize)
            bridge profile compiler prepared initial dispatch reason token finalStore ∧
          CallableIndexedOwnedStoredIndirectStageBoundary.RejectedCompletion budget prepared.site native.diagnostics.unknown
            (compiler.calleeCode.expression.rename ξ) actual store calleeStore calleeNative token := by
  obtain ⟨sourceSize, sourceValue, after, finalMap, finalWorld, trace, post⟩ :=
    CallableIndexedOwnedStoredIndirectCalleePost.reflects_value bridge profile compiler certified found sourceTyped
      environments heaps locals agrees typed initial admitted budget children child childStrict
  refine ⟨sourceSize, sourceValue, after, finalMap, finalWorld, trace, post, ?_⟩
  intro dispatch reason rejected
  exact CallableIndexedOwnedStoredIndirectStageBoundary.reflects_rejected bridge profile compiler prepared initial post
    caller sidecarSource dispatch rejected trace budget completed within

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource in
/-- A Source callee fault invokes only its strict child and remains the genuine
semanticFault alternative of Staging.CallBoundary at that same reached heap. -/
theorem preserves_callee_fault (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (fault : SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee reason after)
    (smaller : size < budget) :
    ∃ sourceSize token finalStore finalMap finalWorld,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
      sidecar.source = source ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata (.semanticFault reason) after ∧
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id (.fault reason) after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler initial (.fault reason) after (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, token, finalStore, finalMap, finalWorld, original, evaluated, post⟩ :=
    CallableIndexedOwnedStoredIndirectCalleePost.preserves_fault bridge profile compiler prepared certified found sourceTyped
      parentTyped wellFormed runtime covers environments heaps locals agrees typed initial admitted budget children fault smaller
  exact ⟨sourceSize, token, finalStore, finalMap, finalWorld, caller, sidecarSource, .calleeFault fault.sound, original, evaluated, post⟩


include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource in
/-- Native callee failure reflects only its real strict child, before either
guard. Its raw Source child grade and enclosing Source grade are independent
of native size; the same child pool supplies the actual parent admission. -/
theorem reflects_callee_fault (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {token : Word} {finalStore : Store}
    (completed : EvaluationSize size actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore)
    (smaller : size < budget) :
    ∃ childSourceSize parentSourceSize reason after finalMap finalWorld,
      SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) childSourceSize
        context evidence source environment before callee reason after ∧
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
      sidecar.source = source ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata (.semanticFault reason) after ∧
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) parentSourceSize
        context evidence source environment before id (.fault reason) after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler initial (.fault reason) after (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    children size smaller certified found sourceTyped environments heaps locals agrees typed initial admitted completed
  cases represented with
  | fault matched =>
    rename_i reason
    cases trace with
    | fault failed =>
      have original : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram)
          (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [sourceSize]]) context evidence source environment
          before id (.fault reason) after := by
        refine .fault (.form (size_fault := SourceExecutionSize.stepSize [sourceSize]) (lookupExpression?_sound compiler.found) ?_)
        rw [compiler.originalForm]
        exact .indirectCallee failed
      have whole := CallableContract.call_callee_failure (result := compiler.resultType)
        (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
        prepared.site.gates native.diagnostics.unknown completed.sound
      rw [← prepared.lowered_rename compiler ξ] at whole
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      rw [← loweredType] at whole
      exact ⟨sourceSize, _, _, after, finalMap, finalWorld, failed, caller, sidecarSource,
        .calleeFault failed.sound, original, whole, .fault matched, finalHeaps, maps, worlds, frame, metadata,
        reached, related, after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped original frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageChildren
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectNativePrefix
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectSuccessStep
/-! The exact successful ordered argument witness keeps both the actual
callee-to-argument map/world effects and the cumulative caller effects. Its
complete fourth-bind trace and strict grade remain attached to that same
argument store. This receipt adds no execution producer or classifier. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectSuccessStep
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

variable {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value} {sourceValue : Dynamic.Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  {sourceTypes : List TypeSystem.Ty}

/-- The actual intermediate effects are retained beside the complete argument
post and entire original fourth-bind receipt. No cumulative extension is
inverted to reconstruct them. -/
def SuccessStep (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sources values after argumentStore finalMap finalWorld,
    EvaluationSize nativeSize (.unit :: calleeNative :: actual) calleeStore
      ((((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0).weakenAt 0)
      (.inRight .word (DataPatternValues.packValues values)) argumentStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment calleeHeap ids sources after ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after argumentStore ∧
    LocationMap.Extends calleeMap finalMap ∧ WorldExtends calleeWorld finalWorld ∧
    AdministrativePreserved calleeMap calleeStore finalMap argumentStore ∧ Dynamic.HeapMetadataExtend calleeHeap after ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentStore ∧ Dynamic.HeapMetadataExtend before after ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, argumentStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
    (∃ remainingSize,
      EvaluationSize remainingSize (DataPatternValues.packValues values :: .unit :: calleeNative :: actual) argumentStore
        (LanguageResult.bind compiler.resultType
          (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
          (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧
      remainingSize < budget)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectSuccessStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectArgumentPrefix
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

variable {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value} {sourceValue : Dynamic.Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee sourceValue calleeHeap)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge functionModel compiler initial sourceValue calleeHeap calleeNative calleeStore calleeMap calleeWorld)
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
    CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults) (context := context)
      bridge functionModel compiler initial (.fault reason) after value finalStore finalMap finalWorld

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
        bridge functionModel compiler initial budget value finalStore ∨
      (SuccessPrefix (registry := registry) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
        (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
        bridge functionModel compiler prepared initial budget value finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep (registry := registry)
        (context := context) (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
        (sourceTypes := sourceTypes) (calleeHeap := calleeHeap) (calleeNative := calleeNative)
        (calleeStore := calleeStore) (calleeMap := calleeMap) (calleeWorld := calleeWorld)
        bridge functionModel compiler prepared initial budget value finalStore)) := by
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
  exact ForModel.reflects_suffix_with_effects (functionModel := functions) (bridge := bridge) (compiler := compiler) (prepared := prepared) (parentTyped := parentTyped) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (environments := environments) (locals := locals) (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted) (caller := caller) (sidecarSource := sidecarSource) (calleeTrace := calleeTrace) (post := post) (accepted := accepted) (tree := tree) (unique := unique) (children := children) (completed := completed) (smaller := smaller) budget


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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityBoundary
/-! Closure arity rejection uses the actual successful callee post and ordered
argument children. The selected Generated row and original Source contract
supply physical counts; packed types supply no count. No body is invoked and
no legacy captured prefix is strengthened. The accepted first stage remains
independent. Reflection also retains an earlier argument fault at its real post.
The second-gate token carries its exact RuntimeError and phase. Interpreting it
through the actual diagnostic table is a separate static receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityBoundary
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedIndirectExpressionHeads
universe u

section Selected
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {function : Dynamic.Closure} {native : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call ids (.closure function) native)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata node dispatch.row)

include selected in
/-- The real closure binding identifies the selected ledger's physical count. -/
theorem parameter_count : dispatch.row.entry.parameterCount = function.parameters.length := by
  have retained := CallableIndexedOwnedStoredIndirectCallBounds.selected_contract dispatch selected
  cases dispatch.bound with
  | closure parameters _ =>
    exact (selected.parameter_count retained).trans (congrArg List.length parameters)

include selected in
/-- This is the original second-gate error, with both actual physical counts. -/
theorem rejected_row (different : function.parameters.length ≠ ids.length) :
    dispatch.row.afterArguments = .error (.argumentArityMismatch function.parameters.length ids.length) := by
  have parameters := parameter_count dispatch selected
  have arguments := selected.argument_count
  have mismatch : dispatch.row.entry.parameterCount ≠ dispatch.row.argumentCount := by
    rw [parameters, arguments]
    exact different
  simpa only [parameters, arguments] using dispatch.row.afterArguments_mismatch mismatch

include selected in
/-- Source count rejection closes only the second decision, at its real phase. -/
theorem rejected_gate (different : function.parameters.length ≠ ids.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown dispatch.contract =
      some (site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeApplication
        (.argumentArityMismatch function.parameters.length ids.length)) := by
  rw [site.decision_known .beforeApplication unknown dispatch.contract dispatch.row dispatch.found]
  exact SourceCoreCallableContracts.reason_rejected dispatch.row site.reasonAt .beforeApplication _
    (rejected_row dispatch selected different)
end Selected

section Completion
variable {actual : Environment} {store calleeStore : Store} {native : Value} {token : Word}

/-- The existing third and fourth binds retain the actual argument completion.
An argument fault precedes the pure arity error and keeps its own post. -/
inductive Completion (budget : Nat) (resultType : Ty) (arguments : Expr) : Value → Store → Prop where
  | failed {size : Nat} {input : Ty} {fault : Value} {after : Store}
      (argumentsTrace : EvaluationSize size (.unit :: native :: actual) calleeStore
        ((arguments.weakenAt 0).weakenAt 0) (.inLeft input fault) after)
      (strict : size < budget) : Completion budget resultType arguments (.inLeft resultType fault) after
  | rejected {size : Nat} {input : Ty} {argument : Value} {after : Store}
      (argumentsTrace : EvaluationSize size (.unit :: native :: actual) calleeStore
        ((arguments.weakenAt 0).weakenAt 0) (.inRight input argument) after)
      (strict : size < budget) : Completion budget resultType arguments (.inLeft resultType (.word token)) after

private theorem second_read {environment : Environment} {before : Store} {payload : Value}
    {word : Word} {index : Nat} (shape : native = .pair payload (.word word))
    (found : environment[index]? = some native) :
    Evaluates environment before (.second (.var index)) (.word word) before :=
  .second (.var (found.trans (congrArg some shape)))

/-- Only finite original bind inversions and actual pure gate evaluations are
used. The callee's effectful store is the argument computation's real input. -/
theorem completed {budget size : Nat} {resultType : Ty} {callee arguments : Expr}
    {gates : List CallableContract.Gate} {unknown word : Word} {payload result : Value} {after : Store}
    (shape : native = .pair payload (.word word))
    (calleeTrace : Evaluates actual store callee (.inRight .word native) calleeStore)
    (stage : CallableContract.decision gates .beforeArguments unknown word = none)
    (arity : CallableContract.decision gates .beforeApplication unknown word = some token)
    (trace : EvaluationSize size actual store (CallableContract.call gates unknown resultType callee arguments) result after)
    (within : size ≤ budget) :
    Completion (actual := actual) (calleeStore := calleeStore) (native := native) (token := token)
      budget resultType arguments result after := by
  have descriptor : Evaluates (native :: actual) calleeStore (.second (.var 0)) (.word word) calleeStore :=
    second_read (index := 0) shape rfl
  cases CallableIndirectCallBounds.bind_completed trace within with
  | failed first _ =>
    obtain ⟨same, _⟩ := evaluation_deterministic first.sound calleeTrace
    cases same
  | continued first remaining _ remainingStrict =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic first.sound calleeTrace
    cases same
    cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
    | failed gate _ =>
      obtain ⟨same, _⟩ := CallableIndirectCallBounds.dispatch_decision descriptor gate
      simp only [stage, CallableContract.resultValue] at same
      cases same
    | continued gate remaining _ remainingStrict =>
      obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision descriptor gate
      simp only [stage, CallableContract.resultValue] at same
      cases same
      cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
      | failed argumentsTrace smaller => exact .failed argumentsTrace smaller
      | continued argumentsTrace remaining smaller remainingStrict =>
        cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
        | failed gate _ =>
          obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision
            (second_read (index := 2) shape rfl) gate
          simp only [arity, CallableContract.resultValue] at same
          cases same
          exact .rejected argumentsTrace smaller
        | continued gate _ _ _ =>
          obtain ⟨same, _⟩ := CallableIndirectCallBounds.dispatch_decision
            (second_read (index := 2) shape rfl) gate
          simp only [arity, CallableContract.resultValue] at same
          cases same
end Completion

section Boundary
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
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
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
  {function : Dynamic.Closure} {calleeNative : Value}
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge profile compiler first
    (.closure function) calleeHeap calleeNative store mapping world)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  (different : function.parameters.length ≠ ids.length)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "arityToken" => prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
  CallableContract.Phase.beforeApplication (SourceTypedRuntime.RuntimeError.argumentArityMismatch function.parameters.length ids.length)

/-- Ordinary child faults keep their original relation. Arity rejection retains
its exact selected RuntimeError and token without assuming a table decoder law. -/
def FaultToken (reason : Dynamic.SemanticFault) (token : Word) : Prop :=
  faults reason token ∨ reason = .argumentArityMismatch function.parameters.length ids.length ∧ token = arityToken

/-- Both fault alternatives retain the same complete actual argument post.
Deep Source heap admission is not asserted for the enclosing fault. -/
def ResultAt (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) (token : Word) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  FaultToken (faults := faults) compiler prepared dispatch reason token ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧ PostAdmission bridge context compiler.original.type (.fault reason) reached

include stages caller sidecarSource unique in
private theorem actual_selected :
    CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row := by
  have contains : ContainsExpression sidecar.source prepared.site.call compiler.original := by
    rw [sidecarSource, prepared.call]
    exact lookupExpression?_sound compiler.found
  exact CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages prepared.table caller
    contains compiler.originalForm (sidecarSource ▸ unique) dispatch.found

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  post stages caller sidecarSource dispatch accepted different calleeTrace in
/-- Actual successful Source arguments produce the real arity fault and raw
selected token. No callable body, strong origin or captured-prefix law is used. -/
theorem preserves_arity (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {argumentsSize : Nat} {arguments : List Dynamic.Value} {after : Dynamic.Heap}
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      context evidence source environment calleeHeap ids arguments after)
    (within : argumentsSize ≤ budget) :
    ∃ sourceSize finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id (.fault (.argumentArityMismatch function.parameters.length ids.length)) after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) (.inLeft lowered.type (.word arityToken)) finalStore ∧
      ResultAt (registry := registry) (faults := faults) (context := context) bridge profile compiler prepared first dispatch
        (.argumentArityMismatch function.parameters.length ids.length) after arityToken finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, represented, heaps, maps, worlds, frame, calleeMetadata, calleeState, related, calleePost⟩ := post
  have calleeAdmission := calleePost.at_value.2
  obtain ⟨parameter, sourceResult, rawTypes, _calleeTyping, argumentsTyping, application⟩ :=
    CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts unique compiler.found compiler.originalForm parentTyped
  have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
  have argumentsCount := arguments_count_of_source_admission wellFormed runtime covers (locals.mono calleeMetadata)
    calleeAdmission.heap argumentsTyping count argumentsTrace
  have actualCount : arguments.length = ids.length := argumentsCount.trans parent.arity.symm
  have rejected : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) (SourceExecutionSize.stepSize [])
      context evidence function.evidence after (.closure function) arguments
      (.fault (.argumentArityMismatch function.parameters.length ids.length)) after := by
    rw [← actualCount]
    exact .fault (.closureArity (actualCount.symm ▸ different))
  obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
    compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeAdmission.heap
    argumentsTyping count calleeTrace (SourceSuffix.called argumentsTrace rejected)
  have selected := actual_selected compiler prepared unique stages caller sidecarSource dispatch
  obtain ⟨payloads, finalStore, finalMap, finalWorld, evaluated, _values, finalHeaps, lastMaps, lastWorlds,
      lastFrame, lastMetadata, reached, lastRelated, _argumentAdmission⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.preserves_values_bounded bridge budget tree unique argumentsTyping children
      (environments.extend maps worlds) heaps (locals.mono calleeMetadata)
      (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit)
      (.cons .unit (.cons represented.runtime_hasType (typed.weaken worlds)))
      calleeState calleeAdmission argumentsTrace within
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at evaluated
  rw [dispatch.shape] at calleeEvaluation evaluated
  have whole := prepared.site.lower_arity_failure (result := compiler.resultType) native.diagnostics.unknown dispatch.row _ dispatch.found
    (dispatch.accepted accepted) (rejected_row dispatch selected different) calleeEvaluation evaluated
  dsimp only [SourceCoreCallableContracts.Callsite.lower] at whole
  rw [← prepared.lowered_rename compiler ξ] at whole
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  rw [← loweredType] at whole
  exact ⟨sourceSize, finalStore, finalMap, finalWorld, original, whole, Or.inr ⟨rfl, rfl⟩,
    finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, calleeMetadata.trans lastMetadata,
    reached, callerProtocol.trans related lastRelated,
    after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (frame.trans lastFrame)⟩

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  post stages caller sidecarSource dispatch accepted different calleeTrace in
/-- Native reflection retains either the earlier actual argument fault or the
true closure arity rejection. The original binds supply the strict child grade;
Source reconstruction has its own independent grade and exact argument post. -/
theorem reflects_boundary (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (evaluation : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize reason after token finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id (.fault reason) after ∧ value = .inLeft lowered.type (.word token) ∧
      ResultAt (registry := registry) (faults := faults) (context := context) bridge profile compiler prepared first dispatch
        reason after token finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, represented, heaps, maps, worlds, frame, calleeMetadata, calleeState, related, calleePost⟩ := post
  have calleeAdmission := calleePost.at_value.2
  obtain ⟨parameter, sourceResult, rawTypes, _calleeTyping, argumentsTyping, application⟩ :=
    CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts unique compiler.found compiler.originalForm parentTyped
  have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
  have selected := actual_selected compiler prepared unique stages caller sidecarSource dispatch
  have stage := CallableIndexedOwnedSelectedCallStageAcceptance.before_arguments dispatch accepted native.diagnostics.unknown
  have arity := rejected_gate dispatch selected different native.diagnostics.unknown
  rw [prepared.lowered_rename compiler ξ] at evaluation
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons represented.runtime_hasType (typed.weaken worlds))
  cases completed dispatch.shape calleeEvaluation stage arity evaluation within with
  | failed argumentsTrace smaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        lastMaps, lastWorlds, lastFrame, lastMetadata, reached, lastRelated, _argumentPost⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend maps worlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | fault matched =>
      cases trace with
      | fault failed =>
        obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeAdmission.heap
          argumentsTyping count calleeTrace (SourceSuffix.argumentFault failed)
        exact ⟨sourceSize, _, after, _, finalMap, finalWorld, original, by rw [loweredType], Or.inl matched,
          finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, calleeMetadata.trans lastMetadata,
          reached, callerProtocol.trans related lastRelated,
          after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (frame.trans lastFrame)⟩
  | rejected argumentsTrace smaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        lastMaps, lastWorlds, lastFrame, lastMetadata, reached, lastRelated, _argumentPost⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend maps worlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | @values sources values _values =>
      cases trace with
      | values sourceArguments =>
        have argumentsCount := arguments_count_of_source_admission wellFormed runtime covers (locals.mono calleeMetadata)
          calleeAdmission.heap argumentsTyping count sourceArguments
        have actualCount : _ = ids.length := argumentsCount.trans parent.arity.symm
        have rejected : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) (SourceExecutionSize.stepSize [])
            context evidence function.evidence after (.closure function) sources
            (.fault (.argumentArityMismatch function.parameters.length ids.length)) after := by
          rw [← actualCount]
          exact .fault (.closureArity (actualCount.symm ▸ different))
        obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeAdmission.heap
          argumentsTyping count calleeTrace (SourceSuffix.called sourceArguments rejected)
        exact ⟨sourceSize, _, after, arityToken, finalMap, finalWorld, original, by rw [loweredType], Or.inr ⟨rfl, rfl⟩,
          finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, calleeMetadata.trans lastMetadata,
          reached, callerProtocol.trans related lastRelated,
          after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (frame.trans lastFrame)⟩
end Boundary
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityBoundary
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectApplicationPrefix
/-! Resolve the actual fourth guard using the same selected row's physical
closure and argument counts. The original full fourth-bind receipt remains
beside its strict application projection. Source arity rejection uses the
actual ordered Source trace and its real reached pool; packed types supply no
count or stage verdict. No callable body is invoked by this finite boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectApplicationPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

section Gate
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {function : Dynamic.Closure} {carrier : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call ids (.closure function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata node dispatch.row)

include selected in
/-- The selected row's accepted verdict uses genuine physical counts. -/
theorem accepted_row (same : function.parameters.length = ids.length) : dispatch.row.afterArguments = .ok () := by
  apply dispatch.row.afterArguments_ok
  rw [CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected, selected.argument_count]
  exact same

include selected in
/-- Concrete dispatch at the actual callee fixes only this actual fourth gate.
The passed branch exposes the original application trace and strict bound. -/
theorem resolve_application
    {budget : Nat} {unknown : Word} {result : Ty} {actual : Environment}
    {argumentStore finalStore : Store} {packed value : Value}
    (receipt : CallableIndexedOwnedStoredIndirectArgumentPrefix.ApplicationPrefix
      budget site unknown result actual argumentStore carrier packed value finalStore) :
    (function.parameters.length ≠ ids.length ∧
      dispatch.row.afterArguments = .error (.argumentArityMismatch function.parameters.length ids.length) ∧
      value = .inLeft result (.word (site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
        .beforeApplication (.argumentArityMismatch function.parameters.length ids.length))) ∧
      finalStore = argumentStore) ∨
    (function.parameters.length = ids.length ∧ dispatch.row.afterArguments = .ok () ∧
      ∃ size, EvaluationSize size (.unit :: packed :: .unit :: carrier :: actual) argumentStore
        (.apply (.second (.first (.var 3))) (.var 1)) value finalStore ∧ size < budget) := by
  have read : Evaluates (packed :: .unit :: carrier :: actual) argumentStore (.second (.var 2))
      (.word dispatch.contract) argumentStore :=
    .second (.var (by simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have original := site.dispatch_known .beforeApplication unknown dispatch.contract dispatch.row dispatch.found read
  by_cases sameCount : function.parameters.length = ids.length
  · have answer := accepted_row dispatch selected sameCount
    rw [SourceCoreCallableContracts.reason_accepted dispatch.row site.reasonAt .beforeApplication answer] at original
    cases receipt with
    | failed gate strict =>
      have same := (evaluation_deterministic gate.sound original).1
      cases same
    | passed gate application gateStrict applicationStrict =>
      obtain ⟨same, stores⟩ := evaluation_deterministic gate.sound original
      cases same
      subst stores
      exact Or.inr ⟨sameCount, answer, _, application, applicationStrict⟩
  · have answer := CallableIndexedOwnedStoredClosureArityBoundary.rejected_row dispatch selected sameCount
    rw [SourceCoreCallableContracts.reason_rejected dispatch.row site.reasonAt .beforeApplication _ answer] at original
    cases receipt with
    | failed gate strict =>
      obtain ⟨same, stores⟩ := evaluation_deterministic gate.sound original
      cases same
      exact Or.inl ⟨sameCount, answer, rfl, stores⟩
    | passed gate application gateStrict applicationStrict =>
      have same := (evaluation_deterministic gate.sound original).1
      cases same
end Gate

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

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge profile compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {sourceTypes : List TypeSystem.Ty}
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)

local notation "arityToken" => prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
  CallableContract.Phase.beforeApplication (SourceTypedRuntime.RuntimeError.argumentArityMismatch function.parameters.length ids.length)

/-- The exact rejection keeps the independently graded Source fault, actual
argument post and cumulative caller pool. Its token is the selected raw error. -/
def RejectedAt (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize after finalMap finalWorld,
    function.parameters.length ≠ ids.length ∧
    dispatch.row.afterArguments = .error (.argumentArityMismatch function.parameters.length ids.length) ∧
    RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before id (.fault (.argumentArityMismatch function.parameters.length ids.length)) after ∧
    Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
      context evidence source environment before id callee ids metadata
      (.semanticFault (.argumentArityMismatch function.parameters.length ids.length)) after ∧
    value = .inLeft lowered.type (.word arityToken) ∧
    CallableIndexedOwnedStoredClosureArityBoundary.ResultAt (registry := registry) (faults := faults) (context := context)
      bridge profile compiler prepared initial dispatch (.argumentArityMismatch function.parameters.length ids.length)
      after arityToken finalStore finalMap finalWorld

/-- Actual accepted argument success retains the full fourth bind separately
from the strict application projection, at that same argument store. -/
def PassedAt (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  function.parameters.length = ids.length ∧ dispatch.row.afterArguments = .ok () ∧
  ∃ values argumentStore remainingSize applicationSize,
    EvaluationSize remainingSize (DataPatternValues.packValues values :: .unit :: calleeNative :: actual) argumentStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ remainingSize < budget ∧
    EvaluationSize applicationSize (.unit :: DataPatternValues.packValues values :: .unit :: calleeNative :: actual) argumentStore
      (.apply (.second (.first (.var 3))) (.var 1)) value finalStore ∧ applicationSize < budget

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

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge functionModel compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {sourceTypes : List TypeSystem.Ty}
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)

local notation "arityToken" => prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
  CallableContract.Phase.beforeApplication (SourceTypedRuntime.RuntimeError.argumentArityMismatch function.parameters.length ids.length)

/-- The exact rejection keeps the independently graded Source fault, actual
argument post and cumulative caller pool. Its token is the selected raw error. -/
def RejectedAt (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize after finalMap finalWorld,
    function.parameters.length ≠ ids.length ∧
    dispatch.row.afterArguments = .error (.argumentArityMismatch function.parameters.length ids.length) ∧
    RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before id (.fault (.argumentArityMismatch function.parameters.length ids.length)) after ∧
    Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
      context evidence source environment before id callee ids metadata
      (.semanticFault (.argumentArityMismatch function.parameters.length ids.length)) after ∧
    value = .inLeft lowered.type (.word arityToken) ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.FaultPost (registry := registry) (context := context)
      bridge functionModel compiler initial
      (CallableIndexedOwnedStoredClosureArityBoundary.FaultToken (faults := faults) compiler prepared dispatch) (.argumentArityMismatch function.parameters.length ids.length)
      after arityToken finalStore finalMap finalWorld

include parentTyped wellFormed runtime covers locals admitted calleeTrace post accepted unique parent selected in
/-- Resolve only the actual successful ordered argument receipt. The original
receipt is returned verbatim; no semantic producer or body result is assumed. -/
theorem resolve_success (budget : Nat) {value : Value} {finalStore : Store}
    (receipt : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge functionModel compiler prepared initial budget value finalStore) :
    CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge functionModel compiler prepared initial budget value finalStore ∧
    (RejectedAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (sidecar := sidecar) bridge functionModel compiler prepared initial dispatch value finalStore ∨
    PassedAt (actual := actual) compiler prepared dispatch budget value finalStore) := by
  refine ⟨receipt, ?_⟩
  obtain ⟨_nativeSize, argumentSize, sources, values, after, argumentStore, finalMap, finalWorld,
    _nativeArguments, _argumentStrict, argumentsTrace, _represented, finalHeaps, maps, worlds,
    frame, metadataExtended, ⟨reached, related, argumentAdmission⟩,
    ⟨remainingSize, remaining, remainingStrict, prefixReceipt⟩⟩ := receipt
  rcases resolve_application dispatch selected prefixReceipt with
    ⟨different, rejected, valueEq, storeEq⟩ | ⟨same, passed, applicationSize, application, applicationStrict⟩
  · subst finalStore
    obtain ⟨_calleeEvaluation, _representation, _calleeHeaps, _calleeMaps, _calleeWorlds, _calleeFrame,
      calleeMetadata, calleeReached, _calleeRelated, calleePost⟩ := post
    have calleeAdmission := calleePost.at_value.2
    obtain ⟨_parameter, _result, rawTypes, _calleeTyped, argumentsTyped, application⟩ :=
      CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts unique compiler.found compiler.originalForm parentTyped
    have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
    have argumentsCount := arguments_count_of_source_admission wellFormed runtime covers (locals.mono calleeMetadata)
      calleeAdmission.heap argumentsTyped count argumentsTrace
    have actualCount : sources.length = ids.length := argumentsCount.trans parent.arity.symm
    have failed : Dynamic.CallableFaults (Program.ofChecked compiled.sourceProgram) context evidence function.evidence
        after (.closure function) sources (.argumentArityMismatch function.parameters.length ids.length) after := by
      rw [← actualCount]
      exact .closureArity (actualCount.symm ▸ different)
    have called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
        (SourceExecutionSize.stepSize []) context evidence function.evidence after (.closure function) sources
        (.fault (.argumentArityMismatch function.parameters.length ids.length)) after := by
      rw [← actualCount]
      exact .fault (.closureArity (actualCount.symm ▸ different))
    obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
      compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeAdmission.heap
      argumentsTyped count calleeTrace (CallableIndexedOwnedIndirectExpressionHeads.SourceSuffix.called argumentsTrace called)
    obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack sources
    have coercions : Dynamic.CoercionPathExecutes (Program.ofChecked compiled.sourceProgram) context evidence
        after metadata.argumentCoercions packed packed after := by
      rw [compiler.argumentCoercions]
      exact .nil
    have staged : Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata
        (.semanticFault (.argumentArityMismatch function.parameters.length ids.length)) after :=
      .applicationFault calleeTrace.sound (by simpa only [prepared.call] using accepted) argumentsTrace.sound packing coercions
        packing parent.arity argumentsCount failed
    have loweredType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    left
    refine ⟨sourceSize, after, finalMap, finalWorld, different, rejected, original, staged, ?_, ?_⟩
    · exact loweredType.symm ▸ valueEq
    · exact ⟨Or.inr ⟨rfl, rfl⟩, finalHeaps, maps, worlds, frame, metadataExtended, reached, related,
        after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped original frame⟩
  · right
    exact ⟨same, passed, values, argumentStore, remainingSize, applicationSize, remaining, remainingStrict,
      application, applicationStrict⟩

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

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge profile compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {sourceTypes : List TypeSystem.Ty}
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)

local notation "arityToken" => prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
  CallableContract.Phase.beforeApplication (SourceTypedRuntime.RuntimeError.argumentArityMismatch function.parameters.length ids.length)

include parentTyped wellFormed runtime covers locals admitted calleeTrace post accepted unique parent selected in
/-- Resolve only the actual successful ordered argument receipt. The original
receipt is returned verbatim; no semantic producer or body result is assumed. -/
theorem resolve_success (budget : Nat) {value : Value} {finalStore : Store}
    (receipt : CallableIndexedOwnedStoredIndirectArgumentPrefix.SuccessPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge profile compiler prepared initial budget value finalStore) :
    CallableIndexedOwnedStoredIndirectArgumentPrefix.SuccessPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge profile compiler prepared initial budget value finalStore ∧
    (RejectedAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (sidecar := sidecar) bridge profile compiler prepared initial dispatch value finalStore ∨
    PassedAt (actual := actual) compiler prepared dispatch budget value finalStore) := by
  exact ForModel.resolve_success (functionModel := functions) (bridge := bridge) (compiler := compiler) (prepared := prepared) (parentTyped := parentTyped) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals) (initial := initial) (admitted := admitted) (calleeTrace := calleeTrace) (post := post) (accepted := accepted) (unique := unique) (parent := parent) (dispatch := dispatch) (selected := selected) budget receipt

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectApplicationPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectParentPrefix
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
Accepted arguments retain the entire original receipt, actual intermediate
effects and fourth-bind grade. -/
def ClosureResolutionWithEffects (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  (∃ reason, value = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧
    CallableIndexedOwnedStoredIndirectStageBoundary.ForModel.ResultAt
      (registry := registry) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (mapping := calleeMap) (world := calleeWorld)
      (calleeHeap := calleeHeap) (store := calleeStore)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize)
      bridge functionModel compiler prepared initial dispatch reason (dispatch.reason reason) finalStore) ∨
  (Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function) ∧
    (CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.FaultPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge functionModel compiler initial budget value finalStore ∨
    (CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge functionModel compiler prepared initial budget value finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
        (registry := registry) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
        (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
        (calleeMap := calleeMap) (calleeWorld := calleeWorld)
        bridge functionModel compiler prepared initial budget value finalStore ∧
      (CallableIndexedOwnedStoredIndirectApplicationPrefix.ForModel.RejectedAt
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (sidecar := sidecar) bridge functionModel compiler prepared initial dispatch value finalStore ∨
      CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
        compiler prepared dispatch budget value finalStore))))

variable (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge functionModel compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)

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
      bridge functionModel compiler prepared initial dispatch budget value finalStore := by
  rcases CallableIndexedOwnedStoredIndirectNativePrefix.ForModel.resolve_at_post bridge functionModel compiler prepared initial
      caller sidecarSource calleeTrace post dispatch receipt with rejected | ⟨accepted, suffixSize, suffix, smaller⟩
  · exact Or.inl rejected
  · right
    refine ⟨accepted, ?_⟩
    obtain ⟨_caller, _source, arguments⟩ :=
      CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.reflects_suffix_with_effects bridge functionModel compiler prepared parentTyped
        wellFormed runtime covers environments locals agrees typed initial admitted caller sidecarSource calleeTrace post
        accepted tree unique budget children suffix smaller
    rcases arguments with failed | succeeded
    · exact Or.inl failed
    · right
      obtain ⟨sameSuccess, verdict⟩ := CallableIndexedOwnedStoredIndirectApplicationPrefix.ForModel.resolve_success
        bridge functionModel compiler prepared parentTyped wellFormed runtime covers locals initial admitted
        calleeTrace post accepted unique parent dispatch selected budget succeeded.1
      exact ⟨sameSuccess, succeeded.2, verdict⟩
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
    CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge functionModel compiler initial sourceValue after carrier calleeStore finalMap finalWorld ∧
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
          bridge functionModel compiler prepared initial dispatch budget value finalStore

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
    (CallableIndexedOwnedStoredIndirectNativePrefix.ForModel.FaultPrefix
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        bridge functionModel compiler initial budget value finalStore ∨
      ValuePrefixWithEffects (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
        (sourceTypes := sourceTypes) (sidecar := sidecar) bridge functionModel compiler prepared initial budget value finalStore) := by
  obtain ⟨sameCaller, sameSource, producedPrefix⟩ :=
    CallableIndexedOwnedStoredIndirectNativePrefix.ForModel.reflects_prefix bridge functionModel compiler prepared certified found
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
    exact resolve_closure_with_effects bridge functionModel compiler prepared parentTyped wellFormed runtime covers environments locals
      agrees typed initial admitted caller sidecarSource tree unique parent dispatch selected trace post budget children gate

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
  exact ForModel.resolve_closure_with_effects (functionModel := functions) (bridge := bridge) (compiler := compiler) (prepared := prepared) (parentTyped := parentTyped) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (environments := environments) (locals := locals) (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted) (caller := caller) (sidecarSource := sidecarSource) (tree := tree) (unique := unique) (parent := parent) (dispatch := dispatch) (selected := selected) (calleeTrace := calleeTrace) (post := post) (children := children) budget receipt


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
  exact ForModel.reflects_parent_with_effects (functionModel := functions) (bridge := bridge) (compiler := compiler) (prepared := prepared) (certified := certified) (found := found) (sourceTyped := sourceTyped) (parentTyped := parentTyped) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted) (caller := caller) (sidecarSource := sidecarSource) (tree := tree) (unique := unique) (parent := parent) (children := children) (completed := completed) (within := within) budget


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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceBundleReceipts
/-! The authentic ordered Source typing row identifies the stored types of
the same argument tree. Original parent typing and the actual successful
callee trace then supply the raw closure bundle. Physical arity remains
independent; no native type or packed-type equality determines that count. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceBundleReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

/-- Uniqueness aligns each independently typed Source occurrence with the
actual stored node in the argument tree. Recursion is on static Source typing. -/
theorem source_row {source : TypedSource} {context : SourceSemantics.Context}
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {ids : List ExpressionId} {types storedTypes : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source context ids types)
    (tree : DataExpressionSequence.Tree source certificate scope ids storedTypes codes) :
    types = storedTypes := by
  cases typed with
  | nil => cases tree; rfl
  | cons head tail =>
    obtain ⟨typedNode, contained, sameType⟩ := head.stored_type
    cases tree with
    | single found generated =>
      cases tail
      have sameNode := Option.some.inj ((lookupExpression?_complete unique contained).symm.trans found)
      cases sameNode
      exact congrArg (fun type => [type]) sameType.symm
    | cons found generated rest =>
      have sameNode := Option.some.inj ((lookupExpression?_complete unique contained).symm.trans found)
      cases sameNode
      rw [sameType, ← source_row unique tail rest]
termination_by ids.length

/-- Real parent typing, empty argument coercions and the actual callee post
derive the raw Source bundle at the exact selected original binder row. -/
theorem source_bundle_of_trace
    {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before calleeHeap : Dynamic.Heap} {root callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode} {type : TypeSystem.Ty}
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {storedTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {function : Dynamic.Closure} {bindings : List CallableIndexedParameterCertificates.Binding}
    {size : Nat}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type)
    (tree : DataExpressionSequence.Tree source certificate scope ids storedTypes codes)
    (empty : metadata.argumentCoercions = [])
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment
      before callee (.closure function) calleeHeap)
    (binders : bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body)) :
    TypeSystem.Ty.productMany storedTypes =
      TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) := by
  obtain ⟨parameter, result, types, calleeTyped, argumentsTyped, application⟩ :=
    CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts unique found form typed
  obtain ⟨reachedTyped, _, _⟩ := wellFormed.wholeLanguagePreservation.expression context evidence source environment
    before calleeHeap callee (.closure function) (.function parameter result)
    runtime covers locals heapTyped calleeTyped calleeTrace.sound
  have closureTypes := reachedTyped.closure_function_inv
  have row := source_row unique argumentsTyped tree
  have bundle := CallableIndexedOwnedStoredClosureArgumentReceipts.empty_bundle application empty
  rw [← row, binders]
  exact bundle.trans closureTypes.1

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceBundleReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceResultReceipts
/-! Empty output coercions retain the authentic raw result of an indirect
Source application. Its actual successful callee trace identifies that result
with the selected closure's original result type. This is a finite Source
receipt; physical arity and native type projections remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceResultReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

/-- The original parent typing and its real empty output path identify the
callee's result before any runtime or native representation is considered. -/
theorem original_result
    {source : TypedSource} {context : SourceSemantics.Context}
    {root callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type) (empty : node.coercions = []) :
    ∃ parameter, ExpressionHasType source context callee (.function parameter type) := by
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have endpoint := requirements.outputPath.foldl_target
    rw [empty, List.foldl_nil] at endpoint
    rw [form] at raw
    cases raw with
    | indirectCall calleeTyped _ _ =>
      exact ⟨_, endpoint ▸ calleeTyped⟩

/-- Genuine Source preservation at the actual callee post yields the exact
Source result equality, without a native type or packed-type inference. -/
theorem source_result_of_trace
    {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before calleeHeap : Dynamic.Heap} {root callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode} {type : TypeSystem.Ty}
    {function : Dynamic.Closure} {size : Nat}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? root = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (typed : ExpressionHasType source context root type) (empty : node.coercions = [])
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment
      before callee (.closure function) calleeHeap) :
    type = function.resultType := by
  obtain ⟨parameter, calleeTyped⟩ := original_result unique found form typed empty
  obtain ⟨reachedTyped, _, _⟩ := wellFormed.wholeLanguagePreservation.expression context evidence source environment
    before calleeHeap callee (.closure function) (.function parameter type)
    runtime covers locals heapTyped calleeTyped calleeTrace.sound
  exact reachedTyped.closure_function_inv.2.1

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredSourceResultReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityDiagnostics
/-! The actual callable diagnostic factory interprets only the new arity
alternative at its exact beforeApplication token. An earlier argument fault
retains its original FaultRep. Every runtime state and effect remains the
frozen arity boundary's same result; no universal semantic decoder is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityDiagnostics
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
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {sidecar : SourceCoreStageContracts.Sidecar} {function : Dynamic.Closure} {calleeNative : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)
  (different : function.parameters.length ≠ ids.length)
  {base : SourceCoreFaultSites.Table} {minimum : Nat}
  (diagnosticsPrepared : SourceCoreCallableFaultSites.prepare compiled.indexed.base.plan native.table base minimum = .ok native.diagnostics)

private theorem issued_reason {table : SourceCoreStageCodebook.Table}
    {caller : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {reasonAt : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table caller call reasonAt = .ok site) :
    site.reasonAt = reasonAt := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; rfl
  · cases issued

include prepared dispatch in
private theorem actual_member : dispatch.row ∈ native.table.decisions := by
  have member := List.mem_of_find?_eq_some dispatch.found
  change dispatch.row ∈ prepared.site.table.casesAt prepared.site.caller prepared.site.call at member
  have contained := (List.mem_filter.mp member).1
  rwa [prepared.table] at contained

include selected different diagnosticsPrepared in
/-- The exact selected arity error decodes through its own real prepared table. -/
theorem arity_diagnostic :
    ∃ diagnostic,
      native.diagnostics.rootTable.diagnostic?
        (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeApplication
          (.argumentArityMismatch function.parameters.length ids.length)) = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch function.parameters.length ids.length := by
  have found := CallableFaultDiagnosticPreparation.prepared_after_arguments diagnosticsPrepared
    (actual_member compiler prepared dispatch)
    (CallableIndexedOwnedStoredClosureArityBoundary.rejected_row dispatch selected different)
  rw [issued_reason prepared.prepared]
  exact found

include selected different diagnosticsPrepared in
/-- Only the arity alternative adds a real table observation. Earlier child
fault representation is retained without an invented table law. -/
theorem decoded_fault {reason : Dynamic.SemanticFault} {token : Word}
    (observed : CallableIndexedOwnedStoredClosureArityBoundary.FaultToken (faults := faults) compiler prepared dispatch reason token) :
    faults reason token ∨ ∃ diagnostic,
      reason = .argumentArityMismatch function.parameters.length ids.length ∧
      native.diagnostics.rootTable.diagnostic? token = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch function.parameters.length ids.length := by
  rcases observed with earlier | ⟨reasonEq, tokenEq⟩
  · exact Or.inl earlier
  · obtain ⟨diagnostic, found, error⟩ := arity_diagnostic compiler prepared dispatch selected different diagnosticsPrepared
    exact Or.inr ⟨diagnostic, reasonEq, tokenEq.symm ▸ found, error⟩

variable {context : SourceSemantics.Context}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)

include selected different diagnosticsPrepared in
/-- The complete runtime receipt is retained verbatim beside the actual table
observation. The returned pool and all cumulative effects remain identical. -/
theorem decoded_result {reason : Dynamic.SemanticFault} {after : Dynamic.Heap} {token : Word} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : CallableIndexedOwnedStoredClosureArityBoundary.ResultAt (registry := registry) (faults := faults)
      (context := context) bridge profile compiler prepared initial dispatch reason after token finalStore finalMap finalWorld) :
    CallableIndexedOwnedStoredClosureArityBoundary.ResultAt (registry := registry) (faults := faults)
      (context := context) bridge profile compiler prepared initial dispatch reason after token finalStore finalMap finalWorld ∧
    (faults reason token ∨ ∃ diagnostic,
      reason = .argumentArityMismatch function.parameters.length ids.length ∧
      native.diagnostics.rootTable.diagnostic? token = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch function.parameters.length ids.length) :=
  ⟨result, decoded_fault compiler prepared dispatch selected different diagnosticsPrepared result.1⟩
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArityDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectAcceptedApplication
/-! The accepted application consumes the exact ordered argument receipt and
its retained callee-to-argument effects. The whole fourth-bind grade stays
unchanged; its pure reads give the actual payload application grade. Genuine
same-Code association and selected binder projection receipts remain static
inputs. Source traces derive raw callee and argument admission, while only the
strict shared-family body IH invokes the callable and restores the same caller
pool. Ordered argument reflection is not repeated. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectAcceptedApplication
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
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
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge profile compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
    compiler.original dispatch.row)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (association : Association headers keys registry faults calleeMap calleeWorld function calleeNative bindings parameterCore resultCore)
  (bindingPack : parameterCore = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))

/-- Semantic callable outcomes retain their genuine staged counterpart.
Stage rejection is a separate earlier outcome. -/
def boundaryOutcome : Dynamic.ExpressionOutcome → Staging.CallBoundary.Outcome
  | .value value => .value value
  | .fault reason => .semanticFault reason

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

/-- The original successful prefix, actual intermediate effects and passed
fourth gate remain attached beside the complete Source and staged outcome. -/
def ResultAt (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
    CallableIndexedOwnedStoredIndirectArgumentPrefix.SuccessPrefix
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
    CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore ∧
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata (boundaryOutcome outcome) after ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler initial outcome after value finalStore finalMap finalWorld

include parentTyped wellFormed runtime covers locals admitted tree unique parent actualFunctionType
  calleeTrace post accepted association bindingPack in
/-- The exact successful argument receipt supplies binding representations and
current admission internally. The strict payload grade selects only body IH;
all original prefix receipts are returned unchanged beside the whole result. -/
theorem reflects_selected (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.SuccessPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge profile compiler prepared initial budget value finalStore)
    (step : CallableIndexedOwnedStoredIndirectSuccessStep.SuccessStep
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge profile compiler prepared initial budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    ResultAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := calleeMap) (calleeWorld := calleeWorld) (sidecar := sidecar)
      bridge profile compiler prepared initial dispatch budget value finalStore := by
  refine ⟨original, step, passed, ?_⟩
  obtain ⟨_nativeSize, argumentSize, sources, values, middle, argumentStore, argumentMap, argumentWorld,
    _argumentsNative, _argumentsStrict, argumentsTrace, represented, argumentHeaps, stepMaps, stepWorlds, _stepFrame, _stepMetadata,
    maps, worlds, frame, metadataExtended, ⟨argumentState, related, argumentAdmission⟩,
    ⟨remainingSize, remaining, remainingStrict⟩⟩ := step
  obtain ⟨_calleeEvaluation, calleeRep, _calleeHeaps, _calleeMaps, _calleeWorlds, _calleeFrame,
    _calleeMetadata, _calleeState, _calleeRelated, _calleePost⟩ := post
  have sourceBundle := CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
    unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
    wellFormed runtime covers locals admitted.heap calleeTrace
    (CallableIndexedOwnedStoredIndirectCallBounds.Association.source_binders association)
  have nativeBundle := (CallableIndexedOwnedStoredNativePackReceipts.compiler_parameter_pack
    compiler actualFunctionType association calleeRep).trans bindingPack
  have nativeResult := (CallableIndexedOwnedStoredNativePackReceipts.compiler_parameters
    compiler actualFunctionType association calleeRep).2
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals admitted.heap calleeTrace)
  have binderCount : ids.length = bindings.length := passed.1.symm.trans
    (CallableIndexedOwnedStoredIndirectCallBounds.Association.binding_count association).symm
  have nativeCount : (compiler.codes.map (·.type)).length = bindings.length := by
    simpa only [List.length_map] using compiler.ordered_children.1.symm.trans binderCount
  have valuesCount : sources.length = bindings.length := represented.length.1.symm.trans nativeCount
  have representedArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles bindings represented
    valuesCount sourceBundle nativeBundle
  have future := association.extend stepMaps stepWorlds
  obtain ⟨parameter, sourceResult, rawTypes, _calleeTyping, argumentsTyping, application,
    calleeTyped, calleeHeapTyped, _calleeExtension, calleeLocals, rawTyped, _argumentHeapTyped,
    extension, _argumentLocals, _fullExtension, rawArity, packed, packing, _packedTyped, _raw⟩ :=
    CallableIndexedOwnedStoredCallSourcePrefix.from_admission bridge initial wellFormed runtime covers locals admitted
      unique compiler.found compiler.originalForm parentTyped compiler.argumentCoercions future representedArguments
      calleeTrace argumentsTrace
  have count : rawTypes.length = metadata.argumentCount := by
    cases application with | intro count _ _ _ => exact count.symm
  have argumentsCount := arguments_count_of_source_admission wellFormed runtime covers calleeLocals calleeHeapTyped
    argumentsTyping count argumentsTrace
  have read : Evaluates (DataPatternValues.packValues values :: .unit :: calleeNative :: actual) argumentStore
      (.second (.var 2)) (.word dispatch.contract) argumentStore :=
    .second (.var (by simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have gate := prepared.site.dispatch_known .beforeApplication native.diagnostics.unknown
    dispatch.contract dispatch.row dispatch.found read
  rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication passed.2.1] at gate
  cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
  | failed failed _strict =>
    have same := (evaluation_deterministic failed.sound gate).1
    cases same
  | continued acceptedGate applicationTrace _gateStrict applicationStrict =>
    obtain ⟨same, stores⟩ := evaluation_deterministic acceptedGate.sound gate
    cases same
    subst stores
    have payloadTrace := CallableIndexedOwnedStoredApplicationProjection.to_payload applicationTrace
    obtain ⟨callSize, outcome, after, called, finalMap, finalWorld, resultRep, finalHeaps, lastMaps, lastWorlds,
      lastFrame, lastMetadata, _baseReached, _baseRelated, _stable, returned, _samePool, lastRelated⟩ :=
      CallableIndexedOwnedAdmittedStoredClosureInvocation.reflects_at bridge functions wellFormed runtime future
        argumentState argumentAdmission calleeTyped extension representedArguments argumentHeaps rawTyped packing
        (CallableIndexedOwnedStoredClosureArgumentReceipts.empty_bundle application compiler.argumentCoercions)
        rawArity budget below (callContext := context) (callerEvidence := evidence) payloadTrace (Nat.le_of_lt applicationStrict)
    obtain ⟨sourceSize, sourceParent⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm
      parent.requirements parent.coercions compiler.argumentCoercions parent.arity wellFormed runtime covers
      calleeLocals calleeHeapTyped argumentsTyping count calleeTrace
      (CallableIndexedOwnedIndirectExpressionHeads.SourceSuffix.called argumentsTrace called)
    have coercions : Dynamic.CoercionPathExecutes (Program.ofChecked compiled.sourceProgram) context evidence
        middle metadata.argumentCoercions packed packed middle := by
      rw [compiler.argumentCoercions]
      exact .nil
    have staged : Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata (boundaryOutcome outcome) after := by
      cases called with
      | value applied =>
        exact .applied calleeTrace.sound (by simpa only [prepared.call] using accepted) argumentsTrace.sound
          packing coercions packing parent.arity argumentsCount applied.sound
      | fault failed =>
        exact .applicationFault calleeTrace.sound (by simpa only [prepared.call] using accepted) argumentsTrace.sound
          packing coercions packing parent.arity argumentsCount failed.sound
    have loweredType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    have parentRep : GenericExpressionMeaning.ResultRepresents model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value := by
      rw [loweredType, nativeResult]
      cases resultRep with
      | value relatedPayload => exact .value (.compatible rawResult relatedPayload)
      | fault matched => exact .fault matched
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceParent, staged, parentRep, finalHeaps,
      maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadataExtended.trans lastMetadata,
      returned, callerProtocol.trans related lastRelated,
      after_expression_sized initial returned admitted wellFormed runtime covers locals parentTyped sourceParent
        (frame.trans lastFrame)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectAcceptedApplication
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectAcceptedSiteApplication
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectParentApplication
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectSiteSuccess
/-! The exact contextual Site retains its chosen binder policy beside the
actual callee post. Genuine Source parent typing identifies the raw ordered
argument bundle; the actual represented callee and same-Code projections
identify the native bundle and result. Four finite continuations reuse the
frozen success adapter with the same reached pool and independent grades.
Physical binder count, raw result compatibility and genuine stage gates remain
explicit. This covers accepted empty coercions at strong ordinary/principal
origins; rejection and other origin branches remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectSiteSuccess
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
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType result)
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
  binderCount rawResult stages caller sidecarSource dispatch accepted calleeTrace in
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
  have actualPost := post
  obtain ⟨_calleeEvaluation, represented, _heaps, _maps, _worlds, _frame, _metadata, _reached, _related, _admitted⟩ := post
  have selected : CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
      (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment) (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
      site.code.receipt.loweredParameters site.code.receipt.parameterCore site.code.receipt.resultCore :=
    CallableIndexedOwnedStoredClosureInvocation.Association.ordinary
      (headers := headers) (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (function := closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)
      (scope := captureScope) (actual := capturedActual)
      owner captured site.code history support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree
  have sourceBundle := CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
    unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
    wellFormed runtime covers locals firstAdmission.heap calleeTrace
    (CallableIndexedOwnedStoredIndirectCallBounds.Association.source_binders selected)
  have nativeBundle := CallableIndexedOwnedContextualLambdaPackReceipts.compiler_binding_pack_of_ordinary_site
    captured site history profile binderPolicy compiler actualFunctionType represented owner observed referenceIndex
    nativeTyped escaped support origin prefixContext syntaxTree
  have nativeResult := (CallableIndexedOwnedStoredNativePackReceipts.compiler_parameters
    compiler actualFunctionType selected represented).2
  exact CallableIndexedOwnedStoredIndirectCalleeSuccess.preserves_ordinary
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission owner captured site.code history support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree actualPost
    binderCount sourceBundle nativeBundle rawResult nativeResult stages caller sidecarSource dispatch accepted calleeTrace
    budget children below suffix argumentsWithin callWithin

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured site history binderPolicy actualFunctionType support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree post
  binderCount rawResult stages caller sidecarSource dispatch accepted calleeTrace in
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
  have actualPost := post
  obtain ⟨_calleeEvaluation, represented, _heaps, _maps, _worlds, _frame, _metadata, _reached, _related, _admitted⟩ := post
  have selected : CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
      (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment) (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
      site.code.receipt.loweredParameters site.code.receipt.parameterCore site.code.receipt.resultCore :=
    CallableIndexedOwnedStoredClosureInvocation.Association.ordinary
      (headers := headers) (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (function := closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)
      (scope := captureScope) (actual := capturedActual)
      owner captured site.code history support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree
  have sourceBundle := CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
    unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
    wellFormed runtime covers locals firstAdmission.heap calleeTrace
    (CallableIndexedOwnedStoredIndirectCallBounds.Association.source_binders selected)
  have nativeBundle := CallableIndexedOwnedContextualLambdaPackReceipts.compiler_binding_pack_of_ordinary_site
    captured site history profile binderPolicy compiler actualFunctionType represented owner observed referenceIndex
    nativeTyped escaped support origin prefixContext syntaxTree
  have nativeResult := (CallableIndexedOwnedStoredNativePackReceipts.compiler_parameters
    compiler actualFunctionType selected represented).2
  exact CallableIndexedOwnedStoredIndirectCalleeSuccess.reflects_ordinary
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission owner captured site.code history support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree actualPost
    binderCount sourceBundle nativeBundle rawResult nativeResult stages caller sidecarSource dispatch accepted calleeTrace
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
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType result)
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
  binderCount rawResult stages caller sidecarSource dispatch accepted calleeTrace in
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
  have actualPost := post
  obtain ⟨_calleeEvaluation, represented, _heaps, _maps, _worlds, _frame, _metadata, _reached, _related, _admitted⟩ := post
  have selected : CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
      (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment) (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
      site.code.receipt.loweredParameters site.code.receipt.parameterCore site.code.receipt.resultCore :=
    CallableIndexedOwnedStoredClosureInvocation.Association.principal
      (headers := headers) (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (function := closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)
      (scope := captureScope) (actual := capturedActual)
      owner captured site.code history support origin observed leading referenceIndex nativeTyped escaped syntaxTree
  have sourceBundle := CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
    unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
    wellFormed runtime covers locals firstAdmission.heap calleeTrace
    (CallableIndexedOwnedStoredIndirectCallBounds.Association.source_binders selected)
  have nativeBundle := CallableIndexedOwnedContextualLambdaPackReceipts.compiler_binding_pack_of_principal_site
    captured site history profile binderPolicy compiler actualFunctionType represented owner observed referenceIndex
    nativeTyped escaped support origin leading syntaxTree
  have nativeResult := (CallableIndexedOwnedStoredNativePackReceipts.compiler_parameters
    compiler actualFunctionType selected represented).2
  exact CallableIndexedOwnedStoredIndirectCalleeSuccess.preserves_principal
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission owner captured site.code history support origin observed leading referenceIndex nativeTyped escaped syntaxTree actualPost
    binderCount sourceBundle nativeBundle rawResult nativeResult stages caller sidecarSource dispatch accepted calleeTrace
    budget children below suffix argumentsWithin callWithin

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured site history binderPolicy actualFunctionType support origin observed leading referenceIndex nativeTyped escaped syntaxTree post
  binderCount rawResult stages caller sidecarSource dispatch accepted calleeTrace in
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
  have actualPost := post
  obtain ⟨_calleeEvaluation, represented, _heaps, _maps, _worlds, _frame, _metadata, _reached, _related, _admitted⟩ := post
  have selected : CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
      (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment) (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
      site.code.receipt.loweredParameters site.code.receipt.parameterCore site.code.receipt.resultCore :=
    CallableIndexedOwnedStoredClosureInvocation.Association.principal
      (headers := headers) (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (function := closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)
      (scope := captureScope) (actual := capturedActual)
      owner captured site.code history support origin observed leading referenceIndex nativeTyped escaped syntaxTree
  have sourceBundle := CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
    unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
    wellFormed runtime covers locals firstAdmission.heap calleeTrace
    (CallableIndexedOwnedStoredIndirectCallBounds.Association.source_binders selected)
  have nativeBundle := CallableIndexedOwnedContextualLambdaPackReceipts.compiler_binding_pack_of_principal_site
    captured site history profile binderPolicy compiler actualFunctionType represented owner observed referenceIndex
    nativeTyped escaped support origin leading syntaxTree
  have nativeResult := (CallableIndexedOwnedStoredNativePackReceipts.compiler_parameters
    compiler actualFunctionType selected represented).2
  exact CallableIndexedOwnedStoredIndirectCalleeSuccess.reflects_principal
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission owner captured site.code history support origin observed leading referenceIndex nativeTyped escaped syntaxTree actualPost
    binderCount sourceBundle nativeBundle rawResult nativeResult stages caller sidecarSource dispatch accepted calleeTrace
    budget children below completed within
end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectSiteSuccess
end
