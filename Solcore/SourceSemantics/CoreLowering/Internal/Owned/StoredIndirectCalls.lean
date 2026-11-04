import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.IndirectSequences
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ProfileExtraction
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableFaultDiagnosticPreparation
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState

/-!
# Owned callables: stored indirect calls

Call bounds and callee posts of stored indirect calls, with stage boundaries and diagnostics.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallBounds
/-! Accepted empty-coercion stored calls retain the actual successful callee
post and its full ordinary or principal association. The association carries
same-body Syntax, compiler binders and immutable captured history; current
caller rows come from the actual caller post. The original ordered argument
fold, payload invocation and finite call inversions retain all intermediate
states and independent Source/native grades. Actual callee child receipts are
fixed at their reached post; they assert no completed callee family law.
Legacy arbitrary prefixes, builtin/global stored origins, nonclosure callees,
arity rejection, staging rejection and nonempty argument/output coercions
remain outside this accepted strong-origin companion. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedStoredClosureInvocation (Association)
open CallableIndexedOwnedStoredClosureArgumentReceipts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Real selected binders keep their physical count independently of packing. -/
theorem Association.binding_count {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (selected : Association headers keys registry faults mapping world function native bindings parameter result) :
    bindings.length = function.parameters.length := by
  cases selected with
  | ordinary _ _ code _ _ _ _ _ _ _ _ _ =>
    simpa only [List.length_map] using
      (congrArg List.length (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm
  | principal _ _ code _ _ _ _ _ _ _ _ _ =>
    simpa only [List.length_map] using
      (congrArg List.length (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm

/-- Exact original parameters retain the raw Source binder row. -/
theorem Association.source_binders {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (selected : Association headers keys registry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) = function.parameters.map (fun binder => binder.scheme.body) := by
  cases selected with
  | ordinary _ _ code _ _ _ _ _ _ _ _ _ =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm
  | principal _ _ code _ _ _ _ _ _ _ _ _ =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm

/-- The actual native carrier retains its visible contract word. -/
theorem Association.shape {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (selected : Association headers keys registry faults mapping world function native bindings parameter result) :
    ∃ payload word, native = .pair payload (.word word) := by
  cases selected <;> exact ⟨_, _, rfl⟩

/-- A selected actual guard is the guard produced for this same entry contract. -/
theorem selected_contract {sidecar : SourceCoreStageContracts.Sidecar}
    {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode}
    {function : Dynamic.Closure} {native : Value}
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call ids (.closure function) native)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata node dispatch.row) :
    dispatch.row.entry.contract = some dispatch.guard.contract := by
  cases contractAt : dispatch.row.entry.contract with
  | none =>
    have empty := selected.generated.builtin contractAt
    rw [dispatch.attached] at empty
    cases empty
  | some contract =>
    obtain ⟨guard, prepared, attached, _⟩ := selected.generated.user contract contractAt
    have same := Option.some.inj (attached.symm.trans dispatch.attached)
    subst guard
    obtain ⟨receipt⟩ := CallContractCertificates.guard_of_accepted prepared
    exact congrArg some receipt.contract_eq.symm

/-- Source binding and authentic argument arity close the exact second gate. -/
theorem application_gate {sidecar : SourceCoreStageContracts.Sidecar}
    {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode}
    {function : Dynamic.Closure} {native : Value}
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call ids (.closure function) native)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata node dispatch.row)
    (arity : function.parameters.length = ids.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none := by
  have same : dispatch.contract = dispatch.row.entry.id :=
    beq_iff_eq.mp (List.find?_some (p := fun row : SourceCoreStageCodebook.Decision =>
      dispatch.contract == row.entry.id) dispatch.found)
  rw [same]
  exact selected.before_application_for_closure (selected_contract dispatch selected) dispatch.bound arity unknown

private theorem second_read {environment : Environment} {store : Store} {native payload : Value}
    {word : Word} {index : Nat} (shape : native = .pair payload (.word word))
    (found : environment[index]? = some native) :
    Evaluates environment store (.second (.var index)) (.word word) store :=
  .second (.var (found.trans (congrArg some shape)))

section Completion
variable {actual : Environment} {store calleeStore : Store} {native : Value}

/-- The original fourth bind supplies its full application grade, not merely
separate component grades. This is needed for the unchanged strict body budget. -/
inductive AcceptedCompletion (budget : Nat) (resultType : Ty) (arguments : Expr) : Value → Store → Prop where
  | failed {size : Nat} {input : Ty} {token : Value} {after : Store}
      (argumentsTrace : EvaluationSize size (.unit :: native :: actual) calleeStore
        ((arguments.weakenAt 0).weakenAt 0) (.inLeft input token) after)
      (strict : size < budget) : AcceptedCompletion budget resultType arguments (.inLeft resultType token) after
  | applied {argumentsSize applicationSize : Nat} {input : Ty} {argument value : Value} {middle after : Store}
      (argumentsTrace : EvaluationSize argumentsSize (.unit :: native :: actual) calleeStore
        ((arguments.weakenAt 0).weakenAt 0) (.inRight input argument) middle)
      (applicationTrace : EvaluationSize applicationSize [native, argument] middle
        CallableIndexedLambdaCalls.applyPayload value after)
      (argumentsStrict : argumentsSize < budget) (applicationStrict : applicationSize < budget) :
      AcceptedCompletion budget resultType arguments value after

/-- Only finite existing bind inversions and actual pure gate decisions are
used. The successful callee may have changed the real store. -/
theorem accepted_completed {budget size : Nat} {resultType : Ty} {callee arguments : Expr}
    {gates : List CallableContract.Gate} {unknown : Word} {word : Word} {payload result : Value} {after : Store}
    (shape : native = .pair payload (.word word))
    (calleeTrace : Evaluates actual store callee (.inRight .word native) calleeStore)
    (stage : CallableContract.decision gates .beforeArguments unknown word = none)
    (arity : CallableContract.decision gates .beforeApplication unknown word = none)
    (trace : EvaluationSize size actual store (CallableContract.call gates unknown resultType callee arguments) result after)
    (within : size ≤ budget) :
    AcceptedCompletion (actual := actual) (calleeStore := calleeStore) (native := native) budget resultType arguments result after := by
  have descriptor : Evaluates (native :: actual) calleeStore (.second (.var 0)) (.word word) calleeStore := by
    exact second_read (index := 0) shape rfl
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
      | failed argumentsTrace argumentsStrict => exact .failed argumentsTrace argumentsStrict
      | continued argumentsTrace remaining argumentsStrict remainingStrict =>
        cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
        | failed gate _ =>
          obtain ⟨same, _⟩ := CallableIndirectCallBounds.dispatch_decision (second_read (index := 2) shape rfl) gate
          simp only [arity, CallableContract.resultValue] at same
          cases same
        | continued gate application _ applicationStrict =>
          obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision (second_read (index := 2) shape rfl) gate
          simp only [arity, CallableContract.resultValue] at same
          cases same
          exact .applied argumentsTrace (CallableIndexedOwnedStoredApplicationProjection.to_payload application)
            argumentsStrict applicationStrict
/-- The same visible descriptor closes the first real gate before an
actual argument fault. -/
theorem call_argument_fault {resultType input : Ty} {callee arguments : Expr}
    {gates : List CallableContract.Gate} {unknown word reason : Word} {payload : Value} {after : Store}
    (shape : native = .pair payload (.word word))
    (calleeTrace : Evaluates actual store callee (.inRight .word native) calleeStore)
    (stage : CallableContract.decision gates .beforeArguments unknown word = none)
    (argumentsTrace : Evaluates (.unit :: native :: actual) calleeStore
      ((arguments.weakenAt 0).weakenAt 0) (.inLeft input (.word reason)) after) :
    Evaluates actual store (CallableContract.call gates unknown resultType callee arguments)
      (.inLeft resultType (.word reason)) after := by
  rw [shape] at calleeTrace argumentsTrace
  exact CallableContract.call_argument_failure gates unknown calleeTrace stage argumentsTrace

/-- The fourth bind consumes the original payload application itself. No
body or captured environment is reconstructed from its result. -/
theorem call_payload_success {resultType : Ty} {callee arguments : Expr}
    {gates : List CallableContract.Gate} {unknown word : Word} {payload argument result : Value}
    {middle after : Store}
    (shape : native = .pair payload (.word word))
    (calleeTrace : Evaluates actual store callee (.inRight .word native) calleeStore)
    (stage : CallableContract.decision gates .beforeArguments unknown word = none)
    (argumentsTrace : Evaluates (.unit :: native :: actual) calleeStore
      ((arguments.weakenAt 0).weakenAt 0) (.inRight .word argument) middle)
    (arity : CallableContract.decision gates .beforeApplication unknown word = none)
    (application : Evaluates [native, argument] middle CallableIndexedLambdaCalls.applyPayload result after) :
    Evaluates actual store (CallableContract.call gates unknown resultType callee arguments) result after := by
  apply LanguageResult.bind_success resultType calleeTrace
  apply LanguageResult.bind_success resultType
  · have gate := CallableContract.dispatch_evaluates gates .beforeArguments unknown word
      (second_read (index := 0) shape rfl : Evaluates (native :: actual) calleeStore (.second (.var 0)) (.word word) calleeStore)
    simpa only [stage, CallableContract.resultValue] using gate
  apply LanguageResult.bind_success resultType argumentsTrace
  apply LanguageResult.bind_success resultType
  · have gate := CallableContract.dispatch_evaluates gates .beforeApplication unknown word
      (second_read (index := 2) shape rfl : Evaluates (argument :: .unit :: native :: actual) middle (.second (.var 2)) (.word word) middle)
    simpa only [arity, CallableContract.resultValue] using gate
  exact CallableIndexedOwnedStoredApplicationProjection.evaluates_from_payload application
end Completion


/-- Native typing is already part of the full association at this same world. -/
theorem Association.native_typed {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (selected : Association headers keys registry faults mapping world function native bindings parameter result) :
    RuntimeValueHasType world native (CallableContract.functionType parameter result) compiled.indexed.layouts.definitions := by
  cases selected with
  | ordinary _ _ _ _ _ _ _ _ _ typed _ _ => exact typed
  | principal _ _ _ _ _ _ _ _ _ typed _ _ => exact typed

namespace ForModel
section Selected
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
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
  (calleeState : callerProtocol.State ⟨scope, mapping, world, calleeHeap, store, canonical⟩)
  (calleeRelated : callerProtocol.Relates first calleeState)
  (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
  (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
  (calleeMetadata : Dynamic.HeapMetadataExtend before calleeHeap)
  {function : Dynamic.Closure} {calleeNative : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (nativeTyped : RuntimeValueHasType world calleeNative (CallableContract.functionType parameterCore resultCore) compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world calleeHeap store)
  (binderCount : ids.length = bindings.length)
  (sourceBundle : TypeSystem.Ty.productMany sourceTypes = TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)))
  (nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
    SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType)
  (nativeResult : compiler.resultType = resultCore)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word calleeNative) store)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

/-- The whole parent keeps the actual returned caller witness and success-only
Source admission. Its native and Source result types remain independent receipts. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  GenericExpressionMeaning.ResultRepresents model finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧ PostAdmission bridge context compiler.original.type outcome reached

include rawResult nativeResult in
theorem parent_result {finalMap : LocationMap} {finalWorld : StoreTyping}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (related : FunctionCalls.ResultRepresents model finalMap finalWorld function.resultType resultCore faults outcome value) :
    GenericExpressionMeaning.ResultRepresents model finalMap finalWorld compiler.original.type lowered.type faults outcome value := by
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  rw [loweredType, nativeResult]
  cases related with
  | value payload => exact .value (.compatible rawResult payload)
  | fault matched => exact .fault matched

/-- A genuine called constructor at the same Source suffix and its exact grade. -/
def CalledSuffix {suffixArgumentsSize suffixCallSize : Nat}
    {suffixOutcome : Dynamic.ExpressionOutcome} {suffixAfter : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      suffixArgumentsSize suffixCallSize suffixOutcome suffixAfter) : Prop :=
  ∃ (arguments : List Dynamic.Value) (middle : Dynamic.Heap),
    ∃ argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) suffixArgumentsSize
      context evidence source environment calleeHeap ids arguments middle,
    ∃ called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) suffixCallSize
      context evidence function.evidence middle (.closure function) arguments suffixOutcome suffixAfter,
      suffix = .called argumentsTrace called

/-- An intermediate leaf at the actual admitted argument state. The final
prepared endpoint constructs this leaf from strict body children. -/
def ApplicationPreserves (budget : Nat)
    {suffixArgumentsSize suffixCallSize : Nat} {suffixOutcome : Dynamic.ExpressionOutcome} {suffixAfter : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      suffixArgumentsSize suffixCallSize suffixOutcome suffixAfter) : Prop :=
  ∀ {middleMap : LocationMap} {middleWorld : StoreTyping} {middle : Dynamic.Heap} {middleStore : Store}
    {arguments : List Dynamic.Value} {payloads : List Value} {types : List TypeSystem.Ty}
    {parameter sourceResult : TypeSystem.Ty} {packed : Dynamic.Value},
    (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩) →
    Admission bridge context argumentState →
    LocationMap.Extends mapping middleMap → WorldExtends world middleWorld →
    AdministrativePreserved mapping store middleMap middleStore → Dynamic.HeapMetadataExtend calleeHeap middle →
    Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter sourceResult) →
    Dynamic.HeapTypesExtend calleeHeap middle →
    DataExpressionSequence.Values model middleMap middleWorld sourceTypes (compiler.codes.map (·.type)) arguments payloads →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions middleMap middleWorld middle middleStore →
    Dynamic.ValuesHaveTypes context middle arguments types → Dynamic.ValuesPack arguments packed →
    TypeSystem.Ty.productMany types = parameter →
    ∀ {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize context evidence
      source environment calleeHeap ids arguments middle) →
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize context evidence
      function.evidence middle (.closure function) arguments outcome after) →
    CalledSuffix (context := context) (evidence := evidence) (environment := environment) suffix →
    callSize ≤ budget →
    ∃ result finalStore finalMap finalWorld,
      CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown dispatch.contract = none ∧
      Evaluates [calleeNative, DataPatternValues.packValues payloads] middleStore
        CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld function.resultType resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends middleMap finalMap ∧ WorldExtends middleWorld finalWorld ∧
      AdministrativePreserved middleMap middleStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend middle after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates argumentState returned

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata nativeTyped heaps
  rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation in
/-- A real successful callee post feeds ordered admitted arguments, the exact
parameter continuation and the original whole call. Only strict child IH remains. -/
theorem preserves_selected_with_application
    (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget)
    (applicationPreserves : ApplicationPreserves (registry := registry) (faults := faults) bridge functions compiler prepared (native := native)
      (context := context) (evidence := evidence) (environment := environment) (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := mapping) (world := world) (store := store) (function := function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := resultCore) (dispatch := dispatch) budget suffix) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      ResultAt (registry := registry) (faults := faults) (context := context) bridge functions compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨parameter, sourceResult, rawTypes, calleeTyping, argumentsTyping, application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  obtain ⟨calleeTyped, calleeHeapTyped, calleeExtension⟩ :=
    wellFormed.wholeLanguagePreservation.expression context evidence source environment before calleeHeap callee
      (.closure function) (.function parameter sourceResult) runtime covers locals firstAdmission.heap calleeTyping calleeTrace.sound
  have calleeAdmission : Admission bridge context calleeState :=
    ⟨calleeHeapTyped, StableRows.after_administrative (bridge.pool first) (bridge.pool calleeState) firstAdmission.rows calleeFrame⟩
  have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
  obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
    compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
    argumentsTyping count calleeTrace suffix
  have stage := CallableIndexedOwnedSelectedCallStageAcceptance.before_arguments dispatch accepted native.diagnostics.unknown
  have emitted := prepared.lowered_rename compiler ξ
  rw [nativeResult] at emitted
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons nativeTyped (typed.weaken calleeWorlds))
  cases suffix with
  | argumentFault failed =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        frame, metadata, reached, related, _stable⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_fault_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission failed argumentsWithin
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at evaluated
    have whole := call_argument_fault (resultType := resultCore) dispatch.shape calleeEvaluation stage evaluated
    rw [← emitted] at whole
    exact ⟨sourceSize, _, finalStore, finalMap, finalWorld, original, whole,
      parent_result functions compiler rawResult nativeResult (.fault matched), finalHeaps,
      calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans metadata,
      reached, callerProtocol.trans calleeRelated related,
      after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (calleeFrame.trans frame)⟩
  | called argumentsTrace called =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentEvaluation, represented, middleHeaps,
        maps, worlds, frame, metadata, argumentState, related, argumentAdmission⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_values_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace argumentsWithin
    obtain ⟨packed, packing, rawTyped, _heapTyped, extension, _packedTyped⟩ :=
      after_trace wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped argumentsTyping argumentsTrace
    obtain ⟨result, finalStore, finalMap, finalWorld, arity, evaluated, resultRep, finalHeaps, lastMaps, lastWorlds,
        lastFrame, lastMetadata, returned, lastRelated⟩ :=
      applicationPreserves argumentState argumentAdmission maps worlds frame metadata calleeTyped extension
        represented middleHeaps rawTyped packing (empty_bundle application compiler.argumentCoercions)
        argumentsTrace called ⟨_, _, argumentsTrace, called, rfl⟩ callWithin
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentEvaluation
    have whole := call_payload_success (resultType := resultCore) dispatch.shape calleeEvaluation stage
      argumentEvaluation arity evaluated
    rw [← emitted] at whole
    exact ⟨sourceSize, result, finalStore, finalMap, finalWorld, original, whole,
      parent_result functions compiler rawResult nativeResult resultRep, finalHeaps,
      (calleeMaps.trans maps).trans lastMaps, (calleeWorlds.trans worlds).trans lastWorlds,
      (calleeFrame.trans frame).trans lastFrame, (calleeMetadata.trans metadata).trans lastMetadata,
      returned, callerProtocol.trans (callerProtocol.trans calleeRelated related) lastRelated,
      after_expression_sized first returned firstAdmission wellFormed runtime covers locals parentTyped original
        ((calleeFrame.trans frame).trans lastFrame)⟩

end Selected
end ForModel

section Selected
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
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
  (calleeState : callerProtocol.State ⟨scope, mapping, world, calleeHeap, store, canonical⟩)
  (calleeRelated : callerProtocol.Relates first calleeState)
  (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
  (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
  (calleeMetadata : Dynamic.HeapMetadataExtend before calleeHeap)
  {function : Dynamic.Closure} {calleeNative : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (association : Association headers keys registry faults mapping world function calleeNative bindings parameterCore resultCore)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile) mapping world calleeHeap store)
  (binderCount : ids.length = bindings.length)
  (sourceBundle : TypeSystem.Ty.productMany sourceTypes = TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)))
  (nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
    SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType)
  (nativeResult : compiler.resultType = resultCore)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word calleeNative) store)

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

/-- The whole parent keeps the actual returned caller witness and success-only
Source admission. Its native and Source result types remain independent receipts. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  GenericExpressionMeaning.ResultRepresents model finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧ PostAdmission bridge context compiler.original.type outcome reached

include rawResult nativeResult in
private theorem parent_result {finalMap : LocationMap} {finalWorld : StoreTyping}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (related : FunctionCalls.ResultRepresents model finalMap finalWorld function.resultType resultCore faults outcome value) :
    GenericExpressionMeaning.ResultRepresents model finalMap finalWorld compiler.original.type lowered.type faults outcome value := by
  exact ForModel.parent_result functions compiler rawResult nativeResult related

include stages caller sidecarSource unique in
private theorem actual_selected :
    CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row := by
  have contains : ContainsExpression sidecar.source prepared.site.call compiler.original := by
    rw [sidecarSource, prepared.call]
    exact lookupExpression?_sound compiler.found
  exact CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages prepared.table caller
    contains compiler.originalForm (sidecarSource ▸ unique) dispatch.found

include association binderCount in
private theorem actual_arity : function.parameters.length = ids.length :=
  (Association.binding_count association).symm.trans binderCount.symm

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata association heaps binderCount sourceBundle nativeBundle
  rawResult nativeResult stages caller sidecarSource dispatch accepted calleeTrace calleeEvaluation in
/-- A real successful callee post feeds ordered admitted arguments, the exact
parameter continuation and the original whole call. Only strict child IH remains. -/
theorem preserves_selected (budget : Nat)
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
      ResultAt (registry := registry) (faults := faults) (context := context) bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  apply ForModel.preserves_selected_with_application bridge functions compiler prepared parent tree unique parentTyped
    wellFormed runtime covers environments locals agrees typed first firstAdmission calleeState calleeRelated
    calleeMaps calleeWorlds calleeFrame calleeMetadata (Association.native_typed association) heaps rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation
    (actual_selected compiler prepared unique stages caller sidecarSource dispatch) budget children suffix argumentsWithin callWithin
  intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
    argumentState argumentAdmission maps worlds frame metadata calleeTyped extension representedValues
    middleHeaps rawTyped packing bundle argumentsSize callSize outcome after argumentsTrace called _sameSuffix callWithin
  have nativeCount : (compiler.codes.map (·.type)).length = bindings.length := by
    simpa only [List.length_map] using compiler.ordered_children.1.symm.trans binderCount
  have valuesCount : _ = bindings.length := representedValues.length.1.symm.trans nativeCount
  have representedArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles bindings representedValues
    valuesCount sourceBundle nativeBundle
  have future := association.extend maps worlds
  have rawArity := arity_of_association future representedArguments
  obtain ⟨result, finalStore, evaluated, finalMap, finalWorld, resultRep, finalHeaps, lastMaps, lastWorlds,
      lastFrame, lastMetadata, _baseReached, _baseRelated, _stable, returned, _samePool, lastRelated⟩ :=
    CallableIndexedOwnedAdmittedStoredClosureInvocation.preserves_at bridge functions wellFormed runtime future
      argumentState argumentAdmission calleeTyped extension representedArguments middleHeaps rawTyped packing bundle
      rawArity budget below called callWithin
  exact ⟨result, finalStore, finalMap, finalWorld,
    application_gate dispatch (actual_selected compiler prepared unique stages caller sidecarSource dispatch)
      (actual_arity association binderCount) native.diagnostics.unknown,
    evaluated, resultRep, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, lastRelated⟩

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata association heaps binderCount sourceBundle nativeBundle
  rawResult nativeResult stages caller sidecarSource dispatch accepted calleeTrace calleeEvaluation in
/-- The real fourth-bind application bound invokes the unchanged body budget.
The reflected Source parent keeps its independent grade and actual caller post. -/
theorem reflects_selected (budget : Nat)
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
      ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨parameter, sourceResult, rawTypes, calleeTyping, argumentsTyping, application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  obtain ⟨calleeTyped, calleeHeapTyped, _calleeExtension⟩ :=
    wellFormed.wholeLanguagePreservation.expression context evidence source environment before calleeHeap callee
      (.closure function) (.function parameter sourceResult) runtime covers locals firstAdmission.heap calleeTyping calleeTrace.sound
  have calleeAdmission : Admission bridge context calleeState :=
    ⟨calleeHeapTyped, StableRows.after_administrative (bridge.pool first) (bridge.pool calleeState) firstAdmission.rows calleeFrame⟩
  have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
  have selected := actual_selected compiler prepared unique stages caller sidecarSource dispatch
  have stage := CallableIndexedOwnedSelectedCallStageAcceptance.before_arguments dispatch accepted native.diagnostics.unknown
  have arity := application_gate dispatch selected (actual_arity association binderCount) native.diagnostics.unknown
  have emitted := prepared.lowered_rename compiler ξ
  rw [nativeResult] at emitted
  rw [emitted] at completed
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons (Association.native_typed association) (typed.weaken calleeWorlds))
  cases accepted_completed dispatch.shape calleeEvaluation stage arity completed within with
  | failed argumentsTrace smaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, argumentsOutcome, after, finalMap, finalWorld, sourceArguments, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | fault matched =>
      cases sourceArguments with
      | fault failed =>
        obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
          argumentsTyping count calleeTrace (SourceSuffix.argumentFault failed)
        exact ⟨sourceSize, _, after, finalMap, finalWorld, original,
          parent_result profile compiler rawResult nativeResult (.fault matched), finalHeaps,
          calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans metadata,
          reached, callerProtocol.trans calleeRelated related,
          after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (calleeFrame.trans frame)⟩
  | applied argumentsTrace applicationTrace smaller applicationSmaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, argumentsOutcome, middle, middleMap, middleWorld, sourceArguments, represented, middleHeaps,
        maps, worlds, frame, metadata, argumentState, related, argumentPost⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | values represented =>
      cases sourceArguments with
      | values sourceArguments =>
        have nativeCount : (compiler.codes.map (·.type)).length = bindings.length := by
          simpa only [List.length_map] using compiler.ordered_children.1.symm.trans binderCount
        have valuesCount : _ = bindings.length := represented.length.1.symm.trans nativeCount
        have representedArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles bindings represented
          valuesCount sourceBundle nativeBundle
        have future := association.extend maps worlds
        obtain ⟨packed, packing, rawTyped, _heapTyped, extension, _packedTyped⟩ :=
          after_trace wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped argumentsTyping sourceArguments
        have rawArity := arity_of_association future representedArguments
        obtain ⟨callSize, outcome, after, called, finalMap, finalWorld, resultRep, finalHeaps, lastMaps, lastWorlds,
            lastFrame, lastMetadata, _baseReached, _baseRelated, _stable, returned, _samePool, lastRelated⟩ :=
          CallableIndexedOwnedAdmittedStoredClosureInvocation.reflects_at bridge functions wellFormed runtime future
            argumentState (argumentPost.successful _ rfl) calleeTyped extension representedArguments middleHeaps rawTyped packing
            (empty_bundle application compiler.argumentCoercions) rawArity budget below applicationTrace (Nat.le_of_lt applicationSmaller)
        obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
          argumentsTyping count calleeTrace (SourceSuffix.called sourceArguments called)
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, original,
          parent_result profile compiler rawResult nativeResult resultRep, finalHeaps,
          (calleeMaps.trans maps).trans lastMaps, (calleeWorlds.trans worlds).trans lastWorlds,
          (calleeFrame.trans frame).trans lastFrame, (calleeMetadata.trans metadata).trans lastMetadata,
          returned, callerProtocol.trans (callerProtocol.trans calleeRelated related) lastRelated,
          after_expression_sized first returned firstAdmission wellFormed runtime covers locals parentTyped original
            ((calleeFrame.trans frame).trans lastFrame)⟩
end Selected

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCalleePost
/-! Strict callee children produce their actual value post and complete
shared-model representation. Strong ordinary/principal provenance is inspected
only at that produced post; it is not a completed callee family law. Callee
faults stop at the same real state, before arguments or invocation. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCalleePost
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
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

/-- All fields describe exactly the callee child's real reached witness.
The complete value relation is retained for finite provenance selection. -/
def ValuePost (sourceValue : Dynamic.Value) (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word value) finalStore ∧
  ValueRep compiled.compatible.checked registry functions finalMap finalWorld calleeNode.type sourceValue value compiler.calleeCode.type ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates initial reached ∧ PostAdmission bridge context calleeNode.type (.value sourceValue) reached

include certified found sourceTyped environments locals agrees typed admitted in
/-- The preservation IH constructs the native value and state internally.
No native value, selected association or callee execution is supplied. -/
theorem ForModel.preserves_callee_value
    (functionModel : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (modelHeaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functionModel mapping world before store)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel) context evidence source certificate faults size)
    {size : Nat} {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee sourceValue after)
    (smaller : size < budget) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge functionModel compiler initial
        sourceValue after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children size smaller certified found sourceTyped environments modelHeaps locals agrees typed initial admitted (.value trace)
  cases represented with
  | value represented =>
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩

include certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The preservation IH constructs the native value and state internally.
No native value, selected association or callee execution is supplied. -/
theorem preserves_value (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee sourceValue after)
    (smaller : size < budget) :
    ∃ value finalStore finalMap finalWorld,
      ValuePost (registry := registry) (faults := faults) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge profile compiler initial
        sourceValue after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    ForModel.preserves_callee_value
    (bridge := bridge) (functionModel := functions) (compiler := compiler)
    (certified := certified) (found := found) (sourceTyped := sourceTyped)
    (environments := environments) (modelHeaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    budget children trace smaller
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩

include certified found sourceTyped environments heaps locals agrees typed admitted in
/-- Native reflection recovers the independently sized original callee
trace and the same exact reached value post. -/
theorem reflects_value (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word value) finalStore)
    (smaller : size < budget) :
    ∃ sourceSize sourceValue after finalMap finalWorld,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before callee sourceValue after ∧
      ValuePost (registry := registry) (faults := faults) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge profile compiler initial
        sourceValue after value finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children size smaller certified found sourceTyped environments heaps locals agrees typed initial admitted completed
  cases represented with
  | value represented =>
    cases trace with
    | value trace =>
      exact ⟨sourceSize, _, after, finalMap, finalWorld, trace, completed.sound, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩

/-- At an actual closure post, the observer keeps every rich constructor.
It does not upgrade legacy arbitrary prefixes into strong invocation inputs. -/
theorem ValuePost.selected {function : Dynamic.Closure} {after : Dynamic.Heap} {value : Value} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping}
    (post : ValuePost (registry := registry) (faults := faults) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge profile compiler initial
      (.closure function) after value finalStore finalMap finalWorld) :
    CallableIndexedOwnedObservedGeneralCallee.Selected (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) (mapping := finalMap) (world := finalWorld)
      (raw := calleeNode.type) (function := function) (native := value) (type := compiler.calleeCode.type) :=
  CallableIndexedOwnedObservedGeneralCallee.of_representation profile post.2.1

include compiler in
private theorem source_callee_fault {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (fault : SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee reason after) :
    ∃ parentSize, RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) parentSize
      context evidence source environment before id (.fault reason) after := by
  refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [size]],
    .fault (.form (size_fault := SourceExecutionSize.stepSize [size]) (lookupExpression?_sound compiler.found) ?_)⟩
  rw [compiler.originalForm]
  exact .indirectCallee fault

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments locals agrees typed admitted in
/-- A Source callee fault invokes only its strict child and stops at the
child's actual reached state, before either guard or the arguments. -/
theorem ForModel.preserves_callee_fault
    (functionModel : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (modelHeaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functionModel mapping world before store)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel) context evidence source certificate faults size)
    {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (fault : SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee reason after)
    (smaller : size < budget) :
    ∃ sourceSize token finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id (.fault reason) after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge functionModel compiler initial (.fault reason) after (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    children size smaller certified found sourceTyped environments modelHeaps locals agrees typed initial admitted (.fault fault)
  cases represented with
  | fault matched =>
    obtain ⟨sourceSize, original⟩ := source_callee_fault compiler fault
    have whole := CallableContract.call_callee_failure (result := compiler.resultType)
      (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
      prepared.site.gates native.diagnostics.unknown evaluated
    rw [← prepared.lowered_rename compiler ξ] at whole
    have loweredType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    rw [← loweredType] at whole
    exact ⟨sourceSize, _, finalStore, finalMap, finalWorld, original, whole, .fault matched,
      finalHeaps, maps, worlds, frame, metadata, reached, related,
      after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped original frame⟩

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted in
/-- A Source callee fault invokes only its strict child and stops at the
child's actual reached state, before either guard or the arguments. -/
theorem preserves_fault (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (fault : SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee reason after)
    (smaller : size < budget) :
    ∃ sourceSize token finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id (.fault reason) after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler initial (.fault reason) after (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, token, finalStore, finalMap, finalWorld, original, evaluated,
      represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    ForModel.preserves_callee_fault
    (bridge := bridge) (functionModel := functions) (compiler := compiler) (prepared := prepared)
    (certified := certified) (found := found) (sourceTyped := sourceTyped)
    (parentTyped := parentTyped) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    (environments := environments) (modelHeaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    budget children fault smaller
  exact ⟨sourceSize, token, finalStore, finalMap, finalWorld, original, evaluated,
    represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted in
/-- A native first-bind fault reflects only its exact strict callee child.
The enclosing Source fault has an independent grade and the same post. -/
theorem reflects_fault (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {token : Word} {finalStore : Store}
    (completed : EvaluationSize size actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore)
    (smaller : size < budget) :
    ∃ sourceSize reason after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id (.fault reason) after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler initial (.fault reason) after (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    children size smaller certified found sourceTyped environments heaps locals agrees typed initial admitted completed
  cases represented with
  | fault matched =>
    cases trace with
    | fault failed =>
      obtain ⟨parentSize, original⟩ := source_callee_fault compiler failed
      have whole := CallableContract.call_callee_failure (result := compiler.resultType)
        (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
        prepared.site.gates native.diagnostics.unknown completed.sound
      rw [← prepared.lowered_rename compiler ξ] at whole
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      rw [← loweredType] at whole
      exact ⟨parentSize, _, after, finalMap, finalWorld, original, whole, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, reached, related,
        after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped original frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCalleePost
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageBoundary
/-! A real rejected first-stage guard stops at the actual successful callee
post. Source staging faults retain their own CallBoundary outcome, beside the
unchanged callee admission and cumulative pool effects. Two original bind
inversions preserve the actual native child grades and full parent bound.
There is no argument or body invocation, plain Dynamic fault conversion,
whole-expression law, or recursively staged whole-language claim. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageBoundary
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

/-- The authentic attached guard chooses this exact beforeArguments error. -/
theorem gate_rejected
    {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
    {call : ExpressionId} {ids : List ExpressionId} {sourceValue : Dynamic.Value} {carrier : Value}
    (dispatch : CallStageBoundary.Dispatch frame site call ids sourceValue carrier)
    {reason : Staging.CallGuard.Fault} (rejected : Staging.CallBoundary.GuardRejects frame call ids sourceValue reason)
    (unknown : Word) (actual : Environment) (store : Store) :
    Evaluates (carrier :: actual) store
      (CallableContract.dispatch site.gates .beforeArguments unknown (.second (.var 0)))
      (.inLeft .unit (.word (dispatch.reason reason))) store := by
  have read : Evaluates (carrier :: actual) store (.second (.var 0)) (.word dispatch.contract) store :=
    .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have original := site.dispatch_known .beforeArguments unknown dispatch.contract dispatch.row dispatch.found read
  rw [SourceCoreCallableContracts.reason_rejected dispatch.row site.reasonAt .beforeArguments _ (dispatch.rejected rejected)] at original
  exact original

/-- These are the original two strict children at the exact callee store. -/
def RejectedCompletion (budget : Nat) (site : SourceCoreCallableContracts.Callsite) (unknown : Word)
    (callee : Expr) (actual : Environment) (before calleeStore : Store) (carrier : Value) (token : Word) : Prop :=
  ∃ calleeSize gateSize,
    EvaluationSize calleeSize actual before callee (.inRight .word carrier) calleeStore ∧
    EvaluationSize gateSize (carrier :: actual) calleeStore
      (CallableContract.dispatch site.gates .beforeArguments unknown (.second (.var 0)))
      (.inLeft .unit (.word token)) calleeStore ∧
    calleeSize < budget ∧ gateSize < budget

/-- Finite inversion of the two existing binds fixes the rejected first gate.
The entire supplied native grade remains within its original budget. -/
theorem completed_rejected
    {budget size : Nat} {site : SourceCoreCallableContracts.Callsite} {unknown : Word}
    {callee arguments : Expr} {actual : Environment} {before calleeStore after : Store}
    {carrier value : Value} {token : Word} {result : Ty}
    (calleeEvaluation : Evaluates actual before callee (.inRight .word carrier) calleeStore)
    (gateEvaluation : Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch site.gates .beforeArguments unknown (.second (.var 0)))
      (.inLeft .unit (.word token)) calleeStore)
    (completed : EvaluationSize size actual before
      (CallableContract.call site.gates unknown result callee arguments) value after)
    (within : size ≤ budget) :
    value = .inLeft result (.word token) ∧ after = calleeStore ∧
      RejectedCompletion budget site unknown callee actual before calleeStore carrier token := by
  cases CallableIndirectCallBounds.bind_completed completed within with
  | failed child _ =>
    have same := (evaluation_deterministic child.sound calleeEvaluation).1
    cases same
  | continued child remaining childStrict remainingStrict =>
    obtain ⟨same, stores⟩ := evaluation_deterministic child.sound calleeEvaluation
    cases same
    subst stores
    cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
    | failed gate gateStrict =>
      obtain ⟨same, stores⟩ := evaluation_deterministic gate.sound gateEvaluation
      cases same
      subst stores
      exact ⟨rfl, rfl, _, _, child, gate, childStrict, gateStrict⟩
    | continued gate _ _ _ =>
      have same := (evaluation_deterministic gate.sound gateEvaluation).1
      cases same

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
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {sourceValue : Dynamic.Value} {calleeNative : Value}
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge functionModel compiler first
    sourceValue calleeHeap calleeNative store mapping world)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue calleeNative)
  {reason : Staging.CallGuard.Fault}
  (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) prepared.site.call ids sourceValue reason)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee sourceValue calleeHeap)

/-- The complete original value post remains beside the genuine staged fault.
It is the callee's admission, not a plain Dynamic parent fault admission. -/
def ResultAt (reason : Staging.CallGuard.Fault) (token : Word) (finalStore : Store) : Prop :=
  SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
  sidecar.source = source ∧
  CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge functionModel compiler first
    sourceValue calleeHeap calleeNative store mapping world ∧
  SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee sourceValue calleeHeap ∧
  Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
    context evidence source environment before id callee ids metadata (.stageFault reason) calleeHeap ∧
  token = dispatch.reason reason ∧ CallStageBoundary.ReasonRepresents prepared.site reason token ∧
  finalStore = store ∧
  Evaluates actual firstStore (lowered.expression.rename ξ)
    (.inLeft compiler.resultType (.word token)) finalStore

include caller sidecarSource post rejected calleeTrace in
/-- The actual Source stage rejection emits its first-gate word at the same
callee pool, before any argument or body computation. -/
theorem preserves_rejected :
    ResultAt (registry := registry) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize) bridge functionModel compiler prepared first dispatch reason (dispatch.reason reason) store := by
  have failed := dispatch.rejected rejected
  have calleeEvaluation := post.1
  rw [dispatch.shape] at calleeEvaluation
  have whole := prepared.site.lower_stage_failure (result := compiler.resultType)
    (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) native.diagnostics.unknown dispatch.row
    (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason)
    dispatch.found failed calleeEvaluation
  have original : Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
      context evidence source environment before id callee ids metadata (.stageFault reason) calleeHeap :=
    .stageRejected calleeTrace.sound (by simpa only [prepared.call] using rejected)
  refine ⟨caller, sidecarSource, post, calleeTrace, original, rfl, dispatch.reason_represents reason, rfl, ?_⟩
  simpa only [SourceCoreCallableContracts.Callsite.lower, CallStageBoundary.Dispatch.reason, prepared.lowered_rename compiler ξ] using whole

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
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {sourceValue : Dynamic.Value} {calleeNative : Value}
  (post : CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge profile compiler first
    sourceValue calleeHeap calleeNative store mapping world)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue calleeNative)
  {reason : Staging.CallGuard.Fault}
  (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) prepared.site.call ids sourceValue reason)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee sourceValue calleeHeap)

/-- The complete original value post remains beside the genuine staged fault.
It is the callee's admission, not a plain Dynamic parent fault admission. -/
def ResultAt (reason : Staging.CallGuard.Fault) (token : Word) (finalStore : Store) : Prop :=
  SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
  sidecar.source = source ∧
  CallableIndexedOwnedStoredIndirectCalleePost.ValuePost (registry := registry) (faults := faults)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge profile compiler first
    sourceValue calleeHeap calleeNative store mapping world ∧
  SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee sourceValue calleeHeap ∧
  Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
    context evidence source environment before id callee ids metadata (.stageFault reason) calleeHeap ∧
  token = dispatch.reason reason ∧ CallStageBoundary.ReasonRepresents prepared.site reason token ∧
  finalStore = store ∧
  Evaluates actual firstStore (lowered.expression.rename ξ)
    (.inLeft compiler.resultType (.word token)) finalStore

include caller sidecarSource post rejected calleeTrace in
/-- The actual Source stage rejection emits its first-gate word at the same
callee pool, before any argument or body computation. -/
theorem preserves_rejected :
    ResultAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize) bridge profile compiler prepared first dispatch reason (dispatch.reason reason) store := by
  exact ForModel.preserves_rejected bridge
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile) compiler prepared first post
    caller sidecarSource dispatch rejected calleeTrace

include caller sidecarSource post rejected calleeTrace in
/-- A real bounded native completion reflects the exact same staged fault and
callee post while retaining both original strict native child bounds. -/
theorem reflects_rejected (budget : Nat) {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ token, value = .inLeft compiler.resultType (.word token) ∧
      ResultAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize) bridge profile compiler prepared first dispatch reason token finalStore ∧
      RejectedCompletion budget prepared.site native.diagnostics.unknown (compiler.calleeCode.expression.rename ξ)
        actual firstStore store calleeNative token := by
  have exactGate := gate_rejected dispatch rejected native.diagnostics.unknown actual store
  have full := completed
  rw [prepared.lowered_rename compiler ξ] at full
  obtain ⟨same, storeEq, bounds⟩ := completed_rejected post.1 exactGate full within
  subst finalStore
  exact ⟨dispatch.reason reason, same,
    preserves_rejected bridge profile compiler prepared first post caller sidecarSource dispatch rejected calleeTrace, bounds⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageBoundary
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallForModelReflection
/-! Finite accepted stored-call reflection for an arbitrary authenticated receiving
model. The actual callee Association and ordered argument bundles feed the original
model-generic payload invocation once. Only genuine strict expression/body IH is
required. ResultAt retains that model's result and heap at the same returned caller,
with raw Source admission derived from the reconstructed whole Source trace.
This endpoint does not close any child family, classify arbitrary callees, recover
strong payloads from the erased model or retain a discarded body-state witness. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallForModelReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedStoredClosureInvocation (Association)
open CallableIndexedOwnedStoredClosureArgumentReceipts
open CallableIndexedOwnedStoredIndirectCallBounds
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

section Selected
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
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
  (calleeState : callerProtocol.State ⟨scope, mapping, world, calleeHeap, store, canonical⟩)
  (calleeRelated : callerProtocol.Relates first calleeState)
  (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
  (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
  (calleeMetadata : Dynamic.HeapMetadataExtend before calleeHeap)
  {function : Dynamic.Closure} {calleeNative : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (association : Association headers keys registry faults mapping world function calleeNative bindings parameterCore resultCore)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world calleeHeap store)
  (binderCount : ids.length = bindings.length)
  (sourceBundle : TypeSystem.Ty.productMany sourceTypes = TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)))
  (nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
    SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType)
  (nativeResult : compiler.resultType = resultCore)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word calleeNative) store)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include association binderCount sourceBundle nativeBundle wellFormed runtime in
/-- The exact ordered bundle at the actual argument post supplies the original
receiving-model payload invocation. Its body obligation is only strict same-family
IH. The selected callee association is extended along the real map and world. -/
theorem application_reflects_of_bundles (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {middleMap : LocationMap} {middleWorld : StoreTyping} {middle : Dynamic.Heap} {middleStore : Store}
    {arguments : List Dynamic.Value} {payloads : List Value} {types : List TypeSystem.Ty}
    {parameter sourceResult : TypeSystem.Ty} {packed : Dynamic.Value}
    (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩)
    (argumentAdmission : Admission bridge context argumentState)
    (maps : LocationMap.Extends mapping middleMap) (worlds : WorldExtends world middleWorld)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter sourceResult))
    (extension : Dynamic.HeapTypesExtend calleeHeap middle)
    (represented : DataExpressionSequence.Values model middleMap middleWorld sourceTypes
      (compiler.codes.map (·.type)) arguments payloads)
    (middleHeaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      middleMap middleWorld middle middleStore)
    (rawTyped : Dynamic.ValuesHaveTypes context middle arguments types)
    (packing : Dynamic.ValuesPack arguments packed)
    (bundle : TypeSystem.Ty.productMany types = parameter)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [calleeNative, DataPatternValues.packValues payloads] middleStore
      CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ callSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize
        context evidence function.evidence middle (.closure function) arguments outcome after ∧
      CallableIndexedOwnedStoredClosureInvocation.CallerResultAt
        (registry := registry) (faults := faults) functions bridge argumentState
        function resultCore outcome after value finalStore := by
  have nativeCount : (compiler.codes.map (·.type)).length = bindings.length := by
    simpa only [List.length_map] using compiler.ordered_children.1.symm.trans binderCount
  have valuesCount : _ = bindings.length := represented.length.1.symm.trans nativeCount
  have representedArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    bindings represented valuesCount sourceBundle nativeBundle
  have future := association.extend maps worlds
  have rawArity := arity_of_association future representedArguments
  exact CallableIndexedOwnedAdmittedStoredClosureInvocation.reflects_at bridge functions wellFormed runtime future
    argumentState argumentAdmission calleeTyped extension representedArguments middleHeaps rawTyped packing
    bundle rawArity budget below completed within

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata association heaps binderCount sourceBundle nativeBundle
  rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation in
/-- The original finite whole-call inversion retains independent Source/native
grades. Argument faults keep the actual child post; successful arguments call the
receiving-model payload reflector once at their genuine reached state. -/
theorem reflects_selected
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar prepared.site callee ids metadata compiler.original dispatch.row)
    (budget : Nat)
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
      CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ResultAt
        (registry := registry) (faults := faults) (context := context)
        bridge functions compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨parameter, sourceResult, rawTypes, calleeTyping, argumentsTyping, application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  obtain ⟨calleeTyped, calleeHeapTyped, _calleeExtension⟩ :=
    wellFormed.wholeLanguagePreservation.expression context evidence source environment before calleeHeap callee
      (.closure function) (.function parameter sourceResult) runtime covers locals firstAdmission.heap calleeTyping calleeTrace.sound
  have calleeAdmission : Admission bridge context calleeState :=
    ⟨calleeHeapTyped, StableRows.after_administrative (bridge.pool first) (bridge.pool calleeState) firstAdmission.rows calleeFrame⟩
  have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
  have stage := CallableIndexedOwnedSelectedCallStageAcceptance.before_arguments dispatch accepted native.diagnostics.unknown
  have arity := application_gate dispatch selected ((Association.binding_count association).symm.trans binderCount.symm) native.diagnostics.unknown
  have emitted := prepared.lowered_rename compiler ξ
  rw [nativeResult] at emitted
  rw [emitted] at completed
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons (Association.native_typed association) (typed.weaken calleeWorlds))
  cases accepted_completed dispatch.shape calleeEvaluation stage arity completed within with
  | failed argumentsTrace smaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, argumentsOutcome, after, finalMap, finalWorld, sourceArguments, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | fault matched =>
      cases sourceArguments with
      | fault failed =>
        obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
          argumentsTyping count calleeTrace (SourceSuffix.argumentFault failed)
        exact ⟨sourceSize, _, after, finalMap, finalWorld, original,
          CallableIndexedOwnedStoredIndirectCallBounds.ForModel.parent_result functions compiler rawResult nativeResult (.fault matched), finalHeaps,
          calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans metadata,
          reached, callerProtocol.trans calleeRelated related,
          after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (calleeFrame.trans frame)⟩
  | applied argumentsTrace applicationTrace smaller applicationSmaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, argumentsOutcome, middle, middleMap, middleWorld, sourceArguments, represented, middleHeaps,
        maps, worlds, frame, metadata, argumentState, related, argumentPost⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | values represented =>
      cases sourceArguments with
      | values sourceArguments =>
        obtain ⟨packed, packing, rawTyped, _heapTyped, extension, _packedTyped⟩ :=
          after_trace wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped argumentsTyping sourceArguments
        obtain ⟨callSize, outcome, after, called, finalMap, finalWorld, resultRep, finalHeaps, lastMaps, lastWorlds,
            lastFrame, lastMetadata, _baseReached, _baseRelated, _stable, returned, _samePool, lastRelated⟩ :=
          application_reflects_of_bundles (bridge := bridge) (functions := functions) (compiler := compiler)
            (association := association) (binderCount := binderCount) (sourceBundle := sourceBundle)
            (nativeBundle := nativeBundle) (wellFormed := wellFormed) (runtime := runtime)
            budget below argumentState (argumentPost.successful _ rfl) maps worlds
            calleeTyped extension represented middleHeaps rawTyped packing
            (empty_bundle application compiler.argumentCoercions) applicationTrace (Nat.le_of_lt applicationSmaller)
        obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
          argumentsTyping count calleeTrace (SourceSuffix.called sourceArguments called)
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, original,
          CallableIndexedOwnedStoredIndirectCallBounds.ForModel.parent_result functions compiler rawResult nativeResult resultRep, finalHeaps,
          (calleeMaps.trans maps).trans lastMaps, (calleeWorlds.trans worlds).trans lastWorlds,
          (calleeFrame.trans frame).trans lastFrame, (calleeMetadata.trans metadata).trans lastMetadata,
          returned, callerProtocol.trans (callerProtocol.trans calleeRelated related) lastRelated,
          after_expression_sized first returned firstAdmission wellFormed runtime covers locals parentTyped original
            ((calleeFrame.trans frame).trans lastFrame)⟩
end Selected
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallForModelReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCalleeSuccess
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageDiagnostics
/-! Actual public native presence supplies the same sealed callable diagnostic
factory. Only the genuine rejected beforeArguments row is interpreted; its
stage fault remains distinct from plain Dynamic faults. The complete boundary
receipt, callee pool and cumulative effects are retained unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageDiagnostics
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {sidecar : SourceCoreStageContracts.Sidecar} {sourceValue : Dynamic.Value} {calleeNative : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue calleeNative)
  {reason : Staging.CallGuard.Fault}
  (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) prepared.site.call ids sourceValue reason)
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)

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

include rejected stages in
/-- The actual public factory decodes the exact rejected first-gate token. -/
theorem stage_diagnostic :
    ∃ diagnostic, native.diagnostics.rootTable.diagnostic? (dispatch.reason reason) = some diagnostic ∧
      diagnostic.error = CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason := by
  obtain ⟨_diagnostics, _cached, _callableCached, generated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have decoded := CallableFaultDiagnosticPreparation.prepared_before_arguments generated
    (actual_member compiler prepared dispatch) (dispatch.rejected rejected)
  simpa only [CallStageBoundary.Dispatch.reason, issued_reason prepared.prepared] using decoded

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {calleeSize : Nat}

include rejected stages in
/-- The entire staged result is retained verbatim beside its real table
observation; no semantic fault representation is invented. -/
theorem decoded_result {token : Word} {finalStore : Store}
    (result : CallableIndexedOwnedStoredIndirectStageBoundary.ResultAt
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize)
      bridge profile compiler prepared first dispatch reason token finalStore) :
    CallableIndexedOwnedStoredIndirectStageBoundary.ResultAt
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize)
      bridge profile compiler prepared first dispatch reason token finalStore ∧
    ∃ diagnostic, native.diagnostics.rootTable.diagnostic? token = some diagnostic ∧
      diagnostic.error = CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason := by
  obtain ⟨diagnostic, decoded, error⟩ := stage_diagnostic compiler prepared dispatch rejected stages
  exact ⟨result, diagnostic, result.2.2.2.2.2.1.symm ▸ decoded, error⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectStageDiagnostics
end
