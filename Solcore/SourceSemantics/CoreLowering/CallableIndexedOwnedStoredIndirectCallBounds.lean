import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStoredClosureInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedObservedGeneralCallee
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredCallSourcePrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallStageAcceptance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredApplicationProjection

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
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  rw [loweredType, nativeResult]
  cases related with
  | value payload => exact .value (.compatible rawResult payload)
  | fault matched => exact .fault matched

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
  have selected := actual_selected compiler prepared unique stages caller sidecarSource dispatch
  have stage := CallableIndexedOwnedSelectedCallStageAcceptance.before_arguments dispatch accepted native.diagnostics.unknown
  have arity := application_gate dispatch selected (actual_arity association binderCount) native.diagnostics.unknown
  have emitted := prepared.lowered_rename compiler ξ
  rw [nativeResult] at emitted
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons (Association.native_typed association) (typed.weaken calleeWorlds))
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
      parent_result profile compiler rawResult nativeResult (.fault matched), finalHeaps,
      calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans metadata,
      reached, callerProtocol.trans calleeRelated related,
      after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (calleeFrame.trans frame)⟩
  | called argumentsTrace called =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentEvaluation, represented, middleHeaps,
        maps, worlds, frame, metadata, argumentState, related, argumentAdmission⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_values_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace argumentsWithin
    have nativeCount : (compiler.codes.map (·.type)).length = bindings.length := by
      simpa only [List.length_map] using compiler.ordered_children.1.symm.trans binderCount
    have valuesCount : _ = bindings.length := represented.length.1.symm.trans nativeCount
    have representedArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles bindings represented
      valuesCount sourceBundle nativeBundle
    have future := association.extend maps worlds
    obtain ⟨packed, packing, rawTyped, _heapTyped, extension, _packedTyped⟩ :=
      after_trace wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped argumentsTyping argumentsTrace
    have rawArity := arity_of_association future representedArguments
    obtain ⟨result, finalStore, evaluated, finalMap, finalWorld, resultRep, finalHeaps, lastMaps, lastWorlds,
        lastFrame, lastMetadata, _baseReached, _baseRelated, _stable, returned, _samePool, lastRelated⟩ :=
      CallableIndexedOwnedAdmittedStoredClosureInvocation.preserves_at bridge functions wellFormed runtime future
        argumentState argumentAdmission calleeTyped extension representedArguments middleHeaps rawTyped packing
        (empty_bundle application compiler.argumentCoercions) rawArity budget below called callWithin
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentEvaluation
    have whole := call_payload_success (resultType := resultCore) dispatch.shape calleeEvaluation stage
      argumentEvaluation arity evaluated
    rw [← emitted] at whole
    exact ⟨sourceSize, result, finalStore, finalMap, finalWorld, original, whole,
      parent_result profile compiler rawResult nativeResult resultRep, finalHeaps,
      (calleeMaps.trans maps).trans lastMaps, (calleeWorlds.trans worlds).trans lastWorlds,
      (calleeFrame.trans frame).trans lastFrame, (calleeMetadata.trans metadata).trans lastMetadata,
      returned, callerProtocol.trans (callerProtocol.trans calleeRelated related) lastRelated,
      after_expression_sized first returned firstAdmission wellFormed runtime covers locals parentTyped original
        ((calleeFrame.trans frame).trans lastFrame)⟩

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
