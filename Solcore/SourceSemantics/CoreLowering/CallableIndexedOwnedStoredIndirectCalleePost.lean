import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallBounds

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
    children size smaller certified found sourceTyped environments heaps locals agrees typed initial admitted (.value trace)
  cases represented with
  | value represented =>
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
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
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    children size smaller certified found sourceTyped environments heaps locals agrees typed initial admitted (.fault fault)
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
