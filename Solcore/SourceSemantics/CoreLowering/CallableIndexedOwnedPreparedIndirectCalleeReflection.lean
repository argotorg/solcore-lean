import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCalleePost

/-! The actual strict callee child reflects at the complete function model.
A value retains its original Source trace and reached post. An ordinary child
fault stops the whole indirect call at that same post, before the gates and
arguments. Source and native grades are independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectCalleeReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
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
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge functionModel compiler initial
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
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults) (context := context)
        bridge functionModel compiler initial (.fault reason) after (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld := by
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


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectCalleeReflection
