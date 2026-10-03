import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLoopContracts
import Solcore.SourceSemantics.CoreLowering.NamedForFunctionFallthrough
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForControlShape
import Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBodyMeaning

/-! The actual function finish consumes the original measured flow. Source
body and flow witnesses have the same source grade; native finish inversion
selects a strict original flow child. Reflection constructs its independent
source grade, retaining the reached lexical exit and protected outer entry.
The flow meaning is an explicit pointwise premise for catalog mutual induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedLoopContracts (ExecutesAt)
open RecursiveNamedCallBounds (BodyTrace)

/-- The wrapper adds no source execution step: every case retains the same
measured function-statement witness and its distinct source call exit. -/
theorem trace_flow {program : Program} {size : Nat} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ finalContext control,
      ExecutesAt size true program context function.evidence function.source environment before function.body finalContext control after ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
  cases trace with
  | returned trace => exact ⟨_, _, .control trace, .returned _⟩
  | unit same trace => exact ⟨_, _, .control trace, .unit _ same⟩
  | fault failed => exact ⟨_, _, .fault failed, .fault _⟩
  | escaped trace escape =>
    rcases escape with ⟨next, rfl⟩ | ⟨next, rfl⟩
    · exact ⟨_, _, .control trace, .breaking next⟩
    · exact ⟨_, _, .control trace, .continuing next⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {type : Ty} {flow code : Expr}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word}
  (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope function.body
    type reasonAt fellThrough escaped = .ok code)
  (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope function.body
    type reasonAt true escaped = .ok flow)
  (tree : GenericImperativeFor.Tree layouts owner active frameLayout globals onError values function.source
    expressionSyntax certificates ambient.definitions administrative context scope
    (.statements true function.body) function.resultType type flow)
  (projection : values.checked.catalog.project function.resultType = .ok type)
  (unique : NodeOccurrencesUnique function.source)
  {faults : FunctionCalls.FaultRep} (escapedFault : faults .controlEscapedFunction escaped)
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include accepted generated in
private theorem emitted : code = CompatibleStatements.finish type flow fellThrough escaped := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  rw [generated] at accepted
  exact Except.ok.inj accepted.symm

include accepted generated tree projection unique escapedFault transport in
theorem preserves_at (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program function.evidence
      (source := function.source) (context := context) (registry := registry) (solved := solved) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  obtain ⟨finalContext, control, trace, exit⟩ := trace_flow trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped installed trace
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow functions (fun next same => by
    cases same
    exact NamedForFunctionFallthrough.true_fallthrough_unit tree unique trace.sound)
    projection fellThrough escaped escapedFault represented evaluated
  have evaluated : Evaluates actual store (code.rename ξ) result finalStore := by
    rw [emitted accepted generated, ImperativeFunctionFinish.rename]
    exact completed
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, ImperativeFunctionFinish.result related exit,
    finalHeaps, maps, worlds, frame, metadata, ⟨finalContext, control, trace.sound, exit, lexical⟩,
    transport.extend installed maps worlds frame metadata⟩

include accepted generated tree projection unique escapedFault transport in
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAt (entry := entry) functions program function.evidence
        (source := function.source) (context := context) (registry := registry) (solved := solved) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  rw [emitted accepted generated, ImperativeFunctionFinish.rename] at evaluated
  obtain ⟨flowSize, flowValue, middleStore, smaller, flowEval⟩ := RecursiveNamedCallBounds.finish_flow evaluated
  obtain ⟨sourceSize, finalContext, control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    meaning flowSize (Nat.lt_of_lt_of_le smaller within) valid
      environments heaps locals agrees typed reference read unmapped installed flowEval
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow functions (fun next same => by
    cases same
    exact NamedForFunctionFallthrough.true_fallthrough_unit tree unique trace.sound)
    projection fellThrough escaped escapedFault represented flowEval.sound
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound completed
  have sourceResult : ∃ outcome, BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
    generalize raw : function.resultType = expected at related
    cases related with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed => exact ⟨_, .unit raw executed, .value .unit, .unit _ rfl⟩
    | returned payload =>
      cases trace with
      | control executed => exact ⟨_, .returned executed, .value payload, .returned _⟩
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (tree.control_not_fault unique executed.sound)
      | fault failed => exact ⟨_, .fault failed, .fault matched, .fault _⟩
    | breaking finalEnvironment matched =>
      cases trace with
      | control executed => exact ⟨_, .escaped executed (.inl ⟨_, rfl⟩), .fault matched, .breaking _⟩
    | continuing finalEnvironment matched =>
      cases trace with
      | control executed => exact ⟨_, .escaped executed (.inr ⟨_, rfl⟩), .fault matched, .continuing _⟩
  obtain ⟨outcome, bodyTrace, represented, exit⟩ := sourceResult
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, bodyTrace, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨finalContext, control, trace.sound, exit, lexical⟩, transport.extend installed maps worlds frame metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
