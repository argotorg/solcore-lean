import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceInversion

/-! Finite staged loops compose with the actual following statements.
Loop completion restores the original lexical context and environment while
retaining every iteration's heap effects and captured cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileSequences
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CompatibleExpressionPrimitives (bool_fields)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

open CallableIndexedOwnedAdmittedStagedConditionalHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode}
  {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode : Expr} {selfReason : Word}

variable {mode : Bool} {id : StatementId} {statement : StatementNode}
  {rest : List StatementId} {body : Expr}

private theorem fallthrough_environment {program : Program} {stages : Staging.Recursive.Registry}
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {environment innerEnvironment : Dynamic.Environment} {condition : ExpressionId} {statements : List StatementId}
    {size : Nat} {before after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.While program stages size invocation context environment before condition statements
      (.fallthrough innerEnvironment) after) : innerEnvironment = environment := by
  induction size using Nat.strongRecOn generalizing before after with
  | ind size ih =>
    cases trace with
    | done => rfl
    | next test body next =>
      exact ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp)) next

include bridge functions condition transport in
theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → ReflectsAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (correct : BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope statements expected type loopCode budget)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .whileLoop test statements)
    (remaining : FlowReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope mode rest expected type body budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store ((LocalLoop.sequence type (LocalLoop.whileLoop type testCode loopCode selfReason) body).rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages mode sourceSize invocation context environment before
        (id :: rest) finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, headRelated, headPost⟩ :=
    CallableIndexedOwnedAdmittedStagedWhileHeads.reflects bridge functions condition transport children
      found nodeType typed generated nativeTyped correct (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted headEval
  cases represented with
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .whileReturned (lookupStatement?_sound statementFound) form headTrace,
        .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
        middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .whileFault (lookupStatement?_sound statementFound) form headTrace,
        .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
        middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      have same := fallthrough_environment headTrace
      subst innerEnvironment
      obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
      obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented,
          finalHeaps, maps, worlds, framePreserved, metadata, reached, tailRelated, post⟩ :=
        remaining (Nat.le_trans (Nat.le_of_lt smaller) within)
          (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken firstWorlds)))) reference
          ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState conditioned headPost
          (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
      exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
        .whileFallthrough (lookupStatement?_sound statementFound) form headTrace tailTrace,
        represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans framePreserved, firstMetadata.trans metadata, reached,
        callerProtocol.trans headRelated tailRelated, post⟩

include bridge functions condition transport in
theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → PreservesAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (correct : BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope statements expected type loopCode budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .whileLoop test statements)
    (remaining : FlowPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope mode rest expected type body budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.StatementsIn program stages mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.sequence type (LocalLoop.whileLoop type testCode loopCode selfReason) body).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have finish {headSize : Nat} {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Staging.Recursive.Size.While program stages headSize invocation context environment before test statements headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type (LocalLoop.whileLoop type testCode loopCode selfReason) body).rename ξ) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults headOutcome value ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          callerProtocol.Relates initial reached ∧ Post bridge context expected headOutcome reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, reached, related, post⟩ :=
      CallableIndexedOwnedAdmittedStagedWhileHeads.preserves bridge functions condition transport children
        found nodeType typed generated nativeTyped correct bounded environments heaps locals agrees actualTyped
        reference read unmapped initial conditioned admitted headTrace
    cases represented with
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedWhileSourceInversion.loop_and_tail unique statementFound form trace with
    ⟨loopSize, sourceValue, sameSize, _contextEq, outcomeEq, loopTrace⟩ |
    ⟨loopSize, failure, sameSize, _contextEq, outcomeEq, loopTrace⟩ |
    ⟨loopSize, tailSize, middle, sameSize, loopTrace, tailTrace⟩
  · subst outcome
    exact finish loopTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (by rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish loopTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (by rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · have headWithin : loopSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
        maps, worlds, preservation, metadata, middleState, headRelated, headPost⟩ :=
      CallableIndexedOwnedAdmittedStagedWhileHeads.preserves bridge functions condition transport children
        found nodeType typed generated nativeTyped correct headWithin environments heaps locals agrees actualTyped
        reference read unmapped initial conditioned admitted loopTrace
    cases represented with
    | fallthrough _ _ =>
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
            lastMaps, lastWorlds, lastFrame, lastMetadata, reached, tailRelated, post⟩ :=
          remaining tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            middleState conditioned headPost tailTrace
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
          metadata.trans lastMetadata, reached, callerProtocol.trans headRelated tailRelated, post⟩
        rw [LoopRenaming.sequence]
        simp only [GenericExpressionMeaning.rename_prefix] at tailEval
        exact LocalLoop.sequence_fallthrough _ headEval tailEval

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileSequences
