import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion

/-! Conditional heads use the actual staged condition and selected arm. The
outer statement fold owns fallthrough sequencing and restores its original
lexical context while retaining the arm's heap and captured cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalSequences
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
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode}
  {left : List StatementId} {right : Option (List StatementId)}
  {expected : TypeSystem.Ty} {type : Ty} {testCode leftCode rightCode : Expr}

variable {mode : Bool} {id : StatementId} {statement : StatementNode}
  {rest : List StatementId} {body : Expr}

include bridge functions condition in
theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → ReflectsAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (leftCorrect : BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope left expected type leftCode budget)
    (rightCorrect : BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope (right.getD []) expected type rightCode budget)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .ifThen test left right)
    (remaining : FlowReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope mode rest expected type body budget ∨
      (NodeOccurrencesUnique invocation.source ∧ GenericLexicalStatements.Stopped invocation.source left ∧
        GenericLexicalStatements.Stopped invocation.source (right.getD [])))
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
    (completed : EvaluationSize size actual store ((LocalLoop.sequence type (LocalLoop.conditional type testCode leftCode rightCode) body).rename ξ) value finalStore) :
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
    CallableIndexedOwnedAdmittedStagedConditionalHeads.reflects bridge functions condition children
      found nodeType typed generated leftCorrect rightCorrect (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted headEval
  cases represented with
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      cases headTrace with
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifReturned (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
            middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      cases headTrace with
      | fault testTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifConditionFault (lookupStatement?_sound statementFound) form testTrace,
            .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
            middleState, headRelated, headPost⟩
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifFault (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
            middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      cases headTrace with
      | @branch testSize branchSize truth tested innerContext outcome after testTrace branchTrace =>
        rcases remaining with remaining | ⟨unique, leftStops, rightStops⟩
        · obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
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
            .ifFallthrough (lookupStatement?_sound statementFound) form testTrace branchTrace tailTrace,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans framePreserved, firstMetadata.trans metadata, reached,
            callerProtocol.trans headRelated tailRelated, post⟩
        · have stopped : GenericLexicalStatements.Stopped invocation.source (if truth then left else right.getD []) := by
            cases truth <;> assumption
          exact False.elim (CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.stopped_not_fallthrough unique stopped branchTrace)

include bridge functions condition in
theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → PreservesAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (leftCorrect : BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope left expected type leftCode budget)
    (rightCorrect : BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope (right.getD []) expected type rightCode budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .ifThen test left right)
    (remaining : FlowPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope mode rest expected type body budget ∨
      (GenericLexicalStatements.Stopped invocation.source left ∧
        GenericLexicalStatements.Stopped invocation.source (right.getD [])))
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
      Evaluates actual store ((LocalLoop.sequence type (LocalLoop.conditional type testCode leftCode rightCode) body).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have finish {headSize : Nat} {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Trace program stages invocation context environment before test left right headSize headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type (LocalLoop.conditional type testCode leftCode rightCode) body).rename ξ) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults headOutcome value ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          callerProtocol.Relates initial reached ∧ Post bridge context expected headOutcome reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, reached, related, post⟩ :=
      CallableIndexedOwnedAdmittedStagedConditionalHeads.preserves bridge functions condition children
        found nodeType typed generated leftCorrect rightCorrect bounded environments heaps locals agrees actualTyped
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
  rcases CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion.children unique statementFound form trace with
    ⟨testSize, failure, sameSize, contextEq, outcomeEq, testTrace⟩ |
    ⟨testSize, branchSize, truth, sourceValue, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, truth, failure, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, tailSize, truth, middle, branchHeap, innerContext, innerEnvironment, sameSize, testTrace, branchTrace, tailTrace⟩
  · subst outcome
    exact finish (.fault testTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · rcases remaining with remaining | ⟨leftStops, rightStops⟩
    · have headWithin : Staging.Recursive.Size.stepSize [testSize, branchSize] ≤ budget := by
        rw [sameSize] at within
        simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within ⊢
        omega
      obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
          maps, worlds, preservation, metadata, middleState, headRelated, headPost⟩ :=
        CallableIndexedOwnedAdmittedStagedConditionalHeads.preserves bridge functions condition children
          found nodeType typed generated leftCorrect rightCorrect headWithin environments heaps locals agrees actualTyped
          reference read unmapped initial conditioned admitted (.branch testTrace branchTrace)
      cases represented with
      | fallthrough innerEnvironment _ =>
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
    · have stopped : GenericLexicalStatements.Stopped invocation.source (if truth then left else right.getD []) := by
        cases truth <;> assumption
      exact False.elim (CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.stopped_not_fallthrough unique stopped branchTrace)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalSequences
