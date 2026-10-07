import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionReady
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping

/-! Pointwise composition of the existing static heads. Structural children
may use the same budget (group and singleton code are unchanged). Real call
body children remain subject to the separate strict bound of their call leaf.
This layer composes finite obligations; it does not close the recursive Tree. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompositionsBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives CoreProof
open RecursiveNamedBoundedContracts RecursiveNamedCallBounds
open CompatibleExpressionConditionals
open CompatibleExpressionTypedCompositions (Head)


private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId) (first second : SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate := fun current id code =>
  current = scope ∧ ((id = left ∧ code = first) ∨ (id = right ∧ code = second))

private theorem two_tree {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {left right : ExpressionId}
    {leftNode rightNode : ExpressionNode} {first second : SourceCoreBasic.LoweredExpr}
    (leftFound : source.lookupExpression? left = some leftNode)
    (rightFound : source.lookupExpression? right = some rightNode) :
    DataExpressionSequence.Tree source (Two scope left right first second) scope
      [left, right] [leftNode.type, rightNode.type] [first, second] :=
  .cons leftFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ (.single rightFound ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

private theorem pair_result {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {leftType rightType : TypeSystem.Ty}
    {first second : SourceCoreBasic.LoweredExpr} {faults : FunctionCalls.FaultRep}
    {sequence : DataExpressionSequence.Outcome} {value : Value}
    (result : DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world [leftType, rightType] [first, second] faults sequence value) :
    ∃ outcome, CompatibleExpressionProducts.PacksOutcome sequence outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping world (.product leftType rightType) (.product first.type second.type) faults outcome value := by
  cases result with
  | values represented =>
    change DataExpressionSequence.Values _ _ _ [leftType, rightType] [first.type, second.type] _ _ at represented
    cases represented with
    | cons left tail =>
      cases tail with
      | cons right tail =>
        cases tail
        exact ⟨_, .values (.cons (.singleton _)), .value (.product left right)⟩
  | fault matched => exact ⟨_, .fault _, .fault matched⟩


variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}

universe u v
namespace Stateful
open ProtectedStateTransition (Transition)
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)

private def ReflectsRawAt {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate) (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩


/-- The second child starts at the first child's concrete post-witness. -/
private theorem continue_transition {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {initial middle reached : ProtectedStateTransition.Index}
    {state : protocol.State initial} {middleState : protocol.State middle}
    (first : protocol.Relates state middleState)
    (second : Transition protocol middleState reached) :
    Transition protocol state reached := by
  obtain ⟨final, last⟩ := second
  exact ⟨final, protocol.trans first last⟩

namespace WithReady
open ProtectedStateExpressionOperandTyping
variable (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop)

private theorem pair_transition
    {initial final : ProtectedStateTransition.Index} {state : protocol.State initial}
    {sequence : DataExpressionSequence.Outcome} {outcome : Dynamic.ExpressionOutcome}
    (packed : CompatibleExpressionProducts.PacksOutcome sequence outcome)
    (transition : ∃ reached : protocol.State final, protocol.Relates state reached ∧
      ∀ sources, sequence = .ok sources → ready reached) :
    ProtectedStateTransition.WithReady.Reached protocol ready outcome state final := by
  obtain ⟨reached, related, successful⟩ := transition
  refine ⟨reached, related, ?_⟩
  cases packed with
  | values _ => exact fun _ _ => successful _ rfl
  | fault _ => intro value impossible; cases impossible

theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (tree : Head checked source certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.PreservesAt protocol ready
        (CompatibleAmbientHeap.payloadModel checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.WithReady.Reached protocol ready outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning inner (by rw [form]; change inner ∈ [inner]; simp) n bound _ _ _ ⟨rfl, child⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry initialReady trace
    obtain ⟨childSize, childTrace, childSmaller⟩ := RecursiveNamedExpressionSourceBounds.group_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
      ih childSize (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) innerFound environments heaps locals agrees actualTyped installedEntry initialReady childTrace
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have leftIH := fun n (bound : n ≤ budget) => @meaning left (by rw [form]; change left ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, firstTree⟩
    have rightIH := fun n (bound : n ≤ budget) => @meaning right (by rw [form]; change right ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, secondTree⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry initialReady trace
    -- The sequence uses a strict bound; its successor is exactly childSize ≤ budget.
    have children : ∀ childId, childId ∈ [left, right] → ∀ childSize, childSize < budget + 1 → ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionPreservesAt protocol ready childSize (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (fun current expression code => expression = childId ∧ Two scope left right first second current expression code) faults := by
      intro childId member childSize bound
      apply ProtectedStateTransition.WithReady.PreservesAt.to_sequence protocol ready
      intro childScope childId childCode entry
      obtain ⟨sameId, rfl, alternatives⟩ := entry
      subst childId
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH childSize (by omega)
      · exact rightIH childSize (by omega)
    obtain ⟨sequenceSize, sequence, sourceTrace, packed, sequenceSmaller⟩ := RecursiveNamedExpressionSourceBounds.pair_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
      ProtectedDataExpressionSequence.Stateful.WithReady.preserves_bounded protocol ready (budget + 1) (two_tree (first := first) (second := second) leftFound rightFound) children environments heaps locals agrees actualTyped installedEntry initialReady sourceTrace (by omega)
    obtain ⟨actualOutcome, actualPack, payload⟩ := pair_result represented
    have sameOutcome := actualPack.functional packed
    subst actualOutcome
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata, pair_transition protocol ready packed transition⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning operand (by rw [form]; change operand ∈ [operand]; simp) n bound _ _ _ ⟨rfl, child⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have sourceStep := RecursiveNamedExpressionSourceBounds.unary_inv metadata form unique trace
    cases sourceStep with
    | value childTrace applied childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) childFound environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, actualApplied, coreApplied, resultRep⟩ := profile.preserves payload
        have same := actualApplied.functional applied
        subst sourceResult
        refine ⟨.inRight .word result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, ProtectedStateTransition.WithReady.Reached.of_value protocol ready transition _⟩
        · rw [unary_rename]; exact LocalPrimitiveResults.unary_success evaluated coreApplied
        · exact .value (outputType ▸ resultRep)
    | fault childTrace childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) childFound environments heaps locals agrees actualTyped installedEntry initialReady (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [unary_rename]; exact LocalPrimitiveResults.unary_failure evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    | invalid childTrace failed childSmaller =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) childFound environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨_, _, applied, _, _⟩ := profile.preserves payload
        exact False.elim (unary_fault_excluded applied failed)
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have leftIH := fun n (bound : n ≤ budget) => @meaning left (by rw [form]; change left ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, leftTree⟩
    have rightIH := fun n (bound : n ≤ budget) => @meaning right (by rw [form]; change right ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, rightTree⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have sourceStep := RecursiveNamedExpressionSourceBounds.binary_inv metadata form unique trace
    cases sourceStep with
    | leftFault childTrace childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry initialReady (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact mode.left_failure operator evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    | leftInvalid childTrace invalid childSmaller =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := leftIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        exact False.elim (profile.left_valid payload invalid)
    | short childTrace circuit childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit evaluated
        exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
          .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, ProtectedStateTransition.WithReady.Reached.of_value protocol ready transition _⟩
    | rightFault firstTrace continues secondTrace firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt firstSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry initialReady (.value firstTrace)
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
          rightIH _ (Nat.le_trans (Nat.le_of_lt secondSmaller) bounded) rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) (.fault secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact profile.right_failure payload continues first second,
            .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated transition⟩
    | value firstTrace continues secondTrace applied firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt firstSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry initialReady (.value firstTrace)
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
          rightIH _ (Nat.le_trans (Nat.le_of_lt secondSmaller) bounded) rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          obtain ⟨sourceResult, result, actualApplied, resultRep, combined⟩ := profile.right_success leftPayload rightPayload continues first second
          have same := actualApplied.functional applied
          subst sourceResult
          exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
            .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated
              (ProtectedStateTransition.WithReady.Reached.of_value protocol ready transition _)⟩
    | invalid firstTrace continues secondTrace failed firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt firstSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry initialReady (.value firstTrace)
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, _, _, _, second, represented, _, maps, worlds, _⟩ :=
          rightIH _ (Nat.le_trans (Nat.le_of_lt secondSmaller) bounded) rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          obtain ⟨_, _, applied, _, _⟩ := profile.right_success leftPayload rightPayload continues first second
          exact False.elim (binary_fault_excluded applied failed)

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have conditionIH := fun n (bound : n ≤ budget) => @meaning condition (by rw [form]; change condition ∈ [condition, thenId, elseId]; simp) n bound _ _ _ ⟨rfl, conditionTree⟩
    have thenIH := fun n (bound : n ≤ budget) => @meaning thenId (by rw [form]; change thenId ∈ [condition, thenId, elseId]; simp) n bound _ _ _ ⟨rfl, thenTree⟩
    have elseIH := fun n (bound : n ≤ budget) => @meaning elseId (by rw [form]; change elseId ∈ [condition, thenId, elseId]; simp) n bound _ _ _ ⟨rfl, elseTree⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have sourceStep := RecursiveNamedExpressionSourceBounds.conditional_inv metadata form unique trace
    cases sourceStep with
    | fault childTrace childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        conditionIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) conditionFound environments heaps locals agrees actualTyped installedEntry initialReady (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [choose_rename]; exact LocalControl.choose_failure type evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    | @branch conditionSize branchSize flag middle outcome after conditionTrace branchTrace conditionSmaller branchSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        conditionIH _ (Nat.le_trans (Nat.le_of_lt conditionSmaller) bounded) conditionFound environments heaps locals agrees actualTyped installedEntry initialReady (.value conditionTrace)
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
      cases represented with
      | value payload =>
        obtain ⟨actualFlag, sourceEq, coreEq⟩ := bool_fields payload
        cases sourceEq
        subst coreEq
        cases flag with
        | false =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
            elseIH _ (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded) elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated transition⟩
          · rw [choose_rename]; exact LocalControl.choose_false type first branch
          · simpa only [elseType] using represented
        | true =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
            thenIH _ (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded) thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated transition⟩
          · rw [choose_rename]; exact LocalControl.choose_true type first branch
          · simpa only [thenType] using represented
    | invalid childTrace invalid runtimeType childSmaller =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := conditionIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) conditionFound environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨flag, rfl, _⟩ := bool_fields payload
        exact False.elim (invalid trivial)



theorem Head.reflects_raw_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (tree : Head checked source certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.ReflectsAt protocol ready
        (CompatibleAmbientHeap.payloadModel checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.WithReady.Reached protocol ready outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning inner (by rw [form]; change inner ∈ [inner]; simp) n bound _ _ _ ⟨rfl, child⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
      ih size bounded innerFound environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.group_intro metadata form trace.sound, ?_, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have leftIH := fun n (bound : n ≤ budget) => @meaning left (by rw [form]; change left ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, firstTree⟩
    have rightIH := fun n (bound : n ≤ budget) => @meaning right (by rw [form]; change right ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, secondTree⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    -- The sequence uses a strict bound; its successor is exactly childSize ≤ budget.
    have children : ∀ childId, childId ∈ [left, right] → ∀ childSize, childSize < budget + 1 → ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionReflectsAt protocol ready childSize (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (fun current expression code => expression = childId ∧ Two scope left right first second current expression code) faults := by
      intro childId member childSize bound
      apply ProtectedStateTransition.WithReady.ReflectsAt.to_sequence protocol ready
      intro childScope childId childCode entry
      obtain ⟨sameId, rfl, alternatives⟩ := entry
      subst childId
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH childSize (by omega)
      · exact rightIH childSize (by omega)
    obtain ⟨sequenceSize, sequence, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
      ProtectedDataExpressionSequence.Stateful.WithReady.reflects_bounded protocol ready (budget + 1) (two_tree (first := first) (second := second) leftFound rightFound) children environments heaps locals agrees actualTyped installedEntry initialReady evaluated (by omega)
    obtain ⟨outcome, packed, payload⟩ := pair_result represented
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.pair_intro metadata form sourceTrace.sound packed, ?_, finalHeaps, maps, worlds, frame, heapMetadata, pair_transition protocol ready packed transition⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning operand (by rw [form]; change operand ∈ [operand]; simp) n bound _ _ _ ⟨rfl, child⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    rw [unary_rename] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (by omega) childFound environments heaps locals agrees actualTyped installedEntry initialReady childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_failure (operator := core) childEvaluation.sound) complete
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.fault failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (by omega) childFound environments heaps locals agrees actualTyped installedEntry initialReady childEvaluation
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
        obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_success childEvaluation.sound coreApplied) complete
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.value childTrace.sound applied),
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, ProtectedStateTransition.WithReady.Reached.of_value protocol ready transition _⟩
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have leftIH := fun n (bound : n ≤ budget) => @meaning left (by rw [form]; change left ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, leftTree⟩
    have rightIH := fun n (bound : n ≤ budget) => @meaning right (by rw [form]; change right ∈ [left, right]; simp) n bound _ _ _ ⟨rfl, rightTree⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    rw [Mode.binary_rename] at evaluated
    have complete := evaluated.sound
    rw [Mode.binary_eq] at evaluated
    cases evaluated with
    | caseLeft leftEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        leftIH _ (by omega) leftFound environments heaps locals agrees actualTyped installedEntry initialReady leftEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (mode.left_failure operator leftEvaluation.sound)
          exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.leftFault failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    | caseRight leftEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        leftIH _ (by omega) leftFound environments heaps locals agrees actualTyped installedEntry initialReady leftEvaluation
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
      cases represented with
      | @value sourceValue coreValue payload =>
        rw [leftType] at payload
        cases trace with
        | value firstTrace =>
          rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
          · obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit leftEvaluation.sound
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            exact ⟨_, middle, middleMap, middleWorld, binary_intro metadata form (.short firstTrace.sound circuit),
              .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, ⟨middleState, firstRelated, fun _ _ => firstReady _ rfl⟩⟩
          · obtain ⟨rightSize, rightValue, rightStore, rightEvaluation, rightSmaller⟩ := RecursiveNamedExpressionSourceBounds.right_evaluated profile payload continues branch
            have shifted := rightEvaluation
            rw [← GenericExpressionMeaning.rename_prefix] at shifted
            obtain ⟨rightSourceSize, rightOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
              rightIH rightSize (by omega) rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) shifted
            cases represented with
            | fault matched =>
              cases trace with
              | fault failed =>
                have combined := profile.right_failure payload continues leftEvaluation.sound rightEvaluation.sound
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.rightFault firstTrace.sound continues failed.sound),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated transition⟩
            | value rightPayload =>
              rw [rightType] at rightPayload
              have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
              obtain ⟨sourceResult, result, applied, resultRep, combined⟩ :=
                profile.right_success leftPayload rightPayload continues leftEvaluation.sound rightEvaluation.sound
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              cases trace with
              | value secondTrace =>
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.value firstTrace.sound continues secondTrace.sound applied),
                  .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated (ProtectedStateTransition.WithReady.Reached.of_value protocol ready transition _)⟩

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have conditionIH := fun n (bound : n ≤ budget) => @meaning condition (by rw [form]; change condition ∈ [condition, thenId, elseId]; simp) n bound _ _ _ ⟨rfl, conditionTree⟩
    have thenIH := fun n (bound : n ≤ budget) => @meaning thenId (by rw [form]; change thenId ∈ [condition, thenId, elseId]; simp) n bound _ _ _ ⟨rfl, thenTree⟩
    have elseIH := fun n (bound : n ≤ budget) => @meaning elseId (by rw [form]; change elseId ∈ [condition, thenId, elseId]; simp) n bound _ _ _ ⟨rfl, elseTree⟩
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    rw [choose_rename] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        conditionIH _ (by omega) conditionFound environments heaps locals agrees actualTyped installedEntry initialReady childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalControl.choose_failure type childEvaluation.sound)
          exact ⟨_, after, finalMap, finalWorld, conditional_intro metadata form (.fault failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        conditionIH _ (by omega) conditionFound environments heaps locals agrees actualTyped installedEntry initialReady childEvaluation
      obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
      cases represented with
      | value payload =>
        obtain ⟨flag, sourceEq, coreEq⟩ := bool_fields payload
        subst sourceEq
        subst coreEq
        cases trace with
        | value conditionTrace =>
          obtain ⟨selectedSize, selected, selectedSmaller⟩ := RecursiveNamedExpressionSourceBounds.choose_branch_evaluated branch
          cases flag with
          | false =>
            change EvaluationSize selectedSize _ _ ((elseCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
              elseIH selectedSize (by omega) elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace.sound branchTrace.sound),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated transition⟩
            simpa only [elseType] using represented
          | true =>
            change EvaluationSize selectedSize _ _ ((thenCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
              thenIH selectedSize (by omega) thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState (firstReady _ rfl) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace.sound branchTrace.sound),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, ProtectedStateTransition.WithReady.Reached.continue protocol ready firstRelated transition⟩
            simpa only [thenType] using represented



theorem Head.reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (tree : Head checked source certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.ReflectsAt protocol ready
        (CompatibleAmbientHeap.payloadModel checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.WithReady.Reached protocol ready outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial initialReady evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    Head.reflects_raw_at functions program evidence protocol ready budget size bounded tree found meaning
      environments heaps locals agrees actualTyped initial initialReady evaluated
  obtain ⟨sourceSize, sized⟩ := ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩

end WithReady

theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults childSize) :
    ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults size := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, _⟩ := WithReady.Head.preserves_at functions program evidence protocol (fun _ => True)
        budget size bounded unique tree found
        (fun child _ childSize bound => by
          intro current expression code certified
          exact ProtectedStateTransition.WithReady.PreservesAt.of_stateful protocol (meaning childSize bound) certified.2)
        environments heaps locals agrees actualTyped initial True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related⟩

private theorem Head.reflects_raw_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults childSize) :
    ReflectsRawAt protocol size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, _⟩ := WithReady.Head.reflects_raw_at functions program evidence protocol (fun _ => True)
        budget size bounded tree found
        (fun child _ childSize bound => by
          intro current expression code certified
          exact ProtectedStateTransition.WithReady.ReflectsAt.of_stateful protocol (meaning childSize bound) certified.2)
        environments heaps locals agrees actualTyped initial True.intro evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related⟩

/-- Finite native completion yields an independently sized source trace. -/
theorem Head.reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.ReflectsAt protocol
      (CompatibleAmbientHeap.payloadModel checked registry functions) program context evidence source certificate faults childSize) :
    ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults size := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    Head.reflects_raw_at functions program evidence protocol budget size bounded meaning tree found environments heaps locals agrees actualTyped installedEntry evaluated
  obtain ⟨sourceSize, sized⟩ := ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩

end Stateful

/-- Legacy entries carry a proof witness and no runtime record data. -/
private def legacyProtocol (entry : ProtectedExpressionMeaning.Entry) :
    ProtectedStateTransition.Protocol Unit where
  State index := PLift (entry index.scope index.mapping index.world index.heap index.store index.canonical)
  records _ := ()
  Relates _ _ := True
  refl _ := True.intro
  trans _ _ := True.intro

variable {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport

private theorem lift_preserves_at {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults entry) :
    ProtectedStateTransition.PreservesAt (legacyProtocol entry) (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees actualTyped initial.down trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨PLift.up (transport.extend initial.down maps worlds frame metadata), True.intro⟩⟩

private theorem lift_reflects_at {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults entry) :
    ProtectedStateTransition.ReflectsAt (legacyProtocol entry) (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees actualTyped initial.down evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨PLift.up (transport.extend initial.down maps worlds frame metadata), True.intro⟩⟩

theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    (meaning : ∀ childSize, childSize ≤ budget → RecursiveNamedBoundedContracts.PreservesAt childSize (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults entry := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped installedEntry trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.Head.preserves_at functions program evidence (legacyProtocol entry) budget size bounded unique
      (fun childSize bound => lift_preserves_at functions program evidence transport (meaning childSize bound))
      tree found environments heaps locals agrees actualTyped (PLift.up installedEntry) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

/-- Finite native completion yields an independently sized source trace. -/
theorem Head.reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt childSize
      (CompatibleAmbientHeap.payloadModel checked registry functions) program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults entry := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.Head.reflects_at functions program evidence (legacyProtocol entry) budget size bounded
      (fun childSize bound => lift_reflects_at functions program evidence transport (meaning childSize bound))
      tree found environments heaps locals agrees actualTyped (PLift.up installedEntry) evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompositionsBounds
