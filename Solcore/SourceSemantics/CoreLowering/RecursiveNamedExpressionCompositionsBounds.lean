import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds

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
private def ReflectsRawAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate) (faults : FunctionCalls.FaultRep) (entry : ProtectedExpressionMeaning.Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after


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
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport

theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    (meaning : ∀ childSize, childSize ≤ budget → RecursiveNamedBoundedContracts.PreservesAt childSize (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have ih := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨childSize, childTrace, childSmaller⟩ := RecursiveNamedExpressionSourceBounds.group_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ih childSize (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) innerFound environments heaps locals agrees actualTyped installedEntry childTrace
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have leftIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ firstTree
    have rightIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    -- The sequence uses a strict bound; its successor is exactly childSize ≤ budget.
    have children : ∀ childSize, childSize < budget + 1 → ProtectedDataExpressionSequence.ExpressionPreservesAt childSize (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (Two scope left right first second) faults entry := by
      intro childSize bound
      apply RecursiveNamedPlaceKeyContracts.preserves_at
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH childSize (by omega)
      · exact rightIH childSize (by omega)
    obtain ⟨sequenceSize, sequence, sourceTrace, packed, sequenceSmaller⟩ := RecursiveNamedExpressionSourceBounds.pair_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ProtectedDataExpressionSequence.preserves_bounded transport (budget + 1) (two_tree (first := first) (second := second) leftFound rightFound) children environments heaps locals agrees actualTyped installedEntry sourceTrace (by omega)
    obtain ⟨actualOutcome, actualPack, payload⟩ := pair_result represented
    have sameOutcome := actualPack.functional packed
    subst actualOutcome
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have ih := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := RecursiveNamedExpressionSourceBounds.unary_inv metadata form unique trace
    cases sourceStep with
    | value childTrace applied childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) childFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, actualApplied, coreApplied, resultRep⟩ := profile.preserves payload
        have same := actualApplied.functional applied
        subst sourceResult
        refine ⟨.inRight .word result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
        · rw [unary_rename]; exact LocalPrimitiveResults.unary_success evaluated coreApplied
        · exact .value (outputType ▸ resultRep)
    | fault childTrace childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) childFound environments heaps locals agrees actualTyped installedEntry (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [unary_rename]; exact LocalPrimitiveResults.unary_failure evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | invalid childTrace failed childSmaller =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) childFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨_, _, applied, _, _⟩ := profile.preserves payload
        exact False.elim (unary_fault_excluded applied failed)
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have leftIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ leftTree
    have rightIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ rightTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := RecursiveNamedExpressionSourceBounds.binary_inv metadata form unique trace
    cases sourceStep with
    | leftFault childTrace childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact mode.left_failure operator evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | leftInvalid childTrace invalid childSmaller =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := leftIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        exact False.elim (profile.left_valid payload invalid)
    | short childTrace circuit childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit evaluated
        exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
          .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata⟩
    | rightFault firstTrace continues secondTrace firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt firstSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
          rightIH _ (Nat.le_trans (Nat.le_of_lt secondSmaller) bounded) rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.fault secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact profile.right_failure payload continues first second,
            .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
    | value firstTrace continues secondTrace applied firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt firstSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
          rightIH _ (Nat.le_trans (Nat.le_of_lt secondSmaller) bounded) rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.value secondTrace)
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
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
    | invalid firstTrace continues secondTrace failed firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH _ (Nat.le_trans (Nat.le_of_lt firstSmaller) bounded) leftFound environments heaps locals agrees actualTyped installedEntry (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, _, _, _, second, represented, _, maps, worlds, _⟩ :=
          rightIH _ (Nat.le_trans (Nat.le_of_lt secondSmaller) bounded) rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          obtain ⟨_, _, applied, _, _⟩ := profile.right_success leftPayload rightPayload continues first second
          exact False.elim (binary_fault_excluded applied failed)

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have conditionIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ conditionTree
    have thenIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ thenTree
    have elseIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ elseTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := RecursiveNamedExpressionSourceBounds.conditional_inv metadata form unique trace
    cases sourceStep with
    | fault childTrace childSmaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        conditionIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) conditionFound environments heaps locals agrees actualTyped installedEntry (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [choose_rename]; exact LocalControl.choose_failure type evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | @branch conditionSize branchSize flag middle outcome after conditionTrace branchTrace conditionSmaller branchSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        conditionIH _ (Nat.le_trans (Nat.le_of_lt conditionSmaller) bounded) conditionFound environments heaps locals agrees actualTyped installedEntry (.value conditionTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualFlag, sourceEq, coreEq⟩ := bool_fields payload
        cases sourceEq
        subst coreEq
        cases flag with
        | false =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
            elseIH _ (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded) elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
          · rw [choose_rename]; exact LocalControl.choose_false type first branch
          · simpa only [elseType] using represented
        | true =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
            thenIH _ (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded) thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
          · rw [choose_rename]; exact LocalControl.choose_true type first branch
          · simpa only [thenType] using represented
    | invalid childTrace invalid runtimeType childSmaller =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := conditionIH _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) conditionFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨flag, rfl, _⟩ := bool_fields payload
        exact False.elim (invalid trivial)


private theorem Head.reflects_raw_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt childSize (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults entry) :
    ReflectsRawAt size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have ih := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ih size bounded innerFound environments heaps locals agrees actualTyped installedEntry evaluated
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.group_intro metadata form trace.sound, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have leftIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ firstTree
    have rightIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    -- The sequence uses a strict bound; its successor is exactly childSize ≤ budget.
    have children : ∀ childSize, childSize < budget + 1 → ProtectedDataExpressionSequence.ExpressionReflectsAt childSize (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (Two scope left right first second) faults entry := by
      intro childSize bound
      apply RecursiveNamedPlaceKeyContracts.reflects_at
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH childSize (by omega)
      · exact rightIH childSize (by omega)
    obtain ⟨sequenceSize, sequence, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ProtectedDataExpressionSequence.reflects_bounded transport (budget + 1) (two_tree (first := first) (second := second) leftFound rightFound) children environments heaps locals agrees actualTyped installedEntry evaluated (by omega)
    obtain ⟨outcome, packed, payload⟩ := pair_result represented
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.pair_intro metadata form sourceTrace.sound packed, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have ih := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [unary_rename] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih _ (by omega) childFound environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_failure (operator := core) childEvaluation.sound) complete
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.fault failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih _ (by omega) childFound environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
        obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_success childEvaluation.sound coreApplied) complete
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.value childTrace.sound applied),
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata⟩
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have leftIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ leftTree
    have rightIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ rightTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [Mode.binary_rename] at evaluated
    have complete := evaluated.sound
    rw [Mode.binary_eq] at evaluated
    cases evaluated with
    | caseLeft leftEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH _ (by omega) leftFound environments heaps locals agrees actualTyped installedEntry leftEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (mode.left_failure operator leftEvaluation.sound)
          exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.leftFault failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight leftEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH _ (by omega) leftFound environments heaps locals agrees actualTyped installedEntry leftEvaluation
      cases represented with
      | @value sourceValue coreValue payload =>
        rw [leftType] at payload
        cases trace with
        | value firstTrace =>
          rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
          · obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit leftEvaluation.sound
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            exact ⟨_, middle, middleMap, middleWorld, binary_intro metadata form (.short firstTrace.sound circuit),
              .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩
          · obtain ⟨rightSize, rightValue, rightStore, rightEvaluation, rightSmaller⟩ := RecursiveNamedExpressionSourceBounds.right_evaluated profile payload continues branch
            have shifted := rightEvaluation
            rw [← GenericExpressionMeaning.rename_prefix] at shifted
            obtain ⟨rightSourceSize, rightOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
              rightIH rightSize (by omega) rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) shifted
            cases represented with
            | fault matched =>
              cases trace with
              | fault failed =>
                have combined := profile.right_failure payload continues leftEvaluation.sound rightEvaluation.sound
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.rightFault firstTrace.sound continues failed.sound),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
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
                  firstFrame.trans frame, firstMetadata.trans heapMetadata⟩

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have conditionIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ conditionTree
    have thenIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ thenTree
    have elseIH := fun n (bound : n ≤ budget) => @meaning n bound _ _ _ elseTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [choose_rename] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        conditionIH _ (by omega) conditionFound environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalControl.choose_failure type childEvaluation.sound)
          exact ⟨_, after, finalMap, finalWorld, conditional_intro metadata form (.fault failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        conditionIH _ (by omega) conditionFound environments heaps locals agrees actualTyped installedEntry childEvaluation
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
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
              elseIH selectedSize (by omega) elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace.sound branchTrace.sound),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
            simpa only [elseType] using represented
          | true =>
            change EvaluationSize selectedSize _ _ ((thenCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
              thenIH selectedSize (by omega) thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace.sound branchTrace.sound),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
            simpa only [thenType] using represented



/-- Finite native completion yields an independently sized source trace. -/
theorem Head.reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt childSize
      (CompatibleAmbientHeap.payloadModel checked registry functions) program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults entry := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    Head.reflects_raw_at functions program evidence transport budget size bounded meaning tree found environments heaps locals agrees actualTyped installedEntry evaluated
  obtain ⟨sourceSize, sized⟩ := ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompositionsBounds
