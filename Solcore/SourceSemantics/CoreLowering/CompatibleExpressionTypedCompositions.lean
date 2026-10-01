import Solcore.SourceSemantics.CoreLowering.TypedDataExpressionSequence
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalExecution
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalTree

/-! One-level typed composition for data, primitive and conditional expressions.
The children are static certificates. A recursive compiler proof supplies their
universal meanings; the actual operand/branch slot gets its runtime type from
the represented result and the existing environment follows the world extension.
No source execution or native child evaluation is a static head premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedCompositions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals

inductive Head (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | group {id node inner innerNode lowered}
      (metadata : Metadata checked source id node lowered.type)
      (form : node.form = .group inner) (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : certificate scope inner lowered) :
      Head checked source certificate scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : Metadata checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode) (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (firstTree : certificate scope left first)
      (secondTree : certificate scope right second) :
      Head checked source certificate scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩
  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : Metadata checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : UnaryProfile operator operandType resultType core)
      (child : certificate scope operand ⟨core.operandType, childCode⟩) :
      Head checked source certificate scope id
        ⟨core.resultType, LocalPrimitiveResults.unary core childCode⟩
  | binary {id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      (metadata : Metadata checked source id node (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = operandType)
      (outputType : node.type = resultType)
      (profile : BinaryProfile operator operandType resultType mode)
      (first : certificate scope left ⟨mode.operandType operator, leftCode⟩)
      (second : certificate scope right ⟨mode.operandType operator, rightCode⟩) :
      Head checked source certificate scope id
        ⟨mode.resultType operator, mode.binary operator leftCode rightCode⟩

  | conditional {id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      (metadata : Metadata checked source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (thenFound : source.lookupExpression? thenId = some thenNode)
      (elseFound : source.lookupExpression? elseId = some elseNode)
      (conditionType : conditionNode.type = .bool)
      (thenType : thenNode.type = node.type) (elseType : elseNode.type = node.type)
      (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
      (thenTree : certificate scope thenId ⟨type, thenCode⟩)
      (elseTree : certificate scope elseId ⟨type, elseCode⟩) :
      Head checked source certificate scope id
        ⟨type, LocalControl.choose type conditionCode thenCode elseCode⟩

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

theorem Head.preserves
    (unique : NodeOccurrencesUnique source)
    (meaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults := by
  intro scope id lowered tree
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ih innerFound environments heaps locals agrees actualTyped (CompatibleExpressionProducts.group_inv metadata form unique trace)
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have leftIH := @meaning _ _ _ firstTree
    have rightIH := @meaning _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have children : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (Two scope left right first second) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    obtain ⟨sequence, sourceTrace, packed⟩ := CompatibleExpressionProducts.pair_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      TypedDataExpressionSequence.preserves (two_tree (first := first) (second := second) leftFound rightFound) children environments heaps locals agrees actualTyped sourceTrace
    obtain ⟨actualOutcome, actualPack, payload⟩ := pair_result represented
    have sameOutcome := actualPack.functional packed
    subst actualOutcome
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := unary_inv metadata form unique trace
    cases sourceStep with
    | value childTrace applied =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih childFound environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, actualApplied, coreApplied, resultRep⟩ := profile.preserves payload
        have same := actualApplied.functional applied
        subst sourceResult
        refine ⟨.inRight .word result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
        · rw [unary_rename]; exact LocalPrimitiveResults.unary_success evaluated coreApplied
        · exact .value (outputType ▸ resultRep)
    | fault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih childFound environments heaps locals agrees actualTyped (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [unary_rename]; exact LocalPrimitiveResults.unary_failure evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | invalid childTrace failed =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := ih childFound environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨_, _, applied, _, _⟩ := profile.preserves payload
        exact False.elim (unary_fault_excluded applied failed)
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have leftIH := @meaning _ _ _ leftTree
    have rightIH := @meaning _ _ _ rightTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := binary_inv metadata form unique trace
    cases sourceStep with
    | leftFault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact mode.left_failure operator evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | leftInvalid childTrace invalid =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := leftIH leftFound environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        exact False.elim (profile.left_valid payload invalid)
    | short childTrace circuit =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit evaluated
        exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
          .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata⟩
    | rightFault firstTrace continues secondTrace =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (.fault secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact profile.right_failure payload continues first second,
            .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
    | value firstTrace continues secondTrace applied =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (.value secondTrace)
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
    | invalid firstTrace continues secondTrace failed =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, _, firstMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, _, _, _, second, represented, _, maps, worlds, _⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          obtain ⟨_, _, applied, _, _⟩ := profile.right_success leftPayload rightPayload continues first second
          exact False.elim (binary_fault_excluded applied failed)

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have conditionIH := @meaning _ _ _ conditionTree
    have thenIH := @meaning _ _ _ thenTree
    have elseIH := @meaning _ _ _ elseTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := conditional_inv metadata form unique trace
    cases sourceStep with
    | fault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [choose_rename]; exact LocalControl.choose_failure type evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | @branch flag middle outcome after conditionTrace branchTrace =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped (.value conditionTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualFlag, sourceEq, coreEq⟩ := bool_fields payload
        cases sourceEq
        subst coreEq
        cases flag with
        | false =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
            elseIH elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
          · rw [choose_rename]; exact LocalControl.choose_false type first branch
          · simpa only [elseType] using represented
        | true =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
            thenIH thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
          · rw [choose_rename]; exact LocalControl.choose_true type first branch
          · simpa only [thenType] using represented
    | invalid childTrace invalid runtimeType =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := conditionIH conditionFound environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨flag, rfl, _⟩ := bool_fields payload
        exact False.elim (invalid trivial)


theorem Head.reflects
    (meaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults) :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults := by
  intro scope id lowered tree
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ih innerFound environments heaps locals agrees actualTyped evaluated
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.group_intro metadata form trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have leftIH := @meaning _ _ _ firstTree
    have rightIH := @meaning _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have children : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (Two scope left right first second) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    obtain ⟨sequence, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      TypedDataExpressionSequence.reflects (two_tree (first := first) (second := second) leftFound rightFound) children environments heaps locals agrees actualTyped evaluated
    obtain ⟨outcome, packed, payload⟩ := pair_result represented
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.pair_intro metadata form sourceTrace packed, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [unary_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih childFound environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_failure (operator := core) childEvaluation) complete
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.fault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih childFound environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
        obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_success childEvaluation coreApplied) complete
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.value childTrace applied),
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata⟩
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have leftIH := @meaning _ _ _ leftTree
    have rightIH := @meaning _ _ _ rightTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [Mode.binary_rename] at evaluated
    have complete := evaluated
    rw [Mode.binary_eq] at evaluated
    cases evaluated with
    | caseLeft leftEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped leftEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (mode.left_failure operator leftEvaluation)
          exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.leftFault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight leftEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped leftEvaluation
      cases represented with
      | @value sourceValue coreValue payload =>
        rw [leftType] at payload
        cases trace with
        | value firstTrace =>
          rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
          · obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit leftEvaluation
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            exact ⟨_, middle, middleMap, middleWorld, binary_intro metadata form (.short firstTrace circuit),
              .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩
          · obtain ⟨rightValue, rightStore, rightEvaluation⟩ := profile.right_evaluated payload continues branch
            have shifted := rightEvaluation
            rw [← GenericExpressionMeaning.rename_prefix] at shifted
            obtain ⟨rightOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
              rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) shifted
            cases represented with
            | fault matched =>
              cases trace with
              | fault failed =>
                have combined := profile.right_failure payload continues leftEvaluation rightEvaluation
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.rightFault firstTrace continues failed),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
            | value rightPayload =>
              rw [rightType] at rightPayload
              have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
              obtain ⟨sourceResult, result, applied, resultRep, combined⟩ :=
                profile.right_success leftPayload rightPayload continues leftEvaluation rightEvaluation
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              cases trace with
              | value secondTrace =>
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.value firstTrace continues secondTrace applied),
                  .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata⟩

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have conditionIH := @meaning _ _ _ conditionTree
    have thenIH := @meaning _ _ _ thenTree
    have elseIH := @meaning _ _ _ elseTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [choose_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalControl.choose_failure type childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, conditional_intro metadata form (.fault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | value payload =>
        obtain ⟨flag, sourceEq, coreEq⟩ := bool_fields payload
        subst sourceEq
        subst coreEq
        cases trace with
        | value conditionTrace =>
          have selected := choose_branch_evaluated branch
          cases flag with
          | false =>
            change Evaluates _ _ ((elseCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
              elseIH elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace branchTrace),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
            simpa only [elseType] using represented
          | true =>
            change Evaluates _ _ ((thenCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
              thenIH thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace branchTrace),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
            simpa only [thenType] using represented


end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedCompositions
