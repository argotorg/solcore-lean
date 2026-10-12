import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorSourceBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompositionsBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence

/-! Recursive staged operators consume their actual child caller witnesses.
Pure operator steps keep that state; the right operand or selected branch starts
at the first successful child's exact heap and admission. Both fault kinds pass
through unchanged. Static heads contain only compiler fields and children. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CompatibleExpressionPrimitives CompatibleExpressionConditionals
open ProtectedStateExpressionOperandTyping
universe u
inductive Head (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
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

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

/-- Strict Source children preserve the exact staged result and owned state. -/
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique invocation.source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source) (covers : invocation.evidence.Covers context)
    (meaning : PreservesBelow bridge context model stages invocation certificate faults budget) :
    PreservesAt bridge context model stages invocation (Head compiled.compatible.checked invocation.source certificate) faults size := by
  intro scope id lowered tree root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    cases tree with
    | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have ih := fun n (bound : n < budget) => @meaning n bound _ _ _ child _ childFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change operand ∈ [operand]; simp) childFound)
      have sourceStep := CallableIndexedOwnedPreparedStagedOperatorSourceBounds.unary_inv metadata form unique trace
      cases sourceStep with
      | value childTrace applied childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          ih _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | value payload =>
          rw [inputType] at payload
          obtain ⟨sourceResult, result, actualApplied, coreApplied, resultRep⟩ := profile.preserves payload
          have same := actualApplied.functional applied
          subst sourceResult
          refine ⟨.inRight .word result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, ⟨reached, related⟩⟩
          · rw [unary_rename]; exact LocalPrimitiveResults.unary_success evaluated coreApplied
          · exact .value (outputType ▸ resultRep)
      | fault childTrace childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          ih _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [unary_rename]; exact LocalPrimitiveResults.unary_failure evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
      | invalid childTrace failed childSmaller =>
        obtain ⟨_, _, _, _, _, represented, _⟩ := ih _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | value payload =>
          rw [inputType] at payload
          obtain ⟨_, _, applied, _, _⟩ := profile.preserves payload
          exact False.elim (failed.excludes_application ⟨_, applied⟩)
    | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have leftIH := fun n (bound : n < budget) => @meaning n bound _ _ _ leftTree _ leftFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change left ∈ [left, right]; simp) leftFound)
      have rightIH := fun n (bound : n < budget) => @meaning n bound _ _ _ rightTree _ rightFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change right ∈ [left, right]; simp) rightFound)
      have sourceStep := CallableIndexedOwnedPreparedStagedOperatorSourceBounds.binary_inv metadata form unique trace
      cases sourceStep with
      | leftFault childTrace childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact mode.left_failure operator evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
      | leftInvalid childTrace invalid childSmaller =>
        obtain ⟨_, _, _, _, _, represented, _⟩ := leftIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | value payload =>
          rw [leftType] at payload
          exact False.elim (profile.left_valid payload invalid)
      | short childTrace circuit childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | value payload =>
          rw [leftType] at payload
          obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit evaluated
          exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, ⟨reached, related⟩⟩
      | rightFault firstTrace continues secondTrace firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
          rw [GenericExpressionMeaning.rename_prefix] at second
          cases represented with
          | fault matched =>
            exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact profile.right_failure payload continues first second,
              .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
      | value firstTrace continues secondTrace applied firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
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
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
      | invalid firstTrace continues secondTrace failed firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, _, _, _, second, represented, _, maps, worlds, _⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
          rw [GenericExpressionMeaning.rename_prefix] at second
          cases represented with
          | value rightPayload =>
            rw [rightType] at rightPayload
            have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
            obtain ⟨_, _, applied, _, _⟩ := profile.right_success leftPayload rightPayload continues first second
            exact False.elim (failed.excludes_application ⟨_, applied⟩)

    | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have conditionIH := fun n (bound : n < budget) => @meaning n bound _ _ _ conditionTree _ conditionFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change condition ∈ [condition, thenId, elseId]; simp) conditionFound)
      have thenIH := fun n (bound : n < budget) => @meaning n bound _ _ _ thenTree _ thenFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change thenId ∈ [condition, thenId, elseId]; simp) thenFound)
      have elseIH := fun n (bound : n < budget) => @meaning n bound _ _ _ elseTree _ elseFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change elseId ∈ [condition, thenId, elseId]; simp) elseFound)
      have sourceStep := CallableIndexedOwnedPreparedStagedOperatorSourceBounds.conditional_inv metadata form unique trace
      cases sourceStep with
      | fault childTrace childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          conditionIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [choose_rename]; exact LocalControl.choose_failure type evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
      | @branch conditionSize branchSize flag middle outcome after conditionTrace branchTrace conditionSmaller branchSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          conditionIH _ (Nat.lt_of_lt_of_le conditionSmaller bounded) environments heaps locals agrees actualTyped initial admitted conditionTrace
        cases represented with
        | value payload =>
          obtain ⟨actualFlag, sourceEq, coreEq⟩ := bool_fields payload
          cases sourceEq
          subst coreEq
          cases flag with
          | false =>
            obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
              elseIH _ (Nat.lt_of_lt_of_le branchSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
                (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 branchTrace
            rw [GenericExpressionMeaning.rename_prefix] at branch
            refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            · rw [choose_rename]; exact LocalControl.choose_false type first branch
            · simpa only [elseType] using represented
          | true =>
            obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
              thenIH _ (Nat.lt_of_lt_of_le branchSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
                (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 branchTrace
            rw [GenericExpressionMeaning.rename_prefix] at branch
            refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            · rw [choose_rename]; exact LocalControl.choose_true type first branch
            · simpa only [thenType] using represented

  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    CallableIndexedOwnedAdmittedStagedExpressionBounds.after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

/-- Completed native children produce their own staged grades and exact state. -/
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique invocation.source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source) (covers : invocation.evidence.Covers context)
    (meaning : ReflectsBelow bridge context model stages invocation certificate faults budget) :
    ReflectsAt bridge context model stages invocation (Head compiled.compatible.checked invocation.source certificate) faults size := by
  intro scope id lowered tree root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted evaluated
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    cases tree with
    | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have ih := fun n (bound : n < budget) => @meaning n bound _ _ _ child _ childFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change operand ∈ [operand]; simp) childFound)
      have occurrence : Staging.Recursive.Occurrence invocation id (.unary operator operand) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      rw [unary_rename] at evaluated
      have complete := evaluated.sound
      cases evaluated with
      | caseLeft childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          ih _ (by omega) environments heaps locals agrees actualTyped initial admitted childEvaluation
        cases represented with
        | fault matched =>
          have failed := trace
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_failure (operator := core) childEvaluation.sound) complete
          exact ⟨_, _, after, finalMap, finalWorld, .unaryOperandFault occurrence failed, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
      | caseRight childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          ih _ (by omega) environments heaps locals agrees actualTyped initial admitted childEvaluation
        cases represented with
        | value payload =>
          rw [inputType] at payload
          obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_success childEvaluation.sound coreApplied) complete
          have childTrace := trace
          exact ⟨_, _, after, finalMap, finalWorld, .unary occurrence childTrace applied,
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, ⟨reached, related⟩⟩
    | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have leftIH := fun n (bound : n < budget) => @meaning n bound _ _ _ leftTree _ leftFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change left ∈ [left, right]; simp) leftFound)
      have rightIH := fun n (bound : n < budget) => @meaning n bound _ _ _ rightTree _ rightFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change right ∈ [left, right]; simp) rightFound)
      have occurrence : Staging.Recursive.Occurrence invocation id (.binary left operator right) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      rw [Mode.binary_rename] at evaluated
      have complete := evaluated.sound
      rw [Mode.binary_eq] at evaluated
      cases evaluated with
      | caseLeft leftEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          leftIH _ (by omega) environments heaps locals agrees actualTyped initial admitted leftEvaluation
        cases represented with
        | fault matched =>
          have failed := trace
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (mode.left_failure operator leftEvaluation.sound)
          exact ⟨_, _, after, finalMap, finalWorld, .binaryLeftFault occurrence failed, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
      | caseRight leftEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (by omega) environments heaps locals agrees actualTyped initial admitted leftEvaluation
        cases represented with
        | @value sourceValue coreValue payload =>
          rw [leftType] at payload
          have firstTrace := trace
          rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
          · obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit leftEvaluation.sound
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            exact ⟨_, _, middle, middleMap, middleWorld, .binaryShortCircuit occurrence firstTrace circuit,
              .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, ⟨middleState, firstRelated⟩⟩
          · obtain ⟨rightSize, rightValue, rightStore, rightEvaluation, rightSmaller⟩ := RecursiveNamedExpressionSourceBounds.right_evaluated profile payload continues branch
            have shifted := rightEvaluation
            rw [← GenericExpressionMeaning.rename_prefix] at shifted
            obtain ⟨rightSourceSize, rightOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
              rightIH rightSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 shifted
            cases represented with
            | fault matched =>
              have failed := trace
              have combined := profile.right_failure payload continues leftEvaluation.sound rightEvaluation.sound
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              exact ⟨_, _, after, finalMap, finalWorld, .binaryRightFault occurrence firstTrace continues failed,
                .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            | value rightPayload =>
              rw [rightType] at rightPayload
              have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
              obtain ⟨sourceResult, result, applied, resultRep, combined⟩ :=
                profile.right_success leftPayload rightPayload continues leftEvaluation.sound rightEvaluation.sound
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              have secondTrace := trace
              exact ⟨_, _, after, finalMap, finalWorld, .binary occurrence firstTrace continues secondTrace applied,
                .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩

    | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have conditionIH := fun n (bound : n < budget) => @meaning n bound _ _ _ conditionTree _ conditionFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change condition ∈ [condition, thenId, elseId]; simp) conditionFound)
      have thenIH := fun n (bound : n < budget) => @meaning n bound _ _ _ thenTree _ thenFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change thenId ∈ [condition, thenId, elseId]; simp) thenFound)
      have elseIH := fun n (bound : n < budget) => @meaning n bound _ _ _ elseTree _ elseFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change elseId ∈ [condition, thenId, elseId]; simp) elseFound)
      have occurrence : Staging.Recursive.Occurrence invocation id (.conditional condition thenId elseId) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      rw [choose_rename] at evaluated
      have complete := evaluated.sound
      cases evaluated with
      | caseLeft childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          conditionIH _ (by omega) environments heaps locals agrees actualTyped initial admitted childEvaluation
        cases represented with
        | fault matched =>
          have failed := trace
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalControl.choose_failure type childEvaluation.sound)
          exact ⟨_, _, after, finalMap, finalWorld, .conditionalFault occurrence failed, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
      | caseRight childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          conditionIH _ (by omega) environments heaps locals agrees actualTyped initial admitted childEvaluation
        cases represented with
        | value payload =>
          obtain ⟨flag, sourceEq, coreEq⟩ := bool_fields payload
          subst sourceEq
          subst coreEq
          have conditionTrace := trace
          obtain ⟨selectedSize, selected, selectedSmaller⟩ := RecursiveNamedExpressionSourceBounds.choose_branch_evaluated branch
          cases flag with
          | false =>
            change EvaluationSize selectedSize _ _ ((elseCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
              elseIH selectedSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 selected
            refine ⟨_, outcome, after, finalMap, finalWorld, .conditional occurrence conditionTrace branchTrace,
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            simpa only [elseType] using represented
          | true =>
            change EvaluationSize selectedSize _ _ ((thenCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
              thenIH selectedSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 selected
            refine ⟨_, outcome, after, finalMap, finalWorld, .conditional occurrence conditionTrace branchTrace,
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            simpa only [thenType] using represented

  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    CallableIndexedOwnedAdmittedStagedExpressionBounds.after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorBounds
