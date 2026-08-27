import Solcore.Core.Eval
import Solcore.Core.RenamingRuntime

set_option autoImplicit false

namespace Solcore.Core

private theorem UnaryOp.apply_related
    {op : UnaryOp} {source target result : Value}
    (values : ValuesRelated source target)
    (applied : op.apply source = some result) :
    ∃ result', op.apply target = some result' ∧ ValuesRelated result result' := by
  cases op <;> cases values <;>
    simp [UnaryOp.apply] at applied ⊢ <;>
    cases applied <;> first | exact .bool _ | exact .word _

private theorem BinaryOp.apply_related
    {op : BinaryOp} {left left' right right' result : Value}
    (leftValues : ValuesRelated left left')
    (rightValues : ValuesRelated right right')
    (applied : op.apply left right = some result) :
    ∃ result',
      op.apply left' right' = some result' ∧ ValuesRelated result result' := by
  cases op <;> cases leftValues <;> cases rightValues <;>
    simp [BinaryOp.apply] at applied ⊢ <;>
    cases applied <;> first | exact .bool _ | exact .word _

private theorem TernaryOp.apply_related
    {op : TernaryOp}
    {firstValue firstValue' secondValue secondValue' thirdValue thirdValue'
      result : Value}
    (firstValues : ValuesRelated firstValue firstValue')
    (secondValues : ValuesRelated secondValue secondValue')
    (thirdValues : ValuesRelated thirdValue thirdValue')
    (applied : op.apply firstValue secondValue thirdValue = some result) :
    ∃ result',
      op.apply firstValue' secondValue' thirdValue' = some result' ∧
      ValuesRelated result result' := by
  cases op <;> cases firstValues <;> cases secondValues <;>
    cases thirdValues <;>
    simp [TernaryOp.apply] at applied ⊢ <;>
    cases applied <;> exact .word _

private theorem Expr.renameList_lookup
    {branches : List Expr} {index : Nat} {branch : Expr}
    (found : branches[index]? = some branch)
    (mapping : Renaming) :
    (Expr.renameList branches mapping)[index]? = some (branch.rename mapping) := by
  induction branches generalizing index with
  | nil => simp at found
  | cons head tail inductionHypothesis =>
      cases index with
      | zero =>
          simp at found
          subst branch
          simp [Expr.renameList]
      | succ index =>
          simp [Expr.renameList] at found ⊢
          exact inductionHypothesis found

theorem Evaluates.rename
    {sourceEnvironment : Environment} {sourceInitialStore : Store}
    {expr : Expr} {sourceValue : Value} {sourceFinalStore : Store}
    (evaluation : Evaluates sourceEnvironment sourceInitialStore expr
      sourceValue sourceFinalStore)
    {mapping : Renaming} {targetEnvironment : Environment}
    {targetInitialStore : Store}
    (environments :
      EnvironmentsRelated mapping sourceEnvironment targetEnvironment)
    (stores : StoresRelated sourceInitialStore targetInitialStore) :
    ∃ targetValue targetFinalStore,
      Evaluates targetEnvironment targetInitialStore (expr.rename mapping)
        targetValue targetFinalStore ∧
      ValuesRelated sourceValue targetValue ∧
      StoresRelated sourceFinalStore targetFinalStore := by
  induction evaluation generalizing mapping targetEnvironment targetInitialStore with
  | unit => exact ⟨.unit, _, .unit, .unit, stores⟩
  | bool => exact ⟨_, _, .bool, .bool _, stores⟩
  | word => exact ⟨_, _, .word, .word _, stores⟩
  | pair _ _ leftIH rightIH =>
      obtain ⟨left', middleStore', leftEvaluation, leftRelated, middleRelated⟩ :=
        leftIH environments stores
      obtain ⟨right', finalStore', rightEvaluation, rightRelated, finalRelated⟩ :=
        rightIH environments middleRelated
      exact ⟨.pair left' right', finalStore',
        .pair leftEvaluation rightEvaluation,
        .pair leftRelated rightRelated, finalRelated⟩
  | first _ operandIH =>
      obtain ⟨operand', finalStore', operandEvaluation, operandRelated,
        finalRelated⟩ := operandIH environments stores
      cases operandRelated with
      | pair leftRelated rightRelated =>
          exact ⟨_, finalStore', .first operandEvaluation,
            leftRelated, finalRelated⟩
  | second _ operandIH =>
      obtain ⟨operand', finalStore', operandEvaluation, operandRelated,
        finalRelated⟩ := operandIH environments stores
      cases operandRelated with
      | pair leftRelated rightRelated =>
          exact ⟨_, finalStore', .second operandEvaluation,
            rightRelated, finalRelated⟩
  | inLeft _ payloadIH =>
      obtain ⟨payload', finalStore', payloadEvaluation, payloadRelated,
        finalRelated⟩ := payloadIH environments stores
      exact ⟨.inLeft _ payload', finalStore', .inLeft payloadEvaluation,
        .inLeft payloadRelated, finalRelated⟩
  | inRight _ payloadIH =>
      obtain ⟨payload', finalStore', payloadEvaluation, payloadRelated,
        finalRelated⟩ := payloadIH environments stores
      exact ⟨.inRight _ payload', finalStore', .inRight payloadEvaluation,
        .inRight payloadRelated, finalRelated⟩
  | caseLeft _ _ scrutineeIH branchIH =>
      obtain ⟨scrutinee', branchStore', scrutineeEvaluation,
        scrutineeRelated, branchStoreRelated⟩ := scrutineeIH environments stores
      cases scrutineeRelated with
      | inLeft payloadRelated =>
          obtain ⟨result', finalStore', branchEvaluation, resultRelated,
            finalRelated⟩ :=
            branchIH (environments.extend payloadRelated) branchStoreRelated
          exact ⟨result', finalStore',
            .caseLeft scrutineeEvaluation branchEvaluation,
            resultRelated, finalRelated⟩
  | caseRight _ _ scrutineeIH branchIH =>
      obtain ⟨scrutinee', branchStore', scrutineeEvaluation,
        scrutineeRelated, branchStoreRelated⟩ := scrutineeIH environments stores
      cases scrutineeRelated with
      | inRight payloadRelated =>
          obtain ⟨result', finalStore', branchEvaluation, resultRelated,
            finalRelated⟩ :=
            branchIH (environments.extend payloadRelated) branchStoreRelated
          exact ⟨result', finalStore',
            .caseRight scrutineeEvaluation branchEvaluation,
            resultRelated, finalRelated⟩
  | lambda =>
      exact ⟨_, _, .lambda, .closure mapping environments, stores⟩
  | apply _ _ _ functionIH argumentIH bodyIH =>
      obtain ⟨function', argumentStore', functionEvaluation, functionRelated,
        argumentStoreRelated⟩ := functionIH environments stores
      cases functionRelated with
      | closure bodyMapping capturedRelated =>
          obtain ⟨argument', bodyStore', argumentEvaluation, argumentRelated,
            bodyStoreRelated⟩ := argumentIH environments argumentStoreRelated
          obtain ⟨result', finalStore', bodyEvaluation, resultRelated,
            finalRelated⟩ :=
            bodyIH (capturedRelated.extend argumentRelated) bodyStoreRelated
          exact ⟨result', finalStore',
            .apply functionEvaluation argumentEvaluation bodyEvaluation,
            resultRelated, finalRelated⟩
  | var found =>
      obtain ⟨value', found', values⟩ := environments.lookup found
      exact ⟨value', targetInitialStore, .var found', values, stores⟩
  | newCell _ initializerIH =>
      obtain ⟨value', initializedStore', initializerEvaluation, values,
        initializedStores⟩ := initializerIH environments stores
      have allocated := initializedStores.allocate values
      rw [Store.allocate_updatedStore, Store.allocate_updatedStore] at allocated
      rw [initializedStores.length_eq]
      exact ⟨.cellRef _ initializedStore'.length,
        initializedStore' ++ [value'], .newCell initializerEvaluation,
        .cellRef, allocated.1⟩
  | loadCell _ read operandIH =>
      obtain ⟨reference', referenceStore', referenceEvaluation,
        referenceRelated, referenceStores⟩ := operandIH environments stores
      cases referenceRelated with
      | cellRef =>
          obtain ⟨value', read', values⟩ := referenceStores.read read
          exact ⟨value', referenceStore', .loadCell referenceEvaluation read',
            values, referenceStores⟩
  | storeCell _ read _ written referenceIH valueIH =>
      obtain ⟨reference', referenceStore', referenceEvaluation,
        referenceRelated, referenceStores⟩ := referenceIH environments stores
      cases referenceRelated with
      | cellRef =>
          obtain ⟨oldValue', read', oldValues⟩ := referenceStores.read read
          obtain ⟨value', valueStore', valueEvaluation, values, valueStores⟩ :=
            valueIH environments referenceStores
          obtain ⟨finalStore', written', finalStores⟩ :=
            valueStores.write values written
          exact ⟨.unit, finalStore',
            .storeCell referenceEvaluation read' valueEvaluation written',
            .unit, finalStores⟩
  | construct _ payloadIH =>
      obtain ⟨payload', finalStore', payloadEvaluation, payloadRelated,
        finalRelated⟩ := payloadIH environments stores
      exact ⟨.constructed _ payload', finalStore',
        .construct payloadEvaluation, .constructed payloadRelated, finalRelated⟩
  | matchData _ owner found _ scrutineeIH branchIH =>
      obtain ⟨scrutinee', branchStore', scrutineeEvaluation,
        scrutineeRelated, branchStores⟩ := scrutineeIH environments stores
      cases scrutineeRelated with
      | constructed payloadRelated =>
          obtain ⟨result', finalStore', branchEvaluation, resultRelated,
            finalRelated⟩ :=
            branchIH (environments.extend payloadRelated) branchStores
          exact ⟨result', finalStore',
            .matchData scrutineeEvaluation owner
              (Expr.renameList_lookup found mapping.lift) branchEvaluation,
            resultRelated, finalRelated⟩
  | unary _ applied operandIH =>
      obtain ⟨operand', finalStore', operandEvaluation, operandRelated,
        finalRelated⟩ := operandIH environments stores
      obtain ⟨result', applied', resultRelated⟩ :=
        UnaryOp.apply_related operandRelated applied
      exact ⟨result', finalStore', .unary operandEvaluation applied',
        resultRelated, finalRelated⟩
  | binary _ _ applied leftIH rightIH =>
      obtain ⟨left', rightStore', leftEvaluation, leftRelated, rightStores⟩ :=
        leftIH environments stores
      obtain ⟨right', finalStore', rightEvaluation, rightRelated,
        finalRelated⟩ := rightIH environments rightStores
      obtain ⟨result', applied', resultRelated⟩ :=
        BinaryOp.apply_related leftRelated rightRelated applied
      exact ⟨result', finalStore',
        .binary leftEvaluation rightEvaluation applied',
        resultRelated, finalRelated⟩
  | ternary _ _ _ applied firstIH secondIH thirdIH =>
      obtain ⟨first', secondStore', firstEvaluation, firstRelated,
        secondStores⟩ := firstIH environments stores
      obtain ⟨second', thirdStore', secondEvaluation, secondRelated,
        thirdStores⟩ := secondIH environments secondStores
      obtain ⟨third', finalStore', thirdEvaluation, thirdRelated,
        finalRelated⟩ := thirdIH environments thirdStores
      obtain ⟨result', applied', resultRelated⟩ :=
        TernaryOp.apply_related firstRelated secondRelated thirdRelated applied
      exact ⟨result', finalStore',
        .ternary firstEvaluation secondEvaluation thirdEvaluation applied',
        resultRelated, finalRelated⟩
  | letE _ _ valueIH bodyIH =>
      obtain ⟨value', bodyStore', valueEvaluation, valueRelated,
        bodyStores⟩ := valueIH environments stores
      obtain ⟨result', finalStore', bodyEvaluation, resultRelated,
        finalRelated⟩ :=
        bodyIH (environments.extend valueRelated) bodyStores
      exact ⟨result', finalStore', .letE valueEvaluation bodyEvaluation,
        resultRelated, finalRelated⟩
  | ifTrue _ _ conditionIH branchIH =>
      obtain ⟨condition', branchStore', conditionEvaluation,
        conditionRelated, branchStores⟩ := conditionIH environments stores
      rw [ValuesRelated.bool_iff.mp conditionRelated] at conditionEvaluation
      obtain ⟨result', finalStore', branchEvaluation, resultRelated,
        finalRelated⟩ := branchIH environments branchStores
      exact ⟨result', finalStore',
        .ifTrue conditionEvaluation branchEvaluation,
        resultRelated, finalRelated⟩
  | ifFalse _ _ conditionIH branchIH =>
      obtain ⟨condition', branchStore', conditionEvaluation,
        conditionRelated, branchStores⟩ := conditionIH environments stores
      rw [ValuesRelated.bool_iff.mp conditionRelated] at conditionEvaluation
      obtain ⟨result', finalStore', branchEvaluation, resultRelated,
        finalRelated⟩ := branchIH environments branchStores
      exact ⟨result', finalStore',
        .ifFalse conditionEvaluation branchEvaluation,
        resultRelated, finalRelated⟩

end Solcore.Core
