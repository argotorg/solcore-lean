import Solcore.Frontend.RustHull.AtomDerivationCorrespondence
import Solcore.Frontend.RustHull.ContextualExpressionCorrespondence

/-! Structural expression simulation consumes only the child executions in a
finite independent Hull derivation. Named calls may recur in those children. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence StatementCorrespondence ContextualExpressionCorrespondence

theorem pair {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial middle final : Semantics.State σ} {left right : Expr}
    {leftValue : Semantics.Value} {rightResult : Semantics.Result Semantics.Value}
    (leftPreserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment left initial (.value leftValue) middle)
    (rightPreserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment right middle rightResult final)
    (type : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment ⟨type, .pair left right, span⟩
      initial (rightResult.map (Semantics.Value.pair leftValue)) final := by
  intro fuel scope lowered compiled covered world mapping environment store environmentRelated globals runtime heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨leftCode, rightCode, leftCompiled, rightCompiled, rfl⟩ :=
        lowerExpression_pair_components compiled
      obtain ⟨leftExtension, targetLeft, middleStore, leftRelated, leftEvaluation, middleHeap, middleExternal, firstFrame⟩ :=
        leftPreserves.value rfl leftCompiled covered environmentRelated globals runtime heap externalRelated
      have middleEnvironment := (environmentRelated.extendWorld leftExtension).prepend [targetLeft]
      obtain ⟨rightExtension, targetRight, finalStore, rightRelated, rightEvaluation, finalHeap, finalExternal, lastFrame⟩ :=
        rightPreserves rightCompiled covered middleEnvironment (globals.prepend [targetLeft]) (runtime.prepend [targetLeft]) middleHeap middleExternal
      have renamed : (rightCode.expression.rename mapping).weakenAt 0 =
          rightCode.expression.rename (fun index => 1 + mapping index) := by
        simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
        congr 1
        funext index
        simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
      cases rightRelated with
      | value related =>
          refine ⟨leftExtension ++ rightExtension, .inRight .word (.pair targetLeft _), finalStore,
            .value (.pair leftRelated related), ?_, ?_, finalExternal, firstFrame.trans lastFrame⟩
          · rw [pair_rename]
            apply Core.LocalSequence.pair_success _ _ leftEvaluation
            simpa [renamed] using rightEvaluation
          · simpa only [List.append_assoc] using finalHeap
      | language reason =>
          refine ⟨leftExtension ++ rightExtension, .inLeft _ (.word reason), finalStore,
            .language reason, ?_, ?_, finalExternal, firstFrame.trans lastFrame⟩
          · rw [pair_rename]
            apply Core.LocalSequence.pair_right_failure _ _ leftEvaluation
            simpa [renamed] using rightEvaluation
          · simpa only [List.append_assoc] using finalHeap

/-- A failing first operand skips the second operand of the actual pair code. -/
theorem pair_fault {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {left right : Expr} {reason : Semantics.Fault}
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment left initial (.fault reason) final)
    (type : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment ⟨type, .pair left right, span⟩
      initial (.fault reason) final := by
  intro fuel scope lowered compiled covered world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨leftCode, rightCode, leftCompiled, _, rfl⟩ := lowerExpression_pair_components compiled
      obtain ⟨extension, target, finalStore, related, evaluated, finalHeap, finalInstalled, frame⟩ :=
        preserves leftCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          refine ⟨extension, .inLeft _ (.word reason), finalStore, .language reason,
            ?_, finalHeap, finalInstalled, frame⟩
          rw [pair_rename]
          exact Core.LocalSequence.pair_left_failure _ _ evaluated

theorem projection {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {operand : Expr} {result : Semantics.Result Semantics.Value}
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment operand initial result final)
    (right : Bool) (type : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, if right then .snd operand else .fst operand, span⟩ initial
      (result.bind (Semantics.projectResult right)) final := by
  intro fuel scope lowered compiled covered world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, leftType, rightType, operandCompiled, operandType, rfl⟩ :=
        lowerExpression_projection_components right compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalInstalled, frame⟩ :=
        preserves operandCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          exact ⟨extension, .inLeft _ (.word reason), finalStore, .language reason,
            Core.LanguageResult.bind_failure _ evaluation, finalHeap, finalInstalled, frame⟩
      | value related =>
          rw [operandType] at related
          cases related with
          | pair leftRelated rightRelated =>
              cases right <;> simp only [Semantics.Result.bind, Semantics.projectResult,
                Bool.false_eq_true, ↓reduceIte]
              · exact ⟨extension, .inRight .word _, finalStore, .value leftRelated,
                  Core.LanguageResult.bind_success _ evaluation (.inRight (.first (.var rfl))),
                  finalHeap, finalInstalled, frame⟩
              · exact ⟨extension, .inRight .word _, finalStore, .value rightRelated,
                  Core.LanguageResult.bind_success _ evaluation (.inRight (.second (.var rfl))),
                  finalHeap, finalInstalled, frame⟩

theorem injection {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {operand : Expr} {result : Semantics.Result Semantics.Value}
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment operand initial result final)
    (right : Bool) (type target : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, if right then .inr target operand else .inl target operand, span⟩ initial
      (result.bind (Semantics.sumInjectionResult right target)) final := by
  intro fuel scope lowered compiled covered world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, leftType, rightType, targetCompiled, operandCompiled, operandType, rfl⟩ :=
        lowerExpression_injection_components right compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalInstalled, frame⟩ :=
        preserves operandCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          exact ⟨extension, .inLeft _ (.word reason), finalStore, .language reason,
            Core.LanguageResult.bind_failure _ evaluation, finalHeap, finalInstalled, frame⟩
      | @value sourceValue targetValue related =>
          obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape targetCompiled
          cases shape <;> try { cases targetShape }
          rename_i leftShape rightShape
          have injected : Semantics.sumInjectionResult right target sourceValue =
              .value (if right then .inr sourceValue else .inl sourceValue) := by
            simp [Semantics.sumInjectionResult, sourceShape]
          simp only [Semantics.Result.bind, injected]
          rw [operandType] at related
          cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at related ⊢
          · exact ⟨extension, .inRight .word (.inLeft rightType _), finalStore, .value (.inl related),
              Core.LanguageResult.bind_success _ evaluation (.inRight (.inLeft (.var rfl))),
              finalHeap, finalInstalled, frame⟩
          · exact ⟨extension, .inRight .word (.inRight leftType _), finalStore, .value (.inr related),
              Core.LanguageResult.bind_success _ evaluation (.inRight (.inRight (.var rfl))),
              finalHeap, finalInstalled, frame⟩

theorem conditional {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial middle final : Semantics.State σ} {conditionExpr yes no : Expr}
    {conditionValue : Semantics.Value} {result : Semantics.Result Semantics.Value}
    (truth : Bool) (tested : Semantics.condition? conditionValue = some truth)
    (conditionPreserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment conditionExpr initial (.value conditionValue) middle)
    (branchPreserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment (if truth then yes else no) middle result final)
    (type target : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, .ifThen target conditionExpr yes no, span⟩ initial result final := by
  intro fuel scope lowered compiled covered world mapping environment store environmentRelated globals runtime heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, test, yesCode, noCode, conditionCompiled, testCompiled,
        yesCompiled, noCompiled, yesType, noType, expressionEqual⟩ :=
        lowerExpression_conditional_components compiled
      obtain ⟨conditionExtension, targetCondition, middleStore, conditionRelated,
        conditionEvaluation, middleHeap, middleExternal, firstFrame⟩ :=
        conditionPreserves.value rfl conditionCompiled covered environmentRelated globals runtime heap externalRelated
      have testEvaluation := ExpressionCorrespondence.condition_evaluates
        testCompiled conditionRelated tested conditionEvaluation
      have middleEnvironment :=
        (environmentRelated.extendWorld conditionExtension).prepend [.bool truth]
      have branchCompiled : lowerExpression fuel signatures scope (if truth then yes else no) =
          .ok (if truth then yesCode else noCode) := by cases truth <;> assumption
      obtain ⟨branchExtension, targetValue, finalStore, related, branchEvaluation, finalHeap, finalExternal, lastFrame⟩ :=
        branchPreserves branchCompiled covered middleEnvironment (globals.prepend [.bool truth]) (runtime.prepend [.bool truth]) middleHeap middleExternal
      refine ⟨conditionExtension ++ branchExtension, targetValue, finalStore, ?_, ?_, ?_, finalExternal, firstFrame.trans lastFrame⟩
      · cases truth <;> simpa only [Bool.false_eq_true, ↓reduceIte, yesType, noType] using related
      · have renamed (expression : Core.Expr) : (expression.rename mapping).weakenAt 0 =
            expression.rename (fun index => 1 + mapping index) := by
          simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
          congr 1
          funext index
          simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
        rw [expressionEqual, choose_rename]
        cases truth with
        | false =>
            apply Core.LocalControl.choose_false _ testEvaluation
            simpa [renamed] using branchEvaluation
        | true =>
            apply Core.LocalControl.choose_true _ testEvaluation
            simpa [renamed] using branchEvaluation
      · simpa only [List.append_assoc] using finalHeap

theorem indexedInjection {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {operand : Expr} {result : Semantics.Result Semantics.Value}
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment operand initial result final)
    (index : Nat) (type target : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, .inK index target operand, span⟩ initial (result.bind (Semantics.injectionResult index target)) final := by
  intro fuel scope lowered compiled covered world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, targetType, injected, targetCompiled, operandCompiled, injectionCompiled, rfl⟩ :=
        lowerExpression_indexedInjection_components compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalInstalled, frame⟩ :=
        preserves operandCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          exact ⟨extension, .inLeft _ (.word reason), finalStore, .language reason,
            Core.LanguageResult.bind_failure _ evaluation, finalHeap, finalInstalled, frame⟩
      | @value sourceValue targetValue related =>
          obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape targetCompiled
          rw [← targetShape] at injectionCompiled
          have supplied : Core.Evaluates (targetValue :: environment) finalStore
              ((Core.Expr.var 0).rename (Core.Renaming.lift mapping)) targetValue finalStore := .var rfl
          obtain ⟨sourceInjected, targetInjected, sourceInjection, injectionRelated, injectionEvaluation⟩ :=
            PureExpressionCorrespondence.inject_evaluates shape related injectionCompiled supplied
          refine ⟨extension, .inRight .word targetInjected, finalStore, ?_, ?_, finalHeap, finalInstalled, frame⟩
          · simpa [Semantics.Result.bind, Semantics.injectionResult, Semantics.inject?,
              sourceShape, sourceInjection, targetShape] using ResultRel.value injectionRelated
          · exact Core.LanguageResult.bind_success _ evaluation (.inRight injectionEvaluation)

/-- A failing condition skips both branches and preserves the condition's heap. -/
theorem conditional_fault {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {conditionExpr yes no : Expr} {reason : Semantics.Fault}
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment conditionExpr initial (.fault reason) final)
    (type target : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, .ifThen target conditionExpr yes no, span⟩ initial (.fault reason) final := by
  intro fuel scope lowered compiled covered world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, test, yesCode, noCode, conditionCompiled, testCompiled,
        _, _, _, _, expressionEqual⟩ := lowerExpression_conditional_components compiled
      obtain ⟨extension, value, finalStore, related, evaluated, finalHeap, finalInstalled, frame⟩ :=
        preserves conditionCompiled covered locals globals runtime heap installed
      cases related with
      | language reason =>
          refine ⟨extension, .inLeft _ (.word reason), finalStore, .language reason,
            ?_, finalHeap, finalInstalled, frame⟩
          rw [expressionEqual, choose_rename]
          exact Core.LocalControl.choose_failure _
            (ExpressionCorrespondence.condition_failure testCompiled evaluated)

/-- A compiled condition whose operand has a represented value cannot produce
the independent semantics' malformed-condition observation. -/
theorem conditional_invalid {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {conditionExpr yes no : Expr} {sourceValue : Semantics.Value}
    (preserves : ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment conditionExpr initial (.value sourceValue) final)
    (invalid : Semantics.condition? sourceValue = none) (type target : Ty) (span : Option Span) :
    ExprSimulation (model := model) (slots := slots) signatures codes locations captured sourceEnvironment
      ⟨type, .ifThen target conditionExpr yes no, span⟩ initial
      (.fault (.invalidValue "condition")) final := by
  intro fuel scope lowered compiled covered world mapping environment store locals globals runtime heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, test, _, _, conditionCompiled, testCompiled, _⟩ :=
        lowerExpression_conditional_components compiled
      obtain ⟨_, _, _, related, _⟩ := preserves.value rfl conditionCompiled covered locals globals runtime heap installed
      obtain ⟨truth, valid⟩ := condition_valid testCompiled related
      rw [invalid] at valid
      cases valid

end Solcore.Frontend.RustHull.DerivationCorrespondence
