import Solcore.Frontend.RustHull.DerivationCorrespondenceSupport
import Solcore.Frontend.RustHull.ContextualExpressionCorrespondence

/-! Structural expression simulation consumes only the child executions in a
finite independent Hull derivation. Named calls may recur in those children. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence StatementCorrespondence ContextualExpressionCorrespondence

theorem ExprSimulation.of_contextual {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {env : Semantics.Environment} {expression : Expr} {initial final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects env expression initial result final)
    (preserves : NamedCallCorrespondence.ContextualExprPreserves functions effects signatures codes locations captured expression) :
    ExprSimulation signatures codes locations captured env expression initial result final := by
  intro source successful
  subst result
  exact preserves evaluated

theorem pair {σ : Type} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial middle final : Semantics.State σ} {left right : Expr}
    {leftValue : Semantics.Value} {rightResult : Semantics.Result Semantics.Value}
    (leftPreserves : ExprSimulation signatures codes locations captured sourceEnvironment left initial (.value leftValue) middle)
    (rightPreserves : ExprSimulation signatures codes locations captured sourceEnvironment right middle rightResult final)
    (type : Ty) (span : Option Span) :
    ExprSimulation signatures codes locations captured sourceEnvironment ⟨type, .pair left right, span⟩
      initial (rightResult.map (Semantics.Value.pair leftValue)) final := by
  intro sourceValue successful
  cases rightResult with
  | fault reason => cases successful
  | value rightValue =>
    simp only [Semantics.Result.map, Semantics.Result.value.injEq] at successful
    subst sourceValue
    intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
    cases fuel with
    | zero => simp [lowerExpression, fail] at compiled
    | succ fuel =>
        obtain ⟨leftCode, rightCode, leftCompiled, rightCompiled, rfl⟩ :=
          lowerExpression_pair_components compiled
        obtain ⟨leftExtension, targetLeft, middleStore, leftRelated, leftEvaluation, middleHeap, middleExternal⟩ :=
          leftPreserves rfl leftCompiled environmentRelated globals heap externalRelated
        have middleEnvironment := (environmentRelated.extendWorld leftExtension).prepend [targetLeft]
        obtain ⟨rightExtension, targetRight, finalStore, rightRelated, rightEvaluation, finalHeap, finalExternal⟩ :=
          rightPreserves rfl rightCompiled middleEnvironment (globals.prepend [targetLeft]) middleHeap middleExternal
        refine ⟨leftExtension ++ rightExtension, .pair targetLeft targetRight, finalStore,
          .pair leftRelated rightRelated, ?_, ?_, finalExternal⟩
        · have renamed : (rightCode.expression.rename mapping).weakenAt 0 =
              rightCode.expression.rename (fun index => 1 + mapping index) := by
            simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
            congr 1
            funext index
            simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
          change Core.Evaluates environment store
            ((Core.LocalSequence.pair leftCode.type rightCode.type
              leftCode.expression rightCode.expression).rename mapping) _ _
          rw [pair_rename]
          apply Core.LocalSequence.pair_success _ _ leftEvaluation
          simpa [renamed] using rightEvaluation
        · simpa only [List.append_assoc] using finalHeap

theorem projection {σ : Type} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {operand : Expr} {result : Semantics.Result Semantics.Value}
    (preserves : ExprSimulation signatures codes locations captured sourceEnvironment operand initial result final)
    (right : Bool) (type : Ty) (span : Option Span) :
    ExprSimulation signatures codes locations captured sourceEnvironment
      ⟨type, if right then .snd operand else .fst operand, span⟩ initial
      (result.bind (Semantics.projectResult right)) final := by
  intro sourceValue successful
  cases result with
  | fault reason => cases successful
  | value value =>
    have projected : Semantics.projectResult right value = .value sourceValue := successful
    intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
    cases fuel with
    | zero => simp [lowerExpression, fail] at compiled
    | succ fuel =>
        obtain ⟨operandCode, leftType, rightType, operandCompiled, operandType, rfl⟩ :=
          lowerExpression_projection_components right compiled
        obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
          preserves rfl operandCompiled environmentRelated globals heap externalRelated
        rw [operandType] at related
        cases related with
        | pair leftRelated rightRelated =>
            cases right <;> simp only [Semantics.projectResult, Bool.false_eq_true, ↓reduceIte,
              Semantics.Result.value.injEq] at projected ⊢
            all_goals cases projected
            · exact ⟨extension, _, finalStore, leftRelated,
                Core.LanguageResult.bind_success _ evaluation (.inRight (.first (.var rfl))),
                finalHeap, finalExternal⟩
            · exact ⟨extension, _, finalStore, rightRelated,
                Core.LanguageResult.bind_success _ evaluation (.inRight (.second (.var rfl))),
                finalHeap, finalExternal⟩

theorem injection {σ : Type} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {operand : Expr} {result : Semantics.Result Semantics.Value}
    (preserves : ExprSimulation signatures codes locations captured sourceEnvironment operand initial result final)
    (right : Bool) (type target : Ty) (span : Option Span) :
    ExprSimulation signatures codes locations captured sourceEnvironment
      ⟨type, if right then .inr target operand else .inl target operand, span⟩ initial
      (result.bind (Semantics.sumInjectionResult right target)) final := by
  intro sourceValue successful
  cases result with
  | fault reason => cases successful
  | value value =>
    have same : sourceValue = (if right then .inr value else .inl value) := by
      cases found : Semantics.shape target with
      | none => simp [Semantics.Result.bind, Semantics.sumInjectionResult, found] at successful
      | some shape =>
        cases shape <;> simp [Semantics.Result.bind, Semantics.sumInjectionResult, found] at successful
        exact successful.symm
    subst sourceValue
    intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
    cases fuel with
    | zero => simp [lowerExpression, fail] at compiled
    | succ fuel =>
        obtain ⟨operandCode, leftType, rightType, _, operandCompiled, operandType, rfl⟩ :=
          lowerExpression_injection_components right compiled
        obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
          preserves rfl operandCompiled environmentRelated globals heap externalRelated
        rw [operandType] at related
        cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at related ⊢
        · exact ⟨extension, .inLeft rightType targetValue, finalStore, .inl related,
            Core.LanguageResult.bind_success _ evaluation (.inRight (.inLeft (.var rfl))),
            finalHeap, finalExternal⟩
        · exact ⟨extension, .inRight leftType targetValue, finalStore, .inr related,
            Core.LanguageResult.bind_success _ evaluation (.inRight (.inRight (.var rfl))),
            finalHeap, finalExternal⟩

theorem conditional {σ : Type} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial middle final : Semantics.State σ} {conditionExpr yes no : Expr}
    {conditionValue : Semantics.Value} {result : Semantics.Result Semantics.Value}
    (truth : Bool) (tested : Semantics.condition? conditionValue = some truth)
    (conditionPreserves : ExprSimulation signatures codes locations captured sourceEnvironment conditionExpr initial (.value conditionValue) middle)
    (branchPreserves : ExprSimulation signatures codes locations captured sourceEnvironment (if truth then yes else no) middle result final)
    (type target : Ty) (span : Option Span) :
    ExprSimulation signatures codes locations captured sourceEnvironment
      ⟨type, .ifThen target conditionExpr yes no, span⟩ initial result final := by
  intro sourceValue successful
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, test, yesCode, noCode, conditionCompiled, testCompiled,
        yesCompiled, noCompiled, yesType, noType, expressionEqual⟩ :=
        lowerExpression_conditional_components compiled
      obtain ⟨conditionExtension, targetCondition, middleStore, conditionRelated,
        conditionEvaluation, middleHeap, middleExternal⟩ :=
        conditionPreserves rfl conditionCompiled environmentRelated globals heap externalRelated
      have testEvaluation := ExpressionCorrespondence.condition_evaluates
        testCompiled conditionRelated tested conditionEvaluation
      have middleEnvironment :=
        (environmentRelated.extendWorld conditionExtension).prepend [.bool truth]
      have branchCompiled : lowerExpression fuel signatures scope (if truth then yes else no) =
          .ok (if truth then yesCode else noCode) := by cases truth <;> assumption
      obtain ⟨branchExtension, targetValue, finalStore, related, branchEvaluation, finalHeap, finalExternal⟩ :=
        branchPreserves successful branchCompiled middleEnvironment (globals.prepend [.bool truth]) middleHeap middleExternal
      refine ⟨conditionExtension ++ branchExtension, targetValue, finalStore, ?_, ?_, ?_, finalExternal⟩
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

theorem indexedInjection {σ : Type} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {operand : Expr} {result : Semantics.Result Semantics.Value}
    (preserves : ExprSimulation signatures codes locations captured sourceEnvironment operand initial result final)
    (index : Nat) (type target : Ty) (span : Option Span) :
    ExprSimulation signatures codes locations captured sourceEnvironment
      ⟨type, .inK index target operand, span⟩ initial (result.bind (Semantics.injectionResult index target)) final := by
  intro sourceValue successful
  cases result with
  | fault reason => cases successful
  | value value =>
    have sourceResult : Semantics.injectionResult index target value = .value sourceValue := successful
    intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
    cases fuel with
    | zero => simp [lowerExpression, fail] at compiled
    | succ fuel =>
        obtain ⟨operandCode, targetType, injected, targetCompiled, operandCompiled, injectionCompiled, rfl⟩ :=
          lowerExpression_indexedInjection_components compiled
        obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
          preserves rfl operandCompiled environmentRelated globals heap externalRelated
        obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape targetCompiled
        rw [← targetShape] at injectionCompiled
        have supplied : Core.Evaluates (targetValue :: environment) finalStore
            ((Core.Expr.var 0).rename (Core.Renaming.lift mapping)) targetValue finalStore := .var rfl
        obtain ⟨sourceInjected, targetInjected, sourceInjection, injectionRelated, injectionEvaluation⟩ :=
          PureExpressionCorrespondence.inject_evaluates shape related injectionCompiled supplied
        have same : sourceInjected = sourceValue := by
          simpa [Semantics.injectionResult, Semantics.inject?, sourceShape, sourceInjection] using sourceResult
        subst sourceInjected
        refine ⟨extension, targetInjected, finalStore, ?_, ?_, finalHeap, finalExternal⟩
        · simpa only [targetShape] using injectionRelated
        · exact Core.LanguageResult.bind_success _ evaluation (.inRight injectionEvaluation)

end Solcore.Frontend.RustHull.DerivationCorrespondence
