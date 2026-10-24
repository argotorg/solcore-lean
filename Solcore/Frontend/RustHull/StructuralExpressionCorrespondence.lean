import Solcore.Frontend.RustHull.PureExpressionCorrespondence

/-! Compositional correspondence for local reads and structured Hull values.
Every compiler premise refers to the actual lowering function. The source
premises are the independent evaluation rules, including their evaluation order.
-/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.PureExpressionCorrespondence

open Correspondence StatementCorrespondence

theorem read {σ : Type} (functions : List Function) (effects : Semantics.ExternalSemantics σ)
    (signatures : List Signature) (external : σ → Core.Store → Prop)
    (type : Ty) (name : String) (span : Option Span) :
    NormalExprPreserves functions effects signatures external ⟨type, .var name, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  have same : final = initial ∧
      Semantics.readResult sourceEnvironment initial name = .value sourceValue := by
    generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
    cases evaluated <;> simp_all
  rcases same with ⟨rfl, sourceResult⟩
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  unfold Semantics.readResult at sourceResult
  cases found : Semantics.lookupLocation sourceEnvironment name with
  | none => simp [found] at sourceResult
  | some location =>
      simp only [found] at sourceResult
      cases loaded : final.heap[location]? with
      | none => simp [loaded] at sourceResult
      | some value =>
          simp only [loaded, Semantics.Result.value.injEq] at sourceResult
          subst value
          obtain ⟨targetValue, related, evaluated⟩ :=
            variable_evaluates compiled environmentRelated heap found loaded
          exact ⟨[], targetValue, store, related, evaluated, by simpa using heap, externalRelated⟩

private theorem pair_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type : Ty} {left right : Expr}
    {span : Option Span} {sourceValue : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment ⟨type, .pair left right, span⟩
      initial (.value sourceValue) final) :
    ∃ leftValue rightValue middle,
      sourceValue = .pair leftValue rightValue ∧
      Semantics.EvalExpr functions effects sourceEnvironment left initial (.value leftValue) middle ∧
      Semantics.EvalExpr functions effects sourceEnvironment right middle (.value rightValue) final := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases evaluated <;> simp_all
  rename_i middle otherLeft otherRight leftValue rightResult kind first second
  cases rightResult with
  | fault reason => simp [Semantics.Result.map] at resultEq
  | value rightValue =>
      simp only [Semantics.Result.map, Semantics.Result.value.injEq] at resultEq
      exact ⟨leftValue, rightValue, resultEq, middle, first, second⟩

theorem pair_rename (leftType rightType : Core.Ty) (left right : Core.Expr)
    (mapping : Core.Renaming) :
    (Core.LocalSequence.pair leftType rightType left right).rename mapping =
      Core.LocalSequence.pair leftType rightType (left.rename mapping) (right.rename mapping) := by
  simp [Core.LocalSequence.pair, Core.LanguageResult.bind, Core.LanguageResult.success,
    Core.Expr.rename, Core.Renaming.lift]

theorem pair {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {external : σ → Core.Store → Prop}
    {left right : Expr} (leftPreserves : NormalExprPreserves functions effects signatures external left)
    (rightPreserves : NormalExprPreserves functions effects signatures external right)
    (type : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external ⟨type, .pair left right, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨leftValue, rightValue, middle, rfl, leftSource, rightSource⟩ := pair_source evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨leftCode, rightCode, leftCompiled, rightCompiled, rfl⟩ :=
        lowerExpression_pair_components compiled
      obtain ⟨leftExtension, targetLeft, middleStore, leftRelated, leftEvaluation, middleHeap, middleExternal⟩ :=
        leftPreserves leftSource leftCompiled environmentRelated heap externalRelated
      have middleEnvironment := (environmentRelated.extendWorld leftExtension).prepend [targetLeft]
      obtain ⟨rightExtension, targetRight, finalStore, rightRelated, rightEvaluation, finalHeap, finalExternal⟩ :=
        rightPreserves rightSource rightCompiled middleEnvironment middleHeap middleExternal
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

private theorem projection_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type : Ty} {operand : Expr}
    {span : Option Span} {sourceValue : Semantics.Value} (right : Bool)
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, if right then .snd operand else .fst operand, span⟩ initial (.value sourceValue) final) :
    ∃ value, Semantics.EvalExpr functions effects sourceEnvironment operand initial (.value value) final ∧
      Semantics.projectResult right value = .value sourceValue := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases right <;> cases evaluated <;> simp_all
  all_goals
    rename_i otherOperand operandResult kind evaluated
    cases operandResult with
    | fault reason => simp [Semantics.Result.bind] at resultEq
    | value value => exact ⟨value, evaluated, rfl⟩

theorem projection {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {external : σ → Core.Store → Prop}
    {operand : Expr} (preserves : NormalExprPreserves functions effects signatures external operand)
    (right : Bool) (type : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external
      ⟨type, if right then .snd operand else .fst operand, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨value, sourceEvaluation, projected⟩ := projection_source right evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, leftType, rightType, operandCompiled, operandType, rfl⟩ :=
        lowerExpression_projection_components right compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
        preserves sourceEvaluation operandCompiled environmentRelated heap externalRelated
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

private theorem injection_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type target : Ty} {operand : Expr}
    {span : Option Span} {sourceValue : Semantics.Value} (right : Bool)
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, if right then .inr target operand else .inl target operand, span⟩
      initial (.value sourceValue) final) :
    ∃ value, Semantics.EvalExpr functions effects sourceEnvironment operand initial (.value value) final ∧
      sourceValue = (if right then .inr value else .inl value) := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases right <;> cases evaluated <;> simp_all
  all_goals
    rename_i otherTarget otherOperand operandResult kind evaluated
    cases operandResult with
    | fault reason => simp [Semantics.Result.bind] at resultEq
    | value value =>
        cases found : Semantics.shape otherTarget with
        | none => simp [Semantics.Result.bind, Semantics.sumInjectionResult, found] at resultEq
        | some shape =>
            cases shape <;> simp [Semantics.Result.bind, Semantics.sumInjectionResult, found] at resultEq
            exact ⟨value, evaluated, resultEq⟩

theorem injection {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {external : σ → Core.Store → Prop}
    {operand : Expr} (preserves : NormalExprPreserves functions effects signatures external operand)
    (right : Bool) (type target : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external
      ⟨type, if right then .inr target operand else .inl target operand, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨value, sourceEvaluation, rfl⟩ := injection_source right evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, leftType, rightType, _, operandCompiled, operandType, rfl⟩ :=
        lowerExpression_injection_components right compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
        preserves sourceEvaluation operandCompiled environmentRelated heap externalRelated
      rw [operandType] at related
      cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at related ⊢
      · exact ⟨extension, .inLeft rightType targetValue, finalStore, .inl related,
          Core.LanguageResult.bind_success _ evaluation (.inRight (.inLeft (.var rfl))),
          finalHeap, finalExternal⟩
      · exact ⟨extension, .inRight leftType targetValue, finalStore, .inr related,
          Core.LanguageResult.bind_success _ evaluation (.inRight (.inRight (.var rfl))),
          finalHeap, finalExternal⟩

private theorem conditional_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type target : Ty} {conditionExpr yes no : Expr}
    {span : Option Span} {sourceValue : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .ifThen target conditionExpr yes no, span⟩ initial (.value sourceValue) final) :
    ∃ middle value truth,
      Semantics.EvalExpr functions effects sourceEnvironment conditionExpr initial (.value value) middle ∧
      Semantics.condition? value = some truth ∧
      Semantics.EvalExpr functions effects sourceEnvironment (if truth then yes else no)
        middle (.value sourceValue) final := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases evaluated <;> simp_all
  case ifTrue => exact ⟨_, _, by assumption, Or.inr ⟨by assumption, by assumption⟩⟩
  case ifFalse => exact ⟨_, _, by assumption, Or.inl ⟨by assumption, by assumption⟩⟩

theorem choose_rename (type : Core.Ty) (conditionExpr yes no : Core.Expr) (mapping : Core.Renaming) :
    (Core.LocalControl.choose type conditionExpr yes no).rename mapping =
      Core.LocalControl.choose type (conditionExpr.rename mapping) (yes.rename mapping) (no.rename mapping) := by
  simp [Core.LocalControl.choose, Core.LanguageResult.bind, Core.Expr.rename, Core.Renaming.lift]

theorem conditional {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {external : σ → Core.Store → Prop}
    {conditionExpr yes no : Expr}
    (conditionPreserves : NormalExprPreserves functions effects signatures external conditionExpr)
    (yesPreserves : NormalExprPreserves functions effects signatures external yes)
    (noPreserves : NormalExprPreserves functions effects signatures external no)
    (type target : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external
      ⟨type, .ifThen target conditionExpr yes no, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨middle, conditionValue, truth, conditionSource, tested, branchSource⟩ := conditional_source evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, test, yesCode, noCode, conditionCompiled, testCompiled,
        yesCompiled, noCompiled, yesType, noType, expressionEqual⟩ :=
        lowerExpression_conditional_components compiled
      obtain ⟨conditionExtension, targetCondition, middleStore, conditionRelated,
        conditionEvaluation, middleHeap, middleExternal⟩ :=
        conditionPreserves conditionSource conditionCompiled environmentRelated heap externalRelated
      have testEvaluation := ExpressionCorrespondence.condition_evaluates
        testCompiled conditionRelated tested conditionEvaluation
      have middleEnvironment :=
        (environmentRelated.extendWorld conditionExtension).prepend [.bool truth]
      have branchPreserves : NormalExprPreserves functions effects signatures external
          (if truth then yes else no) := by cases truth <;> assumption
      have branchCompiled : lowerExpression fuel signatures scope (if truth then yes else no) =
          .ok (if truth then yesCode else noCode) := by cases truth <;> assumption
      obtain ⟨branchExtension, targetValue, finalStore, related, branchEvaluation, finalHeap, finalExternal⟩ :=
        branchPreserves branchSource branchCompiled middleEnvironment middleHeap middleExternal
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

end Solcore.Frontend.RustHull.PureExpressionCorrespondence
