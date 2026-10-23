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

end Solcore.Frontend.RustHull.PureExpressionCorrespondence
