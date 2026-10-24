import Solcore.Frontend.RustHull.StructuralExpressionCorrespondence

/-! Indexed source sum injections agree with the nested sums emitted by the
actual compiler, including transparent named layouts and the final payload. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.PureExpressionCorrespondence

open Correspondence StatementCorrespondence

theorem inject_evaluates (shape : Semantics.Shape) {index : Nat} {payloadType : Core.Ty}
    {source : Semantics.Value} {target : Core.Value} (related : ValueRel payloadType source target)
    {value expression : Core.Expr}
    (compiled : inject index (coreType shape) payloadType value = .ok expression)
    {environment : Core.Environment} {initial final : Core.Store} {mapping : Core.Renaming}
    (evaluated : Core.Evaluates environment initial (value.rename mapping) target final) :
    ∃ sourceResult targetResult,
      Semantics.injectShape? index shape source = some sourceResult ∧
      ValueRel (coreType shape) sourceResult targetResult ∧
      Core.Evaluates environment initial (expression.rename mapping) targetResult final := by
  induction shape generalizing index expression with
  | sum left right _ ih =>
      by_cases zero : index = 0
      · subst index
        simp only [coreType, inject, ↓reduceIte] at compiled
        obtain ⟨checked, matched, returned⟩ := lower_bind_eq_ok.mp compiled
        cases checked
        cases returned
        have same := expectType_eq_of_ok matched
        exact ⟨.inl source, .inLeft (coreType right) target,
          by simp [Semantics.injectShape?], .inl (same ▸ related), .inLeft evaluated⟩
      · simp only [coreType, inject, zero, ↓reduceIte] at compiled
        obtain ⟨nested, nestedCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
        cases returned
        obtain ⟨sourceResult, targetResult, injected, resultRelated, resultEvaluated⟩ := ih nestedCompiled
        exact ⟨.inr sourceResult, .inRight (coreType left) targetResult,
          by simp [Semantics.injectShape?, zero, injected], .inr resultRelated, .inRight resultEvaluated⟩
  | word | bool | unit | product =>
      by_cases zero : index = 0
      · subst index
        simp only [coreType, inject, ↓reduceIte] at compiled
        obtain ⟨checked, matched, returned⟩ := lower_bind_eq_ok.mp compiled
        cases checked
        cases returned
        have same := expectType_eq_of_ok matched
        exact ⟨source, target, by simp [Semantics.injectShape?],
          by simpa only [coreType, same] using related, evaluated⟩
      · simp [coreType, inject, zero, fail, Bind.bind, Except.bind] at compiled

private theorem indexedInjection_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type target : Ty} {operand : Expr} {index : Nat}
    {span : Option Span} {sourceValue : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .inK index target operand, span⟩ initial (.value sourceValue) final) :
    ∃ value, Semantics.EvalExpr functions effects sourceEnvironment operand initial (.value value) final ∧
      Semantics.injectionResult index target value = .value sourceValue := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases evaluated <;> simp_all
  rename_i otherIndex otherTarget otherOperand operandResult kind evaluated
  cases operandResult with
  | fault reason => simp [Semantics.Result.bind] at resultEq
  | value value => exact ⟨value, evaluated, rfl⟩

theorem indexedInjection {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {external : σ → Core.Store → Prop}
    {operand : Expr} (preserves : NormalExprPreserves functions effects signatures external operand)
    (index : Nat) (type target : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external
      ⟨type, .inK index target operand, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨value, sourceEvaluation, sourceResult⟩ := indexedInjection_source evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, targetType, injected, targetCompiled, operandCompiled, injectionCompiled, rfl⟩ :=
        lowerExpression_indexedInjection_components compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
        preserves sourceEvaluation operandCompiled environmentRelated heap externalRelated
      obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape targetCompiled
      rw [← targetShape] at injectionCompiled
      have supplied : Core.Evaluates (targetValue :: environment) finalStore
          ((Core.Expr.var 0).rename (Core.Renaming.lift mapping)) targetValue finalStore := .var rfl
      obtain ⟨sourceInjected, targetInjected, sourceInjection, injectionRelated, injectionEvaluation⟩ :=
        inject_evaluates shape related injectionCompiled supplied
      have same : sourceInjected = sourceValue := by
        simpa [Semantics.injectionResult, Semantics.inject?, sourceShape, sourceInjection] using sourceResult
      subst sourceInjected
      refine ⟨extension, targetInjected, finalStore, ?_, ?_, finalHeap, finalExternal⟩
      · simpa only [targetShape] using injectionRelated
      · exact Core.LanguageResult.bind_success _ evaluation (.inRight injectionEvaluation)

end Solcore.Frontend.RustHull.PureExpressionCorrespondence
