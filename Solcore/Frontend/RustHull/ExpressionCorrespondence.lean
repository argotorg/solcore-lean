import Solcore.Frontend.RustHull.LiteralCorrespondence
import Solcore.Frontend.RustHull.LoweringStructure
import Solcore.Core.Derived

/-! Operational correspondence for the expressions produced by the actual
Hull lowerer. Arbitrary variable renamings account for inserted Core binders
while retaining the caller's exact heap and stored function captures. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.ExpressionCorrespondence

open Correspondence

theorem boolean_evaluates {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    {value : Bool} {expression : Core.Expr}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    (compiled : boolean type (.bool value) = .ok expression)
    (mapping : Core.Renaming) (environment : Core.Environment) (store : Core.Store) :
    ∃ source target, Semantics.boolean? sourceType value = some source ∧
      ValueRel type source target ∧
      Core.Evaluates environment store (expression.rename mapping) target store := by
  obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape typeCompiled
  by_cases native : type = .bool
  · have same : shape = .bool := coreType_injective (targetShape.trans native)
    subst shape
    simp only [boolean, native, ↓reduceIte] at compiled
    cases compiled
    rw [native]
    exact ⟨.bool value, .bool value, by simp [Semantics.boolean?, sourceShape], .bool _, .bool⟩
  · by_cases sum : type = .sum .unit .unit
    · have same : shape = .sum .unit .unit := coreType_injective (targetShape.trans sum)
      subst shape
      simp only [boolean, sum, ↓reduceIte] at compiled
      cases compiled
      rw [sum]
      cases value with
      | false =>
          exact ⟨.inl .unit, .inLeft .unit .unit,
            by simp [Semantics.boolean?, sourceShape], .inl .unit, .ifFalse .bool (.inLeft .unit)⟩
      | true =>
          exact ⟨.inr .unit, .inRight .unit .unit,
            by simp [Semantics.boolean?, sourceShape], .inr .unit, .ifTrue .bool (.inRight .unit)⟩
    · simp [boolean, native, sum, fail] at compiled

theorem condition_evaluates {lowered : Lowered} {expression : Core.Expr}
    {source : Semantics.Value} {target : Core.Value} {value : Bool}
    (compiled : condition lowered = .ok expression)
    (related : ValueRel lowered.type source target)
    (truth : Semantics.condition? source = some value)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial (lowered.expression.rename mapping)
      (.inRight .word target) final) :
    Core.Evaluates environment initial (expression.rename mapping)
      (.inRight .word (.bool value)) final := by
  by_cases native : lowered.type = .bool
  · simp only [condition, native, ↓reduceIte] at compiled
    cases compiled
    rw [native] at related
    cases related with
    | bool result =>
        simp only [Semantics.condition?, Option.some.injEq] at truth
        cases truth
        exact evaluated
  · by_cases sum : lowered.type = .sum .unit .unit
    · simp only [condition, sum, ↓reduceIte] at compiled
      cases compiled
      rw [sum] at related
      cases related with
      | inl payload =>
          cases payload
          simp only [Semantics.condition?, Option.some.injEq] at truth
          cases truth
          exact Core.LanguageResult.bind_success _ evaluated
            (.caseLeft (.var rfl) (.inRight .bool))
      | inr payload =>
          cases payload
          simp only [Semantics.condition?, Option.some.injEq] at truth
          cases truth
          exact Core.LanguageResult.bind_success _ evaluated
            (.caseRight (.var rfl) (.inRight .bool))
    · simp [condition, native, sum, fail] at compiled

theorem condition_failure {lowered : Lowered} {expression : Core.Expr} {reason : Core.Word}
    (compiled : condition lowered = .ok expression)
    {mapping : Core.Renaming} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial (lowered.expression.rename mapping)
      (.inLeft lowered.type (.word reason)) final) :
    Core.Evaluates environment initial (expression.rename mapping)
      (.inLeft .bool (.word reason)) final := by
  by_cases native : lowered.type = .bool
  · simp only [condition, native, ↓reduceIte] at compiled
    cases compiled
    simpa only [native] using evaluated
  · by_cases sum : lowered.type = .sum .unit .unit
    · simp only [condition, sum, ↓reduceIte] at compiled
      cases compiled
      exact Core.LanguageResult.bind_failure _ evaluated
    · simp [condition, native, sum, fail] at compiled

theorem bool {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {expression : Expr} {value : Bool} {lowered : Lowered}
    (kind : expression.kind = .bool value)
    (compiled : lowerExpression fuel signatures scope expression = .ok lowered)
    (mapping : Core.Renaming) (environment : Core.Environment) (store : Core.Store) :
    ∃ target, ResultRel lowered.type (Semantics.booleanResult expression.ty value) target ∧
      Core.Evaluates environment store (lowered.expression.rename mapping) target store := by
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      simp only [lowerExpression, kind] at compiled
      obtain ⟨type, typeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨code, boolCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      dsimp only [Bind.bind, Except.bind, Pure.pure] at compiled
      obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
      cases checked
      cases returned
      obtain ⟨source, target, parsed, related, evaluated⟩ :=
        boolean_evaluates typeCompiled boolCompiled mapping environment store
      refine ⟨.inRight .word target, ?_, .inRight evaluated⟩
      simpa only [Semantics.booleanResult, parsed] using ResultRel.value related

theorem word {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {expression : Expr} {text : String} {lowered : Lowered}
    (kind : expression.kind = .word text)
    (compiled : lowerExpression fuel signatures scope expression = .ok lowered)
    (mapping : Core.Renaming) (environment : Core.Environment) (store : Core.Store) :
    ∃ value, ResultRel lowered.type (Semantics.literalResult text) value ∧
      Core.Evaluates environment store (lowered.expression.rename mapping) value store := by
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      simp only [lowerExpression, kind] at compiled
      obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨value, parsed, compiled⟩ := lower_bind_eq_ok.mp compiled
      dsimp only [Bind.bind, Except.bind, Pure.pure] at compiled
      obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
      cases checked
      cases returned
      rw [Semantics.literalResult, parseWord_some_of_ok parsed]
      exact ⟨_, .value (.word value), .inRight .word⟩

theorem unit {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {expression : Expr} {lowered : Lowered}
    (kind : expression.kind = .unit)
    (compiled : lowerExpression fuel signatures scope expression = .ok lowered)
    (mapping : Core.Renaming) (environment : Core.Environment) (store : Core.Store) :
    ResultRel lowered.type (.value .unit) (.inRight .word .unit) ∧
      Core.Evaluates environment store (lowered.expression.rename mapping)
        (.inRight .word .unit) store := by
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      simp only [lowerExpression, kind] at compiled
      obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      dsimp only [Bind.bind, Except.bind, Pure.pure] at compiled
      obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
      cases checked
      cases returned
      exact ⟨.value .unit, .inRight .unit⟩

theorem read {world : World} {sourceEnvironment : Semantics.Environment}
    {sourceHeap : Semantics.Heap} {scope : Scope} {mapping : Core.Renaming}
    {environment : Core.Environment} {store : Core.Store}
    (envRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heapRelated : HeapRel world sourceHeap store)
    {name : String} {location : Nat} {sourceValue : Semantics.Value} {lowered : Lowered}
    (found : Semantics.lookupLocation sourceEnvironment name = some location)
    (read : sourceHeap[location]? = some sourceValue)
    (compiled : scope.read name = .ok lowered) :
    ∃ value, ValueRel lowered.type sourceValue value ∧
      Core.Evaluates environment store (lowered.expression.rename mapping)
        (.inRight .word value) store := by
  unfold Scope.read at compiled
  obtain ⟨⟨binding, index⟩, lookup, returned⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨targetLocation, value, reference, variableLookup, initialized, related⟩ :=
    envRelated.read heapRelated found lookup read
  simp only [reference, ↓reduceIte] at returned
  cases returned
  refine ⟨value, related, ?_⟩
  exact Core.OptionalCell.read_success _ (.var variableLookup) initialized

end Solcore.Frontend.RustHull.ExpressionCorrespondence
