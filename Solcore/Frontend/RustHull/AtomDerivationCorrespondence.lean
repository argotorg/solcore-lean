import Solcore.Frontend.RustHull.DerivationCorrespondenceSupport
import Solcore.Frontend.RustHull.ExpressionCorrespondence

/-! Actual successful lowering and represented source bindings rule out malformed
literal and variable observations. No source-result classification is assumed. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCorrespondence
open Correspondence

theorem word {σ : Type} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {env : Semantics.Environment}
    {expression : Expr} {initial : Semantics.State σ} {text : String}
    (kind : expression.kind = .word text) :
    ExprSimulation signatures codes locations captured env expression initial
      (Semantics.literalResult text) initial := by
  intro fuel scope lowered compiled _ world mapping environment store _ _ heap installed
  obtain ⟨target, related, evaluated⟩ := ExpressionCorrespondence.word kind compiled mapping environment store
  exact ⟨[], target, store, related, evaluated, by simpa using heap, installed, ClosuresPreserved.refl store⟩

theorem bool {σ : Type} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {env : Semantics.Environment}
    {expression : Expr} {initial : Semantics.State σ} {value : Bool}
    (kind : expression.kind = .bool value) :
    ExprSimulation signatures codes locations captured env expression initial
      (Semantics.booleanResult expression.ty value) initial := by
  intro fuel scope lowered compiled _ world mapping environment store _ _ heap installed
  obtain ⟨target, related, evaluated⟩ := ExpressionCorrespondence.bool kind compiled mapping environment store
  exact ⟨[], target, store, related, evaluated, by simpa using heap, installed, ClosuresPreserved.refl store⟩

theorem unit {σ : Type} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {env : Semantics.Environment}
    {expression : Expr} {initial : Semantics.State σ}
    (kind : expression.kind = .unit) :
    ExprSimulation signatures codes locations captured env expression initial (.value .unit) initial := by
  intro fuel scope lowered compiled _ world mapping environment store _ _ heap installed
  obtain ⟨related, evaluated⟩ := ExpressionCorrespondence.unit kind compiled mapping environment store
  exact ⟨[], _, store, related, evaluated, by simpa using heap, installed, ClosuresPreserved.refl store⟩

theorem var {σ : Type} {signatures : List Signature} {codes : List GlobalCode}
    {locations : Nat → Nat} {captured : Core.Environment} {env : Semantics.Environment}
    {expression : Expr} {initial : Semantics.State σ} {name : String}
    (kind : expression.kind = .var name) :
    ExprSimulation signatures codes locations captured env expression initial
      (Semantics.readResult env initial name) initial := by
  intro fuel scope lowered compiled covered world mapping environment store locals _ heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      simp only [lowerExpression, kind] at compiled
      obtain ⟨expected, _, compiled⟩ := lower_bind_eq_ok.mp compiled
      cases allowed : name.startsWith Effects.reservedPrefix with
      | true => simp [allowed, fail, lower_bind_eq_ok] at compiled
      | false =>
          simp only [allowed, Bool.false_eq_true, ↓reduceIte] at compiled
          obtain ⟨readCode, readCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
          obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
          cases checked
          cases returned
          have originalRead := readCompiled
          unfold Scope.read at readCompiled
          obtain ⟨⟨binding, index⟩, looked, _⟩ := lower_bind_eq_ok.mp readCompiled
          obtain ⟨sourceLocation, found⟩ := covered name binding index allowed looked
          obtain ⟨targetLocation, entry, _, _⟩ := locals name sourceLocation binding index found looked
          obtain ⟨source, _, sourceRead, _, _⟩ := heap.cell sourceLocation binding.type targetLocation entry
          obtain ⟨target, related, evaluated⟩ := ExpressionCorrespondence.read locals heap found sourceRead originalRead
          refine ⟨[], .inRight .word target, store, ?_, evaluated, by simpa using heap,
            installed, ClosuresPreserved.refl store⟩
          simpa only [Semantics.readResult, found, sourceRead] using ResultRel.value related

/-- The actual Boolean conversion accepts only representations whose source
value has a Boolean observation. -/
theorem condition_valid {lowered : Lowered} {expression : Core.Expr}
    {source : Semantics.Value} {target : Core.Value}
    (compiled : condition lowered = .ok expression) (related : ValueRel lowered.type source target) :
    ∃ truth, Semantics.condition? source = some truth := by
  by_cases native : lowered.type = .bool
  · rw [native] at related
    cases related
    exact ⟨_, rfl⟩
  · by_cases sum : lowered.type = .sum .unit .unit
    · rw [sum] at related
      cases related with
      | inl payload => cases payload; exact ⟨false, rfl⟩
      | inr payload => cases payload; exact ⟨true, rfl⟩
    · simp [condition, native, sum, fail] at compiled

end Solcore.Frontend.RustHull.DerivationCorrespondence
