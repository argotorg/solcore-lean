import Solcore.Frontend.RustHull.ExpressionCorrespondence
import Solcore.Frontend.RustHull.StatementCorrespondence

/-! Independent source derivations instantiate the expression premise used by
the actual statement compiler. Literal and local-read cases require no assumed
correspondence for a function body or for an external operation. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.PureExpressionCorrespondence

open Correspondence StatementCorrespondence

theorem word {σ : Type} (functions : List Function) (effects : Semantics.ExternalSemantics σ)
    (signatures : List Signature) (external : σ → Core.Store → Prop)
    (type : Ty) (text : String) (span : Option Span) :
    NormalExprPreserves functions effects signatures external ⟨type, .word text, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  have same : final = initial ∧ Semantics.Result.value sourceValue = Semantics.literalResult text := by
    generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
    cases evaluated <;> simp_all
  rcases same with ⟨rfl, sourceResult⟩
  intro fuel scope lowered compiled world mapping environment store _ heap externalRelated
  obtain ⟨target, related, evaluated⟩ := ExpressionCorrespondence.word rfl compiled mapping environment store
  rw [← sourceResult] at related
  cases related with
  | value payload => exact ⟨[], _, store, payload, evaluated, by simpa using heap, externalRelated⟩

theorem bool {σ : Type} (functions : List Function) (effects : Semantics.ExternalSemantics σ)
    (signatures : List Signature) (external : σ → Core.Store → Prop)
    (type : Ty) (value : Bool) (span : Option Span) :
    NormalExprPreserves functions effects signatures external ⟨type, .bool value, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  have same : final = initial ∧ Semantics.Result.value sourceValue = Semantics.booleanResult type value := by
    generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
    cases evaluated <;> simp_all
  rcases same with ⟨rfl, sourceResult⟩
  intro fuel scope lowered compiled world mapping environment store _ heap externalRelated
  obtain ⟨target, related, evaluated⟩ := ExpressionCorrespondence.bool rfl compiled mapping environment store
  rw [← sourceResult] at related
  cases related with
  | value payload => exact ⟨[], _, store, payload, evaluated, by simpa using heap, externalRelated⟩

theorem unit {σ : Type} (functions : List Function) (effects : Semantics.ExternalSemantics σ)
    (signatures : List Signature) (external : σ → Core.Store → Prop)
    (type : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external ⟨type, .unit, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  have same : final = initial ∧ sourceValue = .unit := by
    generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
    cases evaluated <;> simp_all
  rcases same with ⟨rfl, rfl⟩
  intro fuel scope lowered compiled world mapping environment store _ heap externalRelated
  obtain ⟨related, evaluated⟩ := ExpressionCorrespondence.unit rfl compiled mapping environment store
  cases related with
  | value payload => exact ⟨[], _, store, payload, evaluated, by simpa using heap, externalRelated⟩

end Solcore.Frontend.RustHull.PureExpressionCorrespondence
