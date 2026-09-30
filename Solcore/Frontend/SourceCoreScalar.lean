import Solcore.Frontend.SourceCoreBasic

/-! The runtime scalar boundary extends the legacy staged carrier with native
Integer. Legacy elaboration and comptime evaluation retain their own projection.
Input conversion inspects complete product trees and never accepts closures or
references through their outer type alone. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreScalar

open SourceInference

def lowerType (site : SourceCoreElaboration.ErrorSite)
    (type : TypeSystem.Ty) : Except SourceCoreElaboration.Error Core.Ty :=
  match SourceCoreElaboration.lowerType site type with
  | .ok projected => .ok projected
  | .error error => match type with
    | .constructor (.builtin .integer) => .ok .integer
    | .product left right => do pure (.product (← lowerType site left) (← lowerType site right))
    | .comptime inner => lowerType site inner
    | _ => .error error

theorem lowerType_extends {site : SourceCoreElaboration.ErrorSite}
    {type : TypeSystem.Ty} {projected : Core.Ty}
    (legacy : SourceCoreElaboration.lowerType site type = .ok projected) :
    lowerType site type = .ok projected := by
  simp [lowerType, legacy]

def lowerBinder (source : TypedSource) (scope : SourceCoreBasic.Scope)
    (binder : TypedBinder) : Except SourceCoreBasic.Error Core.Ty := do
  if binder.id.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.id.owner)
  unless binder.scheme.quantified.isEmpty do throw (.polymorphicBinding binder.id)
  unless binder.schemeRequirements.isEmpty do throw (.bindingRequirementsPresent binder.id)
  if binder.comptime then throw (.comptimeBinding binder.id)
  if scope.any (fun entry => decide (entry.1 = binder.id)) then throw (.duplicateBinding binder.id)
  (lowerType (.binder binder.id) binder.scheme.body).mapError SourceCoreBasic.Error.typeProjection

inductive Value where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | integer (value : Int)
  | product (left right : Value)
  deriving Repr

def Value.toCore : Value → Core.Value
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .integer value => .integer value
  | .product left right => .pair left.toCore right.toCore

def Value.type : Value → Core.Ty
  | .unit => .unit
  | .bool _ => .bool
  | .word _ => .word
  | .integer _ => .integer
  | .product left right => .product left.type right.type

def Value.ofCore? : Core.Value → Option Value
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .pair left right => do pure (.product (← ofCore? left) (← ofCore? right))
  | _ => none

theorem Value.typed (value : Value) (world : Core.StoreTyping)
    (definitions : Core.DataEnvironment := []) :
    Core.RuntimeValueHasType world value.toCore value.type definitions := by
  induction value with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ left right => exact .pair left right

@[simp] theorem Value.ofCore?_toCore (value : Value) :
    Value.ofCore? value.toCore = some value := by
  induction value <;> simp_all [ofCore?, toCore]

theorem Value.ofCore?_reflect {core : Core.Value} {value : Value}
    (accepted : Value.ofCore? core = some value) : core = value.toCore := by
  cases core with
  | unit | bool | word | integer =>
      simp only [ofCore?, Option.some.injEq] at accepted
      subst value
      rfl
  | pair left right =>
      simp only [ofCore?, bind, Option.bind_eq_some_iff] at accepted
      obtain ⟨leftValue, leftAccepted, rightValue, rightAccepted, equality⟩ := accepted
      cases Option.some.inj equality
      simp only [toCore]
      rw [ofCore?_reflect leftAccepted, ofCore?_reflect rightAccepted]
  | hostFunction | closure | inLeft | inRight | cellRef | constructed =>
      simp only [ofCore?, reduceCtorEq] at accepted
termination_by sizeOf core
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end Solcore.Frontend.SourceCoreScalar
