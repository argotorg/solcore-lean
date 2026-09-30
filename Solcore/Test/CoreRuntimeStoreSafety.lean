import Solcore.Core.RuntimeStoreSafety
import Solcore.Core.BoundedSafety

/-! Higher-order store invariants do not traverse cyclic captured references. -/

set_option autoImplicit false

namespace Tests.CoreRuntimeStoreSafety

open Solcore.Core

private def functionType : Ty := .function .unit .unit

private def selfClosure : Value :=
  .closure .unit .unit (.var 0) [.cellRef functionType 0]

private theorem selfClosure_typed :
    RuntimeValueHasType [functionType] selfClosure functionType :=
  .closure (.cons (.cellRef rfl) .nil) (.var rfl)

/-- The closure captures its own location. Typing remains a finite proof. -/
private theorem cyclicStore_typed :
    RuntimeStoreHasTypes [functionType] [selfClosure] where
  length_eq := rfl
  lookup := by
    intro location type found
    cases location with
    | zero =>
        have equal : functionType = type := Option.some.inj found
        subst type
        exact ⟨selfClosure, rfl, selfClosure_typed⟩
    | succ location => simp at found

private def callState : State :=
  .initial (.apply (.var 0) .unit) [selfClosure] [selfClosure]

/-- The pure machine now uses the general world-indexed store invariant. -/
private theorem callState_typed : StateHasType callState .unit :=
  .eval cyclicStore_typed (.cons selfClosure_typed .nil)
    (.apply (.var rfl) .unit) .nil

example (fuel : Nat) (fault : MachineFault) (state : State) :
    runStateful fuel callState ≠ .fault fault state :=
  well_typed_runStateful_never_faults callState_typed

example : runStateful 6 callState = .done .unit [selfClosure] := by
  rfl

private def allocationState : State :=
  .initial (.newCell .bool (.bool true)) [] [selfClosure]

private theorem allocationState_typed : StateHasType allocationState (.cell .bool) :=
  .eval cyclicStore_typed .nil (.newCell .bool) .nil

example : runStateful 3 allocationState =
    .done (.cellRef .bool 1) [selfClosure, .bool true] := by
  rfl

example (fuel : Nat) (checkpoint : State)
    (exhausted : runStateful fuel allocationState = .outOfFuel checkpoint) :
    ∃ future, WorldExtends [functionType] future ∧
      RuntimeStoreHasTypes future checkpoint.store :=
  well_typed_runStateful_preserves_checkpoint_world
    allocationState_typed cyclicStore_typed exhausted

example :
    ∃ value, Store.read? [selfClosure] 0 = some value ∧
      RuntimeValueHasType [functionType] value functionType :=
  cyclicStore_typed.read rfl

/-- Allocation weakens every captured reference to the extended world. -/
example : RuntimeStoreHasTypes [functionType, .bool] [selfClosure, .bool true] :=
  cyclicStore_typed.allocate (.bool : RuntimeValueHasType _ (.bool true) .bool)

/-- Writing a closure with a captured location preserves the store invariant. -/
example : RuntimeStoreHasTypes [functionType] [selfClosure] :=
  cyclicStore_typed.write (location := 0) rfl selfClosure_typed rfl

/-- An annotation without a matching world entry is insufficient. -/
example : ¬ RuntimeValueHasType [functionType]
    (.cellRef functionType 1) (.cell functionType) := by
  intro typing
  cases typing with
  | cellRef found => simp at found

example : ¬ RuntimeStoreHasTypes [functionType] [] := by
  intro typing
  have equal := typing.length_eq
  cases equal

/-- Higher-order constructor payloads retain their nominal environment. -/
private def dataDefinitions : DataEnvironment :=
  [{ constructorPayloadTypes := [functionType] }]

private def constructedClosure : Value :=
  .constructed ⟨⟨0⟩, 0⟩ (.closure .unit .unit (.var 0) [])

example : RuntimeStoreHasTypes [.namedData ⟨0⟩] [constructedClosure]
    dataDefinitions := by
  have valueTyping : RuntimeValueHasType [] constructedClosure
      (.namedData ⟨0⟩) dataDefinitions :=
    .constructed rfl (.closure .nil (.var rfl))
  exact (RuntimeStoreHasTypes.nil dataDefinitions).allocate valueTyping

end Tests.CoreRuntimeStoreSafety
