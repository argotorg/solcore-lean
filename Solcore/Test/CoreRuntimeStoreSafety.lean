import Solcore.Core.RuntimeStoreSafety

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
