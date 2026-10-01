import Solcore.Core.DefinitionExtension

set_option autoImplicit false
namespace Tests.CoreDefinitionExtension
open Solcore.Core
private def before : DataEnvironment := [⟨[.word]⟩]
private def after : DataEnvironment := before ++ [⟨[.function .word (.namedData ⟨0⟩)]⟩]
private def tag : ConstructorId := ⟨⟨0⟩, 0⟩
private def code : Expr := .lambda .word (.namedData ⟨0⟩) (.construct tag (.var 0))
private def value : Value := .closure .word (.namedData ⟨0⟩) (.construct tag (.var 0)) []

private theorem extended : before.Extends after := .append _ _
private theorem body : HasType [.word] (.construct tag (.var 0)) (.namedData ⟨0⟩) before :=
  .construct rfl (.var rfl)
private theorem closure : RuntimeValueHasType [] value (.function .word (.namedData ⟨0⟩)) before :=
  .closure .nil body

example : after.lookupConstructorPayloadType? tag = some .word := extended.constructor_lookup rfl
example : HasType [] code (.function .word (.namedData ⟨0⟩)) after :=
  (HasType.lambda .word (.namedData rfl) body).extend_definitions extended
example : RuntimeValueHasType [] value (.function .word (.namedData ⟨0⟩)) after :=
  closure.extend_definitions extended
example : RuntimeEnvironmentHasTypes [] [value] [.function .word (.namedData ⟨0⟩)] after :=
  (RuntimeEnvironmentHasTypes.cons closure .nil).extend_definitions extended
example (world : StoreTyping) (store : Store) (typed : RuntimeStoreHasTypes world store before) :
    RuntimeStoreHasTypes world store after := typed.extend_definitions extended

example : (.namedData ⟨1⟩ : Ty).WellFormed after := .namedData rfl
example : ¬ (.namedData ⟨1⟩ : Ty).WellFormed before := by
  intro typed
  cases typed with
  | namedData found => simp [before] at found

example : after.lookupConstructorPayloadType? ⟨⟨1⟩, 0⟩ = some (.function .word (.namedData ⟨0⟩)) := rfl
example : before.lookupConstructorPayloadType? ⟨⟨1⟩, 0⟩ = none := rfl
end Tests.CoreDefinitionExtension
