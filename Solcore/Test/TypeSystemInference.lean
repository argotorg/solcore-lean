import Solcore.TypeSystem.Inference

set_option autoImplicit false

namespace Solcore.Test.TypeSystemInference

open TypeSystem

example : DecidableEq Ty := inferInstance
example : DecidableEq Inference.Error := inferInstance

private def identity : Expr :=
  .lambda "x" (.variable "x")

example : Inference.inferClosed identity =
    .ok (.function (.variable ⟨0⟩) (.variable ⟨0⟩)) := by
  rfl

private def polymorphicIdentityPair : Expr :=
  .letE "id" identity
    (.pair
      (.application (.variable "id") .unit)
      (.application (.variable "id") (.bool true)))

example : Inference.inferClosed polymorphicIdentityPair =
    .ok (.product .unit .bool) := by
  rfl

private def selfApplication : Expr :=
  .lambda "x" (.application (.variable "x") (.variable "x"))

example : Inference.inferClosed selfApplication =
    .error (.unification
      (.occursCheck ⟨0⟩ (.function (.variable ⟨0⟩) (.variable ⟨1⟩)))) := by
  rfl

example : Inference.inferClosed (.variable "missing") =
    .error (.unknownVariable "missing") := by
  rfl

private def variable0 : Ty := .variable ⟨0⟩
private def box (argument : Ty) : Ty :=
  .application (.constructor (.builtin .word)) argument

example : Unification.unifyTypes (box variable0) (box .bool) =
    .ok [(⟨0⟩, .bool)] := by
  rfl

private def rigidOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"rigid", by decide⟩], by decide⟩⟩, 0⟩

example : Unification.unifyTypes
    (.parameter { owner := rigidOwner, index := 0 })
    (.parameter { owner := rigidOwner, index := 1 }) =
    .error (.mismatch
      (.parameter { owner := rigidOwner, index := 0 })
      (.parameter { owner := rigidOwner, index := 1 })) := by
  rfl

private def rigidParameter : TypeParameterId :=
  { owner := rigidOwner, index := 0 }

example :
    let scheme : DeclarationScheme :=
      { parameters := [rigidParameter]
        body := .function (.parameter rigidParameter) (.parameter rigidParameter) }
    scheme.instantiate 20 =
      (.function (.variable ⟨20⟩) (.variable ⟨20⟩), 21) := by
  rfl

example :
    let scheme : Scheme :=
      { quantified := [⟨7⟩], body := .function (.variable ⟨7⟩) (.variable ⟨7⟩) }
    scheme.instantiate 10 =
      (.function (.variable ⟨10⟩) (.variable ⟨10⟩), 11) := by
  rfl

end Solcore.Test.TypeSystemInference
