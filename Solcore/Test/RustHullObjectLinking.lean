import Solcore.Frontend.RustHull.ObjectLinking

set_option autoImplicit false
namespace Tests.RustHullObjectLinking
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def call (name symbol : String) : YulExpr :=
  ⟨.call ⟨name, none⟩ [⟨.literal (.string (Lean.toJson symbol).compress), none⟩], none⟩

private def program (body : List YulStmt) : Program :=
  ⟨[], [], [.object "Deploy" ⟨[⟨.assembly body, none⟩], [], none⟩
    [.object "Runtime" ⟨[], [], none⟩ [] none] none], none⟩

private def image : CodeImage.Image :=
  {path := ["Deploy"], bytes := [1, 2, 3, 4, 5], embeds := [⟨⟨3, 2⟩, "Runtime"⟩]}

private def linked (input : Program) (image : CodeImage.Image := image) : IO Program :=
  match ObjectLinking.link input image with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def bodyOf (input : Program) : List YulStmt :=
  match input.objects with
  | [.object _ ⟨[⟨.assembly body, _⟩], _, _⟩ _ _] => body
  | _ => []

def run : IO Unit := do
  let input := program [⟨.expression (call "datasize" "Deploy"), none⟩,
    ⟨.expression (call "datasize" "Runtime"), none⟩,
    ⟨.expression (call "dataoffset" "Runtime"), none⟩]
  let output ← linked input
  let expected := [5, 2, 3].map fun value =>
    YulStmt.mk (.expression ⟨.literal (.number (toString value)), none⟩) none
  require (bodyOf output == expected) "object symbol extents were not resolved exactly"

  let unknown := program [⟨.expression (call "datasize" "Absent"), none⟩]
  require (ObjectLinking.link unknown image).toOption.isNone "unknown object symbol was accepted"
  let dynamic := program [⟨.expression ⟨.call ⟨"dataoffset", none⟩ [⟨.ident ⟨"x", none⟩, none⟩], none⟩, none⟩]
  require (ObjectLinking.link dynamic image).toOption.isNone "dynamic object symbol was accepted"

  let long := "ThisRuntimeObjectNameExceedsThirtyTwoBytes"
  let longImage := {image with embeds := [⟨⟨3, 2⟩, long⟩]}
  let longInput := program [⟨.expression (call "dataoffset" long), none⟩]
  require (bodyOf (← linked longInput longImage) ==
    [⟨.expression ⟨.literal (.number "3"), none⟩, none⟩])
    "object symbol was treated as a word-sized string literal"

  let shadow : YulStmt := ⟨.functionDef ⟨"datasize", none⟩ [] [⟨"r", none⟩] [], none⟩
  let shadowed := program [⟨.expression (call "datasize" "Absent"), none⟩, shadow]
  require ((← linked shadowed) == shadowed) "hoisted Yul function did not shadow intrinsic name"
  let innerShadow := program [⟨.block [shadow], none⟩, ⟨.expression (call "datasize" "Runtime"), none⟩]
  require (bodyOf (← linked innerShadow) ==
    [⟨.block [shadow], none⟩, ⟨.expression ⟨.literal (.number "2"), none⟩, none⟩])
    "block-local intrinsic shadow escaped its scope"

  let nested : Program := {input with objects := [.object "Deploy" ⟨[], [], none⟩
    [.object "Runtime" ⟨[⟨.assembly [⟨.expression (call "datasize" "Deploy"), none⟩], none⟩], [], none⟩ [] none] none]}
  require ((← linked nested) == nested) "parent image rewrote a child's symbol namespace"

end Tests.RustHullObjectLinking
