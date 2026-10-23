import Solcore.Frontend.RustHull.Contract
import Solcore.Frontend.RustHull.ObjectLinking

/-! Prepare runtime and constructor objects with exact linked backend bytes.
Constructor arguments are appended to init code, while calldata is supplied
separately through the ordinary contract context. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.LinkedContract

def compileObject (program : Program) (path : List String) (images : List CodeImage.Image)
    (constructorArguments : List UInt8 := []) (fuel : Nat := 4096) : LowerM Contract.CompiledObject := do
  let lift {α : Type} (result : Except String α) : LowerM α :=
    result.mapError fun message => ⟨message, none⟩
  lift (CodeImage.validate program.objects images)
  let image ← lift (CodeImage.select images path)
  let bytes ← lift (CodeImage.executionBytes image constructorArguments)
  let linked ← ObjectLinking.link program image fuel
  Contract.compileObject linked path fuel (some bytes)

def prepare (program : Program) (path : List String) (images : List CodeImage.Image)
    (constructorArguments : List UInt8 := []) (context : Contract.Context := {})
    (fuel : Nat := 4096) : LowerM Contract.Prepared := do
  return (← compileObject program path images constructorArguments fuel).instantiate context

end Solcore.Frontend.RustHull.LinkedContract
