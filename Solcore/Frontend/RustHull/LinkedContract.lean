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
  let catalog ← images.filterMapM fun candidate => do
    let isInit := !candidate.embeds.isEmpty
    -- Preserve an unsuffixed init template even when it is the selected root.
    if candidate.path == path && !isInit then pure none
    else
      -- An unrelated section may use symbols absent from its own image. Its
      -- bytes remain observable, but it has no executable catalog identity.
      match ObjectLinking.link program candidate fuel with
      | .error _ => pure none
      | .ok linked => pure (some ({
          program := linked
          path := candidate.path
          bytes := candidate.bytes
          isInit := isInit
        } : AccountRuntime.CodeDefinition))
  Contract.compileObject linked path fuel (some bytes) catalog

def prepare (program : Program) (path : List String) (images : List CodeImage.Image)
    (constructorArguments : List UInt8 := []) (context : Contract.Context := {})
    (fuel : Nat := 4096) : LowerM Contract.Prepared := do
  return (← compileObject program path images constructorArguments fuel).instantiate context

/-- Prepare init code with constructor arguments in the code suffix and empty
calldata. Calls to the constructing address see no installed runtime code.
The caller still supplies the balance after its transaction value transfer. -/
def prepareDeployment (program : Program) (path : List String) (images : List CodeImage.Image)
    (constructorArguments : List UInt8 := []) (context : Contract.Context := {})
    (fuel : Nat := 4096) : LowerM Contract.Prepared := do
  let image ← (CodeImage.select images path).mapError fun message => ⟨message, none⟩
  if image.bytes.length + constructorArguments.length > 49152 then
    throw ⟨"deployment init code including constructor arguments exceeds 49152 bytes", none⟩
  prepare program path images constructorArguments
    {context with calldata := [], selfCodeAvailable := false, deploying := true, created := true} fuel

end Solcore.Frontend.RustHull.LinkedContract
