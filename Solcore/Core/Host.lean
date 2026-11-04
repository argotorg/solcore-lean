import Solcore.Core.Typing

/-!
# Host capabilities

`hostContext` and `hostEnvironment` bind every `HostFunction` at a fixed position.
`Program.HostWellTyped` and `Program.checkHost` check a program against them.
-/

/-! Fixed runtime capabilities and checking for Core programs that use them. -/

set_option autoImplicit false

namespace Solcore.Core

/-- Append-only types supplied to a host-aware Core program. -/
def hostContext : Context :=
  HostFunction.all.map HostFunction.functionType

/-- Runtime values corresponding positionally to `hostContext`. -/
def hostEnvironment : Environment :=
  HostFunction.all.map fun function => .hostFunction function

namespace Program

/-- Declarative validity under the exact runtime capability context. -/
structure HostWellTyped (program : Program) : Prop where
  dataDefinitionsWellFormed : program.dataDefinitions.WellFormed
  resultTypeWellFormed : Ty.WellFormed program.dataDefinitions program.resultType
  bodyHasType :
    HasType hostContext program.body program.resultType program.dataDefinitions

/-- Check a Core program under the fixed host capability context. -/
def checkHost (program : Program) : Bool :=
  if program.dataDefinitions.isWellFormed then
    if program.resultType.isWellFormed program.dataDefinitions then
      match infer? hostContext program.body program.dataDefinitions with
      | some inferredType => decide (inferredType = program.resultType)
      | none => false
    else
      false
  else
    false

end Program

end Solcore.Core
