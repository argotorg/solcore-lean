import Solcore.Synthesis.Source.ArrayCases

/-! A `runtime-memory-arrays` case: an array plan of one integer element type
whose steps make, alias, copy, slice and write memory arrays, grids and the
storage array and fold what they observe, at an input that `run(uint256)`
receives. Its reference panics with `Panic(0x11)`, `Panic(0x12)`,
`Panic(0x31)`, `Panic(0x32)` or `Panic(0x41)`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MemoryArrays
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Arrays
open Solcore.Synthesis.Source.Arrays (Profile CheckedPlan CheckedInput)

def caseSchema : String := "solcore-lean.semantic-memory-array-case.v1"

def profile : Profile := {
  caseSchema, planSchema := "solcore-lean.memory-array-plan.v1",
  profileVersion := "runtime-memory-arrays-v1/plan-seed-v1",
  emitterVersion := Arrays.memoryEmitterVersion, wrapperVersion := Arrays.memoryWrapperVersion,
  planKey := "memoryArrayPlan", shapesKey := "memoryArrayShapes",
  originKind := "memory-array-generated", stage := "memory-array-profile", label := "memory array",
  admitted := Plan.memoryAdmitted, generate := generateMemory, emit := Arrays.emitMemory,
  shapes := Plan.memoryShapes, minimumNodes := 256 }

def maximumNodes : Nat := Arrays.maximumNodes

def checkedPlan (json : Json) : Except String (CheckedPlan profile) := profile.checkedPlan json

def caseProgram (json : Json) : Except String (CheckedInput profile) := profile.caseProgram json

def observe (plan : CheckedPlan profile) (input : Word) (fuel : Nat) : Json := Arrays.observe plan input fuel

def emitCase (plan : CheckedPlan profile) (input : Word) (origin : Json) (fuel : Nat) : Except String Json :=
  profile.emitCase plan input origin fuel

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) : Json :=
  profile.generateCases firstSeed nodes count attempts fuel inputSelection acceptance

def replayCase (json : Json) (fuel : Nat) : Except String Json := profile.replayCase json fuel

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := profile.shrinkCases json limit fuel

end Solcore.Synthesis.Source.MemoryArrays
