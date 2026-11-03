import Solcore.Synthesis.Source.ArrayCases

/-! A `runtime-array-abi` case: an array plan of one integer element type with
one or two `T[]` or `calldata<T[]>` parameters made from the input Word,
whose steps read, write, slice and copy them and memory arrays and grids,
returning the fold or a `T[]`. Its reference panics as the memory-array
reference does, or reverts with std's `DirtyHigherBitsForInteger()` for a
narrow element std's decoder does not admit. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ArrayAbi
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Arrays
open Solcore.Synthesis.Source.Arrays (Profile CheckedPlan CheckedInput)

def caseSchema : String := "solcore-lean.semantic-array-abi-case.v1"

def profile : Profile := {
  caseSchema, planSchema := "solcore-lean.array-abi-plan.v1",
  profileVersion := "runtime-array-abi-v1/plan-seed-v1",
  emitterVersion := Arrays.abiEmitterVersion, wrapperVersion := Arrays.abiWrapperVersion,
  planKey := "arrayAbiPlan", shapesKey := "arrayAbiShapes",
  originKind := "array-abi-generated", stage := "array-abi-profile", label := "array ABI",
  admitted := Plan.abiAdmitted, generate := generateAbi, emit := Arrays.emitAbi,
  shapes := Plan.abiShapes, minimumNodes := 512 }

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

end Solcore.Synthesis.Source.ArrayAbi
