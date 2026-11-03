import Solcore.Synthesis.Source.IntegerCases

/-! A `runtime-checked-arithmetic` case: an integer plan of one integer type
whose steps are checked and unchecked operations, helpers, lambdas and
defaulted `uint256` literals, at an input that `run(uint256)` or `run(T)`
receives. Its reference panics with `Panic(0x11)` or `Panic(0x12)`, or reverts
with std's `DirtyHigherBitsForInteger()` for a `run(T)` argument std does not
admit. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CheckedArithmetic
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Integers
open Solcore.Synthesis.Source.Integers (Profile CheckedPlan CheckedInput)

def caseSchema : String := "solcore-lean.semantic-checked-arithmetic-case.v1"

def profile : Profile := {
  caseSchema, planSchema := "solcore-lean.checked-arithmetic-plan.v1",
  profileVersion := "runtime-checked-arithmetic-v1/plan-seed-v1",
  emitterVersion := Integers.arithmeticEmitterVersion, wrapperVersion := Integers.arithmeticWrapperVersion,
  planKey := "checkedArithmeticPlan", shapesKey := "checkedArithmeticShapes",
  originKind := "checked-arithmetic-generated", stage := "checked-arithmetic-profile", label := "checked arithmetic",
  admitted := Plan.arithmeticAdmitted, generate := generateArithmetic, emit := Integers.emitArithmetic,
  shapes := Plan.arithmeticShapes }

def maximumNodes : Nat := Integers.maximumNodes

def checkedPlan (json : Json) : Except String (CheckedPlan profile) := profile.checkedPlan json

def caseProgram (json : Json) : Except String (CheckedInput profile) := profile.caseProgram json

def observe (plan : CheckedPlan profile) (input : Word) (fuel : Nat) : Json := Integers.observe plan input fuel

def emitCase (plan : CheckedPlan profile) (input : Word) (origin : Json) (fuel : Nat) : Except String Json :=
  profile.emitCase plan input origin fuel

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) : Json :=
  profile.generateCases firstSeed nodes count attempts fuel inputSelection acceptance

def replayCase (json : Json) (fuel : Nat) : Except String Json := profile.replayCase json fuel

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := profile.shrinkCases json limit fuel

end Solcore.Synthesis.Source.CheckedArithmetic
