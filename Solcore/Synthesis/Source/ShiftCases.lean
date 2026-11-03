import Solcore.Synthesis.Source.IntegerCases

/-! A `runtime-shifts` case: an integer plan of one value type, a Word or an
integer type, whose steps shift by amounts of a Word or an unsigned type
converted from the input, or by literal amounts, inside and outside
`unchecked` blocks, at an input that `run(uint256)` receives. Its reference
never reverts. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Shifts
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Integers
open Solcore.Synthesis.Source.Integers (Profile CheckedPlan CheckedInput)

def caseSchema : String := "solcore-lean.semantic-shift-case.v1"

def profile : Profile := {
  caseSchema, planSchema := "solcore-lean.shift-plan.v1", profileVersion := "runtime-shifts-v1/plan-seed-v1",
  emitterVersion := Integers.shiftEmitterVersion, wrapperVersion := Integers.shiftWrapperVersion,
  planKey := "shiftPlan", shapesKey := "shiftShapes", originKind := "shift-generated", stage := "shift-profile",
  label := "shift", admitted := Plan.shiftAdmitted, generate := generateShifts, emit := Integers.emitShifts,
  shapes := Plan.shiftShapes }

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

end Solcore.Synthesis.Source.Shifts
