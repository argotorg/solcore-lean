import Solcore.Frontend.RustHull.Lowering

/-! Scalar entry preparation from command-line input strings. Parsing preserves
the checked-Hull runner's Word, Bool, Unit and two-Unit Boolean layouts. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ScalarExecution

def parseInput (type : Core.Ty) (input : String) : LowerM Core.Expr :=
  match type with
  | .word => return .word (← parseWord input)
  | .bool => if input = "true" then pure (.bool true)
      else if input = "false" then pure (.bool false)
      else fail "Boolean input must be true or false"
  | .sum .unit .unit => if input = "true" then pure (.inRight .unit .unit)
      else if input = "false" then pure (.inLeft .unit .unit)
      else fail "Boolean input must be true or false"
  | .unit => if input = "unit" then pure .unit else fail "Unit input must be unit"
  | _ => fail "CLI input supports Word, Bool and Unit"

/-- Check arity before parsing any input. Arguments keep their original order;
zero and one arguments use Core's unit and scalar bundle layouts. -/
def parseArguments (parameters : List Core.Ty) (inputs : List String) : LowerM Core.Expr := do
  unless inputs.length = parameters.length do fail "argument count mismatch"
  match parameters, inputs with
  | [], [] => pure .unit
  | [type], [input] => parseInput type input
  | type :: types, input :: inputs => do
      let head ← parseInput type input
      let tail ← parseArguments types inputs
      pure (.pair head tail)
  | _, _ => fail "argument count mismatch"

inductive Error where
  | lowering (error : LoweringError)
  | input (error : LoweringError)
  deriving Repr

structure Prepared where
  compiled : Compiled
  argument : Core.Expr
  deriving Repr

def Prepared.expression (prepared : Prepared) : Core.Expr :=
  .apply prepared.compiled.expression prepared.argument

def Prepared.resultType (prepared : Prepared) : Core.Ty :=
  Core.LanguageResult.resultType prepared.compiled.result

def prepare (program : Program) (entry : String) (inputs : List String)
    (compilationFuel : Nat := 4096) : Except Error Prepared := do
  let compiled ← (compile program entry compilationFuel).mapError Error.lowering
  let argument ← (parseArguments compiled.parameters inputs).mapError Error.input
  pure ⟨compiled, argument⟩

def run (prepared : Prepared) (fuel : Nat := 10000000) : Core.StatefulRunResult :=
  Core.runStateful fuel (.initial prepared.expression)

def resume (checkpoint : Core.State) (fuel : Nat := 10000000) : Core.StatefulRunResult :=
  Core.runStateful fuel checkpoint

end Solcore.Frontend.RustHull.ScalarExecution
