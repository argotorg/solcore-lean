import Solcore.Synthesis.Source.FunctionCases
import Solcore.Synthesis.Source.MutationCases
import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.LoopCases
import Solcore.Synthesis.Source.GenericCases
import Solcore.Synthesis.Source.ClosureCases

/-! Bounded command-line case generation, observation, replay and reduction. -/
set_option autoImplicit false
open Lean Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def natural (label value : String) (maximum : Nat) : IO Nat := do
  let some result := value.toNat? | throw (IO.userError s!"invalid {label}")
  unless toString result = value && result ≤ maximum do
    throw (IO.userError s!"{label} must be canonical and at most {maximum}")
  return result

private def readJson (file : String) : IO Json := do
  let metadata ← (System.FilePath.mk file).metadata
  unless metadata.byteSize.toNat ≤ 2097152 do
    throw (IO.userError "input exceeds 2 MiB")
  let contents ← IO.FS.readFile file
  unless contents.utf8ByteSize ≤ 2097152 do throw (IO.userError "input exceeds 2 MiB")
  get (Json.parse contents)

private def fuelValue (rest : List String) : IO Nat := do
  match rest with
  | [] => pure 1000000
  | [fuel] => natural "execution fuel" fuel 10000000
  | _ => throw (IO.userError "too many arguments")

private def execute (args : List String) : IO Json := do
  match args with
  | ["closure-generate", seed, nodes, count, attempts, fuel] =>
      let count ← natural "case count" count 1024
      unless count > 0 do throw (IO.userError "case count must be positive")
      return Closure.generateCases (Solcore.Synthesis.Core.Seed.ofNat
        (← natural "seed" seed (2 ^ 64 - 1)))
        (← natural "node budget" nodes 512)
        count
        (← natural "attempt limit" attempts 10000)
        (← natural "execution fuel" fuel 10000000)
  | ["generic-generate", seed, nodes, count, attempts, fuel] =>
      let count ← natural "case count" count 1024
      unless count > 0 do throw (IO.userError "case count must be positive")
      return Generic.generateCases (Solcore.Synthesis.Core.Seed.ofNat
        (← natural "seed" seed (2 ^ 64 - 1)))
        (← natural "node budget" nodes 512)
        count
        (← natural "attempt limit" attempts 10000)
        (← natural "execution fuel" fuel 10000000)
  | ["loop-generate", seed, nodes, count, attempts, fuel] =>
      let count ← natural "case count" count 1024
      unless count > 0 do throw (IO.userError "case count must be positive")
      return Loop.generateCases (Solcore.Synthesis.Core.Seed.ofNat
        (← natural "seed" seed (2 ^ 64 - 1)))
        (← natural "node budget" nodes 512)
        count
        (← natural "attempt limit" attempts 10000)
        (← natural "execution fuel" fuel 10000000)
  | ["aggregate-generate", seed, nodes, count, attempts, fuel] =>
      let count ← natural "case count" count 1024
      unless count > 0 do throw (IO.userError "case count must be positive")
      return Aggregate.generateCases (Solcore.Synthesis.Core.Seed.ofNat
        (← natural "seed" seed (2 ^ 64 - 1)))
        (← natural "node budget" nodes 512)
        count
        (← natural "attempt limit" attempts 10000)
        (← natural "execution fuel" fuel 10000000)
  | ["mutation-generate", seed, nodes, count, attempts, fuel] =>
      let count ← natural "case count" count 1024
      unless count > 0 do throw (IO.userError "case count must be positive")
      return Mutation.generateCases (Solcore.Synthesis.Core.Seed.ofNat
        (← natural "seed" seed (2 ^ 64 - 1)))
        (← natural "node budget" nodes 512)
        count
        (← natural "attempt limit" attempts 10000)
        (← natural "execution fuel" fuel 10000000)
  | ["function-generate", seed, nodes, count, attempts, fuel] =>
      let count ← natural "case count" count 1024
      unless count > 0 do throw (IO.userError "case count must be positive")
      return Function.generateCases (Solcore.Synthesis.Core.Seed.ofNat
        (← natural "seed" seed (2 ^ 64 - 1)))
        (← natural "node budget" nodes 512)
        count
        (← natural "attempt limit" attempts 10000)
        (← natural "execution fuel" fuel 10000000)
  | ["input-generate", seed, nodes, count, attempts, fuel] =>
      let count ← natural "case count" count 1024
      unless count > 0 do throw (IO.userError "case count must be positive")
      return Input.generateCases (Solcore.Synthesis.Core.Seed.ofNat
        (← natural "seed" seed (2 ^ 64 - 1)))
        (← natural "node budget" nodes 512)
        count
        (← natural "attempt limit" attempts 10000)
        (← natural "execution fuel" fuel 10000000)
  | ["generate", seed, nodes, count, attempts, fuel] =>
      let count ← natural "case count" count 1024
      unless count > 0 do throw (IO.userError "case count must be positive")
      return generateCases (Solcore.Synthesis.Core.Seed.ofNat
        (← natural "seed" seed (2 ^ 64 - 1)))
        (← natural "node budget" nodes 512)
        count
        (← natural "attempt limit" attempts 10000)
        (← natural "execution fuel" fuel 10000000)
  | "emit" :: file :: rest =>
      let checked ← get (checkedProgram (← readJson file))
      get ((emitCase checked (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest)).mapError reprStr)
  | "input-emit" :: file :: input :: rest =>
      let function ← get (Input.checkedFunction (← readJson file))
      let input ← get (Input.inputWord input)
      get (Input.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "function-emit" :: file :: input :: rest =>
      let function ← get (Function.checkedFunction (← readJson file))
      let input ← get (Input.inputWord input)
      get (Function.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "closure-emit" :: file :: input :: rest =>
      let function ← get (Closure.checkedPlan (← readJson file))
      let input ← get (Input.inputWord input)
      get (Closure.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "generic-emit" :: file :: input :: rest =>
      let function ← get (Generic.checkedPlan (← readJson file))
      let input ← get (Input.inputWord input)
      get (Generic.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "loop-emit" :: file :: input :: rest =>
      let function ← get (Loop.checkedPlan (← readJson file))
      let input ← get (Input.inputWord input)
      get (Loop.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "aggregate-emit" :: file :: input :: rest =>
      let function ← get (Aggregate.checkedFunction (← readJson file))
      let input ← get (Input.inputWord input)
      get (Aggregate.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "mutation-emit" :: file :: input :: rest =>
      let function ← get (Mutation.checkedFunction (← readJson file))
      let input ← get (Input.inputWord input)
      get (Mutation.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "observe" :: file :: rest =>
      let json ← readJson file
      let fuel ← fuelValue rest
      if (json.getObjValAs? String "schema").toOption == some Closure.caseSchema then
        let checked ← get (Closure.caseProgram json)
        return Closure.observe checked.plan checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some Generic.caseSchema then
        let checked ← get (Generic.caseProgram json)
        return Generic.observe checked.plan checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some Loop.caseSchema then
        let checked ← get (Loop.caseProgram json)
        return Loop.observe checked.plan checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some Aggregate.caseSchema then
        let checked ← get (Aggregate.caseProgram json)
        return Aggregate.observe checked.function checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some Mutation.caseSchema then
        let checked ← get (Mutation.caseProgram json)
        return Mutation.observe checked.function checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some Function.caseSchema then
        let checked ← get (Function.caseProgram json)
        return Function.observe checked.function checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some Input.caseSchema then
        let checked ← get (Input.caseProgram json)
        return Input.observe checked.function checked.input fuel
      else
        let checked ← get (caseProgram json)
        return observe checked fuel
  | "replay" :: file :: rest =>
      let json ← readJson file
      let fuel ← fuelValue rest
      get (if (json.getObjValAs? String "schema").toOption == some Closure.caseSchema then
        Closure.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Generic.caseSchema then
        Generic.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Loop.caseSchema then
        Loop.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Aggregate.caseSchema then
        Aggregate.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Mutation.caseSchema then
        Mutation.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Function.caseSchema then
        Function.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Input.caseSchema then
          Input.replayCase json fuel else replayCase json fuel)
  | "shrink" :: file :: limit :: rest =>
      let json ← readJson file
      let limit ← natural "shrink limit" limit 4096
      let fuel ← fuelValue rest
      get (if (json.getObjValAs? String "schema").toOption == some Closure.caseSchema then
        Closure.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Generic.caseSchema then
        Generic.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Loop.caseSchema then
        Loop.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Aggregate.caseSchema then
        Aggregate.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Mutation.caseSchema then
        Mutation.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Function.caseSchema then
        Function.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Input.caseSchema then
          Input.shrinkCases json limit fuel else shrinkCases json limit fuel)
  | _ => throw (IO.userError "usage: semantic-case-tool generate|input-generate|function-generate|mutation-generate|aggregate-generate|loop-generate|generic-generate|closure-generate SEED NODES COUNT ATTEMPTS FUEL | emit PROGRAM.json [FUEL] | input-emit|function-emit|mutation-emit|aggregate-emit FUNCTION.json INPUT [FUEL] | loop-emit|generic-emit|closure-emit PLAN.json INPUT [FUEL] | observe CASE.json [FUEL] | replay CASE.json [FUEL] | shrink CASE.json LIMIT [FUEL]")

def main (args : List String) : IO UInt32 := do
  try
    let result ← execute args
    IO.println result.compress
    return 0
  catch error =>
    IO.println (Json.mkObj [("stage", toJson "case-tool"),
      ("status", toJson "rejected"), ("detail", toJson error.toString)]).compress
    return 2
