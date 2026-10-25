import Solcore.Synthesis.Source.InputCases

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
  | "observe" :: file :: rest =>
      let json ← readJson file
      let fuel ← fuelValue rest
      if (json.getObjValAs? String "schema").toOption == some Input.caseSchema then
        let checked ← get (Input.caseProgram json)
        return Input.observe checked.function checked.input fuel
      else
        let checked ← get (caseProgram json)
        return observe checked fuel
  | "replay" :: file :: rest =>
      let json ← readJson file
      let fuel ← fuelValue rest
      get (if (json.getObjValAs? String "schema").toOption == some Input.caseSchema then
        Input.replayCase json fuel else replayCase json fuel)
  | "shrink" :: file :: limit :: rest =>
      let json ← readJson file
      let limit ← natural "shrink limit" limit 4096
      let fuel ← fuelValue rest
      get (if (json.getObjValAs? String "schema").toOption == some Input.caseSchema then
        Input.shrinkCases json limit fuel else shrinkCases json limit fuel)
  | _ => throw (IO.userError "usage: semantic-case-tool generate|input-generate SEED NODES COUNT ATTEMPTS FUEL | emit PROGRAM.json [FUEL] | input-emit FUNCTION.json INPUT [FUEL] | observe CASE.json [FUEL] | replay CASE.json [FUEL] | shrink CASE.json LIMIT [FUEL]")

def main (args : List String) : IO UInt32 := do
  try
    let result ← execute args
    IO.println result.compress
    return 0
  catch error =>
    IO.println (Json.mkObj [("stage", toJson "case-tool"),
      ("status", toJson "rejected"), ("detail", toJson error.toString)]).compress
    return 2
