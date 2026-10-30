import Solcore.Synthesis.Source.ConstructorArgumentsCases

/-! Native constructor-argument case boundary. Source generation and replay never execute the
imported Hull or use stored expected results. The observer requires explicit
bindings for the actual deployed target and caller. -/
set_option autoImplicit false
open Lean Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def natural (label value : String) (maximum : Nat) : IO Nat := do
  unless value.length ≤ 20 do throw (IO.userError s!"invalid {label}")
  let some result := value.toNat? | throw (IO.userError s!"invalid {label}")
  unless toString result = value && result ≤ maximum do
    throw (IO.userError s!"{label} must be canonical and at most {maximum}")
  return result

private def readJson (file : String) : IO Json := do
  let metadata ← (System.FilePath.mk file).metadata
  unless metadata.byteSize.toNat ≤ 2097152 do throw (IO.userError "input exceeds 2 MiB")
  let contents ← IO.FS.readFile file
  unless contents.utf8ByteSize ≤ 2097152 do throw (IO.userError "input exceeds 2 MiB")
  get (Json.parse contents)

private def fuelValue (rest : List String) : IO Nat :=
  match rest with
  | [] => pure 1000000
  | [fuel] => natural "execution fuel" fuel 10000000
  | _ => throw (IO.userError "too many arguments")

/-- A trailing G0 generator version selects the step generator's revision, and
a further count the generated transactions; without them, generation keeps `v1`
and three transactions, which the fixed corpora pin. -/
private def generation : List String → IO (Solcore.Synthesis.Core.GeneratorRevision × Nat)
  | [] => pure (.v1, 3)
  | version :: rest => do
      let some revision := Solcore.Synthesis.Core.GeneratorRevision.ofVersion? version
        | throw (IO.userError "unknown G0 generator version")
      match rest with
      | [] => pure (revision, 3)
      | [transactions] =>
          let count ← natural "transaction count" transactions Solcore.Synthesis.Stateful.Sequence.maxTransactions
          unless count > 0 do throw (IO.userError "transaction count must be positive")
          pure (revision, count)
      | _ => throw (IO.userError "too many arguments")

private def execute (args : List String) : IO Json := do
  match args with
  | "generate" :: seed :: nodes :: count :: attempts :: fuel :: options =>
      let count ← natural "scenario count" count 1024
      unless count > 0 do throw (IO.userError "scenario count must be positive")
      let (revision, transactions) ← generation options
      return ConstructorArguments.generateCases (Solcore.Synthesis.Core.Seed.ofNat
        (← natural "seed" seed (2 ^ 64 - 1)))
        (← natural "node budget" nodes 512) count
        (← natural "attempt limit" attempts 10000)
        (← natural "execution fuel" fuel 10000000) revision transactions
  | "emit" :: file :: deployment :: transactions :: rest =>
      let plan ← get (ConstructorArguments.checkedPlan (← readJson file))
      let deployment ← get (ConstructorArguments.decodeDeployment plan.parameters (← readJson deployment))
      let transactions ← get (ConstructorArguments.decodeTransactions (← readJson transactions))
      let scenario ← get (ConstructorArguments.checkedScenario plan deployment transactions)
      get (ConstructorArguments.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) (← fuelValue rest))
  | "replay" :: file :: rest =>
      get (ConstructorArguments.replayCase (← readJson file) (← fuelValue rest))
  | "observe" :: file :: bindings :: rest =>
      let fuel ← fuelValue rest
      let refreshed ← get (ConstructorArguments.replayCase (← readJson file) fuel)
      let scenario ← get (ConstructorArguments.caseProgram refreshed)
      let bindings ← get (Solcore.Synthesis.Stateful.StorageExecution.decodeBindings (← readJson bindings))
      return ConstructorArguments.observe scenario bindings fuel
  | "shrink" :: file :: limit :: rest =>
      get (ConstructorArguments.shrinkCases (← readJson file) (← natural "shrink limit" limit 4096) (← fuelValue rest))
  | _ => throw (IO.userError "usage: semantic-constructor-argument-tool generate SEED NODES COUNT ATTEMPTS FUEL [G0-GENERATOR-VERSION [TRANSACTIONS]] | emit PLAN.json DEPLOYMENT.json TRANSACTIONS.json [FUEL] | replay CASE.json [FUEL] | observe CASE.json BINDINGS.json [FUEL] | shrink CASE.json LIMIT [FUEL]")

def main (args : List String) : IO UInt32 := do
  try
    IO.println (← execute args).compress
    return 0
  catch error =>
    IO.println (Json.mkObj [("stage", toJson "constructor-argument-case-tool"),
      ("status", toJson "rejected"), ("detail", toJson error.toString)]).compress
    return 2
