import Solcore.Synthesis.Source.FunctionCases
import Solcore.Synthesis.Source.MutationCases
import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.LoopCases
import Solcore.Synthesis.Source.NestedLoopCases
import Solcore.Synthesis.Source.GenericCases
import Solcore.Synthesis.Source.ClosureCases
import Solcore.Synthesis.Source.ComptimeCases
import Solcore.Synthesis.Source.ModuleCases
import Solcore.Synthesis.Source.PrimitiveCases
import Solcore.Synthesis.Source.CallGraphCases
import Solcore.Synthesis.Source.CallGraphLoopCases
import Solcore.Synthesis.Source.AggregateCallGraphCases

/-! Bounded command-line case generation, observation, replay and reduction. -/
set_option autoImplicit false
open Lean Solcore.Synthesis.Source
open Solcore.Synthesis.Core (Seed GeneratorRevision)

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

/-- A generation command and the options it accepts after its five arguments. -/
private structure Generator where
  g0 : Bool
  runtimeInput : Bool
  /-- Whether its generated functions can be identities on the boundary inputs. -/
  identityFilter : Bool
  run : Seed → Nat → Nat → Nat → Nat → GeneratorRevision → InputSelection → Acceptance → Json

private def generator (command : String) : Option Generator :=
  match command with
  | "generate" => some ⟨true, false, false,
      fun seed nodes count attempts fuel revision _ _ =>
        generateCases seed nodes count attempts fuel revision⟩
  | "input-generate" => some ⟨true, true, true,
      fun seed nodes count attempts fuel revision inputs acceptance =>
        Input.generateCases seed nodes count attempts fuel revision inputs acceptance⟩
  | "primitive-generate" => some ⟨true, true, true,
      fun seed nodes count attempts fuel revision inputs acceptance =>
        Primitive.generateCases seed nodes count attempts fuel revision inputs acceptance⟩
  | "call-graph-generate" => some ⟨false, true, true,
      fun seed nodes count attempts fuel _ inputs acceptance =>
        CallGraph.generateCases seed nodes count attempts fuel inputs acceptance⟩
  | "call-graph-loop-generate" => some ⟨false, true, false,
      fun seed nodes count attempts fuel _ inputs _ =>
        CallGraphLoop.generateCases seed nodes count attempts fuel inputs⟩
  | "aggregate-call-graph-generate" => some ⟨false, true, true,
      fun seed nodes count attempts fuel _ inputs acceptance =>
        AggregateCallGraph.generateCases seed nodes count attempts fuel inputs acceptance⟩
  | "function-generate" => some ⟨true, true, true,
      fun seed nodes count attempts fuel revision inputs acceptance =>
        Function.generateCases seed nodes count attempts fuel revision inputs acceptance⟩
  | "mutation-generate" => some ⟨true, true, true,
      fun seed nodes count attempts fuel revision inputs acceptance =>
        Mutation.generateCases seed nodes count attempts fuel revision inputs acceptance⟩
  | "aggregate-generate" => some ⟨true, true, true,
      fun seed nodes count attempts fuel revision inputs acceptance =>
        Aggregate.generateCases seed nodes count attempts fuel revision inputs acceptance⟩
  | "loop-generate" => some ⟨true, true, false,
      fun seed nodes count attempts fuel revision inputs _ =>
        Loop.generateCases seed nodes count attempts fuel revision inputs⟩
  | "nested-loop-generate" => some ⟨true, true, false,
      fun seed nodes count attempts fuel revision inputs _ =>
        NestedLoop.generateCases seed nodes count attempts fuel revision inputs⟩
  | "generic-generate" => some ⟨true, true, false,
      fun seed nodes count attempts fuel revision inputs _ =>
        Generic.generateCases seed nodes count attempts fuel revision inputs⟩
  | "closure-generate" => some ⟨true, true, true,
      fun seed nodes count attempts fuel revision inputs acceptance =>
        Closure.generateCases seed nodes count attempts fuel revision inputs acceptance⟩
  | "comptime-generate" => some ⟨true, true, true,
      fun seed nodes count attempts fuel revision inputs acceptance =>
        Comptime.generateCases seed nodes count attempts fuel revision inputs acceptance⟩
  | "module-generate" => some ⟨true, true, true,
      fun seed nodes count attempts fuel revision inputs acceptance =>
        Modules.generateCases seed nodes count attempts fuel revision inputs acceptance⟩
  | _ => none

/-- Each option appears at most once. A G0 generator version selects the G0
revision of a G0-based command, `v1` by default; the seeded input selection
applies to runtime-input commands, `boundary` by default; the identity filter
applies to runtime-input commands whose functions can be identities, the
profile's own filters by default. Fixed corpora use all three defaults. -/
private def generationOptions (spec : Generator) (options : List String) :
    IO (GeneratorRevision × InputSelection × Acceptance) := do
  let mut revision : Option GeneratorRevision := none
  let mut inputs : Option InputSelection := none
  let mut acceptance : Option Acceptance := none
  for option in options do
    if let some value := GeneratorRevision.ofPureVersion? option then
      unless spec.g0 && revision.isNone do
        throw (IO.userError s!"unexpected G0 generator version {option}")
      revision := some value
    else if let some value := InputSelection.ofVersion? option then
      unless spec.runtimeInput && inputs.isNone do
        throw (IO.userError s!"unexpected input selection {option}")
      inputs := some value
    else if let some value := Acceptance.ofVersion? option then
      unless spec.identityFilter && acceptance.isNone do
        throw (IO.userError s!"unexpected acceptance filter {option}")
      acceptance := some value
    else throw (IO.userError s!"unknown generation option {option}")
  return (revision.getD .v1, inputs.getD .boundary, acceptance.getD .profile)

private def execute (args : List String) : IO Json := do
  if let command :: seed :: nodes :: count :: attempts :: fuel :: options := args then
    if let some spec := generator command then
      if options.length ≤ 3 then
        let count ← natural "case count" count 1024
        unless count > 0 do throw (IO.userError "case count must be positive")
        let seed := Seed.ofNat (← natural "seed" seed (2 ^ 64 - 1))
        let nodes ← natural "node budget" nodes 512
        let attempts ← natural "attempt limit" attempts 10000
        let fuel ← natural "execution fuel" fuel 10000000
        let (revision, inputs, acceptance) ← generationOptions spec options
        return spec.run seed nodes count attempts fuel revision inputs acceptance
  match args with
  | "emit" :: file :: rest =>
      let checked ← get (checkedProgram (← readJson file))
      get ((emitCase checked (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest)).mapError reprStr)
  | "input-emit" :: file :: input :: rest =>
      let function ← get (Input.checkedFunction (← readJson file))
      let input ← get (Input.inputWord input)
      get (Input.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "aggregate-call-graph-emit" :: file :: input :: rest =>
      let function ← get (AggregateCallGraph.checkedFunction (← readJson file))
      let input ← get (AggregateCallGraph.inputWord input)
      get (AggregateCallGraph.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "call-graph-loop-emit" :: file :: input :: rest =>
      let plan ← get (CallGraphLoop.checkedPlan (← readJson file))
      let input ← get (CallGraphLoop.inputWord input)
      get (CallGraphLoop.emitCase plan input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "call-graph-emit" :: file :: input :: rest =>
      let function ← get (CallGraph.checkedFunction (← readJson file))
      let input ← get (CallGraph.inputWord input)
      get (CallGraph.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "primitive-emit" :: file :: input :: rest =>
      let function ← get (Primitive.checkedFunction (← readJson file))
      let input ← get (Primitive.inputWord input)
      get (Primitive.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "function-emit" :: file :: input :: rest =>
      let function ← get (Function.checkedFunction (← readJson file))
      let input ← get (Input.inputWord input)
      get (Function.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "module-emit" :: file :: input :: rest =>
      let function ← get (Modules.checkedPlan (← readJson file))
      let input ← get (Input.inputWord input)
      get (Modules.emitCase function input (Json.mkObj [("kind", toJson "imported")])
        (← fuelValue rest))
  | "comptime-emit" :: file :: input :: rest =>
      let function ← get (Comptime.checkedPlan (← readJson file))
      let input ← get (Input.inputWord input)
      get (Comptime.emitCase function input (Json.mkObj [("kind", toJson "imported")])
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
  | "nested-loop-emit" :: file :: input :: rest =>
      let plan ← get (NestedLoop.checkedPlan (← readJson file))
      let input ← get (Input.inputWord input)
      get (NestedLoop.emitCase plan input (Json.mkObj [("kind", toJson "imported")])
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
      if (json.getObjValAs? String "schema").toOption == some Modules.caseSchema then
        let checked ← get (Modules.caseProgram json)
        return Modules.observe checked.plan checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some Comptime.caseSchema then
        let checked ← get (Comptime.caseProgram json)
        return Comptime.observe checked.plan checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some Closure.caseSchema then
        let checked ← get (Closure.caseProgram json)
        return Closure.observe checked.plan checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some Generic.caseSchema then
        let checked ← get (Generic.caseProgram json)
        return Generic.observe checked.plan checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some NestedLoop.caseSchema then
        let checked ← get (NestedLoop.caseProgram json)
        return NestedLoop.observe checked.plan checked.input fuel
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
      else if (json.getObjValAs? String "schema").toOption == some CallGraph.caseSchema then
        let checked ← get (CallGraph.caseProgram json)
        return CallGraph.observe checked.function checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some CallGraphLoop.caseSchema then
        let checked ← get (CallGraphLoop.caseProgram json)
        return CallGraphLoop.observe checked.plan checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some AggregateCallGraph.caseSchema then
        let checked ← get (AggregateCallGraph.caseProgram json)
        return AggregateCallGraph.observe checked.function checked.input fuel
      else if (json.getObjValAs? String "schema").toOption == some Primitive.caseSchema then
        let checked ← get (Primitive.caseProgram json)
        return Primitive.observe checked.function checked.input fuel
      else
        let checked ← get (caseProgram json)
        return observe checked fuel
  | "replay" :: file :: rest =>
      let json ← readJson file
      let fuel ← fuelValue rest
      get (if (json.getObjValAs? String "schema").toOption == some Modules.caseSchema then
        Modules.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Comptime.caseSchema then
        Comptime.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Closure.caseSchema then
        Closure.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Generic.caseSchema then
        Generic.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some NestedLoop.caseSchema then
        NestedLoop.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Loop.caseSchema then
        Loop.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Aggregate.caseSchema then
        Aggregate.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Mutation.caseSchema then
        Mutation.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Function.caseSchema then
        Function.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Input.caseSchema then
          Input.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some CallGraph.caseSchema then
          CallGraph.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some CallGraphLoop.caseSchema then
          CallGraphLoop.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some AggregateCallGraph.caseSchema then
          AggregateCallGraph.replayCase json fuel
        else if (json.getObjValAs? String "schema").toOption == some Primitive.caseSchema then
          Primitive.replayCase json fuel else replayCase json fuel)
  | "shrink" :: file :: limit :: rest =>
      let json ← readJson file
      let limit ← natural "shrink limit" limit 4096
      let fuel ← fuelValue rest
      get (if (json.getObjValAs? String "schema").toOption == some Modules.caseSchema then
        Modules.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Comptime.caseSchema then
        Comptime.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Closure.caseSchema then
        Closure.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Generic.caseSchema then
        Generic.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some NestedLoop.caseSchema then
        NestedLoop.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Loop.caseSchema then
        Loop.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Aggregate.caseSchema then
        Aggregate.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Mutation.caseSchema then
        Mutation.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Function.caseSchema then
        Function.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Input.caseSchema then
          Input.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some CallGraph.caseSchema then
          CallGraph.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some CallGraphLoop.caseSchema then
          CallGraphLoop.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some AggregateCallGraph.caseSchema then
          AggregateCallGraph.shrinkCases json limit fuel
        else if (json.getObjValAs? String "schema").toOption == some Primitive.caseSchema then
          Primitive.shrinkCases json limit fuel else shrinkCases json limit fuel)
  | _ => throw (IO.userError "usage: semantic-case-tool generate|input-generate|primitive-generate|call-graph-generate|call-graph-loop-generate|aggregate-call-graph-generate|function-generate|mutation-generate|aggregate-generate|loop-generate|nested-loop-generate|generic-generate|closure-generate|comptime-generate|module-generate SEED NODES COUNT ATTEMPTS FUEL [G0-GENERATOR-VERSION, not for call-graph commands] [seeded-inputs-v1/splitmix64, not for generate] [exclude-boundary-identity-v1, not for generate, loop-generate, nested-loop-generate, call-graph-loop-generate or generic-generate] | emit PROGRAM.json [FUEL] | input-emit|primitive-emit|call-graph-emit|aggregate-call-graph-emit|function-emit|mutation-emit|aggregate-emit FUNCTION.json INPUT [FUEL] | loop-emit|nested-loop-emit|call-graph-loop-emit|generic-emit|closure-emit|comptime-emit|module-emit PLAN.json INPUT [FUEL] | observe CASE.json [FUEL] | replay CASE.json [FUEL] | shrink CASE.json LIMIT [FUEL]")

def main (args : List String) : IO UInt32 := do
  try
    let result ← execute args
    IO.println result.compress
    return 0
  catch error =>
    IO.println (Json.mkObj [("stage", toJson "case-tool"),
      ("status", toJson "rejected"), ("detail", toJson error.toString)]).compress
    return 2
