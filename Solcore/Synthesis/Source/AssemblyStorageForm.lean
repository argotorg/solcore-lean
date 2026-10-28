import Solcore.Synthesis.Core.GeneratorV2
import Solcore.Synthesis.Core.Seed
import Solcore.Synthesis.Source.AggregateRenderer

/-! The rendering forms shared by the inline Yul storage and Keccak loops. In
every form the loop is a Solcore `while` loop around one Solcore step call,
since a Yul block can call only builtins and its own Yul functions; the forms
differ in how the iteration's storage, hash and log work is split into
`assembly` blocks around that call. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AssemblyStorage

open Solcore.Core.Wire (Expr)
open Solcore.Synthesis.Core.Aggregates (CheckedDAG)

/-- How an iteration's Yul blocks surround the step call. -/
inductive Form where
  /-- A read block before the call and a write block after it, which computes
  the slot again; the counter advances in Solcore. -/
  | split
  /-- The read block assigns the slot to a Solcore local that the write block
  uses; the write block advances the counter. -/
  | carried
  /-- One block after the call writes, advances the counter and reads the next
  iteration; a block before the loop reads the first. -/
  | pipelined
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Form

def all : List Form := [.split, .carried, .pipelined]

def name : Form → String
  | .split => "split"
  | .carried => "carried"
  | .pipelined => "pipelined"

def ofString? : String → Option Form
  | "split" => some .split
  | "carried" => some .carried
  | "pipelined" => some .pipelined
  | _ => none

theorem ofString?_name (form : Form) : ofString? form.name = some form := by
  cases form <;> rfl

end Form

/-- A SplitMix64 hash of the seed in a profile's own domain, so that
consecutive seeds vary in form independently of the plan. -/
def formFor (domain : UInt64) (seed : Solcore.Synthesis.Core.Seed) : Form :=
  Form.all[(Solcore.Synthesis.Core.GeneratorV2.mix (seed.toUInt64 ^^^ domain)).toNat % Form.all.length]?.getD .split

/-- The step's helpers as `sc_fn<k>` and its entry as `sc_step`, rendered as
in the parent loop profiles. -/
def stepLines (step : CheckedDAG) : Except EmitError (List String) := do
  let mut names : List String := []
  let mut lines : List String := []
  for (body, index) in step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 step.entry
  let result ← AggregateRenderer.requireValue entry
  return lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", ""]

/-- The imports: std, its dispatch, and `std.opcodes` only for the step's
opcode aliases. -/
def importLines (step : CheckedDAG) : List String :=
  ["import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (step.helpers ++ [step.entry]) ++ [""]

end Solcore.Synthesis.Source.AssemblyStorage
