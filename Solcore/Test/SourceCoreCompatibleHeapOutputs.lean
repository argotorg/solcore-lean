import Solcore.Frontend.SourceCoreCompatibleHeapOutputs
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCompatibleHeapOutputs.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCompatibleHeapOutputs.decodeCell

/-! Actual checked source inputs, ordinary lets, updates, lazy mappings and
callable leaves are exported from their live typed marked stores. Initial
source cells are retained without validation. Generalized/lambda cells remain
explicit rejected boundaries of this first heap decoder. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleHeapOutputs
open Solcore Solcore.Frontend SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Marked := SourceCoreCompatibleMarkedFunctions.Prepared
abbrev Decoder {checked : Checked} (marked : Marked checked) := SourceCoreCompatibleHeapOutputs.Prepared marked
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Cell := SourceTypedRuntime.Cell

private def w (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def word (value : Nat) : SourceTypedRuntime.Value := .word (w value)
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function updates(value: Word) returns (Word) { let next = value; next += 2; return next; }",
    "function lazy() returns (Word) { let table: mapping(Word => Word); table[1] = 7; return 0; }",
    "function alias(value: mapping(@Word => Word)) returns (Word) { let stored = value; return 1; }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function holders() returns (Word) { let named = inc; let native = wordToInteger; return named(5); }",
    "function failure(value: Word) returns (Word) { let changed = value; changed = 11; let absent: Word; return absent; }",
    "function lambdaCell() returns (Word) { let f: function(Word) returns (Word) = lam(value: Word) { return value; }; return 1; }",
    "function principal() returns (Word) { let f = lam(value) { return value; }; return 1; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"heap output fixture missing {name}")

private def initial (owner : Key) : List Cell := [
  {type := .error, value := some (.closure [] .unit []
    {owner := owner.declaration, inputs := [], roots := [], nodes := []}
    owner [(⟨owner.declaration, 999⟩, ⟨777⟩)] [])},
  {type := .word, value := some (.bool true)}]

private def checkCells {checked : Checked} (marked : Marked checked) (decoder : Decoder marked)
    (owner : Key) (arguments : List SourceTypedRuntime.Value) (expected : List Cell) : IO Unit := do
  let completion ← match marked.runSource owner arguments 100000 512 with
    | .ok result => pure result
    | .error error => throw (IO.userError s!"heap source invocation failed: {reprStr error}")
  let exported ← match SourceCoreCompatibleHeapOutputs.exportHeap decoder completion (initial owner) 512 with
    | .ok exported => pure exported
    | .error error => throw (IO.userError s!"heap export failed: {reprStr error}")
  assertTrue (reprStr exported.cells == reprStr expected)
    s!"heap values or raw source types changed: {reprStr exported.cells}"
  assertTrue (reprStr (exported.heap.take 2) == reprStr (initial owner)) "opaque heap prefix changed"
  assertTrue (exported.receipt.ledger.locations.map (·.source.index) == (List.range expected.length).map (2 + ·))
    "source-visible allocation order changed"
  assertTrue (exported.receipt.ledger.rows.map (fun row => row.environment.map Prod.fst) ==
    exported.receipt.ledger.rows.map (fun row => row.entry.key.scope.map Prod.fst)) "capture binder metadata changed"

private def checkpoints {checked : Checked} (marked : Marked checked) (decoder : Decoder marked) (owner : Key) : IO Unit := do
  let mut completion ← match marked.runSource owner [word 9] 0 512 with
    | .ok result => pure result | .error error => throw (IO.userError (reprStr error))
  let mut prior := ([] : List SourceCoreAllocationLedger.LocationEntry)
  let mut sawPending := false
  let mut finished := false
  for _ in List.range 1500 do
    let exported ← match SourceCoreCompatibleHeapOutputs.exportHeap decoder completion (initial owner) 512 with
      | .ok exported => pure exported
      | .error error => throw (IO.userError s!"checkpoint heap export failed: {reprStr error}")
    assertTrue (reprStr (exported.heap.take 2) == reprStr (initial owner)) "checkpoint lost opaque prefix"
    let locations := exported.receipt.ledger.locations
    assertTrue (decide (locations.take prior.length = prior)) "checkpoint changed prior source locations"
    prior := locations
    if exported.receipt.ledger.pending.isSome then sawPending := true
    match completion.result.native.observation with
    | .succeeded .. => finished := true; break
    | .outOfFuel _ => completion := completion.resume 1
    | observation => throw (IO.userError s!"checkpoint became unexpected result: {reprStr observation}")
  assertTrue sawPending "no pending source allocation checkpoint was exercised"
  assertTrue finished "finite update fixture did not finish"

private def rejected {checked : Checked} (marked : Marked checked) (decoder : Decoder marked) (owner : Key)
    (expected : SourceCoreCompatibleHeapOutputs.Error → Bool) : IO Unit := do
  let completion ← match marked.runSource owner [] 100000 512 with
    | .ok result => pure result | .error error => throw (IO.userError (reprStr error))
  match SourceCoreCompatibleHeapOutputs.exportHeap decoder completion [] 512 with
  | .error error => assertTrue (expected error) s!"heap boundary rejection changed: {reprStr error}"
  | .ok _ => throw (IO.userError "unsupported heap payload unexpectedly exported")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"heap fixture checker failed: {reprStr error}")
  let names := ["updates", "lazy", "alias", "holders", "failure", "lambdaCell", "principal"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"heap fixture worklist failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 512 with
    | .ok automatic => pure automatic
    | .error error => throw (IO.userError s!"heap fixture base factory failed: {reprStr error}")
  let marked ← match SourceCoreCompatibleMarkedFunctions.prepare automatic.prepared 512 with
    | .ok marked => pure marked
    | .error error => throw (IO.userError s!"heap fixture marked factory failed: {reprStr error}")
  let decoder ← match SourceCoreCompatibleHeapOutputs.prepare marked with
    | .ok decoder => pure decoder
    | .error error => throw (IO.userError s!"heap output recipe failed: {reprStr error}")
  let updates ← key program "updates"
  checkCells marked decoder updates [word 9] [⟨.word, some (word 9)⟩, ⟨.word, some (word 11)⟩]
  checkCells marked decoder (← key program "lazy") []
    [⟨.mapping .word .word, some (.mapping .word .word [(word 1, word 7)])⟩]
  let raw : SourceTypedRuntime.Value := .mapping (.proxy (.comptime .word)) .word
    [(.proxy (.comptime .word), word 7), (.proxy (.comptime .word), word 8)]
  let aliasType := TypeSystem.Ty.mapping (.proxy .word) .word
  checkCells marked decoder (← key program "alias") [raw] [⟨aliasType, some raw⟩, ⟨aliasType, some raw⟩]
  let inc ← key program "inc"
  checkCells marked decoder (← key program "holders") []
    [⟨.function .word .word, some (.global inc [])⟩,
     ⟨.function .word .integer, some (.builtin .wordToInteger)⟩, ⟨.word, some (word 5)⟩]
  checkCells marked decoder (← key program "failure") [word 9]
    [⟨.word, some (word 9)⟩, ⟨.word, some (word 11)⟩, ⟨.word, none⟩]
  checkpoints marked decoder updates
  rejected marked decoder (← key program "lambdaCell") fun
    | .output {code := .lambdaExportRequiresLedger _, ..} => true | _ => false
  rejected marked decoder (← key program "principal") fun
    | .generalizedBinding _ _ => true | _ => false

example {checked : Checked} {marked : Marked checked} {decoder : Decoder marked}
    {completion : SourceCoreCompatibleMarkedFunctions.Completion marked} {initial : List Cell}
    (exported : SourceCoreCompatibleHeapOutputs.Export decoder completion initial) :
    exported.heap.take initial.length = initial := exported.prefix_exact

example {checked : Checked} {marked : Marked checked} {decoder : Decoder marked}
    {completion : SourceCoreCompatibleMarkedFunctions.Completion marked} {initial : List Cell}
    (exported : SourceCoreCompatibleHeapOutputs.Export decoder completion initial) :
    exported.cells.map (·.type) = exported.receipt.ledger.rows.map SourceCoreCompatibleHeapOutputs.rawType :=
  exported.decoded.types_exact

end Tests.SourceCoreCompatibleHeapOutputs
