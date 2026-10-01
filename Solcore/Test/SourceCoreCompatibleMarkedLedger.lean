import Solcore.Frontend.SourceCoreCompatibleMarkedLedger
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! A real checked source program supplies completed, failed and suspended
native observations. Every snapshot is scanned with its actual finite-world
typing; the scan does not evaluate source expressions or inspect the retained
legacy heap prefix. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMarkedLedger
open Solcore Solcore.Frontend SourceInference
open SourceCoreCompatibleMarkedLedger
abbrev Key := SourceSpecialization.SpecializationKey

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function success(value: Word) returns (Word) { let next = value + 1; return next; }",
    "function failure(value: Word) returns (Word) { let absent: Word; return absent; }",
    "function forever(value: Word) returns (Word) { let total = value; while (true) { total += 1; } return total; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"marked ledger fixture missing {name}")

private def opaquePrefix (key : Key) : SourceHeap := [
  {type := .error, value := some (.closure [] .unit []
    {owner := key.declaration, inputs := [], roots := [], nodes := []}
    key [(⟨key.declaration, 999⟩, ⟨777⟩)] [])},
  {type := .word, value := some (.bool true)}]

private def inspect {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (initialHeap : SourceHeap) : IO (Receipt completion initialHeap) :=
  match scan completion initialHeap with
  | .ok receipt => pure receipt
  | .error error => throw (IO.userError s!"actual marked store failed ledger scan: {reprStr error}")

private def start {checked : Checked} (prepared : Prepared checked) (key : Key) (fuel : Nat) :
    IO (Completion prepared) :=
  match prepared.runSource key [.word (Core.Word.ofNatModulo 9)] fuel 256 with
  | .ok completion => pure completion
  | .error error => throw (IO.userError s!"marked ledger execution failed: {reprStr error}")

/-- Every single transition is observed, including the gap between marker
and optional payload allocation. Only completed pairs extend the location map. -/
private def stepSuccess {checked : Checked} (prepared : Prepared checked) (key : Key) : IO Unit := do
  let initialHeap := opaquePrefix key
  let mut completion ← start prepared key 0
  let mut previous : List SourceCoreAllocationLedger.LocationEntry := []
  let mut sawPending := false
  let mut finished := false
  for _ in List.range 1000 do
    let receipt ← inspect completion initialHeap
    let current := receipt.ledger.locations
    assertTrue (decide (current.take previous.length = previous)) "resumption changed an existing source location"
    assertTrue (reprStr receipt.ledger.initialHeap == reprStr initialHeap) "opaque source prefix changed"
    if receipt.ledger.pending.isSome then sawPending := true
    previous := current
    match completion.result.native.observation with
    | .succeeded value _ =>
      assertTrue (decide (value = .word (Core.Word.ofNatModulo 10))) "source result changed"
      assertTrue (current.map (·.source.index) == [2, 3]) "source-visible allocation order changed"
      assertTrue receipt.ledger.pending.isNone "successful allocation left pending marker"
      let resumed := completion.resume 0
      assertTrue (decide (store resumed = store completion)) "terminal resumption changed the store"
      finished := true
      break
    | .outOfFuel _ => completion := completion.resume 1
    | observation => throw (IO.userError s!"unexpected success observation: {reprStr observation}")
  assertTrue finished "success fixture did not terminate"
  assertTrue sawPending "single-step fixture never observed marker-only checkpoint"

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"marked ledger checker failed: {reprStr error}")
  let successKey ← key program "success"
  let failureKey ← key program "failure"
  let foreverKey ← key program "forever"
  let plan ← match SourceSpecializationWorklist.run program
      ([successKey, failureKey, foreverKey].map (fun key => ⟨key.declaration, []⟩)) 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"marked ledger plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 256 with
    | .ok automatic => pure automatic
    | .error error => throw (IO.userError s!"marked ledger base factory failed: {reprStr error}")
  let prepared ← match SourceCoreCompatibleMarkedFunctions.prepare automatic.prepared 256 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"marked ledger factory failed: {reprStr error}")
  stepSuccess prepared successKey
  let failed ← start prepared failureKey 10000
  let failureReceipt ← inspect failed (opaquePrefix failureKey)
  match failed.result.native.observation with
  | .failed _ actual =>
    assertTrue (decide (store failed = actual)) "language failure lost actual store"
    assertTrue (failureReceipt.ledger.rows.length == 2) "language failure lost source cells"
    assertTrue ((failureReceipt.ledger.rows.map (·.payload.isSome)) == [true, false])
      "uninitialized failure changed optional source payload"
  | observation => throw (IO.userError s!"failure became another observation: {reprStr observation}")
  let suspended ← start prepared foreverKey 1000
  let first ← inspect suspended (opaquePrefix foreverKey)
  match suspended.result.native.observation with
  | .outOfFuel checkpoint =>
    assertTrue (decide (store suspended = checkpoint.store)) "suspension lost checkpoint store"
    assertTrue (first.ledger.rows.length == 2) "loop administrative cells leaked into source heap"
  | observation => throw (IO.userError s!"loop suspension became terminal: {reprStr observation}")
  let resumed := suspended.resume 1000
  let second ← inspect resumed (opaquePrefix foreverKey)
  match resumed.result.native.observation with
  | .outOfFuel _ =>
    assertTrue (decide (first.ledger.locations = second.ledger.locations)) "loop resume changed source cell locations"
    assertTrue (decide (first.ledger.rows.map (·.environment) = second.ledger.rows.map (·.environment)))
      "loop resume changed captured lexical references"
  | observation => throw (IO.userError s!"infinite loop unexpectedly completed: {reprStr observation}")

example {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) :
    Core.RuntimeStoreHasTypes (world completion) (store completion) prepared.layouts.definitions :=
  store_typed completion

example {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared)
    {checkpoint : Core.State} (suspended : completion.result.native.observation = .outOfFuel checkpoint) :
    store completion = checkpoint.store := suspended_store completion suspended

end Tests.SourceCoreCompatibleMarkedLedger
