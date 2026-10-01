import Solcore.Frontend.SourceCoreCallablePairedLedger
import Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallablePairedPrograms.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedAncestry.Prepared.mk

/-! Actual two-pass compiler execution retains a generalized read's caller
snapshot separately from the principal's lexical creation snapshot. This test
uses the owned native runner and allocation ledger; decoding a frame alone is
not treated as evidence of its execution history or source closure identity.
-/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePairedPrograms
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Frame := SourceCoreCallablePairedFrames.Frame
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared (checked : Checked) := Solcore.Frontend.SourceCoreCallablePairedPrograms.Prepared checked

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function sharedHistory(seed: Word) returns (Word) {",
    " let shared = lam(item) { let probe: Word = 0; return item; };",
    " let outer = lam(value) { keep(value); return shared(value); };",
    " return outer(seed) + outer(seed); }",
    "function getLocal(seed: Word) returns (F) { let f = lam(item) { seed += 1; return item; }; return f; }",
    "function useReturned(seed: Word) returns (Word) { let f = getLocal(seed); return f(8) + f(9); }",
    "function mono(seed: Word) returns (Word) { let f: F = lam(item: Word) -> Word { seed += item; return seed; }; f(3); return f(4); }",
    "function zero() returns (Word) { let f = lam() -> Word { let probe: Word = 9; return probe; }; return f(); }",
    "function recursive(n: Word) returns (Word) { let f: F; f = lam(left: Word) { return left == 0 ? 0 : f(left - 1) + 1; }; return f(n); }",
    "function unused() returns (Word) { let unused = lam(item) { return item; }; return 7; }",
    "function looping(limit: Word) returns (Word) { let total = 0; for (let i = 0; i < limit; i += 1) { total += i; } return total; }",
    "function absent(seed: Word) returns (Word) { let f = lam(item) { seed += 1; let absent: Word; return absent; }; return f(0); }",
    "function spin() returns (Word) { let f = lam() -> Word { while (true) {} return 0; }; return f(); }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"paired native fixture missing {name}")
private def initial : SourceCoreAllocationLedger.SourceHeap :=
  [⟨.word, none⟩, ⟨.function .word .word, none⟩, ⟨.mapping .word .word, none⟩]

example {checked : Checked} (prepared : Prepared checked) :
    SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base
      (SourceCoreCallablePairedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
      prepared.fuel = .ok prepared.secondPass.closures := prepared.secondPass.compiled

example {checked : Checked} {prepared : Prepared checked}
    (completion : SourceCoreCallablePairedPrograms.Completion prepared) :
    Core.RuntimeStoreHasTypes (SourceCoreCallablePairedLedger.world completion)
      (SourceCoreCallablePairedLedger.store completion) prepared.layouts.definitions :=
  SourceCoreCallablePairedLedger.store_typed completion

private def successful {checked : Checked} (prepared : Prepared checked) (owner : Key)
    (arguments : List SourceTypedRuntime.Value) (expected : Nat) (spent : Nat) :
    IO (SourceCoreCallablePairedPrograms.Completion prepared) := do
  let first ← get "paired native start" (prepared.runSource owner arguments spent 500)
  let early ← get "paired partial typed ledger" (SourceCoreCallablePairedLedger.scan first initial)
  assertTrue (early.ledger.initialHeap.map (·.type) == initial.map (·.type)) "suspension altered inert source prefix"
  let completion := first.resume 150000
  let ledger ← get "paired complete typed ledger" (SourceCoreCallablePairedLedger.scan completion initial)
  assertTrue ledger.ledger.pending.isNone "paired completion retained an incomplete marker"
  assertTrue (ledger.ledger.rows.all (fun row => initial.length ≤ row.sourceLocation.index))
    "paired administrative cell entered the source prefix"
  assertTrue (SourceCoreCallablePairedLedger.frame? completion == some .empty)
    "paired invocation failed to restore its empty current frame"
  match completion.result.native.observation with
  | .succeeded (.word value) _ => assertTrue (value == w expected) "paired execution changed the result"
  | other => throw (IO.userError s!"paired invocation did not succeed: {reprStr other}")
  pure completion

private def shared {checked : Checked} (prepared : Prepared checked)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (owner : Key) : IO Unit := do
  let named ← match graph.inputs.callable.table.idAt? (.named owner) with
    | some named => pure named | none => throw (IO.userError "paired shared origin missing")
  let lexical : Frame := .named named
  let rootPosition ← match graph.table.lookupIndex? lexical with
    | some (some index) => pure index | _ => throw (IO.userError "paired lexical root unavailable")
  for spent in [0, 31, 150000] do
    let completion ← successful prepared owner [.word (w 3)] 6 spent
    let ledger ← get "shared paired ledger" (SourceCoreCallablePairedLedger.scan completion initial)
    let seed ← match ledger.ledger.rows.find? (·.entry.key.binder.name == "seed") with
      | some row => pure row | none => throw (IO.userError "paired shared seed missing")
    let shared ← match ledger.ledger.rows.find? (·.entry.key.binder.name == "shared") with
      | some row => pure row | none => throw (IO.userError "paired shared bundle missing")
    assertTrue (shared.environment == [(seed.entry.key.binder.id, seed.sourceLocation)])
      "read-parent compilation changed the principal's lexical environment"
    let mut callers : List Frame := []
    let mut sources : List TypedSource := []
    for row in ledger.ledger.rows do
      let snapshot ← get "paired allocation snapshot"
        (SourceCoreCallablePairedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
      assertTrue ((graph.table.lookup? snapshot.frame).isSome)
        s!"actual paired allocation {row.entry.key.binder.name} lacks cached metadata"
      if row.entry.key.binder.name == "probe" then
        match snapshot.frame with
        | .appliedView read target caller captured =>
          assertTrue (captured == lexical) "shared principal's creation snapshot was replaced by its read caller"
          match caller with
          | .appliedView _ _ outerCaller outerLexical =>
            assertTrue (outerCaller == lexical && outerLexical == lexical) "outer read lost one of its root snapshots"
          | _ => throw (IO.userError "shared read did not preserve its active outer caller")
          let callerPosition ← match graph.table.lookupIndex? caller with
            | some (some index) => pure index | _ => throw (IO.userError "actual shared caller unavailable")
          let recipe ← match graph.recipeAt? callerPosition rootPosition read target with
            | some recipe => pure recipe | none => throw (IO.userError "actual shared paired recipe unavailable")
          let state ← match graph.table.lookup? snapshot.frame with
            | some (some state) => pure state | _ => throw (IO.userError "actual shared source state missing")
          assertTrue (state.nativeActive != state.metadata.active &&
            state.metadata.active == recipe.read.substitution && recipe.read.witnesses.isEmpty)
            "native cumulative substitution leaked into the source principal"
          callers := callers ++ [caller]
          sources := sources ++ [state.metadata.source]
        | _ => throw (IO.userError "shared allocation did not retain the paired applied-view frame")
    assertTrue (callers.length == 2 && callers.eraseDups.length == 2 && sources.eraseDups.length == 1)
      "different read callers did not preserve the shared principal's single source profile"

private def escaped {checked : Checked} (prepared : Prepared checked)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (getOwner useOwner : Key) : IO Unit := do
  let named ← match graph.inputs.callable.table.idAt? (.named getOwner) with
    | some named => pure named | none => throw (IO.userError "paired get origin missing")
  let lexical : Frame := .named named
  for spent in [0, 41, 150000] do
    let completion ← successful prepared useOwner [.word (w 3)] 17 spent
    let ledger ← get "returned paired ledger" (SourceCoreCallablePairedLedger.scan completion initial)
    let wrapper ← match ledger.ledger.rows.find? (fun row =>
        row.entry.key.binder.name == "f" && row.entry.key.owner == useOwner) with
      | some row => pure row | none => throw (IO.userError "escaped view payload missing")
    match wrapper.payload with
    | some (.pair (.pair _ (.closure _ _ _ (readSnapshot :: original :: _))) _) =>
      assertTrue (SourceCoreCallablePairedFrameCodec.decode prepared.ancestry.layout.frame readSnapshot == some lexical)
        "escaped view sampled the application caller instead of the read-time caller"
      match original with
      | .pair (.pair _ (.closure _ _ _ (creationSnapshot :: _))) _ =>
        assertTrue (SourceCoreCallablePairedFrameCodec.decode prepared.ancestry.layout.frame creationSnapshot == some lexical)
          "escaped view lost its original lambda's creation snapshot"
      | _ => throw (IO.userError "escaped view did not retain its original native callable")
    | _ => throw (IO.userError "escaped read wrapper did not save its two values at creation")
    let seed ← match ledger.ledger.rows.find? (fun row =>
        row.entry.key.binder.name == "seed" && row.entry.key.owner == getOwner) with
      | some row => pure row | none => throw (IO.userError "escaped shared seed missing")
    assertTrue (seed.payload == some (.word (w 5))) "escaped applications split their shared mutable capture"
    let items := ledger.ledger.rows.filter (·.entry.key.binder.name == "item")
    assertTrue (items.length == 2) "escaped applications lost their source parameter allocations"
    for row in items do
      let snapshot ← get "escaped application snapshot"
        (SourceCoreCallablePairedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
      match snapshot.frame with
      | .appliedView _ _ caller captured =>
        assertTrue (caller == lexical && captured == lexical) "escaped application replaced the saved read profile"
      | _ => throw (IO.userError "escaped application lacked a paired frame")
      assertTrue ((graph.table.lookup? snapshot.frame).isSome) "escaped paired snapshot lacked a prepared source profile"

private def otherFlows {checked : Checked} (prepared : Prepared checked)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (program : CheckedProgram) : IO Unit := do
  for (name, arguments, expected) in [
      ("mono", [SourceTypedRuntime.Value.word (w 10)], 17),
      ("zero", [], 9), ("recursive", [.word (w 4)], 4),
      ("unused", [], 7), ("looping", [.word (w 4)], 6)] do
    let owner ← key program name
    for spent in [0, 37, 150000] do
      let completion ← successful prepared owner arguments expected spent
      let ledger ← get "paired simple flow ledger" (SourceCoreCallablePairedLedger.scan completion initial)
      for row in ledger.ledger.rows do
        let snapshot ← get "paired simple flow snapshot"
          (SourceCoreCallablePairedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
        assertTrue ((graph.table.lookup? snapshot.frame).isSome) s!"{name} lost an allocation metadata profile"
        if name == "zero" && row.entry.key.binder.name == "probe" then
          assertTrue (match snapshot.frame with | .lambda .. => true | _ => false)
            "zero-parameter monomorphic lambda acquired a generalized view"
        if name == "unused" && row.entry.key.binder.name == "unused" then
          assertTrue (row.payload == some .unit) "unused principal unexpectedly required a native lambda"
  let failed ← get "paired language failure" (prepared.runSource (← key program "absent") [.word (w 3)] 150000 500)
  match failed.result.native.observation with
  | .failed reason _ =>
    assertTrue ((failed.result.diagnostics.diagnostic? reason).isSome) "paired failure lost its source diagnostic"
    assertTrue (SourceCoreCallablePairedLedger.frame? failed == some .empty) "language failure did not restore context"
    let ledger ← get "paired failure ledger" (SourceCoreCallablePairedLedger.scan failed initial)
    let seed ← match ledger.ledger.rows.find? (·.entry.key.binder.name == "seed") with
      | some row => pure row | none => throw (IO.userError "paired failure lost prior effects")
    assertTrue (seed.payload == some (.word (w 4))) "language failure erased an earlier shared mutation"
  | other => throw (IO.userError s!"paired language failure classification changed: {reprStr other}")
  let pending ← get "paired nonterminating run" (prepared.runSource (← key program "spin") [] 5000 500)
  let resumed := pending.resume 5000
  for completion in [pending, resumed] do
    assertTrue (match completion.result.native.observation with | .outOfFuel .. => true | _ => false)
      "infinite source loop was reported as completion"
    let _ ← get "paired suspended ledger" (SourceCoreCallablePairedLedger.scan completion initial)
    let current ← match SourceCoreCallablePairedLedger.frame? completion with
      | some current => pure current | none => throw (IO.userError "suspended paired frame missing")
    assertTrue ((graph.table.lookup? current).isSome) "suspended callable lost its prepared metadata profile"

def run : IO Unit := do
  let program ← get "paired source checker" (checkProgram workspace)
  let names := ["sharedHistory", "getLocal", "useReturned", "mono", "zero", "recursive", "unused", "looping", "absent", "spin"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"paired worklist failed: {reprStr other}")
  let automatic ← get "paired compatible base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← get "paired two-pass compiler" (SourceCoreCallablePairedPrograms.prepare automatic.prepared 500)
  let graph ← get "paired reached metadata" (SourceCoreCallableAncestryPairedPreparation.prepare prepared.base)
  assertTrue (prepared.entries.length == keys.length) "paired root inventory changed"
  assertTrue (prepared.layouts.definitions.take automatic.checked.catalog.definitions.length == automatic.checked.catalog.definitions)
    "paired administrative suffix changed the original catalog"
  assertTrue (!prepared.layouts.entries.isEmpty) "paired compilation emitted no source markers"
  shared prepared graph (← key program "sharedHistory")
  escaped prepared graph (← key program "getLocal") (← key program "useReturned")
  otherFlows prepared graph program
  IO.println "actual paired callable frames: saved read/lexical parents, shared source profiles, escaped captures and typed resume GREEN"

end Tests.SourceCoreCallablePairedPrograms
