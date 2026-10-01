import Solcore.Frontend.SourceCoreCallableIndexedLedger
import Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableIndexedPrograms.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedAncestry.Prepared.mk

/-! Actual indexed compiler regressions. The graph is prepared once before
execution. Native snapshots contain one integer state index, while cached
recipes retain distinct read-caller and lexical source profiles. Compiler
receipts, broad native store typing, real allocation markers and checkpoints
remain part of the enclosing artifact; carrier shape alone is not authority. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedPrograms
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Frame := SourceCoreCallableIndexedFrames.Frame
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared (checked : Checked) := Solcore.Frontend.SourceCoreCallableIndexedPrograms.Prepared checked

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
    "function deep() returns (Word) { let f0 = lam(item0) { let f1 = lam(item1) { let f2 = lam(item2) { let probeDeep: Word = 7; return probeDeep; }; return f2(true); }; return f1(true); }; return f0(true); }",
    "function repeatViews(limit: Word) returns (Word) { let total = 0; let f = lam(item) { total += 1; return item; }; let i = 0; while (i < limit) { f(true); i += 1; } return total; }",
    "function looping(limit: Word) returns (Word) { let total = 0; for (let i = 0; i < limit; i += 1) { total += i; } return total; }",
    "function absent(seed: Word) returns (Word) { let f = lam(item) { seed += 1; let absent: Word; return absent; }; return f(0); }",
    "function spin() returns (Word) { let f = lam() -> Word { while (true) {} return 0; }; return f(); }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"indexed native fixture missing {name}")
private def initial : SourceCoreAllocationLedger.SourceHeap :=
  [⟨.word, none⟩, ⟨.function .word .word, none⟩, ⟨.mapping .word .word, none⟩]

example {checked : Checked} (prepared : Prepared checked) :
    SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base
      (SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
      prepared.fuel = .ok prepared.secondPass.closures := prepared.secondPass.compiled

example {checked : Checked} {prepared : Prepared checked}
    (completion : SourceCoreCallableIndexedPrograms.Completion prepared) :
    Core.RuntimeStoreHasTypes (SourceCoreCallableIndexedLedger.world completion)
      (SourceCoreCallableIndexedLedger.store completion) prepared.layouts.definitions :=
  SourceCoreCallableIndexedLedger.store_typed completion

private def successful {checked : Checked} (prepared : Prepared checked) (owner : Key)
    (arguments : List SourceTypedRuntime.Value) (expected : Nat) (spent : Nat) :
    IO (SourceCoreCallableIndexedPrograms.Completion prepared) := do
  let first ← get "indexed native start" (prepared.runSource owner arguments spent 500)
  let early ← get "indexed partial typed ledger" (SourceCoreCallableIndexedLedger.scan first initial)
  assertTrue (early.ledger.initialHeap.map (·.type) == initial.map (·.type)) "suspension altered inert source prefix"
  let completion := first.resume 150000
  let ledger ← get "indexed complete typed ledger" (SourceCoreCallableIndexedLedger.scan completion initial)
  assertTrue ledger.ledger.pending.isNone "indexed completion retained an incomplete marker"
  assertTrue (ledger.ledger.rows.all (fun row => initial.length ≤ row.sourceLocation.index))
    "indexed administrative cell entered the source prefix"
  assertTrue (SourceCoreCallableIndexedLedger.frame? completion == some .empty)
    "indexed invocation failed to restore its empty current frame"
  match completion.result.native.observation with
  | .succeeded (.word value) _ => assertTrue (value == w expected) "indexed execution changed the result"
  | other => throw (IO.userError s!"indexed invocation did not succeed: {reprStr other}")
  pure completion

private def shared {checked : Checked} (prepared : Prepared checked)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (owner : Key) : IO Unit := do
  let named ← match graph.inputs.callable.table.idAt? (.named owner) with
    | some named => pure named | none => throw (IO.userError "indexed shared origin missing")
  let lexical := SourceCoreCallableIndexedDispatch.namedFrame graph.table named
  let rootPosition ← match lexical.index? with
    | some index => pure index | _ => throw (IO.userError "indexed lexical root unavailable")
  let view ← match graph.inputs.views.entries.filter (·.view.binding.binder.name == "shared") with
    | [view] => pure view | _ => throw (IO.userError "wrong indexed shared view count")
  let target ← match graph.inputs.callable.table.idAt?
      (.lambda view.view.owner view.view.principal.initializer view.view.cumulative) with
    | some target => pure target | none => throw (IO.userError "indexed shared target missing")
  let mut expected : List Frame := []
  let mut callerSources : List TypedSource := []
  for outer in graph.inputs.views.entries.filter (·.view.binding.binder.name == "outer") do
    let outerTarget ← match graph.inputs.callable.table.idAt?
        (.lambda outer.view.owner outer.view.principal.initializer outer.view.cumulative) with
      | some target => pure target | none => throw (IO.userError "indexed outer target missing")
    let caller := SourceCoreCallableIndexedDispatch.selectedFrame graph.table outerTarget lexical
      (SourceCoreCallableIndexedDispatch.readFrame outer.id outerTarget lexical)
    let callerPosition ← match caller.index? with
      | some index => pure index | _ => throw (IO.userError "indexed outer transition missing")
    let recipe ← match graph.recipeAt? callerPosition rootPosition view.id target with
      | some recipe => pure recipe | none => throw (IO.userError "indexed cached paired recipe missing")
    let next := SourceCoreCallableIndexedDispatch.selectedFrame graph.table target lexical
      (SourceCoreCallableIndexedDispatch.readFrame view.id target caller)
    expected := expected ++ [next]
    callerSources := callerSources ++ [recipe.caller.metadata.source]
  assertTrue (expected.length == 2 && callerSources.eraseDups.length == 2)
    "indexed preparation collapsed occurrence-specific read caller metadata"
  for spent in [0, 31, 150000] do
    let completion ← successful prepared owner [.word (w 3)] 6 spent
    let ledger ← get "shared indexed ledger" (SourceCoreCallableIndexedLedger.scan completion initial)
    let seed ← match ledger.ledger.rows.find? (·.entry.key.binder.name == "seed") with
      | some row => pure row | none => throw (IO.userError "indexed shared seed missing")
    let principal ← match ledger.ledger.rows.find? (·.entry.key.binder.name == "shared") with
      | some row => pure row | none => throw (IO.userError "indexed shared bundle missing")
    assertTrue (principal.environment == [(seed.entry.key.binder.id, seed.sourceLocation)])
      "indexed read-parent compilation changed principal lexical captures"
    let mut observed : List Frame := []
    let mut sources : List TypedSource := []
    for row in ledger.ledger.rows do
      let snapshot ← get "indexed allocation snapshot"
        (SourceCoreCallableIndexedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
      let state ← match SourceCoreCallableIndexedDispatch.lookup? graph.table snapshot.frame with
        | some (some state) => pure state
        | _ => throw (IO.userError s!"actual indexed allocation {row.entry.key.binder.name} lacks cached metadata")
      assertTrue (match snapshot.frame with | .state _ => true | _ => false)
        "source allocation saved a recursive or transient frame"
      if row.entry.key.binder.name == "probe" then
        assertTrue (expected.contains snapshot.frame) "native shared application selected the wrong indexed pair"
        assertTrue (state.nativeActive != state.metadata.active && state.metadata.active == view.view.ownSubstitution)
          "native cumulative context leaked into original source principal metadata"
        observed := observed ++ [snapshot.frame]
        sources := sources ++ [state.metadata.source]
    assertTrue (observed.length == 2 && sources.eraseDups.length == 1)
      "indexed shared calls changed their single original source principal"

private def escaped {checked : Checked} (prepared : Prepared checked)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (getOwner useOwner : Key) : IO Unit := do
  let named ← match graph.inputs.callable.table.idAt? (.named getOwner) with
    | some named => pure named | none => throw (IO.userError "indexed get origin missing")
  let lexical := SourceCoreCallableIndexedDispatch.namedFrame graph.table named
  for spent in [0, 41, 150000] do
    let completion ← successful prepared useOwner [.word (w 3)] 17 spent
    let ledger ← get "returned indexed ledger" (SourceCoreCallableIndexedLedger.scan completion initial)
    let wrapper ← match ledger.ledger.rows.find? (fun row =>
        row.entry.key.binder.name == "f" && row.entry.key.owner == useOwner) with
      | some row => pure row | none => throw (IO.userError "escaped view payload missing")
    match wrapper.payload with
    | some (.pair (.pair _ (.closure _ _ _ (readSnapshot :: original :: _))) _) =>
      assertTrue (SourceCoreCallableIndexedFrames.decode prepared.ancestry.layout.frame readSnapshot == some lexical)
        "escaped view sampled the application caller instead of the read-time caller"
      match original with
      | .pair (.pair _ (.closure _ _ _ (creationSnapshot :: _))) _ =>
        assertTrue (SourceCoreCallableIndexedFrames.decode prepared.ancestry.layout.frame creationSnapshot == some lexical)
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
        (SourceCoreCallableIndexedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
      assertTrue (match snapshot.frame with | .state _ => true | _ => false)
        "escaped application saved a transient or recursive carrier"
      assertTrue ((SourceCoreCallableIndexedDispatch.lookup? graph.table snapshot.frame).isSome)
        "escaped indexed snapshot lacked a prepared source profile"

private def otherFlows {checked : Checked} (prepared : Prepared checked)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (program : CheckedProgram) : IO Unit := do
  for (name, arguments, expected) in [
      ("mono", [SourceTypedRuntime.Value.word (w 10)], 17),
      ("zero", [], 9), ("recursive", [.word (w 4)], 4),
      ("unused", [], 7), ("looping", [.word (w 4)], 6), ("deep", [], 7),
      ("repeatViews", [.word (w 30)], 30)] do
    let owner ← key program name
    for spent in [0, 37, 150000] do
      let completion ← successful prepared owner arguments expected spent
      let ledger ← get "indexed simple flow ledger" (SourceCoreCallableIndexedLedger.scan completion initial)
      for row in ledger.ledger.rows do
        let snapshot ← get "indexed simple flow snapshot"
          (SourceCoreCallableIndexedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
        assertTrue ((SourceCoreCallableIndexedDispatch.lookup? graph.table snapshot.frame).isSome) s!"{name} lost an allocation metadata profile"
        assertTrue (match snapshot.frame with | .state _ => true | _ => false)
          s!"{name} allocation transported a recursive or transient frame"
        if name == "zero" && row.entry.key.binder.name == "probe" then
          assertTrue (match snapshot.frame with | .state .. => true | _ => false)
            "zero-parameter monomorphic lambda acquired a generalized view"
        if name == "unused" && row.entry.key.binder.name == "unused" then
          assertTrue (row.payload == some .unit) "unused principal unexpectedly required a native lambda"
  let failed ← get "indexed language failure" (prepared.runSource (← key program "absent") [.word (w 3)] 150000 500)
  match failed.result.native.observation with
  | .failed reason _ =>
    assertTrue ((failed.result.diagnostics.diagnostic? reason).isSome) "indexed failure lost its source diagnostic"
    assertTrue (SourceCoreCallableIndexedLedger.frame? failed == some .empty) "language failure did not restore context"
    let ledger ← get "indexed failure ledger" (SourceCoreCallableIndexedLedger.scan failed initial)
    let seed ← match ledger.ledger.rows.find? (·.entry.key.binder.name == "seed") with
      | some row => pure row | none => throw (IO.userError "indexed failure lost prior effects")
    assertTrue (seed.payload == some (.word (w 4))) "language failure erased an earlier shared mutation"
  | other => throw (IO.userError s!"indexed language failure classification changed: {reprStr other}")
  let pending ← get "indexed nonterminating run" (prepared.runSource (← key program "spin") [] 5000 500)
  let resumed := pending.resume 5000
  for completion in [pending, resumed] do
    assertTrue (match completion.result.native.observation with | .outOfFuel .. => true | _ => false)
      "infinite source loop was reported as completion"
    let _ ← get "indexed suspended ledger" (SourceCoreCallableIndexedLedger.scan completion initial)
    let current ← match SourceCoreCallableIndexedLedger.frame? completion with
      | some current => pure current | none => throw (IO.userError "suspended indexed frame missing")
    assertTrue ((SourceCoreCallableIndexedDispatch.lookup? graph.table current).isSome) "suspended callable lost its prepared metadata profile"

def run : IO Unit := do
  let program ← get "indexed source checker" (checkProgram workspace)
  let names := ["sharedHistory", "getLocal", "useReturned", "mono", "zero", "recursive", "unused", "deep", "repeatViews", "looping", "absent", "spin"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"indexed worklist failed: {reprStr other}")
  let automatic ← get "indexed compatible base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← get "indexed two-pass compiler" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let graph := prepared.ancestry.graph
  assertTrue (prepared.entries.length == keys.length) "indexed root inventory changed"
  assertTrue (prepared.layouts.definitions.take automatic.checked.catalog.definitions.length == automatic.checked.catalog.definitions)
    "indexed administrative suffix changed the original catalog"
  assertTrue (!prepared.layouts.entries.isEmpty) "indexed compilation emitted no source markers"
  shared prepared graph (← key program "sharedHistory")
  escaped prepared graph (← key program "getLocal") (← key program "useReturned")
  otherFlows prepared graph program
  IO.println "actual indexed callable compiler: cached caller/lexical edges, constant-depth snapshots, shared captures, failures and typed resume GREEN"

end Tests.SourceCoreCallableIndexedPrograms
