import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceCoreIndexedSession.Snapshot.mk
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Snapshot.saved
#check_failure Solcore.Frontend.SourceCoreIndexedSession.PrefixSnapshot.sourcePrefix
#check_failure Solcore.Frontend.SourceCoreHeapSnapshot.ObservedValue.source
#check_failure Solcore.Frontend.SourceCoreHeapSnapshot.Principal.mk
#check_failure Solcore.Frontend.SourceCoreHeapSnapshot.Principal.source
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Value.closure
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false
namespace Tests.SourceCoreHeapSnapshot
open Solcore Solcore.Frontend SourceCoreIndexedSession
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α := SourceCoreUnifiedCorpusSupport.get label
private def require (condition : Bool) (message : String) : IO Unit := SourceCoreUnifiedCorpusSupport.assertTrue condition message
private def word (value : Nat) : Value := .word (Core.Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "function inc(n: Word) returns (Word) { return n + 1; }",
  "function sum(a: Word, b: Word) returns (Word) { return a + b; }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { let f: function(Word) returns (Word) = lam(step: Word) { seed += step; return seed; }; return f; }",
  "function use(f: function(Word) returns (Word), n: Word) returns (Word) { return f(n); }",
  "function unused(captured: Word) returns (Word) { let unused = lam(item) { return (item, captured); }; return captured; }",
  "function stored(seed: Word) returns (Word) { let f: function(Word) returns (Word) = lam(step: Word) { seed += step; return seed; }; return seed; }",
  "function views(seed: Word) returns (Word) { let f = lam(item) { seed += 1; return item; }; f(true); return f(4); }",
  "function echo(table: mapping(Word => @Word)) returns (mapping(Word => @Word)) { return table; }",
  "function sourceClosure() returns (function() returns (Word)) { let captured: Word = 7; return lam() -> Word { return captured; }; }",
  "function sourceView(seed: Word) returns (function(Word) returns (Word)) { let f = lam(item) { return item; }; return f; }",
  "function failure(seed: Word) returns (Word) { let f = lam() -> Word { seed += 2; let absent: Word; return absent; }; return f(); }",
  "function spin() returns (Word) { while (true) {} return 0; }"
]
private def names : List String := ["inc", "sum", "make", "use", "unused", "stored", "views", "echo", "sourceClosure", "sourceView", "failure", "spin"]

private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (args : List Value) : IO (Completion artifact) := do
  match ← session.run key args 300000 with
  | .ok (.succeeded completion) => pure completion
  | .ok (.failed reason _) => throw (IO.userError s!"snapshot language failure: {reprStr reason}")
  | .ok (.exportError error _) => throw (IO.userError s!"snapshot export: {reprStr error}")
  | .ok (.outOfFuel _) => throw (IO.userError "snapshot execution exhausted")
  | .error error => throw (IO.userError s!"snapshot call rejected: {reprStr error}")

private def ready {artifact : Artifact} (snapshot : Snapshot artifact) : IO (Session artifact) :=
  match snapshot.restore with
  | .ready session => pure session
  | .suspended _ => throw (IO.userError "ready snapshot restored a checkpoint")

example {artifact : Artifact} (snapshot : Snapshot artifact) := snapshot.source_length
example {artifact : Artifact} (snapshot : Snapshot artifact) := snapshot.prefix_length
example {artifact : Artifact} (snapshot : Snapshot artifact) := snapshot.restore_native_size
example {artifact : Artifact} (snapshot : Snapshot artifact) := snapshot.restore_world
example {artifact : Artifact} (snapshot : Snapshot artifact) := snapshot.restore_authority
example {artifact : Artifact} (snapshot : Snapshot artifact) := snapshot.restore_typed

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "opaque heap snapshots" content names
  let recipe ← get "snapshot recipe" (Recipe.prepare compiled)
  let artifact ← recipe.open
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  -- This migration-only initial state was produced by the same cached Core
  -- artifact. Its source closure and captured indices never become Core refs.
  let (rawReturned, previous) ← match compiled.run (← key "sourceClosure") [] 1024 300000 with
    | .ok result => match result.observation with
      | .done value final => pure (value, final)
      | other => throw (IO.userError s!"prefix native fixture failed: {reprStr other}")
    | .error error => throw (IO.userError s!"prefix fixture rejected: {reprStr error}")
  let (rawView, rawPrefix) ← match compiled.run (← key "sourceView") [.word (Core.Word.ofNatModulo 5)] 1024 300000 previous with
    | .ok result => match result.observation with
      | .done value final => pure (value, final)
      | other => throw (IO.userError s!"prefix view native fixture failed: {reprStr other}")
    | .error error => throw (IO.userError s!"prefix view fixture rejected: {reprStr error}")
  let initialState : SourceTypedRuntime.RuntimeState := {heap := rawPrefix.heap ++ [
      ⟨.function .unit .word, some rawReturned⟩,
      ⟨.function .word .word, some rawView⟩,
      ⟨.comptime (.proxy .word), some (.proxy (.comptime .word))⟩,
      ⟨.mapping .word (.proxy .word), some (.mapping (.comptime .word) (.proxy (.comptime .word)) [
        (.word (Core.Word.ofNatModulo 1), .proxy (.comptime .word)),
        (.word (Core.Word.ofNatModulo 1), .proxy (.comptime .word))])⟩,
      ⟨.parameter ⟨(← key "unused").declaration, 999⟩, none⟩]}
  let inert ← match Legacy.preparePrefix artifact initialState 1024 with
    | some acceptedPrefix => pure acceptedPrefix | none => throw (IO.userError "accepted opaque closure/raw prefix rejected")
  let initial ← match (← artifact.bootstrapFromPrefix inert).resume 300000 with
    | .ready session => pure session
    | _ => throw (IO.userError "snapshot bootstrap failed")
  let original ← get "initial snapshot" (← initial.snapshot)
  require (original.prefixSize == initialState.heap.length && original.heapSize == initialState.heap.length)
    "source prefix changed or administrative globals leaked into observation"
  require (original.cells.map (·.type) == initialState.heap.map (·.type)) "raw source prefix types changed"
  require (original.cellAt? (initialState.heap.length - 1) |>.any fun cell => cell.value.isNone)
    "open uninitialized prefix was lost"
  match (original.cellAt? (initialState.heap.length - 2)).bind (·.value) with
  | some (.legacy observed) => match observed.view with
    | .mapping (.comptime _) (.proxy (.comptime _)) entries =>
      require (entries.length == 2) "ordered duplicate raw prefix mapping changed"
    | _ => throw (IO.userError "raw mapping header was canonicalized")
  | _ => throw (IO.userError "inert mapping observation was not opaque legacy data")
  match (original.cellAt? (rawPrefix.heap.length + 1)).bind (·.value) with
  | some (.legacy observed) => match observed.view with
    | .instantiated _ requirements principal =>
      require requirements.isEmpty "unqualified view invented witnesses"
      match principal.view with
      | .closure parameters _ _ environment _ =>
        require (parameters.length == 1 && !environment.isEmpty) "raw principal header/captures were lost"
      | _ => throw (IO.userError "instantiated observation lost original principal")
    | _ => throw (IO.userError "prefix observation erased instantiated wrapper")
  | _ => throw (IO.userError "prefix instantiated cell unavailable")
  let importedAgain ← match (← artifact.bootstrapFromPrefix original.prefix).resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "opaque prefix rebootstrap failed")
  let reimported ← get "reimported prefix view" (← importedAgain.snapshot)
  require (reimported.cells.map (·.type) == original.cells.map (·.type) &&
      reimported.prefixSize == original.prefixSize && importedAgain.installedGlobalsPresent)
    "opaque prefix reuse changed raw types or active native global layout"
  match importedAgain.restoreSnapshot original with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "prefix reuse transferred the original native snapshot issuer")
  let restoredInitial ← ready original
  let maker ← execute restoredInitial (← key "make") [word 10]
  let kept ← get "captured snapshot" (← maker.session.snapshot)
  let before ← ready kept
  let changed ← execute before (← key "use") [maker.value, word 2]
  require (changed.value == word 12) "restored capture lost its native shared cell"
  let rolledBack ← match changed.session.restoreSnapshot kept with
    | .ok (.ready session) => pure session
    | _ => throw (IO.userError "same-session snapshot rejected")
  let replayed ← execute rolledBack (← key "use") [maker.value, word 3]
  require (replayed.value == word 13) "snapshot kept the newer store rather than its captured store"
  let replayedAgain ← execute (← ready kept) (← key "use") [maker.value, word 3]
  require (replayedAgain.value == word 13) "duplicate restore changed handle ownership or captured state"
  -- Snapshot-created function capabilities belong to the returned registry.
  let retainedHandles := kept.cells.filterMap fun cell => match cell.value with
    | some (.data (.function handle)) => some handle | _ => none
  require (!retainedHandles.isEmpty) "source lambda parameter/cell did not export a capability"
  for handle in retainedHandles do
    discard <| get "snapshot handle exact registry" ((← ready kept).authenticate 1024 handle.sourceType (.function handle))
  let unexported ← execute replayed.session (← key "stored") [word 70]
  let branchA ← get "new heap capability branch A" (← unexported.session.snapshot)
  let branchB ← get "new heap capability branch B" (← unexported.session.snapshot)
  let newlyIssued := branchA.cells.drop kept.heapSize |>.filterMap fun cell => match cell.value with
    | some (.data (.function handle)) => some handle | _ => none
  let newHandle ← match newlyIssued.getLast? with
    | some handle => pure handle | none => throw (IO.userError "unexported stored lambda did not issue snapshot handle")
  match unexported.session.authenticate 1024 newHandle.sourceType (.function newHandle) with
  | .error {code := .unknownHandle, ..} => pure ()
  | _ => throw (IO.userError "snapshot silently changed the original registry")
  discard <| get "new snapshot registry" ((← ready branchA).authenticate 1024 newHandle.sourceType (.function newHandle))
  match (← ready branchB).authenticate 1024 newHandle.sourceType (.function newHandle) with
  | .error {code := .unknownHandle, ..} => pure ()
  | _ => throw (IO.userError "branched snapshots collided at the same registry slot")
  let invoked ← match ← (← ready branchA).invokePacked newHandle (word 2) 300000 with
    | .ok (.succeeded completion) => pure completion
    | _ => throw (IO.userError "stored snapshot-issued capability failed native invocation")
  require (invoked.value == word 72) "stored capability lost its actual mutable capture"
  let foreign ← match (← artifact.bootstrapFresh).resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "foreign bootstrap failed")
  match foreign.restoreSnapshot kept with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "snapshot transferred store/registry into a foreign session")
  match foreign.authenticate 1024 (.function .word .word) maker.value with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "restored handle changed its issuer")
  -- Empty native Unit bundles retain the open original source principal.
  let unused ← execute replayed.session (← key "unused") [word 21]
  let unusedAgain ← execute unused.session (← key "unused") [word 22]
  let unusedSnapshot ← get "unused generic principal snapshot" (← unusedAgain.session.snapshot)
  let principals := unusedSnapshot.cells.filterMap fun cell => match cell.value with
    | some (.principal principal) => some (cell, principal) | _ => none
  require (principals.length == 2) "unused Unit principals were dropped or treated as ground handles"
  let mut captures : List Nat := []
  for (cell, principal) in principals do
    require (!principal.scheme.quantified.isEmpty && cell.type == principal.type && principal.type != .unit)
      "generic principal lost its raw open type/scheme"
    match principal.observation.view with
    | .closure parameters _ _ environment _ =>
      require (parameters.length == 1 && environment.length == 1) "unused principal signature or capture order changed"
      let location ← match environment with
        | (_, location) :: _ => pure location
        | [] => throw (IO.userError "principal capture missing")
      require (location >= initialState.heap.length && location < cell.location) "principal capture bypassed source prefix offset"
      captures := captures ++ [location]
    | _ => throw (IO.userError "principal exposed a substituted view instead of original closure metadata")
  require (captures[0]? != captures[1]?) "reused binder ID confused captures from distinct invocations"
  let viewed ← execute unusedAgain.session (← key "views") [word 30]
  let viewsSnapshot ← get "used generic principal snapshot" (← viewed.session.snapshot)
  require (viewsSnapshot.cells.any fun cell => match cell.value with
    | some (.principal principal) => !principal.scheme.quantified.isEmpty | _ => false)
    "used generalized bundle lost principal metadata"
  let mapping : Value := .mapping (.comptime .word) (.proxy (.comptime .word)) [
    (word 1, .proxy (.comptime .word)), (word 1, .proxy (.comptime .word))]
  let echoed ← execute viewed.session (← key "echo") [mapping]
  let rawSnapshot ← get "native raw data snapshot" (← echoed.session.snapshot)
  require (rawSnapshot.cells.any fun cell => match cell.value with | some (.data value) => value == mapping | _ => false)
    "native cell snapshot changed raw mapping/proxy metadata or duplicate order"
  let start ← get "snapshot checkpoint" (echoed.session.start (← key "unused") [word 40])
  let suspended ← match ← start.resume 37 with
    | .outOfFuel checkpoint => pure checkpoint | _ => throw (IO.userError "expected real suspended allocation")
  let saved ← get "checkpoint heap snapshot" (← suspended.snapshot)
  require (saved.nativeHeapSize == suspended.heapSize) "checkpoint snapshot observed original session store"
  let resumed ← match saved.restore with
    | .suspended checkpoint => checkpoint.resume 300000
    | .ready _ => throw (IO.userError "snapshot dropped real native continuation")
  match resumed with
  | .succeeded completion => require (completion.value == word 40) "snapshot continuation resumed from wrong state"
  | _ => throw (IO.userError "snapshot continuation did not finish")
  match ← echoed.session.run (← key "failure") [word 50] 300000 with
  | .ok (.failed _ session) =>
    let faultSnapshot ← get "fault heap snapshot" (← session.snapshot)
    require (faultSnapshot.cells.any fun cell => match cell.value with | some (.data value) => value == word 52 | _ => false)
      "language-fault snapshot lost captured write"
    require (faultSnapshot.cells.any fun cell => cell.value.isNone && cell.location >= initialState.heap.length)
      "language-fault snapshot lost uninitialized source allocation"
  | _ => throw (IO.userError "failure fixture classification changed")
  match echoed.session.start (← key "sum") [word 1] 0 with
  | .error {code := .argumentCountMismatch 2 1, ..} => pure ()
  | _ => throw (IO.userError "root arity diagnostic lost original counts or ran encoding first")
  IO.println "opaque source heap/session snapshots GREEN"

end Tests.SourceCoreHeapSnapshot
