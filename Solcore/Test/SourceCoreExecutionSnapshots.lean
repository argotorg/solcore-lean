import Solcore.Frontend.SourceCompiler

#check_failure Solcore.Frontend.SourceCoreExecution.Snapshot.mk
#check_failure Solcore.Frontend.SourceCoreExecution.Snapshot.payload
#check_failure Solcore.Frontend.SourceCoreExecution.PrefixSnapshot.mk
#check_failure Solcore.Frontend.SourceCoreExecution.PrefixSnapshot.payload
#check_failure Solcore.Frontend.SourceCoreHeapSnapshot.ObservedValue.source
#check_failure Solcore.Frontend.SourceCoreHeapSnapshot.Principal.source

set_option autoImplicit false
namespace Tests.SourceCoreExecutionSnapshots
open Solcore Solcore.Frontend SourceCoreExecution

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def word (n : Nat) : Value := .word (Core.Word.ofNatModulo n)
private def boot {artifact : Artifact} (bootstrap : Bootstrap artifact) : IO (Session artifact) :=
  match bootstrap.resume 300000 with
  | .ready session => pure session
  | _ => throw (IO.userError "snapshot bootstrap did not finish")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (inputs : List Value) :
    IO (Completion artifact) := do
  match ← session.run key inputs {executionFuel := 300000} with
  | .ok (.succeeded completed) => pure completed
  | _ => throw (IO.userError "snapshot source invocation did not succeed")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function make(seed: Word) returns (Word) { let f: function(Word) returns (Word) = lam(step: Word) { seed += step; return seed; }; return seed; }",
    "function unused(seed: Word) returns (Word) { let f = lam(value) { return (value, seed); }; return seed; }",
    "function absent() returns (Word) { let missing: Word; return missing; }",
    "function spin() returns (Word) { while (true) {} return 0; }"
  ]}] }

example {artifact : Artifact} (snapshot : Snapshot artifact) :
    match snapshot.restore with
    | .ready session => session.heapSize = snapshot.nativeHeapSize
    | .suspended checkpoint => checkpoint.heapSize = snapshot.nativeHeapSize := snapshot.restore_native_size

example : SourceCompiler.Compiled = Compiled := rfl
example : SourceCompiler.Session = Session := rfl

def run : IO Unit := do
  let checked ← get "snapshot checking" (checkProgram workspace)
  let seeds ← ["make", "unused", "absent", "spin"].mapM fun name =>
    match checked.signatures.functions.filter (·.name == name) with
    | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
    | _ => throw (IO.userError "snapshot root missing")
  let compiled ← get "snapshot compilation" (compileChecked checked seeds
    {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "snapshot key missing")
  let artifact ← compiled.open
  let raw : SourceTypedRuntime.RuntimeState := {heap := [
    ⟨.error, none⟩, ⟨.word, some (.word (Core.Word.ofNatModulo 99))⟩]}
  let inert ← match Legacy.preparePrefix artifact raw with
    | some inert => pure inert | none => throw (IO.userError "snapshot valid inert prefix rejected")
  require (inert.heapSize == 2) "snapshot prefix lost a source cell"
  let initial ← boot (← artifact.bootstrapFromPrefix inert)
  let made ← execute initial (← key 0) [word 10]
  let snapshot ← get "public heap snapshot" (← made.session.snapshot)
  require (snapshot.prefixSize == 2 && snapshot.heapSize == 4 && snapshot.nativeHeapSize == made.session.heapSize)
    "public snapshot changed prefix/allocation counts"
  require (snapshot.cells.map (·.location) == [0, 1, 2, 3] && !snapshot.pendingAllocation)
    "public snapshot exposed administrative cells or changed source locations"
  let stored ← match snapshot.cellAt? 3 with
    | some {value := some (.data (.function handle)), ..} => pure handle
    | _ => throw (IO.userError "public snapshot did not export the stored callable")
  match made.session.startHandlePacked stored (word 1) with
  | .error {code := .unknownHandle, ..} => pure ()
  | _ => throw (IO.userError "snapshot-issued handle escaped its saved registry")
  let restored ← match snapshot.restore with
    | .ready session => pure session | _ => throw (IO.userError "ready snapshot became suspended")
  match ← restored.invokePacked stored (word 4) {executionFuel := 300000} with
  | .ok (.succeeded completion) => require (completion.value == word 14) "snapshot callable lost shared capture"
  | _ => throw (IO.userError "snapshot callable did not invoke")
  let foreign ← boot (← artifact.bootstrap)
  match foreign.restoreSnapshot snapshot with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "public snapshot transferred another session's ownership")
  let reused ← boot (← artifact.bootstrapFromPrefix snapshot.prefix)
  let generic ← execute reused (← key 1) [word 8]
  let genericSnapshot ← get "public principal snapshot" (← generic.session.snapshot)
  require (genericSnapshot.prefixSize == 2 && genericSnapshot.heapSize == 4)
    "public principal snapshot changed allocation count"
  match genericSnapshot.cellAt? 3 with
  | some {value := some (.principal principal), ..} =>
      require (!principal.scheme.quantified.isEmpty) "public principal snapshot erased its generic scheme"
      match principal.observation.view with
      | .closure _ _ _ captures _ => require (captures.map (·.2) == [2]) "public principal snapshot changed source capture"
      | _ => throw (IO.userError "public principal observation lost its closure metadata")
  | _ => throw (IO.userError "unused native Unit was not exposed as a readonly principal")
  let failed ← match ← generic.session.run (← key 2) [] {executionFuel := 300000} with
    | .ok (.failed reason session) =>
        match ← get "snapshot language diagnostic" (session.diagnostic (← key 2) reason) with
        | some {error := .uninitializedLocal _, ..} => pure session
        | _ => throw (IO.userError "snapshot fault classification changed")
    | _ => throw (IO.userError "snapshot uninitialized source cell did not fail")
  let failedSnapshot ← get "public failed heap snapshot" (← failed.snapshot)
  require (failedSnapshot.heapSize == 5 && (failedSnapshot.cellAt? 4).any (·.value.isNone))
    "public failed snapshot lost the allocated uninitialized cell"
  let spinning ← get "public snapshot spin" (failed.start (← key 3) [])
  let pending ← match ← spinning.resume 200 with
    | .outOfFuel checkpoint => pure checkpoint | _ => throw (IO.userError "snapshot spin terminated")
  let pendingSnapshot ← get "public suspended snapshot" (← pending.snapshot)
  require (pendingSnapshot.nativeHeapSize == pending.heapSize) "suspended snapshot lost native cells"
  match pendingSnapshot.restore with
  | .suspended checkpoint =>
      match ← checkpoint.resume 200 with
      | .outOfFuel _ => pure () | _ => throw (IO.userError "snapshot restored spin terminated")
  | .ready _ => throw (IO.userError "suspended snapshot lost its continuation")
  let empty ← get "empty snapshot compilation" (compileChecked checked [])
  let emptyArtifact ← empty.open
  let emptySession ← boot (← emptyArtifact.bootstrap)
  let emptySnapshot ← get "empty public snapshot" (← emptySession.snapshot)
  require (emptySnapshot.heapSize == 0 && emptySnapshot.nativeHeapSize == 0 && emptySnapshot.prefixSize == 0)
    "empty snapshot invented cells"
  let emptyAgain ← boot (← emptyArtifact.bootstrapFromPrefix emptySnapshot.prefix)
  require (emptyAgain.heapSize == 0) "empty prefix bootstrap invented native state"
  IO.println "common public snapshot, principal views, owned restore and suspended continuation GREEN"

end Tests.SourceCoreExecutionSnapshots
