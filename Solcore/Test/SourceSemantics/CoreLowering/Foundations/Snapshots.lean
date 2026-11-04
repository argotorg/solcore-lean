import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.Frontend.SourceCompiler
import Solcore.Frontend.SourceCoreLegacyHeapImport

/-!
# Snapshot tests

Execution snapshots and active heap prefixes.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreActiveHeapPrefix
#check_failure Solcore.Frontend.SourceCoreIndexedSession.PrefixSnapshot.sourcePrefix
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Snapshot.saved
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false
namespace Tests.SourceCoreActiveHeapPrefix
open Solcore Solcore.Frontend SourceCoreIndexedSession
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α := SourceCoreUnifiedCorpusSupport.get label
private def require (condition : Bool) (message : String) : IO Unit := SourceCoreUnifiedCorpusSupport.assertTrue condition message
private def word (value : Nat) : Value := .word (Core.Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "trait Mark<T> {}", "impl Mark<Word> {}",
  "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
  "enum Holder { Hold(function(Word) returns (Word)) }",
  "function inc(n: Word) returns (Word) { return n + 1; }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { let f: function(Word) returns (Word) = lam(step: Word) { seed += step; return seed; }; return f; }",
  "function use(f: function(Word) returns (Word), n: Word) returns (Word) { return f(n); }",
  "function view(seed: Word) returns (function(Word) returns (Word)) { let f = lam(item) { seed += 1; return item; }; let g: function(Word) returns (Word) = f; return g; }",
  "function qualified(seed: Word) returns (function(Word) returns (Word)) { let f = lam(item) { seed += 1; return keep(item); }; let g: function(Word) returns (Word) = f; return g; }",
  "function history(seed: Word) returns (Word) { let shared = lam(item) { let probe: Word = 0; return item; }; let outer = lam(value) { keep(value); return shared(value); }; return outer(seed) + outer(seed); }",
  "function unused(captured: Word) returns (Word) { let unused = lam(item) { return (item, captured); }; return captured; }",
  "function tuple(value: (function(Word) returns (Word), Word)) returns ((function(Word) returns (Word), Word)) { return value; }",
  "function boxed(value: Holder) returns (Holder) { return value; }",
  "function table(value: mapping(Word => function(Word) returns (Word))) returns (mapping(Word => function(Word) returns (Word))) { return value; }",
  "function proxies(value: mapping(Word => @Word)) returns (mapping(Word => @Word)) { return value; }",
  "function builtin(value: function(Word) returns (integer)) returns (function(Word) returns (integer)) { return value; }",
  "function failure(seed: Word) returns (Word) { let f = lam() -> Word { seed += 2; let absent: Word; return absent; }; return f(); }",
  "function spin(seed: Word) returns (Word) { let f: function(Word) returns (Word) = lam(step: Word) { seed += step; return seed; }; while (true) { f(1); } return seed; }"
]
private def names : List String := ["inc", "make", "use", "view", "qualified", "history", "unused", "tuple", "boxed", "table", "proxies", "builtin", "failure", "spin"]
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (args : List Value) : IO (Completion artifact) := do
  match ← session.run key args 300000 with
  | .ok (.succeeded completion) => pure completion
  | .ok (.exportError error _) => throw (IO.userError s!"active export: {reprStr error}")
  | .error error => throw (IO.userError s!"active call: {reprStr error}")
  | _ => throw (IO.userError "active fixture did not finish")

private def bootstrap {artifact : Artifact} (snapshot : PrefixSnapshot artifact) : IO (Session artifact) := do
  match (← artifact.bootstrapFromPrefix snapshot).resume 300000 with
  | .ready session => pure session
  | _ => throw (IO.userError "active prefix did not bootstrap")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "active heap migration" content names
  let artifact ← (← get "active recipe" (Recipe.prepare compiled)).open
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  let rawInitial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩]}
  let initialPrefix ← match Legacy.preparePrefix artifact rawInitial 1024 with
    | some prefixSnapshot => pure prefixSnapshot | none => throw (IO.userError "active initial prefix rejected")
  let initial ← bootstrap initialPrefix
  let made ← execute initial (← key "make") [word 10]
  let changed ← execute made.session (← key "use") [made.value, word 3]
  require (changed.value == word 13) "capture fixture failed"
  let view ← execute changed.session (← key "view") [word 20]
  let qualified ← execute view.session (← key "qualified") [word 25]
  let history ← execute qualified.session (← key "history") [word 2]
  require (history.value == word 4) "paired caller/lexical fixture failed"
  let unused ← execute history.session (← key "unused") [word 30]
  let tuple ← execute unused.session (← key "tuple") [.product made.value (word 9)]
  -- Actual nominal constructor metadata is discovered once by the source
  -- program/catalog; no Core tag is accepted as a source constructor ID.
  let holder ← match compiled.sourceProgram.signatures.dataTypes.find? (·.name == "Holder") with
    | some holder => pure holder | none => throw (IO.userError "Holder signature missing")
  let constructor ← match holder.constructors.filter (·.name == "Hold") with
    | [constructor] => pure constructor | _ => throw (IO.userError "holder constructor missing")
  let metadata : SourceInference.DataConstructorInstantiation := {
    constructor := constructor.id, parameterSubstitution := [], payloadTypes := constructor.payloadTypes,
    resultType := .nominal holder.id [] }
  let boxed ← execute tuple.session (← key "boxed") [.constructed metadata [made.value]]
  let functionType : TypeSystem.Ty := .function .word .word
  let rawMapping : Value := .mapping (.comptime .word) (.comptime functionType) [(word 1, made.value), (word 1, view.value)]
  let mapped ← execute boxed.session (← key "table") [rawMapping]
  let rawProxy : Value := .mapping (.comptime .word) (.proxy (.comptime .word)) [(word 1, .proxy (.comptime .word)), (word 1, .proxy (.comptime .word))]
  let proxies ← execute mapped.session (← key "proxies") [rawProxy]
  let converted ← get "active builtin" (← proxies.session.builtin .wordToInteger)
  let builtin ← execute converted.session (← key "builtin") [converted.value]
  let before ← get "active observation" (← builtin.session.snapshot)
  let exported ← get "whole source heap prefix" (before.exportPrefix 1024 1024)
  require (exported.heapSize == before.heapSize && before.prefix.heapSize == 1)
    "whole export changed source heap size or initial-prefix API meaning"
  let closures := exported.cells.filterMap fun cell => match cell.value with
    | some (.legacy observation) => match observation.view with
      | .closure _ _ _ captures _ => some captures | _ => none
    | _ => none
  require (!closures.isEmpty) "whole export lost source lambda cells"
  for captures in closures do
    require (captures.all fun (_, location) => location < exported.heapSize)
      "whole export emitted a native location rather than a source capture"
  require (exported.cells.any fun cell => match cell.value with
    | some (.legacy observation) => match observation.view with | .instantiated .. => true | _ => false
    | _ => false) "whole export erased generalized read wrappers"
  require (exported.cells.any fun cell => match cell.value with
    | some (.legacy observation) => match observation.view with
      | .instantiated _ requirements _ => !requirements.isEmpty
      | _ => false
    | _ => false) "whole export erased own qualified-read witnesses"
  require (exported.cells.any fun cell => match cell.value with
    | some (.legacy observation) => match observation.view with
      | .mapping (.comptime _) (.comptime _) entries => entries.length == 2
      | _ => false
    | _ => false) "whole export changed ordered raw function mapping"
  require (exported.cells.any fun cell => match cell.value with
    | some (.legacy observation) => match observation.view with | .constructed _ [_] => true | _ => false
    | _ => false) "whole export lost nominal callable payload"
  let imported ← bootstrap exported
  require (imported.heapSize == initial.heapSize && imported.installedGlobalsPresent)
    "whole source prefix was imported into the active native world"
  let reimportedView ← get "whole reimport observation" (← imported.snapshot)
  require (reimportedView.heapSize == exported.heapSize && reimportedView.prefixSize == exported.heapSize)
    "rebootstrap changed inert source offsets"
  let next ← execute imported (← key "unused") [word 40]
  let after ← get "post-reimport source observation" (← next.session.snapshot)
  require (after.cells.drop exported.heapSize |>.any fun cell => match cell.value with
    | some (.principal principal) => match principal.observation.view with
      | .closure _ _ _ captures _ => captures.any fun (_, location) => location >= exported.heapSize && location < cell.location
      | _ => false
    | _ => false) "new native source captures ignored the reimported prefix offset"
  match imported.authenticate 1024 functionType made.value with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "inert export moved native handle ownership")
  let reexported ← get "repeat whole prefix export" (after.exportPrefix 1024 1024)
  require (reexported.heapSize == after.heapSize) "second generation prefix export lost source cells"
  match ← builtin.session.run (← key "failure") [word 50] 300000 with
  | .ok (.failed _ session) =>
    let fault ← get "fault source view" (← session.snapshot)
    let faultPrefix ← get "fault whole prefix" (fault.exportPrefix 1024 1024)
    require (faultPrefix.cells.any fun cell => match cell.value with
      | some (.legacy observation) => match observation.view with | .word value => value == Core.Word.ofNatModulo 52 | _ => false
      | _ => false) "whole fault export lost captured write"
    discard <| bootstrap faultPrefix
  | _ => throw (IO.userError "whole fault fixture changed classification")
  let spin ← get "active spin start" (builtin.session.start (← key "spin") [word 60])
  let suspended ← match ← spin.resume 250 with
    | .outOfFuel checkpoint => pure checkpoint | _ => throw (IO.userError "spin completed")
  let partialView ← get "partial whole source view" (← suspended.snapshot)
  let partialPrefix ← get "partial whole prefix" (partialView.exportPrefix 1024 1024)
  discard <| bootstrap partialPrefix
  IO.println "whole active source heap to opaque inert prefix GREEN"

end Tests.SourceCoreActiveHeapPrefix
end

section
-- leanmerge: from Solcore.Test.SourceCoreExecutionSnapshots
#check_failure Solcore.Frontend.SourceCoreExecution.Snapshot.mk
#check_failure Solcore.Frontend.SourceCoreExecution.Snapshot.payload
#check_failure Solcore.Frontend.SourceCoreExecution.PrefixSnapshot.mk
#check_failure Solcore.Frontend.SourceCoreExecution.PrefixSnapshot.payload
#check_failure Solcore.Frontend.SourceCoreHeapSnapshot.ObservedValue.source
#check_failure Solcore.Frontend.SourceCoreHeapSnapshot.Principal.source
#check_failure Solcore.Frontend.SourceCompiler.Legacy.preparePrefix
#check_failure Solcore.Frontend.SourceCoreExecution.Legacy.preparePrefix

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

example {artifact : Artifact} {snapshot : Snapshot artifact} {exported : PrefixSnapshot artifact}
    {validationFuel boundaryFuel : Nat}
    (accepted : snapshot.exportPrefix validationFuel boundaryFuel = .ok exported) :
    exported.heapSize = snapshot.heapSize := snapshot.exportPrefix_length accepted

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
  let legacy ← match SourceCoreLegacyHeapImport.preparePrefix artifact raw with
    | some inert => pure inert | none => throw (IO.userError "snapshot valid inert prefix rejected")
  let inert ← get "common initial heap input" (artifact.preparePrefix [
    ⟨.error, none⟩, ⟨.word, some (word 99)⟩])
  require (legacy.cells.map (·.type) == inert.cells.map (·.type))
    "common heap input changed historical raw cell types"
  match artifact.preparePrefix [⟨.word, some (.bool true)⟩] with
  | .error {code := .validationRejected 1024, ..} => pure ()
  | _ => throw (IO.userError "common heap input accepted a forged cell payload")
  match artifact.preparePrefix [⟨.product .word .word, some (.product (word 1) (word 2))⟩] 1024 1 with
  | .error {path := [.cell 0, .left], code := .conversionFuelExhausted} => pure ()
  | _ => throw (IO.userError "common heap input lost conversion budget or path")
  require (inert.heapSize == 2) "snapshot prefix lost a source cell"
  let initial ← boot (← artifact.bootstrapFromPrefix inert)
  let made ← execute initial (← key 0) [word 10]
  let snapshot ← get "public heap snapshot" (← made.session.snapshot)
  require (snapshot.prefixSize == 2 && snapshot.heapSize == 5 && snapshot.nativeHeapSize == made.session.heapSize)
    "public snapshot changed prefix/allocation counts"
  require (snapshot.cells.map (·.location) == [0, 1, 2, 3, 4] && !snapshot.pendingAllocation)
    "public snapshot exposed administrative cells or changed source locations"
  let stored ← match snapshot.cellAt? 4 with
    | some {value := some (.data (.function handle)), ..} => pure handle
    | _ => throw (IO.userError "public snapshot did not export the stored callable")
  match artifact.preparePrefix [⟨stored.sourceType, some (.function stored)⟩] with
  | .error {path := [.cell 0], code := .callableRequiresSnapshot} => pure ()
  | _ => throw (IO.userError "common initial heap imported an unjoined callable handle")
  match made.session.startHandlePacked stored (word 1) with
  | .error {code := .unknownHandle, ..} => pure ()
  | _ => throw (IO.userError "snapshot-issued handle escaped its saved registry")
  let restored ← match snapshot.restore with
    | .ready session => pure session | _ => throw (IO.userError "ready snapshot became suspended")
  match ← restored.invokePacked stored (word 4) {executionFuel := 300000} with
  | .ok (.succeeded completion) => require (completion.value == word 14) "snapshot callable lost its captured value"
  | _ => throw (IO.userError "snapshot callable did not invoke")
  let foreign ← boot (← artifact.bootstrap)
  match foreign.restoreSnapshot snapshot with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "public snapshot transferred another session's ownership")
  let reused ← boot (← artifact.bootstrapFromPrefix snapshot.prefix)
  let completePrefix ← get "public full heap export" snapshot.exportPrefix
  require (completePrefix.heapSize == snapshot.heapSize) "public heap export lost source cells"
  match (completePrefix.cells[4]? : Option SourceCoreHeapSnapshot.Cell) with
  | some {value := some (.legacy observed), ..} =>
      match observed.view with
      | .closure _ _ _ captures _ => require (captures.map (·.2) == [3]) "public heap export changed raw captures"
      | _ => throw (IO.userError "public exported prefix lost callable metadata")
  | _ => throw (IO.userError "public exported prefix did not retain an inert callable")
  let migrated ← boot (← artifact.bootstrapFromPrefix completePrefix)
  match migrated.startHandlePacked stored (word 1) with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "public prefix export transferred live handle ownership")
  let migratedMade ← execute migrated (← key 0) [word 20]
  let migratedSnapshot ← get "public full prefix reuse" (← migratedMade.session.snapshot)
  require (migratedSnapshot.prefixSize == 5 && migratedSnapshot.heapSize == 8)
    "public full heap reuse lost prefix or allocation offsets"
  let generic ← execute reused (← key 1) [word 8]
  let genericSnapshot ← get "public principal snapshot" (← generic.session.snapshot)
  require (genericSnapshot.prefixSize == 2 && genericSnapshot.heapSize == 5)
    "public principal snapshot changed allocation count"
  match genericSnapshot.cellAt? 4 with
  | some {value := some (.principal principal), ..} =>
      require (!principal.scheme.quantified.isEmpty) "public principal snapshot erased its generic scheme"
      match principal.observation.view with
      | .closure _ _ _ captures _ => require (captures.map (·.2) == [3]) "public principal snapshot changed source capture"
      | _ => throw (IO.userError "public principal observation lost its closure metadata")
  | _ => throw (IO.userError "unused native Unit was not exposed as a readonly principal")
  let failed ← match ← generic.session.run (← key 2) [] {executionFuel := 300000} with
    | .ok (.failed reason session) =>
        match ← get "snapshot language diagnostic" (session.diagnostic (← key 2) reason) with
        | some {error := .uninitializedLocal _, ..} => pure session
        | _ => throw (IO.userError "snapshot fault classification changed")
    | _ => throw (IO.userError "snapshot uninitialized source cell did not fail")
  let failedSnapshot ← get "public failed heap snapshot" (← failed.snapshot)
  require (failedSnapshot.heapSize == 6 && (failedSnapshot.cellAt? 5).any (·.value.isNone))
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
  let emptyInput ← get "empty common initial heap" (emptyArtifact.preparePrefix [])
  require (emptyInput.heapSize == 0) "empty initial heap invented source cells"
  match emptyArtifact.preparePrefix [⟨.word, none⟩] with
  | .error {code := .emptyArtifactHeap 1, ..} => pure ()
  | _ => throw (IO.userError "empty artifact erased a nonempty initial heap")
  IO.println "common public snapshot, principal views, owned restore and suspended continuation GREEN"

end Tests.SourceCoreExecutionSnapshots
end
