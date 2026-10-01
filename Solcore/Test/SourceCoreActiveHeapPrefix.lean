import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Test.SourceCoreUnifiedCorpusSupport

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
