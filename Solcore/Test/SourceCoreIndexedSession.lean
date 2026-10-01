import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Frontend.SourceCoreSession
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCorePublicValues.Handle.mk
#check_failure Solcore.Frontend.SourceCorePublicValues.Handle.artifact
#check_failure Solcore.Frontend.SourceCorePublicValues.Handle.slot
#check_failure Solcore.Frontend.SourceCorePublicValues.ArtifactAuthority.mk
#check_failure Solcore.Frontend.SourceCorePublicValues.SessionAuthority.artifact
#check_failure Solcore.Frontend.SourceCoreIndexedSession.register
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Session.store
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Checkpoint.state
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Value.closure
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Value.cellRef

set_option autoImplicit false
namespace Tests.SourceCoreIndexedSession
open Solcore Solcore.Frontend SourceCoreIndexedSession
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α := SourceCoreUnifiedCorpusSupport.get label
private def require (condition : Bool) (message : String) : IO Unit := SourceCoreUnifiedCorpusSupport.assertTrue condition message
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def word (n : Nat) : Value := .word (w n)
private def content : String := String.intercalate "\n" [
  "enum Holder { Put(function(Word) returns (Word)) }",
  "function inc(n: Word) returns (Word) { return n + 1; }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(step: Word) { seed += step; return inc(seed); }; }",
  "function use(f: function(Word) returns (Word), n: Word) returns (Word) { return f(n); }",
  "function twins(seed: Word) returns (function(Word) returns (Word), function(Word) returns (Word)) {",
  " let f: function(Word) returns (Word) = lam(step: Word) { seed += step; return seed; };",
  " let g: function(Word) returns (Word) = lam(step: Word) { seed += step; return seed; }; return (f, g); }",
  "function named() returns (function(Word) returns (Word)) { return inc; }",
  "function mirror(f: function(Word) returns (Word)) returns (function(Word) returns (Word)) { return f; }",
  "function boxed(f: function(Word) returns (Word)) returns (Holder) { return .Put(f); }",
  "function unbox(v: Holder) returns (function(Word) returns (Word)) { match (v) { case .Put(f) { return f; } } }",
  "function mapEcho(v: mapping(Word => function(Word) returns (Word))) returns (mapping(Word => function(Word) returns (Word))) { return v; }",
  "function mapGet(v: mapping(Word => function(Word) returns (Word)), k: Word) returns (function(Word) returns (Word)) { return v[k]; }",
  "function wordMap(v: mapping(Word => Word)) returns (mapping(Word => Word)) { return v; }",
  "function proxy(v: @Word) returns (@Word) { return v; }",
  "function failurePair(seed: Word) returns (function(Word) returns (Word), function() returns (Word)) {",
  " let f: function(Word) returns (Word) = lam(step: Word) { seed += step; let absent: Word; return absent; };",
  " let g: function() returns (Word) = lam() { return seed; }; return (f, g); }",
  "function get(f: function() returns (Word)) returns (Word) { return f(); }",
  "function spin() returns (Word) { while (true) {} return 0; }"
]
private def names : List String := ["inc", "make", "use", "twins", "named", "mirror", "boxed", "unbox", "mapEcho", "mapGet", "wordMap", "proxy", "failurePair", "get", "spin"]
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (args : List Value)
    (fuel : Nat := 300000) : IO (Completion artifact) := do
  match ← session.run key args fuel with
  | .ok (.succeeded result) => pure result
  | .ok (.exportError error _) => throw (IO.userError s!"session export: {reprStr error}")
  | .ok (.failed reason _) => throw (IO.userError s!"session language failure: {reprStr reason}")
  | .ok (.outOfFuel _) => throw (IO.userError "session exhausted")
  | .error error => throw (IO.userError s!"session rejected: {reprStr error}")

-- The certificate retains the private world's exact frame location.
example {artifact : Artifact} (session : Session artifact) := session.frame_location_zero
example {artifact : Artifact} (completion : Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value := completion.typed
example {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat) := checkpoint.native_safe fuel
example : SourceCoreSession.Value = SourceCorePublicValues.Value := rfl

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "persistent indexed session" content names
  let recipe ← get "session recipe" (Recipe.prepare compiled)
  let artifact ← recipe.open
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  let sentinel : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, none⟩]}
  let sourcePrefix ← match InertPrefix.prepare artifact sentinel 500 with
    | some accepted => pure accepted | none => throw (IO.userError "inert prefix rejected")
  let bootstrap ← artifact.bootstrap sourcePrefix
  let suspended ← match bootstrap.resume 1 with
    | .outOfFuel next => pure next | _ => throw (IO.userError "bootstrap did not suspend")
  let initial ← match suspended.resume 300000 with
    | .ready initial => pure initial
    | .error error => throw (IO.userError s!"bootstrap: {reprStr error}")
    | .outOfFuel _ => throw (IO.userError "bootstrap exhausted")
  require (initial.heapSize == compiled.indexed.base.globals.length + 1) "bootstrap installed unexpected source/input cells"
  require initial.installedGlobalsPresent "bootstrap did not authenticate globals"
  require (reprStr initial.inertPrefix == reprStr sentinel) "bootstrap imported/changed the inert source prefix"
  let made ← execute initial (← key "make") [word 10]
  let used ← execute made.session (← key "use") [made.value, word 2]
  require (used.value == word 13) "returned native capture/global call failed"
  let reused ← execute used.session (← key "use") [made.value, word 3]
  require (reused.value == word 16) "capture was copied instead of shared"
  require (reused.session.installedGlobalsPresent && reprStr reused.session.inertPrefix == reprStr sentinel) "later invocation replaced globals or prefix"
  let mirrored ← execute reused.session (← key "mirror") [made.value]
  require (mirrored.value == made.value && mirrored.session.functionCount == 1) "handle registry did not retain exact native closure"
  let pair ← execute mirrored.session (← key "twins") [word 20]
  let (left, right) ← match pair.value with
    | .product left right => pure (left, right) | _ => throw (IO.userError "twins did not return two handles")
  let first ← execute pair.session (← key "use") [left, word 2]
  let second ← execute first.session (← key "use") [right, word 3]
  require (first.value == word 22 && second.value == word 25) "two handles lost aliased capture"
  let box ← execute second.session (← key "boxed") [left]
  let unboxed ← execute box.session (← key "unbox") [box.value]
  require (unboxed.value == left) "nominal payload function did not preserve the handle"
  let functionType : TypeSystem.Ty := .function .word .word
  let rawMapping : Value := .mapping (.comptime .word) functionType [(word 1, left), (word 1, right)]
  let mapped ← execute unboxed.session (← key "mapEcho") [rawMapping]
  require (mapped.value == rawMapping) "mapping raw header, duplicate order or function leaves changed"
  let fromMap ← execute mapped.session (← key "mapGet") [mapped.value, word 1]
  require (fromMap.value == left) "ordered mapping selected wrong duplicate"
  let rawWords : Value := .mapping (.comptime .word) (.comptime .word) [(word 1, word 7), (word 1, word 9)]
  let echoed ← execute fromMap.session (← key "wordMap") [rawWords]
  require (echoed.value == rawWords) "raw mapping metadata/default was canonicalized"
  let proxy ← execute echoed.session (← key "proxy") [.proxy (.comptime .word)]
  require (proxy.value == .proxy (.comptime .word)) "raw proxy metadata was canonicalized"
  let named ← execute proxy.session (← key "named") []
  let called ← execute named.session (← key "use") [named.value, word 40]
  require (called.value == word 41) "owned global handle was not callable"
  let pending ← get "start captured call" (called.session.start (← key "use") [made.value, word 1])
  let next ← match ← pending.resume 37 with
    | .outOfFuel next => pure next | _ => throw (IO.userError "partial call did not suspend")
  let resumed ← match ← next.resume 300000 with
    | .succeeded result => pure result | _ => throw (IO.userError "native checkpoint did not complete")
  require (resumed.value == word 17 && resumed.session.installedGlobalsPresent) "resume lost capture/global authority"
  let branchedA ← execute initial (← key "make") [word 50]
  let branchedB ← execute initial (← key "make") [word 50]
  match branchedB.session.authenticate 1024 functionType branchedA.value with
  | .error {code := .unknownHandle, ..} => pure ()
  | _ => throw (IO.userError "branched export slot collision accepted")
  let freshBootstrap ← artifact.bootstrap sourcePrefix
  let fresh ← match freshBootstrap.resume 300000 with
    | .ready fresh => pure fresh | _ => throw (IO.userError "second bootstrap failed")
  match fresh.authenticate 1024 functionType made.value with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "foreign session accepted handle")
  let otherArtifact ← recipe.open
  let otherPrefix ← match InertPrefix.prepare otherArtifact {} 500 with
    | some accepted => pure accepted | none => throw (IO.userError "empty prefix rejected")
  let otherBootstrap ← otherArtifact.bootstrap otherPrefix
  let other ← match otherBootstrap.resume 300000 with
    | .ready other => pure other | _ => throw (IO.userError "foreign artifact bootstrap failed")
  match other.authenticate 1024 functionType made.value with
  | .error {code := .foreignArtifact, ..} => pure ()
  | _ => throw (IO.userError "foreign artifact accepted handle")
  let failedPair ← execute resumed.session (← key "failurePair") [word 70]
  let (fails, observes) ← match failedPair.value with
    | .product left right => pure (left, right) | _ => throw (IO.userError "failure pair missing")
  let afterFault ← match ← failedPair.session.run (← key "use") [fails, word 4] 300000 with
    | .ok (.failed _ session) => pure session | _ => throw (IO.userError "language failure changed category")
  let observed ← execute afterFault (← key "get") [observes]
  require (observed.value == word 74) "language fault rolled back shared mutation"
  let spinning ← get "spin" (observed.session.start (← key "spin") [])
  let spinningNext ← match ← spinning.resume 200 with
    | .outOfFuel next => pure next | _ => throw (IO.userError "spin completed")
  match ← spinningNext.resume 300 with
  | .outOfFuel _ => pure () | _ => throw (IO.userError "resumed spin completed")

end Tests.SourceCoreIndexedSession
