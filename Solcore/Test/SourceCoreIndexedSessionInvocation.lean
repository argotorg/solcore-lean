import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceCoreIndexedSession.Request
#check_failure Solcore.Frontend.SourceCoreIndexedSession.selectCallable
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Checkpoint.request
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Value.closure

set_option autoImplicit false
namespace Tests.SourceCoreIndexedSessionInvocation
open Solcore Solcore.Frontend SourceCoreIndexedSession
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α := SourceCoreUnifiedCorpusSupport.get label
private def require (condition : Bool) (message : String) : IO Unit := SourceCoreUnifiedCorpusSupport.assertTrue condition message
private def word (value : Nat) : Value := .word (Core.Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "function add(left: Word, right: Word) returns (Word) { return left + right; }",
  "function tuple(value: (Word, Word)) returns (Word) { return 33; }",
  "function zero() returns (Word) { return 4; }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(step: Word) { seed += step; return seed; }; }",
  "function twins(seed: Word) returns (function(Word) returns (Word), function(Word) returns (Word)) {",
  " let left = lam(step: Word) -> Word { seed += step; return seed; };",
  " let right = lam(step: Word) -> Word { seed += step; return seed; }; return (left, right); }",
  "function failurePair(seed: Word) returns (function(Word) returns (Word), function() returns (Word)) {",
  " let fails = lam(step: Word) -> Word { seed += step; let absent: Word; return absent; };",
  " let observes = lam() -> Word { return seed; }; return (fails, observes); }",
  "function spin() returns (function() returns (Word)) { return lam() -> Word { while (true) {} return 0; }; }",
  "function marked() returns (function(Word) returns (Word)) { return lam(comptime value: Word) -> Word { return value; }; }",
  "function markedGlobal(comptime value: Word) returns (Word) { return value; }",
  "function markedResult() returns (comptime<Word>) { return 5; }",
  "function stagedSource() returns (Word) { let f = markedGlobal; return f(21); }"
]
private def names : List String := ["add", "tuple", "zero", "make", "twins", "failurePair", "spin", "marked", "markedGlobal", "markedResult", "stagedSource"]
private def handle : Value → IO Handle
  | .function handle => pure handle
  | _ => throw (IO.userError "function export was not an opaque handle")
private def success {artifact : Artifact} (label : String) : Except Error (Outcome artifact) → IO (Completion artifact)
  | .ok (.succeeded completion) => pure completion
  | .ok (.failed reason _) => throw (IO.userError s!"{label}: language failure {reprStr reason}")
  | .ok (.exportError error _) => throw (IO.userError s!"{label}: export {reprStr error}")
  | .ok (.outOfFuel _) => throw (IO.userError s!"{label}: exhausted")
  | .error error => throw (IO.userError s!"{label}: rejected {reprStr error}")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (args : List Value) : IO (Completion artifact) := do
  success "cached source root" (← session.run key args 300000)
private def invoke {artifact : Artifact} (session : Session artifact) (value : Value) (argument : Value) : IO (Completion artifact) := do
  success "direct packed handle" (← session.invokePacked (← handle value) argument 300000)

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "direct packed invocation" content names
  let recipe ← get "direct recipe" (Recipe.prepare compiled)
  let artifact ← recipe.open
  let bootstrap ← artifact.bootstrapFresh
  let initial ← match bootstrap.resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "direct bootstrap failed")
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  let add ← get "two-parameter named handle" (← initial.named (← key "add"))
  let tuple ← get "tuple-parameter named handle" (← add.session.named (← key "tuple"))
  require (add.sourceType == tuple.sourceType) "fixture did not preserve the grouped source function type"
  let grouped : Value := .product (word 8) (word 9)
  let added ← invoke tuple.session add.value grouped
  require (added.value == word 17 && added.session.heapSize == tuple.session.heapSize + 6)
    "two scalar parameters lost values or source allocation count"
  let tupled ← invoke added.session tuple.value grouped
  require (tupled.value == word 33 && tupled.session.heapSize == added.session.heapSize + 3)
    "one tuple parameter was flattened into two parameter allocations"
  let zero ← get "zero-parameter named handle" (← tupled.session.named (← key "zero"))
  let zeroed ← invoke zero.session zero.value .unit
  require (zeroed.value == word 4 && zeroed.session.heapSize == zero.session.heapSize)
    "Unit parameter bundle added source parameter cells"
  let made ← execute zeroed.session (← key "make") [word 10]
  let first ← invoke made.session made.value (word 4)
  let next ← get "direct native checkpoint" (first.session.startHandlePacked (← handle made.value) (word 5))
  let saved ← match ← next.resume 0 with
    | .outOfFuel checkpoint => pure checkpoint | _ => throw (IO.userError "direct call did not preserve zero-fuel checkpoint")
  let progressed ← match ← saved.resume 37 with
    | .outOfFuel checkpoint => pure checkpoint | _ => throw (IO.userError "direct call did not preserve partial checkpoint")
  let resumed ← success "direct resume" (.ok (← progressed.resume 300000))
  require (first.value == word 14 && resumed.value == word 19 && resumed.session.installedGlobalsPresent)
    "direct closure mutation or native resume lost the retained world"
  let pair ← execute resumed.session (← key "twins") [word 30]
  let (left, right) ← match pair.value with
    | .product left right => pure (left, right) | _ => throw (IO.userError "shared direct closures missing")
  let leftCall ← invoke pair.session left (word 3)
  let rightCall ← invoke leftCall.session right (word 4)
  require (leftCall.value == word 33 && rightCall.value == word 37) "direct handles copied shared captures"
  let failedPair ← execute rightCall.session (← key "failurePair") [word 70]
  let (fails, observes) ← match failedPair.value with
    | .product fails observes => pure (fails, observes) | _ => throw (IO.userError "direct failure closures missing")
  let failsHandle ← handle fails
  let failureStart ← get "direct fault checkpoint" (failedPair.session.startHandlePacked failsHandle (word 4))
  let faulted ← match ← failureStart.resume 300000 with
    | .failed reason session =>
        let before ← get "direct checkpoint diagnostic" (failureStart.diagnostic reason)
        let after ← get "direct retained handle diagnostic" (session.handleDiagnostic failsHandle reason)
        require (decide (before = after)) "direct fault lost request origin or metadata"
        match after with
        | some {error := .uninitializedLocal _, span := some _, ..} => pure session
        | _ => throw (IO.userError "direct fault lost exact source read diagnostic")
    | _ => throw (IO.userError "direct fault changed classification")
  let observed ← invoke faulted observes .unit
  require (observed.value == word 74) "direct language failure rolled back captured writes"
  let builtin ← get "direct builtin" (← observed.session.builtin .integerAdd)
  let integer ← invoke builtin.session builtin.value (.product (.integer 900000000000000000000000000000000000) (.integer 7))
  require (integer.value == .integer 900000000000000000000000000000000007) "packed builtin lost native Integer arithmetic"
  let marked ← execute integer.session (← key "marked") []
  let markedGlobal ← get "marked named handle" (← marked.session.named (← key "markedGlobal"))
  let markedResult ← get "marked result handle" (← markedGlobal.session.named (← key "markedResult"))
  for function in [marked.value, markedGlobal.value, markedResult.value] do
    let before := markedResult.session.heapSize
    match markedResult.session.startHandlePacked (← handle function) (.proxy (.comptime .word)) 0 with
    | .error {code := .stagedInvocationRequired _, ..} => pure ()
    | _ => throw (IO.userError "direct host stage rejection did not precede invalid packed input")
    require (markedResult.session.heapSize == before) "staged host rejection mutated source/native cells"
  let staged ← execute markedResult.session (← key "stagedSource") []
  require (staged.value == word 21) "legitimate staged source call no longer executes through its compiled guard"
  let spinning ← execute staged.session (← key "spin") []
  let spinningHandle ← handle spinning.value
  let pending ← match ← spinning.session.invokePacked spinningHandle .unit 200 with
    | .ok (.outOfFuel checkpoint) => pure checkpoint | _ => throw (IO.userError "direct spin completed")
  match ← pending.resume 300 with
  | .outOfFuel _ => pure () | _ => throw (IO.userError "resumed direct spin completed")
  let foreignBootstrap ← artifact.bootstrapFresh
  let foreign ← match foreignBootstrap.resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "foreign direct bootstrap failed")
  match foreign.startHandlePacked spinningHandle .unit with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "direct invocation accepted a foreign session handle")
  IO.println "direct owned packed invocation, source arity, stage guards, shared writes and native resume GREEN"

end Tests.SourceCoreIndexedSessionInvocation
