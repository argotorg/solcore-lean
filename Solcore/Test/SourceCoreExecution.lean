import Solcore.Frontend.SourceCoreExecution

#check_failure Solcore.Frontend.SourceCoreExecution.Options.backendPreference
#check_failure Solcore.Frontend.SourceCoreExecution.Compiled.mk
#check_failure Solcore.Frontend.SourceCoreExecution.Artifact.mk
#check_failure Solcore.Frontend.SourceCoreExecution.Session.payload
#check_failure Solcore.Frontend.SourceCoreExecution.Checkpoint.payload
#check_failure Solcore.Frontend.SourceCoreExecution.Value.closure
#check_failure Solcore.Frontend.SourceCoreExecution.Value.cellRef
#check_failure Solcore.Frontend.SourceCoreExecution.Authentication.mk

/-! The same public value, artifact, session and checkpoint types execute data,
recursive calls and returned native functions. The empty compilation has no
callable code. All setup is cached before opening an ownership domain. -/
set_option autoImplicit false
namespace Tests.SourceCoreExecution
open Solcore Solcore.Frontend SourceCoreExecution

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def word (n : Nat) : Value := .word (Core.Word.ofNatModulo n)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(step: Word) { seed += step; return seed; }; }",
    "function use(f: function(Word) returns (Word), step: Word) returns (Word) { return f(step); }",
    "function recurse(n: Word) returns (Word) { return n == 0 ? 31 : recurse(n - 1); }",
    "function local(flag: Bool) returns (Word, Bool) { let id = lam(value) { return value; }; return (id(7), id(flag)); }",
    "function mappingEcho(value: mapping(Word => Word)) returns (mapping(Word => Word)) { return value; }",
    "function spin() returns (Word) { while (true) {} return 0; }",
    "function main() returns (Word) { return 55; }",
    "function uninitialized() returns (Word) { let absent: Word; return absent; }",
    "export {recurse};"
  ]}] }
private def seed (program : CheckedProgram) (name : String) : IO Seed :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
  | _ => throw (IO.userError s!"single public execution fixture missing {name}")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value) :
    IO (Completion artifact) := do
  match ← session.run key arguments {executionFuel := 300000} with
  | .ok (.succeeded result) => pure result
  | .ok (.exportError error _) => throw (IO.userError s!"public export: {reprStr error}")
  | .ok (.failed reason _) => throw (IO.userError s!"public language failure: {reprStr reason}")
  | .ok (.outOfFuel _) => throw (IO.userError "public execution exhausted")
  | .error error => throw (IO.userError s!"public invocation: {reprStr error}")
private def boot (artifact : Artifact) : IO (Session artifact) := do
  let bootstrap ← artifact.bootstrap
  match bootstrap.resume 300000 with
  | .ready session => pure session
  | .error error => throw (IO.userError s!"public bootstrap: {reprStr error}")
  | .outOfFuel _ => throw (IO.userError "public bootstrap exhausted")

example (compiled : Compiled) :
    SourceCompilationPlan.validateExecutablePlanEvidence compiled.program compiled.plan = .ok () := compiled.plan_validated
example {raw : Workspace.RawWorkspace} {seeds : List Seed} {options : Options} {compiled : Compiled}
    (accepted : compile raw seeds options = .ok compiled) :
    checkProgram raw options.checkingFuel = .ok compiled.program := compile_checked_source accepted
example {artifact : Artifact} (completion : Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value := completion.typed
example {raw : Workspace.RawWorkspace} {options : Options} {compiled : Compiled}
    (accepted : compileEntry raw options = .ok compiled) :
    checkProgram raw options.checkingFuel = .ok compiled.program := compileEntry_checked_source accepted
example {raw : Workspace.RawWorkspace} {options : Options} {compiled : StaticWordProgram}
    (accepted : compileStaticWord raw options = .ok compiled) :
    checkProgram raw options.checkingFuel = .ok compiled.compiled.program := compileStaticWord_checked_source accepted

def run : IO Unit := do
  let program ← get "public check" (checkProgram workspace)
  let seeds ← ["make", "use", "recurse", "local", "mappingEcho", "spin", "make", "uninitialized"].mapM (seed program)
  let options : Options := {specializationBudget := 256, compilationFuel := 1000}
  let compiled ← get "public single compilation" (compile workspace seeds options)
  require (compiled.rootCount == 8 && compiled.keys[0]? == compiled.keys[6]?) "public roots lost duplicate ordering"
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "public root missing")
  let artifact ← compiled.open
  let bootstrap ← artifact.bootstrap
  let pending ← match bootstrap.resume 1 with
    | .outOfFuel pending => pure pending | _ => throw (IO.userError "public bootstrap did not suspend")
  let initial ← match pending.resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "public bootstrap resume failed")
  require (artifact.rootCount == 8 && initial.functionCount == 0) "public artifact initialization changed roots/handles"
  let made ← execute initial (← key 0) [word 10]
  let first ← execute made.session (← key 1) [made.value, word 2]
  let second ← execute first.session (← key 1) [made.value, word 3]
  require (first.value == word 12 && second.value == word 15) "public session lost shared capture"
  require (initial.heapSize < made.session.heapSize && made.session.heapSize < second.session.heapSize) "public session replaced its native heap"
  let recursive ← execute second.session (← key 2) [word 5]
  require (recursive.value == word 31) "public recursive result changed"
  let localResult ← execute recursive.session (← key 3) [.bool true]
  require (localResult.value == .product (word 7) (.bool true)) "public local specialization changed"
  let raw : Value := .mapping (.comptime .word) (.comptime .word) [(word 1, word 7), (word 1, word 9)]
  let mapped ← execute localResult.session (← key 4) [raw]
  require (mapped.value == raw) "public value lost raw mapping metadata or duplicate order"
  let started ← get "public call start" (mapped.session.start (← key 1) [made.value, word 4])
  let checkpoint ← match ← started.resume 1 with
    | .outOfFuel checkpoint => pure checkpoint | _ => throw (IO.userError "public call did not suspend")
  let resumed ← match ← checkpoint.resume 300000 with
    | .succeeded result => pure result | _ => throw (IO.userError "public call did not resume")
  require (resumed.value == word 19) "public checkpoint lost capture"
  let named ← get "public named handle" (← resumed.session.named (← key 2))
  let namedResult ← execute named.session (← key 1) [named.value, word 4]
  require (namedResult.value == word 31) "public named handle lost cached code"
  let builtin ← get "public builtin handle" (← namedResult.session.builtin .wordToInteger)
  discard <| get "public builtin authentication"
    (builtin.session.authenticate 1024 (.function .word .integer) builtin.value)
  let afterFault ← match ← builtin.session.run (← key 7) [] {executionFuel := 300000} with
    | .ok (.failed reason session) =>
        match ← get "public language diagnostic" (session.diagnostic (← key 7) reason) with
        | some {error := .uninitializedLocal _, span := some _, ..} => pure session
        | _ => throw (IO.userError "public failure lost classification/site/span")
    | _ => throw (IO.userError "public uninitialized read changed outcome")
  let other ← compiled.open
  let foreign ← boot other
  match ← foreign.run (← key 1) [made.value, word 1] {executionFuel := 300000} with
  | .error {code := .foreignArtifact, ..} => pure ()
  | _ => throw (IO.userError "public boundary accepted foreign handle")
  let spinning ← get "public spin start" (afterFault.start (← key 5) [])
  let spinning ← match ← spinning.resume 200 with
    | .outOfFuel next => pure next | _ => throw (IO.userError "public spin completed")
  match ← spinning.resume 300 with
  | .outOfFuel _ => pure () | _ => throw (IO.userError "public resumed spin completed")
  let empty ← get "public empty compilation" (compileChecked program [] options)
  let emptyArtifact ← empty.open
  let emptySession ← boot emptyArtifact
  require (emptyArtifact.rootCount == 0 && emptySession.heapSize == 0) "empty public artifact invented callable state"
  match ← emptySession.run (← key 0) [] with
  | .error {code := .missingEntry _, ..} => pure ()
  | _ => throw (IO.userError "empty public session accepted a call")
  let mainCompiled ← get "public conventional main" (compileEntry workspace options)
  require (mainCompiled.rootCount == 1) "public main gained another root"
  let mainArtifact ← mainCompiled.open
  let mainSession ← boot mainArtifact
  let mainKey ← match mainCompiled.keys.head? with
    | some key => pure key | none => throw (IO.userError "public main missing")
  let mainResult ← execute mainSession mainKey []
  require (mainResult.value == word 55) "public conventional main changed result"
  let abi ← get "public Static Word compilation" (compileStaticWord workspace options)
  let abiRoot ← match abi.roots with
    | [root] => pure root | _ => throw (IO.userError "public ABI changed exported root set")
  require (abi.count == 1 && abiRoot.metadata.name.text == "recurse" &&
    (abi.rootForSelector? abiRoot.metadata.selector).isSome) "public ABI lost selector metadata"
  let abiArtifact ← abi.compiled.open
  let abiSession ← boot abiArtifact
  let abiResult ← execute abiSession abiRoot.root.key [word 3]
  require (abiResult.value == word 31) "public ABI root changed execution"

end Tests.SourceCoreExecution
