import Solcore.Frontend.SourceCompilerSession

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.RuntimeValue
#check_failure Solcore.Frontend.SourceCompilerSession.Compiled.mk
#check_failure Solcore.Frontend.SourceCompilerSession.Compiled.recipe
#check_failure Solcore.Frontend.SourceCoreSession.Handle.mk

/-! Explicit roots share one checked catalog and cached ownership recipe.
These tests exercise native session reuse; importing an arbitrary pre-existing
source heap or source closure remains outside this boundary. -/

set_option autoImplicit false

namespace Tests.SourceCompilerSession

open Solcore Solcore.Frontend SourceCompilerSession
abbrev OwnedValue := SourceCoreSession.Value

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : OwnedValue := .word (Core.Word.ofNatModulo value)
private def functionType : TypeSystem.Ty := .function .word .word

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Holder { Put(function(Word) returns (Word)) }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function makeAdder(value: Word) returns (function(Word) returns (Word)) {",
    " return lam(delta: Word) -> Word { value = value + delta; return inc(value); }; }",
    "function use(f: function(Word) returns (Word), delta: Word) returns (Word) { return f(delta); }",
    "function mirror(f: function(Word) returns (Word)) returns (function(Word) returns (Word)) { return f; }",
    "function box(f: function(Word) returns (Word)) returns (Holder) { return .Put(f); }",
    "function unbox(value: Holder) returns (function(Word) returns (Word)) { match (value) { case .Put(f) { return f; } } }",
    "function keep<T>(value: T) returns (T) { return value; }"
  ] }] }

private def signature (program : CheckedProgram) (name : String) : IO ProgramFunctionSignature :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure signature
  | _ => throw (IO.userError s!"multi-root fixture function missing: {name}")

private def root (compiled : Compiled) (index : Nat) : IO Root :=
  match compiled.root? index with
  | some root => pure root
  | none => throw (IO.userError s!"multi-root metadata missing: {index}")

private def execute {artifact : SourceCoreSession.Artifact} (session : SourceCoreSession.Session artifact)
    (key : Key) (arguments : List OwnedValue) : IO (SourceCoreSession.Completion artifact) := do
  match ← session.run key arguments 65536 with
  | .ok (.succeeded completion) => pure completion
  | .error error => throw (IO.userError s!"multi-root session input rejected: {reprStr error}")
  | .ok (.exportError error _) => throw (IO.userError s!"multi-root result rejected: {reprStr error}")
  | _ => throw (IO.userError "multi-root session did not finish successfully")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"multi-root source rejected: {reprStr error}")
  let moduleId : Workspace.ModuleId ← match Workspace.CanonicalSourcePath.parse "main.solc" with
    | some canonical => pure { library := .main, path := canonical.modulePath }
    | none => throw (IO.userError "multi-root module identity failed")
  let use ← signature program "use"
  let seeds := [Seed.named moduleId "makeAdder", .declaration use.id, .named moduleId "mirror",
    .named moduleId "box", .named moduleId "unbox", .named moduleId "keep" [.word],
    .named moduleId "keep" [.bool], .named moduleId "use"]
  let options : Options := { specializationBudget := 256, compilationFuel := 256 }
  let compiled ← match compileChecked program seeds options with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError s!"multi-root preparation rejected: {reprStr error}")
  assertTrue (compiled.rootCount == seeds.length && compiled.keys.length == seeds.length)
    "explicit roots were deduplicated or reordered"
  assertTrue (compiled.root? seeds.length |>.isNone) "out-of-range root metadata was accepted"
  for (seed, index) in seeds.zipIdx do
    assertTrue (decide ((← root compiled index).seed = seed)) "public root order changed"
  let maker ← root compiled 0
  let consumer ← root compiled 1
  let mirror ← root compiled 2
  let box ← root compiled 3
  let unbox ← root compiled 4
  let keepWord ← root compiled 5
  let keepBool ← root compiled 6
  let duplicate ← root compiled 7
  assertTrue (consumer.key == duplicate.key) "named/declaration roots failed canonicalization"
  assertTrue (keepWord.key != keepBool.key) "distinct generic roots shared a specialization key"
  assertTrue (decide (maker.inputTypes = [.word] ∧ maker.resultType = functionType ∧
    consumer.inputTypes = [functionType, .word] ∧ consumer.resultType = .word ∧
    keepWord.inputTypes = [.word] ∧ keepBool.resultType = .bool))
    "ordered root metadata lost closed source signatures"
  assertTrue (compiled.signatures.functions.map (·.name) == program.signatures.functions.map (·.name))
    "cached facade lost its source signature catalog"
  assertTrue (compiled.checked.catalog.definitions.length > 0 &&
    compiled.dataContext.checked.catalog.definitions == compiled.checked.catalog.definitions)
    "all roots did not retain the actual nominal catalog"
  let rawCompiled ← match compile workspace seeds options with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError s!"raw multi-root checking failed: {reprStr error}")
  assertTrue (rawCompiled.keys == compiled.keys) "raw checking changed canonical roots"

  let artifact ← compiled.open
  assertTrue (artifact.keys == compiled.keys) "opening the cached recipe changed entry order"
  let session ← artifact.newSession
  let made ← execute session maker.key [word 10]
  let handle ← match made.value with
    | .function handle => pure handle
    | _ => throw (IO.userError "maker did not export an owned function")
  let first ← execute made.session consumer.key [.function handle, word 2]
  assertTrue (first.value == word 13) "another root lost the original globals or captured cell"
  let second ← execute first.session duplicate.key [.function handle, word 3]
  assertTrue (second.value == word 16 && second.session.heapSize > first.session.heapSize)
    "duplicate root execution lost shared mutation across world extension"
  let mirrored ← execute second.session mirror.key [.function handle]
  assertTrue (mirrored.value == .function handle) "another root re-exported a different function capability"
  let boxed ← execute mirrored.session box.key [.function handle]
  let unboxed ← execute boxed.session unbox.key [boxed.value]
  assertTrue (unboxed.value == .function handle) "nominal multi-root exchange changed the function identity"
  let keptWord ← execute unboxed.session keepWord.key [word 41]
  let keptBool ← execute keptWord.session keepBool.key [.bool true]
  assertTrue (keptWord.value == word 41 && keptBool.value == .bool true)
    "ground generic roots did not run in the shared catalog"
  let checkpoint ← match keptBool.session.start consumer.key [.function handle, word 4] with
    | .ok checkpoint => pure checkpoint
    | .error error => throw (IO.userError s!"multi-root checkpoint rejected: {reprStr error}")
  let next ← match ← checkpoint.resume 2 with
    | .outOfFuel next => pure next
    | _ => throw (IO.userError "multi-root checkpoint failed to suspend")
  match ← next.resume 65536 with
  | .succeeded completion => assertTrue (completion.value == word 20) "multi-root resume lost captured mutation"
  | _ => throw (IO.userError "multi-root checkpoint failed to finish")
  match session.authenticate 1024 functionType (.function handle) with
  | .error error => assertTrue (error.code == .unknownHandle) "pre-export session snapshot accepted the handle"
  | .ok _ => throw (IO.userError "unregistered handle entered an old session snapshot")
  let sibling ← artifact.newSession
  match sibling.authenticate 1024 functionType (.function handle) with
  | .error error => assertTrue (error.code == .foreignSession) "distinct sessions aliased ownership"
  | .ok _ => throw (IO.userError "another session accepted the function capability")
  let reopened ← compiled.open
  let foreign ← reopened.newSession
  match foreign.authenticate 1024 functionType (.function handle) with
  | .error error => assertTrue (error.code == .foreignArtifact) "cached reopening aliased artifact ownership"
  | .ok _ => throw (IO.userError "another opened artifact accepted the function capability")

  let missing := Seed.named moduleId "missing"
  match compileChecked program [maker.seed, missing] options with
  | .error (.seed 1 actual (.unknownName actualModule "missing")) =>
      assertTrue (decide (actual = missing ∧ actualModule = moduleId)) "seed failure lost selector metadata"
  | _ => throw (IO.userError "seed failure lost its caller index")
  match compileChecked program [.named moduleId "keep"] options with
  | .error (.seed 0 _ (.typeArgumentArityMismatch _ 1 0)) => pure ()
  | _ => throw (IO.userError "generic seed with wrong arity was accepted")
  match compileChecked program seeds { options with specializationBudget := 0 } with
  | .error (.specializationBudgetExhausted _ _) => pure ()
  | _ => throw (IO.userError "specialization exhaustion was hidden")
  let empty ← match compileChecked program [] options with
    | .ok empty => pure empty
    | .error error => throw (IO.userError s!"empty explicit root set failed: {reprStr error}")
  assertTrue (empty.rootCount == 0 && empty.keys.isEmpty) "empty root set gained an implicit main"
  let emptyArtifact ← empty.open
  let emptySession ← emptyArtifact.newSession
  match emptySession.start maker.key [word 10] with
  | .error error => assertTrue (error.code == .missingEntry maker.key) "missing cached entry error changed"
  | .ok _ => throw (IO.userError "empty artifact ran an uncompiled root")
  let invalid : Workspace.RawWorkspace := { workspace with
    mainSources := [{ path := "main.solc", content := "function broken() returns (Word) { return absent; }" }] }
  match compile invalid [] options with
  | .error (.checking _) => pure ()
  | _ => throw (IO.userError "raw facade bypassed source checking for an empty root list")
  IO.println "cached multi-root source compiler and shared owned handles GREEN"

end Tests.SourceCompilerSession
