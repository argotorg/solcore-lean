import Solcore.Frontend.SourceCompiler

/-! Public compiler routing uses the actual cached catalog. The owned-session
fixture passes a returned function back through a nominal command and retains
its captured mutable cell and old globals across later entry invocations. -/

set_option autoImplicit false

namespace Tests.SourceCompilerCoreGeneral

open Solcore Solcore.Frontend SourceCompiler
abbrev DataValue := SourceCoreDataValues.Value
abbrev OwnedValue := SourceCoreSession.Value

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def scalar (value : Nat) : Core.Value := .word (word value)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree { Leaf(Word), Pair(Tree, Tree) }",
    "enum Command { Create(Word), Invoke(function(Word) returns (Word), Word) }",
    "enum Reply { Made(function(Word) returns (Word)), Result(Word) }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function main(value: Word) returns (Tree) { return .Leaf(inc(value)); }",
    "function echo(value: Tree) returns (Tree) { return value; }",
    "function recurse(count: Word, value: Tree) returns (Tree) { return count == 0 ? value : recurse(count - 1, Tree.Pair(value, value)); }",
    "function mappingValue(table: mapping(Word => Word)) returns (mapping(Word => Word)) { table[7] += 3; return table; }",
    "function missing(table: mapping(Word => Tree), key: Word) returns (Tree) { return table[key]; }",
    "function absent() returns (Tree) { let value: Tree; return value; }",
    "function proxyValue() returns (@Tree) { return @Tree; }",
    "function makeAdder(value: Word) returns (function(Word) returns (Word)) { return lam(delta: Word) -> Word { value = value + delta; return inc(value); }; }",
    "function step(command: Command) returns (Reply) { match (command) {",
    " case .Create(value) { return .Made(lam(delta: Word) -> Word { value = value + delta; return inc(value); }); }",
    " case .Invoke(f, delta) { return .Result(f(delta)); } } }"
  ] }] }

private def compile (program : CheckedProgram) (name : String) (preference : BackendPreference) : IO CompiledEntry := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"public general fixture missing: {name}")
  match compileChecked program (.declaration signature.id [])
      { backendPreference := preference, stagingFuel := 256, specializationBudget := 256 } with
  | .ok compiled =>
      assertTrue (compiled.backend == .core) s!"{name}: public compiler did not select Core"
      pure compiled
  | .error error => throw (IO.userError s!"{name}: public general compilation rejected: {reprStr error}")

private def context (compiled : CompiledEntry) : IO SourceCoreDataValues.Context :=
  match compiled.coreDataContext? with
  | some context => pure context
  | none => throw (IO.userError "public general artifact lost its actual catalog")

private def encoded (context : SourceCoreDataValues.Context) (type : TypeSystem.Ty) (value : DataValue) : IO Core.Value :=
  match SourceCoreDataValues.encode 256 context type value with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"public general data input rejected: {reprStr error}")

private def runData (compiled : CompiledEntry) (arguments : List Core.Value) : IO DataValue := do
  match compiled.runCore arguments { executionFuel := 65536 } with
  | .ok (.coreLanguageResult (.succeeded value _)) =>
      match SourceCoreDataValues.decode 256 (← context compiled) compiled.resultType value with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"public general result projection failed: {reprStr error}")
  | other => throw (IO.userError s!"public general run failed: {reprStr other}")

private def metadata (program : CheckedProgram) (name : String) (index : Nat) : IO SourceInference.DataConstructorInstantiation := do
  let signature ← match program.signatures.dataTypes.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"public general data signature missing: {name}")
  let constructor ← match signature.constructors[index]? with
    | some constructor => pure constructor
    | none => throw (IO.userError "public general constructor missing")
  pure ⟨constructor.id, [], constructor.payloadTypes, .nominal signature.id []⟩

private def ownedRun {artifact : SourceCoreSession.Artifact} (session : SourceCoreSession.Session artifact)
    (key : SourceCoreSession.Key) (argument : OwnedValue) : IO (SourceCoreSession.Completion artifact) := do
  match ← session.run key [argument] 65536 with
  | .ok (.succeeded completion) => pure completion
  | .error error => throw (IO.userError s!"public owned input rejected: {reprStr error}")
  | .ok (.exportError error _) => throw (IO.userError s!"public owned result rejected: {reprStr error}")
  | _ => throw (IO.userError "public owned function invocation failed")

example (program : CheckedProgram) (seed : Seed) (options : CompileOptions) (compiled : CompiledEntry)
    (accepted : compileChecked program seed options = .ok compiled) : compiled.HasPublicResultProjection :=
  compileChecked_hasPublicResultProjection program seed options compiled accepted
example (compiled : CompiledEntry) (arguments : List Core.Value) (store : Core.Store) (options : RunOptions)
    (observation : Core.LanguageResult.Observation) (projection : compiled.HasPublicResultProjection)
    (ran : compiled.run (.coreValues arguments store) options = .ok (.coreLanguageResult observation)) :
    compiled.CoreLanguageResultHasPublicType observation :=
  compiled.run_coreLanguageResult_has_public_resultType arguments store options observation projection ran

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"public general source rejected: {reprStr error}")
  let leafMetadata ← metadata program "Tree" 0
  let pairMetadata ← metadata program "Tree" 1
  let leaf := fun value => SourceCoreDataValues.Value.constructed leafMetadata [.word (word value)]
  let pair := fun left right => SourceCoreDataValues.Value.constructed pairMetadata [left, right]
  for preference in [BackendPreference.automatic, .core] do
    let main ← compile program "main" preference
    assertTrue ((← context main).checked.catalog.definitions.length > 0) "nominal public typing used an empty data environment"
    for _ in [0, 1] do
      assertTrue ((← runData main [scalar 8]) == leaf 9) "cached nominal public run changed"
    let echo ← compile program "echo" preference
    let tree := pair (leaf 3) (pair (leaf 4) (leaf 5))
    let input ← encoded (← context echo) leafMetadata.resultType tree
    assertTrue ((← runData echo [input]) == tree) "deep nominal public input/result changed"
    match echo.runCore [.constructed ⟨⟨999⟩, 0⟩ .unit] { executionFuel := 65536 } with
    | .error (.coreGeneralInput (.input _ _)) => pure ()
    | _ => throw (IO.userError "public general raw input accepted an unknown nominal identity")
    match main.runCore [scalar 8] { executionFuel := 65536 } [.unit] with
    | .error (.coreGeneralInput (.initialStoreUnsupported 1)) => pure ()
    | _ => throw (IO.userError "fresh raw public API accepted an unowned initial heap")
    let recursive ← compile program "recurse" preference
    let input ← encoded (← context recursive) leafMetadata.resultType (leaf 2)
    assertTrue ((← runData recursive [scalar 2, input]) == pair (pair (leaf 2) (leaf 2)) (pair (leaf 2) (leaf 2)))
      "public recursive Core execution changed"
    let mapping ← compile program "mappingValue" preference
    let entries := [(SourceCoreDataValues.Value.word (word 7), .word (word 4)), (.word (word 7), .word (word 99)), (.word (word 2), .word (word 6))]
    let input ← encoded (← context mapping) (.mapping .word .word) (.mapping .word .word entries)
    assertTrue ((← runData mapping [input]) == .mapping .word .word
      [(.word (word 7), .word (word 7)), (.word (word 7), .word (word 99)), (.word (word 2), .word (word 6))])
      "public mapping duplicate order or latest write changed"
    let proxy ← compile program "proxyValue" preference
    assertTrue ((← runData proxy []) == .proxy leafMetadata.resultType) "public proxy lost raw inner identity"
    let function ← compile program "makeAdder" preference
    match function.runCore [scalar 10] { executionFuel := 65536 } with
    | .ok (.coreLanguageResult (.succeeded (.pair (.inLeft .word .unit) (.closure ..)) _)) => pure ()
    | other => throw (IO.userError s!"public function-returning Core result changed: {reprStr other}")
    for name in ["missing", "absent"] do
      let failed ← compile program name preference
      let arguments ← if name == "missing" then do
        let empty ← encoded (← context failed) (.mapping .word leafMetadata.resultType) (.mapping .word leafMetadata.resultType [])
        pure [empty, scalar 7]
      else pure []
      match failed.runCore arguments { executionFuel := 65536 } with
      | .ok (.coreLanguageResult (.failed reason _)) =>
          match failed.coreFailureDiagnostic? reason with
          | some diagnostic =>
              assertTrue diagnostic.span.isSome "public general failure lost occurrence span"
              if name == "missing" then
                assertTrue (decide (diagnostic.error = .typeMismatch leafMetadata.resultType none))
                  "public absent mapping default changed its source error"
          | none => throw (IO.userError "public general language failure lost its diagnostic")
      | other => throw (IO.userError s!"public general language failure changed: {reprStr other}")

  let conventional ← match compileEntry workspace { backendPreference := .core, stagingFuel := 256 } with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError s!"conventional general entry rejected: {reprStr error}")
  assertTrue (conventional.backend == .core && (← runData conventional [scalar 4]) == leaf 5)
    "raw compileEntry did not use the public general Core branch"

  let step ← compile program "step" .automatic
  let artifact ← match ← step.openCoreArtifact? with
    | some artifact => pure artifact
    | none => throw (IO.userError "public compiler did not expose its cached owned recipe")
  assertTrue (artifact.keys == [step.key]) "public cached owned root key changed"
  let session ← artifact.newSession
  let createMetadata ← metadata program "Command" 0
  let invokeMetadata ← metadata program "Command" 1
  let madeMetadata ← metadata program "Reply" 0
  let resultMetadata ← metadata program "Reply" 1
  let made ← ownedRun session step.key (.constructed createMetadata [.word (word 10)])
  let handle ← match made.value with
    | .constructed actual [.function handle] =>
        assertTrue (decide (actual = madeMetadata)) "owned nominal function result lost constructor metadata"
        pure handle
    | _ => throw (IO.userError "owned nominal function result changed shape")
  let invoked ← ownedRun made.session step.key (.constructed invokeMetadata [.function handle, .word (word 2)])
  assertTrue (invoked.value == .constructed resultMetadata [.word (word 13)])
    "cached public artifact lost the original global/capture references"
  let again ← ownedRun invoked.session step.key (.constructed invokeMetadata [.function handle, .word (word 3)])
  assertTrue (again.value == .constructed resultMetadata [.word (word 16)] && again.session.heapSize > invoked.session.heapSize)
    "public owned session did not retain capture mutation across world extension"
  let checkpoint ← match again.session.start step.key (.constructed invokeMetadata [.function handle, .word (word 1)] :: []) with
    | .ok checkpoint => pure checkpoint
    | .error error => throw (IO.userError s!"public owned checkpoint rejected: {reprStr error}")
  let next ← match ← checkpoint.resume 2 with
    | .outOfFuel next => pure next
    | _ => throw (IO.userError "public owned checkpoint did not suspend")
  match ← next.resume 65536 with
  | .succeeded completion =>
      assertTrue (completion.value == .constructed resultMetadata [.word (word 17)]) "public owned resume changed capture state"
  | _ => throw (IO.userError "public owned resume failed")
  let separate ← match ← step.openCoreArtifact? with
    | some artifact => pure artifact
    | none => throw (IO.userError "public cached recipe disappeared on reuse")
  let other ← separate.newSession
  match other.authenticate 1024 invokeMetadata.resultType (.constructed invokeMetadata [.function handle, .word (word 1)]) with
  | .error error => assertTrue (error.code == .foreignArtifact) "cached reopening aliased artifact ownership"
  | .ok _ => throw (IO.userError "another cached artifact accepted the function capability")
  IO.println "public source compiler catalog Core and owned sessions GREEN"

end Tests.SourceCompilerCoreGeneral
