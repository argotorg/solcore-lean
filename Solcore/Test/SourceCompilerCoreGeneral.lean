import Solcore.Test.SourceCompilerFeatureSupport

/-! One cached compiler artifact supplies public data/function sessions and
internal native boundary checks. Metadata, ordered duplicates, captured mutable
cells and globals survive repeated invocation and checkpoint resumption. -/
set_option autoImplicit false
namespace Tests.SourceCompilerCoreGeneral
open Solcore Solcore.Frontend Tests.SourceCompilerFeatureSupport

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

private def metadata (program : CheckedProgram) (name : String) (index : Nat) : IO SourceInference.DataConstructorInstantiation := do
  let signature ← match program.signatures.dataTypes.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"public general data signature missing: {name}")
  let constructor ← match signature.constructors[index]? with
    | some constructor => pure constructor
    | none => throw (IO.userError "public general constructor missing")
  pure ⟨constructor.id, [], constructor.payloadTypes, .nominal signature.id []⟩

private def ownedRun {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (argument : Value) : IO (SourceCoreExecution.Completion artifact) := do
  match ← get "owned invocation" (← session.run key [argument] executionOptions) with
  | .succeeded completion => pure completion
  | .exportError error _ => throw (IO.userError s!"owned result rejected: {reprStr error}")
  | _ => throw (IO.userError "owned invocation failed")

example (entry : Entry) : SourceCoreExecution.prepare entry.compiled = .ok entry.execution := entry.prepared
example {definitions : Core.DataEnvironment} {type : Core.Ty}
    (result : SourceCoreGeneralEntry.Result definitions type) :
    result.observation.HasType type definitions := result.typed

def run : IO Unit := do
  let program ← get "general source checking" (checkProgram workspace)
  let leafMetadata ← metadata program "Tree" 0
  let pairMetadata ← metadata program "Tree" 1
  let leaf := fun value => SourceCorePublicValues.Value.constructed leafMetadata [scalar value]
  let pair := fun left right => SourceCorePublicValues.Value.constructed pairMetadata [left, right]
  let main ← compileNamed program "main"
  require (main.cached.compatible.checked.catalog.definitions.length > 0)
    "nominal typing used an empty data environment"
  for _ in [0, 1] do
    require ((← main.run [scalar 8]) == leaf 9) "cached nominal run changed"
  let echo ← compileNamed program "echo"
  let tree := pair (leaf 3) (pair (leaf 4) (leaf 5))
  require ((← echo.run [tree]) == tree) "deep nominal public input/result changed"
  match (← echo.native).start [.constructed ⟨⟨999⟩, 0⟩ .unit] with
  | .error (.input 0 _) => pure ()
  | _ => throw (IO.userError "cached native entry accepted an unknown nominal identity")
  match (← main.native).start [.word (word 8)] [.unit] with
  | .error (.initialStoreUnsupported 1) => pure ()
  | _ => throw (IO.userError "fresh cached native entry accepted an unowned initial heap")
  let recursive ← compileNamed program "recurse"
  require ((← recursive.run [scalar 2, leaf 2]) ==
    pair (pair (leaf 2) (leaf 2)) (pair (leaf 2) (leaf 2))) "recursive execution changed"
  let mapping ← compileNamed program "mappingValue"
  let entries : List (Value × Value) := [(scalar 7, scalar 4), (scalar 7, scalar 99), (scalar 2, scalar 6)]
  require ((← mapping.run [.mapping .word .word entries]) == .mapping .word .word
    [(scalar 7, scalar 7), (scalar 7, scalar 99), (scalar 2, scalar 6)])
    "mapping duplicate order or latest write changed"
  let proxy ← compileNamed program "proxyValue"
  require ((← proxy.run []) == .proxy leafMetadata.resultType) "proxy lost raw inner identity"
  let function ← compileNamed program "makeAdder"
  match ← function.run [scalar 10] with
  | .function _ => pure ()
  | _ => throw (IO.userError "function return lost its owned handle")
  match ← nativeObservation (← function.audit [scalar 10]) with
  | .succeeded (.pair (.pair (.inLeft .word .unit) (.closure ..)) (.word contract)) _ =>
      require (contract != Core.Word.zero) "callable lost its authenticated contract descriptor"
  | _ => throw (IO.userError "cached function result changed native shape")
  for name in ["missing", "absent"] do
    let failed ← compileNamed program name
    let arguments : List Value := if name == "missing" then
      [.mapping .word leafMetadata.resultType [], scalar 7] else []
    let invocation ← failed.invoke arguments
    match invocation.outcome with
    | .failed reason _ =>
        match ← invocation.diagnostic reason with
        | some diagnostic =>
            require diagnostic.span.isSome "general failure lost occurrence span"
            if name == "missing" then
              require (decide (diagnostic.error = .typeMismatch leafMetadata.resultType none))
                "absent mapping default changed source error"
        | none => throw (IO.userError "general language failure lost its diagnostic")
    | _ => throw (IO.userError "general language failure changed")

  let conventional ← get "conventional general entry" (SourceCoreExecution.compileEntry workspace options)
  let conventionalRoot ← match conventional.root? 0 with
    | some root => pure root | none => throw (IO.userError "conventional root missing")
  let conventionalArtifact ← conventional.open
  let conventionalSession ← boot conventionalArtifact
  let conventionalResult ← ownedRun conventionalSession conventionalRoot.key (scalar 4)
  require (conventionalResult.value == leaf 5) "raw compileEntry changed conventional main"

  let step ← compileNamed program "step"
  let artifact ← step.execution.open
  require (step.execution.keys == [step.key]) "cached owned root key changed"
  let session ← boot artifact
  let createMetadata ← metadata program "Command" 0
  let invokeMetadata ← metadata program "Command" 1
  let madeMetadata ← metadata program "Reply" 0
  let resultMetadata ← metadata program "Reply" 1
  let made ← ownedRun session step.key (.constructed createMetadata [scalar 10])
  let handle ← match made.value with
    | .constructed actual [.function handle] =>
        require (decide (actual = madeMetadata)) "owned nominal result lost constructor metadata"
        pure handle
    | _ => throw (IO.userError "owned nominal function result changed shape")
  let invoked ← ownedRun made.session step.key (.constructed invokeMetadata [.function handle, scalar 2])
  require (invoked.value == .constructed resultMetadata [scalar 13])
    "cached artifact lost original global/capture references"
  let again ← ownedRun invoked.session step.key (.constructed invokeMetadata [.function handle, scalar 3])
  require (again.value == .constructed resultMetadata [scalar 16] && again.session.heapSize > invoked.session.heapSize)
    "owned session lost capture mutation across world extension"
  let checkpoint ← get "owned checkpoint" (again.session.start step.key
    [.constructed invokeMetadata [.function handle, scalar 1]])
  let next ← match ← checkpoint.resume 2 with
    | .outOfFuel next => pure next
    | _ => throw (IO.userError "owned checkpoint did not suspend")
  match ← next.resume 300000 with
  | .succeeded completion =>
      require (completion.value == .constructed resultMetadata [scalar 17]) "owned resume changed capture state"
  | _ => throw (IO.userError "owned resume failed")
  let separate ← step.execution.open
  let other ← boot separate
  match other.authenticate 1024 invokeMetadata.resultType (.constructed invokeMetadata [.function handle, scalar 1]) with
  | .error {code := .foreignArtifact, ..} => pure ()
  | _ => throw (IO.userError "another cached artifact accepted the function capability")
  IO.println "public compiler data and owned sessions GREEN"
end Tests.SourceCompilerCoreGeneral
