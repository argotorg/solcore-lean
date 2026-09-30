import Solcore.Frontend.SourceCoreSession

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.RuntimeValue
#check_failure Solcore.Frontend.SourceCoreSession.Handle.mk
#check_failure Solcore.Frontend.SourceCoreSession.Session.mk
#check_failure Solcore.Frontend.SourceCoreSession.Recipe.mk
#check_failure Solcore.Frontend.SourceCoreSession.Session.store
#check_failure Solcore.Frontend.SourceCoreSession.Checkpoint.state
#check_failure Solcore.Frontend.SourceCoreSession.register
#check_failure Solcore.Frontend.SourceCoreSession.Value.closure
#check_failure Solcore.Frontend.SourceCoreSession.Value.cellRef
#check_failure Solcore.Frontend.SourceCoreSession.Handle.artifact

set_option autoImplicit false

namespace Tests.SourceCoreSession

open Solcore Solcore.Frontend SourceCoreSession

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Value := .word (Core.Word.ofNatModulo value)
private def functionType : TypeSystem.Ty := .function .word .word

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Holder { Put(function(Word) returns (Word)) }",
    "enum Branch { Leaf(function(Word) returns (Word)), Pair(Branch, Branch) }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function make(value: Word) returns (function(Word) returns (Word)) {",
    " return lam(delta: Word) -> Word { value = value + delta; return inc(value); }; }",
    "function twins(value: Word) returns (function(Word) returns (Word), function(Word) returns (Word)) {",
    " let f: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; };",
    " let g: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; return value; }; return (f, g); }",
    "function use(f: function(Word) returns (Word), delta: Word) returns (Word) { return f(delta); }",
    "function mirror(f: function(Word) returns (Word)) returns (function(Word) returns (Word)) { return f; }",
    "function named() returns (function(Word) returns (Word)) { return inc; }",
    "function boxed(f: function(Word) returns (Word)) returns (Holder) { return .Put(f); }",
    "function echoBox(value: Holder) returns (Holder) { return value; }",
    "function unbox(value: Holder) returns (function(Word) returns (Word)) { match (value) { case .Put(f) { return f; } } }",
    "function echoMap(value: mapping(Word => function(Word) returns (Word))) returns (mapping(Word => function(Word) returns (Word))) { return value; }",
    "function fromMap(value: mapping(Word => function(Word) returns (Word)), key: Word) returns (function(Word) returns (Word)) { return value[key]; }",
    "function echoPair(value: (Word, function(Word) returns (Word))) returns (Word, function(Word) returns (Word)) { return value; }",
    "function failurePair(value: Word) returns (function(Word) returns (Word), function() returns (Word)) {",
    " let f: function(Word) returns (Word) = lam(delta: Word) -> Word { value = value + delta; let absent: Word; return absent; };",
    " let g: function() returns (Word) = lam() -> Word { return value; }; return (f, g); }",
    "function get(f: function() returns (Word)) returns (Word) { return f(); }"
    , "function proxyWord() returns (@Word) { return @Word; }"
    , "function echoBranch(value: Branch) returns (Branch) { return value; }"
  ] }] }

private def plan (program : CheckedProgram) : IO SourceSpecializationWorklist.Plan :=
  match SourceSpecializationWorklist.run program
      (program.signatures.functions.map fun signature => { declaration := signature.id, parameterSubstitution := [] }) 256 with
  | .ok (.complete plan) => pure plan
  | other => throw (IO.userError s!"session specialization failed: {reprStr other}")

private def prepare (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan) : IO Artifact := do
  match ← Artifact.prepareAutomatic program plan 256 with
  | .ok artifact => pure artifact
  | .error error => throw (IO.userError s!"session automatic catalog compilation failed: {reprStr error}")

private def keyFor (artifact : Artifact) (program : CheckedProgram) (name : String) : IO Key := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"session fixture function missing: {name}")
  match artifact.keys.find? fun key => decide (key.declaration = signature.id) with
  | some key => pure key
  | none => throw (IO.userError s!"session artifact omitted root: {name}")

private def execute {artifact : Artifact} (session : Session artifact) (key : Key)
    (arguments : List Value) (fuel : Nat := 65536) : IO (Completion artifact) := do
  match ← session.run key arguments fuel with
  | .error error => throw (IO.userError s!"session input rejected: {reprStr error}")
  | .ok (.succeeded completion) => pure completion
  | .ok (.failed reason _) => throw (IO.userError s!"session language failure: {reprStr reason}")
  | .ok (.exportError error _) => throw (IO.userError s!"session export rejected: {reprStr error}")
  | .ok (.outOfFuel _) => throw (IO.userError "session fixture exhausted fuel")

private def reject {artifact : Artifact} (session : Session artifact) (type : TypeSystem.Ty)
    (value : Value) (fuel : Nat := 1024) : IO Error :=
  match session.authenticate fuel type value with
  | .error error => pure error
  | .ok _ => throw (IO.userError "session accepted a forged or foreign value")

example {artifact : Artifact} (completion : Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value := completion.typed
example {artifact : Artifact} {session : Session artifact} {fuel : Nat} {type : TypeSystem.Ty} {value : Value}
    (certificate : Authentication session fuel type value) : session.Authenticates fuel type value := certificate.typed
example {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat) : checkpoint.NativeSafe fuel :=
  checkpoint.native_safe fuel
example {artifact : Artifact} {checkpoint next : Checkpoint artifact} {spent : Nat}
    (exhausted : checkpoint.suspend? spent = some next) (additional : Nat) :
    checkpoint.NativeResumes next spent additional := Checkpoint.suspend?_fuel_resume exhausted additional

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"session source rejected: {reprStr error}")
  let plan ← plan program
  let recipe ← match Recipe.prepareAutomatic program plan 256 with
    | .ok recipe => pure recipe
    | .error error => throw (IO.userError s!"session recipe rejected: {reprStr error}")
  assertTrue (recipe.program.entries.length == program.signatures.functions.length) "cached recipe omitted roots"
  let artifact ← recipe.open
  let key := keyFor artifact program
  let initial ← artifact.newSession
  assertTrue (initial.heapSize == 0 && initial.functionCount == 0) "fresh session is not empty"
  let made ← execute initial (← key "make") [word 10]
  assertTrue (made.session.functionCount == 1 && made.session.heapSize > 0) "returned closure was not privately registered"
  let first ← execute made.session (← key "use") [made.value, word 2]
  assertTrue (first.value == word 13 && first.session.heapSize > made.session.heapSize)
    "owned closure lost its old global references or shared capture during world extension"
  let second ← execute first.session (← key "use") [made.value, word 3]
  assertTrue (second.value == word 16) "reused closure did not retain its mutable capture"
  let mirrored ← execute second.session (← key "mirror") [made.value]
  assertTrue (mirrored.value == made.value && mirrored.session.functionCount == 1)
    "function export did not reuse the exact existing handle"
  let identity : Session artifact → Value → Option FunctionIdentity := fun session value => match value with
    | .function handle => session.functionIdentity? handle
    | _ => none
  assertTrue (identity mirrored.session made.value == some .anonymous) "anonymous function identity tag changed"
  let named ← execute mirrored.session (← key "named") []
  let same ← execute named.session (← key "named") []
  assertTrue ((match identity named.session named.value with | some (.named _) => true | _ => false) &&
      identity same.session same.value == identity named.session named.value)
    "named function identity tag changed between exports"

  let otherSession ← artifact.newSession
  assertTrue ((← reject otherSession functionType made.value).code == .foreignSession)
    "another fresh session accepted an owned function"
  let otherArtifact ← recipe.open
  let other ← otherArtifact.newSession
  assertTrue ((← reject other functionType made.value).code == .foreignArtifact)
    "another artifact accepted an owned function"
  let branchA ← execute initial (← key "make") [word 1]
  let branchB ← execute initial (← key "make") [word 1]
  assertTrue (branchA.value != branchB.value) "branched immutable sessions reused an export token"
  assertTrue ((← reject branchB.session functionType branchA.value).code == .unknownHandle)
    "a branch accepted another branch's colliding slot"
  assertTrue ((← reject made.session (.function .unit .word) made.value).code ==
      .handleTypeMismatch (.function .unit .word) functionType) "wrong function type was accepted"
  let foreignPair := Value.product (word 7) made.value
  let error ← reject otherSession (.product .word functionType) foreignPair
  assertTrue (error.path == [.productRight] && error.code == .foreignSession) "deep handle ownership path changed"

  let twins ← execute same.session (← key "twins") [word 20]
  let (left, right) ← match twins.value with
    | .product left right => pure (left, right)
    | _ => throw (IO.userError "shared closure product changed shape")
  let leftResult ← execute twins.session (← key "use") [left, word 2]
  let rightResult ← execute leftResult.session (← key "use") [right, word 3]
  assertTrue (leftResult.value == word 22 && rightResult.value == word 25)
    "separately exported closures stopped sharing the same source cell"
  let paired := Value.product (word 9) right
  let pairEcho ← execute rightResult.session (← key "echoPair") [paired]
  assertTrue (pairEcho.value == paired) "deep function product roundtrip changed its handle"
  let boxed ← execute pairEcho.session (← key "boxed") [right]
  let boxEcho ← execute boxed.session (← key "echoBox") [boxed.value]
  assertTrue (boxEcho.value == boxed.value) "nominal function payload roundtrip changed metadata or handle"
  let unboxed ← execute boxEcho.session (← key "unbox") [boxEcho.value]
  assertTrue (unboxed.value == right) "nominal matcher changed the owned function"
  let (metadata, payloads) ← match boxed.value with
    | .constructed metadata payloads => pure (metadata, payloads)
    | _ => throw (IO.userError "nominal owned result changed shape")
  let forged := Value.constructed { metadata with payloadTypes := [.word] } payloads
  assertTrue ((← reject unboxed.session metadata.resultType forged).code != .unknownHandle)
    "forged constructor payload metadata was accepted"
  let forged := Value.constructed { metadata with parameterSubstitution := [(⟨metadata.constructor.dataType, 0⟩, .word)] } payloads
  let _ ← reject unboxed.session metadata.resultType forged
  let forged := Value.constructed { metadata with constructor := { metadata.constructor with constructorIndex := 99 } } payloads
  let _ ← reject unboxed.session metadata.resultType forged
  let foreignBox := Value.constructed metadata [made.value]
  let error ← reject otherSession metadata.resultType foreignBox
  assertTrue (error.path == [.constructorPayload 0] && error.code == .foreignSession)
    "nominal payload did not deeply authenticate its function owner"
  let branch ← match program.signatures.dataTypes.filter (·.name == "Branch") with
    | [branch] => pure branch
    | _ => throw (IO.userError "recursive session data signature missing")
  let branchType := TypeSystem.Ty.nominal branch.id []
  let leafMetadata : SourceInference.DataConstructorInstantiation := ⟨⟨branch.id, 0⟩, [], [functionType], branchType⟩
  let pairMetadata : SourceInference.DataConstructorInstantiation := ⟨⟨branch.id, 1⟩, [], [branchType, branchType], branchType⟩
  let leaf := Value.constructed leafMetadata [right]
  let nested := (List.range 20).foldl (fun value _ => .constructed pairMetadata [value, leaf]) leaf
  let recursive ← execute unboxed.session (← key "echoBranch") [nested]
  assertTrue (recursive.value == nested) "recursive nominal function payload roundtrip changed"
  let mapping := Value.mapping .word functionType [(word 7, left), (word 7, right), (word 2, named.value)]
  let mapEcho ← execute unboxed.session (← key "echoMap") [mapping]
  assertTrue (mapEcho.value == mapping) "ordered mapping function payloads were sorted or deduplicated"
  let selected ← execute mapEcho.session (← key "fromMap") [mapping, word 7]
  assertTrue (selected.value == left) "duplicate mapping keys changed first-match function identity"
  let error ← reject otherSession (.mapping .word functionType) mapping
  assertTrue (error.path == [.mappingValue 0] && error.code == .foreignSession) "mapping function owner was not checked"
  let error ← reject selected.session (.mapping .word functionType) (.mapping .integer functionType [])
  assertTrue (error.code == .data (.mappingMetadataMismatch .word functionType .integer functionType))
    "mapping source metadata forgery was accepted"
  assertTrue ((← reject selected.session (.proxy .word) (.proxy .integer)).code ==
      .data (.proxyIdentityMismatch .word .integer)) "proxy raw inner identity forgery was accepted"
  assertTrue ((← reject selected.session (.product .word functionType) paired 1).code == .data .exhausted)
    "deep validation ignored its fuel bound"

  let failedPair ← execute selected.session (← key "failurePair") [word 30]
  let (failing, getter) ← match failedPair.value with
    | .product failing getter => pure (failing, getter)
    | _ => throw (IO.userError "failure pair changed shape")
  let failedSession ← match ← failedPair.session.run (← key "use") [failing, word 4] 65536 with
    | .ok (.failed _ session) => pure session
    | _ => throw (IO.userError "language failure did not retain the owned heap")
  let afterFailure ← execute failedSession (← key "get") [getter]
  assertTrue (afterFailure.value == word 34) "effects before language failure were lost"

  let checkpoint ← match afterFailure.session.start (← key "use") [right, word 1] with
    | .ok checkpoint => pure checkpoint
    | .error error => throw (IO.userError s!"typed session checkpoint rejected: {reprStr error}")
  let next ← match ← checkpoint.resume 2 with
    | .outOfFuel next => pure next
    | _ => throw (IO.userError "small fuel did not retain a typed session checkpoint")
  let resumed ← match ← next.resume 65536 with
    | .succeeded completion => pure completion
    | _ => throw (IO.userError "typed session resume failed")
  let direct ← match ← checkpoint.resume 65538 with
    | .succeeded completion => pure completion
    | _ => throw (IO.userError "typed session combined fuel failed")
  assertTrue (resumed.value == word 26 && direct.value == resumed.value && direct.session.heapSize == resumed.session.heapSize)
    "resume changed capture mutation or heap extension"
  assertTrue ((resumed.session.authenticate 1024 functionType right).isOk)
    "checkpoint world extension invalidated an existing owned handle"
  let pureNext ← match checkpoint.suspend? 2 with
    | some next => pure next
    | none => throw (IO.userError "pure native checkpoint observation did not retain exhaustion")
  let pureResumed ← match ← pureNext.resume 65536 with
    | .succeeded completion => pure completion
    | _ => throw (IO.userError "pure suspension checkpoint failed to resume")
  assertTrue (pureResumed.value == resumed.value) "pure and IO checkpoint paths diverged"
  let exportSession ← match ← pureResumed.session.run (← key "named") [] 65536 0 with
    | .ok (.exportError error session) =>
        assertTrue (error.code == .data .exhausted) "bounded export changed its error"
        pure session
    | _ => throw (IO.userError "zero export fuel did not retain the certified native heap")
  let afterExportError ← execute exportSession (← key "use") [right, word 1]
  assertTrue (afterExportError.value == word 27) "export failure invalidated existing handles or heap effects"
  let factoryArtifact ← prepare program plan
  let factorySession ← factoryArtifact.newSession
  assertTrue ((← reject factorySession functionType right).code == .foreignArtifact)
    "automatic artifact factory reused an existing ownership token"
  IO.println "source Core owned function sessions GREEN"

end Tests.SourceCoreSession
