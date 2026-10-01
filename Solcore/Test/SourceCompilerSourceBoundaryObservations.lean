import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.SourceCoreRawMetadata
import Solcore.Frontend.SourceCoreRawMetadataRuntime

/-! Concrete observations of the existing public source-value boundary.
These checked fixtures use the exact cached artifact also prepared for the
common public session. Internal observations pin raw prefix compatibility. The initial prefix is validated and inert;
public captured-closure arguments remain rejected. -/

set_option autoImplicit false

namespace Tests.SourceCompilerSourceBoundaryObservations

open Solcore Solcore.Frontend SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function proxyEcho(value: @Word) returns (@Word) { return value; }",
    "function proxyLookup(table: mapping(@Word => Word)) returns (Word) { return table[@Word]; }",
    "function proxyMissing(table: mapping(Word => @Word)) returns (@Word) { return table[9]; }",
    "function mappingEcho(value: mapping(Word => Word)) returns (mapping(Word => Word)) { return value; }",
    "function boxEcho(value: Box<Word>) returns (Box<Word>) { return value; }",
    "function boxMatch(value: Box<Word>) returns (Word) { match (value) { case .Box(inner) { return inner; } default { return 99; } } }",
    "function scalar(value: Word) returns (Word) { return value; }",
    "function returnClosure() returns (function() returns (Word)) { let captured: Word = 7; return lam() -> Word { return captured; }; }",
    "function unusedPoly(captured: Word) returns (Word) { let f = lam(value) { return (value, captured); }; return captured; }",
    "function apply(f: function(Word) returns (Word), value: Word) returns (Word) { let retained: function(Word) returns (Word) = scalar; return f(value); }",
    "function applyUnselected(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
    "function invokeUnit(f: function() returns (Word)) returns (Word) { return f(); }",
    "function applyInteger(f: function(Word) returns (integer), value: Word) returns (integer) { return f(value); }"
  ] }] }

private def compile (program : CheckedProgram) (name : String) : IO SourceCompilerFeatureSupport.Entry :=
  SourceCompilerFeatureSupport.compileNamed program name []
    {specializationBudget := 128, compilationFuel := 1000}

private def options : SourceCoreExecution.RunOptions := { inputValidationFuel := 128, executionFuel := 10000 }

private def completed (compiled : SourceCompilerFeatureSupport.Entry) (arguments : List SourceTypedRuntime.Value)
    (state : SourceTypedRuntime.RuntimeState := {}) : IO (SourceTypedRuntime.Value × SourceTypedRuntime.RuntimeState) := do
  let result ← SourceCompilerFeatureSupport.get "retained boundary execution"
    (compiled.cached.run compiled.key arguments options.inputValidationFuel options.executionFuel state)
  match result.observation with
  | .done value state => pure (value, state)
  | other => throw (IO.userError s!"source boundary execution failed: {reprStr other}")

private def wordResult (compiled : SourceCompilerFeatureSupport.Entry) (arguments : List SourceTypedRuntime.Value) (expected : Nat)
    (state : SourceTypedRuntime.RuntimeState := {}) : IO SourceTypedRuntime.RuntimeState := do
  let (value, state) ← completed compiled arguments state
  match value with
  | .word actual => assertTrue (actual == word expected) "source boundary Word result changed"; pure state
  | _ => throw (IO.userError "source boundary result was not Word")

example (type : TypeSystem.Ty) : SourceCoreRawMetadata.runtimeType type = SourceTypedRuntime.runtimeType type := by
  exact SourceCoreRawMetadata.runtimeType_sourceValues type

example (signatures : ProgramSignatures) (instantiation : DataConstructorInstantiation) :
    SourceCoreRawMetadata.constructorAuthentic signatures instantiation =
      SourceTypedRuntime.validConstructorInstantiation signatures instantiation := rfl

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"source boundary checking failed: {reprStr error}")
  let proxy ← compile program "proxyEcho"
  match (← completed proxy [.proxy (.comptime .word)]).1 with
  | .proxy (.comptime .word) => pure ()
  | _ => throw (IO.userError "accepted proxy metadata was erased")
  let lookup ← compile program "proxyLookup"
  let rawProxyMap : SourceTypedRuntime.Value := .mapping (.proxy .word) .word
    [(.proxy (.comptime .word), .word (word 7))]
  discard <| wordResult lookup [rawProxyMap] 0
  discard <| wordResult lookup [.mapping (.proxy .word) .word [(.proxy .word, .word (word 7))]] 7
  let missing ← compile program "proxyMissing"
  match (← completed missing [.mapping .word (.proxy (.comptime .word)) []]).1 with
  | .proxy (.comptime .word) => pure ()
  | _ => throw (IO.userError "mapping default ignored the actual raw value header")
  let mapping ← compile program "mappingEcho"
  let rawMap : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(.word (word 3), .word (word 7)), (.word (word 3), .word (word 9))]
  assertTrue (reprStr (← completed mapping [rawMap]).1 == reprStr rawMap)
    "mapping raw header or duplicate entry order changed"
  let box ← match program.signatures.dataTypes.filter (·.name == "Box") with
    | [signature] => pure signature
    | _ => throw (IO.userError "source boundary Box signature missing")
  let (parameter, constructor) ← match box.parameters, box.constructors with
    | [parameter], [constructor] => pure (parameter, constructor)
    | _, _ => throw (IO.userError "source boundary Box signature malformed")
  let stagedMetadata : DataConstructorInstantiation := {
    constructor := constructor.id, parameterSubstitution := [(parameter, .comptime .word)]
    payloadTypes := [.comptime .word], resultType := .nominal box.id [.comptime .word] }
  let ordinaryMetadata : DataConstructorInstantiation := {
    constructor := constructor.id, parameterSubstitution := [(parameter, .word)]
    payloadTypes := [.word], resultType := .nominal box.id [.word] }
  let echo ← compile program "boxEcho"
  match (← completed echo [.constructed stagedMetadata [.word (word 7)]]).1 with
  | .constructed actual _ => assertTrue (actual == stagedMetadata) "authenticated nominal metadata changed"
  | _ => throw (IO.userError "source boundary nominal result changed shape")
  let matchBox ← compile program "boxMatch"
  let noMatch ← wordResult matchBox [.constructed stagedMetadata [.word (word 7)]] 99
  let matched ← wordResult matchBox [.constructed ordinaryMetadata [.word (word 7)]] 7
  assertTrue (noMatch.heap.length == 2 && matched.heap.length == 3)
    "hidden scrutinee or successful pattern binder source allocation changed"
  let factory ← compile program "returnClosure"
  let (closure, initial) ← completed factory []
  let withClosure : SourceTypedRuntime.RuntimeState := {
    heap := initial.heap ++ [{type := .function .unit .word, value := some closure}] }
  let (_, reused) ← completed factory [] withClosure
  assertTrue (reprStr (reused.heap.take withClosure.heap.length) == reprStr withClosure.heap && reused.heap.length == 3)
    "accepted existing closure heap prefix changed"
  /- Old code validation checks capture readability, not lexical type alignment.
  This prefix cannot be reached by any accepted public function input. -/
  let readablePrefix : SourceTypedRuntime.RuntimeState := { heap := [
    {type := .bool, value := some (.bool true)},
    {type := .function .unit .word, value := some closure}] }
  let (_, reusedReadable) ← completed factory [] readablePrefix
  assertTrue (reprStr (reusedReadable.heap.take 2) == reprStr readablePrefix.heap)
    "accepted inert readable closure prefix changed"
  let scalar ← compile program "scalar"
  let openPrefix : SourceTypedRuntime.RuntimeState := { heap := [
    {type := .error, value := none}, {type := .word, value := some (.word (word 99))}] }
  let scalarState ← wordResult scalar [.word (word 8)] 8 openPrefix
  assertTrue (reprStr (scalarState.heap.take 2) == reprStr openPrefix.heap && scalarState.heap.length == 3)
    "uninitialized open source prefix was rejected or changed"
  let unused ← compile program "unusedPoly"
  let unusedState ← wordResult unused [.word (word 8)] 8
  match unusedState.heap with
  | [_, {type := .function _ _, value := some (.closure _ _ _ _ _ captures _)}] =>
      assertTrue (captures.map (fun capture => capture.2.index) == [0]) "unused principal closure lost its source capture"
  | _ => throw (IO.userError "unused generalized source binding did not retain its principal closure heap cell")
  let key : SourceSpecialization.SpecializationKey ← match program.signatures.functions.filter (·.name == "scalar") with
    | [signature] => pure ⟨signature.id, []⟩
    | _ => throw (IO.userError "source boundary selected global key missing")
  let apply ← compile program "apply"
  let globalState ← wordResult apply [.global key [], .word (word 8)] 8
  assertTrue (globalState.heap.length == 4) "global input/callee parameter allocation changed"
  let unselected ← compile program "applyUnselected"
  let rejectedGlobal ← SourceCompilerFeatureSupport.get "unselected global audit"
    (unselected.cached.run unselected.key [.global key [], .word (word 8)] options.inputValidationFuel options.executionFuel)
  match rejectedGlobal.observation with
  | .fault (.typeMismatch _ _) _ => pure ()
  | _ => throw (IO.userError "a global outside the selected plan was accepted")
  let invoke ← compile program "invokeUnit"
  let rejectedClosure ← SourceCompilerFeatureSupport.get "raw closure audit"
    (invoke.cached.run invoke.key [closure] options.inputValidationFuel options.executionFuel)
  match rejectedClosure.observation with
  | .fault (.typeMismatch _ _) _ => pure ()
  | _ => throw (IO.userError "public raw captured closure argument was accepted")
  let builtin ← compile program "applyInteger"
  match (← completed builtin [.builtin .wordToInteger, .word (word 8)]).1 with
  | .integer 8 => pure ()
  | _ => throw (IO.userError "public builtin function input changed")
  let malformedPrefix : SourceTypedRuntime.RuntimeState := {
    heap := [{type := .word, value := some (.bool true)}] }
  let malformedInput ← SourceCompilerFeatureSupport.get "input ordering audit"
    (scalar.cached.run scalar.key [.bool true] options.inputValidationFuel options.executionFuel malformedPrefix)
  match malformedInput.observation with
  | .fault (.typeMismatch .word (some .bool)) _ => pure ()
  | _ => throw (IO.userError "public input failure did not precede initial heap rejection")
  -- The public data carrier keeps the same accepted metadata and order.
  unless (← proxy.run [.proxy (.comptime .word)]) == .proxy (.comptime .word) do
    throw (IO.userError "public proxy metadata changed")
  unless (← lookup.run [.mapping (.proxy .word) .word
      [(.proxy (.comptime .word), .word (word 7))]]) == .word (word 0) do
    throw (IO.userError "public proxy-key comparison erased raw metadata")
  unless (← missing.run [.mapping .word (.proxy (.comptime .word)) []]) == .proxy (.comptime .word) do
    throw (IO.userError "public mapping default lost its raw value header")
  let publicMap : SourceCoreExecution.Value := .mapping (.comptime .word) (.comptime .word)
    [(.word (word 3), .word (word 7)), (.word (word 3), .word (word 9))]
  unless (← mapping.run [publicMap]) == publicMap do
    throw (IO.userError "public mapping metadata or duplicate order changed")
  let publicBox : SourceCoreExecution.Value := .constructed stagedMetadata [.word (word 7)]
  unless (← echo.run [publicBox]) == publicBox && (← matchBox.run [publicBox]) == .word (word 99) do
    throw (IO.userError "public nominal metadata or matching changed")
  IO.println "public raw metadata, function inputs and inert source heap observations GREEN"

end Tests.SourceCompilerSourceBoundaryObservations
