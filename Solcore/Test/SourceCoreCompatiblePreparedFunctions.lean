import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.ProgramChecking

/-! Automatic compatible artifacts own checked definitions, cached functions,
raw input extensions and dynamic diagnostics. Invocation and resume use Core. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatiblePreparedFunctions
open Solcore Solcore.Frontend SourceInference
abbrev DataValue := SourceCoreCompatibleValues.Value
abbrev Key := SourceSpecialization.SpecializationKey

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "trait Marker<T> {}", "impl Marker<mapping(Word => Word)> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function local(table: mapping(Word => Word)) returns (mapping(Word => Word)) { let f = lam(item) { return keep(item); }; return f(table); }",
    "function ordered(table: mapping(@Word => Word), key: @Word) returns (mapping(@Word => Word)) { table[key] += 3; return table; }",
    "function lazy() returns (mapping(Word => Word)) { let table: mapping(Word => Word); table[1] = 7; return table; }",
    "function choose(value: Box<Word>) returns (Word) { match (value) { case .Box(bound) { return bound; } default { return 99; } } }",
    "function missing(table: mapping(Word => Box<Word>), key: Word) returns (Word) { table[key] = .Box(7); return 7; }",
    "function absent() returns (Word) { let absent: Word; return absent; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"compatible prepared fixture missing: {name}")

private def completed {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (key : Key)
    (arguments : List DataValue) (fuel : Nat) : IO (SourceCoreCompatibleFunctions.Completion checked) := do
  match prepared.runData key arguments fuel 500 with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"compatible prepared run failed: {reprStr error}")

private def succeeded {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (key : Key)
    (arguments : List DataValue) (expected : DataValue) : IO Unit := do
  for fuel in [0, 8, 65536] do
    let completion ← completed prepared key arguments fuel
    let native := match completion.result.native.checkpoint? with
      | some checkpoint => checkpoint.resume 65536
      | none => completion.result.native
    match native.observation with
    | .succeeded value _ =>
        let decoded ← match SourceCoreCompatibleValues.decode 500 completion.result.context
            completion.entry.sourceResultType value with
          | .ok value => pure value
          | .error error => throw (IO.userError s!"compatible prepared output failed: {reprStr error}")
        assertTrue (decoded == expected) s!"compatible prepared result changed: {reprStr decoded}"
    | observation => throw (IO.userError s!"compatible prepared observation changed: {reprStr observation}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"compatible prepared source rejected: {reprStr error}")
  let names := ["local", "ordered", "lazy", "choose", "missing", "absent"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program
      (keys.map (fun key => ⟨key.declaration, []⟩)) 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"compatible prepared worklist failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic
    | .error error => throw (IO.userError s!"compatible automatic factory failed: {reprStr error}")
  let prepared := automatic.prepared
  assertTrue (prepared.entries.length == keys.length) "compatible prepared roots disappeared"
  let table : DataValue := .mapping .word .word [(.word (w 1), .word (w 9))]
  succeeded prepared (← key program "local") [table] table
  succeeded prepared (← key program "lazy") [] (.mapping .word .word [(.word (w 1), .word (w 7))])
  let rawMap : DataValue := .mapping (.proxy (.comptime .word)) (.comptime .word)
    [(.proxy (.comptime .word), .word (w 1)), (.proxy (.comptime .word), .word (w 2))]
  let updated : DataValue := .mapping (.proxy (.comptime .word)) (.comptime .word)
    [(.proxy (.comptime .word), .word (w 4)), (.proxy (.comptime .word), .word (w 2))]
  succeeded prepared (← key program "ordered") [rawMap, .proxy (.comptime .word)] updated
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "compatible Box missing")
  let ctor ← match box.constructors[0]? with
    | some ctor => pure ctor | none => throw (IO.userError "compatible constructor missing")
  let boxType := TypeSystem.Ty.nominal box.id [.word]
  let ordinary : DataConstructorInstantiation := ⟨ctor.id, box.parameters.zip [.word], [.word], boxType⟩
  let raw : DataConstructorInstantiation := ⟨ctor.id, box.parameters.zip [.comptime .word],
    [.comptime .word], .nominal box.id [.comptime .word]⟩
  succeeded prepared (← key program "choose") [.constructed ordinary [.word (w 7)]] (.word (w 7))
  succeeded prepared (← key program "choose") [.constructed raw [.word (w 7)]] (.word (w 99))
  let failure ← completed prepared (← key program "missing")
    [.mapping (.comptime .word) (.comptime boxType) [], .word (w 1)] 65536
  match failure.result.native.observation with
  | .failed reason _ =>
      let diagnostic ← match failure.result.diagnostics.diagnostic? reason with
        | some diagnostic => pure diagnostic
        | none => throw (IO.userError "compatible dynamic missing diagnostic absent")
      assertTrue (decide (diagnostic.error = .typeMismatch (.comptime boxType) none))
        "compatible dynamic fault lost its raw value type"
      assertTrue diagnostic.span.isSome "compatible dynamic fault lost its source span"
  | observation => throw (IO.userError s!"compatible missing default did not fail: {reprStr observation}")
  let absent ← completed prepared (← key program "absent") [] 65536
  match absent.result.native.observation with
  | .failed reason _ =>
      assertTrue (absent.result.diagnostics.diagnostic? reason).isSome
        "compatible uninitialized read lost its diagnostic"
  | observation => throw (IO.userError s!"compatible uninitialized read changed: {reprStr observation}")
  assertTrue (decide (failure.result.diagnostics.additional.map (·.1)).Nodup)
    "compatible dynamic/callable diagnostic reservations overlap"
  IO.println "compatible automatic function artifacts, raw data, dynamic diagnostics and typed resume GREEN"
end Tests.SourceCoreCompatiblePreparedFunctions
