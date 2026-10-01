import Solcore.Frontend.SourceCoreCompatibleMarkedFunctions
import Solcore.Frontend.ProgramChecking

/-! Real checked multi-root compilation with one fixed allocation suffix.
Execution and resumption use the shared typed Core machine. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMarkedFunctions
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey

private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "trait Marker<T> {}", "impl Marker<mapping(Word => Word)> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function local(table: mapping(Word => Word)) returns (mapping(Word => Word)) { let f = lam(item) { return keep(item); }; return f(table); }",
    "function lazy() returns (mapping(Word => Word)) { let table: mapping(Word => Word); table[1] = 7; return table; }",
    "function choose(value: Box<Word>) returns (Word) { match (value) { case .Box(bound) { return bound; } default { return 99; } } }",
    "function capture(start: Word) returns (Word) { let value = start; let f = lam(step: Word) { value += step; return value; }; f(3); return f(4); }",
    "function recursive(n: Word) returns (Word) { let f: function(Word) returns (Word); f = lam(left: Word) { return left == 0 ? 0 : f(left - 1) + 1; }; return f(n); }",
    "function unused() returns (Word) { let unused = lam(item) { return item; }; return 7; }",
    "function tuple(value: (Word, Bool)) returns (Word) { match (value) { case ((left, flag)) { return flag ? left : 99; } default { return 77; } } }",
    "function looping(limit: Word) returns (Word) { let total = 0; for (let i = 0; i < limit; i += 1) { total += i; } return total; }",
    "function absent() returns (Word) { let absent: Word; return absent; }"
    , "function getLocal(start: Word) returns (function(Word) returns (Word)) { let value = start; let f = lam(item) { value += 1; return item; }; return f; }"
    , "function useReturned(start: Word) returns (Word) { let f = getLocal(start); return f(9); }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"marked fixture missing {name}")

private def runSuccess {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.Prepared checked) (key : Key) (arguments : List SourceTypedRuntime.Value)
    (expected : SourceCoreCompatibleValues.Value) : IO Unit := do
  for fuel in [0, 7, 37, 150000] do
    let completion ← match prepared.runSource key arguments fuel 500 with
      | .ok completion => pure completion
      | .error error => throw (IO.userError s!"marked run failed: {reprStr error}")
    let completion := completion.resume 150000
    match completion.result.native.observation with
    | .succeeded value store =>
      let decoded ← match SourceCoreCompatibleValues.decode 500 completion.result.context completion.entry.sourceResultType value with
        | .ok decoded => pure decoded
        | .error error => throw (IO.userError s!"marked output failed: {reprStr error}")
      assertTrue (decoded == expected) s!"marked result changed: {reprStr decoded}"
      assertTrue (store.any fun value => match value with
        | .constructed constructor _ => constructor.owner.index ≥ checked.catalog.definitions.length
        | _ => false) "source invocation omitted allocation markers"
    | observation => throw (IO.userError s!"marked result did not succeed: {reprStr observation}")

example {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.Prepared checked) :
    Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base (Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.markedRepresentation checked prepared.fuel prepared.layouts
      (some ⟨prepared.base.sourceProgram, prepared.base.plan, prepared.views⟩))
      prepared.fuel = .ok prepared.secondPass.closures := prepared.secondPass.compiled

example {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.Prepared checked) :
    Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base (Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.discoveryRepresentation prepared.base prepared.fuel prepared.discovery (some prepared.views))
      prepared.fuel = .ok prepared.firstPass.closures := prepared.firstPass.compiled

private def manyRoots : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc"
    externalLibraries := []
    mainSources := [{
      path := "main.solc"
      content := String.intercalate "\n" ((List.range 40).map fun index =>
        "function root" ++ toString index ++ "() returns (Word) { return 7; }")}] }
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"many roots rejected: {reprStr error}")
  let plan ← match SourceSpecializationWorklist.run program
      (program.signatures.functions.map (fun signature => ⟨signature.id, []⟩)) 500 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"many roots plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 32 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"many roots base failed: {reprStr error}")
  let prepared ← match Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.prepare automatic.prepared 32 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"many roots marked failed: {reprStr error}")
  assertTrue (prepared.entries.length == 40) "source fuel incorrectly bounded the complete Core inventory"
  let completion ← match prepared.runSource (← key program "root39") [] 50000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"many roots run failed: {reprStr error}")
  match completion.result.native.observation with
  | .succeeded (.word value) _ => assertTrue (value == w 7) "many roots result changed"
  | observation => throw (IO.userError s!"many roots observation changed: {reprStr observation}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"marked fixture rejected: {reprStr error}")
  let names := ["local", "lazy", "choose", "capture", "recursive", "unused", "tuple", "looping", "absent", "getLocal", "useReturned"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"marked worklist failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic
    | .error error => throw (IO.userError s!"marked base factory failed: {reprStr error}")
  let prepared ← match Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"marked factory failed: {reprStr error}")
  assertTrue (prepared.entries.length == keys.length) "marked roots disappeared"
  assertTrue (!prepared.layouts.entries.isEmpty) "marked catalog is empty"
  assertTrue (prepared.layouts.definitions.take automatic.checked.catalog.definitions.length == automatic.checked.catalog.definitions)
    "marked suffix changed ambient definitions"
  runSuccess prepared (← key program "local") [.mapping .word .word [(.word (w 1), .word (w 9))]]
    (.mapping .word .word [(.word (w 1), .word (w 9))])
  runSuccess prepared (← key program "lazy") [] (.mapping .word .word [(.word (w 1), .word (w 7))])
  runSuccess prepared (← key program "capture") [.word (w 10)] (.word (w 17))
  runSuccess prepared (← key program "recursive") [.word (w 4)] (.word (w 4))
  runSuccess prepared (← key program "unused") [] (.word (w 7))
  runSuccess prepared (← key program "tuple") [.product (.word (w 13)) (.bool true)] (.word (w 13))
  runSuccess prepared (← key program "looping") [.word (w 4)] (.word (w 6))
  runSuccess prepared (← key program "useReturned") [.word (w 4)] (.word (w 9))
  let returned ← match prepared.runSource (← key program "getLocal") [.word (w 4)] 150000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"local view output failed: {reprStr error}")
  match returned.result.native.observation with
  | .succeeded value _ =>
      let parsed ← match SourceCoreCallableViewWrappers.parse? .word .word value with
        | some parsed => pure parsed | none => throw (IO.userError "local read omitted its exact view wrapper")
      let view ← match prepared.views.entryAt? parsed.view with
        | some view => pure view | none => throw (IO.userError "local read wrapper lost its cached view")
      assertTrue (view.view.owner == (← key program "getLocal")) "local wrapper authenticated a foreign owner"
      assertTrue view.view.wrapsPrincipal "local wrapper used monomorphic metadata"
      match parsed.original with
      | .pair (.pair (.inLeft .word .unit) (.closure ..)) (.word descriptor) =>
          assertTrue (descriptor == parsed.contract) "local wrapper changed its stage descriptor"
      | _ => throw (IO.userError "local wrapper changed its original anonymous carrier")
  | observation => throw (IO.userError s!"local view output changed: {reprStr observation}")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "marked Box missing")
  let constructor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "marked constructor missing")
  let instantiation : DataConstructorInstantiation := ⟨constructor.id, box.parameters.zip [.word], [.word], .nominal box.id [.word]⟩
  runSuccess prepared (← key program "choose") [.constructed instantiation [.word (w 7)]] (.word (w 7))
  let absent ← match prepared.runSource (← key program "absent") [] 150000 500 with
    | .ok completion => pure completion
    | .error error => throw (IO.userError s!"marked absent run failed: {reprStr error}")
  match absent.result.native.observation with
  | .failed reason store =>
      let diagnostic ← match absent.result.diagnostics.diagnostic? reason with
        | some diagnostic => pure diagnostic | none => throw (IO.userError "marked absent diagnostic missing")
      assertTrue diagnostic.span.isSome "marked absent span lost"
      assertTrue (!store.isEmpty) "marked failure lost allocations"
  | observation => throw (IO.userError s!"marked absent result changed: {reprStr observation}")
  manyRoots
  IO.println "actual compatible function compiler and shared allocation suffix GREEN"

end Tests.SourceCoreCompatibleMarkedFunctions
