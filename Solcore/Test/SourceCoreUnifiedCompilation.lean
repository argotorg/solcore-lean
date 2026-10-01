import Solcore.Frontend.SourceCoreUnifiedCompilation
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreUnifiedCompilation.Compiled.mk

/-! Checked source programs exercise the prepared public Core adapter through
its complete result and source heap export, including genuine suspension and
resumption. Expected results come from the source fixture's visible behavior. -/
set_option autoImplicit false
namespace Tests.SourceCoreUnifiedCompilation
open Solcore Solcore.Frontend SourceInference
abbrev Compiled := Solcore.Frontend.SourceCoreUnifiedCompilation.Compiled
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Key := SourceSpecialization.SpecializationKey

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

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
    "function absent() returns (Word) { let absent: Word; return absent; }",
    "function getLocal(start: Word) returns (function(Word) returns (Word)) { let value = start; let f = lam(item) { value += 1; return item; }; return f; }",
    "function useReturned(start: Word) returns (Word) { let f = getLocal(start); return f(9); }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, Word> { function coerce(value: Bool) returns (Word) { let table: mapping(Word => Word); table[0] = value ? 40 : 6; table[0] += 2; return table[0]; } }",
    "function converted(value: Bool) returns (Word) { return value; }",
    "function integerValue(value: integer) returns (integer) { return value + 1; }",
    "function failAfterWrite() returns (Word) { let captured: Word = 1; let fail = lam() -> Word { captured += 2; let missing: Word; return missing; }; return fail(); }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"unified fixture missing {name}")

private def initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, none⟩]}

private def check (compiled : Compiled) (owner : Key) (arguments : List SourceValue)
    (expected : SourceValue) : IO Unit := do
  for spent in [0, 37, 150000] do
    let first ← get "unified Core run" (compiled.run owner arguments 500 spent initial)
    assertTrue first.execution.isSome "valid unified invocation omitted its native receipt"
    if spent == 0 then
      match first.observation with
      | .outOfFuel state => assertTrue (reprStr state == reprStr initial) "zero fuel changed initial source prefix"
      | result => throw (IO.userError s!"zero fuel did not suspend: {reprStr result}")
    let final ← get "unified Core resume" (Solcore.Frontend.SourceCoreUnifiedCompilation.Result.resume first 150000)
    match final.observation with
    | .done actual state =>
      assertTrue (reprStr actual == reprStr expected) s!"unified result changed: {reprStr actual}"
      assertTrue (reprStr (state.heap.take initial.heap.length) == reprStr initial.heap)
        "unified execution changed the inert source prefix"
    | result => throw (IO.userError s!"unified execution did not complete: {reprStr result}")

example (compiled : Compiled) :
    SourceCoreCompatibleFunctions.prepare compiled.sourceProgram compiled.validationPlan compiled.compilationFuel =
      .ok compiled.compatible := compiled.compatiblePrepared
example (compiled : Compiled) : SourceCoreUnifiedRuntime.prepare compiled.indexed = .ok compiled.runtime :=
  compiled.runtimePrepared

def run : IO Unit := do
  let program ← get "unified checking" (checkProgram workspace)
  let names := ["local", "lazy", "choose", "capture", "recursive", "unused", "tuple", "looping",
    "absent", "getLocal", "useReturned", "converted", "integerValue", "failAfterWrite"]
  let roots ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (roots.map fun root => ⟨root.declaration, []⟩) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"unified worklist failed: {reprStr other}")
  let compiled ← get "unified preparation" (Solcore.Frontend.SourceCoreUnifiedCompilation.prepare program plan 500)
  assertTrue (compiled.keys == roots) "unified factory changed root order"
  let mapping : SourceValue := .mapping .word .word [(.word (w 1), .word (w 9))]
  check compiled (← key program "local") [mapping] mapping
  check compiled (← key program "lazy") [] (.mapping .word .word [(.word (w 1), .word (w 7))])
  check compiled (← key program "capture") [.word (w 10)] (.word (w 17))
  check compiled (← key program "recursive") [.word (w 4)] (.word (w 4))
  check compiled (← key program "unused") [] (.word (w 7))
  check compiled (← key program "tuple") [.product (.word (w 13)) (.bool true)] (.word (w 13))
  check compiled (← key program "looping") [.word (w 4)] (.word (w 6))
  check compiled (← key program "useReturned") [.word (w 4)] (.word (w 9))
  check compiled (← key program "converted") [.bool true] (.word (w 42))
  check compiled (← key program "converted") [.bool false] (.word (w 8))
  check compiled (← key program "integerValue") [.integer (-3)] (.integer (-2))
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "unified Box missing")
  let constructor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "unified constructor missing")
  let instantiation : DataConstructorInstantiation := ⟨constructor.id, box.parameters.zip [.word], [.word], .nominal box.id [.word]⟩
  check compiled (← key program "choose") [.constructed instantiation [.word (w 7)]] (.word (w 7))
  for name in ["absent", "failAfterWrite"] do
    let result ← get "unified language failure" (compiled.run (← key program name) [] 500 150000 initial)
    match result.observation with
    | .fault (.uninitializedLocal _) state =>
      assertTrue (initial.heap.length < state.heap.length) "language failure lost its source allocations"
      if name == "failAfterWrite" then
        assertTrue (state.heap.any fun cell => match cell.value with
          | some (.word value) => value == w 3 | _ => false) "language failure lost the captured write"
    | other => throw (IO.userError s!"unified language failure changed: {reprStr other}")
  IO.println "cached unified Core artifact, complete source observations and resumptions GREEN"

end Tests.SourceCoreUnifiedCompilation
