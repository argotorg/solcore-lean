import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataInputs
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicDataInputs
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicDataInputs

theorem actual_start_inputs {artifact : Artifact} (session : Session artifact)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact}
    (accepted : session.start key arguments fuel = .ok checkpoint)
    (data : ∀ argument ∈ arguments, DataPublic argument) : checkpoint.DataInputs session key arguments :=
  (Session.start_root_receipt session accepted).data_inputs data

abbrev same_start_inputs := @RecursiveNamedPublicDataInputs.StartAt.data_inputs
abbrev actual_source_arguments := @RecursiveNamedPublicDataInputs.StartAt.data_arguments

/-- These raw metadata fields and duplicate entries are independent syntax.
Source representation additionally requires the real accepted encoding. -/
theorem raw_mapping_meaning (first second : Word) :
    Means (.mapping (.proxy (.comptime .word)) (.comptime .word)
      [(.proxy (.comptime .word), .word first), (.proxy (.comptime .word), .word second)])
      (.mapping (.proxy (.comptime .word)) (.comptime .word)
        [(.proxy (.comptime .word), .word first), (.proxy (.comptime .word), .word second)]) :=
  ⟨_, by simp [DataInput.publicValue, DataInput.publicEntries], .mapping (.prepend (.proxy _) (.word _) (.prepend (.proxy _) (.word _) .empty))⟩

theorem raw_constructor_meaning (metadata : DataConstructorInstantiation) (inner : TypeSystem.Ty) :
    Means (.constructed metadata [.proxy inner]) (.constructed metadata [.proxy inner]) :=
  ⟨_, by simp [DataInput.publicValue, DataInput.publicValues], .constructed (.cons (.proxy _) .nil)⟩

theorem raw_nested_product (metadata : DataConstructorInstantiation) (inner : TypeSystem.Ty) (value : Word) :
    Means (.product (.constructed metadata [.proxy inner]) (.mapping .word .word [(.word value, .word value)]))
      (.product (.constructed metadata [.proxy inner]) (.mapping .word .word [(.word value, .word value)])) :=
  ⟨_, by simp [DataInput.publicValue, DataInput.publicValues, DataInput.publicEntries], .product (.constructed (.cons (.proxy _) .nil)) (.mapping (.prepend (.word _) (.word _) .empty))⟩

theorem handle_boundary (handle : SourceCorePublicValues.Handle) : ¬ DataPublic (.function handle) := by
  intro related
  obtain ⟨carrier, image⟩ := related
  cases carrier <;> simp [DataInput.publicValue] at image

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (value : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "enum Box<T> { Put(T) }",
  "function box(value: Box<@Word>) returns (Box<@Word>) { return value; }",
  "function proxy(value: @Word) returns (@Word) { return value; }",
  "function alias(value: mapping(@Word => Word)) returns (mapping(@Word => Word)) { return value; }",
  "function lookup(value: mapping(Word => Word), key: Word) returns (Word) { return value[key]; }",
  "function nested(value: mapping(Word => mapping(Word => Word))) returns (mapping(Word => mapping(Word => Word))) { return value; }",
  "function fault(value: mapping(Word => Word)) returns (Word) { let prior = value; let missing: Word; return missing; }"
]

private def cells {artifact : Artifact} (session : Session artifact)
    (expected : List (TypeSystem.Ty × Option SourceCorePublicValues.Value)) : IO Unit := do
  let snapshot ← get "data input full heap" (← session.snapshot)
  let actual := snapshot.cells.map fun cell =>
    (cell.type, cell.value.map fun value => match value with
      | .data value => some value
      | _ => none)
  require (reprStr actual == reprStr (expected.map fun (type, value) => (type, value.map some)))
    s!"data input ordered heap changed: {reprStr actual}"
  require session.installedGlobalsPresent "data input run lost installed globals"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "actual public data inputs" content
    ["box", "proxy", "alias", "lookup", "nested", "fault"]
  let recipe ← get "data input recipe" (Recipe.prepare compiled)
  let artifact ← recipe.open
  let boot ← artifact.bootstrapFresh
  let initial ← match boot.resume 300000 with
    | .ready session => pure session
    | .error error => throw (IO.userError s!"data bootstrap: {reprStr error}")
    | .outOfFuel _ => throw (IO.userError "data bootstrap exhausted")
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  let box ← match compiled.sourceProgram.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "public input Box missing")
  let constructor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "public input Put missing")
  let inner := TypeSystem.Ty.proxy (.comptime .word)
  let substitution : TypeSystem.ParameterSubstitution := box.parameters.zip [inner]
  let rawType := TypeSystem.Ty.nominal box.id [inner]
  let metadata : DataConstructorInstantiation := {
    constructor := constructor.id, parameterSubstitution := substitution,
    payloadTypes := constructor.payloadTypes.map substitution.apply, resultType := rawType }
  let boxed : SourceCorePublicValues.Value := .constructed metadata [.proxy (.comptime .word)]
  let duplicate : SourceCorePublicValues.Value := .mapping (.comptime .word) (.comptime .word)
    [(word 1, word 7), (word 1, word 9), (word 2, word 11)]
  let aliases : SourceCorePublicValues.Value := .mapping (.proxy (.comptime .word)) (.comptime .word)
    [(.proxy (.comptime .word), word 13), (.proxy (.comptime .word), word 17), (.proxy .word, word 19)]
  let nested : SourceCorePublicValues.Value := .mapping (.comptime .word)
    (.mapping (.comptime .word) (.comptime .word)) [(word 3, duplicate), (word 3, .mapping .word .word [])]
  let boxType := TypeSystem.Ty.nominal box.id [.proxy .word]
  let successes : List (String × List SourceCorePublicValues.Value × SourceCorePublicValues.Value ×
      List (TypeSystem.Ty × Option SourceCorePublicValues.Value)) := [
    ("box", [boxed], boxed, [(boxType, some boxed)]),
    ("proxy", [.proxy (.comptime .word)], .proxy (.comptime .word), [(.proxy .word, some (.proxy (.comptime .word)))]),
    ("alias", [aliases], aliases, [(.mapping (.proxy .word) .word, some aliases)]),
    ("lookup", [duplicate, word 1], word 7, [(.mapping .word .word, some duplicate), (.word, some (word 1))]),
    ("lookup", [duplicate, word 19], word 0, [(.mapping .word .word, some duplicate), (.word, some (word 19))]),
    ("nested", [nested], nested, [(.mapping .word (.mapping .word .word), some nested)])]
  for fuel in [0, 1, 31, 300000] do
    for (name, arguments, expected, heap) in successes do
      let checkpoint ← get "actual data public start" (initial.start (← key name) arguments)
      let first ← checkpoint.resume fuel
      let finished ← match first with
        | .outOfFuel checkpoint => checkpoint.resume 300000
        | result => pure result
      match finished with
      | .succeeded completion =>
        require (completion.value == expected) "public data result, raw metadata or duplicate order changed"
        cells completion.session heap
      | _ => throw (IO.userError "public data success did not complete")
    let checkpoint ← get "actual data fault start" (initial.start (← key "fault") [duplicate])
    let first ← checkpoint.resume fuel
    let finished ← match first with
      | .outOfFuel checkpoint => checkpoint.resume 300000
      | result => pure result
    match finished with
    | .failed _ session =>
      cells session [(.mapping .word .word, some duplicate), (.mapping .word .word, some duplicate), (.word, none)]
    | _ => throw (IO.userError "public data fault did not complete")
  require (initial.start (← key "box") [.constructed {metadata with payloadTypes := [.word]} [word 1]]).toOption.isNone
    "public input accepted altered raw constructor metadata"
  require (initial.start (← key "alias") [.mapping .word .word [(word 1, word 2)]]).toOption.isNone
    "public input accepted wrong mapping key metadata"
  require (initial.start (← key "lookup") [duplicate, .bool false]).toOption.isNone
    "public input accepted wrong scalar kind after metadata encoding"
  IO.println "actual public data encoding / raw constructor and proxy metadata / ordered mappings and defaults / full heap / fault and resume GREEN"

end Tests.SourceCoreRecursiveNamedPublicDataInputs
