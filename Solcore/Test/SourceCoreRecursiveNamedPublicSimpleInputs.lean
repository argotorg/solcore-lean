import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputs
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicSimpleInputs
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open GeneralHeap ReadOnly CompatiblePayload RecursiveNamedPublicSimpleInputs

theorem actual_start_inputs {artifact : Artifact} (session : Session artifact)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact}
    (accepted : session.start key arguments fuel = .ok checkpoint)
    (simple : ∀ argument ∈ arguments, SimplePublic argument) :
    checkpoint.SimpleInputs session key arguments :=
  (Session.start_root_receipt session accepted).simple_inputs simple

abbrev same_start_inputs := @RecursiveNamedPublicSimpleInputs.StartAt.simple_inputs
abbrev actual_source_arguments := @RecursiveNamedPublicSimpleInputs.StartAt.simple_arguments

/-- Expected type erasure keeps the original raw input type in the receipt. -/
theorem raw_word_view (value : Word) :
    SimpleInput (.comptime .word) (.word value) (.word value) := .word value rfl

theorem nested_order (word : Word) (flag : Bool) (integer : Int) :
    SimpleInput (.product .word (.product .bool .integer))
      (.product (.word word) (.product (.bool flag) (.integer integer)))
      (.pair (.word word) (.pair (.bool flag) (.integer integer))) :=
  .product rfl (.word word rfl) (.product rfl (.bool flag rfl) (.integer integer rfl))

theorem preserves_distinct_scalar_kind (value : Word) :
    ¬ SimpleInput .word (.bool false) (.word value) := by
  intro related
  cases related

theorem handle_boundary (handle : SourceCorePublicValues.Handle) :
    ¬ SimplePublic (.function handle) := by intro simple; cases simple

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (value : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "function mixed(a: Word, b: integer, gate: Bool) returns ((Word, integer)) { return (gate ? a : a + 1, b); }",
  "function echo(value: (Word, (Bool, integer))) returns ((Word, (Bool, integer))) { return value; }",
  "function fault(n: Word, pair: (Bool, integer)) returns (Word) { let prior = n; let missing: Word; return missing; }"
]

private def cells {artifact : Artifact} (session : Session artifact)
    (expected : List (TypeSystem.Ty × Option SourceCorePublicValues.Value)) : IO Unit := do
  let snapshot ← get "simple input full heap" (← session.snapshot)
  let actual := snapshot.cells.map fun cell =>
    (cell.type, cell.value.map fun value => match value with
      | .data value => some value
      | _ => none)
  require (reprStr actual == reprStr (expected.map fun (type, value) => (type, value.map some)))
    s!"simple input ordered heap changed: {reprStr actual}"
  require session.installedGlobalsPresent "public input run lost installed globals"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "actual public simple inputs" content ["mixed", "echo", "fault"]
  let recipe ← get "simple input recipe" (Recipe.prepare compiled)
  let artifact ← recipe.open
  let boot ← artifact.bootstrapFresh
  let initial ← match boot.resume 300000 with
    | .ready session => pure session
    | .error error => throw (IO.userError s!"simple bootstrap: {reprStr error}")
    | .outOfFuel _ => throw (IO.userError "simple bootstrap exhausted")
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  let huge : Int := -(2^130 + 71)
  let nested := SourceCorePublicValues.Value.product (word 29) (.product (.bool false) (.integer huge))
  let successes : List (String × List SourceCorePublicValues.Value × SourceCorePublicValues.Value ×
      List (TypeSystem.Ty × Option SourceCorePublicValues.Value)) := [
    ("mixed", [word 13, .integer huge, .bool true], .product (word 13) (.integer huge),
      [(.word, some (word 13)), (.integer, some (.integer huge)), (.bool, some (.bool true))]),
    ("mixed", [word 17, .integer 73, .bool false], .product (word 18) (.integer 73),
      [(.word, some (word 17)), (.integer, some (.integer 73)), (.bool, some (.bool false))]),
    ("echo", [nested], nested, [(.product .word (.product .bool .integer), some nested)])]
  for fuel in [0, 1, 31, 300000] do
    for (name, arguments, expected, heap) in successes do
      let checkpoint ← get "actual simple public start" (initial.start (← key name) arguments)
      let first ← checkpoint.resume fuel
      let finished ← match first with
        | .outOfFuel checkpoint => checkpoint.resume 300000
        | result => pure result
      match finished with
      | .succeeded completion =>
        require (completion.value == expected) "simple public result or argument order changed"
        cells completion.session heap
      | _ => throw (IO.userError "simple public success did not complete")
    let checkpoint ← get "actual simple fault start" (initial.start (← key "fault") [word 37, .product (.bool true) (.integer huge)])
    let first ← checkpoint.resume fuel
    let finished ← match first with
      | .outOfFuel checkpoint => checkpoint.resume 300000
      | result => pure result
    match finished with
    | .failed _ session =>
      cells session [(.word, some (word 37)), (.product .bool .integer, some (.product (.bool true) (.integer huge))),
        (.word, some (word 37)), (.word, none)]
    | _ => throw (IO.userError "simple public language fault did not complete")
  require (initial.start (← key "mixed") [.bool true, .integer 3, .bool false]).toOption.isNone
    "public encoder accepted Bool in the Word position"
  require (initial.start (← key "mixed") [word 3, .integer 5]).toOption.isNone
    "public encoder accepted missing final argument"
  IO.println "actual public scalar/product encoding / ordered source inputs / full heap / fault and resume GREEN"

end Tests.SourceCoreRecursiveNamedPublicSimpleInputs
