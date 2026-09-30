import Solcore.Frontend.SourceCorePlanCatalog
import Solcore.Frontend.SourceCoreCompatibleDataExpressions

/-! Actual checked functions use compatible leaves through the common
contextual function compiler. Evidence, local instances and coercions share
the original plan and stage descriptors. Invocation evaluates cached Core. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleFunctions
open Solcore Solcore.Frontend SourceInference
abbrev DataValue := SourceCoreCompatibleValues.Value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<mapping(Word => Word)> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function local(table: mapping(Word => Word)) returns (mapping(Word => Word)) { let f = lam(item) { return keep(item); }; return f(table); }",
    "function alias(table: mapping(@Word => Word)) returns (Word) { let f = lam(item) { return item; }; let copied = f(table); return copied[@Word]; }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, mapping(Word => Word)> { function coerce(value: Bool) returns (mapping(Word => Word)) { let table: mapping(Word => Word); return table; } }",
    "function converted(flag: Bool) returns (mapping(Word => Word)) { return flag; }",
    "function marked(first: Bool, second: Bool) returns (Bool) { let copied: Bool = first; return second; }"
  ]}]
}

private def check (program : CheckedProgram) (name : String) (arguments : List DataValue)
    (expected : DataValue) (marked : Bool := false) : IO Unit := do
  let root ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"compatible function root missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program [⟨root.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"compatible worklist failed: {reprStr result}")
  let plan ← match SourceCompilationPlan.prepareExecutablePlanEvidence program plan with
    | .ok plan => pure plan
    | .error error => throw (IO.userError s!"compatible plan failed: {reprStr error}")
  let entries ← match SourceCompilationPlan.localLambdaCatalog plan with
    | .ok entries => pure entries
    | .error error => throw (IO.userError s!"compatible local discovery failed: {reprStr error}")
  let types := (SourceCorePlanCatalog.planTypes plan ++ entries.flatMap (fun entry =>
    SourceCorePlanCatalog.sourceTypes (entry.source.applySubstitution entry.substitution))).filter
      SourceCoreDataCatalog.closed |>.eraseDups
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 300 types with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"compatible catalog failed: {reprStr error}")
  let strict ← match SourceCoreDataCatalog.prepare program.signatures 300 types true with
    | .ok strict => pure strict
    | .error error => throw (IO.userError s!"diagnostic catalog failed: {reprStr error}")
  let context := SourceCoreCompatibleValues.Context.initial checked
  let reference := Core.OptionalCell.referenceType .bool
  let markerDefinitions : Core.DataEnvironment := [⟨[.unit]⟩, ⟨[reference]⟩,
    ⟨[.product reference reference]⟩]
  let allocate : SourceCoreSourceCells.Allocator := SourceCoreSourceCells.marked fun request =>
    pure ⟨⟨checked.catalog.definitions.length + request.scope.length⟩,
      SourceCoreSourceCells.captureType request.scope⟩
  let representation : SourceCoreGeneralFunctions.Representation := {
    expressions := {SourceCoreCompatibleDataExpressions.functionPolicy 300 context with
      sourceCells := if marked then some allocate else none}
    allowStaged := true
    loops := fun _ _ _ _ child => SourceCoreCompatibleDataExpressions.loopPolicy context child
  }
  let project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty := fun type =>
    (checked.project type).map (·.type) |>.mapError fun _ => .initializerMetadataMismatch ⟨⟨root.id, 0⟩⟩
  let locals ← match SourceCoreLocalPolymorphism.prepareWithProjection project plan with
    | .ok locals => pure locals
    | .error error => throw (IO.userError s!"compatible local projection failed: {reprStr error}")
  let functions ← match plan.specializations.reverse.mapM
      (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation) with
    | .ok functions => pure functions
    | .error error => throw (IO.userError s!"compatible signatures failed: {reprStr error}")
  let globals := functions.map (·.signature)
  let key : SourceSpecialization.SpecializationKey := ⟨root.id, []⟩
  let diagnostics ← match SourceCoreDataPlaceFaultSites.prepare strict program.signatures plan key with
    | .ok diagnostics => pure diagnostics
    | .error error => throw (IO.userError s!"compatible diagnostics failed: {reprStr error}")
  let table ← match SourceCoreStageCodebook.prepareWithProjection program plan project with
    | .ok table => pure table
    | .error error => throw (IO.userError s!"compatible descriptors failed: {reprStr error}")
  let callableDiagnostics ← match SourceCoreCallableFaultSites.prepare plan table diagnostics.rootTable with
    | .ok diagnostics => pure diagnostics
    | .error error => throw (IO.userError s!"compatible call diagnostics failed: {reprStr error}")
  let native : SourceCoreGeneralFunctions.CallableContext := ⟨table, callableDiagnostics⟩
  let locals ← match locals.withCallableContracts (fun caller initializer active =>
      table.idAt? (.lambda caller initializer active)) with
    | .ok locals => pure locals
    | .error error => throw (IO.userError s!"compatible local descriptors failed: {reprStr error}")
  let diagnostics := {diagnostics with rootTable := callableDiagnostics.rootTable}
  let closures ← match functions.mapM (SourceCoreGeneralFunctions.compileClosureWithRepresentation
      program representation program.signatures plan globals diagnostics locals (some native) 128) with
    | .ok closures => pure closures
    | .error error => throw (IO.userError s!"{name} compatible body failed: {reprStr error}")
  let function ← match functions.find? (·.signature.key == key) with
    | some function => pure function
    | none => throw (IO.userError "compatible compiled root missing")
  let mut inputContext := context
  let mut lowered := []
  for ((binder, type), argument) in function.inputs.zip arguments do
    let encoded ← match SourceCoreCompatibleValues.encode 300 inputContext binder.scheme.body argument with
      | .ok encoded => pure encoded
      | .error error => throw (IO.userError s!"compatible input failed: {reprStr error}")
    inputContext := encoded.context
    let literal ← match SourceCoreCompatibleDataExpressions.quote encoded.value with
      | some literal => pure literal
      | none => throw (IO.userError "compatible data input contained code")
    lowered := lowered ++ [⟨type, Core.LanguageResult.success literal⟩]
  let body ← match SourceCoreGeneralFunctions.assembleCall globals functions closures key
      (SourceCoreCalls.packArguments lowered) with
    | .ok body => pure body
    | .error error => throw (IO.userError s!"compatible assembly failed: {reprStr error}")
  let executable : Core.Program := ⟨Core.LanguageResult.resultType function.signature.resultType,
    body, checked.catalog.definitions ++ (if marked then markerDefinitions else [])⟩
  unless executable.check do throw (IO.userError s!"{name} failed actual compatible Core checker")
  for initialFuel in [0, 8, 65536] do
    let result := executable.runStateful initialFuel
    let result := match result with
      | .outOfFuel state => Core.runStateful 65536 state
      | result => result
    match Core.LanguageResult.observeResult result with
    | .succeeded value store =>
        let resultType := function.specialized.function.inferredBodyType
        let decoded ← match SourceCoreCompatibleValues.decode 300 inputContext resultType value with
          | .ok value => pure value
          | .error error => throw (IO.userError s!"compatible output failed: {reprStr error}")
        unless decoded == expected do throw (IO.userError s!"{name} compatible result changed: {reprStr decoded}")
        if marked then
          let marker := fun n captures => SourceCoreHeapMarkers.markerValue
            ⟨⟨checked.catalog.definitions.length + n⟩,
              if n = 0 then .unit else if n = 1 then reference else .product reference reference⟩ captures
          let expectedTail : List Core.Value := [marker 0 .unit, .inRight .unit (.bool false),
            marker 1 (.cellRef (Core.OptionalCell.cellType .bool) 2), .inRight .unit (.bool true),
            marker 2 (.pair (.cellRef (Core.OptionalCell.cellType .bool) 4)
              (.cellRef (Core.OptionalCell.cellType .bool) 2)), .inRight .unit (.bool false)]
          unless store.drop 1 == expectedTail do
            throw (IO.userError s!"marked root parameters captured temporary/global cells: {reprStr store}")
    | result => throw (IO.userError s!"{name} compatible execution failed: {reprStr result}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"compatible function fixture rejected: {reprStr error}")
  let w := fun n => Core.Word.ofNatModulo n
  let table : DataValue := .mapping .word .word [(.word (w 1), .word (w 7))]
  check program "local" [table] table
  check program "alias" [.mapping (.proxy (.comptime .word)) .word
    [(.proxy (.comptime .word), .word (w 7))]] (.word (w 0))
  check program "alias" [.mapping (.proxy .word) .word
    [(.proxy .word, .word (w 7))]] (.word (w 7))
  check program "converted" [.bool true] (.mapping .word .word [])
  check program "marked" [.bool false, .bool true] (.bool true) true
  IO.println "compatible general functions, qualified local evidence, coercions and resumed Core execution GREEN"

end Tests.SourceCoreCompatibleFunctions
