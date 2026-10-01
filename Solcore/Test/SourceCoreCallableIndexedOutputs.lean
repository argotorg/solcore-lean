import Solcore.Frontend.SourceCoreCallableIndexedOutputs
import Solcore.Frontend.SourceCoreCallableIndexedCellHeaders
import Solcore.Frontend.SourceCoreCallableIndexedHeapOutputs
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableIndexedOutputs.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedOutputs.Located.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedOutputs.Leaf.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedOutputs.Success.mk

set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedOutputs
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev SourceValue := SourceTypedRuntime.Value
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "enum Holder { Hold(Word, F) }",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function tuple(seed: Word) returns (F, F) { let f = lam(item) { keep(item); seed += 1; return seed; }; return (f, f); }",
    "function nominal(seed: Word) returns (Holder) { let f = lam(item) { keep(item); seed += 1; return seed; }; return .Hold(7, f); }",
    "function mappingReturn(value: mapping(Word => F), seed: Word) returns (mapping(Word => F)) { let f = lam(item) { keep(item); seed += 1; return seed; }; value[4] = f; return value; }",
    "function plain(seed: Word) returns (Word, Bool) { return (seed, true); }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"deep output fixture missing {name}")
private structure Projected (checked : SourceCoreCompatibleCatalog.Checked)
    (source : TypeSystem.Ty) (native : Core.Ty) : Type where
  eq : checked.catalog.project source = .ok native
private def initial : List SourceTypedRuntime.Cell := [⟨.word, none⟩, ⟨.function .word .word, none⟩]
private def prefixMatches (heap : List SourceTypedRuntime.Cell) : Bool :=
  reprStr (heap.take initial.length) == reprStr initial

private def closure (plan : SourceSpecializationWorklist.Plan) (value : SourceValue) : IO SourceTypedRuntime.Environment := do
  match value with
  | .instantiated substitution witnesses (.closure parameters _ _ _ _ captured _) =>
    assertTrue (!substitution.isEmpty && witnesses.length == 1) "deep output lost its actual read witnesses"
    assertTrue (parameters.any (fun binder => !binder.scheme.body.freeVariables.isEmpty)) "deep output specialized its raw original header"
    assertTrue (value.type? plan == some (.function .word .word)) "deep closure restored runtime type changed"
    assertTrue (captured.all (fun binding => initial.length ≤ binding.2.index)) "deep closure referenced opaque source prefix"
    pure captured
  | _ => throw (IO.userError "deep output lost instantiated original closure")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"deep output source rejected: {reprStr error}")
  let roots ← ["tuple", "nominal", "mappingReturn", "plain", "inc"].mapM (key program)
  let requests := roots.map fun owner =>
    (⟨owner.declaration, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program requests 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"deep output worklist failed: {reprStr other}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"deep output base failed: {reprStr error}")
  let native ← match SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500 with
    | .ok native => pure native | .error error => throw (IO.userError s!"deep output native preparation failed: {reprStr error}")
  let output ← match SourceCoreCallableIndexedOutputs.prepare native with
    | .ok output => pure output | .error error => throw (IO.userError s!"deep output caches failed: {reprStr error}")
  let cellHeaders ← match SourceCoreCallableIndexedCellHeaders.prepare (program := native) output.graph with
    | .ok headers => pure headers | .error error => throw (IO.userError s!"raw source cell headers failed: {reprStr error}")
  let heapOutput ← match SourceCoreCallableIndexedHeapOutputs.prepare native with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"heap output preparation failed: {reprStr error}")
  let inc ← key program "inc"
  let mapping : SourceValue := .mapping .word (.comptime (.function .word .word))
    [(.word (w 4), .global inc []), (.word (w 4), .global inc [])]
  let fixtures : List (String × List SourceValue) :=
    [("tuple", [.word (w 3)]), ("nominal", [.word (w 3)]),
     ("mappingReturn", [mapping, .word (w 3)]), ("plain", [.word (w 3)])]
  for (name, arguments) in fixtures do
    for budget in [0, 29, 100000] do
      let checkpoint ← match native.runSource (← key program name) arguments budget 500 with
        | .ok completion => pure completion
        | .error error => throw (IO.userError s!"deep output native call failed: {reprStr error}")
      if budget == 0 then
        let early ← match SourceCoreCallableIndexedHeapOutputs.exportHeap heapOutput checkpoint initial with
          | .ok exported => pure exported | .error error => throw (IO.userError s!"early heap export failed: {reprStr error}")
        assertTrue (early.heap.length == initial.length && prefixMatches early.heap) "zero-fuel export changed opaque source prefix"
      let completion := checkpoint.resume 100000
      let projected ← match same : automatic.checked.catalog.project completion.entry.sourceResultType with
        | .error error => throw (IO.userError s!"deep output projection failed: {reprStr error}")
        | .ok type =>
          if equal : type = completion.entry.native.resultType then
            pure (show Projected automatic.checked completion.entry.sourceResultType completion.entry.native.resultType from
              ⟨by simpa only [equal] using same⟩)
          else throw (IO.userError "deep output native result type changed")
      let decoded ← match SourceCoreCallableIndexedOutputs.decodeSuccess output completion completion.entry.sourceResultType
          projected.eq initial 1024 with
        | .ok decoded => pure decoded | .error error => throw (IO.userError s!"deep source output failed: {reprStr error}")
      for row in decoded.ledger.ledger.rows do
        let selected ← match SourceCoreCallableIndexedCellHeaders.select cellHeaders row with
          | .ok selected => pure selected | .error error => throw (IO.userError s!"raw allocation header selection failed: {reprStr error}")
        assertTrue (selected.header.raw.binder.id == row.entry.key.binder.id) "raw source cell header changed binder identity"
      let exported ← match SourceCoreCallableIndexedHeapOutputs.exportHeap heapOutput completion initial with
        | .ok exported => pure exported | .error error => throw (IO.userError s!"paired source heap export failed: {reprStr error}")
      assertTrue (prefixMatches exported.heap) "heap export changed opaque source prefix"
      assertTrue (exported.cells.length == decoded.ledger.ledger.rows.length) "heap export lost source allocation order"
      let genericRows := decoded.ledger.ledger.rows.filter (fun row => !row.entry.key.binder.scheme.quantified.isEmpty)
      if name != "plain" then
        assertTrue (!genericRows.isEmpty) "generic closure fixture no longer records a principal"
      for row in genericRows do
        match exported.heap[row.sourceLocation.index]? with
        | some ⟨_, some (.closure parameters _ _ _ _ captured _)⟩ =>
          assertTrue (parameters.any (fun binder => !binder.scheme.body.freeVariables.isEmpty)) "heap export specialized original principal"
          assertTrue (captured == row.environment) "heap export changed principal capture order or aliases"
        | _ => throw (IO.userError "heap export lost raw generic principal closure")
      match name, decoded.decoded.source with
      | "tuple", .product left right =>
        let leftEnv ← closure plan left
        let rightEnv ← closure plan right
        assertTrue (leftEnv == rightEnv && leftEnv.length == 1) "deep tuple split the shared seed cell"
      | "nominal", .constructed _ [.word number, value] =>
        assertTrue (number == w 7) "nominal data changed alongside closure restoration"
        assertTrue ((← closure plan value).length == 1) "nominal closure lost source capture"
      | "mappingReturn", .mapping keyType valueType [(.word first, left), (.word second, .global owner _)] =>
        assertTrue (keyType == .word && valueType == .comptime (.function .word .word)) "deep mapping raw metadata changed"
        assertTrue (first == w 4 && second == w 4 && owner == inc) "deep mapping duplicate order changed"
        assertTrue ((← closure plan left).length == 2) "deep mapping closure lost value/seed captures"
      | "plain", .product (.word number) (.bool flag) => assertTrue (number == w 3 && flag) "data-only output changed"
      | _, value => throw (IO.userError s!"unexpected deep source output {name}: {reprStr value}")
      match SourceCoreCallableIndexedOutputs.locate completion decoded.ledger (.word (w 987654321)) with
      | .error .unavailableValue => pure () | _ => throw (IO.userError "foreign value gained native result/payload provenance")
  let hidden := Core.Value.cellRef .word 42
  let carrier := Core.Value.closure .unit .unit .unit [hidden]
  assertTrue (SourceCoreCallableNativeSubvalues.find hidden carrier |>.isNone) "public native path entered a closure environment"
  IO.println "deep indexed tuple/nominal/mapping closure outputs, raw metadata and native data origins GREEN"

end Tests.SourceCoreCallableIndexedOutputs
