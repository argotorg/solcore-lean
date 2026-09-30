import Solcore.Frontend.SourceCoreGeneralEntry
import Solcore.Core.LocalSequence

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.Value

set_option autoImplicit false

namespace Tests.SourceCoreGeneralEntry

open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceCoreGeneralEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree { Leaf(integer), Pair(Tree, Tree) }",
    "function keepTree(value: Tree) returns (Tree) { return value; }",
    "function keepMap(value: mapping(integer => Tree)) returns (mapping(integer => Tree)) { return value; }",
    "function keepProxy(value: @Word) returns (@Word) { return value; }",
    "function keepScalar(value: (integer, (Word, Bool))) returns (integer, (Word, Bool)) { return value; }",
    "function pack(first: Tree, second: mapping(integer => Tree), third: @Word) returns (Tree, (mapping(integer => Tree), @Word)) { return (first, (second, third)); }",
    "function absent(value: Tree) returns (Tree) { let missing: Tree; return missing; }",
    "function make(value: Tree) returns (function() returns (Tree)) { return lam() -> Tree { return value; }; }",
    "function keepFunction(value: function() returns (Tree)) returns (function() returns (Tree)) { return value; }",
    "function staged(comptime value: Word) returns (Word) { return value; }"
  ] }]
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"general entry function missing: {name}")

private def planFor (program : CheckedProgram) (names : List String) : IO Plan := do
  let requests ← names.mapM (request program)
  match SourceSpecializationWorklist.run program requests 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"general entry plan failed: {reprStr result}")

private def sites {checked : Checked} (request : BodyRequest checked) : Except String SourceCoreFaultSites.Table :=
  (SourceCoreFaultSites.prepare request.specialized.function.typedBody request.sourceResultType).mapError reprStr

/-- These small callbacks exercise the entry boundary. They are not an
alternative general source interpreter or a claim of full body lowering. -/
private def identityLowerer {checked : Checked} : BodyLowerer checked String := fun _ request => do
  pure ⟨OptionalCell.read request.result.type (.var 0) Word.zero, ← sites request⟩

private def packLowerer {checked : Checked} : BodyLowerer checked String := fun _ request => do
  let [first, second, third] := request.inputs | throw "expected three inputs"
  pure ⟨LocalSequence.pair first.type (.product second.type third.type)
    (OptionalCell.read first.type (.var 2) Word.zero)
    (LocalSequence.pair second.type third.type
      (OptionalCell.read second.type (.var 1) Word.zero)
      (OptionalCell.read third.type (.var 0) Word.zero)), ← sites request⟩

private def absentLowerer {checked : Checked} : BodyLowerer checked String := fun _ request => do
  let sites ← sites request
  let [site] := sites.reads | throw "expected one uninitialized read"
  pure ⟨.letE (OptionalCell.allocate request.result.type)
    (OptionalCell.read request.result.type (.var 0) site.reason), sites⟩

private def closureLowerer {checked : Checked} : BodyLowerer checked String := fun _ request => do
  let [input] := request.inputs | throw "expected one input"
  pure ⟨LanguageResult.success (TaggedFunction.anonymous
    (.lambda .unit (LanguageResult.resultType input.type)
      (OptionalCell.read input.type (.var 1) Word.zero))), ← sites request⟩

private def compilePlan (program : CheckedProgram) (checked : Checked) (names : List String)
    (lowerer : BodyLowerer checked String) : IO (PreparedProgram checked) := do
  let plan ← planFor program names
  match prepare program plan checked 100 lowerer with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"general entry preparation failed: {reprStr error}")

private def firstEntry {checked : Checked} (prepared : PreparedProgram checked) : IO (Entry checked) :=
  match prepared.entries with
  | first :: _ => pure first
  | [] => throw (IO.userError "general seed entry missing")

private def invoke {checked : Checked} (entry : Entry checked) (arguments : List Value) (fuel : Nat := 10000) :
    IO (Result (definitions checked) entry.resultType) :=
  match entry.run arguments fuel with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"general entry input rejected: {reprStr error}")

private def rejectedInput {checked : Checked} (entry : Entry checked) (arguments : List Value) : IO RunError :=
  match entry.start arguments with
  | .error error => pure error
  | .ok _ => throw (IO.userError "invalid general entry input was accepted")

private def present (value : Value) : Value := .inRight .unit value

example (definitions : DataEnvironment) (world : StoreTyping) (value : Value) (type : Core.Ty)
    (accepted : ValidatedValue definitions value type) : RuntimeValueHasType world value type definitions :=
  accepted.typed world

example {checked : Checked} (entry : Entry checked) (result : Result (definitions checked) entry.resultType)
    {value : Value} {store : Store} (completed : result.observation = .succeeded value store) :
    ∃ world, RuntimeStoreHasTypes world store (definitions checked) ∧
      RuntimeValueHasType world value entry.resultType (definitions checked) :=
  result.success_typed completed

example {definitions : DataEnvironment} {type : Core.Ty}
    (checkpoint next : Checkpoint definitions type) (spent additional : Nat)
    (suspended : runStateful spent checkpoint.state = .outOfFuel next.state) :
    (next.resume additional).observation = (checkpoint.resume (spent + additional)).observation :=
  checkpoint.resume_after_exhaustion next spent additional suspended

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"general entry source fixture rejected: {reprStr errors}")
  let signature ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some signature => pure signature
    | none => throw (IO.userError "Tree signature missing")
  let treeType := TypeSystem.Ty.nominal signature.id []
  let mappingType := TypeSystem.Ty.mapping .integer treeType
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 100
      [treeType, mappingType, .proxy .word] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"general entry catalog failed: {reprStr error}")
  let treeId := (checked.catalog.identity? treeType).getD ⟨999⟩
  let mapId := (checked.catalog.identity? mappingType).getD ⟨999⟩
  let proxyId := (checked.catalog.identity? (.proxy .word)).getD ⟨999⟩
  let leaf := fun value => Value.constructed ⟨treeId, 0⟩ (.integer value)
  let tree := Value.constructed ⟨treeId, 1⟩ (.pair (leaf (-(2 ^ 300))) (leaf 7))
  let mapping := Value.constructed ⟨mapId, 1⟩
    (.pair (.pair (.integer (-8)) tree) (.constructed ⟨mapId, 0⟩ .unit))
  let proxy := Value.constructed ⟨proxyId, 0⟩ .unit
  let scalar := Value.pair (.integer (2 ^ 400)) (.pair (.word Word.zero) (.bool false))
  let prepared ← compilePlan program checked ["keepTree", "keepMap", "keepProxy", "keepScalar", "keepTree"] identityLowerer
  assertTrue (prepared.entries.map (·.key) == prepared.plan.seedKeys) "general entry changed seed order/duplicates"
  for (entry, argument) in prepared.entries.zip [tree, mapping, proxy, scalar, tree] do
    let result ← invoke entry [argument]
    assertTrue (result.observation == .succeeded argument [present argument]) "deep input/output carrier changed"
  let treeEntry ← firstEntry prepared
  let again ← invoke treeEntry [leaf 42]
  assertTrue (again.observation == .succeeded (leaf 42) [present (leaf 42)]) "cached entry reused input state"

  let packed ← firstEntry (← compilePlan program checked ["pack"] packLowerer)
  let arguments := [tree, mapping, proxy]
  let initial ← match packed.start arguments with
    | .ok initial => pure initial
    | .error error => throw (IO.userError s!"packed inputs rejected: {reprStr error}")
  assertTrue (initial.state.store == arguments.map present) "input allocation order changed"
  assertTrue (initial.state.control == .eval packed.body [
    .cellRef (OptionalCell.cellType (.namedData proxyId)) 2,
    .cellRef (OptionalCell.cellType (.namedData mapId)) 1,
    .cellRef (OptionalCell.cellType (.namedData treeId)) 0]) "input environment lost newest-first identity"
  let result ← invoke packed arguments
  assertTrue (result.observation == .succeeded (.pair tree (.pair mapping proxy)) (arguments.map present))
    "packed general outputs changed"
  let paused := initial.resume 5
  let next ← match paused.checkpoint? with
    | some next => pure next
    | none => throw (IO.userError "general execution did not retain a typed checkpoint")
  assertTrue ((next.resume 9995).observation == result.observation) "general checkpoint resume changed result/store"

  let malformed := Value.constructed ⟨treeId, 1⟩ (.pair (leaf 1) (.constructed ⟨treeId, 0⟩ (.bool true)))
  let rejected ← rejectedInput treeEntry [malformed]
  match rejected with
  | .input 0 error =>
    assertTrue (decide (error.path = [.constructorPayload, .pairRight, .constructorPayload]))
      "deep malformed payload path was lost"
  | _ => throw (IO.userError "deep malformed payload had wrong error")
  let mapEntry ← match prepared.entries[1]? with
    | some entry => pure entry
    | none => throw (IO.userError "mapping entry missing")
  discard <| rejectedInput mapEntry [.constructed ⟨mapId, 1⟩
    (.pair (.pair (.bool true) tree) (.constructed ⟨mapId, 0⟩ .unit))]
  discard <| rejectedInput mapEntry [.constructed ⟨mapId, 1⟩
    (.pair (.pair (.integer 5) tree) (leaf 0))]
  let proxyEntry ← match prepared.entries[2]? with
    | some entry => pure entry
    | none => throw (IO.userError "proxy entry missing")
  discard <| rejectedInput proxyEntry [.constructed ⟨proxyId, 0⟩ (.integer 0)]
  discard <| rejectedInput treeEntry [.constructed ⟨treeId, 9⟩ .unit]
  discard <| rejectedInput treeEntry [proxy]
  discard <| rejectedInput treeEntry []
  discard <| rejectedInput treeEntry [tree, tree]
  for forbidden in [Value.closure .unit .unit .unit [], .cellRef .integer 0, .hostFunction .storageRead] do
    discard <| rejectedInput treeEntry [.constructed ⟨treeId, 0⟩ forbidden]
  match treeEntry.start [tree] [.unit] with
  | .error (.initialStoreUnsupported 1) => pure ()
  | _ => throw (IO.userError "external initial store accepted")

  let failing ← firstEntry (← compilePlan program checked ["absent"] absentLowerer)
  let failed ← invoke failing [tree]
  let [site] := failing.faultSites.reads | throw (IO.userError "failure site missing")
  assertTrue (failed.observation == .failed site.reason [present tree, .inLeft (.namedData treeId) .unit])
    "general failure did not retain typed nominal store"
  assertTrue (failing.failureDiagnostic? site.reason |>.isSome) "general diagnostic lookup failed"
  assertTrue (!(failing.failureDiagnostic? (Word.ofNatModulo 9999)).isSome) "unknown diagnostic was accepted"

  let make ← firstEntry (← compilePlan program checked ["make"] closureLowerer)
  let returned ← invoke make [tree]
  let returnedValue ← match returned.observation with
    | .succeeded value _ => pure value
    | other => throw (IO.userError s!"internal closure result failed: {reprStr other}")
  let functionInput ← firstEntry (← compilePlan program checked ["keepFunction"] identityLowerer)
  match (← rejectedInput functionInput [returnedValue]) with
  | .input 0 error => assertTrue (decide (error.code = .functionHandleRequired)) "raw closure was not explicitly rejected"
  | _ => throw (IO.userError "raw closure input error changed")

  let badBody : BodyLowerer checked String := fun _ request => do
    pure ⟨LanguageResult.success .unit, ← sites request⟩
  let inputPlan ← planFor program ["keepTree"]
  match prepare program inputPlan checked 100 badBody with
  | .error (.coreCheckFailed _ _) => pure ()
  | _ => throw (IO.userError "uncertified callback body escaped checking")
  let stagedPlan ← planFor program ["staged"]
  match prepare program stagedPlan checked 100 identityLowerer with
  | .error (.stagedInputUnsupported _) => pure ()
  | _ => throw (IO.userError "unsupported staged input was not rejected")
  IO.println "source Core general entry GREEN"

end Tests.SourceCoreGeneralEntry
