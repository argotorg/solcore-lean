import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaCalls
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaInvocation CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
section Proof
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : SourceSemantics.Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem completed_call {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {result : Core.Value} {finalStore : Store} {fuel : Nat}
    (completed : runStateful fuel (.initial CallableIndexedLambdaCalls.applyPayload
      [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments] store)
      = .done (.inRight .word result) finalStore) :
    ∃ sourceResult after finalMap finalWorld,
      Dynamic.CallableApplies program callerContext callerEvidence function.evidence before (.closure function) arguments sourceResult after ∧
      (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile)).Represents
        finalMap finalWorld function.resultType sourceResult result code.receipt.resultCore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeap, _, _, _, _, caller⟩ :=
    CallableIndexedLambdaCalls.reflects captured code history body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing (runStateful_evaluation_sound completed)
  cases related with
  | value payload =>
    cases execution with
    | value called => exact ⟨_, after, finalMap, finalWorld, called, payload, finalHeap, caller.read⟩

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem failed_call {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {token : Word} {finalStore : Store} {fuel : Nat}
    (completed : runStateful fuel (.initial CallableIndexedLambdaCalls.applyPayload
      [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments] store)
      = .done (.inLeft code.receipt.resultCore (.word token)) finalStore) :
    ∃ reason after finalMap finalWorld,
      Dynamic.CallableFaults program callerContext callerEvidence function.evidence before (.closure function) arguments reason after ∧
      faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeap, _, _, _, _, caller⟩ :=
    CallableIndexedLambdaCalls.reflects captured code history body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing (runStateful_evaluation_sound completed)
  cases related with
  | fault represented =>
    cases execution with
    | fault failed => exact ⟨_, after, finalMap, finalWorld, failed, represented, finalHeap, caller.read⟩
end Proof

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "function make(seed: Word) returns (F) { let unused: Word = 99; return lam(item: Word) -> Word { let converted = item + seed; { let nested = converted + wordFromInteger(0); nested; } if (converted < seed) { return seed; } return converted; }; }",
    "function fail(seed: Word) returns (F) { return lam(item: Word) -> Word { let table: mapping(Bool => Word); let loaded = table[item == seed]; let converted = item + seed; let gap: Word; return gap; }; }",
    "function two(seed: Word) returns (function(Word, Word) returns (Word)) { return lam(first: Word, second: Word) -> Word { return seed + first - second; }; }",
    "function zero(seed: Word) returns (function() returns (Word)) { return lam() -> Word { return seed + wordFromInteger(0); }; }",
    "function unitMaker() returns (function()) { return lam() { { let item = wordFromInteger(0); item; } }; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey :=
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, []⟩
  | none => throw (IO.userError s!"missing lambda call fixture {name}")

/-- Each resumed run starts from the actual suspended machine state. The
comparison includes the complete store, including parameters and body effects. -/
private def resumed (start : Core.State) : IO Core.StatefulRunResult := do
  let expected := runStateful 500000 start
  for spent in [0, 1, 17, 49, 111, 317] do
    let observed := match runStateful spent start with
      | .outOfFuel checkpoint => runStateful 500000 checkpoint
      | completed => completed
    SourceCompilerFeatureSupport.require (observed == expected) s!"lambda call resume changed value/store at {spent}"
  pure expected

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "lambda call checker" (checkProgram workspace)
  let names := ["make", "fail", "two", "zero", "unitMaker"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"lambda call worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "lambda call base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "lambda call indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let word := Word.ofNatModulo
  for (name, key) in names.zip keys do
    let inputs := if name == "unitMaker" then [] else [.word (word 3)]
    let completed ← SourceCompilerFeatureSupport.get "lambda maker" (prepared.runSource key inputs 500000)
    match completed.result.native.observation with
    | .succeeded native store =>
      let packed := if name == "two" then .pair (.word (word 10)) (.word (word 2))
        else if name == "zero" || name == "unitMaker" then .unit else .word (word 10)
      let result ← resumed (.initial CallableIndexedLambdaCalls.applyPayload [native, packed] store)
      match result with
      | .done value finalStore =>
        SourceCompilerFeatureSupport.require
          (finalStore[0]? == some (encode prepared.ancestry.layout.frame .empty))
          "lambda payload call did not restore the original caller frame"
        if name == "zero" then
          SourceCompilerFeatureSupport.require (finalStore == store) "zero-parameter pure call changed the store"
        else
          SourceCompilerFeatureSupport.require (finalStore.length > store.length)
            "lambda parameter/body allocations were lost"
        if name == "fail" then
          match value with
          | .inLeft .word (.word _) =>
            SourceCompilerFeatureSupport.require
              (finalStore.any (fun v => v == .inRight .unit (.word (word 13))))
              "lambda fault lost a completed body binding"
            SourceCompilerFeatureSupport.require (finalStore.any (fun v => v == .inLeft .word .unit))
              "lambda fault lost the uninitialized source cell"
          | other => throw (IO.userError s!"lambda fault result {reprStr other}")
        else
          let expected := if name == "unitMaker" then .unit else .word (word (if name == "make" then 13 else if name == "two" then 11 else 3))
          SourceCompilerFeatureSupport.require (value == .inRight .word expected) s!"lambda {name} result {reprStr value}"
      | other => throw (IO.userError s!"lambda {name} machine result {reprStr other}")
    | other => throw (IO.userError s!"lambda {name} creation {reprStr other}")
  IO.println "indexed lambda calls: source success/fault reflection, builtin lexical body, ordered parameters, exact caller restore and resumed store GREEN"
end Tests.SourceCoreCallableIndexedLambdaCalls
