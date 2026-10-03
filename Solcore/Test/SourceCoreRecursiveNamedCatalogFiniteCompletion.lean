import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogFiniteCompletion
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Final finite-machine consumers use the actual installed catalog and static
profiles without any callee execution premise. Runtime fixtures check source
cells, first fault and complete resumed observations. Spin suspension remains
suspension; these finite observations do not prove source divergence. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCatalogFiniteCompletion
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
section ActualCalls
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Sufficient fuel follows from a finite independent source execution,
including language faults represented by the normal result carrier. -/
theorem finite_source_has_native_fuel {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact RecursiveNamedCatalogFiniteCompletion.has_sufficient_fuel functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles caller member represented heaps trace

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Every machine completion reflects. No relation between source and
native fuel, and no assumption of source termination, enters this consumer. -/
theorem any_completed_machine_has_source_meaning
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact RecursiveNamedCatalogFiniteCompletion.completed_run_reflects functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller member represented heaps capture completed
end ActualCalls

private def content : String := String.intercalate "\n" [
  "function count(n: Word) returns (Word) { let prior = n; if (n != 0) { return count(n - 1); } return 5; }",
  "function flip(n: Word) returns (Bool) { if (n == 0) { return true; } return flop(n - 1); }",
  "function flop(n: Word) returns (Bool) { if (n == 0) { return false; } return flip(n - 1); }",
  "function unit(n: Word) { let prior = n; if (n != 0) { unit(n - 1); return; } }",
  "function fail(n: Word) returns (Word) { let prior = n; if (n != 0) { return fail(n - 1); } let gap: Word; return gap; }",
  "function callerFault() returns (Word) { let prior = 59; fail(2); let skipped = 99; return skipped; }",
  "function spin(n: Word) returns (Word) { return spin(n); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (w n))
private def recursionCells : List (TypeSystem.Ty × Option SourceTypedRuntime.Value) :=
  [present 2, present 2, present 1, present 1, present 0, present 0]
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"finite completion resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"finite completion prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue
    (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"finite completion ordered cells changed {label}: {reprStr final.heap}"
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "finite completion fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "finite completion exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive catalog finite completion" content
    ["count", "flip", "flop", "unit", "fail", "callerFault", "spin"]
  SourceCoreUnifiedCorpusSupport.assertTrue (compiled.indexed.base.functions.length == 7 &&
    compiled.indexed.secondPass.closures.length == 7) "finite completion cached named inventory changed"
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 853)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("count", [w 0], w 5, [present 0, present 0]),
    ("count", [w 2], w 5, recursionCells),
    ("flip", [w 2], .bool true, [present 2, present 1, present 0]),
    ("flop", [w 2], .bool false, [present 2, present 1, present 0]),
    ("unit", [w 2], .unit, recursionCells)]
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("fail", [w 2], recursionCells ++ [(.word, none)]),
    ("callerFault", [], present 59 :: recursionCells ++ [(.word, none)])]
  let complete ← successes.mapM fun test => finish compiled test.1 test.2.1 300000 initial
  let failed ← failures.mapM fun test => finish compiled test.1 test.2.1 300000 initial
  let expectedFault ← faultBinder compiled
  for fuel in [0, 41, 300000] do
    for (test, baseline) in successes.zip complete do
      let (name, arguments, expected, expectedCells) := test
      let observation ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"finite completion full resume changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"finite completion result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue
          (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"finite completion source heap not deeply safe {name}"
      | other => throw (IO.userError s!"finite completion {name}: {reprStr other}")
    for (test, baseline) in failures.zip failed do
      let (name, arguments, expectedCells) := test
      let observation ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"finite completion full fault resume changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == expectedFault) s!"finite completion first fault binder changed {name}"
        cells initial final expectedCells name
      | other => throw (IO.userError s!"finite completion fault {name}: {reprStr other}")
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled "spin" [w 2] 1200 initial
  let second ← SourceCoreUnifiedCorpusSupport.get "finite spin resume" (first.resume 1200)
  let third ← SourceCoreUnifiedCorpusSupport.get "finite spin second resume" (second.resume 1200)
  for result in [first, second, third] do
    match result.observation with
    | .outOfFuel final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
        "finite spin prefix changed"
      SourceCoreUnifiedCorpusSupport.assertTrue (!(final.heap.drop initial.heap.length).isEmpty)
        "finite spin lost reached source parameter cells"
    | other => throw (IO.userError s!"finite spin suspension became completion: {reprStr other}")
  IO.println "recursive catalog finite completion: all-grade meaning, sufficient fuel and completed-run reflection, exact cells/faults/public resume, retained spin suspension GREEN"

end Tests.SourceCoreRecursiveNamedCatalogFiniteCompletion
