import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Actual invocation consumers close every callee using the static catalog's
mutual theorem. No body/flow/expression meaning law is an external premise.
Runtime cases execute checked self/mutual match bodies and verify every source cell,
first fault, initial prefix and the complete resumed observation. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedCatalogMatchMeaning
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
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
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
theorem independent_call_preserved {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld,
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact invocation_preserves_bounded (functions := functions) (registry := registry) (faults := faults) size
    (fun child _ => RecursiveNamedCatalogMutualMeaning.preserves_at_match functions extension faithful observations runtimeViews owners
      uninitialized missing escaped prefixMatches profiles child header member)
    caller member represented heaps trace (Nat.le_refl size)

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
theorem completed_call_reflected
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact invocation_reflects_bounded (functions := functions) (registry := registry) (faults := faults) size
    (fun child _ => RecursiveNamedCatalogMutualMeaning.reflects_at_match functions extension faithful observations runtimeViews
      uninitialized missing escaped prefixMatches profiles child header member)
    caller member represented heaps capture completed (Nat.le_refl size)
end ActualCalls

section StaticCompatibility
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}
  {fuel : Nat} {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {policy : AssignmentDiagnosticPolicy}
  (profile : ProfileFor policy headers header compilation fuel expressionSyntax administrative registry faults)

include profile in
/-- The original For profile requires no additional catalog validity. -/
theorem for_without_catalog :
    Nonempty (MatchProfileFor policy headers header compilation fuel expressionSyntax administrative registry faults) := ⟨profile.to_match⟩

/-- Static inclusion keeps the actual flow rather than recompiling it. -/
theorem same_flow : profile.to_match.flow = profile.flow := rfl

theorem same_ready : GenericImperativeMatch.Tree.ReadyFor policy registry faults profile.to_match.tree :=
  profile.to_match.errors.ready
end StaticCompatibility

private def content : String := String.intercalate "\n" [
  "function self(n: Word) returns (Word) { match ((n, n)) { case (0, terminal) { return terminal + 2; } default { let total = 0; for (let i = 0; i < 2; i += 1) { total += self(n - 1); } return total; } } }",
  "function left(n: Word) returns (Word) { match (n) { case 0 { return 7; } default { return right(n - 1); } } }",
  "function right(n: Word) returns (Word) { let i = n; while (i != 0) { i -= 1; match (i) { case 0 { return left(i); } default { return left(i); } } } return 11; }",
  "function driver(n: Word) returns (Word) { let total = self(2); for (let i = 0; i < n; i += 1) { total += left(i); } return total; }",
  "function unit(n: Word) { let prior = n; if (n != 0) { unit(n - 1); return; } }",
  "function fail(n: Word) returns (Word) { let prior = n; match (n) { case 0 { let gap: Word; return gap; } default { return fail(n - 1); } } }",
  "function driverFault() returns (Word) { let prior = 29; fail(2); let skipped = 99; return skipped; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (w n))
private def pair (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value :=
  (.product .word .word, some (.product (w n) (w n)))
private def selfCells : Nat → List (TypeSystem.Ty × Option SourceTypedRuntime.Value)
  | 0 => [present 0, pair 0, present 0]
  | n + 1 => [present (n + 1), pair (n + 1), present (2 ^ (n + 2)), present 2] ++ selfCells n ++ selfCells n
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"match catalog resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"match catalog prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue
    (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"match catalog ordered cells changed {label}: {reprStr final.heap}"
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "match catalog fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "match catalog exact fault binder missing")

def run : IO Unit := do
  let names := ["self", "left", "right", "driver", "unit", "fail", "driverFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive match catalog meaning" content names
  SourceCoreUnifiedCorpusSupport.assertTrue
    (compiled.indexed.base.functions.length == names.length &&
      compiled.indexed.secondPass.closures.length == names.length) "match catalog saved named inventory changed"
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 839)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("self", [w 0], w 2, selfCells 0),
    ("self", [w 2], w 8, selfCells 2),
    ("left", [w 2], w 7, [present 2, present 2, present 1, present 0, present 0, present 0, present 0]),
    ("right", [w 2], w 11, [present 2, present 1, present 1, present 1, present 1, present 0, present 0]),
    ("driver", [w 3], w 33, [present 3] ++ selfCells 2 ++
      [present 33, present 3, present 0, present 0, present 1, present 1, present 0, present 0, present 2, present 2, present 1, present 0, present 0, present 0, present 0]),
    ("unit", [w 2], .unit, [present 2, present 2, present 1, present 1, present 0, present 0])]
  let failureCells := [present 2, present 2, present 2, present 1, present 1, present 1, present 0, present 0, present 0, (.word, none)]
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("fail", [w 2], failureCells), ("driverFault", [], present 29 :: failureCells)]
  let complete ← successes.mapM fun test => finish compiled test.1 test.2.1 300000 initial
  let failed ← failures.mapM fun test => finish compiled test.1 test.2.1 300000 initial
  let expectedFault ← faultBinder compiled
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip complete do
      let (name, arguments, expected, expectedCells) := test
      let observation ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"match catalog full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"match catalog result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue
          (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"match catalog heap not deeply safe {name}"
      | other => throw (IO.userError s!"match catalog {name}: {reprStr other}")
    for (test, baseline) in failures.zip failed do
      let (name, arguments, expectedCells) := test
      let observation ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"match catalog full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == expectedFault) s!"match catalog first fault binder changed {name}"
        cells initial final expectedCells name
      | other => throw (IO.userError s!"match catalog fault {name}: {reprStr other}")
  IO.println "recursive match catalog meaning: static profiles close all body IH, independent finite grades, self/mutual calls, exact source cells/faults and public resume GREEN"

end Tests.SourceCoreRecursiveNamedCatalogMatchMeaning
