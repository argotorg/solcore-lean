import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogEntries
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogBodyFinishBounds
import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeFor
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogFiniteCompletion
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInitialization
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfileFactory
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeMatchProfiles
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedCallEvidence
import Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedNamedCallCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedParameterProjections
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedSourceFrames
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes
import Solcore.SourceSemantics.CoreLowering.SourceExecutionSize
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts

/-!
# Recursive named catalog tests

The recursive named catalog, prepared stages, calls and traces.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedCatalog
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.Header.certificate
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.Profile.mk
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.ParameterEntry.mk

/-! Static header/profile separation and real all-target parameter entry.
Formal consumers require actual captured reference coherence; no body meaning
or source/native body execution is an input. Checked cached runs exercise self
and mutual globals under imperative bodies, faults and native resume. They do
not establish the deferred mutually recursive correspondence theorem. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCatalog
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open RecursiveNamedCatalog CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterMeaning
section Foundation
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix callerPrefix : Nat} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store}

/-- This final prefix consumer exposes every actual global reference in the
callee body environment. The only independent runtime inputs are represented
arguments, the initial heap and the retained installed catalog. -/
theorem all_targets_after_named_prefix
    (authority : Authority headers locations capturePrefix mapping world heap store)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store) :
    ∃ origin index metadata,
      prepared.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      ∃ capture : Capture headers locations capturePrefix authority.frameLocation header mapping world heap store,
        ∃ entry : ParameterEntry headers locations capturePrefix functions registry header arguments heap
          (store.set authority.frameLocation (encode prepared.layout.frame (.state index))) mapping world
          capture.administrative
          (.unit :: prepared.layout.frame.type :: header.named.signature.parameterType :: capture.capturedContext)
          (.unit :: encode prepared.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured)
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
          authority.frameLocation (.state index) (.named origin),
          ∀ target, target ∈ headers →
            entry.actualBody[entry.embedding (header.bindings.length + (capturePrefix + 1) + target.slot)]? = some
              (.cellRef (OptionalCell.cellType target.named.signature.functionType) (locations target)) := by
  obtain ⟨origin, index, metadata, owned, history, _, capture, ⟨entry⟩⟩ := named_parameters authority member represented heaps
  refine ⟨origin, index, metadata, owned, history, capture, entry, ?_⟩
  intro target targetMember
  simpa only [List.length_map, List.length_reverse] using entry.lookups (entry.catalog.globals target targetMember)

/-- Native typing alone cannot replace a missing capture reference. -/
theorem missing_capture_rejected {header target : Header prepared values ambient.definitions program} {location : Location}
    (capture : Capture headers locations capturePrefix location header mapping world heap store)
    (member : target ∈ headers)
    (missing : capture.canonical[capturePrefix + target.slot]? = none) : False := by
  have exactReference := capture.coherent target member
  rw [missing] at exactReference
  cases exactReference

/-- All closures remain exact after actual argument-prefix effects. -/
theorem target_after_prefix {scope : Scope} {canonical actual : Environment} {ξ : Renaming}
    (entry : Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    {futureMap : LocationMap} {futureWorld : StoreTyping} {after : Dynamic.Heap} {futureStore : Store}
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers) (reason : Word) :
    ∃ capture : Capture headers locations capturePrefix entry.authority.frameLocation header futureMap futureWorld after futureStore,
      Evaluates actual futureStore (OptionalCell.read header.named.signature.functionType
        (.var (ξ (scope.length + callerPrefix + header.slot))) reason)
        (.inRight .word (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)) futureStore :=
  (entry.extend maps worlds frame metadata).read_target agrees member reason

end Foundation

private def content : String := String.intercalate "\n" [
  "function self(n: Word) returns (Word) { if (n == 0) { return 2; } let total = 0; for (let i = 0; i < 2; i += 1) { total += self(n - 1); } return total; }",
  "function left(n: Word) returns (Word) { return n == 0 ? 7 : right(n - 1); }",
  "function right(n: Word) returns (Word) { let i = n; while (i != 0) { i -= 1; return left(i); } return 11; }",
  "function driver(n: Word) returns (Word) { let f = left; let total = self(2); for (let i = 0; i < n; i += 1) { total += f(i); } return total; }",
  "function fail(n: Word) returns (Word) { let written = self(n); let gap: Word; return gap; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (SourceCoreUnifiedCorpusSupport.word n)

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named catalog" content ["self", "left", "right", "driver", "fail"]
  SourceCoreUnifiedCorpusSupport.assertTrue (compiled.indexed.base.functions.length == 5)
    "recursive catalog changed the finite named inventory"
  SourceCoreUnifiedCorpusSupport.assertTrue
    (compiled.indexed.secondPass.closures.length == compiled.indexed.base.functions.length)
    "recursive catalog cached slots are incomplete"
  for (name, argument, expected) in [("self", 3, 16), ("left", 2, 7), ("right", 2, 11), ("driver", 3, 33)] do
    for fuel in [0, 7, 83] do
      let _ ← SourceCoreUnifiedCorpusSupport.expect compiled name [w argument] (w expected) fuel
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled "fail" [w 2]
  match first.observation with
  | .fault (.uninitializedLocal _) state =>
    SourceCoreUnifiedCorpusSupport.assertTrue (SourceCoreUnifiedCorpusSupport.hasWord state 8)
      "recursive catalog fault lost completed recursive writes"
    for fuel in [0, 7, 83] do
      let start ← SourceCoreUnifiedCorpusSupport.execute compiled "fail" [w 2] fuel
      let resumed ← SourceCoreUnifiedCorpusSupport.get "recursive catalog fault resume" (start.resume 300000)
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr resumed.observation == reprStr first.observation)
        "recursive catalog fault resume changed source observations"
  | other => throw (IO.userError s!"recursive catalog expected first uninitialized fault: {reprStr other}")
  IO.println "recursive named catalog: static headers/profiles, all-target prefix receipts, captured coherence, self/mutual globals, imperative bodies, fault writes and resume GREEN"
end Tests.SourceCoreRecursiveNamedCatalog
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedCatalogBodyFinishBounds
/-! Concrete builtin flow trees close the remaining flow contracts of both
catalog body adapters. Static profiles use each real parameter entry's packed
administrative context. No runtime body/child law is supplied to these consumers.
The general adapters retain pointwise flow as the later mutual-induction boundary.
Actual calls check parameters, complete body effects, first faults and resume. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCatalogBodyFinishBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds
#check_failure RecursiveNamedCatalogBodyFinishBounds.ProfileFor
#check_failure RecursiveNamedCatalogBodyFinishBounds.BodyState
#check_failure SourceTypedRuntime.run
section Concrete
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionFuel readFuel : Nat} {expressionSyntax : ExpressionId → Prop}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (escapedFault : faults .controlEscapedFunction header.escaped)
  (profiles : ∀ administrative, ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
  (trees : ∀ administrative, BuiltinImperativeFor.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
    header.onError readFuel values header.function.source header.solved header.reasonAt ambient.definitions
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (.statements true header.function.body) header.function.resultType header.output (profiles administrative).flow)
  (errors : ∀ administrative, GenericImperativeFor.Tree.ReachableErrors registry faults (trees administrative))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))

include extension escapedFault profiles trees errors faithful observations runtimeViews uninitialized missing in
theorem concrete_preserves_at (size : Nat) :
    BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  apply RecursiveNamedCatalogBodyFinishBounds.body_preserves_at functions escapedFault profiles size
  intro administrative valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped _ trace
  exact BuiltinImperativeFor.Tree.preserves_reachable functions header.definitions_eq header.registered extension program header.function.evidence
    uninitialized missing faithful observations runtimeViews (trees administrative) (errors administrative) valid header.unique
    environments heaps locals agrees typed reference read unmapped trace.sound

include extension escapedFault profiles trees errors faithful observations runtimeViews uninitialized missing in
theorem concrete_reflects_at (budget size : Nat) (within : size ≤ budget) :
    BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  apply RecursiveNamedCatalogBodyFinishBounds.body_reflects_at functions escapedFault profiles budget size within
  intro administrative child _ valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped _ completed
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    BuiltinImperativeFor.Tree.reflects_reachable functions header.definitions_eq header.registered extension program header.function.evidence
      uninitialized missing faithful observations runtimeViews (trees administrative) (errors administrative) valid header.unique
      environments heaps locals agrees typed reference read unmapped completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size trace
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, frame, metadata, lexical⟩
end Concrete

private def content : String := String.intercalate "\n" [
  "function calculate(limit: Word) returns (Word) { let sum = 0; for (let i = 0; i < limit; i += 1) { if (i == 1) { continue; } sum += i; if (i == 3) { break; } } return sum; }",
  "function early(value: Word) returns (Bool) { let prior = value; while (true) { let inside = value + 1; return true; } let skipped = 99; return false; }",
  "function unitBody(seed: Word) { let saved = seed; for (let i = 0; i < 2; i += 1) { let saved = i; } }",
  "function failBody(seed: Word) returns (Word) { let prior = seed; for (let i = 0; true; i += 1) { let saved = prior + 1; let gap: Word; return gap; } let skipped = 26; return skipped; }",
  "function postFault(seed: Word) returns (Word) { let prior = seed; let gap: Word; for (let i = 0; i < 3; i += gap) { let saved = i + 1; } return prior; }",
  "function nested(value: Word) returns (Word) { for (let i = 0; i < 2; i += 1) { while (true) { let seen = i; if (i == 0) { break; } else { return value; } } } return 0; }",
  "function integerBody(left: Word, right: Word) returns (integer) { return integerSub(wordToInteger(left), wordToInteger(right)); }",
  "function mapped(flag: Bool) returns (Word) { let m: mapping(Bool => Word); m[flag] = 27; return m[flag]; }",
  "function zero() returns (Word) { return calculate(0); }",
  "function outer() returns (Word) { return calculate(5); }",
  "function twice() returns (Word) { let first = calculate(0); let second = calculate(5); return first + second; }",
  "function earlyCall() returns (Bool) { return early(21); }",
  "function unitCall() { unitBody(23); let after = 24; }",
  "function faultCall() returns (Word) { let before = 23; let failed = failBody(24); return failed; }",
  "function postFaultCall() returns (Word) { return postFault(30); }",
  "function nestedCall() returns (Word) { return nested(31); }",
  "function integerCall() returns (integer) { return integerBody(7, 9); }",
  "function mappedCall() returns (Word) { return mapped(true); }",
  "function discardCall() returns (Word) { early(21); return calculate(5); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (w n))
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"catalog body finish resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"catalog body finish prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"catalog body finish complete cells changed {name}: {reprStr final.heap}"
private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "catalog body finish fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "catalog body finish exact fault binder missing")

def run : IO Unit := do
  let names := ["zero", "outer", "twice", "earlyCall", "unitCall", "faultCall", "postFaultCall", "nestedCall", "integerCall", "mappedCall", "discardCall"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named catalog body finish bounds" content names
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 827)⟩]}
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("zero", w 0, [0, 0, 0].map present),
    ("outer", w 5, [5, 5, 3].map present),
    ("twice", w 5, [0, 0, 0, 0, 5, 5, 3, 5].map present),
    ("earlyCall", .bool true, [21, 21, 22].map present),
    ("unitCall", .unit, [23, 23, 2, 0, 1, 24].map present),
    ("nestedCall", w 31, [31, 1, 0, 1].map present),
    ("integerCall", .integer (-2), [7, 9].map present),
    ("mappedCall", w 27, [(.bool, some (.bool true)), (.mapping .bool .word, some (.mapping .bool .word [(.bool true, w 27)]))]),
    ("discardCall", w 5, [21, 21, 22, 5, 5, 3].map present)]
  let failures : List (String × String × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("faultCall", "failBody", [23, 24, 24, 0, 25].map present ++ [(.word, none)]),
    ("postFaultCall", "postFault", [present 30, present 30, (.word, none), present 0, present 1])]
  let complete ← successes.mapM fun test => finish compiled test.1 300000 initial
  let failed ← failures.mapM fun test => finish compiled test.1 300000 initial
  for fuel in [0, 47, 300000] do
    for (test, baseline) in successes.zip complete do
      let (name, expected, expectedCells) := test
      let observation ← finish compiled name fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"catalog body finish full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"catalog body finish result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"catalog body finish heap not deeply safe {name}"
      | other => throw (IO.userError s!"catalog body finish {name}: {reprStr other}")
    for (test, baseline) in failures.zip failed do
      let (name, owner, expectedCells) := test
      let observation ← finish compiled name fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"catalog body finish full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        let expected ← gapBinder compiled owner
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == expected) s!"catalog body finish first fault binder changed {name}"
        cells initial final expectedCells name
      | other => throw (IO.userError s!"catalog body finish fault {name}: {reprStr other}")
  IO.println "recursive named catalog body finish bounds: real parameter/admin context, concrete flow families, called finite for/while/finish, complete source cells, fault order and public resume GREEN"

end Tests.SourceCoreRecursiveNamedCatalogBodyFinishBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedCatalogFiniteCompletion
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedCatalogInitialization
/-! Formal consumers derive the initial whole catalog and empty represented
source heap from the actual accepted recipe. No body meaning or source execution
is an input. Native IO audits deep installed closure typing and complete captures;
it does not manufacture semantic source headers from a runtime cache. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCatalogInitialization
open Solcore Core Frontend SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload RecursiveNamedCatalog
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping
open RecursiveNamedCatalogInitialization

section Formal
variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
  (rows : List LambdaRow)
  (cached : compiled.indexed.secondPass.closures = rows.map LambdaRow.expression)
  (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
    compiled.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
  (ledger : Ledger headers compiled.indexed.secondPass.closures)
  (globals : ∀ header, header ∈ headers → compiled.indexed.base.globals[header.slot]? = some header.named.signature)
  (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (locals : ∀ header, header ∈ headers → header.function.context.locals = [])
  {recipe : SourceCoreIndexedSession.Recipe}
  (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)

include cached ordered ledger globals sizes locals accepted definitions in
theorem actual_initial_authority :
    ∃ world, Nonempty (Authority headers (fun header => location compiled.indexed.base.globals header.slot) 0 [] world ⟨[]⟩
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)) :=
  of_recipe compiled headers rows cached ordered ledger globals sizes locals accepted definitions

include cached ordered ledger globals sizes locals accepted definitions in
theorem actual_initial_source_heap
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame) ∧
      Nonempty (Authority headers (fun header => location compiled.indexed.base.globals header.slot) 0 [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)) := by
  obtain ⟨world, heaps, ⟨entry⟩⟩ := initial_entry compiled headers rows cached ordered ledger globals sizes locals accepted definitions functions registry
  exact ⟨world, heaps, ⟨entry.authority⟩⟩

include cached ordered ledger globals sizes locals accepted definitions in
theorem actual_initial_caller_entry
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame) ∧
      Nonempty (Entry headers (fun header => location compiled.indexed.base.globals header.slot) 0 0 [] [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)
        (initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame)) :=
  initial_entry compiled headers rows cached ordered ledger globals sizes locals accepted definitions functions registry

include cached ordered ledger globals sizes locals accepted definitions in
/-- Any finite completion of the original bootstrap has this same initialized
store and whole catalog. It does not use a source execution as a premise. -/
theorem any_completed_bootstrap
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧ ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩ finalStore ∧
      Nonempty (Authority headers (fun header => location compiled.indexed.base.globals header.slot) 0 [] world ⟨[]⟩ finalStore) := by
  obtain ⟨_, emitted⟩ := recipe_emitted accepted
  have expected := framed_bootstrap compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame ordered
  rw [← cached, ← emitted] at expected
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic (runStateful_evaluation_sound completed) expected
  exact ⟨rfl, actual_initial_source_heap compiled headers rows cached ordered ledger globals sizes locals accepted definitions functions registry⟩
end Formal

private def content : String := String.intercalate "\n" [
  "function step(value: Word) returns (Word) { return value + 1; }",
  "function left(n: Word) returns (Bool) { if (n == 0) { return true; } return right(n - 1); }",
  "function right(n: Word) returns (Bool) { if (n == 0) { return false; } return left(n - 1); }",
  "function order(first: Word, flag: Bool, last: Word) returns (Word) { if (flag) { return step(first); } return step(last); }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { let extra = step(seed); return lam(value: Word) -> Word { extra += value; return extra; }; }",
  "function fail() returns (Word) { let written = 17; let gap: Word; return gap; }",
  "function zero() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def finish (state : State) : IO (Value × Store) :=
  match runStateful 300000 state with
  | .done value store => pure (value, store)
  | other => throw (IO.userError s!"catalog initialization did not finish: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "initial whole catalog" content
    ["left", "right", "order", "make", "fail", "zero"]
  let indexed := compiled.indexed
  let recipe ← get "actual initialization recipe" (SourceCoreIndexedSession.Recipe.prepare compiled)
  let rows ← indexed.secondPass.closures.mapM fun expression =>
    match expression with
    | .lambda parameter result body => pure (⟨parameter, result, body⟩ : LambdaRow)
    | _ => throw (IO.userError "actual cached row is not a lambda")
  let canonical := initialEnvironment indexed.base.globals indexed.ancestry.layout.frame
  let expected := initialStore indexed.base.globals rows indexed.ancestry.layout.frame
  let (value, store) ← finish (.initial recipe.bootstrap [] [])
  require (reprStr store == reprStr expected) "initial whole catalog store changed"
  require (reprStr value == reprStr (Value.inRight .word .unit)) "initial whole catalog success changed"
  let world := store.map Value.type
  require (world[0]? == some indexed.ancestry.layout.frame.type) "initial frame type changed"
  require (store.read? 0 == some (SourceCoreCallableIndexedFrames.encode indexed.ancestry.layout.frame .empty))
    "actual empty frame changed"
  for reference in canonical do
    match reference with
    | .cellRef element location =>
      require (world[location]? == some element) "canonical global/frame reference type changed"
    | _ => throw (IO.userError "initial canonical environment contains a non-reference")
  for (row, slot) in rows.zipIdx do
    let signature ← match indexed.base.globals[slot]? with
      | some signature => pure signature | none => throw (IO.userError "real ordered signature missing")
    require (signature.functionType == .function row.parameter row.result) "full static cache signature changed"
    require (canonical[slot]? == some (.cellRef (OptionalCell.cellType signature.functionType) (location indexed.base.globals slot)))
      "actual coherent catalog reference changed"
    match store.read? (location indexed.base.globals slot) with
    | some (.inRight .unit (.closure parameter result body captured)) =>
      require (captured.length == slot + canonical.length) "real installer capture prefix length changed"
      require (captured.take slot == List.replicate slot Value.unit) "real installer Unit capture prefix changed"
      require (reprStr (captured.drop slot) == reprStr canonical) "canonical captured catalog changed"
      require (reprStr body == reprStr (row.body.rename (shift slot).lift)) "full actual renamed closure code changed"
      require (infer? (parameter :: captured.map Value.type) body indexed.layouts.definitions == some result)
        "deep native typing of actual stored capture/code failed"
      require (captured[shift slot indexed.base.globals.length]? == canonical[indexed.base.globals.length]?)
        "actual captured frame reference changed"
    | _ => throw (IO.userError "actual installed full closure missing")
  for fuel in [0, 1, 43, 300000] do
    let result ← match runStateful fuel (.initial recipe.bootstrap [] []) with
      | .done value store => pure (value, store)
      | .outOfFuel checkpoint => finish checkpoint
      | other => throw (IO.userError s!"actual typed bootstrap fault {reprStr other}")
    require (reprStr result == reprStr (value, store)) s!"whole initialized catalog resume changed {fuel}"
  IO.println "initial whole catalog: actual native store/capture typing, full coherent global/frame references, empty frame and complete resume GREEN"

end Tests.SourceCoreRecursiveNamedCatalogInitialization
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedCatalogMatchMeaning
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
  profile.to_match.errors.ready profile.initialValid
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedCatalogMutualMeaning
/-! Actual invocation consumers close every callee using the static catalog's
mutual theorem. No body/flow/expression meaning law is an external premise.
Runtime cases execute checked self/mutual calls and verify every source cell,
first fault, initial prefix and the complete resumed observation. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCatalogMutualMeaning
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
    (fun child _ => RecursiveNamedCatalogMutualMeaning.preserves_at functions extension faithful observations runtimeViews owners
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
    (fun child _ => RecursiveNamedCatalogMutualMeaning.reflects_at functions extension faithful observations runtimeViews
      uninitialized missing escaped prefixMatches profiles child header member)
    caller member represented heaps capture completed (Nat.le_refl size)
end ActualCalls

private def content : String := String.intercalate "\n" [
  "function self(n: Word) returns (Word) { if (n == 0) { return 2; } let total = 0; for (let i = 0; i < 2; i += 1) { total += self(n - 1); } return total; }",
  "function left(n: Word) returns (Word) { return n == 0 ? 7 : right(n - 1); }",
  "function right(n: Word) returns (Word) { let i = n; while (i != 0) { i -= 1; return left(i); } return 11; }",
  "function driver(n: Word) returns (Word) { let total = self(2); for (let i = 0; i < n; i += 1) { total += left(i); } return total; }",
  "function unit(n: Word) { let prior = n; if (n != 0) { unit(n - 1); return; } }",
  "function fail(n: Word) returns (Word) { let prior = n; if (n != 0) { return fail(n - 1); } let gap: Word; return gap; }",
  "function driverFault() returns (Word) { let prior = 29; fail(2); let skipped = 99; return skipped; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (w n))
private def selfCells : Nat → List (TypeSystem.Ty × Option SourceTypedRuntime.Value)
  | 0 => [present 0]
  | n + 1 => [present (n + 1), present (2 ^ (n + 2)), present 2] ++ selfCells n ++ selfCells n
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"mutual catalog resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"mutual catalog prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue
    (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"mutual catalog ordered cells changed {label}: {reprStr final.heap}"
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "mutual catalog fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "mutual catalog exact fault binder missing")

def run : IO Unit := do
  let names := ["self", "left", "right", "driver", "unit", "fail", "driverFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive catalog mutual meaning" content names
  SourceCoreUnifiedCorpusSupport.assertTrue
    (compiled.indexed.base.functions.length == names.length &&
      compiled.indexed.secondPass.closures.length == names.length) "mutual catalog saved named inventory changed"
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 839)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("self", [w 0], w 2, selfCells 0),
    ("self", [w 2], w 8, selfCells 2),
    ("left", [w 2], w 7, [present 2, present 1, present 0, present 0]),
    ("right", [w 2], w 11, [present 2, present 1, present 1, present 0, present 0]),
    ("driver", [w 3], w 33, [present 3] ++ selfCells 2 ++
      [present 33, present 3, present 0, present 1, present 0, present 0, present 2, present 1, present 0, present 0]),
    ("unit", [w 2], .unit, [present 2, present 2, present 1, present 1, present 0, present 0])]
  let failureCells := [present 2, present 2, present 1, present 1, present 0, present 0, (.word, none)]
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
        s!"mutual catalog full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"mutual catalog result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue
          (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"mutual catalog heap not deeply safe {name}"
      | other => throw (IO.userError s!"mutual catalog {name}: {reprStr other}")
    for (test, baseline) in failures.zip failed do
      let (name, arguments, expectedCells) := test
      let observation ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"mutual catalog full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == expectedFault) s!"mutual catalog first fault binder changed {name}"
        cells initial final expectedCells name
      | other => throw (IO.userError s!"mutual catalog fault {name}: {reprStr other}")
  IO.println "recursive catalog mutual meaning: static profiles close all body IH, independent finite grades, self/mutual calls, exact source cells/faults and public resume GREEN"

end Tests.SourceCoreRecursiveNamedCatalogMutualMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedCatalogNativeContexts
/-! Actual cached loops with named globals certify their free-slot support.
Formal consumers retain exact code, real body state and arbitrary actual
embedding. Remaining source/child/diagnostic laws are not inferred from native
or runtime types. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCatalogNativeContexts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory NativeExpressionContextSupport

variable (cached : SourceCoreUnifiedCompilation.Compiled)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
  (member : nativeEntry ∈ cached.indexed.entries)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (definitions : ambient.definitions = cached.indexed.layouts.definitions)
  {headers : Inventory cached.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {header : Header cached.indexed.ancestry values ambient.definitions program}
  (sameCache : header.compiled.closures = cached.indexed.secondPass.closures)
  (complete : Complete headers) (globals : header.globals = cached.indexed.base.globals.length)
  (support : supported (.lambda header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType) header.code) (cached.indexed.base.globals.length + 1) = true)
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include member definitions sameCache in
private theorem original_cached :
    HasType (cached.indexed.base.globals.map (·.referenceType) ++ .cell cached.indexed.ancestry.layout.frame.type ::
      SourceCoreGeneralEntry.nativeInputContext nativeEntry.native.inputTypes)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions := by
  have selected := header.cached
  rw [sameCache] at selected
  have typed := CallableIndexedCachedNativeTyping.prepared_native_closure cached.indexedPrepared member selected
    (CallableIndexedPreparedInventories.cached_global_at cached header.selected)
  simpa only [← definitions] using typed

include member definitions sameCache complete globals support entry in
theorem actual_canonical_body :
    HasType (SourceCoreLocalCell.coreContext (bodyScope header) ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      header.body (LanguageResult.resultType header.output) ambient.definitions :=
  canonical_cached complete globals (original_cached cached member definitions sameCache) support entry

include member definitions sameCache complete globals support in
theorem actual_renamed_body :
    HasType (CallableIndexedParameterTyped.prefixContext header.bindings actualContext)
      (header.body.rename entry.embedding) (LanguageResult.resultType header.output) ambient.definitions :=
  (actual_canonical_body cached member definitions sameCache complete globals support entry).rename
    (TypedLexicalWhile.environment_respects entry.environments.runtime_hasTypes entry.actualTyped entry.lookups)

variable {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

include member definitions sameCache complete globals support entry in
/-- This consumer feeds the real prepared root's native proof into the single
compiler traversal, without requesting body/loop HasType at actual Γ. -/
theorem actual_extraction (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) lowered.expression
          (LanguageResult.resultType lowered.type) ambient.definitions)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (closed : header.context.typeVariables = []) (residual : header.context.residualTypeVariables = false)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :=
  RecursiveNamedCatalogProfileFactory.extract diagnosticPolicy factory readPolicy binderPolicy allocationPolicy
    expressions assignments unaryPolicy assignmentExpressions syntaxTree closed residual sourceSignatures declarations
    projection accepted (original_cached cached member definitions sameCache) support complete globals entry

/-- Interpretation is required only for the selected extraction. -/
theorem selected_profile {diagnosticPolicy : AssignmentDiagnosticPolicy} {faults : FunctionCalls.FaultRep}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (interpreted : receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults) :=
  ⟨receipt.profile initialValid interpreted⟩

theorem unused_suffix_changes (suffix : Core.Context) :
    HasType (.word :: suffix) (.var 0) .word [] := by
  exact prefix_typing (leading := [.word]) (sourceSuffix := [.bool, .integer])
    (targetSuffix := suffix) (.var rfl) rfl

theorem used_suffix_not_supported : supported (.var 1) 1 = false := rfl

theorem used_suffix_cannot_disappear : ¬ HasType [.word] (.var 1) .bool [] := by
  intro typed
  cases typed with | var found => cases found

theorem bound_under_lambda : supported (.lambda .word .word (.var 0)) 0 = true := rfl

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function step(value: Word) returns (Word) { return value + 1; }",
    "function loop(flag: Bool, seed: Word) returns (Word) { let result = seed; for (let i = 0; i < 3; i = step(i)) { let j = 0; while (j < 2) { result = step(result); j = step(j); } } if (flag) { return step(result); } return result; }",
    "function recursive(value: Word) returns (Word) { if (value == 0) { return 1; } return step(recursive(value - 1)); }",
    "function order(first: Word, flag: Bool, last: Word) returns (Word) { if (flag) { return step(first); } return step(last); }",
    "function make(seed: Word) returns (function(Word) returns (Word)) { let extra = step(seed); return lam(value: Word) -> Word { let i = 0; while (i < 2) { extra = step(extra); i = step(i); } return extra + value; }; }"
  ]}] }

open Tests.SourceCompilerFeatureSupport in
private def checkSupport (entry : Entry) : IO Unit := do
  let prepared := entry.cached.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "actual named diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "actual named parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let leading := prepared.base.globals.map (·.referenceType) ++ [.cell prepared.ancestry.layout.frame.type]
  require (!prepared.entries.isEmpty && !prepared.base.globals.isEmpty) "actual checked roots/globals missing"
  require (prepared.base.globals.length == prepared.base.functions.length) "full inventory order mismatch"
  for (named, index) in prepared.base.functions.zipIdx do
    let own ← match diagnostics.base.find? named.signature.key with
      | some own => pure own | none => throw (IO.userError "actual named diagnostic function missing")
    let statements ← get "actual named roots" ((CallableIndexedNamedGeneration.source named).roots.mapM
      (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "actual named source body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    let parameters ← get "actual parameter allocation"
      (SourceCoreSourceCells.bindParameters (CallableIndexedNamedGeneration.allocator prepared named)
        (CallableIndexedNamedGeneration.source named) [] named.inputs named.signature.resultType
        SourceCoreFunctions.argumentProjection body)
    let output ← get "actual named frame hook"
      (SourceCoreCallableIndexedAncestry.namedBody prepared.ancestry named parameters)
    let code ← match prepared.secondPass.closures[index]? with
      | some code => pure code | none => throw (IO.userError "actual cached closure missing")
    require (prepared.base.globals[index]? == some named.signature) "ordered complete signature mismatch"
    require (code == .lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output)
      "body action did not reproduce the actual cached lambda"
    require (supported code leading.length) "actual cached code reads a hidden wrapper input"
    let bodyLeading := SourceCoreLocalCell.coreContext (named.inputs.reverse.map (fun b => (b.1.id, b.2))) ++
      named.signature.parameterType :: leading
    require (supported body bodyLeading.length) "actual body support escaped parameters/global/frame prefix"
    for root in prepared.entries do
      let wrapper := SourceCoreGeneralEntry.nativeInputContext root.native.inputTypes
      for suffix in [wrapper, [], [.integer, .bool, .function .unit .word]] do
        require (Core.infer? (leading ++ suffix) code prepared.layouts.definitions == some named.signature.functionType)
          "cached closure native typing changed with unused suffix"
        require (Core.infer? (bodyLeading ++ suffix) body prepared.layouts.definitions ==
          some (LanguageResult.resultType named.signature.resultType)) "actual named body lost canonical prefix typing"
    -- Original arguments remain before globals; an actual inserted slot uses syntax renaming.
    let hidden := [.integer, .bool]
    let shifted := code.rename (Renaming.insertion 0)
    require (Core.infer? (.integer :: leading ++ hidden) shifted prepared.layouts.definitions == some named.signature.functionType)
      "actual hidden insertion lost native cached typing"

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let checked ← get "native context source checker" (checkProgram workspace)
  for (name, arguments, expected) in [
      ("loop", [(.bool true : SourceCoreExecution.Value), scalar 2], scalar 9),
      ("loop", [(.bool false : SourceCoreExecution.Value), scalar 7], scalar 13),
      ("recursive", [scalar 4], scalar 5),
      ("order", [scalar 11, (.bool false : SourceCoreExecution.Value), scalar 17], scalar 18)] do
    let entry ← compileNamed checked name
    checkSupport entry
    require ((← entry.run arguments) == expected) "actual source result changed"
    for fuel in [0, 7, 43] do entry.checkResume arguments expected fuel
  let entry ← compileNamed checked "make"
  checkSupport entry
  let invocation ← entry.invoke [scalar 5]
  let done ← match invocation.outcome with
    | .succeeded done => pure done | _ => throw (IO.userError "actual closure creation failed")
  let handle ← match done.value with
    | .function handle => pure handle | _ => throw (IO.userError "actual closure result missing")
  let completed ← get "actual captured closure invocation" (← done.session.invokePacked handle (scalar 3) executionOptions)
  let final ← match completed with
    | .succeeded final => pure final | _ => throw (IO.userError "actual captured closure failed")
  require (final.value == scalar 11) "actual capture or global call changed"
  let baseline ← get "actual final snapshot" (← final.session.snapshot 2048)
  for fuel in [0, 7, 43] do
    let pending ← get "actual captured suspension"
      (← done.session.invokePacked handle (scalar 3) {executionOptions with executionFuel := fuel})
    let resumed ← match pending with
      | .outOfFuel pending => pending.resume 300000 2048 | complete => pure complete
    match resumed with
    | .succeeded actual =>
      let snapshot ← get "resumed final snapshot" (← actual.session.snapshot 2048)
      require (actual.value == final.value && reprStr snapshot.cells == reprStr baseline.cells)
        "resume changed captured values or ordered heap cells"
    | _ => throw (IO.userError "actual capture resume failed")
  IO.println "catalog native contexts: actual cached support, full global slots, canonical body/actual embedding, altered unused suffixes, loop/global/closure execution and resume GREEN"

end Tests.SourceCoreRecursiveNamedCatalogNativeContexts
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedCatalogRuntimeMatchProfiles
/-! Static consumers preserve actual accepted code, runtime literal receipts,
full ledger fields and the initial context. Whole runtime body meaning and a
weaker Header are separate units. Existing runtime runners cover this change. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCatalogRuntimeMatchProfiles
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup RecursiveNamedCatalog
open GenericImperativeMatch.Tree
section Actual
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (valid : CompatibleRuntimeContextValidity.Valid header.solved header.context header.function.evidence)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeMatch.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree)

include valid accepted projection generated tree errors in
/-- The constructor consumes the same full body/flow acceptance and supported
expression Tree; it does not add expression or body execution hypotheses. -/
theorem actual_profile : Nonempty (RuntimeMatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults) :=
  ⟨RuntimeMatchProfileFor.of_extracted valid accepted projection generated tree errors⟩

include accepted projection generated tree errors in
theorem actual_frame_profile (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved) :
    Nonempty (RuntimeMatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults) :=
  ⟨RuntimeMatchProfileFor.of_frame programTyped sameLedger accepted projection generated tree errors⟩

include valid accepted projection generated tree errors in
theorem same_flow : (RuntimeMatchProfileFor.of_extracted valid accepted projection generated tree errors).flow = flow := rfl

include valid accepted projection generated tree errors in
theorem same_native_code : header.body = CompatibleStatements.finish header.output
    (RuntimeMatchProfileFor.of_extracted valid accepted projection generated tree errors).flow header.fellThrough header.escaped :=
  (RuntimeMatchProfileFor.of_extracted valid accepted projection generated tree errors).emitted

include valid accepted projection generated tree errors in
theorem same_diagnostics : CatalogSites diagnosticPolicy registry faults
    (RuntimeMatchProfileFor.of_extracted valid accepted projection generated tree errors).tree := errors

/-- The old profile keeps its initial ordinary proof in the common record.
That proof, rather than a runtime-to-ordinary cast, reconstructs ReadyFor. -/
theorem legacy_ready
    (profile : MatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults) :
    GenericImperativeMatch.Tree.ReadyFor diagnosticPolicy registry faults profile.tree :=
  profile.errors.ready profile.initialValid
end Actual

section Sites
variable {compilation : SourceCoreCompatibleDataMatches.Context} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}

theorem runtime_context (fields : MatchContextFields compilation context)
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence) :
    CompatiblePatternRuntime.ContextValid compilation context := fields.runtime valid

/-- Even unused rows remain members of the actual compilation ledger. -/
theorem unused_row (fields : MatchContextFields compilation context)
    {row : SolvedRequirement} (member : row ∈ context.solvedRequirements) :
    row ∈ compilation.solvedRequirements := fields.ledger ▸ member

/-- The existing arm certificate already contains the actual literal validator
receipt, so no independent numeric-support assumption is introduced. -/
theorem repeated_arms {source : TypedSource} {site : StatementId} {scope : SourceCoreCompatibleDataMatches.Scope}
    {expected : TypeSystem.Ty} {arm : TypedMatchCase} {pattern : SourceCoreCompatibleDataMatches.Pattern}
    {body : Expr} {bodyCertificate : CompatibleMatchCertificates.BodyCertificate}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site arm.span expected arm.pattern pattern)
    (typed : HasType [] pattern.matcher pattern.functionType compilation.definitions)
    (bodyCertified : bodyCertificate (CompatibleMatchCertificates.armScope scope pattern) arm.body body) :
    CompatibleMatchCertificates.Arms compilation source site scope expected bodyCertificate
      [arm, arm] [(pattern, body), (pattern, body)] ∧
    CompatiblePatternRuntime.Certificate compilation source scope site arm.span expected arm.pattern pattern :=
  ⟨.cons certificate typed bodyCertified (.cons certificate typed bodyCertified .nil),
    CompatiblePatternRuntime.of_certificate certificate⟩
end Sites

/-- Static signature/ledger equality and runtime validity cannot recreate the
old ordinary all-row condition. The unused assumption row remains in full. -/
theorem fields_not_ordinary (compilation : SourceCoreCompatibleDataMatches.Context)
    (id : RequirementId) (predicate : ProgramPredicate) :
    let row : SolvedRequirement := ⟨id, predicate, .assumption predicate⟩
    let changed := { compilation with solvedRequirements := [row] }
    let context := (SourceSemantics.Context.ofSignatures compilation.signatures).withSolvedRequirements [row]
    MatchContextFields changed context ∧ RuntimeRequirementLedgerValid context ∧
      ¬ RequirementLedgerWellFormed context := by
  dsimp only
  refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
  · constructor
    · simp [RequirementIdsUnique, Context.withSolvedRequirements]
    · intro row evidence member actual
      have same : row = ⟨id, predicate, .assumption predicate⟩ := by
        simpa [Context.withSolvedRequirements] using member
      subst row
      cases actual
  · intro valid
    have rowValid := valid.entriesValid ⟨id, predicate, .assumption predicate⟩ (by simp [Context.withSolvedRequirements])
    cases rowValid with
    | intro retained =>
      cases retained with
      | intro represents evidence =>
        cases represents with
        | assumption =>
          cases evidence with
          | assumption member => simp only [Context.withSolvedRequirements, Context.ofSignatures, List.not_mem_nil] at member

end Tests.SourceCoreRecursiveNamedCatalogRuntimeMatchProfiles
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedCatalogRuntimeMutualMeaning
/-! Actual invocation consumers close the runtime catalog using one finite
family induction. Every callee profile retains accepted code and actual numeric
receipts. The independent source trace is an input only to preservation;
reflection consumes only the original completed native evaluation. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedCatalogRuntimeMutualMeaning
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
      RuntimeMatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
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
    (fun child _ => RecursiveNamedCatalogMutualMeaning.preserves_at_runtime functions extension faithful observations runtimeViews owners
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
    (fun child _ => RecursiveNamedCatalogMutualMeaning.reflects_at_runtime functions extension faithful observations runtimeViews
      uninitialized missing escaped prefixMatches profiles child header member)
    caller member represented heaps capture completed (Nat.le_refl size)
end ActualCalls


section Families
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}
  {fuel : Nat} {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {policy : AssignmentDiagnosticPolicy}

/-- Selecting runtime mode retains the same accepted profile; no Tree cast is used. -/
theorem runtime_profile
    (profile : RuntimeMatchProfileFor policy headers header compilation fuel expressionSyntax administrative registry faults) :
    Nonempty (RecursiveNamedCatalogMutualMeaning.MatchProfileForMode true policy headers header compilation fuel expressionSyntax administrative registry faults) := ⟨profile⟩

/-- The ordinary adapter retains the ordinary initial condition explicitly. -/
theorem ordinary_profile
    (profile : MatchProfileFor policy headers header compilation fuel expressionSyntax administrative registry faults) :
    Nonempty (RecursiveNamedCatalogMutualMeaning.MatchProfileForMode false policy headers header compilation fuel expressionSyntax administrative registry faults) := ⟨profile.toMatchProfileWith⟩

/-- Initial runtime validity is already the full actual Header field. -/
theorem actual_header : RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved header.context header.function.evidence := header.valid
end Families

abbrev unused_ledger := SourceCoreRecursiveNamedCatalogRuntimeMatchProfiles.fields_not_ordinary

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (word n))
private def pair (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value :=
  (.product .word .word, some (.product (word n) (word n)))
private def content : String := String.intercalate "\n" [
  "trait Marker<T> {}", "impl Marker<Word> {}",
  "function keep<T>(value:T) returns(T) where T:Marker { return value; }",
  "function stopped(n:Word) returns(Word) { { return n + 1; } let f = lam(item) { return keep(item); }; return f(n); }",
  "function self(n:Word) returns(Word) { { if (n == 0) { return 1; } else { return self(n - 1) + 1; } } let f = lam(item) { return keep(item); }; return f(n); }",
  "function matched(n:Word) returns(Word) { match ((n,n)) { case (0, picked) { return picked + 2; } default { return n + 3; } } let f = lam(item) { return keep(item); }; return f(n); }",
  "function broken(n:Word) returns(Word) { { let gap:Word; return gap; } let f = lam(item) { return keep(item); }; return f(n); }"
]

/-- These are actual whole compiled functions, with all template rows retained.
The runtime test does not construct a static profile for arbitrary lambda bodies;
its templates occur after the terminal block/match and remain unexecuted. -/
private def inspect (compiled : SourceCoreUnifiedCorpusSupport.Compiled) (name : String) : IO Unit := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let actual ← get "runtime mutual exact specialization"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  let generic ← match compiled.sourceProgram.functions.filter (·.declaration == key.declaration) with
    | [generic] => pure generic | _ => throw (IO.userError "runtime mutual source function missing")
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger == generic.solvedRequirements)
    "runtime mutual complete ordered template ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (row.predicate == predicate && !actual.assumptions.contains predicate)
          "runtime mutual unused template was promoted to an ordinary assumption"
      | _ => throw (IO.userError "runtime mutual template implementation fabricated")
    | _ => throw (IO.userError "runtime mutual template row missing or duplicated")
  let named ← match compiled.indexed.base.functions.filter (·.specialized.key == key) with
    | [named] => pure named | _ => throw (IO.userError "runtime mutual actual named row missing")
  require (reprStr named.specialized == reprStr actual && named.inputs.length == 1)
    "runtime mutual complete source specialization or ordered input changed"

private def finish (compiled : SourceCoreUnifiedCorpusSupport.Compiled) (name : String) (n fuel : Nat)
    (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [word n] fuel initial
  pure (← get "runtime mutual original checkpoint" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    "runtime mutual original heap prefix changed"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"runtime mutual full ordered heap changed: {reprStr final.heap}"

private def template_functions : IO Unit := do
  let names := ["stopped", "self", "matched", "broken"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "runtime mutual whole template functions" content names
  require (compiled.keys.length == names.length && compiled.indexed.base.functions.length == names.length + 1 &&
    compiled.indexed.secondPass.closures.length == names.length + 1)
    "runtime mutual actual complete cached rows changed"
  for name in names do inspect compiled name
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (word 983)⟩]}
  let successes : List (String × Nat × Nat × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("stopped", 5, 6, [present 5]),
    ("self", 0, 1, [present 0]),
    ("self", 2, 3, [present 2, present 1, present 0]),
    ("matched", 0, 2, [present 0, pair 0, present 0]),
    ("matched", 5, 8, [present 5, pair 5])]
  let complete ← successes.mapM fun test => finish compiled test.1 test.2.1 300000 initial
  let failed ← finish compiled "broken" 5 300000 initial
  let brokenKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "broken"
  let broken ← get "runtime mutual fault specialization" (SourceCompilationPlan.exactSpecialization compiled.validationPlan brokenKey)
  let missing ← match (SourceCoreDataPlaces.declaredBinders broken.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id | _ => throw (IO.userError "runtime mutual actual fault binder missing")
  for fuel in [0, 1, 43, 300000] do
    for (test, baseline) in successes.zip complete do
      let (name, n, expected, expectedCells) := test
      let observation ← finish compiled name n fuel initial
      require (reprStr observation == reprStr baseline) "runtime mutual full success resume changed"
      match observation with
      | .done actual final =>
        require (reprStr actual == reprStr (word expected)) "runtime mutual result changed"
        cells initial final expectedCells
        require (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          "runtime mutual final heap not deeply safe"
      | other => throw (IO.userError s!"runtime mutual unexpected success {reprStr other}")
    let observation ← finish compiled "broken" 5 fuel initial
    require (reprStr observation == reprStr failed) "runtime mutual full fault resume changed"
    match observation with
    | .fault (.uninitializedLocal actual) final =>
      require (actual == missing) "runtime mutual first fault binder changed"
      cells initial final [present 5, (.word, none)]
    | other => throw (IO.userError s!"runtime mutual unexpected fault {reprStr other}")

def run : IO Unit := do
  template_functions
  SourceCoreRecursiveNamedCatalogMatchMeaning.run
  IO.println "runtime catalog mutual: actual whole template functions / same complete ledger / self and mutual calls / independent grades / full heap and first fault / four resume budgets GREEN"

end Tests.SourceCoreRecursiveNamedCatalogRuntimeMutualMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedCatalogRuntimeProfileFactory
/-! Actual cached typing and entry data supply the body native context. The
same compiler inputs produce a runtime profile, without ordinary ledger
validity, arbitrary Profile providers or body execution assumptions. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreRecursiveNamedCatalogRuntimeProfileFactory
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds RecursiveNamedCatalogNativeContexts
open RecursiveNamedCatalogRuntimeProfileFactory NativeExpressionContextSupport

section Actual
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {administrative : Core.Context} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {tracked : Bool} {suffix : Core.Context}
  (inputs : Inputs tracked diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
    (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
    header.named.signature.functionType ambient.definitions)
  (support : supported (.lambda header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
  (complete : Complete headers) (globals : header.globals = base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include inputs cachedTyped support complete globals entry in
theorem actual_extraction : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :=
  extract_source inputs cachedTyped support complete globals entry

include inputs cachedTyped support complete globals entry in
theorem actual_provider (catalog : SignatureCatalogWellFormed values.checked.signatures) :
    ∃ result : Receipt diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ faults : FunctionCalls.FaultRep, result.extracted.diagnostics registry faults →
        ∃ profile : RuntimeMatchProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
            (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults,
          profile.flow = result.flow ∧ HEq profile.tree result.extracted.tree :=
  provider inputs cachedTyped support complete globals entry catalog

variable (result : Receipt diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (catalog : SignatureCatalogWellFormed values.checked.signatures) {faults : FunctionCalls.FaultRep}
  (interpreted : result.extracted.diagnostics registry faults)

theorem same_flow : (result.profile catalog interpreted).flow = result.flow := rfl

theorem same_tree : (result.profile catalog interpreted).tree = result.extracted.tree := rfl

include catalog interpreted in
theorem same_emitted_body : header.body = CompatibleStatements.finish header.output
    (result.profile catalog interpreted).flow header.fellThrough header.escaped :=
  (result.profile catalog interpreted).emitted

/-- Runtime validity does not drop the templates/unused rows in the source ledger. -/
theorem same_full_ledger :
    header.context.solvedRequirements = header.solved ∧ inputs.matchCompilation.solvedRequirements = header.solved :=
  ⟨header.valid.ledger, inputs.matchLedger⟩

include inputs in
theorem actual_expression_child {context : SourceSemantics.Context}
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = true)
    (signatures : context.signatures = values.checked.signatures)
    {scope : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source scope context)
    (syntaxTree : expressionSyntax id) (found : header.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType header.function.source context id node.type)
    (accepted : header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered) :
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation header.readFuel header.function.source
      context header.solved header.reasonAt scope id lowered :=
  inputs.expressions context closed residual signatures declarations syntaxTree found typed accepted

theorem actual_residual : header.context.typeVariables = [] ∧ header.context.residualTypeVariables = true :=
  RecursiveNamedSourceContextFacts.header_fields header
end Actual

abbrev unused_ledger := SourceCoreRecursiveNamedCatalogRuntimeMatchProfiles.fields_not_ordinary

def run : IO Unit := do
  SourceCoreRecursiveNamedCatalogRuntimeMutualMeaning.run
  SourceCoreRecursiveNamedCatalogNativeContexts.run
  IO.println "runtime profile factory: same cached code / actual body entry / full ledger / static compiler extraction and diagnostics GREEN"

end Tests.SourceCoreRecursiveNamedCatalogRuntimeProfileFactory
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPreparedCallEvidence
/-! Actual authenticated direct selection reaches nonempty prepared callee
dictionaries. Formal consumers keep independent source typing and the whole
ledger. Runtime inspection compares the actual public compiler's selected
record, raw evidence, ordered arguments and physical cache row. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedCallEvidence
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedPublicSpecializationMeaning CallableCoercionExpressionCertificates
open RecursiveNamedPreparedCallEvidence

abbrev actual_call := @RecursiveNamedPreparedCallEvidence.from_accepted
abbrev actual_retained_frame := @RecursiveNamedPreparedCallEvidence.callee_frame

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {caller : Specialized}
  {project : Projector} {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
  {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compiled.sourceProgram project caller compilation child fuel caller.function.typedBody scope
    id callee arguments instantiation reasonAt policy node output)
  (callerPrepared : Prepared compiled caller)
  (calleePrepared : Prepared compiled receipt.selection.specialized)

theorem actual_frame {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) caller.parameterSubstitution)
    (extended : MonoBindersExtend callerPrepared.view.source.owner callerPrepared.view.context
      callerPrepared.view.parameters types context) :
    Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
      instantiation.predicates calleePrepared.view.evidence ∧
    ∀ semantic, Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
      instantiation.predicates semantic → semantic = calleePrepared.view.evidence :=
  at_frame receipt callerPrepared calleePrepared wellFormed range extended

theorem actual_cache (globals : compilation.globals = compiled.indexed.base.globals) :
    receipt.native.signature = calleePrepared.named.signature ∧ receipt.native.index = calleePrepared.index ∧
      compiled.indexed.secondPass.closures[receipt.native.index]? = some calleePrepared.code := by
  obtain ⟨signature, slot⟩ := native_target receipt calleePrepared globals
  exact ⟨signature, slot, by simpa only [slot] using calleePrepared.cached⟩

theorem full_dictionaries :
    receipt.selection.available = callerPrepared.available ∧ receipt.selection.actual = calleePrepared.available :=
  ⟨caller_dictionary receipt callerPrepared, callee_dictionary receipt calleePrepared⟩

theorem retained_full_metadata
    (order : instantiation.parameterSubstitution.map Prod.fst =
      (receipt.selection.specialized.parameterSubstitution.map Prod.fst).reverse) :
    instantiation = CallableNamedCanonicalOrder.retainedInstantiation receipt.selection.specialized :=
  retained_metadata receipt order

theorem unused_rows_kept {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend callerPrepared.view.source.owner callerPrepared.view.context
      callerPrepared.view.parameters types context) :
    context.solvedRequirements = caller.function.solvedRequirements :=
  (RecursiveNamedPreparedCallEvidence.Prepared.context_fields callerPrepared extended).2.1
end Actual

section Boundaries

theorem same_goals_do_not_identify_trees (goal : ProgramPredicate) (first second : ProgramImplId)
    (different : first ≠ second) :
    (TraitEvidence.implementation goal first []).goal =
      (TraitEvidence.implementation goal second []).goal ∧
    TraitEvidence.implementation goal first [] ≠ .implementation goal second [] := by
  refine ⟨rfl, ?_⟩
  intro same
  exact different (TraitEvidence.implementation.inj same).2.1

theorem dictionary_keeps_order (first second : TypedTraitResolution.Evidence) :
    CallableNamedMetadata.environment [first, second, first] =
      [(SourceTypedRuntime.runtimeEvidenceGoal first, CallableNamedMetadata.evidence first),
       (SourceTypedRuntime.runtimeEvidenceGoal second, CallableNamedMetadata.evidence second),
       (SourceTypedRuntime.runtimeEvidenceGoal first, CallableNamedMetadata.evidence first)] := rfl

theorem duplicate_requirements_not_unique (context : SourceSemantics.Context) (row : SolvedRequirement) :
    ¬ RequirementIdsUnique {context with solvedRequirements := [row, row]} := by
  simp [RequirementIdsUnique]

end Boundaries

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def content := String.intercalate "\n" [
  "trait Mark<T> {}", "trait Stamp<T> {}", "impl Mark<Word> {}", "impl Stamp<Word> {}",
  "function keep<A, B>(value: A, unused: B) returns (A) where A: Mark, A: Stamp, A: Mark { return value; }",
  "function relay<A, B>(value: A, unused: B) returns (A) where A: Stamp, A: Mark { let retained: Word = 3; return keep(value, unused); }",
  "function missing<T>(value: T) returns (T) where T: Mark { let absent: T; return absent; }",
  "function closed() returns (Word) { return relay(7, true); }",
  "function constrained(value: Word) returns (Word) where Word: Mark, Word: Stamp { return relay(value, false); }",
  "function fault() returns (Word) { return missing(9); }"
]

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let indexed := compiled.indexed
  let base := indexed.base
  let diagnostics ← match base.diagnostics with
    | some value => pure value.program | none => throw (IO.userError "prepared call diagnostics absent")
  let diagnostics := match base.callableContext with
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable} | none => diagnostics
  let parents ← get "actual parent preparation" (SourceCoreStageCodebook.prepareContexts base.sourceProgram base.plan
    (base.locals.bindings.flatMap (·.instances)))
  let mut calls := 0
  let mut qualified := 0
  let mut repeated := 0
  let mut unusedRows := 0
  for named in base.functions do
    let caller := named.specialized
    let source := caller.function.typedBody
    let ledger := caller.function.solvedRequirements
    let representation := (CallableIndexedNamedGeneration.representation indexed).atContext named.signature.key []
    let compilation := CallableIndexedNamedGeneration.context indexed named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let own ← match diagnostics.base.find? named.signature.key with
      | some own => pure own | none => throw (IO.userError "prepared caller diagnostics absent")
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
      base.locals parents own.assignments diagnostics compilation base.callableContext none none
    let callables := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
    let available ← get "full prepared caller dictionary" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
    for item in source.nodes do
      if let .expression node := item then
        if let .call callee args (.declaration instantiation) := node.form then
          let actual ← get "actual contextual direct call" (lower indexed.fuel source scope node.id reasonAt)
          let special ← get "actual authenticated some branch" (SourceCoreEvidence.lowerWithProjector base.sourceProgram
            representation.expressions.projectType caller compilation lower (indexed.fuel - 1) source scope node.id reasonAt callables)
          require (special == some actual) "authenticated branch is not actual emitted code"
          discard <| get "full actual callee metadata" (SourceCompilationPlan.validateDirectDeclarationCallee source node.id callee instantiation)
          let target ← get "actual full instantiation target" (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
          let key ← get "actual call edge" (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
          let selected ← get "actual full selected specialization" (SourceCompilationPlan.exactSpecialization base.plan key)
          let produced ← get "actual complete materialization" (SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation)
          discard <| get "full actual authentication" (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence base.sourceProgram.signatures key selected.assumptions produced)
          let canonical ← get "same prepared callee resolver" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram selected.key selected.assumptions)
          require (reprStr produced == reprStr canonical && !produced.isEmpty && selected.key == key)
            "actual dictionary differs from full prepared callee evidence"
          let (signature, slot) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
            | [row] => pure row | _ => throw (IO.userError "actual global selection is not singleton")
          let calleeNamed ← match base.functions[slot]? with
            | some value => pure value | none => throw (IO.userError "actual physical callee row absent")
          require (calleeNamed.specialized == selected && calleeNamed.signature == signature &&
            reprStr instantiation == reprStr (CallableNamedCanonicalOrder.retainedInstantiation selected))
            "full callee/retained metadata/physical signature changed"
          let cached ← match indexed.secondPass.closures[slot]? with
            | some value => pure value | none => throw (IO.userError "actual cached callee absent")
          require (match cached with | .lambda .. => true | _ => false) "actual callee cache is not a closure"
          let children ← get "actual ordered arguments" (args.mapM (fun id => lower (indexed.fuel - 1) source scope id reasonAt))
          let packed := SourceCoreCalls.packArguments children
          require (node.coercions.isEmpty && actual == ⟨signature.resultType,
            SourceCoreCalls.call signature (scope.length + compilation.administrativePrefix + slot) packed.expression compilation.internalReason⟩)
            "actual direct call changed ordered arguments/code/slot"
          require (children.map (·.type) == calleeNamed.inputs.map Prod.snd && packed.type == signature.parameterType)
            "actual native argument vector changed"
          let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
            base.globals.map (·.referenceType) ++ [.cell indexed.ancestry.layout.frame.type]
          require (Core.infer? nativeContext actual.expression indexed.layouts.definitions == some (LanguageResult.resultType actual.type))
            "actual call failed native checking"
          calls := calls + 1
          if !caller.assumptions.isEmpty then qualified := qualified + 1
          if produced.length == 3 then
            repeated := repeated + 1
            require (produced[0]? == produced[2]? && produced[0]? != produced[1]?) "repeated predicate dictionary lost original order"
            require (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence base.sourceProgram.signatures key selected.assumptions produced.reverse).toOption.isSome
              "symmetric duplicate order should authenticate identically"
            let reordered ← match produced with
              | [first, second, third] => pure [second, first, third]
              | _ => throw (IO.userError "expected ordered triple")
            require (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence base.sourceProgram.signatures key selected.assumptions reordered).toOption.isNone
              "same multiset authenticated in a different order"
          let unused := ledger.filter (fun row => !(node.requirements.contains row.id))
          unusedRows := unusedRows + unused.length
          require (reprStr ledger == reprStr caller.function.solvedRequirements) "unused rows removed"
          if !unused.isEmpty then
            let augmented := {caller with function := {caller.function with solvedRequirements := unused ++ ledger ++ unused}}
            let again ← get "unused full ledger additions" (SourceCompilationPlan.exactDirectCallRuntimeEvidence augmented node available instantiation)
            require (reprStr again == reprStr produced) "unreached rows changed actual reached selection"
  require (calls ≥ 4 && qualified ≥ 2 && repeated ≥ 1 && unusedRows > 0)
    s!"nonempty prepared call coverage {calls}/{qualified}/{repeated}/{unusedRows}"

private def full_result (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) : IO (SourceTypedRuntime.RunResult × String) := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel
  let final ← get "actual prepared call resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution | none => throw (IO.userError "original native result absent")
  match execution.completion.result.native.observation with
  | .succeeded _ _ | .failed _ _ => pure ()
  | _ => throw (IO.userError "original native run unfinished")
  pure (final.observation, reprStr execution.completion.result.native.observation)

def run : IO Unit := do
  let names := ["closed", "constrained", "fault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "nonempty prepared calls" content names
  inspect compiled
  for (name, arguments, expected) in [("closed", [], some (word 7)), ("constrained", [word 17], some (word 17)), ("fault", [], none)] do
    let baseline ← full_result compiled name arguments 300000
    for fuel in [0, 1, 43, 300000] do
      let actual ← full_result compiled name arguments fuel
      require (reprStr actual == reprStr baseline) "same full source/native heap changed on resume"
      match expected, actual.1 with
      | some value, .done result state =>
        require (reprStr result == reprStr value) "prepared nonempty dictionary result changed"
        require (state.heap.any (fun cell => reprStr cell.value == reprStr (some (word 3)))) "unused initializer cell lost"
      | none, .fault (.uninitializedLocal _) state =>
        require (state.heap.any (fun cell => cell.value.isNone)) "fault heap lost uninitialized cell"
      | _, _ => throw (IO.userError "prepared nonempty call outcome changed")
  IO.println "prepared call evidence: actual some branch/nonempty full dictionaries/repeated goals/retained order/unused rows/physical cache/ordered args/full native+source heaps/resume GREEN"
end Tests.SourceCoreRecursiveNamedPreparedCallEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedCallEvidenceBounds
/-! Actual accepted named expressions keep one caller dictionary through all
ordered children. The catalog closes callee BodyBelow internally with the same
static profile family; reflection takes no source trace or preservation law.
Ordinary source flags, coercion-free admission, all ranges, source typing,
full ledger validity, diagnostic interpretation and entry authority remain
independent conditions. The runtime fixture reuses the real nonempty dictionary
compiler audit, including duplicate predicates and original argument order. -/
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedCallEvidenceBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates

abbrev actual_prepared_tree := @RecursiveNamedExpressionCompilerCertificates.tree_of_contextual_prepared
abbrev actual_header := @RecursiveNamedPreparedHeaders.Prepared.retained_header_with_evidence
abbrev actual_extraction := @RecursiveNamedCatalogRuntimeProfileFactory.extract_source_with

section ActualCompilation

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
      RuntimeMatchProfileForWith true diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {callerCompilation : SourceCoreFunctions.Context} (evidence : Dynamic.EvidenceEnvironment)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
theorem actual_preserves_at
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : RuntimeAdmission source admitted) (coverage : ReachedCoverage headers callerCompilation source admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes headers context)
    (emptySelected : SelectedEmptyEvidence headers callerCompilation source admitted)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered callerCompilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers callerCompilation source context admitted)
    (policyFor : PolicyForWith (headers := headers) (some evidence) policy callerCompilation readFuel values source context scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callableProfile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel callerCompilation source scope id reasonAt = .ok lowered)
    (valid : CompatibleRuntimeContextValidity.Valid callerCompilation.solvedRequirements context evidence)
    (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  have receipt := RecursiveNamedExpressionCompilerCertificates.tree_of_functions_at_runtime_evidence (some evidence)
    admission coverage sourceTypes emptySelected order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active callableProfile fragmentCoercions coercions allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedCatalogMutualMeaning.expression_preserves_at_runtime_evidence functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles evidence valid unique callerUninitialized callerMissing size receipt rootFound


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
theorem actual_reflects_at
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : RuntimeAdmission source admitted) (coverage : ReachedCoverage headers callerCompilation source admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes headers context)
    (emptySelected : SelectedEmptyEvidence headers callerCompilation source admitted)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered callerCompilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers callerCompilation source context admitted)
    (policyFor : PolicyForWith (headers := headers) (some evidence) policy callerCompilation readFuel values source context scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callableProfile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel callerCompilation source scope id reasonAt = .ok lowered)
    (valid : CompatibleRuntimeContextValidity.Valid callerCompilation.solvedRequirements context evidence)
    (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  have receipt := RecursiveNamedExpressionCompilerCertificates.tree_of_functions_at_runtime_evidence (some evidence)
    admission coverage sourceTypes emptySelected order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active callableProfile fragmentCoercions coercions allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedCatalogMutualMeaning.expression_reflects_at_runtime_evidence functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles evidence valid callerUninitialized callerMissing size receipt rootFound

end ActualCompilation

section Boundaries
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {code : SourceCoreBasic.LoweredExpr}

theorem same_tree
    (receipt : RuntimeExpressionsWith (some evidence) headers compilation readFuel source context solved reasonAt scope id code) :
    CompatibleExpressionCalls.Tree
      (RecursiveNamedCallEvidenceHeads.Head headers compilation source context evidence)
      readFuel values source context solved reasonAt scope id code := receipt.choose

theorem unused_rows_kept (valid : CompatibleRuntimeContextValidity.Valid solved context evidence) :
    context.solvedRequirements = solved := valid.ledger

theorem dictionary_keeps_duplicates (first second : TypedTraitResolution.Evidence) :
    CallableNamedMetadata.environment [first, second, first] =
      [(SourceTypedRuntime.runtimeEvidenceGoal first, CallableNamedMetadata.evidence first),
       (SourceTypedRuntime.runtimeEvidenceGoal second, CallableNamedMetadata.evidence second),
       (SourceTypedRuntime.runtimeEvidenceGoal first, CallableNamedMetadata.evidence first)] := rfl

theorem empty_family_unchanged :
    RecursiveNamedCallEvidenceHeads.Calls none headers compilation source context =
      RecursiveNamedCatalog.Head headers compilation source context := rfl

theorem duplicate_requirement_ids_rejected (row : SolvedRequirement) :
    ¬ RequirementIdsUnique {context with solvedRequirements := [row, row]} := by
  simp [RequirementIdsUnique]

end Boundaries

def run : IO Unit := do
  SourceCoreRecursiveNamedPreparedCallEvidence.run
  SourceCoreRecursiveNamedCatalogRuntimeMutualMeaning.run

end Tests.SourceCoreRecursiveNamedCallEvidenceBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPreparedHeaderPolicies
/-! The actual named matcher checks in its original table and emits exactly
that code under the final frame/marker definitions. Source grammar, independent
source typing and diagnostic interpretation remain separate. Runtime inspection
uses explicit child callbacks; whole callable semantics are covered by existing
regressions, without constructing Header proofs from native comparisons. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedHeaderPolicies
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedCatalog RecursiveNamedPublicSpecializationMeaning
open RecursiveNamedPreparedHeaderPolicies CompatibleMatchAmbientLowering

abbrev actual_static_inputs := @RecursiveNamedPreparedHeaderPolicies.Prepared.inputs
abbrev actual_exact_policy := @RecursiveNamedCatalogRuntimeProfileFactory.Inputs.of_exact
abbrev actual_body_extraction := @GenericImperativeMatch.extraction_of_typed_body_with_lowering

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row) {instantiation : DeclarationInstantiation}
  {header : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions
    (Program.ofChecked compiled.sourceProgram)}
  (atHeader : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
include atHeader

theorem actual_callback : PolicySuccess header.policy (RecursiveNamedPreparedHeaderPolicies.Prepared.ambientMatch prepared) :=
  RecursiveNamedPreparedHeaderPolicies.Prepared.header_match prepared atHeader

theorem actual_binder (scope : SourceCoreBasic.Scope) (binder : TypedBinder) (closed : binder.scheme.quantified = []) :
    header.policy.lowerBinder header.function.source scope binder =
      SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked header.function.source scope binder :=
  RecursiveNamedPreparedHeaderPolicies.Prepared.header_binder prepared atHeader scope binder closed

omit atHeader in
theorem actual_tables_differ :
    (RecursiveNamedPreparedHeaderPolicies.Prepared.baseMatch prepared).definitions ≠
      compiled.indexed.layouts.definitions := by
  intro same
  have lengths := congrArg List.length same
  rw [CallableIndexedAmbient.definitions_exact compiled.indexed] at lengths
  simp only [List.length_append, List.length_cons] at lengths
  change compiled.compatible.checked.catalog.definitions.length =
    compiled.compatible.checked.catalog.definitions.length + (_ + 1) at lengths
  omega

omit atHeader in
theorem actual_context_keeps_fields :
    (RecursiveNamedPreparedHeaderPolicies.Prepared.ambientMatch prepared).values =
        (RecursiveNamedPreparedHeaderPolicies.Prepared.baseMatch prepared).values ∧
    (RecursiveNamedPreparedHeaderPolicies.Prepared.ambientMatch prepared).solvedRequirements =
        prepared.named.specialized.function.solvedRequirements ∧
    (RecursiveNamedPreparedHeaderPolicies.Prepared.ambientMatch prepared).sourceCells =
        (RecursiveNamedPreparedHeaderPolicies.Prepared.baseMatch prepared).sourceCells := ⟨rfl, rfl, rfl⟩
end Actual

/-- Only the original empty-context pattern proof is extended. -/
theorem same_pattern {compilation : SourceCoreCompatibleDataMatches.Context} {native : DataEnvironment}
    (extension : compilation.definitions.Extends native)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreBasic.Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : SourceCoreCompatibleDataMatches.CertifiedPattern compilation.definitions}
    (accepted : SourceCoreCompatibleDataMatches.compilePattern compilation fuel source scope site span expected pattern = .ok compiled) :
    SourceCoreCompatibleDataMatches.compilePattern (withDefinitions compilation native) fuel source scope site span expected pattern =
      .ok ⟨compiled.pattern, compiled.typed.extend_definitions extension⟩ :=
  compilePattern_success compilation native extension accepted

/-- A valid final-table child need not typecheck in the base table. -/
theorem child_cannot_be_lowered_to_base :
    HasType [.cell (.namedData ⟨0⟩)] (.lambda (.namedData ⟨0⟩) (.namedData ⟨0⟩) (.var 0))
      (.function (.namedData ⟨0⟩) (.namedData ⟨0⟩)) [⟨[.unit]⟩] ∧
    ¬ HasType [.cell (.namedData ⟨0⟩)] (.lambda (.namedData ⟨0⟩) (.namedData ⟨0⟩) (.var 0))
      (.function (.namedData ⟨0⟩) (.namedData ⟨0⟩)) [] := by
  constructor
  · apply infer_sound; decide
  · intro typed
    have inferred := infer_complete typed
    cases inferred

theorem complete_order (compilation : SourceCoreCompatibleDataMatches.Context) (native : DataEnvironment)
    (row : SolvedRequirement) :
    (withDefinitions {compilation with solvedRequirements := row :: row :: compilation.solvedRequirements} native).solvedRequirements =
      row :: row :: compilation.solvedRequirements := rfl

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def content : String := String.intercalate "\n" [
  "enum Choice { Left(Word), Right(Word) }",
  "function tuple(value: (Word, Word)) returns (Word) { match (value) { case (0, x) { return x; } case (x, y) { return x + y; } } }",
  "function choose(value: Word) returns (Word) { match (value) { case 0 { return 3; } default { return 5; } } }",
  "function nominal(value: Choice) returns (Word) { match (value) { case .Left(x) { return x; } case .Right(y) { return y; } } }"
]

/-- Explicit child callbacks isolate the definitions-only compiler bridge.
The allocator, actual source, original scopes and full nominal registry are real. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let final := compiled.indexed.layouts.definitions
  let base := compiled.compatible.checked.catalog.definitions
  require (base.length < final.length && final.take base.length == base) "ambient definition prefix lost"
  let mut count := 0
  for named in compiled.indexed.base.functions do
    let source := named.specialized.function.typedBody
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let cells := some (CallableIndexedNamedGeneration.allocator compiled.indexed named)
    let original : SourceCoreCompatibleDataMatches.Context :=
      ⟨.initial compiled.compatible.checked, named.specialized.function.solvedRequirements, cells, none⟩
    let ambient := withDefinitions original final
    let nativeContext := SourceCoreLocalCell.coreContext scope ++
      [named.signature.parameterType] ++ compiled.indexed.base.globals.map (·.referenceType) ++
      [.cell compiled.indexed.ancestry.layout.frame.type]
    for node in source.nodes do
      match node with
      | .statement statement => match statement.form with
        | .matchWith resolution =>
          let scrutinee ← match source.lookupExpression? resolution.scrutinee with
            | some node => pure node | none => throw (IO.userError "ambient scrutinee missing")
          let type ← get "actual scrutinee projection" (original.checked.catalog.project scrutinee.type)
          let childExpression : SourceCoreCompatibleDataMatches.ExpressionLowerer := fun _ _ _ _ _ =>
            .ok ⟨type, OptionalCell.read type (.var 0) (Word.ofNatModulo 91)⟩
          let childBody : SourceCoreCompatibleDataMatches.BodyLowerer := fun _ _ _ _ _ _ _ =>
            .ok (LocalLoop.returned (.word (Word.ofNatModulo 73)))
          let code ← get "actual base match" (SourceCoreCompatibleDataMatches.lowerWithReasons original childExpression childBody
            100 source scope statement.id resolution .word (fun _ => Word.ofNatModulo 93) (Word.ofNatModulo 95))
          let lifted ← get "ambient same match" (SourceCoreCompatibleDataMatches.lowerWithReasons ambient childExpression childBody
            100 source scope statement.id resolution .word (fun _ => Word.ofNatModulo 93) (Word.ofNatModulo 95))
          require (code == lifted) "ambient normalization changed ordered whole match code"
          require (infer? nativeContext code final == some (LocalLoop.resultType .word)) "actual child/admin typing lost"
          require (infer? nativeContext code base == none) "base unexpectedly contains actual administrative markers"
          for arm in resolution.cases do
            let before ← get "actual pattern" (SourceCoreCompatibleDataMatches.compilePattern original 100 source
              ((resolution.hiddenScrutinee, type) :: scope) statement.id arm.span scrutinee.type arm.pattern)
            let after ← get "ambient pattern" (SourceCoreCompatibleDataMatches.compilePattern ambient 100 source
              ((resolution.hiddenScrutinee, type) :: scope) statement.id arm.span scrutinee.type arm.pattern)
            require (reprStr before.pattern == reprStr after.pattern) "ambient pattern raw metadata/order changed"
          count := count + 1
        | _ => pure ()
      | _ => pure ()
  require (count == 3) "ambient actual match inventory changed"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "prepared header ambient policies" content ["tuple", "choose", "nominal"]
  inspect compiled
  IO.println "prepared header policies: actual base/final tables / same ordered match code / ambient children and allocators / default and nominal patterns GREEN"

end Tests.SourceCoreRecursiveNamedPreparedHeaderPolicies
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPreparedHeaders
/-! Actual compiler receipts assemble the Header without input Header/native
projection callbacks. Independent raw source typing and ordinary admission stay
visible. These consumers do not supply a runtime Entry or semantic profile. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedHeaders
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedPublicSpecializationMeaning RecursiveNamedPreparedHeaders RecursiveNamedCatalog

section Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {values : SourceCoreCompatibleValues.Context}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (range : ParameterSubstitution.RangeWellFormed
    (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
  (closed : row.assumptions = []) (ordinaryReturn : row.function.returnComptime = false)
  (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)

include prepared wellFormed range closed ordinaryReturn ordinaryParameters in
theorem actual_canonical
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok prepared.named.signature.key) :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared (CallableNamedMetadata.instantiation row) header :=
  RecursiveNamedPreparedHeaders.Prepared.canonical_header prepared wellFormed range closed ordinaryReturn ordinaryParameters target

include prepared wellFormed range closed ordinaryReturn ordinaryParameters in
theorem actual_retained
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key) :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared (CallableNamedCanonicalOrder.retainedInstantiation row) header :=
  RecursiveNamedPreparedHeaders.Prepared.retained_header prepared wellFormed range closed ordinaryReturn ordinaryParameters target

include prepared wellFormed range in
theorem source_shape_before_native_pack : prepared.named.signature.parameterType =
    SourceCoreCompatibleCatalog.packTypes (prepared.named.inputs.map Prod.snd) :=
  RecursiveNamedPreparedHeaders.Prepared.parameter_pack prepared wellFormed range

variable {instantiation : DeclarationInstantiation}
  {header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
    (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include prepared aligned in
theorem actual_full_cache :
    header.named.specialized = row ∧ header.slot = prepared.index ∧
    header.bindings = prepared.named.inputs ∧
    HEq header.compiled compiled.indexed.secondPass ∧
    header.compiled.closures[header.slot]? = some prepared.code := by
  refine ⟨aligned.named ▸ prepared.same, aligned.slot, aligned.bindings, aligned.secondPass, ?_⟩
  rw [header.cached]
  have emitted := prepared.compilation.emitted
  rw [aligned.named, aligned.code]
  exact congrArg some emitted.symm

include prepared aligned in
theorem exact_policy_and_body :
    header.policy = RecursiveNamedPreparedHeaders.Prepared.policy prepared ∧
    SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body ∧
    (∃ facts, BodyHasType header.function.source header.context header.function.resultType facts) :=
  ⟨aligned.policy, aligned.accepted, aligned.bodyTyped⟩

include prepared aligned in
theorem actual_runtime_context : CompatibleRuntimeContextValidity.Valid
    prepared.named.specialized.function.solvedRequirements header.context prepared.view.evidence := by
  have valid := header.valid
  rw [aligned.solved, aligned.function] at valid
  exact valid

include prepared aligned closed in
theorem actual_closed_dictionary : header.function.evidence = [] := by
  rw [aligned.function]
  exact RecursiveNamedPreparedHeaders.Prepared.evidence_empty prepared closed

include prepared aligned in
theorem full_parameter_order :
    header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) =
      prepared.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)) := by
  rw [aligned.bindings]

include prepared in
theorem constrained_not_empty_header (constrained : row.assumptions ≠ []) :
    ¬ ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header ∧
        header.named.specialized.assumptions = [] := by
  rintro ⟨header, aligned, closed⟩
  apply constrained
  rw [aligned.named, prepared.same] at closed
  exact closed

include prepared in
theorem staged_return_not_header (staged : row.function.returnComptime = true) :
    ¬ ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header := by
  rintro ⟨header, aligned⟩
  have ordinary := header.ordinaryReturn
  rw [aligned.named, prepared.same, staged] at ordinary
  cases ordinary
end Prepared

/-- The actual public compiler, original retained row and full target lookup
supply the row-to-Header bridge in one application. -/
abbrev actual_public := @RecursiveNamedPreparedHeaders.of_public_compile

/-- Packing alone cannot recover the raw binder count. The real preparation
and source certificate are necessary even for Unit. -/
theorem packed_unit_does_not_identify_inputs :
    SourceCoreCompatibleCatalog.packTypes ([] : List Core.Ty) =
      SourceCoreCompatibleCatalog.packTypes [.unit] ∧ ([] : List Core.Ty) ≠ [.unit] := by
  exact ⟨rfl, by intro equal; cases equal⟩

end Tests.SourceCoreRecursiveNamedPreparedHeaders
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPreparedInitialization
/-! Formal consumers start from actual compiled preparation. They request no
lambda-row decoding equation, ordered cache-signature law, global-signature
law or syntactic support input. Independent source headers and their ledger
remain explicit. Native IO audits actual cached code and original bootstrap. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedInitialization
open Solcore Core Frontend SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload RecursiveNamedCatalog
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

section Formal
variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)

include accepted in
theorem actual_typed_initial_store :
    ∃ world, RuntimeStoreHasTypes world (RecursiveNamedCatalogPreparedInitialization.store compiled)
      compiled.indexed.layouts.definitions :=
  RecursiveNamedCatalogPreparedInitialization.typed accepted

include accepted in
theorem actual_cached_support {slot : Nat} {code : Expr}
    (cached : compiled.indexed.secondPass.closures[slot]? = some code) :
    NativeExpressionContextSupport.supported code (compiled.indexed.base.globals.length + 1) = true :=
  RecursiveNamedCatalogPreparedInitialization.supported_cached accepted cached

variable {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
  (ledger : Ledger headers compiled.indexed.secondPass.closures)
  (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (locals : ∀ header, header ∈ headers → header.function.context.locals = [])
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)

include accepted ledger sizes locals definitions in
theorem actual_source_entry
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩
        (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      Nonempty (Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled)
        (RecursiveNamedCatalogPreparedInitialization.environment compiled)) :=
  RecursiveNamedCatalogPreparedInitialization.entry compiled headers ledger sizes locals accepted definitions functions registry

include accepted ledger sizes locals definitions in
theorem actual_completed_source_entry
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧ ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩ finalStore ∧
      Nonempty (Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ finalStore (RecursiveNamedCatalogPreparedInitialization.environment compiled)) :=
  RecursiveNamedCatalogPreparedInitialization.completed_entry compiled headers ledger sizes locals accepted definitions functions registry completed
end Formal

private def content : String := String.intercalate "\n" [
  "function step(value: Word) returns (Word) { return value + 1; }",
  "function left(n: Word) returns (Bool) { if (n == 0) { return true; } return right(n - 1); }",
  "function right(n: Word) returns (Bool) { if (n == 0) { return false; } return left(n - 1); }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { let extra = step(seed); return lam(value: Word) -> Word { extra += value; return extra; }; }",
  "function terminal(flag: Bool) returns (Word) { if (flag) { return 7; } else { return 9; } }",
  "function failed() returns (Word) { let gap: Word; return gap; }",
  "function zero() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def finish (state : State) : IO (Value × Store) :=
  match runStateful 300000 state with
  | .done value store => pure (value, store)
  | other => throw (IO.userError s!"prepared initialization did not finish: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "prepared catalog initialization" content
    ["left", "right", "make", "terminal", "failed", "zero"]
  let recipe ← get "actual prepared initialization recipe" (SourceCoreIndexedSession.Recipe.prepare compiled)
  let rows := RecursiveNamedCachedRows.rows compiled
  let base := compiled.indexed.base
  require (rows.length == base.functions.length && rows.length == base.globals.length)
    "actual complete ordered cache length changed"
  require (reprStr (rows.map LambdaRow.expression) == reprStr compiled.indexed.secondPass.closures)
    "actual entire cached lambda code changed"
  for (row, slot) in rows.zipIdx do
    let named ← match base.functions[slot]? with
      | some named => pure named | none => throw (IO.userError "actual row lost ordered named function")
    let signature ← match base.globals[slot]? with
      | some signature => pure signature | none => throw (IO.userError "actual row lost full signature")
    require (signature == named.signature && row.parameter == signature.parameterType &&
      row.result == LanguageResult.resultType signature.resultType)
      "full prepared row signature/order changed"
    require (NativeExpressionContextSupport.supported row.expression (base.globals.length + 1))
      "actual cached support depends on an extra wrapper input"
  let expected := RecursiveNamedCatalogPreparedInitialization.store compiled
  let canonical := RecursiveNamedCatalogPreparedInitialization.environment compiled
  let (value, store) ← finish (.initial recipe.bootstrap [] [])
  require (reprStr store == reprStr expected && reprStr value == reprStr (Value.inRight .word .unit))
    "actual prepared bootstrap result/store changed"
  for (row, slot) in rows.zipIdx do
    let expectedClosure : Value := .inRight .unit (installedValue canonical slot row)
    require (reprStr (store.read? (RecursiveNamedCatalogInitialization.location base.globals slot)) ==
      reprStr (some expectedClosure)) "actual complete stored closure/capture changed"
    match expectedClosure with
    | .inRight _ (.closure parameter result body captured) =>
      require (infer? (parameter :: captured.map Value.type) body compiled.indexed.layouts.definitions == some result)
        "actual prepared stored body/capture typing changed"
    | _ => throw (IO.userError "prepared actual row did not produce a closure")
  for fuel in [0, 1, 43, 300000] do
    let resumed ← match runStateful fuel (.initial recipe.bootstrap [] []) with
      | .done value store => pure (value, store)
      | .outOfFuel state => finish state
      | other => throw (IO.userError s!"actual prepared bootstrap failed: {reprStr other}")
    require (reprStr resumed == reprStr (value, store)) s!"prepared bootstrap resume changed {fuel}"
  IO.println "prepared catalog initialization: actual whole cache rows/signatures/code/support, full stored captures and bootstrap resume GREEN"

end Tests.SourceCoreRecursiveNamedPreparedInitialization
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPreparedParameterProjections
/-! Consumers retain actual preparation slots, binder positions and raw types.
Packed types alone do not identify a parameter vector of unknown arity. The
runtime fixture inspects every real prepared input and its accumulated scope. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedParameterProjections
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedPreparedParameterProjections

section Formal
variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {slot : Nat} {named : SourceCoreGeneralFunctions.Function}
  (selected : compiled.indexed.base.functions[slot]? = some named)

include selected in
theorem actual_preparation :
    ∃ specialized, compiled.compatible.prepared.plan.specializations.reverse[slot]? = some specialized ∧
      SourceCoreGeneralFunctions.prepareFunctionWithRepresentation compiled.sourceProgram
        (SourceCoreCompatibleFunctions.representation (.initial compiled.compatible.checked) compiled.compilationFuel)
        specialized = .ok named := cached_preparation compiled selected

include selected in
theorem actual_binder_order :
    named.inputs.map Prod.fst = named.specialized.function.typedBody.inputs :=
  (cached_inputs compiled selected).1

include selected in
theorem actual_prefix {position : Nat} {binding : TypedBinder × Core.Ty}
    (found : named.inputs[position]? = some binding) :
    SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked
      named.specialized.function.typedBody
      ((named.inputs.take position).reverse.map (fun item => (item.1.id, item.2))) binding.1 = .ok binding.2 :=
  (cached_inputs compiled selected).2 position binding found

include selected in
theorem actual_projections :
    (named.inputs.map (fun binding => binding.1.scheme.body)).mapM compiled.compatible.checked.catalog.project =
      .ok (named.inputs.map Prod.snd) := cached_projected compiled selected

/-- The Header's source binders agree with the actual prepared list. The result
still names the actual native vector, not the Header's separately supplied one. -/
theorem actual_header_raw {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment}
    {program : SourceSemantics.Program} (header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values definitions program)
    (selectedHeader : compiled.indexed.base.functions[header.slot]? = some header.named) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM compiled.compatible.checked.catalog.project =
      .ok (header.named.inputs.map Prod.snd) := by
  have same := header.parameters.symm.trans header.agreement.parameters
  have raw := congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) same
  simp only [List.map_map, Function.comp_def] at raw
  rw [raw]
  exact cached_projected compiled selectedHeader
end Formal

theorem packed_unit_arity_boundary :
    SourceCoreCompatibleCatalog.packTypes [] = SourceCoreCompatibleCatalog.packTypes [.unit] ∧
      ([] : List Core.Ty) ≠ [.unit] := by decide

theorem packed_product_arity_boundary :
    SourceCoreCompatibleCatalog.packTypes [.product .word .bool] =
      SourceCoreCompatibleCatalog.packTypes [.word, .bool] ∧
      ([.product .word .bool] : List Core.Ty) ≠ [.word, .bool] := by decide

private def content : String := String.intercalate "\n" [
  "function empty() {}",
  "function unitArg(value: Unit) returns (Unit) { return value; }",
  "function mixed(first: Word, middle: Bool, last: Word) returns (Word) { return first + last; }",
  "function tupleArg(value: (Word, Bool)) returns (Word) { return 3; }",
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function fail(first: Word, second: Word) returns (Word) { let gap: Word; return gap; }",
  "function rootUnit() returns (Unit) { return unitArg(()); }",
  "function rootMixed() returns (Word) { return mixed(7, true, 7); }",
  "function rootTuple() returns (Word) { return tupleArg((7, true)); }",
  "function rootGeneric() returns (Word) { return choose(9, false); }",
  "function rootFault() returns (Word) { return fail(5, 5); }"
]
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let representation := SourceCoreCompatibleFunctions.representation (.initial compiled.compatible.checked) compiled.compilationFuel
  let mut emptyCount := 0
  let mut singletonCount := 0
  let mut manyCount := 0
  let mut genericCount := 0
  let mut total := 0
  for (named, slot) in compiled.indexed.base.functions.zipIdx do
    let specialized ← match compiled.compatible.prepared.plan.specializations.reverse[slot]? with
      | some specialized => pure specialized
      | none => throw (IO.userError "prepared parameter specialization slot missing")
    let actual ← get "actual named preparation" (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation
      compiled.sourceProgram representation specialized)
    require (reprStr actual == reprStr named) "full prepared function/slot changed"
    require (reprStr (named.inputs.map Prod.fst) == reprStr specialized.function.typedBody.inputs)
      "original ordered input binders changed"
    if named.inputs.isEmpty then emptyCount := emptyCount + 1
    else if named.inputs.length == 1 then singletonCount := singletonCount + 1
    else manyCount := manyCount + 1
    if !specialized.parameterSubstitution.isEmpty then genericCount := genericCount + 1
    for (binding, position) in named.inputs.zipIdx do
      let preceding := (named.inputs.take position).reverse.map (fun item => (item.1.id, item.2))
      let native ← get "actual input prefix admission"
        (representation.expressions.lowerBinder specialized.function.typedBody preceding binding.1)
      require (native == binding.2) "actual binder native type changed"
      let projected ← get "actual raw input projection" (compiled.compatible.checked.catalog.project binding.1.scheme.body)
      require (projected == binding.2) "raw binder projection changed"
      require (preceding.length == position) "actual ordered prefix lost a binder"
      total := total + 1
    let vector ← get "actual ordered native input vector"
      ((named.inputs.map (fun binding => binding.1.scheme.body)).mapM compiled.compatible.checked.catalog.project)
    require (vector == named.inputs.map Prod.snd) "actual whole native vector/order changed"
  require (emptyCount == 6 && singletonCount == 2 && manyCount == 3 && genericCount == 1 && total == 9)
    s!"prepared parameter fixture coverage changed {emptyCount}/{singletonCount}/{manyCount}/{genericCount}/{total}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (fuel : Nat)
    (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
  pure (← get "prepared parameters public resume" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "prepared parameters initial heap changed"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"prepared parameters full ordered source cells changed: {reprStr final.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named prepared parameter projections" content
    ["empty", "rootUnit", "rootMixed", "rootTuple", "rootGeneric", "rootFault"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 813)⟩]}
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("empty", .unit, []),
    ("rootUnit", .unit, [(.unit, some .unit)]),
    ("rootMixed", w 14, [(.word, some (w 7)), (.bool, some (.bool true)), (.word, some (w 7))]),
    ("rootTuple", w 3, [(.product .word .bool, some (.product (w 7) (.bool true)))]),
    ("rootGeneric", w 9, [(.word, some (w 9)), (.bool, some (.bool false))])]
  let baselines ← successes.mapM (fun row => finish compiled row.1 300000 initial)
  let faultBaseline ← finish compiled "rootFault" 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip baselines do
      let (name, expected, expectedCells) := test
      let observed ← finish compiled name fuel initial
      require (reprStr observed == reprStr baseline) s!"prepared parameter resume changed {name}"
      match observed with
      | .done value final =>
        require (reprStr value == reprStr expected) s!"prepared parameter result changed {name}"
        cells initial final expectedCells
      | _ => throw (IO.userError s!"prepared parameter expected completion {name}")
    let observed ← finish compiled "rootFault" fuel initial
    require (reprStr observed == reprStr faultBaseline) "prepared parameter fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final => cells initial final [(.word, some (w 5)), (.word, some (w 5)), (.word, none)]
    | _ => throw (IO.userError "prepared parameter fault prefix changed")
  IO.println "recursive named prepared parameters: actual ordered full-prefix preparation/raw projections, Unit/product arities, duplicate types, whole cells and resume GREEN"

end Tests.SourceCoreRecursiveNamedPreparedParameterProjections
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPreparedSourceFrames
/-! The source invocation frame is constructed from actual pass receipts,
independent validity and the ordinary declaration dictionary condition. The
audit replays the actual closure compiler and inspects each full source view. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedSourceFrames
open Solcore Frontend SourceInference TypeSystem SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedSpecializationBodyFacts RecursiveNamedPreparedSourceFrames

section Formal
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Core.Expr} {program : CheckedProgram}
  {representation : SourceCoreGeneralFunctions.Representation}
  {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
  {specialized : SourceSpecialization.SpecializedFunction}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)

include compiled

theorem compiled_source_roots :
    Dynamic.StatementRoots named.specialized.function.typedBody.roots compiled.statements := compiled_roots compiled

theorem prepared_source_agreement
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named) :
    CompatibleNamedBody.NamedAgreement named (view program named compiled.statements) := agreement inputs compiled

theorem actual_canonical_frame
    (signatureMember : signature ∈ program.signatures.functions) (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized)) (closed : named.specialized.assumptions = []) :
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) :=
  canonical_frame signatureMember genericMember accepted valid closed compiled

theorem actual_retained_frame
    (signatureMember : signature ∈ program.signatures.functions) (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized)) (closed : named.specialized.assumptions = []) :
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) :=
  retained_frame signatureMember genericMember accepted valid closed compiled

theorem actual_retained_bundle
    (signatureMember : signature ∈ program.signatures.functions) (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized)) (closed : named.specialized.assumptions = [])
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named) :
    CompatibleNamedBody.NamedAgreement named (view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) :=
  retained_of_compilation signatureMember genericMember accepted valid closed inputs compiled

/-- A source body invocation is recovered from its independent trace using the
constructed frame; a prior SourceFrame is not an input. -/
theorem independent_body_trace
    (signatureMember : signature ∈ program.signatures.functions) (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized)) (closed : named.specialized.assumptions = [])
    {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    {before bound after : Dynamic.Heap} {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    {outcome : Dynamic.ExpressionOutcome}
    (extended : MonoBindersExtend named.specialized.function.typedBody.owner
      (bodyInstance program named.specialized).context named.specialized.function.typedBody.inputs types context)
    (allocated : Dynamic.BindersAllocate [] before named.specialized.function.typedBody.inputs arguments environment bound)
    (trace : FunctionCallBody.Trace (Program.ofChecked program) (view program named compiled.statements)
      context environment bound outcome after) :
    NamedCalls.BodyOutcome (Program.ofChecked program) (bodyInstance program named.specialized) []
      before arguments outcome after :=
  (retained_frame signatureMember genericMember accepted valid closed compiled).body_of_trace extended allocated trace
end Formal

theorem ordinary_empty_dictionary {program : CheckedProgram} {named : SourceCoreGeneralFunctions.Function}
    (closed : named.specialized.assumptions = []) :
    Dynamic.EvidenceEnvironment.Covers (bodyInstance program named.specialized).context [] := empty_covers closed

theorem expression_root_rejected (id : ExpressionId) (rest : List NodeId) (statements : List StatementId) :
    (NodeId.expression id :: rest).mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
      | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)) ≠ .ok statements := by
  simp [List.mapM_cons, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem view_entry_fields (program : CheckedProgram) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) :
    (view program named statements).captured = [] ∧ (view program named statements).evidence = [] ∧
      (view program named statements).context.residualTypeVariables = true := ⟨rfl, rfl, rfl⟩

private def content : String := String.intercalate "\n" [
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function local<T>(value: T) returns (T) { let copied = value; return copied; }",
  "function empty() {}",
  "function terminal(flag: Bool) returns (Word) { if (flag) { return 3; } else { return 4; } return 5; }",
  "function wordRoot() returns (Word) { return choose(7, true); }",
  "function boolRoot() returns (Bool) { return choose(false, 9); }",
  "function localRoot() returns (Word) { return local(11); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "named prepared source frames" content
    ["wordRoot", "boolRoot", "localRoot", "empty", "terminal"]
  let representation := SourceCoreCompatibleFunctions.representation
    (.initial compiled.compatible.checked) compiled.compilationFuel
  let rawDiagnostics ← match compiled.indexed.base.diagnostics with
    | some value => pure value.program
    | none => throw (IO.userError "prepared source frames diagnostics missing")
  let diagnostics := match compiled.indexed.base.callableContext with
    | none => rawDiagnostics
    | some native => {rawDiagnostics with rootTable := native.diagnostics.rootTable}
  let mut rows := 0
  let mut emptyRows := 0
  let mut genericRows := 0
  for (named, slot) in compiled.indexed.base.functions.zipIdx do
    let actual ← get "source frames actual input preparation"
      (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation compiled.sourceProgram representation named.specialized)
    require (reprStr actual == reprStr named) "source frames actual full prepared row changed"
    let code ← get "source frames actual closure compilation"
      (SourceCoreGeneralFunctions.compileClosureWithRepresentation compiled.indexed.base.sourceProgram
        (CallableIndexedNamedGeneration.representation compiled.indexed) compiled.indexed.base.sourceProgram.signatures
        compiled.indexed.base.plan compiled.indexed.base.globals diagnostics compiled.indexed.base.locals
        compiled.indexed.base.callableContext compiled.indexed.fuel named)
    require (compiled.indexed.secondPass.closures[slot]? == some code)
      "source frames real second pass/slot changed"
    let statements ← get "source frames actual root traversal"
      (named.specialized.function.typedBody.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let closure := view compiled.sourceProgram named statements
    require (reprStr closure.source == reprStr named.specialized.function.typedBody &&
      closure.source.roots == statements.map NodeId.statement)
      "source frames full source/root row changed"
    require (reprStr closure.parameters == reprStr (named.inputs.map Prod.fst) &&
      closure.resultType == named.specialized.function.inferredBodyType)
      "source frames raw ordered parameters/result changed"
    require (closure.captured.isEmpty && closure.evidence.isEmpty && named.specialized.assumptions.isEmpty)
      "source frames ordinary source entry dictionary/capture changed"
    require (reprStr closure.context == reprStr (bodyInstance compiled.sourceProgram named.specialized).context &&
      closure.context.residualTypeVariables && closure.context.typeParameters.isEmpty)
      "source frames full original context/ledger flags changed"
    let retained := CallableNamedCanonicalOrder.retainedInstantiation named.specialized
    require (retained.parameterSubstitution == named.specialized.parameterSubstitution.reverse &&
      retained.type == named.specialized.function.type && retained.parameterComptime == closure.parameters.map (·.comptime))
      "source frames full retained substitution/flags changed"
    if statements.isEmpty then emptyRows := emptyRows + 1
    if !named.specialized.parameterSubstitution.isEmpty then genericRows := genericRows + 1
    rows := rows + 1
  require (rows == 8 && emptyRows == 1 && genericRows == 3)
    s!"source frames actual fixture coverage changed {rows}/{emptyRows}/{genericRows}"
  IO.println "named prepared source frames: actual roots/input preparation/closure compilation, complete ordinary canonical and retained views GREEN"

end Tests.SourceCoreRecursiveNamedPreparedSourceFrames
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPreparedStageContracts
/-! Public factory consumers use the same cached artifact and codebook.
Guard rejection keeps the original callee store and never requires argument
or callable-body execution. Source callable provenance remains explicit. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedStageContracts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedPreparedStageContracts

abbrev actual_public_pipeline := @public_compilation
abbrev actual_public_stage_table := @of_public_compile
abbrev actual_indirect_emission := @indirect_call_eq
abbrev actual_ordered_rows := @Prepared.rows
abbrev actual_dispatch_coverage := @Prepared.covers

/-- Actual rows construct the dispatch from source provenance. The only native
child premise is the original callee evaluation; arguments are never replayed. -/
theorem original_callee_stage_failure
    {compiled : SourceCoreUnifiedCompilation.Compiled} {native : SourceCoreGeneralFunctions.CallableContext}
    (prepared : Prepared compiled native) {context : SourceCoreFunctions.Context}
    {site : SourceCoreCallableContracts.Callsite} {sidecar : SourceCoreStageContracts.Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution}
    (issued : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    {sourceValue : Dynamic.Value} {carrier : Core.Value} {contract : Staging.CallGuard.Contract}
    (origin : CallableLedger.OriginRep sidecar.plan site.table sourceValue carrier)
    (bound : (CallableLedger.frame sidecar).Binds sourceValue contract)
    {reason : Staging.CallGuard.Fault}
    (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) node.id arguments sourceValue reason)
    {environment : Environment} {before after : Store} {calleeCode : Expr}
    (evaluated : Evaluates environment before calleeCode (.inRight .word carrier) after)
    (result : Core.Ty) (argumentsCode : Expr) :
    ∃ token,
      Evaluates environment before (site.lower native.diagnostics.unknown result calleeCode argumentsCode)
        (.inLeft result (.word token)) after ∧ CallStageBoundary.ReasonRepresents site reason token := by
  obtain ⟨dispatch⟩ := CallableLedger.dispatch (prepared.rows issued caller contains form) origin bound
  have actual := evaluated
  rw [dispatch.shape] at actual
  exact ⟨dispatch.reason reason,
    site.lower_stage_failure native.diagnostics.unknown dispatch.row _ dispatch.found (dispatch.rejected rejected) actual,
    dispatch.reason_represents reason⟩

/-- Verdict reflection uses the independent guard judgment and needs neither
source execution nor a preservation result. -/
theorem guard_acceptance (guard : SourceCoreStageContracts.Guard) :
    guard.decision = .ok () ↔
      Staging.CallGuard.Accepts (CallStageGuard.frame guard.sidecar.caller)
        ⟨guard.contract.parameters, guard.contract.stagedResult⟩ guard.node.id guard.arguments :=
  CallStageGuard.guard_accepts_iff guard

theorem absent_context {compiled : SourceCoreUnifiedCompilation.Compiled}
    (absent : compiled.indexed.base.callableContext = none)
    (native : SourceCoreGeneralFunctions.CallableContext) : ¬ Prepared compiled native := by
  intro prepared
  have present := prepared.present
  rw [absent] at present
  cases present

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def w := Word.ofNatModulo
private def content : String := String.intercalate "\n" [
  "function marked(comptime item: Word) returns (Word) { return item; }",
  "function identity(item: Word) returns (Word) { return item; }",
  "function namedFault(value: Word) returns (Word) { let f = marked; return f(value); }",
  "function lambdaFault(value: Word) returns (Word) { let f = lam(comptime item: Word) -> Word { return item; }; return f(value); }",
  "function ordinary(value: Word) returns (Word) { let f = identity; return f(value); }",
  "function tupleParameter() returns (Word) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }",
  "function effectfulTuple() returns (comptime<Word>) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }",
  "function builtin(value: Word) returns (integer) { let op = wordToInteger; return op(value); }"
]

private def contractFields (contract : SourceCoreStageContracts.Contract) :=
  (contract.plan, contract.parameters, contract.stagedResult, contract.owner)

private def rowFields (row : SourceCoreStageCodebook.Decision) :=
  (row.caller, row.call, row.entry.id, row.entry.origin, row.entry.parameterCount,
    row.entry.contract.map contractFields, row.argumentCount,
    row.guard.map fun guard => (guard.sidecar.plan, guard.sidecar.caller, guard.node,
      guard.arguments, contractFields guard.contract, guard.decision))

/-- Every guard row belongs to the artifact compiled through the public path.
The low-level rejection probe uses its real descriptor ID; no source origin is
inferred for the explicit probe carrier. -/
private def audit (cached : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let native ← match cached.indexed.base.callableContext with
    | some native => pure native | none => throw (IO.userError "actual stage context missing")
  let table := native.table
  require (!table.entries.isEmpty && !table.decisions.isEmpty) "actual codebook inventory empty"
  let mut rejected := 0
  let mut accepted := 0
  let mut effectful := 0
  for row in table.decisions do
    let site ← get "actual prepared callsite"
      (SourceCoreCallableContracts.prepareCallsite table row.caller row.call native.diagnostics.reasonAt)
    let selected ← match site.rowAt? row.entry.id with
      | some selected => pure selected | none => throw (IO.userError "actual ordered row lookup missing")
    require (reprStr (rowFields selected) == reprStr (rowFields row)) "actual callsite changed its complete row"
    match row.guard with
    | none =>
      require row.entry.contract.isNone "user callable lost its guard"
      require row.beforeArguments.toOption.isSome "builtin acquired a before-arguments guard"
    | some guard =>
      require (guard.node.id == row.call && guard.sidecar.caller.key == row.caller &&
        guard.arguments.length == row.argumentCount) "actual source caller/argument identity changed"
      require (reprStr guard.decision == reprStr
        (SourceCompilationPlan.validateStagedCallableContract guard.sidecar.caller guard.node guard.arguments
          guard.contract.parameters guard.contract.stagedResult guard.contract.owner))
        "actual guard validator equation changed"
      if guard.sidecar.caller.function.returnComptime then
        effectful := effectful + 1
        require row.beforeArguments.toOption.isSome "effectful caller acquired an early stage guard"
      match row.beforeArguments with
      | .ok () => accepted := accepted + 1
      | .error error =>
        rejected := rejected + 1
        let token := site.reasonAt row.caller row.call row.entry.id .beforeArguments error
        let carrier : Core.Value := .pair (.closure .unit .unit .unit []) (.word row.entry.id)
        let initialStore : Store := [.closure .unit .unit .unit [], .word (w 0)]
        let environment : Environment := [.cellRef .word 1, carrier]
        let calleeCode : Expr := .letE (.storeCell (.var 0) (.word (w 11))) (LanguageResult.success (.var 2))
        let argumentsCode : Expr := .letE (.storeCell (.var 0) (.word (w 22))) (LanguageResult.success .unit)
        let code := site.lower native.diagnostics.unknown .unit calleeCode argumentsCode
        for fuel in [0, 1, 31, 30000] do
          let first := runStateful fuel (.initial code environment initialStore)
          let final := match first with
            | .outOfFuel state => runStateful 30000 state
            | other => other
          require (final == .done (.inLeft .unit (.word token))
            [.closure .unit .unit .unit [], .word (w 11)])
            "stage rejection ran arguments, changed the original prefix or lost the callee store"
  require (rejected > 0 && accepted > 0 && effectful > 0) "actual guard branch coverage incomplete"
  for function in BuiltinFunctionId.all do
    let id ← match table.idAt? (.builtin function) with
      | some id => pure id | none => throw (IO.userError "actual builtin descriptor missing")
    let entry ← match table.entryAt? id with
      | some entry => pure entry | none => throw (IO.userError "actual builtin row missing")
    require (entry.parameterCount == function.parameterTypes.length && entry.contract.isNone)
      "actual builtin contract or ordered arity changed"

def run : IO Unit := do
  let program ← get "stage actual checked program" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] })
  let names := ["namedFault", "lambdaFault", "ordinary", "tupleParameter", "effectfulTuple", "builtin"]
  let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
  let seeds := roots.map fun key => SourceCoreCompiler.Seed.declaration key.declaration
  let options : SourceCompiler.Options := {specializationBudget := 512, compilationFuel := 1000}
  let facade ← get "actual public stage compilation" (SourceCompiler.compileChecked program seeds options)
  let source ← get "actual same Core compiler" (SourceCoreCompiler.compileChecked program seeds options)
  let cached ← match source.artifact? with
    | some cached => pure cached | none => throw (IO.userError "nonempty stage roots lost the cache")
  require (facade.keys == source.keys && cached.keys == roots) "public stage root order changed"
  let recipe ← get "actual stage recipe" (SourceCoreIndexedSession.Recipe.prepare cached)
  audit recipe.compiled
  let empty ← get "actual public empty roots" (SourceCoreCompiler.compileChecked program [] options)
  require empty.artifact?.isNone "empty root path invented a codebook"
  let artifact ← recipe.open
  let boot ← artifact.bootstrapFresh
  let initial ← match boot.resume 300000 with
    | .ready session => pure session
    | _ => throw (IO.userError "actual stage bootstrap did not finish")
  for fuel in [0, 1, 31, 300000] do
    let checkpoint ← get "actual ordinary guarded startup"
      (initial.start (← SourceCoreUnifiedCorpusSupport.key program "ordinary") [.word (w 17)])
    let first ← checkpoint.resume fuel
    let final ← match first with
      | .outOfFuel checkpoint => checkpoint.resume 300000
      | other => pure other
    match final with
    | .succeeded completion =>
      require (completion.value == .word (w 17) && completion.session.installedGlobalsPresent)
        "actual ordinary guarded result/global prefix changed"
    | _ => throw (IO.userError "actual ordinary guarded call did not succeed")
  IO.println "actual public compiled stage table / original ordered guards / builtin and effectful bypass / callee-only fault store / full prefix and resume GREEN"

end Tests.SourceCoreRecursiveNamedPreparedStageContracts
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPreparedStageScopes
/-! Static consumers use the actual prepared table, complete plan row and
source view. The metadata receipt does not assert a global staged body run,
native capture correctness, source typing or an arbitrary table's authority. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Tests.SourceCoreRecursiveNamedPreparedStageScopes
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreStageContracts RecursiveNamedPreparedStageScopes

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {native : SourceCoreGeneralFunctions.CallableContext}
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan row.key = .ok row)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named row.key))

include actual prepared record descriptor in
theorem actual_named_scope :
    ∃ sidecar : Sidecar,
      prepareSidecar compiled.indexed.base.plan row.key = .ok sidecar ∧ sidecar.caller = row ∧
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) :=
  selected_of_descriptor actual prepared record descriptor

include actual prepared record descriptor in
theorem full_original_metadata :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      sidecar.caller.function.typedBody = row.function.typedBody ∧
      sidecar.caller.function.solvedRequirements = row.function.solvedRequirements ∧
      sidecar.caller.assumptions = row.assumptions ∧ sidecar.caller.stageAnalysis = row.stageAnalysis ∧
      sidecar.caller.function.returnComptime = row.function.returnComptime := by
  obtain ⟨sidecar, _, same, selected⟩ := selected_of_descriptor actual prepared record descriptor
  exact ⟨sidecar, selected, by rw [same], by rw [same], by rw [same], by rw [same], by rw [same]⟩

include actual prepared record descriptor in
theorem named_substitutions_and_marker :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).origin.declarationSubstitution = row.parameterSubstitution ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).origin.localSubstitution = [] ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).guards.stages.callerReturnComptime = row.function.returnComptime ∧
      SourceStageAnalysis.analyzeFunction row.function = .ok row.stageAnalysis :=
  original_stages actual prepared record descriptor

include actual prepared record descriptor in
theorem independent_source_admission
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).source = row.function.typedBody ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).context =
        (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row).context ∧
      prepared.view.evidence.Covers (RecursiveStageRegistry.scope sidecar [] prepared.view).context ∧
      Staging.FunctionHasStages row.function :=
  source_frame_preserved actual prepared record descriptor wellFormed range

include actual prepared record descriptor in
theorem resolved_dictionary :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).evidence =
        CallableNamedMetadata.environment prepared.available :=
  evidence_preserved actual prepared record descriptor

include actual prepared descriptor in
theorem actual_named_origin
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key) (raw : Core.Value) :
    CallableLedger.OriginRep compiled.indexed.base.plan native.table
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩)
      (.pair raw (.word descriptor.id)) :=
  global_origin actual prepared descriptor target raw
end Actual

theorem anonymous_scope_kept {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    {function : Dynamic.Closure} {scope : Staging.Recursive.Scope}
    (selected : RecursiveStageRegistry.Selected compiled.sourceProgram compiled.indexed.base.plan native.table function scope) :
    (registry actual).Closure function scope := anonymous_preserved actual selected

/-- The actual sidecar cannot be replaced by a different full record while
keeping the same successful plan selection. -/
theorem selected_full_record_unique {plan : Plan} {key : Key} {sidecar : Sidecar}
    {first second : SourceSpecialization.SpecializedFunction}
    (issued : prepareSidecar plan key = .ok sidecar)
    (one : SourceCompilationPlan.exactSpecialization plan key = .ok first)
    (two : SourceCompilationPlan.exactSpecialization plan key = .ok second) : first = second :=
  (sidecar_caller issued one).symm.trans (sidecar_caller issued two)

end Tests.SourceCoreRecursiveNamedPreparedStageScopes
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedTraceBounds
/-! These consumers use finite independent source derivations. A size is
obtained from every original rule, and actual call/loop children lie below
their containing derivation. Fault sizes also include completed successful
prefixes. Cached Core regressions retain self/mutual calls, writes and resume;
this unit does not yet prove recursive source/native correspondence. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedTraceBounds
open Solcore Frontend SourceInference SourceSemantics
open SourceSemantics.CoreLowering

#check_failure SourceTypedRuntime.run

section Leaves
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {heap : Dynamic.Heap} {id : ExpressionId}

example : SourceExecutionSize.ExpressionsEvaluate program 1 context evidence source
    environment heap [] [] heap := .nil

example (absent : Dynamic.ExpressionMissing source id) :
    SourceExecutionSize.ExpressionFaults program 1 context evidence source environment
      heap id (.missingExpression id) heap := .missing absent
end Leaves

section Calls
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
  {function : Dynamic.GlobalFunction} {arguments : List Dynamic.Value}
  {result : Dynamic.Value} {size : Nat}

/-- Actual named dispatch exposes its retained source body strictly below the
whole call. The instantiation fact is recovered from that dispatch. -/
theorem callee_below
    (trace : SourceExecutionSize.CallableApplies program size context caller invocation before
      (.global function) arguments result after) :
    ∃ body child,
      Dynamic.FunctionInstantiates program function.instantiation body ∧
      SourceExecutionSize.BodyInvokes program child body invocation before arguments result after ∧ child < size := by
  cases trace with
  | global instantiated _ _ invoked =>
    exact ⟨_, _, instantiated, invoked, SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- Existence is proved from the original independent dispatch, including
self or mutual calls represented by its finite body derivation. -/
theorem original_callee_below
    (trace : Dynamic.CallableApplies program context caller invocation before
      (.global function) arguments result after) :
    ∃ total body child,
      SourceExecutionSize.CallableApplies program total context caller invocation before
        (.global function) arguments result after ∧
      Dynamic.FunctionInstantiates program function.instantiation body ∧
      SourceExecutionSize.BodyInvokes program child body invocation before arguments result after ∧ child < total := by
  obtain ⟨total, sized⟩ := SourceExecutionSize.CallableApplies.has_size trace
  obtain ⟨body, child, instantiated, invoked, smaller⟩ := callee_below sized
  exact ⟨total, body, child, sized, instantiated, invoked, smaller⟩

/-- A body fault after parameter allocation remains a smaller actual child
of the source named-call fault rule. -/
theorem fault_callee_below {body : Dynamic.BodyInstance} {reason : Dynamic.SemanticFault}
    (instantiated : Dynamic.FunctionInstantiates program function.instantiation body)
    (same : invocation = function.evidence)
    (trace : SourceExecutionSize.BodyFaults program size body invocation before arguments reason after) :
    ∃ total,
      SourceExecutionSize.CallableFaults program total context caller invocation before
        (.global function) arguments reason after ∧ size < total :=
  ⟨_, .globalBody instantiated same trace, SourceExecutionSize.child_lt_stepSize (by simp)⟩
end Calls

section Prefixes
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before middle after : Dynamic.Heap} {id : ExpressionId} {ids : List ExpressionId}
  {value : Dynamic.Value} {reason : Dynamic.SemanticFault}

/-- The preceding successful expression is counted even when the rest of
the ordered argument vector faults. Both original children erase unchanged. -/
theorem successful_prefix_in_fault
    (head : Dynamic.ExpressionEvaluates program context evidence source environment before id value middle)
    (tail : Dynamic.ExpressionsFault program context evidence source environment middle ids reason after) :
    ∃ total first second,
      SourceExecutionSize.ExpressionsFault program total context evidence source environment before (id :: ids) reason after ∧
      SourceExecutionSize.ExpressionEvaluates program first context evidence source environment before id value middle ∧
      SourceExecutionSize.ExpressionsFault program second context evidence source environment middle ids reason after ∧
      first < total ∧ second < total := by
  obtain ⟨first, head⟩ := SourceExecutionSize.ExpressionEvaluates.has_size head
  obtain ⟨second, tail⟩ := SourceExecutionSize.ExpressionsFault.has_size tail
  exact ⟨_, first, second, .tail head tail, head, tail,
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- Escaped control is a fault rule containing a successful body derivation.
That successful premise is retained rather than treated as a leaf. -/
theorem escaped_success_is_counted
    {body : Dynamic.BodyInstance} {arguments : List Dynamic.Value} {roots : List StatementId}
    {inputTypes : List TypeSystem.Ty} {lexicalContext finalContext : SourceSemantics.Context}
    {bound : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (root : Dynamic.StatementRoots body.source.roots roots)
    (inputs : MonoBindersExtend body.source.owner body.context body.source.inputs inputTypes lexicalContext)
    (allocate : Dynamic.BindersAllocate [] before body.source.inputs arguments environment bound)
    (execute : Dynamic.FunctionStatementsExecute program lexicalContext evidence body.source
      environment bound roots finalContext outcome after)
    (escaped : (∃ env, outcome = .breaking env) ∨ (∃ env, outcome = .continuing env)) :
    ∃ total child,
      SourceExecutionSize.BodyFaults program total body evidence before arguments .controlEscapedFunction after ∧
      SourceExecutionSize.FunctionStatementsExecute program child lexicalContext evidence body.source
        environment bound roots finalContext outcome after ∧ child < total := by
  obtain ⟨child, execute⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size execute
  exact ⟨_, child, .controlEscape root inputs allocate execute escaped, execute,
    SourceExecutionSize.child_lt_stepSize (by simp)⟩
end Prefixes

section Loops
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before conditionHeap bodyHeap postHeap after : Dynamic.Heap} {condition : ExpressionId}
  {body : List StatementId} {post : List ForItemForm}
  {bodyContext postContext : SourceSemantics.Context} {bodyEnvironment postEnvironment : Dynamic.Environment}
  {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

/-- A continuing source for loop counts condition, body, post and the next
iteration as separate actual children, in execution order. -/
theorem for_continue_children
    (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before condition (.bool true) conditionHeap)
    (bodyTrace : Dynamic.StatementsExecute program context evidence source environment
      conditionHeap body bodyContext (.continuing bodyEnvironment) bodyHeap)
    (postTrace : Dynamic.ForItemsExecute program context evidence source environment
      bodyHeap post postContext postEnvironment postHeap)
    (nextTrace : Dynamic.ForLoopExecutes program context evidence source environment
      postHeap condition post body context outcome after) :
    ∃ total c b p n,
      SourceExecutionSize.ForLoopExecutes program total context evidence source environment before
        condition post body context outcome after ∧
      SourceExecutionSize.ExpressionEvaluates program c context evidence source environment before
        condition (.bool true) conditionHeap ∧
      SourceExecutionSize.StatementsExecute program b context evidence source environment conditionHeap
        body bodyContext (.continuing bodyEnvironment) bodyHeap ∧
      SourceExecutionSize.ForItemsExecute program p context evidence source environment bodyHeap
        post postContext postEnvironment postHeap ∧
      SourceExecutionSize.ForLoopExecutes program n context evidence source environment postHeap
        condition post body context outcome after ∧ c < total ∧ b < total ∧ p < total ∧ n < total := by
  obtain ⟨c, conditionTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size conditionTrace
  obtain ⟨b, bodyTrace⟩ := SourceExecutionSize.StatementsExecute.has_size bodyTrace
  obtain ⟨p, postTrace⟩ := SourceExecutionSize.ForItemsExecute.has_size postTrace
  obtain ⟨n, nextTrace⟩ := SourceExecutionSize.ForLoopExecutes.has_size nextTrace
  exact ⟨_, c, b, p, n, .nextContinue conditionTrace bodyTrace postTrace nextTrace,
    conditionTrace, bodyTrace, postTrace, nextTrace,
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp),
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- A later loop fault still counts all three successful prefixes. It is
strictly smaller than the parent without claiming equal source/Core cost. -/
theorem for_later_fault_children
    (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before condition (.bool true) conditionHeap)
    (bodyTrace : Dynamic.StatementsExecute program context evidence source environment
      conditionHeap body bodyContext (.fallthrough bodyEnvironment) bodyHeap)
    (postTrace : Dynamic.ForItemsExecute program context evidence source environment
      bodyHeap post postContext postEnvironment postHeap)
    (nextTrace : Dynamic.ForLoopFaults program context evidence source environment
      postHeap condition post body reason after) :
    ∃ total c b p n,
      SourceExecutionSize.ForLoopFaults program total context evidence source environment before condition post body reason after ∧
      c < total ∧ b < total ∧ p < total ∧ n < total ∧
      SourceExecutionSize.ExpressionEvaluates program c context evidence source environment before condition (.bool true) conditionHeap ∧
      SourceExecutionSize.StatementsExecute program b context evidence source environment conditionHeap body bodyContext
        (.fallthrough bodyEnvironment) bodyHeap ∧
      SourceExecutionSize.ForItemsExecute program p context evidence source environment bodyHeap post postContext postEnvironment postHeap ∧
      SourceExecutionSize.ForLoopFaults program n context evidence source environment postHeap condition post body reason after := by
  obtain ⟨c, conditionTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size conditionTrace
  obtain ⟨b, bodyTrace⟩ := SourceExecutionSize.StatementsExecute.has_size bodyTrace
  obtain ⟨p, postTrace⟩ := SourceExecutionSize.ForItemsExecute.has_size postTrace
  obtain ⟨n, nextTrace⟩ := SourceExecutionSize.ForLoopFaults.has_size nextTrace
  exact ⟨_, c, b, p, n, .nextFallthrough conditionTrace bodyTrace postTrace nextTrace,
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp),
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp),
    conditionTrace, bodyTrace, postTrace, nextTrace⟩

/-- While body effects and its later fault also use the same measure. -/
theorem while_later_fault_children
    (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before condition (.bool true) conditionHeap)
    (bodyTrace : Dynamic.StatementsExecute program context evidence source environment
      conditionHeap body bodyContext (.fallthrough bodyEnvironment) bodyHeap)
    (nextTrace : Dynamic.WhileFaults program context evidence source environment
      bodyHeap condition body reason after) :
    ∃ total c b n,
      SourceExecutionSize.WhileFaults program total context evidence source environment before condition body reason after ∧
      SourceExecutionSize.ExpressionEvaluates program c context evidence source environment before condition (.bool true) conditionHeap ∧
      SourceExecutionSize.StatementsExecute program b context evidence source environment conditionHeap body bodyContext
        (.fallthrough bodyEnvironment) bodyHeap ∧
      SourceExecutionSize.WhileFaults program n context evidence source environment bodyHeap condition body reason after ∧
      c < total ∧ b < total ∧ n < total := by
  obtain ⟨c, conditionTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size conditionTrace
  obtain ⟨b, bodyTrace⟩ := SourceExecutionSize.StatementsExecute.has_size bodyTrace
  obtain ⟨n, nextTrace⟩ := SourceExecutionSize.WhileFaults.has_size nextTrace
  exact ⟨_, c, b, n, .nextFallthrough conditionTrace bodyTrace nextTrace,
    conditionTrace, bodyTrace, nextTrace, SourceExecutionSize.child_lt_stepSize (by simp),
    SourceExecutionSize.child_lt_stepSize (by simp), SourceExecutionSize.child_lt_stepSize (by simp)⟩
end Loops

end Tests.SourceCoreRecursiveNamedTraceBounds

namespace Tests.SourceCoreRecursiveNamedTraceBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof

section SourceBoundary
variable {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {size : Nat}
  {context callContext : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {caller : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
  {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}

/-- Both original source call and original function-statement sizes survive
dispatch and parameter allocation; no body execution is an extra premise. -/
theorem actual_source_function_below
    (unique : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types callContext)
    (arity : function.parameters.length = arguments.length)
    (called : RecursiveNamedCallBounds.CallOutcome program size context caller function.evidence before
      (.global ⟨instantiation, function.evidence⟩) arguments outcome after) :
    ∃ bodySize traceSize environment bound,
      RecursiveNamedCallBounds.BodyOutcome program bodySize body function.evidence before arguments outcome after ∧
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program traceSize function callContext environment bound outcome after ∧
      traceSize < bodySize ∧ bodySize < size := by
  obtain ⟨bodySize, invoked, bodyLess⟩ := RecursiveNamedCallBounds.source_call_body unique frame arity called
  obtain ⟨traceSize, environment, bound, allocated, traced, traceLess⟩ :=
    RecursiveNamedCallBounds.body_trace frame extended arity invoked
  exact ⟨bodySize, traceSize, environment, bound, invoked, allocated, traced, traceLess, bodyLess⟩
end SourceBoundary

private def traceBody (reason : Word) : Expr :=
  .letE (.storeCell (.var 1) (.word (Word.ofNatModulo 7))) (.inLeft .word (.word reason))
private def traceClosure (reason : Word) : Value :=
  .closure .unit (LanguageResult.resultType .word) (traceBody reason) [.cellRef .word 0]
private def traceBefore (reason : Word) : Store := [.word Word.zero, .inRight .unit (traceClosure reason)]
private def traceAfter (reason : Word) : Store := [.word (Word.ofNatModulo 7), .inRight .unit (traceClosure reason)]
private def traceCellType : Ty := OptionalCell.cellType (.function .unit (LanguageResult.resultType .word))

/-- An actual finite call writes through its saved capture and faults. The
smaller saved-body trace comes from that exact original completion. -/
theorem captured_fault_original_child (key : SourceSpecialization.SpecializationKey) (reason : Word) :
    ∃ total child,
      EvaluationSize total [.cellRef traceCellType 1] (traceBefore reason)
        (SourceCoreCalls.call ⟨key, .unit, .word⟩ 0 (LanguageResult.success .unit) Word.zero)
        (.inLeft .word (.word reason)) (traceAfter reason) ∧
      EvaluationSize child [.unit, .cellRef .word 0] (traceBefore reason)
        (traceBody reason) (.inLeft .word (.word reason)) (traceAfter reason) ∧ child < total := by
  have executed : Evaluates [.cellRef traceCellType 1] (traceBefore reason)
      (SourceCoreCalls.call ⟨key, .unit, .word⟩ 0 (LanguageResult.success .unit) Word.zero)
      (.inLeft .word (.word reason)) (traceAfter reason) := by
    exact .caseRight (.inRight .unit) (.caseRight
      (.caseRight (.loadCell (.var rfl) rfl) (.inRight (.var rfl)))
      (.apply (.var rfl) (.var rfl)
        (.letE (.storeCell (.var rfl) rfl .word (by simp [traceBefore, traceAfter, Store.write?])) (.inLeft .word))))
  obtain ⟨total, completed⟩ := evaluation_has_size executed
  obtain ⟨child, smaller, bodyTrace⟩ := RecursiveNamedCallBounds.call_body
    (show Evaluates _ _ (LanguageResult.success .unit) (.inRight .word .unit) _ from .inRight .unit)
    (show ([.cellRef traceCellType 1] : Environment)[0]? = some (.cellRef traceCellType 1) from rfl)
    (show (traceBefore reason).read? 1 = some (.inRight .unit (traceClosure reason)) from rfl) completed
  exact ⟨total, child, completed, bodyTrace, smaller⟩

/-- The actual frame wrapper restores its administrative cell after a body
fault, while retaining the separate captured write. Both real subtraces are
strict children of the original wrapper trace. -/
theorem frame_fault_restores_original_child (reason : Word) :
    ∃ total nextSize bodySize bodyStore,
      EvaluationSize total [.cellRef .integer 0, .cellRef .word 1]
        [.integer 12, .word Word.zero]
        (SourceCoreCallableContextFrames.withFrame (.var 0) (.integer 33) (traceBody reason))
        (.inLeft .word (.word reason)) [.integer 12, .word (Word.ofNatModulo 7)] ∧
      EvaluationSize nextSize (.integer 12 :: [.cellRef .integer 0, .cellRef .word 1])
        [.integer 12, .word Word.zero] ((Expr.integer 33).weakenAt 0) (.integer 33)
        [.integer 12, .word Word.zero] ∧
      EvaluationSize bodySize (.unit :: .integer 12 :: [.cellRef .integer 0, .cellRef .word 1])
        [.integer 33, .word Word.zero] (((traceBody reason).weakenAt 0).weakenAt 0)
        (.inLeft .word (.word reason)) bodyStore ∧
      nextSize < total ∧ bodySize < total ∧
      [.integer 12, .word (Word.ofNatModulo 7)] = bodyStore.set 0 (.integer 12) := by
  have bodyEval : Evaluates (.unit :: .integer 12 :: [.cellRef .integer 0, .cellRef .word 1])
      [.integer 33, .word Word.zero] (((traceBody reason).weakenAt 0).weakenAt 0)
      (.inLeft .word (.word reason)) [.integer 33, .word (Word.ofNatModulo 7)] := by
    simp [traceBody, Expr.weakenAt]
    exact .letE (bodyStore := [.integer 33, .word (Word.ofNatModulo 7)])
      (.storeCell (initialStore := [.integer 33, .word Word.zero])
        (referenceStore := [.integer 33, .word Word.zero]) (valueStore := [.integer 33, .word Word.zero])
        (location := 1) (oldValue := .word Word.zero) (.var rfl) rfl .word (by simp [Store.write?])) (.inLeft .word)
  have executed := CallableContextFrames.withFrame_evaluates
    (show DataEquality.Selects [.cellRef .integer 0, .cellRef .word 1] (.var 0) (.cellRef .integer 0) from .var rfl)
    (show Store.read? [.integer 12, .word Word.zero] 0 = some (.integer 12) from rfl)
    (show Evaluates (.integer 12 :: [.cellRef .integer 0, .cellRef .word 1])
      [.integer 12, .word Word.zero] ((Expr.integer 33).weakenAt 0) (.integer 33)
      [.integer 12, .word Word.zero] from by simpa only [Expr.weakenAt] using (Evaluates.integer (environment := .integer 12 :: [.cellRef .integer 0, .cellRef .word 1]) (store := [.integer 12, .word Word.zero]) (value := 33))) bodyEval
  obtain ⟨total, completed⟩ := evaluation_has_size executed
  obtain ⟨nextSize, bodySize, installed, nextStore, bodyStore, nextTrace, bodyTrace, nextLess, bodyLess, restored⟩ :=
    RecursiveNamedCallBounds.with_frame (.var rfl) rfl completed
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextTrace.sound
    (show Evaluates _ _ ((Expr.integer 33).weakenAt 0) (.integer 33) _ from by simpa only [Expr.weakenAt] using (Evaluates.integer (value := 33)))
  exact ⟨total, nextSize, bodySize, bodyStore, completed, nextTrace, bodyTrace, nextLess, bodyLess, restored⟩

/-- A callback limited to this original outer trace is consumed only for its
actual smaller child. No unrestricted body contract is reconstructed. -/
theorem actual_child_callback {contract : Nat → Prop}
    {signature : SourceCoreCalls.Signature} {index : Nat} {arguments : Expr} {reason : Word}
    {total : Nat} {environment : Environment} {store finalStore : Store} {value : Value}
    (callbacks : RecursiveNamedBoundedContracts.Below total contract)
    (completed : EvaluationSize total environment store (SourceCoreCalls.call signature index arguments reason) value finalStore) :
    ∃ child argumentValue argumentStore,
      contract child ∧ child < total ∧ EvaluationSize child environment store arguments argumentValue argumentStore := by
  obtain ⟨child, argumentValue, argumentStore, smaller, trace⟩ := RecursiveNamedCallBounds.call_arguments completed
  exact ⟨child, argumentValue, argumentStore, callbacks.child smaller, smaller, trace⟩

end Tests.SourceCoreRecursiveNamedTraceBounds

namespace Tests.SourceCoreRecursiveNamedTraceBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

/-- Actual accepted parameter compilation and its original completion supply
both the final environment typing and the smaller body derivation. The caller
supplies only typing of the initial actual environment. -/
theorem accepted_parameters_typed_child {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {output : Ty} {body code : Expr}
    {scope : Scope} {bindings : List Binding}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      source scope bindings output SourceCoreFunctions.argumentProjection body = .ok code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
    {canonical logical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {named : Bool} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (bundleSlot : logical[0]? = some (DataPatternValues.packValues values))
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (code.rename ξ) result afterStore) :
    ∃ finalActual finalStore finalWorld finalEmbedding child,
      RuntimeEnvironmentHasTypes finalWorld finalActual
        (CallableIndexedParameterTyped.prefixContext bindings actualContext) nativeDefinitions ∧
      EvaluationSize child finalActual finalStore (body.rename finalEmbedding) result afterStore ∧
      child ≤ size ∧ (bindings ≠ [] → child < size) := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, child, allocated, finalEnvironments, finalHeaps, maps, worlds,
    frame, finalLayout, finalAgrees, spine, finalTyped, childTrace, weak, strict⟩ :=
    RecursiveNamedCallBounds.parameter_prefix tree definitions registered represented environments heaps
      sourceLayout actualLayout actualTyped bundleSlot
      (allTypes := bindings.map Prod.snd) (by simp)
      (by simpa only [List.length_map] using represented.length.2)
      (fun found => by simpa using found) kinds reference read unmapped completed
  exact ⟨finalActual, finalStore, finalWorld, finalEmbedding, child, finalTyped, childTrace, weak, strict⟩

end Tests.SourceCoreRecursiveNamedTraceBounds


namespace Tests.SourceCoreRecursiveNamedTraceBounds
open Solcore Core Frontend

def runBounds : IO Unit := do
  let reason := Word.ofNatModulo 19
  let artifact ← SourceCoreUnifiedCorpusSupport.prepare "original native helper bounds"
    "function helper() returns (Word) { return 19; }" ["helper"]
  let key ← match artifact.indexed.base.functions with
    | function :: _ => pure function.signature.key
    | [] => throw (IO.userError "original native helper bounds missing checked key")
  let signature : SourceCoreCalls.Signature := ⟨key, .unit, .word⟩
  let cases := [
    (State.initial (SourceCoreCalls.call signature 0 (LanguageResult.success .unit) Word.zero)
      [.cellRef traceCellType 1] (traceBefore reason), traceAfter reason),
    (State.initial (SourceCoreCallableContextFrames.withFrame (.var 0) (.integer 33) (traceBody reason))
      [.cellRef .integer 0, .cellRef .word 1] [.integer 12, .word Word.zero],
      [.integer 12, .word (Word.ofNatModulo 7)])]
  for (initial, expected) in cases do
    for fuel in [0, 1, 7, 31] do
      let completed := match runStateful fuel initial with
        | .outOfFuel checkpoint => runStateful 1000 checkpoint
        | result => result
      SourceCoreUnifiedCorpusSupport.assertTrue
        (LanguageResult.observeResult completed == .failed reason expected)
        "original call/frame trace lost a captured fault write or frame restoration on resume"
  IO.println "recursive named trace bounds: all 40 source judgment bridges; actual source call/body children, original Core call/frame/parameter/finish sizes, typed parameter continuation, guarded pointwise budgets, captured faults and resume GREEN"

def run : IO Unit := do
  Tests.SourceCoreRecursiveNamedCatalog.run
  runBounds

end Tests.SourceCoreRecursiveNamedTraceBounds
end
