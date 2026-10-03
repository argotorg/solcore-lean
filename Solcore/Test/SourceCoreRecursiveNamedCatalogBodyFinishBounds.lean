import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogBodyFinishBounds
import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeFor
import Solcore.Test.SourceCoreUnifiedCorpusSupport

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
