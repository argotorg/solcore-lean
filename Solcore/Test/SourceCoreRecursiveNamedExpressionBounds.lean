import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionHeadBounds
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Original ordered argument and call derivations retain their strict child
costs. Concrete builtin lexical bodies discharge the pointwise body interface
at actual catalog entries. Cached executions check order, fault writes, raw
mapping metadata, capture aliases and resume. The whole recursive expression
and called-body correspondence remains a separate proof boundary. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedExpressionBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds

#check_failure SourceTypedRuntime.run
#check_failure RecursiveNamedCatalog.Header.certificate
#check_failure RecursiveNamedCatalogInvocationBounds.BodyState.mk

section ConcreteBodies
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (body : BuiltinNamedCalls.Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include extension uninitialized missing faithful functionLeaves functionTypes in
/-- Concrete body meaning supplies every source budget, with the real frame
reference recovered from the all-target catalog entry. -/
theorem builtin_body_preserves_at (size : Nat) :
    BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      functions registry (Header.of_body body) faults size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry outcome after trace
  have reference : entry.canonical[(body.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + body.globals]? =
      some (.cellRef prepared.layout.frame.type frameLocation) := by
    simpa only [Header.of_body, List.length_map, List.length_reverse] using entry.reference
  have unmapped := entry.catalog.authority.unmapped
  rw [entry.catalog_frame] at unmapped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _⟩ :=
    body.certificate.preserves functions extension body.definitions_eq body.registered program body.valid body.unique
      uninitialized missing faithful functionLeaves functionTypes entry.environments entry.heaps entry.locals
      entry.lookups entry.actualTyped reference entry.state.read unmapped trace.sound
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata⟩

include extension uninitialized missing faithful functionLeaves functionTypes in
/-- Reflection consumes the original native body completion. The concrete
source derivation receives its own size after it has been reconstructed. -/
theorem builtin_body_reflects_at (size : Nat) :
    BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      functions registry (Header.of_body body) faults size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry value finalStore completed
  have reference : entry.canonical[(body.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + body.globals]? =
      some (.cellRef prepared.layout.frame.type frameLocation) := by
    simpa only [Header.of_body, List.length_map, List.length_reverse] using entry.reference
  have unmapped := entry.catalog.authority.unmapped
  rw [entry.catalog_frame] at unmapped
  obtain ⟨outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _⟩ :=
    body.certificate.reflects functions extension body.definitions_eq body.registered program body.valid body.unique
      uninitialized missing faithful functionLeaves functionTypes entry.environments entry.heaps entry.locals
      entry.lookups entry.actualTyped reference entry.state.read unmapped completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.BodyTrace.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, result, heaps, maps, worlds, frame, metadata⟩

variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {readFuel : Nat}
  {compilation : SourceCoreFunctions.Context}
  (callerValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
/-- One concrete installed body and concrete recursive builtin arguments close
the bounded head, without an external child or body execution premise. -/
theorem builtin_named_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context
        (CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt)) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionHeadBounds.preserves_at functions budget size within unique owners
  · exact RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed _
        (CompatibleExpressionBuiltins.preserves functions extension faithful functionLeaves functionTypes
          program evidence callerValid unique callerUninitialized callerMissing)) budget
  · intro header member child _
    have same : header = Header.of_body body := by simpa only [List.mem_singleton] using member
    subst header
    intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after trace
    exact builtin_body_preserves_at (headers := [Header.of_body body]) (locations := locations) (capturePrefix := capturePrefix) functions extension body uninitialized missing faithful functionLeaves functionTypes child entry trace

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
/-- Original native completion reflects through the concrete argument and body
proofs; the reconstructed source expression has a separate finite cost. -/
theorem builtin_named_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context
        (CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt)) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionHeadBounds.reflects_at functions budget size within
  · exact RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed _
        (CompatibleExpressionBuiltins.reflects functions extension faithful functionLeaves functionTypes
          program evidence callerValid callerUninitialized callerMissing)) budget
  · intro header member child _
    have same : header = Header.of_body body := by simpa only [List.mem_singleton] using member
    subst header
    intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore completed
    exact builtin_body_reflects_at (headers := [Header.of_body body]) (locations := locations) (capturePrefix := capturePrefix) functions extension body uninitialized missing faithful functionLeaves functionTypes child entry completed
end ConcreteBodies

section OriginalSource
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {caller invocation : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
  {instantiation : DeclarationInstantiation} {id : ExpressionId} {ids : List ExpressionId}
  {value : Dynamic.Value} {reason : Dynamic.SemanticFault} {first second whole : Nat}

/-- A later argument fault keeps the successful first argument and both
original costs strictly below the containing named expression. -/
theorem later_argument_fault_children
    (head : SourceExecutionSize.ExpressionEvaluates program first context caller source environment before id value middle)
    (tail : SourceExecutionSize.ExpressionsFault program second context caller source environment middle ids reason after)
    (within : SourceExecutionSize.stepSize [first, second] < whole) :
    RecursiveNamedArgumentTraceBounds.TraceAt program context caller invocation source environment before
      (id :: ids) instantiation whole (.fault reason) after ∧ first < whole ∧ second < whole :=
  ⟨.argumentFault (.tail head tail) within,
    Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) within,
    Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) within⟩

/-- Success and body fault share the same ordered argument prefix, while the
retained call outcome supplies a different strictly smaller child. -/
theorem call_children
    {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate program first context caller source environment before ids arguments middle)
    (callTrace : RecursiveNamedCallBounds.CallOutcome program second context caller invocation middle
      (.global ⟨instantiation, invocation⟩) arguments outcome after)
    (firstBelow : first < whole) (secondBelow : second < whole) :
    RecursiveNamedArgumentTraceBounds.TraceAt program context caller invocation source environment before
      ids instantiation whole outcome after :=
  .apply argumentsTrace callTrace firstBelow secondBelow
end OriginalSource

private def content : String := String.intercalate "\n" [
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function take(a: Word, b: Word) returns (Word) { return a - b; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function failAfter(a: Word) returns (Word) { let written = a + 10; let gap: Word; return gap; }",
  "function ordered() returns (Word) { return take(side(7), side(3)); }",
  "function firstFault() returns (Word) { return take(fail(), side(7)); }",
  "function laterFault() returns (Word) { return take(side(7), fail()); }",
  "function bodyFault() returns (Word) { return failAfter(side(7)); }",
  "function mapLeaf(raw: mapping((Bool, Bool) => Word)) returns (mapping((Bool, Bool) => Word)) { return raw; }",
  "function rawEcho(raw: mapping((Bool, Bool) => Word)) returns (mapping((Bool, Bool) => Word)) { return mapLeaf(raw); }",
  "function defaulted() returns (Word) { let raw: mapping((Bool, Bool) => Word); return raw[(true, false)]; }",
  "function alias(n: Word) returns (function(Word) returns (Word)) { let shared = n; return lam(x: Word) -> Word { shared += x; return shared; }; }",
  "function aliases(n: Word) returns (Word) { let first = alias(n); let second = first; let a = first(2); return a + second(3); }",
  "function self(n: Word) returns (Word) { return n == 0 ? 2 : self(n - 1) + 1; }",
  "function left(n: Word) returns (Word) { return n == 0 ? 7 : right(n - 1); }",
  "function right(n: Word) returns (Word) { return n == 0 ? 11 : left(n - 1); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"named bound resume {name}" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"named bound prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"named bound ordered cells changed {label}: {reprStr final.heap}"

private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "named bound fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "named bound exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named expression bounds" content
    ["ordered", "firstFault", "laterFault", "bodyFault", "rawEcho", "defaulted", "aliases", "self", "left", "right"]
  let keyType : TypeSystem.Ty := .product .bool .bool
  let mapType : TypeSystem.Ty := .mapping keyType .word
  let key : SourceTypedRuntime.Value := .product (.bool true) (.bool false)
  let raw : SourceTypedRuntime.Value := .mapping (.comptime keyType) (.comptime .word)
    [(key, w 37), (key, w 91)]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 819)⟩]}
  let gap ← faultBinder compiled "fail"
  let afterGap ← faultBinder compiled "failAfter"
  let cases : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value) := [
    ("ordered", [], w 4), ("rawEcho", [raw], raw), ("defaulted", [], w 0),
    ("aliases", [w 5], w 17), ("self", [w 3], w 5), ("left", [w 2], w 7), ("right", [w 2], w 11)]
  let completed ← cases.mapM fun (name, arguments, _) => finish compiled name arguments 300000 initial
  let faultNames := ["firstFault", "laterFault", "bodyFault"]
  let faults ← faultNames.mapM fun name => finish compiled name [] 300000 initial
  for fuel in [0, 43, 300000] do
    for ((name, arguments, expected), baseline) in cases.zip completed do
      let observation ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"named bound full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected)
          s!"named bound result changed {name}: {reprStr actual}"
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
          s!"named bound inert prefix changed {name}"
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"named bound unsafe source heap {name}"
        if name == "ordered" then
          cells initial final [(.word, some (w 7)), (.word, some (w 7)),
            (.word, some (w 3)), (.word, some (w 3)), (.word, some (w 7)), (.word, some (w 3))] name
        if name == "rawEcho" then cells initial final [(mapType, some raw), (mapType, some raw)] name
      | other => throw (IO.userError s!"named bound {name}: {reprStr other}")
    for (name, baseline) in faultNames.zip faults do
      let observation ← finish compiled name [] fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"named bound full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == if name == "bodyFault" then afterGap else gap)
          "named bound fault lost exact source binder"
        let earlier := if name == "firstFault" then [] else [(.word, some (w 7)), (.word, some (w 7))]
        let inner := if name == "bodyFault" then [(.word, some (w 7)), (.word, some (w 17))]
          else [(.word, some (w 5))]
        cells initial final (earlier ++ inner ++ [(.word, none)]) name
      | other => throw (IO.userError s!"named bound fault {name}: {reprStr other}")
  IO.println "recursive named expression bounds: original child costs, concrete body budgets, all-target frame restoration, ordered arguments, first faults, raw metadata, aliases and native resume GREEN"
end Tests.SourceCoreRecursiveNamedExpressionBounds
