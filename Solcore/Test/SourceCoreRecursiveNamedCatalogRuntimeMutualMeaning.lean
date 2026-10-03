import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning
import Solcore.Test.SourceCoreRecursiveNamedCatalogMatchMeaning
import Solcore.Test.SourceCoreRecursiveNamedCatalogRuntimeMatchProfiles

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
