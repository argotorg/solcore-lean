import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinHeadBounds
import Solcore.Test.SourceCoreRecursiveNamedExpressionCompositionsBounds

/-! Contracted builtin heads consume concrete named or builtin argument proofs
within one finite bound. Runtime fixtures verify ordered argument writes,
conversion and public faults independently of the formal cost measure. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedBuiltinBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds

#check_failure RecursiveNamedBuiltinHeadBounds.Tree
#check_failure SourceTypedRuntime.run

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

variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {readFuel : Nat}
  {compilation : SourceCoreFunctions.Context}
  (callerValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))


def Leaf : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  RecursiveNamedCatalog.Head [Header.of_body body] compilation source context
    (CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt) scope id lowered ∨
  CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
/-- The argument obligation is closed by the concrete singleton body grammar. -/
theorem contracted_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (BuiltinCalls.Typed.Head values source (Leaf body (source := source) (context := context) (compilation := compilation)
        (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedBuiltinHeadBounds.Head.preserves_at (functions := functions) (functionLeaves := functionLeaves)
    (program := program) (evidence := evidence) (unique := unique) (transport := entry_transport) budget size within
  intro child childWithin
  exact SourceCoreRecursiveNamedExpressionCompositionsBounds.leaf_preserves_at functions extension body
    uninitialized missing faithful functionLeaves functionTypes callerValid unique owners
    callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
/-- Native argument completion reconstructs an independently sized Source call. -/
theorem contracted_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (BuiltinCalls.Typed.Head values source (Leaf body (source := source) (context := context) (compilation := compilation)
        (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedBuiltinHeadBounds.Head.reflects_at (functions := functions) (functionLeaves := functionLeaves)
    (program := program) (evidence := evidence) (transport := entry_transport) budget size within
  intro child childWithin
  exact SourceCoreRecursiveNamedExpressionCompositionsBounds.leaf_reflects_at functions extension body
    uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
    budget child childWithin
end ConcreteBodies

private def content : String := String.intercalate "\n" [
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function wordSide(n: Word) returns (Word) { let saved = n; return saved; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function ordered() returns (integer) { return integerSub(wordToInteger(side(7)), wordToInteger(side(3))); }",
  "function converted() returns (integer) { return wordToInteger(wordFromInteger(integerSub(wordToInteger(side(0)), wordToInteger(side(9))))); }",
  "function fromWord() returns (integer) { return wordToInteger(wordSide(11)); }",
  "function nested() returns (integer) { return integerAdd(wordToInteger(wordSide(7)), integerSub(wordToInteger(side(9)), wordToInteger(side(3)))); }",
  "function firstFault() returns (integer) { return integerAdd(wordToInteger(fail()), wordToInteger(side(99))); }",
  "function laterFault() returns (integer) { return integerAdd(wordToInteger(side(7)), wordToInteger(fail())); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (fuel : Nat)
    (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"builtin bound resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"builtin bound prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"builtin bound ordered cells changed {label}: {reprStr final.heap}"
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "builtin bound fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "builtin bound exact fault binder missing")

def run : IO Unit := do
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("ordered", .integer 4, [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 3)), (.word, some (w 3))]),
    ("converted", .integer (Int.ofNat (Word.ofIntModulo (-9)).val), [(.word, some (w 0)), (.word, some (w 0)), (.word, some (w 9)), (.word, some (w 9))]),
    ("fromWord", .integer 11, [(.word, some (w 11)), (.word, some (w 11))]),
    ("nested", .integer 13, [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 9)), (.word, some (w 9)), (.word, some (w 3)), (.word, some (w 3))])]
  let failures := ["firstFault", "laterFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named builtin bounds" content
    (successes.map (fun test => test.1) ++ failures)
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 819)⟩]}
  let gap ← faultBinder compiled
  let completed ← successes.mapM fun test => finish compiled test.1 300000 initial
  let failed ← failures.mapM fun name => finish compiled name 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip completed do
      let (name, expected, expectedCells) := test
      let observation ← finish compiled name fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"builtin bound full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"builtin bound result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"builtin bound unsafe source heap {name}"
      | other => throw (IO.userError s!"builtin bound {name}: {reprStr other}")
    for (name, baseline) in failures.zip failed do
      let observation ← finish compiled name fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"builtin bound full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "builtin bound fault lost source binder"
        let earlier := if name == "laterFault" then [(.word, some (w 7)), (.word, some (w 7))] else []
        cells initial final (earlier ++ [(.word, some (w 5)), (.word, none)]) name
      | other => throw (IO.userError s!"builtin bound fault {name}: {reprStr other}")
  IO.println "recursive named builtin bounds: real contracted arguments, fixed bound, independent Source sizes, ordered effects, first/later faults and resume GREEN"
end Tests.SourceCoreRecursiveNamedBuiltinBounds
