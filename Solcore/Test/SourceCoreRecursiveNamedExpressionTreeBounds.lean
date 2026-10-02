import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds
import Solcore.Test.SourceCoreRecursiveNamedExpressionBounds

/-! The unchanged expression Tree closes every structural child at one budget.
A concrete singleton builtin body closes the remaining body family in these
consumers. General catalog/body mutual closure remains a later unit. Actual
mixed code checks recursive parent/argument positions, fault order and resume. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedExpressionTreeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds
#check_failure RecursiveNamedExpressionTreeBounds.Tree
#check_failure RecursiveNamedExpressionTreeBounds.BodyMeaning
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



include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
/-- Every child is supplied by the same recursive Tree; the concrete body
certificate closes the actual remaining body family. -/
theorem concrete_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        readFuel values source context solved reasonAt) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionTreeBounds.preserves_at functions extension faithful functionLeaves functionTypes
    evidence callerValid unique owners callerUninitialized callerMissing budget size within
  intro header member child _
  have same : header = Header.of_body body := by simpa only [List.mem_singleton] using member
  subst header
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry outcome after trace
  exact SourceCoreRecursiveNamedExpressionBounds.builtin_body_preserves_at
    (headers := [Header.of_body body]) (locations := locations) (capturePrefix := capturePrefix)
    functions extension body uninitialized missing faithful functionLeaves functionTypes child entry trace

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
/-- Completed Core code produces an independent source trace; the body is
proved from its finite static certificate rather than supplied as execution. -/
theorem concrete_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        readFuel values source context solved reasonAt) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionTreeBounds.reflects_at functions extension faithful functionLeaves functionTypes
    evidence callerValid callerUninitialized callerMissing budget size within
  intro header member child _
  have same : header = Header.of_body body := by simpa only [List.mem_singleton] using member
  subst header
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry value finalStore completed
  exact SourceCoreRecursiveNamedExpressionBounds.builtin_body_reflects_at
    (headers := [Header.of_body body]) (locations := locations) (capturePrefix := capturePrefix)
    functions extension body uninitialized missing faithful functionLeaves functionTypes child entry completed
end ConcreteBodies

private def content : String := String.intercalate "\n" [
  "enum Box { Box(Bool) }", "enum Key { Key(Bool) }",
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function truth(flag: Bool) returns (Bool) { let saved = flag; return saved; }",
  "function take(a: Word, b: Word) returns (Word) { return a - b; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function failAfter(n: Word) returns (Word) { let written = n + 10; let gap: Word; return gap; }",
  "function badBool() returns (Bool) { let written = 19; let gap: Bool; return gap; }",
  "function ordered() returns (Word) { return take(side(7), side(3)); }",
  "function grouped() returns (integer) { return ((integerSub(wordToInteger(side(7)), wordToInteger(side(9))))); }",
  "function fromIndex() returns (integer) { let m: mapping(Bool => Word); m[true] = 37; return integerAdd(wordToInteger(m[truth(true)]), wordToInteger(side(5))); }",
  "function choose() returns (integer) { return truth(true) ? integerAdd(wordToInteger(side(7)), wordToInteger(side(9))) : wordToInteger(fail()); }",
  "function boxed() returns (Box) { return Box(truth(integerEq(7, 7))); }",
  "function paired() returns ((Bool, Bool)) { return (truth(integerEq(7, 7)), truth(integerLt(7, 7))); }",
  "function keyData() returns (Bool) { let m: mapping(Key => Bool); return m[Key(truth(integerEq(7, 7)))]; }",
  "function skip() returns (Bool) { return false && truth(integerEq(7, 7)); }",
  "function unary() returns (Bool) { return !truth(false); }",
  "function firstFault() returns (integer) { return integerAdd(wordToInteger(fail()), wordToInteger(side(99))); }",
  "function laterFault() returns (integer) { return integerAdd(wordToInteger(side(7)), wordToInteger(fail())); }",
  "function keyFault() returns (integer) { let m: mapping(Bool => Word); return wordToInteger(m[badBool()]); }",
  "function bodyFault() returns (integer) { return wordToInteger(failAfter(side(7))); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"tree bound resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"tree bound prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"tree bound ordered cells changed {label}: {reprStr final.heap}"
private def constructor (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO DataConstructorInstantiation := do
  let signature ← match compiled.sourceProgram.signatures.dataTypes.filter (·.name == name) with
    | [signature] => pure signature | _ => throw (IO.userError "tree bound nominal signature missing")
  let selected ← match signature.constructors with
    | [selected] => pure selected | _ => throw (IO.userError "tree bound constructor missing")
  pure ⟨selected.id, [], selected.payloadTypes, .nominal signature.id []⟩
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "tree bound fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "tree bound exact fault binder missing")


def run : IO Unit := do
  let names := ["ordered", "grouped", "fromIndex", "choose", "boxed", "paired", "keyData", "skip", "unary",
    "firstFault", "laterFault", "keyFault", "bodyFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named expression Tree bounds" content names
  let box ← constructor compiled "Box"
  let key ← constructor compiled "Key"
  let materialized : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 37)]
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("ordered", w 4, [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 3)), (.word, some (w 3)), (.word, some (w 7)), (.word, some (w 3))]),
    ("grouped", .integer (-2), [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 9)), (.word, some (w 9))]),
    ("fromIndex", .integer 42, [(.mapping .bool .word, some materialized), (.bool, some (.bool true)), (.bool, some (.bool true)), (.word, some (w 5)), (.word, some (w 5))]),
    ("choose", .integer 16, [(.bool, some (.bool true)), (.bool, some (.bool true)), (.word, some (w 7)), (.word, some (w 7)), (.word, some (w 9)), (.word, some (w 9))]),
    ("boxed", .constructed box [.bool true], [(.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("paired", .product (.bool true) (.bool false), [(.bool, some (.bool true)), (.bool, some (.bool true)), (.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("keyData", .bool false, [(.mapping key.resultType .bool, some (.mapping key.resultType .bool [])), (.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("skip", .bool false, []),
    ("unary", .bool true, [(.bool, some (.bool false)), (.bool, some (.bool false))])]
  let failures := ["firstFault", "laterFault", "keyFault", "bodyFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 819)⟩]}
  let firstGap ← faultBinder compiled "fail"
  let keyGap ← faultBinder compiled "badBool"
  let bodyGap ← faultBinder compiled "failAfter"
  let completed ← successes.mapM fun test => finish compiled test.1 [] 300000 initial
  let failed ← failures.mapM fun name => finish compiled name [] 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip completed do
      let (name, expected, expectedCells) := test
      let observation ← finish compiled name [] fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"tree bound full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"tree bound result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"tree bound source heap not deeply safe {name}"
      | other => throw (IO.userError s!"tree bound {name}: {reprStr other}")
    for (name, baseline) in failures.zip failed do
      let observation ← finish compiled name [] fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"tree bound full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        let expected := if name == "keyFault" then keyGap else if name == "bodyFault" then bodyGap else firstGap
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == expected) "tree bound lost first source fault binder"
        let earlier := if name == "laterFault" || name == "bodyFault" then [(.word, some (w 7)), (.word, some (w 7))] else []
        let effects := match name with
          | "keyFault" => [(.mapping .bool .word, some (.mapping .bool .word [])), (.word, some (w 19)), (.bool, none)]
          | "bodyFault" => [(.word, some (w 7)), (.word, some (w 17)), (.word, none)]
          | _ => [(.word, some (w 5)), (.word, none)]
        cells initial final (earlier ++ effects) name
      | other => throw (IO.userError s!"tree bound fault {name}: {reprStr other}")
  IO.println "recursive named expression Tree bounds: unchanged recursive grammar, inclusive structural IH, actual strict callee boundary, mixed parent/arguments, fault order and resume GREEN"
end Tests.SourceCoreRecursiveNamedExpressionTreeBounds
