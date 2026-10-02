import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompositionsBounds
import Solcore.Test.SourceCoreRecursiveNamedExpressionBounds

/-! Concrete named and builtin leaves discharge pointwise head obligations.
Two applications use the same finite budget, including unchanged group code.
The runtime corpus checks named calls under each composition, short circuit
and first-fault effects. Whole recursive Tree closure is a later unit. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedExpressionCompositionsBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds
open CompatibleExpressionTypedCompositions

#check_failure RecursiveNamedExpressionCompositionsBounds.Through
#check_failure RecursiveNamedExpressionCompositionsBounds.Tree
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


private def Leaf : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  RecursiveNamedCatalog.Head [Header.of_body body] compilation source context
    (CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt) scope id lowered ∨
  CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
theorem leaf_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered certificate
  change _ ∨ _ at certificate
  cases certificate with
  | inl named =>
    exact SourceCoreRecursiveNamedExpressionBounds.builtin_named_preserves_at functions extension body uninitialized missing faithful functionLeaves functionTypes
      callerValid unique owners callerUninitialized callerMissing budget size within named
  | inr builtin =>
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed _
        (CompatibleExpressionBuiltins.preserves functions extension faithful functionLeaves functionTypes
          program evidence callerValid unique callerUninitialized callerMissing)) size builtin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
theorem leaf_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered certificate
  change _ ∨ _ at certificate
  cases certificate with
  | inl named =>
    exact SourceCoreRecursiveNamedExpressionBounds.builtin_named_reflects_at functions extension body uninitialized missing faithful functionLeaves functionTypes
      callerValid callerUninitialized callerMissing budget size within named
  | inr builtin =>
    exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed _
        (CompatibleExpressionBuiltins.reflects functions extension faithful functionLeaves functionTypes
          program evidence callerValid callerUninitialized callerMissing)) size builtin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
/-- Head composition consumes concrete leaf proofs at the inclusive budget. -/
theorem composed_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionCompositionsBounds.Head.preserves_at functions program evidence
    entry_transport budget size within unique
  intro child childWithin
  exact leaf_preserves_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid unique owners callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
/-- Reflection reconstructs source costs independently of native costs. -/
theorem composed_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionCompositionsBounds.Head.reflects_at functions program evidence
    entry_transport budget size within
  intro child childWithin
  exact leaf_reflects_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid unique owners callerUninitialized callerMissing in
/-- A second structural layer keeps the same budget, even for groups. -/
theorem twice_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source (Head values.checked source
        (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionCompositionsBounds.Head.preserves_at functions program evidence
    entry_transport budget size within unique
  intro child childWithin
  exact composed_preserves_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid unique owners callerUninitialized callerMissing budget child childWithin

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing in
theorem twice_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source (Head values.checked source
        (Leaf body (source := source) (context := context) (compilation := compilation) (solved := solved) (reasonAt := reasonAt) (readFuel := readFuel)))) faults
      (protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix) := by
  apply RecursiveNamedExpressionCompositionsBounds.Head.reflects_at functions program evidence
    entry_transport budget size within
  intro child childWithin
  exact composed_reflects_at functions extension body uninitialized missing faithful functionLeaves functionTypes
    callerValid callerUninitialized callerMissing budget child childWithin
end ConcreteBodies

private def content : String := String.intercalate "\n" [
  "function side(n: Word) returns (Word) { let saved = n; return saved; }",
  "function truth(flag: Bool) returns (Bool) { let saved = flag; return saved; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function badBool() returns (Bool) { let written = 19; let gap: Bool; return gap; }",
  "function grouped() returns (Word) { return ((side(7))); }",
  "function paired() returns ((Word, Word)) { return (side(7), side(3)); }",
  "function unary() returns (Bool) { return !truth(false); }",
  "function strict() returns (Word) { return side(7) - side(3); }",
  "function choose() returns (Word) { return truth(false) ? fail() : side(11); }",
  "function chooseTrue() returns (Word) { return truth(true) ? side(13) : fail(); }",
  "function andSkip() returns (Bool) { return truth(false) && badBool(); }",
  "function andNext() returns (Bool) { return truth(true) && truth(false); }",
  "function orSkip() returns (Bool) { return truth(true) || badBool(); }",
  "function orNext() returns (Bool) { return truth(false) || truth(true); }",
  "function firstFault() returns (Word) { return fail() + side(7); }",
  "function laterFault() returns (Word) { return side(7) + fail(); }",
  "function conditionFault() returns (Word) { return badBool() ? side(13) : side(11); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (fuel : Nat)
    (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"composition bound resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"composition bound prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"composition bound ordered cells changed {label}: {reprStr final.heap}"
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "composition bound fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "composition bound exact fault binder missing")

def run : IO Unit := do
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("grouped", w 7, [(.word, some (w 7)), (.word, some (w 7))]),
    ("paired", .product (w 7) (w 3), [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 3)), (.word, some (w 3))]),
    ("unary", .bool true, [(.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("strict", w 4, [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 3)), (.word, some (w 3))]),
    ("choose", w 11, [(.bool, some (.bool false)), (.bool, some (.bool false)), (.word, some (w 11)), (.word, some (w 11))]),
    ("chooseTrue", w 13, [(.bool, some (.bool true)), (.bool, some (.bool true)), (.word, some (w 13)), (.word, some (w 13))]),
    ("andSkip", .bool false, [(.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("andNext", .bool false, [(.bool, some (.bool true)), (.bool, some (.bool true)), (.bool, some (.bool false)), (.bool, some (.bool false))]),
    ("orSkip", .bool true, [(.bool, some (.bool true)), (.bool, some (.bool true))]),
    ("orNext", .bool true, [(.bool, some (.bool false)), (.bool, some (.bool false)), (.bool, some (.bool true)), (.bool, some (.bool true))])]
  let failures := ["firstFault", "laterFault", "conditionFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named composition bounds" content
    (successes.map (fun test => test.1) ++ failures)
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 819)⟩]}
  let gap ← faultBinder compiled "fail"
  let boolGap ← faultBinder compiled "badBool"
  let completed ← successes.mapM fun test => finish compiled test.1 300000 initial
  let failed ← failures.mapM fun name => finish compiled name 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip completed do
      let (name, expected, expectedCells) := test
      let observation ← finish compiled name fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"composition bound full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"composition bound result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"composition bound unsafe source heap {name}"
      | other => throw (IO.userError s!"composition bound {name}: {reprStr other}")
    for (name, baseline) in failures.zip failed do
      let observation ← finish compiled name fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"composition bound full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == if name == "conditionFault" then boolGap else gap)
          "composition bound fault lost source binder"
        let earlier := if name == "laterFault" then [(.word, some (w 7)), (.word, some (w 7))] else []
        let inner := if name == "conditionFault" then [(.word, some (w 19)), (.bool, none)] else [(.word, some (w 5)), (.word, none)]
        cells initial final (earlier ++ inner) name
      | other => throw (IO.userError s!"composition bound fault {name}: {reprStr other}")
  IO.println "recursive named composition bounds: inclusive structural budgets, original strict source/native children, all five heads, ordered effects, skip/fault and resume GREEN"
end Tests.SourceCoreRecursiveNamedExpressionCompositionsBounds
