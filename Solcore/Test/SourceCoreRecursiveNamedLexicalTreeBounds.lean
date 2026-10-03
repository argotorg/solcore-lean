import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds
import Solcore.Test.SourceCoreRecursiveNamedExpressionTreeBounds

/-! The actual lexical Tree closes all its children at one inclusive budget.
These consumers use the same concrete named expression family and finite
builtin body certificate. Catalog mutual closure and whole compiler extraction
remain separate boundaries. Runtime cases retain exact allocation/fault order. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedLexicalTreeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
#check_failure RecursiveNamedLexicalTreeBounds.Tree
#check_failure RecursiveNamedLexicalTreeBounds.BodyMeaning
#check_failure SourceTypedRuntime.run
section Concrete
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {body : BuiltinNamedCalls.Body prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope mode statements expected type code) :
    RecursiveNamedLexicalContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  apply RecursiveNamedLexicalTreeBounds.preserves_at functions definitions registered program evidence
    entry_transport entry_binds budget size bounded ?_ tree valid unique
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  intro child within context valid
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_preserves_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid unique owners uninitialized missing budget child within

include definitions registered extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope mode statements expected type code) :
    RecursiveNamedLexicalContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  apply RecursiveNamedLexicalTreeBounds.reflects_at functions definitions registered program evidence
    entry_transport entry_binds budget size bounded ?_ tree valid
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  intro child within context valid
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_reflects_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid uninitialized missing budget child within
end Concrete

private def content : String := String.intercalate "\n" [
  "function side(n: Word) returns (Word) { let copied = n; return copied; }",
  "function truth(flag: Bool) returns (Bool) { let copied = flag; return copied; }",
  "function bad() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function badBool() returns (Bool) { let written = 19; let gap: Bool; return gap; }",
  "function empty() {}",
  "function unitReturn() { return; let skipped = 99; }",
  "function returned() returns (Word) { return side(7); }",
  "function tailed() returns (Word) { side(7) }",
  "function absent() { let gap: Word; }",
  "function initialized() returns (Word) { let value = side(7); return value; }",
  "function discarded() returns (Word) { side(7); return side(3); }",
  "function blocks() returns (Word) { { let inner = side(7); inner; } return side(3); }",
  "function branches(flag: Bool) returns (Word) { if (truth(flag && integerEq(7, 7))) { let chosen = side(7); chosen; } else { let chosen = side(4); chosen; } return side(3); }",
  "function shadow() returns (Word) { let value = side(7); { let value = side(4); value; } return side(value); }",
  "function earlyReturn(flag: Bool) returns (Word) { if (truth(flag)) { return side(9); } else { return side(5); } return bad(); }",
  "function absentFault() returns (Word) { let prior = 2; let gap: Word; return gap; }",
  "function initializerFault() returns (Word) { let prior = side(2); let failed = bad(); return side(99); }",
  "function conditionFault() returns (Word) { let prior = side(2); if (truth(badBool())) { side(99); } return side(100); }",
  "function discardFault() returns (Word) { { let retained = side(4); bad(); } return side(99); }",
  "function returnFault() returns (Word) { return bad(); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (w n))
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"lexical Tree bound resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"lexical Tree bound prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"lexical Tree bound ordered cells changed {name}: {reprStr final.heap}"
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "lexical Tree bound fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "lexical Tree bound exact fault binder missing")

def run : IO Unit := do
  let names := ["empty", "unitReturn", "returned", "tailed", "absent", "initialized", "discarded", "blocks", "branches",
    "shadow", "earlyReturn", "absentFault", "initializerFault", "conditionFault", "discardFault", "returnFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named lexical Tree bounds" content names
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 819)⟩]}
  let boolCells := fun flag => List.replicate 3 (.bool, some (SourceTypedRuntime.Value.bool flag))
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("empty", [], .unit, []), ("unitReturn", [], .unit, []),
    ("returned", [], w 7, [7, 7].map present), ("tailed", [], w 7, [7, 7].map present),
    ("absent", [], .unit, [(.word, none)]), ("initialized", [], w 7, [7, 7, 7].map present),
    ("discarded", [], w 3, [7, 7, 3, 3].map present), ("blocks", [], w 3, [7, 7, 7, 3, 3].map present),
    ("branches", [.bool true], w 3, boolCells true ++ [7, 7, 7, 3, 3].map present),
    ("branches", [.bool false], w 3, boolCells false ++ [4, 4, 4, 3, 3].map present),
    ("shadow", [], w 7, [7, 7, 7, 4, 4, 4, 7, 7].map present),
    ("earlyReturn", [.bool true], w 9, boolCells true ++ [9, 9].map present),
    ("earlyReturn", [.bool false], w 5, boolCells false ++ [5, 5].map present)]
  let failures : List (String × String × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("absentFault", "absentFault", [present 2, (.word, none)]),
    ("initializerFault", "bad", [2, 2, 2, 5].map present ++ [(.word, none)]),
    ("conditionFault", "badBool", [2, 2, 2, 19].map present ++ [(.bool, none)]),
    ("discardFault", "bad", [4, 4, 4, 5].map present ++ [(.word, none)]),
    ("returnFault", "bad", [present 5, (.word, none)])]
  let complete ← successes.mapM fun test => finish compiled test.1 test.2.1 300000 initial
  let failed ← failures.mapM fun test => finish compiled test.1 [] 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip complete do
      let (name, arguments, expected, expectedCells) := test
      let observation ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"lexical Tree bound full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"lexical Tree bound result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"lexical Tree bound heap not deeply safe {name}"
      | other => throw (IO.userError s!"lexical Tree bound {name}: {reprStr other}")
    for (test, baseline) in failures.zip failed do
      let (name, owner, expectedCells) := test
      let observation ← finish compiled name [] fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"lexical Tree bound full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        let expected ← faultBinder compiled owner
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == expected) s!"lexical Tree bound first fault binder changed {name}"
        cells initial final expectedCells name
      | other => throw (IO.userError s!"lexical Tree bound fault {name}: {reprStr other}")
  IO.println "recursive named lexical Tree bounds: all nine unchanged constructors, concrete named/builtin child laws, inclusive budget, allocation/restore/fault order and public resume GREEN"

end Tests.SourceCoreRecursiveNamedLexicalTreeBounds
