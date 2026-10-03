import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForReflection
import Solcore.Test.SourceCoreRecursiveNamedExpressionTreeBounds

/-! The unchanged imperative grammar consumes bounded expression laws at one
budget. The concrete expression Tree and finite builtin callee close those
laws here; no child/body execution is a field of the static receipt. Source
and native costs are independent, and the preservation endpoint includes N. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedImperativeForBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
#check_failure RecursiveNamedImperativeFor.Tree
#check_failure RecursiveNamedImperativeFor.BodyMeaning
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
  {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
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
theorem concrete_preserves (budget : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size => RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  apply RecursiveNamedImperativeFor.preservesAt_for functions definitions registered extension program evidence
    entry_transport entry_binds budget faithful observations ?_ .reachable unique tree errors
  intro context valid child within
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_preserves_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid unique owners uninitialized missing budget child within

include definitions registered extension faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_reflects (budget : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  apply RecursiveNamedImperativeFor.reflectsAt_for functions definitions registered extension program evidence
    entry_transport entry_binds budget ?_ faithful observations .reachable runtimeViews unique tree errors
  intro context valid child smaller
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_reflects_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid uninitialized missing budget child (Nat.le_of_lt smaller)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The inclusive endpoint used by a source-body strong induction. No N+1
budget and no callee law at N is supplied by this consumer. -/
theorem concrete_preserves_at_top (size : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code :=
  concrete_preserves functions definitions registered extension faithful observations runtimeViews evidence unique owners
    uninitialized missing bodyUninitialized bodyMissing size tree errors size (Nat.le_refl size)

include definitions registered extension faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing in
/-- A completed native body gives its own source size, without relating source
cost to the original native budget. -/
theorem concrete_native_only (budget size : Nat) (smaller : size < budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code :=
  concrete_reflects functions definitions registered extension faithful observations runtimeViews evidence unique
    uninitialized missing bodyUninitialized bodyMissing budget tree errors size smaller
end Concrete

private def content : String := String.intercalate "\n" [
  "function side(value: Word) returns (Word) { return value; }",
  "function truth(value: Bool) returns (Bool) { return value; }",
  "function bad() returns (Word) { let stamp = 19; let gap: Word; return gap; }",
  "function badBool() returns (Bool) { let stamp = 23; let gap: Bool; return gap; }",
  "function nested(raw: mapping(Word => Word), seed: Word) returns (Word) { let outer = 0; let count = seed; for (; outer < 2; outer += 1) { let inner = 0; while (inner < 2) { inner += 1; raw[side(1)] += side(2); count += 1; if (inner < 2) { continue; } break; } } return side(count + raw[1]); }",
  "function returns(raw: mapping(Word => Word), seed: Word) returns (Word) { for (let outer = 0; true; let dead = bad()) { while (true) { for (let inner = 0; true; let dead = bad()) { raw[side(1)] += side(2); return side(seed + raw[1]); } } } return 99; }",
  "function headerFault(raw: mapping(Word => Word), seed: Word) returns (Word) { for (raw[side(1)] += side(3), let missing: Word, let failed = missing; true; ) { raw[side(1)] += side(99); } return seed; }",
  "function postFault(raw: mapping(Word => Word), seed: Word) returns (Word) { for (let i = 0; i < 2; let stage = side(3), raw[side(1)] += stage, let missing: Word, raw[side(1)] += missing) { raw[side(1)] += side(2); continue; } return seed; }",
  "function keyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { for (; true; ) { raw[bad()] += side(99); } return seed; }",
  "function rhsFault(raw: mapping(Word => Word), seed: Word) returns (Word) { for (; true; ) { raw[side(1)] += side(2); raw[side(1)] += bad(); } return seed; }",
  "function bitNot(raw: mapping(Word => Word), seed: Word) returns (Word) { let mask = seed; for (let i = 0; i < 2; i += 1, mask ~=, mask ~=) { mask ~=; mask ~=; raw[side(1)] += side(1); } return mask + raw[1]; }",
  "function conditionFault(raw: mapping(Word => Word), seed: Word) returns (Word) { while (truth(badBool())) { raw[side(1)] += side(99); } return seed; }",
  "function empty(raw: mapping(Word => Word), seed: Word) returns (Word) { for (; true; ) { break; } return seed + raw[1]; }",
  "function shadowPost(raw: mapping(Word => Word), seed: Word) returns (Word) { let item = seed; for (let i = 0; i < 2; let item = side(i), item, i += 1) { raw[side(1)] += side(1); } return item + raw[1]; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(w 1, w n), (w 1, w 91)]
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (w n))
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name binderName : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "imperative bound fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == binderName) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "imperative bound exact fault binder missing")

def run : IO Unit := do
  let names := ["nested", "returns", "headerFault", "postFault", "keyFault", "rhsFault", "bitNot", "conditionFault", "empty", "shadowPost"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named imperative bounds" content names
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 819)⟩]}
  let tests : List (String × Option Nat × Nat × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("nested", some 29, 18, [7,2,11,2,1,2,1,2,2,1,2,1,2,29].map present),
    ("returns", some 19, 12, [7,0,0,1,2,19].map present),
    ("headerFault", none, 13, [7,1,3].map present ++ [(.word, none)]),
    ("postFault", none, 15, [7,0,1,2,3,3,1].map present ++ [(.word, none), present 1]),
    ("keyFault", none, 10, [7,19].map present ++ [(.word, none)]),
    ("rhsFault", none, 12, [7,1,2,1,19].map present ++ [(.word, none)]),
    ("bitNot", some 19, 12, [7,7,2,1,1,1,1].map present),
    ("conditionFault", none, 10, [7,23].map present ++ [(.bool, none)]),
    ("empty", some 17, 10, [present 7]),
    ("shadowPost", some 19, 12, [7,7,2,1,1,0,0,1,1,1,1].map present)]
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, expectedResult, mappingValue, rest) in tests do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10, w 7] fuel initial
      let completed ← SourceCoreUnifiedCorpusSupport.get s!"imperative bound resume {name}" (started.resume 400000)
      let observation := completed.observation
      let final ← match observation, expectedResult with
        | .done value final, some expected =>
          SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr (w expected)) s!"imperative bound result {name}"
          pure final
        | .fault (.uninitializedLocal actual) final, none =>
          let (owner, binder) := if name == "conditionFault" then ("badBool", "gap")
            else if name == "keyFault" || name == "rhsFault" then ("bad", "gap") else (name, "missing")
          let expected ← faultBinder compiled owner binder
          SourceCoreUnifiedCorpusSupport.assertTrue (actual == expected) s!"imperative bound first fault {name}"
          pure final
        | other, _ => throw (IO.userError s!"imperative bound unexpected {name}: {reprStr other}")
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
        s!"imperative bound inert prefix {name}"
      let expectedCells := (.mapping .word .word, some (table mappingValue)) :: rest
      SourceCoreUnifiedCorpusSupport.assertTrue
        (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expectedCells)
        s!"imperative bound all ordered raw cells {name}: {reprStr final.heap}"
      current := current ++ [reprStr observation]
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "imperative bound resume changed full observations"
  IO.println "recursive named imperative bounds: same grammar and finite loops, inclusive source endpoint, original native children, concrete callees, nested transfers, ordered keys/post cells/fault effects and resume GREEN"

end Tests.SourceCoreRecursiveNamedImperativeForBounds
