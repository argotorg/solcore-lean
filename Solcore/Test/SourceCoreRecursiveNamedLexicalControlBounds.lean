import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalControlBounds
import Solcore.SourceSemantics.CoreLowering.BuiltinLexicalStatements
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Concrete builtin trees close all six block/sequence/conditional consumers.
Original measured source and native children are selected by the production
helpers. Runtime checks preserve ordered cells through scope restoration,
selected branches, early faults and public checkpoint resume. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedLexicalControlBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedLexicalContracts RecursiveNamedLexicalControlBounds
section Concrete
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (unique : NodeOccurrencesUnique source)
  {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
  {statements rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code body : Expr}

include definitions registered extension faithful observations runtimeViews unique uninitialized missing in
private theorem builtin_preserves_at (size : Nat)
    (tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source solved reasonAt
      context scope mode statements expected type code) :
    PreservesAt (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (solved := solved) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped _ trace
  exact BuiltinLexicalStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews
    program evidence uninitialized missing tree unique valid environments heaps locals agrees typed reference read unmapped trace.sound

include definitions registered extension faithful observations runtimeViews uninitialized missing in
private theorem builtin_reflects_at (size : Nat)
    (tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source solved reasonAt
      context scope mode statements expected type code) :
    ReflectsAt (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (solved := solved) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped _ evaluated
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata, lexical⟩ :=
    BuiltinLexicalStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews
      program evidence uninitialized missing tree valid environments heaps locals agrees typed reference read unmapped evaluated.sound
  obtain ⟨sourceSize, trace⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size trace
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata, lexical⟩

variable {id : StatementId} {node : StatementNode}
  (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
  (inner : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source solved reasonAt
    context scope false statements expected type code)

include definitions registered extension faithful observations runtimeViews unique uninitialized missing found form inner in
theorem closed_block_preserves_at (budget size : Nat) (within : size ≤ budget) :
    HeadPreservesAt (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (solved := solved) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) id expected type code := by
  exact block_preserves_at functions program evidence unique budget size within found form
    (fun child _ => builtin_preserves_at functions definitions registered extension faithful observations runtimeViews program evidence
      uninitialized missing unique child inner)

include definitions registered extension faithful observations runtimeViews uninitialized missing found form inner in
theorem closed_block_reflects_at (budget size : Nat) (within : size ≤ budget) :
    HeadReflectsAt (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (solved := solved) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) id expected type code := by
  exact block_reflects_at functions program evidence budget size within found form
    (fun child _ => builtin_reflects_at functions definitions registered extension faithful observations runtimeViews program evidence
      uninitialized missing child inner)

variable (tail : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source solved reasonAt
    context scope mode rest expected type body)

include definitions registered extension faithful observations runtimeViews unique uninitialized missing transport found form inner tail in
theorem closed_sequence_preserves_at (budget size : Nat) (within : size ≤ budget) :
    PreservesAt (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (solved := solved) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type code body) := by
  exact sequence_preserves_at functions program evidence unique transport budget size within found (by intro expression; simp [form])
    (fun child smaller => closed_block_preserves_at functions definitions registered extension faithful observations runtimeViews
      program evidence uninitialized missing unique found form inner budget child smaller)
    (fun child _ => builtin_preserves_at functions definitions registered extension faithful observations runtimeViews program evidence
      uninitialized missing unique child tail)

include definitions registered extension faithful observations runtimeViews uninitialized missing transport found form inner tail in
theorem closed_sequence_reflects_at (budget size : Nat) (within : size ≤ budget) :
    ReflectsAt (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (solved := solved) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type code body) := by
  exact sequence_reflects_at functions program evidence transport budget size within found (by intro expression; simp [form])
    (fun child smaller => closed_block_reflects_at functions definitions registered extension faithful observations runtimeViews
      program evidence uninitialized missing found form inner budget child smaller)
    (fun child _ => builtin_reflects_at functions definitions registered extension faithful observations runtimeViews program evidence
      uninitialized missing child tail)

variable {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
  {elseBody : Option (List StatementId)} {conditionCode thenCode elseCode : Expr}
  (conditionalForm : node.form = .ifThen condition thenBody elseBody)
  (conditionFound : source.lookupExpression? condition = some conditionNode) (conditionType : conditionNode.type = .bool)
  (conditionTree : CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
  (thenTree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source solved reasonAt
    context scope false thenBody expected type thenCode)
  (elseTree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source solved reasonAt
    context scope false (elseBody.getD []) expected type elseCode)

include definitions registered extension faithful observations runtimeViews unique uninitialized missing transport found conditionalForm conditionFound conditionType conditionTree thenTree elseTree in
theorem closed_conditional_preserves_at (budget size : Nat) (within : size ≤ budget) :
    HeadPreservesAt (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (solved := solved) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  exact conditional_preserves_at functions program evidence transport budget size within unique
    (fun child _ current valid => RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (CompatibleExpressionBuiltins.preserves functions extension faithful observations runtimeViews program evidence valid unique uninitialized missing)) child)
    found conditionalForm conditionFound conditionType conditionTree
    (fun child _ => builtin_preserves_at functions definitions registered extension faithful observations runtimeViews program evidence uninitialized missing unique child thenTree)
    (fun child _ => builtin_preserves_at functions definitions registered extension faithful observations runtimeViews program evidence uninitialized missing unique child elseTree)

include definitions registered extension faithful observations runtimeViews uninitialized missing transport found conditionalForm conditionFound conditionType conditionTree thenTree elseTree in
theorem closed_conditional_reflects_at (budget size : Nat) (within : size ≤ budget) :
    HeadReflectsAt (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (solved := solved) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  exact conditional_reflects_at functions program evidence transport budget size within
    (fun child _ current valid => RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (CompatibleExpressionBuiltins.reflects functions extension faithful observations runtimeViews program evidence valid uninitialized missing)) child)
    found conditionalForm conditionFound conditionType conditionTree
    (fun child _ => builtin_reflects_at functions definitions registered extension faithful observations runtimeViews program evidence uninitialized missing child thenTree)
    (fun child _ => builtin_reflects_at functions definitions registered extension faithful observations runtimeViews program evidence uninitialized missing child elseTree)
end Concrete

private def content : String := String.intercalate "\n" [
  "function branch(flag: Bool) returns (Word) { let prior = 1; { let inside = 2; if (flag) { let selected = 3; return selected; } else { let selected = 4; return selected; } } let unreachable = 99; return unreachable; }",
  "function absent(flag: Bool) returns (Word) { let prior = 5; if (flag) { let selected = 6; } let after = 7; return after; }",
  "function shadow() returns (Word) { let value = 8; { let value = 9; } return value; }",
  "function conditionFault() returns (Word) { let prior = 10; let gap: Bool; if (gap) { let skipped = 98; } let skipped = 99; return skipped; }",
  "function thenFault(flag: Bool) returns (Word) { let prior = 11; if (flag) { let selected = 12; let gap: Word; return gap; } else { let unselected = 97; return unselected; } let skipped = 99; return skipped; }",
  "function elseFault(flag: Bool) returns (Word) { let prior = 13; if (flag) { let unselected = 97; return unselected; } else { let selected = 14; let gap: Word; return gap; } let skipped = 99; return skipped; }",
  "function sequenceFault() returns (Word) { let prior = 15; { let selected = 16; let gap: Word; gap; } let skipped = 99; return skipped; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"lexical control resume {name}" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"lexical control prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"lexical control ordered cells changed {label}: {reprStr final.heap}"
private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "lexical control fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "lexical control exact fault binder missing")

def run : IO Unit := do
  let names := ["branch", "absent", "shadow", "conditionFault", "thenFault", "elseFault", "sequenceFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named lexical control bounds" content names
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("branch", [.bool true], w 3, [(.bool, some (.bool true)), (.word, some (w 1)), (.word, some (w 2)), (.word, some (w 3))]),
    ("branch", [.bool false], w 4, [(.bool, some (.bool false)), (.word, some (w 1)), (.word, some (w 2)), (.word, some (w 4))]),
    ("absent", [.bool true], w 7, [(.bool, some (.bool true)), (.word, some (w 5)), (.word, some (w 6)), (.word, some (w 7))]),
    ("absent", [.bool false], w 7, [(.bool, some (.bool false)), (.word, some (w 5)), (.word, some (w 7))]),
    ("shadow", [], w 8, [(.word, some (w 8)), (.word, some (w 9))])]
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("conditionFault", [], [(.word, some (w 10)), (.bool, none)]),
    ("thenFault", [.bool true], [(.bool, some (.bool true)), (.word, some (w 11)), (.word, some (w 12)), (.word, none)]),
    ("elseFault", [.bool false], [(.bool, some (.bool false)), (.word, some (w 13)), (.word, some (w 14)), (.word, none)]),
    ("sequenceFault", [], [(.word, some (w 15)), (.word, some (w 16)), (.word, none)])]
  let complete ← successes.mapM fun test => finish compiled test.1 test.2.1 300000 initial
  let failed ← failures.mapM fun test => finish compiled test.1 test.2.1 300000 initial
  for fuel in [0, 31, 300000] do
    for (test, baseline) in successes.zip complete do
      let (name, arguments, expected, expectedCells) := test
      let observation ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"lexical control full resume observation changed {name}"
      match observation with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"lexical control result changed {name}"
        cells initial final expectedCells name
        SourceCoreUnifiedCorpusSupport.assertTrue (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"lexical control heap not deeply safe {name}"
      | other => throw (IO.userError s!"lexical control {name}: {reprStr other}")
    for (test, baseline) in failures.zip failed do
      let (name, arguments, expectedCells) := test
      let observation ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr observation == reprStr baseline)
        s!"lexical control full fault resume observation changed {name}"
      match observation with
      | .fault (.uninitializedLocal actual) final =>
        let expected ← faultBinder compiled name
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == expected) s!"lexical control first fault binder changed {name}"
        cells initial final expectedCells name
      | other => throw (IO.userError s!"lexical control fault {name}: {reprStr other}")
  IO.println "recursive named lexical control bounds: concrete builtin consumers, original finite children, three-way flow, scopes/branches/fault prefixes and public resume GREEN"
end Tests.SourceCoreRecursiveNamedLexicalControlBounds
