import Solcore.SourceSemantics.CoreLowering.NamedLoopStatements
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLoopContracts
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Fixed-budget while consumers keep the original source and Core size
witnesses. Concrete named expression and same-family body Trees discharge the
callback contracts here through their existing unrestricted laws. This does
not establish mutual recursive body meaning or generalize for/header/post. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedWhileBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
#check_failure SourceTypedRuntime.run

section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
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
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

variable {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {type : Ty} {conditionCode bodyCode : Expr} {selfReason : Word}

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- All condition and body runtime obligations are discharged by the concrete
named Trees. The actual native head type is retained as a separate static fact. -/
theorem concrete_whole_preserves {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (bodyTree : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (budget size : Nat) (bounded : size ≤ budget)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode bodyCode selfReason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedWhile.HeadPreservesAt functions program evidence
      (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      size id expected type (LocalLoop.whileLoop type conditionCode bodyCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ProtectedWhile.Body.while_preserves_bounded functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix) budget
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners) child)
    found form conditionFound conditionTree typed unique
    (fun child _ => ProtectedWhile.Body.preserves_at_of_unbounded functions program evidence
      (NamedLoopStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
        unique owners uninitialized missing bodyUninitialized bodyMissing bodyTree) child)
    size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Native completion reconstructs the independent source head and its effects.
Successful body control excludes faults by static Tree inversion, rather than
by a caller-supplied body execution or universal semantic contract. -/
theorem concrete_whole_reflects {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (bodyTree : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (budget size : Nat) (bounded : size ≤ budget)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode bodyCode selfReason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedWhile.HeadReflectsAt functions program evidence
      (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      size id expected type (LocalLoop.whileLoop type conditionCode bodyCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ProtectedWhile.Body.while_reflects_bounded functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix) budget
    (fun child _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing) child)
    found form conditionFound conditionTree typed
    (fun child _ => ProtectedWhile.Body.reflects_at_of_unbounded functions program evidence
      (NamedLoopStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
        unique owners uninitialized missing bodyUninitialized bodyMissing bodyTree) child)
    (fun trace => bodyTree.control_not_fault unique trace) size bounded
    valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

end Static

section ActualChildren
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before conditionHeap bodyHeap after : Dynamic.Heap} {condition : ExpressionId}
  {statements : List StatementId} {nextContext : SourceSemantics.Context} {nextEnvironment : Dynamic.Environment}
  {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}
  {c b n budget : Nat}

/-- A successful continuing prefix and a later failure each retain all actual
children; every callback uses the same fixed outer budget. -/
theorem next_fault_children
    (conditionTrace : SourceExecutionSize.ExpressionEvaluates program c context evidence source environment
      before condition (.bool true) conditionHeap)
    (bodyTrace : SourceExecutionSize.StatementsExecute program b context evidence source environment conditionHeap
      statements nextContext (.continuing nextEnvironment) bodyHeap)
    (nextTrace : SourceExecutionSize.WhileFaults program n context evidence source environment bodyHeap
      condition statements reason after)
    (bounded : SourceExecutionSize.stepSize [c, b, n] ≤ budget) :
    SourceExecutionSize.WhileFaults program (SourceExecutionSize.stepSize [c, b, n]) context evidence source environment
      before condition statements reason after ∧ c < budget ∧ b < budget ∧ n < budget :=
  ⟨.nextContinue conditionTrace bodyTrace nextTrace,
    Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded,
    Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded,
    Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded⟩

/-- The actual installed while envelope exposes the original inner condition
witness. Neither witness is regenerated from an agreement of continuations. -/
theorem native_condition_below {size budget : Nat} {environment : Environment} {store finalStore : Store}
    {type : Ty} {condition body : Expr} {selfReason : Word} {value : Value}
    (trace : EvaluationSize size environment store (LocalLoop.whileLoop type condition body selfReason) value finalStore)
    (bounded : size ≤ budget) :
    ∃ entrySize conditionSize conditionValue conditionStore,
      EvaluationSize entrySize
        (Core.LoopExecution.entryEnvironment type store.length environment)
        (TypedLexicalWhile.installedStore store type condition body (LocalLoop.fallthrough type) selfReason environment)
        (LocalLoop.loopBody type condition body (LocalLoop.fallthrough type) selfReason) value finalStore ∧
      EvaluationSize conditionSize
        (Core.LoopExecution.entryEnvironment type store.length environment)
        (TypedLexicalWhile.installedStore store type condition body (LocalLoop.fallthrough type) selfReason environment)
        (Core.LoopExecution.conditionCode condition) conditionValue conditionStore ∧
      conditionSize < entrySize ∧ entrySize < size ∧ conditionSize < budget := by
  obtain ⟨entrySize, smaller, entryTrace⟩ := trace.iterate_entry
  obtain ⟨conditionSize, conditionStore, conditionValue, conditionSmaller, conditionTrace⟩ := entryTrace.bind_computation
  exact ⟨entrySize, conditionSize, conditionValue, conditionStore, entryTrace, conditionTrace,
    conditionSmaller, smaller, Nat.lt_of_lt_of_le (Nat.lt_trans conditionSmaller smaller) bounded⟩
end ActualChildren

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function nested(raw: mapping(Word => Word)) returns (Word) { let index = 0; while (less(index, 5)) { index += next(0); if (less(index, 2)) { continue; } let inner = 0; while (less(inner, 3)) { inner += next(0); raw[next(0)] += next(0); if (less(1, inner)) { break; } } } return raw[next(0)] + index; }",
  "function early(raw: mapping(Word => Word)) returns (Word) { while (less(0, 1)) { raw[next(0)] += next(0); return raw[next(0)]; } return bad(0); }",
  "function failure(raw: mapping(Word => Word)) returns (Word) { let index = 0; while (less(index, 5)) { raw[next(0)] += next(0); index += next(0); if (less(1, index)) { bad(index); } } return raw[next(0)]; }"
]
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(word 1, word n), (word 1, word 91)]

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "fixed-budget guarded while" content ["nested", "early", "failure"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (word 819)⟩]}
  let badKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "bad"
  let bad ← SourceCoreUnifiedCorpusSupport.get "bounded while bad body" (SourceCompilationPlan.exactSpecialization compiled.validationPlan badKey)
  let gap ← match (SourceCoreDataPlaces.declaredBinders bad.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id | _ => throw (IO.userError "bounded while fault binder missing")
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated) in [("nested", some 23, 18), ("early", some 11, 11), ("failure", none, 12)] do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10] fuel initial
      let completed ← SourceCoreUnifiedCorpusSupport.get "bounded while resume" (started.resume 400000)
      let observation := completed.observation
      let final ← match observation, result with
        | .done actual final, some expected =>
          SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (word expected)) s!"bounded while result {name}"
          pure final
        | .fault (.uninitializedLocal id) final, none =>
          SourceCoreUnifiedCorpusSupport.assertTrue (id == gap) "bounded while exact first fault"
          pure final
        | other, _ => throw (IO.userError s!"bounded while unexpected {name}: {reprStr other}")
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "bounded while inert prefix"
      match final.heap[initial.heap.length]? with
      | some cell => SourceCoreUnifiedCorpusSupport.assertTrue (reprStr cell.value == reprStr (some (table updated))) s!"bounded while ordered mapping/write prefix {name}"
      | none => throw (IO.userError "bounded while mapping missing")
      current := current ++ [reprStr observation]
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "bounded while resumed observation"
  IO.println "recursive named while bounds: concrete sameTree callbacks, original source/native children, nested control/fault write prefixes, duplicate order and resume GREEN"

end Tests.SourceCoreRecursiveNamedWhileBounds
