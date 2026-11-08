import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForIterations
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedFunctionLoops
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeFor
import Solcore.Test.SourceSemantics.CoreLowering.Recursive.NamedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeControl
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.WhileLoops
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalStatements
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogExpressions

/-!
# Recursive named statement tests

Recursive named `for`, `while`, imperative, lexical and protected statements.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedForBounds
/-! Fixed-budget for endpoints use the original independent source and Core
size witnesses. Concrete named condition/body Trees and direct empty-post
proofs close the callbacks below; no recursive catalog theorem is claimed.
General graded Header/Post/assignment and mutual callee closure remain later
units. Cached execution separately checks the actual for phase ordering. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedForBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open CallableAncestryPairedLookup (Checked Base)
section Post
variable {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) (program : SourceSemantics.Program)
  (evidence : Dynamic.EvidenceEnvironment) {entry : ProtectedExpressionMeaning.Entry}
  {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
  {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
  {faults : FunctionCalls.FaultRep}

private theorem empty_post_evaluates (continued : Bool) (store : Store) :
    Evaluates (TypedImperativeFor.postValues type location continued ++ actual) store
      (ForLoop.postCode ((LocalLoop.fallthrough type).rename ξ)) (LocalLoop.fallthroughValue type) store := by
  have shape : ForLoop.postCode ((LocalLoop.fallthrough type).rename ξ) = LocalLoop.fallthrough type := by
    simp only [ForLoop.postCode, Core.LoopExecution.conditionCode, ← Expr.rename_insertion, LoopRenaming.fallthrough]
  rw [shape]
  exact LocalLoop.fallthrough_evaluates _ _ _

theorem empty_post_preserves_at (size : Nat) : RecursiveNamedForContracts.PostPreservesAt size functions program evidence
    (entry := entry) (registry := registry) (source := source) (context := context) (scope := scope)
    (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
    (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
    (contextLocation := contextLocation) (location := location) (type := type)
    (conditionCode := conditionCode) (body := body) (selfReason := selfReason) [] (LocalLoop.fallthrough type) := by
  intro mapping world before after store finalContext finalEnvironment state continued trace
  cases trace
  exact ⟨store, mapping, world, empty_post_evaluates continued store,
    state.1.heaps, .refl _, .refl _, .refl _ _, .refl _⟩

theorem empty_post_faults_at (size : Nat) : RecursiveNamedForContracts.PostFaultsAt size functions program evidence
    (entry := entry) (registry := registry) (source := source) (context := context) (scope := scope)
    (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
    (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
    (contextLocation := contextLocation) (location := location) (type := type)
    (conditionCode := conditionCode) (body := body) (selfReason := selfReason) (faults := faults) [] (LocalLoop.fallthrough type) := by
  intro mapping world before after store finalContext reason state continued trace
  cases trace

theorem empty_post_reflects_at (size : Nat) : RecursiveNamedForContracts.PostReflectsAt size functions program evidence
    (entry := entry) (registry := registry) (source := source) (context := context) (scope := scope)
    (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
    (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
    (contextLocation := contextLocation) (location := location) (type := type)
    (conditionCode := conditionCode) (body := body) (selfReason := selfReason) faults [] (LocalLoop.fallthrough type) := by
  intro mapping world before store finalStore value state continued evaluated
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (empty_post_evaluates continued store)
  exact .inl ⟨_, context, environment, before, mapping, world, .nil, rfl,
    state.1.heaps, .refl _, .refl _, .refl _ _, .refl _⟩
end Post

section Concrete
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

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_empty_post_preserves {context : SourceSemantics.Context} {scope : Scope}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {reason : Word} {administrative : Core.Context}
    (budget size : Nat) (bounded : size ≤ budget)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code (LocalLoop.fallthrough type) reason) (LocalLoop.resultType type) ambient.definitions) :
    RecursiveNamedForContracts.LoopPreservesAt functions program evidence size
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      condition [] statements expected type (LocalLoop.iterate type conditionCode code (LocalLoop.fallthrough type) reason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ProtectedFor.Body.loop_preserves_bounded functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix) budget
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners) child)
    conditionFound conditionTree nativeTyped unique
    (fun child _ => ProtectedWhile.Body.preserves_at_of_unbounded functions program evidence
      (NamedLoopStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
        unique owners uninitialized missing bodyUninitialized bodyMissing body) child)
    (fun _ _ _ child _ => empty_post_preserves_at functions program evidence child)
    (fun _ _ _ child _ => empty_post_faults_at functions program evidence child)
    size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_empty_post_reflects {context : SourceSemantics.Context} {scope : Scope}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {reason : Word} {administrative : Core.Context}
    (budget size : Nat) (bounded : size ≤ budget)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code (LocalLoop.fallthrough type) reason) (LocalLoop.resultType type) ambient.definitions) :
    RecursiveNamedForContracts.LoopReflectsAt functions program evidence size
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      condition [] statements expected type (LocalLoop.iterate type conditionCode code (LocalLoop.fallthrough type) reason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ProtectedFor.Body.loop_reflects_bounded functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix) budget
    (fun child _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing) child)
    conditionFound conditionTree nativeTyped
    (fun child _ => ProtectedWhile.Body.reflects_at_of_unbounded functions program evidence
      (NamedLoopStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
        unique owners uninitialized missing bodyUninitialized bodyMissing body) child)
    (fun executed => body.control_not_fault unique executed)
    (fun _ _ _ child _ => empty_post_reflects_at functions program evidence child)
    size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
end Concrete

section ActualChildren
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before conditionHeap bodyHeap postHeap after : Dynamic.Heap} {condition : ExpressionId}
  {post : List ForItemForm} {statements : List StatementId}
  {bodyContext postContext : SourceSemantics.Context} {bodyEnvironment postEnvironment : Dynamic.Environment}
  {reason : Dynamic.SemanticFault} {c b p n budget : Nat}

/-- A later failure retains condition, body, and post success in their actual
order. All four costs are strictly below one fixed outer budget. -/
theorem next_fault_children
    (conditionTrace : SourceExecutionSize.ExpressionEvaluates program c context evidence source environment
      before condition (.bool true) conditionHeap)
    (bodyTrace : SourceExecutionSize.StatementsExecute program b context evidence source environment conditionHeap
      statements bodyContext (.continuing bodyEnvironment) bodyHeap)
    (postTrace : SourceExecutionSize.ForItemsExecute program p context evidence source environment bodyHeap
      post postContext postEnvironment postHeap)
    (nextTrace : SourceExecutionSize.ForLoopFaults program n context evidence source environment postHeap
      condition post statements reason after)
    (bounded : SourceExecutionSize.stepSize [c, b, p, n] ≤ budget) :
    SourceExecutionSize.ForLoopFaults program (SourceExecutionSize.stepSize [c, b, p, n]) context evidence source environment
      before condition post statements reason after ∧ c < budget ∧ b < budget ∧ p < budget ∧ n < budget :=
  ⟨.nextContinue conditionTrace bodyTrace postTrace nextTrace,
    Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded,
    Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded,
    Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded,
    Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded⟩

/-- Break constructs its result from the condition and body alone. -/
theorem break_children
    (conditionTrace : SourceExecutionSize.ExpressionEvaluates program c context evidence source environment
      before condition (.bool true) conditionHeap)
    (bodyTrace : SourceExecutionSize.StatementsExecute program b context evidence source environment conditionHeap
      statements bodyContext (.breaking bodyEnvironment) after) :
    SourceExecutionSize.ForLoopExecutes program (SourceExecutionSize.stepSize [c, b]) context evidence source environment
      before condition post statements context (.fallthrough environment) after :=
  .breaks conditionTrace bodyTrace

/-- The native for envelope retains its original inner condition derivation. -/
theorem native_condition_below {size budget : Nat} {environment : Environment} {store finalStore : Store}
    {type : Ty} {condition body post : Expr} {selfReason : Word} {value : Value}
    (trace : EvaluationSize size environment store (LocalLoop.iterate type condition body post selfReason) value finalStore)
    (bounded : size ≤ budget) :
    ∃ entrySize conditionSize conditionValue conditionStore,
      EvaluationSize entrySize
        (Core.LoopExecution.entryEnvironment type store.length environment)
        (TypedLexicalWhile.installedStore store type condition body post selfReason environment)
        (LocalLoop.loopBody type condition body post selfReason) value finalStore ∧
      EvaluationSize conditionSize
        (Core.LoopExecution.entryEnvironment type store.length environment)
        (TypedLexicalWhile.installedStore store type condition body post selfReason environment)
        (Core.LoopExecution.conditionCode condition) conditionValue conditionStore ∧
      conditionSize < entrySize ∧ entrySize < size ∧ conditionSize < budget := by
  obtain ⟨entrySize, smaller, entryTrace⟩ := trace.iterate_entry
  obtain ⟨conditionSize, conditionStore, conditionValue, conditionSmaller, conditionTrace⟩ := entryTrace.bind_computation
  exact ⟨entrySize, conditionSize, conditionValue, conditionStore, entryTrace, conditionTrace,
    conditionSmaller, smaller, Nat.lt_of_lt_of_le (Nat.lt_trans conditionSmaller smaller) bounded⟩

/-- Post is extracted from the same body-branch witness under the actual six
slots, retaining its strict cost rather than regenerating a completion. -/
theorem native_post_below {size budget : Nat} {actual : Environment} {before bodyStore after : Store}
    {type : Ty} {location : Location} {body post : Expr} {selfReason : Word} {value : Value}
    (continued : Bool)
    (trace : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) before
      (LocalLoop.advance type (Core.LoopExecution.bodyCode body)
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) selfReason)).weakenAt 0)) value after)
    (bodyTrace : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) before
      (Core.LoopExecution.bodyCode body)
      (if continued then LocalLoop.continuingValue type else LocalLoop.fallthroughValue type) bodyStore)
    (bounded : size ≤ budget) :
    ∃ postSize postStore postValue, postSize < budget ∧
      EvaluationSize postSize (TypedImperativeFor.postValues type location continued ++ actual) bodyStore
        (ForLoop.postCode post) postValue postStore := by
  obtain ⟨postSize, postStore, postValue, smaller, postTrace⟩ :=
    RecursiveNamedForContracts.post_computation_size continued trace bodyTrace
  exact ⟨postSize, postStore, postValue, Nat.lt_of_lt_of_le smaller bounded, postTrace⟩
end ActualChildren

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function copied(value: Word) returns (Word) { let local = value; return local; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function stopOrFail(value: Word) returns (Bool) { if (value < 3) { return true; } let gap: Word; return gap == value; }",
  "function transfers(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; less(index, 4); index += next(0)) { raw[next(0)] += copied(1); if (less(index, 2)) { continue; } raw[next(0)] += copied(1); } return copied(index + raw[next(0)]); }",
  "function breaks(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; less(index, 4); raw[next(0)] += copied(10), index += next(0)) { raw[next(0)] += copied(1); break; } return copied(index + raw[next(0)]); }",
  "function early(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; true; raw[next(0)] += copied(10), index += next(0)) { raw[next(0)] += copied(2); return copied(raw[next(0)]); } return copied(99); }",
  "function zero(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; false; raw[next(0)] += bad(seed)) { bad(seed); } return copied(raw[next(0)]); }",
  "function nested(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; less(index, 2); index += next(0)) { let inner = 0; while (less(inner, 3)) { inner += next(0); if (less(inner, 2)) { continue; } raw[next(0)] += copied(1); break; } for (let local = 0; less(local, 2); local += next(0)) { if (less(local, 1)) { continue; } raw[next(0)] += copied(1); } } return copied(index + raw[next(0)]); }",
  "function bodyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; true; raw[next(0)] += copied(9), index += next(0)) { raw[next(0)] += copied(2); bad(seed); } return copied(99); }",
  "function postFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; true; raw[next(0)] += copied(3), let failed = bad(seed), index += next(0)) { raw[next(0)] += copied(2); continue; } return copied(99); }",
  "function conditionFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; stopOrFail(index); index += next(0)) { raw[next(0)] += copied(2); } return copied(99); }",
  "function initializerFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (raw[next(0)] += copied(3), let failed = bad(seed); true; ) { raw[next(0)] += copied(99); } return copied(99); }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10, wordValue 7] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"fixed-budget guarded for resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "fixed-budget guarded for fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "fixed-budget guarded for exact fault binder missing")

/-- Cells after the inert prefix: `raw`, `seed`, the snapshot of `seed` and
`raw` that `saved` takes when it is created, `saved` and `index`. -/
private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"fixed-budget guarded for inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "fixed-budget guarded for missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"fixed-budget guarded for raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 5]? with
    | some cell => pure cell | none => throw (IO.userError "fixed-budget guarded for missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"fixed-budget guarded for writes changed {name}"
  let snapshot := ((final.heap.drop (initial.heap.length + 2)).take 2).map (·.value)
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr snapshot == reprStr [some (wordValue 7), some (table 10)])
    s!"fixed-budget guarded for captured snapshot values changed {name}"
  match final.heap[initial.heap.length + 4]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"fixed-budget guarded for captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 2, initial.heap.length + 3])
      s!"fixed-budget guarded for captured snapshot locations changed {name}"
  | other => throw (IO.userError s!"fixed-budget guarded for lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "fixed-budget guarded for" content
    ["transfers", "breaks", "early", "zero", "nested", "bodyFault", "postFault", "conditionFault", "initializerFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled "bad"
  let conditionGap ← gapBinder compiled "stopOrFail"
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated, counter) in [("transfers",20,16,4), ("breaks",11,11,0), ("early",12,12,0), ("zero",10,10,0), ("nested",16,14,2)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"fixed-budget guarded for result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"fixed-budget guarded for success {name}: {reprStr other}")
    for (name, exactGap, updated, counter) in [("bodyFault",gap,12,0), ("postFault",gap,15,0),
        ("conditionFault",conditionGap,16,3), ("initializerFault",gap,13,0)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == exactGap) s!"fixed-budget guarded for exact fault {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"fixed-budget guarded for failure {name}: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "fixed-budget guarded for resume changed observations"
  IO.println "fixed-budget guarded for: original source/native size, fixed-budget condition/body/post, shared finite for proof, nested for/while, break skips post, continue runs post, initializer/condition/body/post first faults, raw duplicate/capture snapshots and resume GREEN"

end Tests.SourceCoreRecursiveNamedForBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedImperativeForBounds
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedImperativeMatchBounds
/-! The existing Match Tree consumes bounded expression laws at one budget,
including nested match children and loops. The concrete expression Tree and finite builtin callee close those
laws here; no child/body execution is a field of the static receipt. Source
and native costs are independent, and the preservation endpoint includes N. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedImperativeMatchBounds
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
  (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))


include definitions registered extension faithful observations runtimeViews catalogValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_preserves (budget : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (ready : GenericImperativeMatch.Tree.ReachableReady registry faults tree) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size => RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  apply RecursiveNamedImperativeFor.preservesAt_match functions definitions registered extension program evidence
    entry_transport entry_binds budget faithful observations ?_ .reachable unique tree (GenericImperativeMatch.Tree.CatalogSites.of_catalog catalogValid ready)
  intro context valid child within
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_preserves_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid unique owners uninitialized missing budget child within

include definitions registered extension faithful observations runtimeViews catalogValid unique uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_reflects (budget : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (ready : GenericImperativeMatch.Tree.ReachableReady registry faults tree) :
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  apply RecursiveNamedImperativeFor.reflectsAt_match functions definitions registered extension program evidence
    entry_transport entry_binds budget ?_ faithful observations .reachable runtimeViews unique tree (GenericImperativeMatch.Tree.CatalogSites.of_catalog catalogValid ready)
  intro context valid child smaller
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_reflects_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid uninitialized missing budget child (Nat.le_of_lt smaller)

include definitions registered extension faithful observations runtimeViews catalogValid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The inclusive endpoint used by a source-body strong induction. No N+1
budget and no callee law at N is supplied by this consumer. -/
theorem concrete_preserves_at_top (size : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (ready : GenericImperativeMatch.Tree.ReachableReady registry faults tree) :
    RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code :=
  concrete_preserves functions definitions registered extension faithful observations runtimeViews evidence catalogValid unique owners
    uninitialized missing bodyUninitialized bodyMissing size tree ready size (Nat.le_refl size)

include definitions registered extension faithful observations runtimeViews catalogValid unique uninitialized missing bodyUninitialized bodyMissing in
/-- A completed native body gives its own source size, without relating source
cost to the original native budget. -/
theorem concrete_native_only (budget size : Nat) (smaller : size < budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (ready : GenericImperativeMatch.Tree.ReachableReady registry faults tree) :
    RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code :=
  concrete_reflects functions definitions registered extension faithful observations runtimeViews evidence catalogValid unique
    uninitialized missing bodyUninitialized bodyMissing budget tree ready size smaller
end Concrete




/-- For inclusion supplies the static site evidence without any catalog premise. -/
abbrev for_without_catalog := @GenericImperativeMatch.Tree.CatalogSites.of_for

/-- The same ordinary root context reconstructs readiness at every actual site. -/
abbrev same_ready := @GenericImperativeMatch.Tree.CatalogSites.ready

private def content : String := String.intercalate "\n" [
  "function mark(value: Word) returns (Word) { let seen = value; return seen; }",
  "function fail(value: Word) returns (Word) { let seen = value; let gap: Word; return gap; }",
  "function nested(seed: Word) returns (Word) { let sum = 0; for (let i = 0; i < 2; i += 1) { match ((i, mark(seed))) { case (0, value) { sum += value; continue; } default { while (true) { match (i) { case 1 { sum += mark(3); break; } default { sum += 99; break; } } } } } } return sum; }",
  "function terminal(seed: Word) returns (Word) { for (; true; let dead = fail(99)) { match (seed) { case 0 { return mark(5); } default { return mark(7); } } } return 99; }",
  "function selectedFault(seed: Word) returns (Word) { match (seed) { case 0 { let prior = mark(11); return fail(prior); } default { return mark(13); } } }",
  "function scrutineeFault() returns (Word) { let prior = mark(17); match (fail(prior)) { case 0 { return 0; } default { return 1; } } }",
  "function duplicate(raw: mapping(Word => Word)) returns (Word) { match (mark(0)) { case 0 { raw[mark(1)] += mark(2); } default { raw[1] += 99; } } return raw[1]; }",
  "function armShadow(seed: Word) returns (Word) { let kept = seed; match ((0, kept)) { case (0, kept) { let local = mark(kept + 1); } default {} } return kept; }"
]
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cell (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (word n))
private def pair (a b : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value :=
  (.product .word .word, some (.product (word a) (word b)))
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(word 1, word n), (word 1, word 91)]
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "whole match public resume" (first.resume 600000)).observation

/-- Actual nested match/loop code exercises both ordinary and terminal paths.
The expected complete heap records every call, hidden scrutinee and arm binder. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive whole match bounds" content
    ["nested", "terminal", "selectedFault", "scrutineeFault", "duplicate", "armShadow"]
  let failKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let failed ← get "whole match actual failing specialization" (SourceCompilationPlan.exactSpecialization compiled.validationPlan failKey)
  let gap ← match (SourceCoreDataPlaces.declaredBinders failed.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "whole match gap is not unique")
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (word 907)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × Nat × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("nested", [word 5], 8, [cell 5, cell 8, cell 2, cell 5, cell 5, pair 0 5, cell 5, cell 5, cell 5, pair 1 5, cell 1, cell 3, cell 3]),
    ("terminal", [word 0], 5, [cell 0, cell 0, cell 5, cell 5]),
    ("terminal", [word 1], 7, [cell 1, cell 1, cell 7, cell 7]),
    ("selectedFault", [word 1], 13, [cell 1, cell 1, cell 13, cell 13]),
    ("duplicate", [table 10], 12, [(.mapping .word .word, some (table 12)), cell 0, cell 0, cell 0, cell 1, cell 1, cell 2, cell 2]),
    ("armShadow", [word 4], 4, [cell 4, cell 4, pair 0 4, cell 4, cell 5, cell 5, cell 5])]
  for (name, arguments, expected, cells) in successes do
    let baseline ← finish compiled name arguments 600000 initial
    for fuel in [0, 19, 113, 600000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"whole match resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr (word expected)) s!"whole match result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"whole match ordered cells changed {name}: {reprStr final.heap}"
      | other => throw (IO.userError s!"whole match expected success {name}: {reprStr other}")
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("selectedFault", [word 0], [cell 0, cell 0, cell 11, cell 11, cell 11, cell 11, cell 11, (.word, none)]),
    ("scrutineeFault", [], [cell 17, cell 17, cell 17, cell 17, cell 17, (.word, none)])]
  for (name, arguments, cells) in failures do
    let baseline ← finish compiled name arguments 600000 initial
    for fuel in [0, 19, 113, 600000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"whole match fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal id) final =>
        require (id == gap) "whole match lost the actual first callee fault"
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"whole match fault cells changed {name}: {reprStr final.heap}"
      | other => throw (IO.userError s!"whole match expected fault {name}: {reprStr other}")
  IO.println "recursive named imperative match bounds: same Tree, nested match/for/while, selected Entry, terminal post skip, raw duplicate mapping, exact faults/cells and public resume GREEN"

end Tests.SourceCoreRecursiveNamedImperativeMatchBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedLexicalControlBounds
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedLexicalTreeBounds
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedProtectedHeaderBounds
/-! Same guarded header Tree under one fixed outer budget. Concrete named
children close all expression callbacks. Native continuations retain their
original size, including equality for an empty header; post scopes restore
outer observations while retaining allocated cells and fault effects. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedProtectedHeaderBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open CallableAncestryPairedLookup (Checked Base)
open CallableIndexedHistory (NativeFrame)
section Concrete
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

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem named_prefix_preserves (budget : Nat) {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop} {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)) ambient.definitions administrative type continuation
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
    (size : Nat) (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : ProtectedForHeader.Tail (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  exact ProtectedForHeader.Tree.preserves_prefix_bounded functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    faithful observations budget
    (fun current currentValid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget)
    tree valid environments heaps locals agrees actualTyped reference read unmapped installed trace bounded

include definitions registered extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
theorem named_prefix_reflects (budget : Nat) {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop}
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)) ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
    (size : Nat) (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    RecursiveNamedHeaderContracts.ResultAt size (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  exact ProtectedForHeader.Tree.reflects_reachable_bounded functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    faithful observations budget
    (fun current currentValid => RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence currentValid
        uninitialized missing bodyUninitialized bodyMissing) budget)
    runtimeViews tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated bounded

variable {administrative : Core.Context} {type : Ty} {context : SourceSemantics.Context} {scope : Scope}
  {post : List ForItemForm} {postCode : Expr}
  (postTree : ProtectedForHeader.Tree layouts owner active frame globals onError values source
    (fun context => NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
    ambient.definitions administrative type (TypedForHeader.Fallthrough type) context scope post postCode)
  (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {conditionCode bodyCode : Expr} {selfReason : Word}
  (agrees : EnvironmentsAgree ξ canonical actual)
  (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing postTree valid agrees reference in
theorem named_post_preserves (budget : Nat) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size =>
      RecursiveNamedForContracts.PostPreservesAt size functions program evidence
        (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
        (source := source) (registry := registry) (administrative := administrative) (actualContext := actualContext) (frameLayout := frame)
        (context := context) (scope := scope) (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode) (body := bodyCode) (selfReason := selfReason) post postCode) := by
  intro size bounded mapping world before after store finalContext finalEnvironment state continued executed
  exact ProtectedForHeader.post_preserves_bounded functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    faithful observations budget
    (fun current currentValid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget)
    postTree valid agrees reference state continued executed bounded

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing postTree postErrors valid agrees reference in
theorem named_post_faults (budget : Nat) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size =>
      RecursiveNamedForContracts.PostFaultsAt size functions program evidence
        (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix) (faults := faults)
        (source := source) (registry := registry) (administrative := administrative) (actualContext := actualContext) (frameLayout := frame)
        (context := context) (scope := scope) (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode) (body := bodyCode) (selfReason := selfReason) post postCode) := by
  intro size bounded mapping world before after store finalContext reason state continued executed
  exact ProtectedForHeader.post_fault_reachable_bounded functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    faithful observations budget
    (fun current currentValid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
        uninitialized missing bodyUninitialized bodyMissing unique owners) budget)
    postTree postErrors valid agrees reference state continued executed bounded

include definitions registered extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing postTree postErrors valid agrees reference in
theorem named_post_reflects (budget : Nat) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size =>
      RecursiveNamedForContracts.PostReflectsAt size functions program evidence
        (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
        (source := source) (registry := registry) (administrative := administrative) (actualContext := actualContext) (frameLayout := frame)
        (context := context) (scope := scope) (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode) (body := bodyCode) (selfReason := selfReason) faults post postCode) := by
  intro size bounded mapping world before store finalStore value state continued executed
  exact ProtectedForHeader.post_reflects_reachable_bounded functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    faithful observations budget
    (fun current currentValid => RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence currentValid
        uninitialized missing bodyUninitialized bodyMissing) budget)
    runtimeViews postTree postErrors valid agrees reference state continued executed bounded
end Concrete

section Continuation
variable {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {program : SourceSemantics.Program}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {solved : List SolvedRequirement}
  {administrative : Core.Context} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {registry : SourceCoreRawMetadata.Registry} {type : Core.Ty} {faults : FunctionCalls.FaultRep}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
  {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {contextLocation : Location} {native : NativeFrame} {value : Core.Value} {finalStore : Store}
  {items : List ForItemForm} {size budget : Nat}
  {meaning : Nat → SourceSemantics.Context → Scope → Expr → Prop}

/-- Initializers select the continuation at its original inclusive native
size; the independently reconstructed source prefix is never bounded by it. -/
theorem continuation_at_remaining
    (receipt : RecursiveNamedHeaderContracts.ResultAt size (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults
      (RecursiveNamedHeaderContracts.ContinuationWithin budget meaning) context environment heap items mapping world store value finalStore)
    (bounded : size ≤ budget) :
    (∃ sourceSize finalContext reason after,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment heap items finalContext reason after) ∨
    (∃ sourceSize finalContext finalEnvironment after,
      ∃ tail : ProtectedForHeader.Tail (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native
        (RecursiveNamedHeaderContracts.ContinuationWithin budget meaning) finalContext finalEnvironment after,
      ∃ remainingSize, SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment heap items finalContext finalEnvironment after ∧
      remainingSize ≤ size ∧ remainingSize ≤ budget ∧
      EvaluationSize remainingSize tail.actual tail.store (tail.code.rename tail.embedding) value finalStore ∧
      meaning remainingSize finalContext tail.scope tail.code ∧ entry tail.scope tail.mapping tail.world after tail.store tail.canonical) := by
  cases receipt with
  | fault trace _ _ _ _ _ _ _ => exact .inl ⟨_, _, _, _, trace⟩
  | continues tail trace _ _ _ _ remaining smaller =>
    exact .inr ⟨_, _, _, _, tail, _, trace, smaller, Nat.le_trans smaller bounded, remaining,
      RecursiveNamedHeaderContracts.tail_at_remaining tail smaller bounded, tail.installed⟩

/-- An empty initializer keeps the exact same native witness and inclusive
bound. A strict-only continuation family would exclude this case. -/
theorem empty_continuation
    (tail : ProtectedForHeader.Tail (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native
      (RecursiveNamedHeaderContracts.ContinuationWithin size meaning) context environment heap)
    (evaluated : EvaluationSize size tail.actual tail.store (tail.code.rename tail.embedding) value finalStore) :
    RecursiveNamedHeaderContracts.ResultAt size (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults
      (RecursiveNamedHeaderContracts.ContinuationWithin size meaning) context environment heap [] tail.mapping tail.world tail.store value finalStore ∧
    meaning size context tail.scope tail.code ∧ ¬ size < size :=
  ⟨.nil tail evaluated, RecursiveNamedHeaderContracts.tail_at_remaining tail (Nat.le_refl _) (Nat.le_refl _), Nat.lt_irrefl _⟩
end Continuation

private def content : String := String.intercalate "\n" [
  "function mark(value: Word) returns (Word) { let copied = value; return copied; }",
  "function fail(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function empty(raw: mapping(Word => Word), seed: Word) returns (Word) { for (; false;) { raw[seed] = 999; } return seed + raw[seed]; }",
  "function mixed(raw: mapping(Word => Word), seed: Word) returns (Word) { let current = seed; for (let index: Word, index = mark(0), raw[mark(seed)] += mark(1); index < 2; let current = mark(index), current += mark(1), raw[mark(seed)] += mark(current), index += mark(1)) { continue; } return current + raw[seed]; }",
  "function stopped(raw: mapping(Word => Word), seed: Word) returns (Word) { for (raw[mark(seed)] += mark(1); true; raw[mark(seed)] = fail(seed)) { break; } return raw[seed]; }",
  "function headerFault(raw: mapping(Word => Word), seed: Word) returns (Word) { for (raw[mark(seed)] += mark(1), let stop = fail(seed), raw[seed] = 999; true;) {} return raw[seed]; }",
  "function postFault(raw: mapping(Word => Word), seed: Word) returns (Word) { for (let index = 0; index < 2; raw[mark(seed)] += mark(1), let copy = fail(index), index += mark(1)) { raw[mark(seed)] += mark(2); } return raw[seed]; }",
  "function operandFault(raw: mapping(Word => Word), seed: Word) returns (Word) { for (let absent: Word, absent += mark(seed), raw[seed] = 999; true;) {} return raw[seed]; }"
]
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(word 7, word n), (word 7, word 91)]
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (word n))

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "bounded protected header/post" content
    ["empty", "mixed", "stopped", "headerFault", "postFault", "operandFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (word 819)⟩]}
  let badKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let bad ← SourceCoreUnifiedCorpusSupport.get "bounded header fault body" (SourceCompilationPlan.exactSpecialization compiled.validationPlan badKey)
  let gap ← match (SourceCoreDataPlaces.declaredBinders bad.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id | _ => throw (IO.userError "bounded header exact fault binder missing")
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated) in [("empty", some 44, 37), ("mixed", some 48, 41), ("stopped", some 38, 38),
        ("headerFault", none, 38), ("postFault", none, 40), ("operandFault", none, 37)] do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 37, word 7] fuel initial
      let completed ← SourceCoreUnifiedCorpusSupport.get "bounded protected header resume" (started.resume 400000)
      let observation := completed.observation
      let final ← match observation, result with
        | .done actual final, some expected =>
          SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (word expected)) s!"bounded header result {name}"
          pure final
        | .fault (.uninitializedLocal id) final, none =>
          SourceCoreUnifiedCorpusSupport.assertTrue (id == gap && (name == "headerFault" || name == "postFault")) "bounded header exact first fault"
          pure final
        | .fault (.invalidAssignmentOperands operator left right) final, none =>
          SourceCoreUnifiedCorpusSupport.assertTrue (name == "operandFault" && operator == .add && left == none && right == some .word) "bounded header operand fault"
          pure final
        | other, _ => throw (IO.userError s!"bounded header unexpected {name}: {reprStr other}")
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "bounded header inert prefix"
      match final.heap[initial.heap.length]? with
      | some cell => SourceCoreUnifiedCorpusSupport.assertTrue (reprStr cell.value == reprStr (some (table updated))) s!"bounded header ordered mapping/fault prefix {name}"
      | none => throw (IO.userError "bounded header mapping missing")
      let words : List (TypeSystem.Ty × Option SourceTypedRuntime.Value) := match name with
        | "empty" => [7].map present
        | "mixed" =>
          ([7,7,2] ++ [0,0,7,7,1,1] ++ [0,0,1,1,1,7,7,1,1,1,1] ++ [1,1,2,1,1,7,7,2,2,1,1]).map present
        | "stopped" => [7,7,7,1,1].map present
        | "headerFault" => [7,7,7,1,1,7].map present ++ [(.word, none)]
        | "postFault" => [7,0,7,7,2,2,7,7,1,1,0].map present ++ [(.word, none)]
        | _ => [present 7, (.word, none), present 7, present 7]
      let expected := (.mapping .word .word, some (table updated)) :: words
      SourceCoreUnifiedCorpusSupport.assertTrue
        (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
        s!"bounded header every ordered cell {name}: {reprStr final.heap}"
      current := current ++ [reprStr observation]
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "bounded protected header resume changed observations"
  IO.println "bounded protected header/post: same Tree, named child closure, inclusive empty continuation, independent source/native bounds, shadowed post-local restoration, first faults, ordered mapping duplicates and resume GREEN"

end Tests.SourceCoreRecursiveNamedProtectedHeaderBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedForHeaderRuntimeBounds
/-! Runtime header conditions retain the entire ledger and the actual covering
entry. Concrete builtin certificates close expression meaning at every reached
child. Source costs and original native continuation costs remain independent.
The Header catalog and whole named profile are not weakened by this unit. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedForHeaderRuntimeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open CallableIndexedHistory (NativeFrame)
section Concrete
variable {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include definitions registered extension faithful observations runtimeViews unique uninitialized missing transport bindings in
theorem runtime_prefix_preserves (budget : Nat) {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop} {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => (CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)) ambient.definitions administrative type continuation
      context scope items code)
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (size : Nat) (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : ProtectedForHeader.TailFor (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  exact ProtectedForHeader.Tree.preserves_prefix_bounded_for functions definitions registered extension program evidence
    transport
    bindings
    faithful observations
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget
    (fun current currentValid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations runtimeViews
          program evidence currentValid.ledger currentValid.runtime unique uninitialized missing)) budget)
    tree valid environments heaps locals agrees actualTyped reference read unmapped installed trace bounded

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
theorem runtime_prefix_reflects (budget : Nat) {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop}
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => (CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)) ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : entry scope mapping world before store canonical)
    (size : Nat) (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    RecursiveNamedHeaderContracts.ResultAtFor (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) size (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  exact ProtectedForHeader.Tree.reflects_reachable_bounded_for functions definitions registered extension program evidence
    transport
    bindings
    faithful observations
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget
    (fun current currentValid => RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations runtimeViews
          program evidence currentValid.ledger currentValid.runtime uninitialized missing)) budget)
    runtimeViews tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated bounded

variable {administrative : Core.Context} {type : Ty} {context : SourceSemantics.Context} {scope : Scope}
  {post : List ForItemForm} {postCode : Expr}
  (postTree : ProtectedForHeader.Tree layouts owner active frame globals onError values source
    (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
    ambient.definitions administrative type (TypedForHeader.Fallthrough type) context scope post postCode)
  (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {conditionCode bodyCode : Expr} {selfReason : Word}
  (agrees : EnvironmentsAgree ξ canonical actual)
  (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))

include definitions registered extension faithful observations runtimeViews unique uninitialized missing transport bindings postTree valid agrees reference in
theorem runtime_post_preserves (budget : Nat) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size =>
      RecursiveNamedForContracts.PostPreservesAt size functions program evidence
        (entry := entry)
        (source := source) (registry := registry) (administrative := administrative) (actualContext := actualContext) (frameLayout := frame)
        (context := context) (scope := scope) (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode) (body := bodyCode) (selfReason := selfReason) post postCode) := by
  intro size bounded mapping world before after store finalContext finalEnvironment state continued executed
  exact ProtectedForHeader.post_preserves_bounded_for (solved := solved) functions definitions registered extension program evidence
    transport
    bindings
    faithful observations
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget
    (fun current currentValid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations runtimeViews
          program evidence currentValid.ledger currentValid.runtime unique uninitialized missing)) budget)
    postTree valid agrees reference state continued executed bounded

include definitions registered extension faithful observations runtimeViews unique uninitialized missing transport bindings postTree postErrors valid agrees reference in
theorem runtime_post_faults (budget : Nat) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size =>
      RecursiveNamedForContracts.PostFaultsAt size functions program evidence
        (entry := entry) (faults := faults)
        (source := source) (registry := registry) (administrative := administrative) (actualContext := actualContext) (frameLayout := frame)
        (context := context) (scope := scope) (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode) (body := bodyCode) (selfReason := selfReason) post postCode) := by
  intro size bounded mapping world before after store finalContext reason state continued executed
  exact ProtectedForHeader.post_fault_reachable_bounded_for functions definitions registered extension program evidence
    transport
    bindings
    faithful observations
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget
    (fun current currentValid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations runtimeViews
          program evidence currentValid.ledger currentValid.runtime unique uninitialized missing)) budget)
    postTree postErrors valid agrees reference state continued executed bounded

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings postTree postErrors valid agrees reference in
theorem runtime_post_reflects (budget : Nat) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size =>
      RecursiveNamedForContracts.PostReflectsAt size functions program evidence
        (entry := entry)
        (source := source) (registry := registry) (administrative := administrative) (actualContext := actualContext) (frameLayout := frame)
        (context := context) (scope := scope) (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode) (body := bodyCode) (selfReason := selfReason) faults post postCode) := by
  intro size bounded mapping world before store finalStore value state continued executed
  exact ProtectedForHeader.post_reflects_reachable_bounded_for (solved := solved) functions definitions registered extension program evidence
    transport
    bindings
    faithful observations
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget
    (fun current currentValid => RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations runtimeViews
          program evidence currentValid.ledger currentValid.runtime uninitialized missing)) budget)
    runtimeViews postTree postErrors valid agrees reference state continued executed bounded
end Concrete

section Continuation
variable {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {program : SourceSemantics.Program}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {solved : List SolvedRequirement}
  {administrative : Core.Context} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {registry : SourceCoreRawMetadata.Registry} {type : Core.Ty} {faults : FunctionCalls.FaultRep}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
  {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {contextLocation : Location} {native : NativeFrame} {value : Core.Value} {finalStore : Store}
  {items : List ForItemForm} {size budget : Nat}
  {meaning : Nat → SourceSemantics.Context → Scope → Expr → Prop}

/-- Initializers select the continuation at its original inclusive native
size; the independently reconstructed source prefix is never bounded by it. -/
theorem continuation_at_remaining
    (receipt : RecursiveNamedHeaderContracts.ResultAtFor (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) size (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults
      (RecursiveNamedHeaderContracts.ContinuationWithin budget meaning) context environment heap items mapping world store value finalStore)
    (bounded : size ≤ budget) :
    (∃ sourceSize finalContext reason after,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment heap items finalContext reason after) ∨
    (∃ sourceSize finalContext finalEnvironment after,
      ∃ tail : ProtectedForHeader.TailFor (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native
        (RecursiveNamedHeaderContracts.ContinuationWithin budget meaning) finalContext finalEnvironment after,
      ∃ remainingSize, SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment heap items finalContext finalEnvironment after ∧
      remainingSize ≤ size ∧ remainingSize ≤ budget ∧
      EvaluationSize remainingSize tail.actual tail.store (tail.code.rename tail.embedding) value finalStore ∧
      meaning remainingSize finalContext tail.scope tail.code ∧ entry tail.scope tail.mapping tail.world after tail.store tail.canonical) := by
  cases receipt with
  | fault trace _ _ _ _ _ _ _ => exact .inl ⟨_, _, _, _, trace⟩
  | continues tail trace _ _ _ _ remaining smaller =>
    exact .inr ⟨_, _, _, _, tail, _, trace, smaller, Nat.le_trans smaller bounded, remaining,
      RecursiveNamedHeaderContracts.tail_at_remaining_for tail smaller bounded, tail.installed⟩

/-- An empty initializer keeps the exact same native witness and inclusive
bound. A strict-only continuation family would exclude this case. -/
theorem empty_continuation
    (tail : ProtectedForHeader.TailFor (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native
      (RecursiveNamedHeaderContracts.ContinuationWithin size meaning) context environment heap)
    (evaluated : EvaluationSize size tail.actual tail.store (tail.code.rename tail.embedding) value finalStore) :
    RecursiveNamedHeaderContracts.ResultAtFor (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) size (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults
      (RecursiveNamedHeaderContracts.ContinuationWithin size meaning) context environment heap [] tail.mapping tail.world tail.store value finalStore ∧
    meaning size context tail.scope tail.code ∧ ¬ size < size :=
  ⟨.nil tail evaluated, RecursiveNamedHeaderContracts.tail_at_remaining_for tail (Nat.le_refl _) (Nat.le_refl _), Nat.lt_irrefl _⟩
end Continuation

section Boundary
variable {solved : List SolvedRequirement} {context next : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {owner : Resolved.DeclarationId} {binder : TypedBinder}

/-- The actual binder relation transports all runtime rows and coverage. -/
theorem runtime_extend (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
    (extended : BinderExtends owner context binder next) :
    CompatibleRuntimeContextValidity.Valid solved next evidence := valid.extend extended

/-- Unused and repeated occurrences are retained in the same complete ledger. -/
theorem full_ledger {row : SolvedRequirement}
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence) (member : row ∈ solved) :
    row ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
end Boundary

section OrdinaryBoundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def context : SourceSemantics.Context := (Context.ofSignatures signatures).withSolvedRequirements [row]

/-- Runtime tails cannot be erased into a false ordinary-ledger premise. -/
theorem runtime_not_ordinary :
    CompatibleRuntimeContextValidity.Valid [row] context [] ∧
      ¬ CompatibleExpressionLiterals.ContextValid [row] context [] := by
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · change ([⟨0⟩] : List RequirementId).Nodup; decide
    · intro item evidence member implementation
      have same : item = row := by simpa [context, Context.withSolvedRequirements] using member
      subst item
      cases implementation
  · constructor
    · intro predicate evidence found; cases found
    · intro predicate member; cases member
  · intro ordinary
    have valid := ordinary.valid.entriesValid row (by simp [context, Context.withSolvedRequirements])
    cases valid with
    | intro retained =>
      cases retained with
      | intro represents valid =>
        cases represents
        cases valid with
        | assumption member => cases member
end OrdinaryBoundary

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- Actual template-bearing headers are compiled unchanged. This exercises
only their reached Bool children; the enclosing qualified callable is not
claimed to compile. Post executions retain the actual six loop temporaries. -/
private def template_headers : IO Unit := do
  let program ← get "runtime header template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " for (let initialized = false, initialized = true, initialized; false; let changed = true, changed = false, changed) {}",
      " for (let missing: Bool, missing; false;) {}",
      " for (; false; let missing: Bool, missing) {}",
      " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "header template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "header template body missing")
  let specialized ← get "header template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := specialized.function.typedBody
  let ledger := specialized.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger.map (·.id) == generic.solvedRequirements.map (·.id))
    "header template full ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !specialized.assumptions.contains predicate)
          "header template assumption promoted"
      | _ => throw (IO.userError "header template implementation fabricated")
    | _ => throw (IO.userError "header template row missing or duplicated")
  let roots := source.roots.filterMap fun
    | .statement id => (source.lookupStatement? id).bind fun node => match node.form with
      | .forLoop _ _ _ _ => some node | _ => none
    | _ => none
  require (roots.length == 3) "header template actual loop count"
  let policy : SourceCoreLoops.Policy := {lowerExpression := SourceCoreControl.lowerExpressionWithReasons}
  let reason := Word.ofNatModulo 877
  let captured := Core.Value.closure .word .word (.var 0) [.word (Word.ofNatModulo 881)]
  let before : Store := [.integer (-883), captured, .inLeft (LocalLoop.functionType .unit) .unit]
  for (node, index) in roots.zipIdx do
    match node.form with
    | .forLoop initializers _ post _ =>
      for (items, isPost) in [(initializers, false), (post, true)] do
        let code ← get "runtime actual header accepted"
          (SourceCoreLoops.lowerForItems policy (.occurrence node.id.occurrence) 300 source [] items .unit
            (fun _ => reason) (fun _ => .ok (LocalLoop.fallthrough .unit)))
        require (Core.infer? [] code [] == some (LocalLoop.resultType .unit)) "runtime bare header type"
        let fault := (index == 1 && !isPost) || (index == 2 && isPost)
        let cells : List Core.Value := if index == 0 then [.inRight .unit (.bool (!isPost))]
          else if fault then [.inLeft .bool .unit] else []
        let expected : Core.Value := if fault then .inLeft (LocalLoop.controlType .unit) (.word reason)
          else LocalLoop.fallthroughValue .unit
        for continued in [false, true] do
          let actual := if isPost then TypedImperativeFor.postValues .unit 2 continued ++ [captured] else [captured]
          let issued := if isPost then ForLoop.postCode code else code
          require (!isPost || (TypedImperativeFor.postValues .unit 2 continued).length == 6) "post actual six slots"
          for fuel in [0, 1, 23, 10000] do
            let first := Core.runStateful fuel (.initial issued actual before)
            let completed := match first with
              | .outOfFuel state => Core.runStateful 10000 state | other => other
            match completed with
            | .done value after =>
              require (value == expected && after == before ++ cells) "runtime header complete result/store/resume"
            | other => throw (IO.userError s!"runtime header unfinished {reprStr other}")
    | _ => throw (IO.userError "header template loop changed")

def run : IO Unit := do
  template_headers
  SourceCoreRecursiveNamedProtectedHeaderBounds.run
  IO.println "runtime header/post: concrete supported builtin children / full template ledger / original continuation bounds / actual six slots / complete cells and resume GREEN"

end Tests.SourceCoreRecursiveNamedForHeaderRuntimeBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedWhileBounds
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedWhileRuntimeBounds
/-! The sole finite while proof accepts a context predicate. These consumers
specialize it to the complete runtime ledger and actual dictionary, then close
atomic conditions and empty bodies with concrete existing semantics. Template
rows stay present; Header, for and lexical contracts remain unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedWhileRuntimeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open RecursiveNamedLoopContracts (Below PreservesAtFor ReflectsAtFor)
#check_failure SourceTypedRuntime.run

section EmptyBody
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} {frame : SourceCoreCallableIndexedFrames.Layout}
  {globals : Nat} {administrative : Core.Context} {scope : Scope} {expected : TypeSystem.Ty} {type : Ty}

/-- The empty body closes at every original source grade and every predicate. -/
theorem empty_preserves_at (validity : SourceSemantics.Context → Prop) (size : Nat) :
    PreservesAtFor functions program evidence validity (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      (administrative := administrative) (scope := scope) size false [] expected type (LocalLoop.fallthrough type) := by
  intro _ mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals _ _ _ _ _ _ trace
  cases trace with
  | control executed =>
    obtain ⟨rfl, rfl, rfl⟩ := ScalarStatementViews.nil_view false executed.sound
    exact ⟨_, store, mapping, world, LocalLoop.fallthrough_evaluates _ _ _, .fallthrough environment,
      heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩
  | fault failed => exact False.elim (ScalarStatementViews.nil_cannot_fault false failed.sound)

/-- Reflection keeps the native grade and constructs a separate source grade. -/
theorem empty_reflects_at (validity : SourceSemantics.Context → Prop) (size : Nat) :
    ReflectsAtFor functions program evidence validity (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      (administrative := administrative) (scope := scope) size false [] expected type (LocalLoop.fallthrough type) := by
  intro _ mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals _ _ _ _ _ _ evaluated
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.fallthrough_evaluates type actual store)
  have original := ProtectedLexicalStatements.nil_executes false program context evidence source environment before
  obtain ⟨sourceSize, trace⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size original
  exact ⟨sourceSize, context, _, before, mapping, world, trace, .fallthrough environment, heaps,
    .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩
end EmptyBody

section RuntimeWhile
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {administrative : Core.Context}
  {scope : Scope} {type : Ty} {conditionCode : Expr} {selfReason : Word}

include transport in
/-- Runtime validity closes the condition law; the body needs no semantic IH. -/
theorem runtime_preserves_at {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition [])
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionReceipt : CompatibleExpressionLiteralRuntime.Certificate solved source condition ⟨.bool, conditionCode⟩)
    (unique : NodeOccurrencesUnique source)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode (LocalLoop.fallthrough type) selfReason) (LocalLoop.resultType type) ambient.definitions)
    (budget size : Nat) (bounded : size ≤ budget) :
    ProtectedWhile.HeadPreservesAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      size id expected type (LocalLoop.whileLoop type conditionCode (LocalLoop.fallthrough type) selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ProtectedWhile.Body.while_preserves_bounded_for
    (certificate := fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)
    (validity := fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    functions program evidence transport budget
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (TypedGenericExpressionMeaning.preserves_of_unrestricted
          (CompatibleExpressionLiteralRuntime.preserves functions program context evidence valid.ledger valid.runtime unique faults))) child)
    found form conditionFound conditionReceipt typed unique
    (fun child _ => empty_preserves_at functions program evidence _ child) size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed trace

include transport in
/-- Native completion reflects without source execution or preservation input. -/
theorem runtime_reflects_at {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition [])
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionReceipt : CompatibleExpressionLiteralRuntime.Certificate solved source condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode (LocalLoop.fallthrough type) selfReason) (LocalLoop.resultType type) ambient.definitions)
    (budget size : Nat) (bounded : size ≤ budget) :
    ProtectedWhile.HeadReflectsAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      size id expected type (LocalLoop.whileLoop type conditionCode (LocalLoop.fallthrough type) selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ProtectedWhile.Body.while_reflects_bounded_for
    (certificate := fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)
    (validity := fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    functions program evidence transport budget
    (fun child _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (TypedGenericExpressionMeaning.reflects_of_unrestricted
          (CompatibleExpressionLiteralRuntime.reflects functions program context evidence valid.ledger valid.runtime source faults))) child)
    found form conditionFound conditionReceipt typed
    (fun child _ => empty_reflects_at functions program evidence _ child)
    (fun trace => by obtain ⟨_, impossible, _⟩ := ScalarStatementViews.nil_view false trace; cases impossible)
    size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
end RuntimeWhile


section Frame
variable {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
  {types : List TypeSystem.Ty} {solved : List SolvedRequirement}

/-- The real frame supplies the same complete dictionary and ledger, with no
empty-template or ordinary-validity condition. -/
theorem frame_runtime_valid
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved) :
    CompatibleRuntimeContextValidity.Valid solved context function.evidence :=
  CompatibleRuntimeContextValidity.of_frame frame extended programTyped sameLedger

/-- Every retained row, including an unused template, is kept by the consumer. -/
theorem full_ledger_retained {row : SolvedRequirement}
    (valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence) (member : row ∈ solved) :
    row ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
end Frame

section Boundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def context : SourceSemantics.Context := (Context.ofSignatures signatures).withSolvedRequirements [row]

/-- Runtime validity cannot supply the old ordinary premise for an unused row. -/
theorem runtime_not_ordinary :
    CompatibleRuntimeContextValidity.Valid [row] context [] ∧
      ¬ CompatibleExpressionLiterals.ContextValid [row] context [] := by
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · change ([⟨0⟩] : List RequirementId).Nodup; decide
    · intro item evidence member implementation
      have same : item = row := by simpa [context, Context.withSolvedRequirements] using member
      subst item
      cases implementation
  · constructor
    · intro predicate evidence found; cases found
    · intro predicate member; cases member
  · intro ordinary
    have valid := ordinary.valid.entriesValid row (by simp [context, Context.withSolvedRequirements])
    cases valid with
    | intro retained =>
      cases retained with
      | intro represents valid =>
        cases represents
        cases valid with
        | assumption member => cases member
end Boundary

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- The enclosing checked source has a real qualified local. We compile the
reached bare while separately with its original complete node table and rows.
This audit does not claim compilation of the enclosing qualified body. -/
private def template_while : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " while (false) {} let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] }
  let program ← get "runtime while checked template source" (checkProgram workspace)
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature
    | _ => throw (IO.userError "runtime while qualified signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic
    | _ => throw (IO.userError "runtime while qualified body missing")
  let specialized ← get "runtime while actual template specialization"
    (SourceSpecialization.specializeFunction signature generic [])
  let source := specialized.function.typedBody
  let ids := source.localSchemeTemplateIds
  let rows := specialized.function.solvedRequirements
  require (!ids.isEmpty && signature.scheme.predicates.isEmpty && specialized.assumptions.isEmpty)
    "runtime while template ledger boundary disappeared"
  require (rows.map (·.id) == generic.solvedRequirements.map (·.id))
    "runtime while specialization removed or reordered ledger rows"
  for id in ids do
    let row ← match rows.filter (·.id == id) with
      | [row] => pure row
      | _ => throw (IO.userError "runtime while unique template row missing")
    match row.evidence with
    | .assumption predicate =>
      require (predicate == row.predicate && !(specialized.assumptions.contains predicate))
        "runtime while template was promoted to a declaration assumption"
    | _ => throw (IO.userError "runtime while template evidence changed")
  let heads := source.nodes.filterMap fun
    | .statement node => match node.form with
      | .whileLoop condition [] => some (node, condition)
      | _ => none
    | _ => none
  let (node, condition) ← match heads with
    | [pair] => pure pair
    | _ => throw (IO.userError "runtime while actual empty head missing")
  let conditionNode ← match source.lookupExpression? condition with
    | some node => pure node
    | none => throw (IO.userError "runtime while condition lookup missing")
  require (conditionNode.form == .reference "false" (.builtinBoolean false)) "runtime while source condition changed"
  let reason : Word := Word.ofNatModulo 811
  let lower := SourceCoreControl.lowerExpressionWithReasons
  let conditionCode ← get "runtime while original condition lower" (lower 100 source [] condition (fun _ => reason))
  match accepted : SourceCoreLoops.lowerFlowStatementsWithExpression lower 101 source [] [node.id] .unit (fun _ => reason) false reason with
  | .error error => throw (IO.userError s!"runtime while actual compiler failed: {reprStr error}")
  | .ok code =>
    let _issued := accepted
    let expected := LocalLoop.sequence .unit
      (LocalLoop.whileLoop .unit conditionCode.expression (LocalLoop.fallthrough .unit) reason)
      (LocalLoop.fallthrough .unit)
    require (code == expected) "runtime while full original head/empty suffix code changed"
    require (source.localSchemeTemplateIds == ids && specialized.function.solvedRequirements == rows)
      "runtime while compiler filtered the complete source ledger"
    let captured := Core.Value.closure .word .word (.var 0) [.word (Word.ofNatModulo 821)]
    let initial : Store := [.word (Word.ofNatModulo 823), captured]
    let mut baseline : Option (Core.Value × Store) := none
    for fuel in [10000, 0, 1, 19] do
      let first := runStateful fuel (.initial code [] initial)
      let completed := match first with
        | .outOfFuel checkpoint => runStateful 10000 checkpoint
        | result => result
      match completed with
      | .done value store =>
        require (value == .inRight .word (.inLeft LocalLoop.transferType (.inLeft .unit .unit))) "runtime while zero-iteration flow changed"
        require (decide (store.take initial.length = initial)) "runtime while changed complete initial prefix"
        require (store.length == initial.length + 1) "runtime while installed self cell missing"
        match baseline with
        | none => baseline := some (value, store)
        | some pair => require (decide (pair = (value, store))) "runtime while complete closure/store resume changed"
      | other => throw (IO.userError s!"runtime while native completion failed: {reprStr other}")

def run : IO Unit := do
  template_while
  SourceCoreRecursiveNamedWhileBounds.run
  IO.println "runtime while bounds: complete template-bearing checked ledger, original bare while compiler/code, full self-cell store and resume GREEN"

end Tests.SourceCoreRecursiveNamedWhileRuntimeBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedForRuntimeBounds
/-! Fixed-budget for loops accept the same complete runtime context as their
condition, body and post. Concrete builtin certificates and the empty body
close every semantic child here; the post is the actual protected header Tree.
The original source/native measures remain independent. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedForRuntimeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
section Concrete
variable {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))


include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings unique in
theorem runtime_preserves_at {context : SourceSemantics.Context} {scope : Scope}
    {administrative : Core.Context} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode postCode : Expr} {post : List ForItemForm} {reason : Word}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionReceipt : CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt
      scope condition ⟨.bool, conditionCode⟩)
    (postTree : ProtectedForHeader.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      ambient.definitions administrative type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode (LocalLoop.fallthrough type) postCode reason)
      (LocalLoop.resultType type) ambient.definitions)
    (budget size : Nat) (bounded : size ≤ budget) :
    RecursiveNamedForContracts.LoopPreservesAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) size
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      condition post [] expected type
      (LocalLoop.iterate type conditionCode (LocalLoop.fallthrough type) postCode reason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ProtectedFor.Body.loop_preserves_bounded_for functions program evidence transport
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) budget
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations runtimeViews
          program evidence valid.ledger valid.runtime unique uninitialized missing)) child)
    conditionFound conditionReceipt typed unique
    (fun child _ => SourceCoreRecursiveNamedWhileRuntimeBounds.empty_preserves_at functions program evidence _ child)
    (fun agrees reference currentValid child smaller =>
      SourceCoreRecursiveNamedForHeaderRuntimeBounds.runtime_post_preserves functions definitions registered extension
        faithful observations runtimeViews evidence unique transport bindings uninitialized missing
        postTree currentValid agrees reference budget child (Nat.le_of_lt smaller))
    (fun agrees reference currentValid child smaller =>
      SourceCoreRecursiveNamedForHeaderRuntimeBounds.runtime_post_faults functions definitions registered extension
        faithful observations runtimeViews evidence unique transport bindings uninitialized missing
        postTree postErrors currentValid agrees reference budget child (Nat.le_of_lt smaller))
    size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
theorem runtime_reflects_at {context : SourceSemantics.Context} {scope : Scope}
    {administrative : Core.Context} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode postCode : Expr} {post : List ForItemForm} {reason : Word}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionReceipt : CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt
      scope condition ⟨.bool, conditionCode⟩)
    (postTree : ProtectedForHeader.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      ambient.definitions administrative type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode (LocalLoop.fallthrough type) postCode reason)
      (LocalLoop.resultType type) ambient.definitions)
    (budget size : Nat) (bounded : size ≤ budget) :
    RecursiveNamedForContracts.LoopReflectsAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) size
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      condition post [] expected type
      (LocalLoop.iterate type conditionCode (LocalLoop.fallthrough type) postCode reason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ProtectedFor.Body.loop_reflects_bounded_for functions program evidence transport
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) budget
    (fun child _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations runtimeViews
          program evidence valid.ledger valid.runtime uninitialized missing)) child)
    conditionFound conditionReceipt typed
    (fun child _ => SourceCoreRecursiveNamedWhileRuntimeBounds.empty_reflects_at functions program evidence _ child)
    (fun trace => by obtain ⟨_, impossible, _⟩ := ScalarStatementViews.nil_view false trace; cases impossible)
    (fun agrees reference currentValid child smaller =>
      SourceCoreRecursiveNamedForHeaderRuntimeBounds.runtime_post_reflects functions definitions registered extension
        faithful observations runtimeViews evidence transport bindings uninitialized missing
        postTree postErrors currentValid agrees reference budget child (Nat.le_of_lt smaller))
    size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
end Concrete

/-- The original native entry and condition remain strictly below the outer
budget; no regenerated completion witness is substituted. -/
abbrev original_condition := @SourceCoreRecursiveNamedForBounds.native_condition_below

/-- Post retains its actual six-slot evaluation and original cost. -/
abbrev original_post := @SourceCoreRecursiveNamedForBounds.native_post_below

/-- A later fault keeps the complete ordered condition/body/post prefix. -/
abbrev later_fault := @SourceCoreRecursiveNamedForBounds.next_fault_children

/-- Runtime coverage does not imply ordinary validity of unused rows. -/
abbrev runtime_not_ordinary := SourceCoreRecursiveNamedForHeaderRuntimeBounds.runtime_not_ordinary

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- The actual checked/specialized source retains unresolved template rows.
Only its original for roots are compiled here; no enclosing qualified callable
compilation is claimed. Exact phase code and every native cell are checked. -/
private def template_for : IO Unit := do
  let program ← get "runtime for template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " for (; false; let skipped: Bool, skipped) {}",
      " for (; true; let skipped: Bool, skipped) { break; }",
      " for (; true; let failed: Bool, failed) { continue; }",
      " for (; true;) { let failed: Bool; failed; }",
      " for (let looping = true; looping; looping = false) {}",
      " for (let looping = true; looping; looping = false) { continue; }",
      " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "for template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "for template body missing")
  let specialized ← get "for template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := specialized.function.typedBody
  let rows := specialized.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && rows.map (·.id) == generic.solvedRequirements.map (·.id))
    "for full template ledger changed"
  for id in source.localSchemeTemplateIds do
    match rows.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !specialized.assumptions.contains predicate)
          "for template assumption promoted"
      | _ => throw (IO.userError "for template implementation fabricated")
    | _ => throw (IO.userError "for template row missing or duplicated")
  let roots := source.roots.filterMap fun
    | .statement id => (source.lookupStatement? id).bind fun node => match node.form with
      | .forLoop _ _ _ _ => some node | _ => none
    | _ => none
  require (roots.length == 6) "for original root inventory changed"
  let lower := SourceCoreControl.lowerExpressionWithReasons
  let policy : SourceCoreLoops.Policy := { lowerExpression := lower }
  let reason := Word.ofNatModulo 911
  let captured := Core.Value.closure .word .word (.var 0) [.word (Word.ofNatModulo 919)]
  let initial : Store := [.integer (-929), captured]
  for (node, index) in roots.zipIdx do
    match node.form with
    | .forLoop initializers condition post statements =>
      let loopScope ← match initializers with
        | [] => pure []
        | [.letDecl binder (some _)] => pure [(binder.id, Core.Ty.bool)]
        | _ => throw (IO.userError "for initializer shape changed")
      let conditionCode ← get "for original condition"
        (lower 199 source loopScope condition (fun _ => reason))
      let bodyCode ← get "for original body"
        (SourceCoreLoops.lowerFlowStatementsWithPolicy policy 199 source loopScope statements .unit (fun _ => reason) false reason)
      let postCode ← get "for original post"
        (SourceCoreLoops.lowerForItems policy (.occurrence node.id.occurrence) 199 source loopScope post .unit
          (fun _ => reason) (fun _ => .ok (LocalLoop.fallthrough .unit)))
      let head ← get "for original initialization"
        (SourceCoreLoops.lowerForItems policy (.occurrence node.id.occurrence) 199 source [] initializers .unit
          (fun _ => reason) (fun scope => if scope == loopScope then
            .ok (LocalLoop.iterate .unit conditionCode.expression bodyCode postCode reason)
            else .error (.unsupportedStatement node.id node.form)))
      let code ← get "for actual whole loop"
        (SourceCoreLoops.lowerFlowStatementsWithPolicy policy 200 source [] [node.id] .unit (fun _ => reason) false reason)
      require (code == LocalLoop.sequence .unit head (LocalLoop.fallthrough .unit))
        "for actual whole original phases/suffix differ"
      require (Core.infer? [] code [] == some (LocalLoop.resultType .unit)) "for actual code type"
      let localCell := Core.Value.inRight .unit (.bool true)
      let beforeLoop := if loopScope.isEmpty then initial else initial ++ [localCell]
      let actual := if loopScope.isEmpty then [captured]
        else [Core.Value.cellRef (.sum .unit .bool) initial.length, .bool true, captured]
      let conditionActual := if loopScope.isEmpty then conditionCode.expression else conditionCode.expression.weakenAt 1
      let bodyActual := if loopScope.isEmpty then bodyCode else bodyCode.weakenAt 1
      let postActual := if loopScope.isEmpty then postCode else postCode.weakenAt 1
      let installed := TypedLexicalWhile.installedStore beforeLoop .unit conditionActual bodyActual postActual reason actual
      let expectedStore := if index == 2 || index == 3 then installed ++ [.inLeft .bool .unit]
        else if index ≥ 4 then installed.set initial.length (.inRight .unit (.bool false)) else installed
      let expectedValue := if index == 2 || index == 3 then
          Core.Value.inLeft (LocalLoop.controlType .unit) (.word reason)
        else LocalLoop.fallthroughValue .unit
      for fuel in [0, 1, 29, 10000] do
        let first := Core.runStateful fuel (.initial code [captured] initial)
        let completed := match first with
          | .outOfFuel checkpoint => Core.runStateful 10000 checkpoint | result => result
        match completed with
        | .done value after =>
          require (value == expectedValue && after == expectedStore)
            s!"for full ordered store/result/resume changed at root {index}"
        | other => throw (IO.userError s!"for actual loop unfinished {reprStr other}")
    | _ => throw (IO.userError "for original root form changed")

def run : IO Unit := do
  template_for
  SourceCoreRecursiveNamedForBounds.run
  IO.println "runtime for bounds: supported condition / concrete body / actual protected post / original strict children GREEN"

end Tests.SourceCoreRecursiveNamedForRuntimeBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedLexicalRuntimeBounds
/-! The same lexical Tree uses the complete runtime context and actual numeric
literal certificates. The expression law is closed by concrete builtin meaning;
no child or body execution law is a test input. Allocation, scoped restoration,
original source and Core sizes and exact Entry are preserved. Header, for and
catalog mutual closure remain separate boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedLexicalRuntimeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
#check_failure SourceTypedRuntime.run

section Concrete
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {values : ValuesContext}
  {source : TypedSource} {solved : List SolvedRequirement} {fuel : Nat} {reasonAt : ExpressionId → Word}
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
  (bindings : ProtectedExpressionMeaning.Binds entry)

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
/-- The actual builtin certificate closes all reached expression leaves. -/
theorem runtime_preserves_at (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      context scope mode statements expected type code) :
    RecursiveNamedLexicalContracts.PreservesAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  apply RecursiveNamedLexicalTreeBounds.preserves_at_for functions definitions registered program evidence transport bindings
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget size bounded ?_ tree valid unique
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  intro child _ context valid
  exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
    (ProtectedExpressionMeaning.preserves_of_typed entry
      (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations runtimeViews
        program evidence valid.ledger valid.runtime unique uninitialized missing)) child

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
/-- Native completion reflects to an independently sized source outcome. -/
theorem runtime_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      context scope mode statements expected type code) :
    RecursiveNamedLexicalContracts.ReflectsAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  apply RecursiveNamedLexicalTreeBounds.reflects_at_for functions definitions registered program evidence transport bindings
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget size bounded ?_ tree valid
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  intro child _ context valid
  exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
    (ProtectedExpressionMeaning.reflects_of_typed entry
      (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations runtimeViews
        program evidence valid.ledger valid.runtime uninitialized missing)) child

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
/-- The five-way consumer keeps the same trace, grade, frame and heap. -/
theorem imperative_preserves_at (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size ≤ budget) {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      context scope mode statements expected type code) :
    RecursiveNamedLoopContracts.PreservesAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code :=
  RecursiveNamedImperativeLexicalBounds.preserves_at_for functions program evidence _
    (runtime_preserves_at functions definitions registered extension faithful observations runtimeViews program evidence
      uninitialized missing transport bindings unique budget size bounded tree)

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
/-- Reflection also only converts the existing three-way FlowRep. -/
theorem imperative_reflects_at (budget size : Nat) (bounded : size ≤ budget) {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      context scope mode statements expected type code) :
    RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code :=
  RecursiveNamedImperativeLexicalBounds.reflects_at_for functions program evidence _
    (runtime_reflects_at functions definitions registered extension faithful observations runtimeViews program evidence
      uninitialized missing transport bindings budget size bounded tree)
end Concrete

section Transport
/-- Actual lexical extension keeps every solved row and the same dictionary. -/
theorem binder_runtime_valid {solved : List SolvedRequirement} {context nextContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {owner : Resolved.DeclarationId} {binder : TypedBinder}
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
    (extended : BinderExtends owner context binder nextContext) :
    CompatibleRuntimeContextValidity.Valid solved nextContext evidence := valid.extend extended

/-- An actual frame and independent program typing supply the initial context. -/
theorem frame_runtime_valid {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {solved : List SolvedRequirement}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved) :
    CompatibleRuntimeContextValidity.Valid solved context function.evidence :=
  CompatibleRuntimeContextValidity.of_frame frame extended programTyped sameLedger

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def context : SourceSemantics.Context := (Context.ofSignatures signatures).withSolvedRequirements [row]


/-- The same complete runtime ledger still does not imply ordinary validity. -/
theorem runtime_not_ordinary :
    CompatibleRuntimeContextValidity.Valid [row] context [] ∧
      ¬ CompatibleExpressionLiterals.ContextValid [row] context [] :=
  SourceCoreRecursiveNamedWhileRuntimeBounds.runtime_not_ordinary
end Transport

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- The original checked source retains a qualified local and every ledger
row. Only its reached bare lexical roots are lowered here; the enclosing
qualified body is a separate compiler boundary. Full code equality includes
both actual scoped children and the issued empty continuation. -/
private def template_lexical : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " { let scoped = false; scoped; }",
      " if (false) { let selected = false; } else { let selected = true; }",
      " { let gap: Bool; gap; }",
      " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] }
  let program ← get "runtime lexical checked template source" (checkProgram workspace)
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature
    | _ => throw (IO.userError "runtime lexical qualified signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic
    | _ => throw (IO.userError "runtime lexical qualified body missing")
  let specialized ← get "runtime lexical actual template specialization"
    (SourceSpecialization.specializeFunction signature generic [])
  let source := specialized.function.typedBody
  let ids := source.localSchemeTemplateIds
  let rows := specialized.function.solvedRequirements
  require (!ids.isEmpty && signature.scheme.predicates.isEmpty && specialized.assumptions.isEmpty)
    "runtime lexical template ledger boundary disappeared"
  require (rows.map (·.id) == generic.solvedRequirements.map (·.id))
    "runtime lexical specialization removed or reordered ledger rows"
  for id in ids do
    let row ← match rows.filter (·.id == id) with
      | [row] => pure row
      | _ => throw (IO.userError "runtime lexical unique template row missing")
    match row.evidence with
    | .assumption predicate =>
      require (predicate == row.predicate && !(specialized.assumptions.contains predicate))
        "runtime lexical template was promoted to a declaration assumption"
    | _ => throw (IO.userError "runtime lexical template evidence changed")
  let heads := source.roots.filterMap fun
    | .statement id => (source.lookupStatement? id).bind fun node => match node.form with
      | .block _ | .ifThen _ _ _ => some node
      | _ => none
    | _ => none
  require (heads.length == 3) "runtime lexical actual scoped roots changed"
  let reason : Word := Word.ofNatModulo 827
  let lower := SourceCoreControl.lowerExpressionWithReasons
  let captured := Core.Value.closure .word .word (.var 0) [.word (Word.ofNatModulo 829)]
  let initial : Store := [.word (Word.ofNatModulo 831), captured]
  for (node, index) in heads.zipIdx do
    let (headCode, expectedCells, expectedValue) ← match node.form with
      | .block statements =>
        let child ← get "runtime lexical original block child"
          (SourceCoreControl.lowerFlowStatementsWithExpression lower 299 source [] statements .unit (fun _ => reason) false)
        pure (child,
          (if index == 0 then [.inRight .unit (.bool false)] else [.inLeft .bool .unit]),
          (if index == 0 then .inRight .word (.inLeft .unit .unit)
            else .inLeft (LocalControl.controlType .unit) (.word reason)))
      | .ifThen condition thenBody (some elseBody) =>
        let child ← get "runtime lexical original condition" (lower 299 source [] condition (fun _ => reason))
        let thenCode ← get "runtime lexical original then child"
          (SourceCoreControl.lowerFlowStatementsWithExpression lower 299 source [] thenBody .unit (fun _ => reason) false)
        let elseCode ← get "runtime lexical original else child"
          (SourceCoreControl.lowerFlowStatementsWithExpression lower 299 source [] elseBody .unit (fun _ => reason) false)
        pure (LocalControl.conditional .unit child.expression thenCode elseCode,
          [.inRight .unit (.bool true)], .inRight .word (.inLeft .unit .unit))
      | _ => throw (IO.userError "runtime lexical scoped root form changed")
    let code ← get "runtime lexical actual bare compiler"
      (SourceCoreControl.lowerFlowStatementsWithExpression lower 300 source [] [node.id] .unit (fun _ => reason) false)
    let fullCode := LocalControl.sequence .unit headCode (LocalControl.fallthrough .unit)
    require (code == fullCode) "runtime lexical original child/issued continuation code changed"
    require (source.localSchemeTemplateIds == ids && specialized.function.solvedRequirements == rows)
      "runtime lexical compiler filtered the full source ledger"
    let mut baseline : Option (Core.Value × Store) := none
    for fuel in [10000, 0, 1, 19] do
      let first := runStateful fuel (.initial code [] initial)
      let completed := match first with
        | .outOfFuel checkpoint => runStateful 10000 checkpoint
        | result => result
      match completed with
      | .done value store =>
        require (value == expectedValue) "runtime lexical scoped success/fault result changed"
        require (decide (store = initial ++ expectedCells)) "runtime lexical complete scoped/fault store changed"
        match baseline with
        | none => baseline := some (value, store)
        | some pair => require (decide (pair = (value, store))) "runtime lexical complete captured prefix/resume changed"
      | other => throw (IO.userError s!"runtime lexical native completion failed: {reprStr other}")

def run : IO Unit := do
  template_lexical
  SourceCoreRecursiveNamedLexicalTreeBounds.run
  IO.println "runtime lexical bounds: concrete builtin leaves, same full runtime context, exact lexical allocation/restoration/fault order and resume GREEN"

end Tests.SourceCoreRecursiveNamedLexicalRuntimeBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedImperativeRuntimeBounds
/-! Actual builtin expression receipts close the shared finite Match/For/While
statement proof using the same complete runtime context. Selected arm contexts
come only from their actual ordered source binders. Header construction and the
catalog mutual theorem remain separate boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedImperativeRuntimeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
#check_failure SourceTypedRuntime.run
section Concrete
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {values : ValuesContext}
  {source : TypedSource} {solved : List SolvedRequirement} {fuel : Nat} {reasonAt : ExpressionId → Word}
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
  (bindings : ProtectedExpressionMeaning.Binds entry)

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
/-- The complete concrete expression family closes the sole statement induction. -/
theorem runtime_preserves_at (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size ≤ budget) {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {expressionSyntax : ExpressionId → Prop}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      ambient.definitions administrative context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites .reachable registry faults tree) :
    RecursiveNamedLoopContracts.PreservesAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code := by
  apply RecursiveNamedImperativeFor.preservesAt_match_with
    (validity := fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (extend := fun valid extended => valid.extend extended) (runtimeOf := fun _ valid => valid)
    (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
    (program := program) (evidence := evidence) (transport := transport) (bindings := bindings)
    (budget := budget) (faithful := faithful) (observations := observations)
    (meaningMost := ?_) .reachable unique tree errors size bounded
  intro context valid child _
  exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
    (ProtectedExpressionMeaning.preserves_of_typed entry
      (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations runtimeViews
        program evidence valid.ledger valid.runtime unique uninitialized missing)) child

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
/-- The complete concrete expression family closes the sole statement induction. -/
theorem runtime_reflects_at (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size < budget) {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {expressionSyntax : ExpressionId → Prop}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      ambient.definitions administrative context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites .reachable registry faults tree) :
    RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code := by
  apply RecursiveNamedImperativeFor.reflectsAt_match_with
    (validity := fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (extend := fun valid extended => valid.extend extended) (runtimeOf := fun _ valid => valid)
    (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
    (program := program) (evidence := evidence) (transport := transport) (bindings := bindings)
    (budget := budget) (faithful := faithful) (observations := observations)
    (reflection := ?_) .reachable runtimeViews unique tree errors size bounded
  intro context valid child _
  exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
    (ProtectedExpressionMeaning.reflects_of_typed entry
      (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations runtimeViews
        program evidence valid.ledger valid.runtime uninitialized missing)) child

end Concrete

/-- A stronger condition is transported from the original parent through only
actual source binders. Runtime validity is never used to invent this condition. -/
theorem selected_context {source : TypedSource} (condition : SourceSemantics.Context → Prop)
    (extend : ∀ {context next binder}, condition context →
      BinderExtends source.owner context binder next → condition next)
    {context next : SourceSemantics.Context} {hiddenIds : List Resolved.LocalId}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {request : GenericMatchChildren.Request}
    (valid : condition context)
    (related : GenericMatchChildren.ScopedContextFor source context hiddenIds
      scrutineeType cases fallback request next) : condition next :=
  RecursiveNamedImperativeFor.ContextTransport.scoped_context condition extend valid related

/-- The default request retains the exact parent condition. -/
theorem default_context {source : TypedSource} {condition : SourceSemantics.Context → Prop}
    {context : SourceSemantics.Context} {hiddenIds : List Resolved.LocalId}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase}
    {request : GenericMatchChildren.Request} (valid : condition context)
    (scopeIds : request.scope.map Prod.fst = hiddenIds) :
    GenericMatchChildren.ScopedContextFor source context hiddenIds scrutineeType cases
      (some request.statements) request context ∧ condition context :=
  ⟨.default rfl scopeIds, valid⟩

abbrev actual_frame := @SourceCoreRecursiveNamedLexicalRuntimeBounds.frame_runtime_valid
abbrev unused_ledger := SourceCoreRecursiveNamedLexicalRuntimeBounds.runtime_not_ordinary


private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- The original reached blocks are compiled with the real recursive flow and
match callbacks. Their enclosing qualified lambda remains outside this family. -/
private def template_blocks : IO Unit := do
  let program ← get "upper template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " { match ((61, 7)) { case (61, picked) { let chosen: Word = picked; } default {} } }",
      " { if (true) { match (62) { case 61 { let skipped: Word = 1; } default { let reached: Word = 11; } } } else { let skipped: Word = 2; } }",
      " { let missing: Word; match (61) { case 61 { let fault: Word = missing; } default {} } let skipped: Word = 13; }",
      " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "upper template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "upper template function missing")
  let actual ← get "upper template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger == generic.solvedRequirements)
    "upper complete ordered template ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !actual.assumptions.contains predicate)
          "upper unused template assumption promoted"
      | _ => throw (IO.userError "upper template implementation fabricated")
    | _ => throw (IO.userError "upper template row missing/duplicated")
  let checked ← get "upper template catalog" (SourceCoreCompatibleCatalog.prepare program.signatures 100 [.word, .bool])
  let compilation : SourceCoreCompatibleDataMatches.Context := ⟨.initial checked, ledger, none, none⟩
  let functions : SourceCoreFunctions.Context := {
    plan := ⟨[actual.key], [actual], [], []⟩,
    owner := actual.key, globals := [], administrativePrefix := 1, solvedRequirements := ledger, internalReason := Word.zero}
  let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ =>
    .error (.traversalExhausted (.declaration actual.function.declaration))
  let expression : SourceCoreLoops.ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithReasons noBody fuel functions source scope id reasonAt
  let policy : SourceCoreLoops.Policy := {
    lowerExpression := expression
    lowerMatch := some (SourceCoreCompatibleDataMatches.lowerWithReasons compilation) }
  let roots := source.roots.filterMap fun
    | .statement id => (source.lookupStatement? id).bind fun node => match node.form with
      | .block _ => some node | _ => none
    | _ => none
  require (roots.length == 3) "upper original reached blocks changed"
  let reason := Word.ofNatModulo 941
  let word := fun n => Core.Value.word (Word.ofNatModulo n)
  let captured := Core.Value.closure .word .word (.var 0) [word 947]
  let before : Core.Store := [.integer (-953), captured, .cellRef .integer 0]
  let expectedCells : List Core.Store := [
    [.inRight .unit (.pair (word 61) (word 7)), .inRight .unit (word 7), .inRight .unit (word 7)],
    [.inRight .unit (word 62), .inRight .unit (word 11)],
    [.inLeft .word .unit, .inRight .unit (word 61)] ]
  for ((node, cells), index) in (roots.zip expectedCells).zipIdx do
    let code ← get "upper actual recursive flow"
      (SourceCoreLoops.lowerFlowStatementsWithPolicy policy 200 source [] [node.id] .unit
        (fun _ => reason) false reason)
    require (Core.infer? [] code compilation.definitions == some (LocalLoop.resultType .unit))
      "upper recursive flow type changed"
    let expected := if index == 2 then Core.Value.inLeft (LocalLoop.controlType .unit) (.word reason)
      else LocalLoop.fallthroughValue .unit
    for fuel in [0, 1, 23, 10000] do
      let done := match Core.runStateful fuel (.initial code [captured] before) with
        | .outOfFuel state => Core.runStateful 10000 state | other => other
      match done with
      | .done value after =>
        require (value == expected && after == before ++ cells)
          s!"upper original block full ordered store/fault/resume changed at {index}: {reprStr value} / {reprStr after}"
      | other => throw (IO.userError s!"upper original block unfinished {reprStr other}")

def run : IO Unit := do
  template_blocks
  SourceCoreRecursiveNamedImperativeMatchBounds.run
  IO.println "runtime imperative bounds: actual whole recursive Match/For/While / same reached template ledger / stronger context transport / full ordered store and fault/resume GREEN"

end Tests.SourceCoreRecursiveNamedImperativeRuntimeBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedRuntimeHeaders
/-! Runtime headers use actual source-frame validity without requiring ordinary
validity for every retained row. Legacy profiles retain that stronger premise
explicitly. These checks add no execution model or runtime law to the header. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedRuntimeHeaders
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedCatalog GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup

/-- This complete constructor takes authentic static receipts and independent
program typing; there is no pre-existing Header or ordinary validity input. -/
abbrev actual_from_receipts := @Header.of_source_frame
abbrev runtime_from_receipts := @Header.of_runtime_body

/-- The same actual frame supplies full retained runtime rows and coverage. -/
theorem actual_frame {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {solved : List SolvedRequirement}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved) :
    CompatibleRuntimeContextValidity.Valid solved context function.evidence :=
  CompatibleRuntimeContextValidity.of_frame frame extended programTyped sameLedger

section Rebuild
variable {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : SourceSemantics.Program}

/-- Reconstruct from the same fields without reading the prior validity field.
The public constructor above also works before any Header has been built. -/
private def rebuild (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved) :
    Header prepared values definitions program :=
  Header.of_dictionary_frame
    (function := header.function)
    (instantiation := header.instantiation)
    (sourceBody := header.sourceBody)
    (frame := header.frame)
    (named := header.named)
    (agreement := header.agreement)
    (ordinaryReturn := header.ordinaryReturn)
    (ordinaryParameters := header.ordinaryParameters)
    (target := header.target)
    (context := header.context)
    (types := header.types)
    (bindings := header.bindings)
    (parameters := header.parameters)
    (inputs := header.inputs)
    (extended := header.extended)
    (solved := header.solved)
    (reasonAt := header.reasonAt)
    (readFuel := header.readFuel)
    (output := header.output)
    (policy := header.policy)
    (fuel := header.fuel)
    (fellThrough := header.fellThrough)
    (escaped := header.escaped)
    (body := header.body)
    (parameterCode := header.parameterCode)
    (code := header.code)
    (layouts := header.layouts)
    (owner := header.owner)
    (active := header.active)
    (globals := header.globals)
    (onError := header.onError)
    (acceptedPrefix := header.acceptedPrefix)
    (hook := header.hook)
    (definitions_eq := header.definitions_eq)
    (registered := header.registered)
    (unique := header.unique)
    (parameterType := header.parameterType)
    (resultType := header.resultType)
    (representation := header.representation)
    (compiledFuel := header.compiledFuel)
    (compiled := header.compiled)
    (slot := header.slot)
    (selected := header.selected)
    (cached := header.cached)
    programTyped sameLedger

theorem same_cached_row (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved) :
    (rebuild header programTyped sameLedger).slot = header.slot ∧
      (rebuild header programTyped sameLedger).named = header.named ∧
      (rebuild header programTyped sameLedger).code = header.code ∧
      (rebuild header programTyped sameLedger).compiled = header.compiled :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem same_source (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved) :
    (rebuild header programTyped sameLedger).function = header.function ∧
      (rebuild header programTyped sameLedger).sourceBody = header.sourceBody ∧
      (rebuild header programTyped sameLedger).instantiation = header.instantiation ∧
      (rebuild header programTyped sameLedger).context = header.context :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem same_ordered_inputs (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved) :
    (rebuild header programTyped sameLedger).bindings = header.bindings ∧
      (rebuild header programTyped sameLedger).solved = header.solved := ⟨rfl, rfl⟩

theorem retained_unused_row (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    (sameLedger : header.function.context.solvedRequirements = header.solved)
    {row : SolvedRequirement} (member : row ∈ header.solved) :
    row ∈ (rebuild header programTyped sameLedger).context.solvedRequirements := by
  rw [(rebuild header programTyped sameLedger).valid.ledger]
  exact member

theorem old_body_data (body : BuiltinNamedCalls.Body prepared values definitions program) :
    (Header.of_body body).slot = body.slot ∧
      (Header.of_body body).code = body.code ∧
      (Header.of_body body).bindings = body.bindings := ⟨rfl, rfl, rfl⟩

theorem old_body_valid (body : BuiltinNamedCalls.Body prepared values definitions program) :
    (Header.of_body body).valid = CompatibleRuntimeContextValidity.of_ordinary body.valid := rfl
end Rebuild

section LegacyProfiles
variable {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {diagnosticPolicy : AssignmentDiagnosticPolicy}

theorem ordinary_profile
    (profile : ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults) :
    CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence :=
  profile.initialValid

theorem same_match_condition
    (profile : ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax administrative registry faults) :
    profile.to_match.initialValid = profile.initialValid := rfl
end LegacyProfiles

/-- Runtime validity of the same full ledger cannot reconstruct the ordinary
condition required by the legacy profile. -/
abbrev runtime_not_ordinary := SourceCoreRecursiveNamedLexicalRuntimeBounds.runtime_not_ordinary

end Tests.SourceCoreRecursiveNamedRuntimeHeaders
end
