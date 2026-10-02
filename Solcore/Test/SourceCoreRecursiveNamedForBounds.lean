import Solcore.SourceSemantics.CoreLowering.ProtectedForGenericEndpoint
import Solcore.SourceSemantics.CoreLowering.NamedLoopStatements
import Solcore.Test.SourceCoreUnifiedCorpusSupport

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

private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"fixed-budget guarded for inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "fixed-budget guarded for missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"fixed-budget guarded for raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 3]? with
    | some cell => pure cell | none => throw (IO.userError "fixed-budget guarded for missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"fixed-budget guarded for writes changed {name}"
  match final.heap[initial.heap.length + 2]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"fixed-budget guarded for captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 1, initial.heap.length])
      s!"fixed-budget guarded for captured source aliases changed {name}"
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
  IO.println "fixed-budget guarded for: original source/native size, fixed-budget condition/body/post, shared finite for proof, nested for/while, break skips post, continue runs post, initializer/condition/body/post first faults, raw duplicate/capture aliases and resume GREEN"

end Tests.SourceCoreRecursiveNamedForBounds
