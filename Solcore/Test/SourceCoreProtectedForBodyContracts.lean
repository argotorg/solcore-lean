import Solcore.SourceSemantics.CoreLowering.ProtectedForGenericEndpoint
import Solcore.SourceSemantics.CoreLowering.NamedLoopStatements
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Actual guarded for endpoints consume the concrete named condition and
recursive body certificates. Empty post semantics are proved directly here;
full protected header/post Trees are a subsequent unit. Cached Core cases
retain ordered effects, exact faults, duplicate metadata, aliases and resume. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedForBodyContracts
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

theorem empty_post_preserves : ProtectedFor.Body.PostPreserves functions program evidence
    (entry := entry) (registry := registry) (source := source) (context := context) (scope := scope)
    (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
    (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
    (contextLocation := contextLocation) (location := location) (type := type)
    (conditionCode := conditionCode) (body := body) (selfReason := selfReason) [] (LocalLoop.fallthrough type) := by
  intro mapping world before after store finalContext finalEnvironment state continued trace
  cases trace
  exact ⟨store, mapping, world, empty_post_evaluates continued store,
    state.1.heaps, .refl _, .refl _, .refl _ _, .refl _⟩

theorem empty_post_faults : ProtectedFor.Body.PostFaults functions program evidence
    (entry := entry) (registry := registry) (source := source) (context := context) (scope := scope)
    (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
    (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
    (contextLocation := contextLocation) (location := location) (type := type)
    (conditionCode := conditionCode) (body := body) (selfReason := selfReason) (faults := faults) [] (LocalLoop.fallthrough type) := by
  intro mapping world before after store finalContext reason state continued trace
  cases trace

theorem empty_post_reflects : ProtectedFor.Body.PostReflects functions program evidence
    (entry := entry) (registry := registry) (source := source) (context := context) (scope := scope)
    (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
    (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
    (contextLocation := contextLocation) (location := location) (type := type)
    (conditionCode := conditionCode) (body := body) (selfReason := selfReason) faults [] (LocalLoop.fallthrough type) := by
  intro mapping world before store finalStore value state continued evaluated
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (empty_post_evaluates continued store)
  exact .inl ⟨context, environment, before, mapping, world, .nil, rfl,
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
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code (LocalLoop.fallthrough type) reason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedFor.Body.LoopPreserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      condition [] statements expected type (LocalLoop.iterate type conditionCode code (LocalLoop.fallthrough type) reason) := by
  apply ProtectedFor.Body.loop_preserves functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    conditionFound conditionTree nativeTyped unique
    (NamedLoopStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing body)
  · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid
    exact empty_post_preserves functions program evidence
  · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid
    exact empty_post_faults functions program evidence
include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_empty_post_reflects {context : SourceSemantics.Context} {scope : Scope}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {reason : Word} {administrative : Core.Context}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code (LocalLoop.fallthrough type) reason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedFor.Body.LoopReflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      condition [] statements expected type (LocalLoop.iterate type conditionCode code (LocalLoop.fallthrough type) reason) := by
  apply ProtectedFor.Body.loop_reflects functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing)
    conditionFound conditionTree nativeTyped
    (NamedLoopStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing body)
    (fun executed => body.control_not_fault unique executed)
  intro actualContext environment canonical actual ξ contextLocation location agrees reference valid
  exact empty_post_reflects functions program evidence
end Concrete

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
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected guarded for contracts resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected guarded for contracts fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected guarded for contracts exact fault binder missing")

private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected guarded for contracts inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected guarded for contracts missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected guarded for contracts raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 3]? with
    | some cell => pure cell | none => throw (IO.userError "protected guarded for contracts missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected guarded for contracts writes changed {name}"
  match final.heap[initial.heap.length + 2]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected guarded for contracts captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 1, initial.heap.length])
      s!"protected guarded for contracts captured source aliases changed {name}"
  | other => throw (IO.userError s!"protected guarded for contracts lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected guarded for contracts" content
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
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"protected guarded for result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected guarded for success {name}: {reprStr other}")
    for (name, exactGap, updated, counter) in [("bodyFault",gap,12,0), ("postFault",gap,15,0),
        ("conditionFault",conditionGap,16,3), ("initializerFault",gap,13,0)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == exactGap) s!"protected guarded for exact fault {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected guarded for failure {name}: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "protected guarded for resume changed observations"
  IO.println "protected guarded for contracts: shared finite for proof, concrete guarded condition/body, nested for/while, break skips post, continue runs post, initializer/condition/body/post first faults, raw duplicate/capture aliases and resume GREEN"

end Tests.SourceCoreProtectedForBodyContracts
