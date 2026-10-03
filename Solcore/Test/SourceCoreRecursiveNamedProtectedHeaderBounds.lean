import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderPost
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedForContracts
import Solcore.SourceSemantics.CoreLowering.NamedLoopStatements
import Solcore.Test.SourceCoreUnifiedCorpusSupport

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
