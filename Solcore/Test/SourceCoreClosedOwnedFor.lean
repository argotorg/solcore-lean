import Solcore.Test.SourceCoreClosedOwnedWhile
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForReflection

/-! Closed for consumers derive literal/closed lexical callbacks, use real nil
post and header receipts, and construct an actual false-condition completion.
No expression, body, or assignment meaning family is assumed. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedFor
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open ProtectedStateTransition
open Tests.SourceCoreClosedOwnedWhile (booleans boolean_preserves_at boolean_reflects_at)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

section NilPost
variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming} {contextLocation location : Location}
  {type : Ty} {conditionCode bodyCode : Expr} {reason : Word}

private theorem nil_post_preserves (size : Nat) :
    ProtectedFor.Body.Stateful.PostPreservesAt (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := compiled.indexed.ancestry.layout.frame)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type) (conditionCode := conditionCode)
      (body := bodyCode) (selfReason := reason) [] (LocalLoop.fallthrough type) := by
  intro mapping world before after store finalContext finalEnvironment state native _read _guarded continued trace
  cases trace
  refine ⟨store, mapping, world, ?_, ⟨state.live.heaps, .refl _, .refl _, .refl _ _, .refl _⟩, state, ?_⟩
  · rw [TypedImperativeFor.post_rename]
    simpa only [LoopRenaming.fallthrough] using
      LocalLoop.fallthrough_evaluates type (TypedImperativeFor.postValues type location continued ++ actual) store
  · exact (protocol headers keys).refl state.retained

private theorem nil_post_faults (size : Nat) :
    ProtectedFor.Body.Stateful.PostFaultsAt (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := compiled.indexed.ancestry.layout.frame)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type) (conditionCode := conditionCode)
      (body := bodyCode) (selfReason := reason) [] (LocalLoop.fallthrough type) := by
  intro mapping world before after store finalContext reason state native _read _guarded continued trace
  cases trace

private theorem nil_post_reflects (size : Nat) :
    ProtectedFor.Body.Stateful.PostReflectsAt (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := compiled.indexed.ancestry.layout.frame)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type) (conditionCode := conditionCode)
      (body := bodyCode) (selfReason := reason) faults [] (LocalLoop.fallthrough type) := by
  intro mapping world before store finalStore value state native _read _guarded continued evaluated
  have pure : Evaluates (TypedImperativeFor.postValues type location continued ++ actual) store
      (ForLoop.postCode ((LocalLoop.fallthrough type).rename ξ)) (LocalLoop.fallthroughValue type) store := by
    rw [TypedImperativeFor.post_rename]
    simpa only [LoopRenaming.fallthrough] using
      LocalLoop.fallthrough_evaluates type (TypedImperativeFor.postValues type location continued ++ actual) store
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound pure
  exact Or.inl ⟨SourceExecutionSize.stepSize [], context, environment, before, mapping, world, .nil, rfl,
    ⟨state.live.heaps, .refl _, .refl _, .refl _ _, .refl _⟩, state, (protocol headers keys).refl state.retained⟩
end NilPost

section For
variable {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
  (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {bodyCode conditionCode : Expr} {reason : Word}
  {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
  (found : source.lookupStatement? id = some node) (form : node.form = .forLoop [] condition [] statements)
  (conditionFound : source.lookupExpression? condition = some conditionNode)
  (conditionReceipt : booleans source scope condition ⟨.bool, conditionCode⟩)
  (codeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
    (LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason) (LocalLoop.resultType type) ambient.definitions)
  (tree : GenericLexicalStatements.Tree compiled.indexed.layouts owner active compiled.indexed.ancestry.layout.frame
    globals onError values source Tests.SourceCoreClosedOwnedLexicalBody.noExpressions context scope false statements expected type bodyCode)
  (admission : GenericLexicalStatements.Syntax source Tests.SourceCoreClosedOwnedLexicalBody.noExpressionSyntax context false statements expected)
  (unique : NodeOccurrencesUnique source)


include definitions registered conditionFound conditionReceipt codeTyped tree unique in
/-- The literal and closed lexical Tree supply every smaller preservation
callback; the nil post's real source trace supplies its exact unchanged state. -/
theorem closed_loop_preserves_at (budget size : Nat) (within : size ≤ budget) :
    ProtectedFor.Body.Stateful.LoopPreservesAtFor (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      functions program evidence (fun _ => True) size (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition [] statements expected type
      (LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason) := by
  have bodies : RecursiveNamedLoopContracts.Below budget (fun child => ProtectedStateTransition.Lexical.Gated.PreservesAtFor
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program evidence (fun _ => True)
      child (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type bodyCode) := by
    intro child _
    exact RecursiveNamedImperativeLexicalBounds.Stateful.preserves_at_for
      (functions := functions) (program := program) (evidence := evidence)
      (protocol := protocol headers keys) (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (administrative := administrative) (fun _ => True)
      (Tests.SourceCoreClosedOwnedLexicalBody.closed_tree_preserves_at functions evidence definitions registered tree child unique)
  exact ProtectedFor.Body.Stateful.loop_preserves_bounded_for
    (protocol := protocol headers keys) (guard := CallableIndexedOwnedAllocationProducer.StableOwner keys)
    functions program evidence (administrativeTransport headers keys) (fun _ => True) budget
    (fun child _ => boolean_preserves_at functions evidence child unique)
    conditionFound conditionReceipt codeTyped unique bodies
    (fun _ _ _ child _ => nil_post_preserves functions evidence child)
    (fun _ _ _ child _ => nil_post_faults functions evidence child)
    size within

include definitions registered conditionFound conditionReceipt codeTyped tree admission unique in
/-- Native loop reflection uses independently graded literal and closed Tree
proofs; its nil post is reconstructed from the actual pure completion. -/
theorem closed_loop_reflects_at (budget size : Nat) (within : size ≤ budget) :
    ProtectedFor.Body.Stateful.LoopReflectsAtFor (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      functions program evidence (fun _ => True) size (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition [] statements expected type
      (LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason) := by
  have bodies : RecursiveNamedLoopContracts.Below budget (fun child => ProtectedStateTransition.Lexical.Gated.ReflectsAtFor
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program evidence (fun _ => True)
      child (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type bodyCode) := by
    intro child _
    exact RecursiveNamedImperativeLexicalBounds.Stateful.reflects_at_for
      (functions := functions) (program := program) (evidence := evidence)
      (protocol := protocol headers keys) (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (administrative := administrative) (fun _ => True)
      (Tests.SourceCoreClosedOwnedLexicalBody.closed_tree_reflects_at functions evidence definitions registered tree child)
  have bodyCannotFault : ∀ {actualProgram actualContext actualEvidence actualEnvironment before after finalContext reason},
      Dynamic.StatementsExecute actualProgram actualContext actualEvidence source actualEnvironment before statements finalContext (.fault reason) after → False := by
    intro actualProgram actualContext actualEvidence actualEnvironment before after finalContext reason trace
    exact GenericLexicalStatements.control_not_fault admission unique trace
  exact ProtectedFor.Body.Stateful.loop_reflects_bounded_for
    (protocol := protocol headers keys) (guard := CallableIndexedOwnedAllocationProducer.StableOwner keys)
    functions program evidence (administrativeTransport headers keys) (fun _ => True) budget
    (fun child _ => boolean_reflects_at functions evidence child)
    conditionFound conditionReceipt codeTyped bodies bodyCannotFault
    (fun _ _ _ child _ => nil_post_reflects functions evidence child)
    size within
include definitions registered found form conditionFound conditionReceipt codeTyped tree admission unique in
/-- Native completion independently reconstructs source control and its pool. -/
theorem closed_for_reflects (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : EvaluationSize size actual store ((LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      TypedLexicalWhile.Restored environment outcome ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        Transition (protocol headers keys) initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  let continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop :=
    fun nextContext nextScope nextCode => nextContext = context ∧ nextScope = scope ∧
      nextCode = LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason
  have loopCorrect : ∀ {nextContext nextScope nextCode}, continuation nextContext nextScope nextCode →
      RecursiveNamedHeaderContracts.AtMost budget (fun child => ProtectedFor.Body.Stateful.LoopReflectsAtFor
        (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program evidence
        (fun _ => True) child (source := source) (context := nextContext) (registry := registry) (faults := faults)
        (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
        (scope := nextScope) condition [] statements expected type nextCode) := by
    intro nextContext nextScope nextCode receipt child bounded
    obtain ⟨rfl, rfl, rfl⟩ := receipt
    exact closed_loop_reflects_at functions evidence definitions registered conditionFound conditionReceipt codeTyped
      tree admission unique budget child bounded
  let tail : ProtectedForHeader.Stateful.TailFor (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ => True) registry functions source [] evidence administrative compiled.indexed.ancestry.layout.frame globals
      contextLocation native continuation context environment before :=
    ⟨⟨scope, LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason,
      mapping, world, canonical, actual, actualContext, ξ, store, ⟨rfl, rfl, rfl⟩, trivial,
      environments, heaps, locals, agrees, typed, reference, read, unmapped⟩, initial, seed⟩
  have headerResult := ProtectedForHeader.Stateful.ResultAtFor.nil (program := program) (type := type) (faults := faults) tail evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps, maps, worlds, frame, heapMetadata, final, related⟩ :=
    RecursiveNamedImperativeFor.Stateful.header_reflects_at_with_result
      (functions := functions) (program := program) (evidence := evidence) (protocol := protocol headers keys)
      (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys) (validity := fun _ => True) (budget := budget)
      size within found form loopCorrect initial headerResult
  obtain ⟨prefixes, snapshots, _oldMembers⟩ := Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps,
    maps, worlds, frame, heapMetadata, final, related, prefixes, snapshots, ⟨final, related⟩⟩

include codeTyped in
/-- The actual false loop installs its captured self closure, skips its body,
and keeps every row's exact record list. -/
theorem false_for_keeps_records
    (falseCode : conditionCode = LanguageResult.success (.bool false))
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping) :
    let finalStore := TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ)
      (LocalLoop.fallthrough type) reason actual
    let finalWorld := TypedLexicalWhile.installedWorld world type
    ∃ final : State headers keys ⟨scope, mapping, finalWorld, before, finalStore, canonical⟩,
      Evaluates actual store ((LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason).rename ξ)
        (LocalLoop.fallthroughValue type) finalStore ∧
      Relates initial final ∧ records final = records initial ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping finalWorld before finalStore ∧
      finalStore.read? store.length = some (.inRight .unit
        (LocalLoop.installedClosure type (conditionCode.rename ξ) (bodyCode.rename ξ)
          (LocalLoop.fallthrough type) reason store.length actual)) ∧
      store.length ∉ mapping ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native) ∧
      CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native ∧
      (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        compiled.indexed.ancestry.layout.frame mapping finalStore record) := by
  obtain ⟨activation, progress, related, sameRecords⟩ :=
    ProtectedStateTransition.For.initial_state (protocol := protocol headers keys)
      (administrativeTransport headers keys) environments heaps locals agrees typed read unmapped codeTyped initial
  simp only [LoopRenaming.fallthrough] at activation progress related sameRecords
  have conditionEval : Evaluates (Core.LoopExecution.entryEnvironment type store.length actual)
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (LocalLoop.fallthrough type) reason actual)
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) (.inRight .word (.bool false))
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (LocalLoop.fallthrough type) reason actual) := by
    rw [falseCode]
    simp only [Core.LoopExecution.conditionCode, LanguageResult.success, Expr.weakenAt, Expr.rename]
    exact .inRight .bool
  have nativeTrace := Core.LoopExecution.condition_false (type := type) (body := bodyCode.rename ξ)
    (post := LocalLoop.fallthrough type) (selfReason := reason) conditionEval
  refine ⟨activation.retained, ?_, related, sameRecords, progress.1, activation.live.selfRead,
    activation.live.selfUnmapped, (TypedLexicalWhile.retain unmapped read progress.2.2.2.1).2,
    ⟨selected, ghost, metadata, physicalOwner, stable⟩, ?_⟩
  · rw [LoopRenaming.iterate]
    apply LocalLoop.iterate_evaluates
    exact LocalLoop.invoke_success _ _ (.var rfl) activation.live.selfRead nativeTrace
  · intro row record member
    exact record_snapshot activation.retained row member

include definitions registered found form conditionFound conditionReceipt codeTyped tree admission unique in
/-- A constructed false-loop completion reaches the shared reflection fold;
neither an evaluation nor a source execution is assumed. -/
theorem false_for_reflection_exists
    (falseCode : conditionCode = LanguageResult.success (.bool false))
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping) :
    let finalStore := TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ)
      (LocalLoop.fallthrough type) reason actual
    ∃ nativeSize sourceSize outcome after finalMap finalWorld,
      EvaluationSize nativeSize actual store ((LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason).rename ξ)
        (LocalLoop.fallthroughValue type) finalStore ∧
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      TypedLexicalWhile.Restored environment outcome ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome (LocalLoop.fallthroughValue type) ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) := by
  obtain ⟨_installed, evaluated, _observations⟩ := false_for_keeps_records
    (headers := headers) (keys := keys) functions codeTyped falseCode initial selected physicalOwner stable
    environments heaps locals agrees typed read unmapped
  obtain ⟨nativeSize, completed⟩ := evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, _heaps, _maps, _worlds, _frame, _metadata,
      final, related, prefixes, snapshots, _transition⟩ :=
    closed_for_reflects (headers := headers) (keys := keys) functions evidence definitions registered
      found form conditionFound conditionReceipt codeTyped tree admission unique nativeSize nativeSize (Nat.le_refl _)
      initial selected physicalOwner stable environments heaps locals agrees typed reference read unmapped completed
  exact ⟨nativeSize, sourceSize, outcome, after, finalMap, finalWorld, completed, trace, restored, represented,
    final, related, prefixes, snapshots⟩

end For
end Tests.SourceCoreClosedOwnedFor
