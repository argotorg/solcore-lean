import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalTreeBounds
import Solcore.Test.SourceCoreClosedOwnedWhile

/-! A genuine literal-false while and static nil body construct Source and
native completions internally. Actual admission reaches the self-cell
activation and the exact returned pool; every ordered row stays observable. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedAdmittedWhile
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open Tests.SourceCoreClosedOwnedLexicalBody (noExpressions reached_pool_observations)
open Tests.SourceCoreClosedOwnedWhile (booleans boolean_preserves_at boolean_reflects_at)
open RecursiveNamedLexicalContracts.Stateful.WithReady

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

private abbrev bridge := CallableIndexedOwnedIndirectCallerProtocol.of_legacy
  (CallableIndexedOwnedCallerProtocol.base (headers := headers) (keys := keys))

private def ownedProducer {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (same : compiled.indexed.layouts.definitions = definitions) :
    OrdinaryAllocation.Producer (protocol headers keys) compiled.indexed.layouts
      compiled.indexed.ancestry.layout.frame model := by
  subst definitions
  exact CallableIndexedOwnedAllocationProducer.producer headers keys model

private theorem acquire {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (same : compiled.indexed.layouts.definitions = definitions) (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (ownedProducer (headers := headers) (keys := keys) model same) location native := by
  subst definitions
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner model stable

private theorem false_literal_facts {node : ExpressionNode}
    (literal : CompatibleExpressionLiterals.Literal [] node .bool (LanguageResult.success (.bool false))) :
    ∃ name, node.form = .reference name (.builtinBoolean false) ∧ node.type = .bool ∧
      node.requirements = [] ∧ node.coercions = [] := by
  cases literal with
  | bool value form type requirements coercions => exact ⟨_, form, type, requirements, coercions⟩

private theorem false_expression {source : TypedSource} {condition : ExpressionId} {node : ExpressionNode}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (found : source.lookupExpression? condition = some node)
    (literal : CompatibleExpressionLiterals.Literal [] node .bool (LanguageResult.success (.bool false))) :
    ∃ size, SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before condition (.bool false) before := by
  obtain ⟨name, form, _type, requirements, coercions⟩ := false_literal_facts literal
  refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [], SourceExecutionSize.stepSize []],
    .intro (raw := .bool false) (middle := before) (lookupExpression?_sound found) ?_ ?_⟩
  · rw [form]
    exact .builtinBoolean (by simp [Dynamic.OrdinaryRequirementLayout, requirements, coercions, coercionRequirementIds])
  · rw [coercions]
    exact .nil

section Loop
variable {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
  (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
  {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
  (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition [])
  (conditionFound : source.lookupExpression? condition = some conditionNode)
  (conditionLiteral : CompatibleExpressionLiterals.Literal [] conditionNode .bool (LanguageResult.success (.bool false)))
  (codeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
    (LocalLoop.whileLoop type (LanguageResult.success (.bool false)) (LocalLoop.fallthrough type) reason)
    (LocalLoop.resultType type) ambient.definitions)
  (sourceTyped : ProtectedStateImperativeTypedSourceSites.Head source context id)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)

include conditionLiteral sourceTyped unique found form conditionFound in
private theorem parent_facts :
    ProtectedStateImperativeTypedSourceSites.HeadFacts source (fun _ => True) context id expected := by
  obtain ⟨_name, _form, conditionType, _requirements, _coercions⟩ := false_literal_facts conditionLiteral
  obtain ⟨conditionTyped, _bodyTyped⟩ := ProtectedStateImperativeTypedSourceSites.while_loop unique sourceTyped found form
  obtain ⟨control, final, facts, typed⟩ := sourceTyped
  exact ⟨false, [], .whileLoop found form conditionFound conditionType (by simpa only [conditionType] using conditionTyped)
    trivial (.body (.nil (.inl rfl))) (.body (.nil (.inl rfl))), control, final, _, .singleton typed⟩

include conditionLiteral conditionFound in
private theorem condition_receipt :
    booleans source scope condition ⟨.bool, LanguageResult.success (.bool false)⟩ := by
  obtain ⟨name, form, _type, _requirements, _coercions⟩ := false_literal_facts conditionLiteral
  exact ⟨conditionNode, name, false, conditionFound, form, conditionLiteral⟩

include definitions registered unique owner active onError in
private theorem nil_preserves (size : Nat) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
      (protocol headers keys) (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts source (fun _ => True))
      (validity := fun _ => True) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := compiled.indexed.ancestry.layout.frame)
      (globals := globals) (administrative := administrative) (scope := scope)
      size false [] expected type (LocalLoop.fallthrough type) := by
  have correct := CallableIndexedOwnedAdmittedLexicalTreeBounds.preserves_at_for (faults := faults) (expressionSyntax := fun _ => True) (bridge (headers := headers) (keys := keys))
    functions definitions registered evidence (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ownedProducer (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (acquire (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions) unique
    (fun _ => True) (fun _ _ => trivial) size size (Nat.le_refl _)
    (fun child within context valid => by intro scope id lowered impossible; cases impossible)
    (GenericLexicalStatements.Tree.nil (layouts := compiled.indexed.layouts) (owner := owner)
      (active := active) (frame := compiled.indexed.ancestry.layout.frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressions := noExpressions)
      (context := context) (scope := scope) (mode := false) (expected := expected) (type := type) (.inl rfl))
  intro valid _facts mapping world actualContext environment canonical actual before after store ξ location native outcome finalContext
    environments heaps locals agrees typed reference read unmapped initial stable admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
      frame, metadata, lexical, reached⟩ :=
    correct valid (.nil (.inl rfl)) environments heaps locals agrees typed reference read unmapped initial stable admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, TypedLexicalWhile.FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩

include definitions registered unique owner active onError in
private theorem nil_reflects (size : Nat) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
      (protocol headers keys) (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts source (fun _ => True))
      (validity := fun _ => True) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := compiled.indexed.ancestry.layout.frame)
      (globals := globals) (administrative := administrative) (scope := scope)
      size false [] expected type (LocalLoop.fallthrough type) := by
  have correct := CallableIndexedOwnedAdmittedLexicalTreeBounds.reflects_at_for (faults := faults) (expressionSyntax := fun _ => True) (bridge (headers := headers) (keys := keys))
    functions definitions registered evidence (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ownedProducer (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (acquire (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions) unique
    (fun _ => True) (fun _ _ => trivial) size size (Nat.le_refl _)
    (fun child within context valid => by intro scope id lowered impossible; cases impossible)
    (GenericLexicalStatements.Tree.nil (layouts := compiled.indexed.layouts) (owner := owner)
      (active := active) (frame := compiled.indexed.ancestry.layout.frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressions := noExpressions)
      (context := context) (scope := scope) (mode := false) (expected := expected) (type := type) (.inl rfl))
  intro valid _facts mapping world actualContext environment canonical actual before store finalStore ξ location native value
    environments heaps locals agrees typed reference read unmapped initial stable admitted completed
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, lexical, reached⟩ :=
    correct valid (.nil (.inl rfl)) environments heaps locals agrees typed reference read unmapped initial stable admitted completed
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, TypedLexicalWhile.FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩

include definitions registered owner active onError found form conditionFound conditionLiteral codeTyped
  sourceTyped unique wellFormed runtime covers in
/-- A literal constructs the genuine false Source prefix. The admitted while
producer returns the same actual pool, successful deep typing and snapshots;
no execution or body meaning is assumed. -/
theorem source_false_exists
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : CallableIndexedOwnedSourceAdmission.Admission (bridge (headers := headers) (keys := keys)) context initial)
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
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id
        context (.fallthrough environment) before ∧
      Evaluates actual store ((LocalLoop.whileLoop type (LanguageResult.success (.bool false))
        (LocalLoop.fallthrough type) reason).rename ξ) value finalStore ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fallthrough environment) value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld before finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before before ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, before, finalStore, canonical⟩,
        Relates initial reached ∧ CallableIndexedOwnedSourceAdmission.Admission (bridge (headers := headers) (keys := keys)) context reached ∧
        (∀ row, RecordPrefix (records initial row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds
          compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records initial row → record ∈ records reached row) := by
  obtain ⟨expressionSize, expressionTrace⟩ := false_expression (program := program)
    (context := context) (evidence := evidence) (environment := environment) (before := before)
    conditionFound conditionLiteral
  let sourceSize := SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [expressionSize]]
  have trace : RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment
      before id context (.fallthrough environment) before :=
    .control (.whileLoop (lookupStatement?_sound found) form (.done expressionTrace))
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  have conditionMeaning : RecursiveNamedLoopContracts.Below sourceSize (fun child =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) (keys := keys))
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (booleans source) faults child) := by
    intro child _smaller
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful wellFormed runtime covers
      (boolean_preserves_at (headers := headers) (keys := keys) functions evidence child unique)
  obtain ⟨_same, _restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, reachedReady⟩ :=
    CallableIndexedOwnedAdmittedWhileBounds.preserves_bounded_for (bridge (headers := headers) (keys := keys))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions evidence (administrativeTransport headers keys)
      (fun _ => True) sourceSize conditionMeaning found form conditionFound
      (condition_receipt conditionFound conditionLiteral) codeTyped unique
      (fun child _smaller => nil_preserves (owner := owner) (active := active) (onError := onError)
        functions evidence definitions registered unique child)
      sourceSize (Nat.le_refl _) trivial
      (parent_facts found form conditionFound conditionLiteral sourceTyped unique)
      environments heaps locals agrees typed reference read unmapped initial seed admitted trace
  obtain ⟨prefixes, snapshots, members⟩ := reached_pool_observations related
  exact ⟨sourceSize, value, finalStore, finalMap, finalWorld, trace, evaluated, represented, finalHeaps,
    maps, worlds, frame, heapMetadata, reached, related, reachedReady, prefixes, snapshots, members⟩

include definitions registered owner active onError found form conditionFound conditionLiteral codeTyped
  sourceTyped unique wellFormed runtime covers in
/-- The original false-loop producer constructs its actual native self-cell
completion. Shared admitted reflection returns an independent Source grade
and the exact reached pool; its static nil Tree discharges control faults. -/
theorem native_false_exists
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : CallableIndexedOwnedSourceAdmission.Admission (bridge (headers := headers) (keys := keys)) context initial)
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
    let finalStore := TypedLexicalWhile.installedStore store type
      ((LanguageResult.success (.bool false)).rename ξ) ((LocalLoop.fallthrough type).rename ξ)
      (LocalLoop.fallthrough type) reason actual
    ∃ nativeSize sourceSize outcome after finalMap finalWorld,
      EvaluationSize nativeSize actual store ((LocalLoop.whileLoop type (LanguageResult.success (.bool false))
        (LocalLoop.fallthrough type) reason).rename ξ) (LocalLoop.fallthroughValue type) finalStore ∧
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id
        context outcome after ∧ TypedLexicalWhile.Restored environment outcome ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome (LocalLoop.fallthroughValue type) ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      finalStore.read? store.length = some (.inRight .unit
        (LocalLoop.installedClosure type ((LanguageResult.success (.bool false)).rename ξ)
          ((LocalLoop.fallthrough type).rename ξ) (LocalLoop.fallthrough type) reason store.length actual)) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native) ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PostReady (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys))) context outcome reached ∧
        (∀ row, RecordPrefix (records initial row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds
          compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records initial row → record ∈ records reached row) := by
  obtain ⟨_activation, evaluated, _activationRelated, _sameRecords, _activationHeap, selfRead,
      _selfUnmapped, frameRead, _stable, _snapshotHolds⟩ :=
    Tests.SourceCoreClosedOwnedWhile.false_loop_keeps_records (headers := headers) (keys := keys)
      functions codeTyped rfl initial selected physicalOwner stable environments heaps locals agrees typed read unmapped
  obtain ⟨nativeSize, completed⟩ := evaluation_has_size evaluated
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  have conditionMeaning : RecursiveNamedLoopContracts.Below nativeSize (fun child =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge (headers := headers) (keys := keys))
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (booleans source) faults child) := by
    intro child _smaller
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful wellFormed runtime covers
      (boolean_reflects_at (headers := headers) (keys := keys) functions evidence child)
  have bodyTree : GenericImperativeMatch.Tree compiled.indexed.layouts owner active
      compiled.indexed.ancestry.layout.frame globals onError values source (fun _ => True) noExpressions
      ambient.definitions administrative context scope (.statements false []) expected type (LocalLoop.fallthrough type) :=
    .body (.nil (.inl rfl)) (.nil (.inl rfl))
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, reachedReady⟩ :=
    CallableIndexedOwnedAdmittedWhileBounds.reflects_bounded_from_tree_for (bridge (headers := headers) (keys := keys))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions evidence (administrativeTransport headers keys)
      (fun _ => True) nativeSize conditionMeaning found form conditionFound
      (condition_receipt conditionFound conditionLiteral) codeTyped unique
      (fun child _smaller => nil_reflects (owner := owner) (active := active) (onError := onError)
        functions evidence definitions registered unique child) bodyTree
      nativeSize (Nat.le_refl _) trivial
      (parent_facts found form conditionFound conditionLiteral sourceTyped unique)
      environments heaps locals agrees typed reference read unmapped initial seed admitted completed
  obtain ⟨prefixes, snapshots, members⟩ := reached_pool_observations related
  exact ⟨nativeSize, sourceSize, outcome, after, finalMap, finalWorld, completed, trace, restores, represented,
    finalHeaps, maps, worlds, frame, heapMetadata, selfRead, frameRead, reached, related, reachedReady,
    prefixes, snapshots, members⟩

end Loop
end Tests.SourceCoreClosedAdmittedWhile
