import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalTreeBounds
import Solcore.Test.SourceCoreClosedOwnedFor

/-! A genuine literal-false for loop, static nil body and nil post construct
Source and native completions internally. Actual admission follows the real
self-cell activation and returned pool; every ordered row stays observable. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedAdmittedFor
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
    ProtectedFor.Body.Stateful.WithReady.PostPreservesAt (protocol headers keys) (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := compiled.indexed.ancestry.layout.frame)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type) (conditionCode := conditionCode)
      (body := bodyCode) (selfReason := reason) [] (LocalLoop.fallthrough type) := by
  intro mapping world before after store finalContext finalEnvironment state native _read _guarded ready continued trace
  cases trace
  refine ⟨store, mapping, world, ?_, ⟨state.live.heaps, .refl _, .refl _, .refl _ _, .refl _⟩, state, ?_⟩
  · rw [TypedImperativeFor.post_rename]
    simpa only [LoopRenaming.fallthrough] using
      LocalLoop.fallthrough_evaluates type (TypedImperativeFor.postValues type location continued ++ actual) store
  · exact ⟨(protocol headers keys).refl state.retained, ready⟩

private theorem nil_post_faults (size : Nat) :
    ProtectedFor.Body.Stateful.WithReady.PostFaultsAt (protocol headers keys) (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := compiled.indexed.ancestry.layout.frame)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type) (conditionCode := conditionCode)
      (body := bodyCode) (selfReason := reason) [] (LocalLoop.fallthrough type) := by
  intro mapping world before after store finalContext reason state native _read _guarded ready continued trace
  cases trace

private theorem nil_post_reflects (size : Nat) :
    ProtectedFor.Body.Stateful.WithReady.PostReflectsAt (protocol headers keys) (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := compiled.indexed.ancestry.layout.frame)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type) (conditionCode := conditionCode)
      (body := bodyCode) (selfReason := reason) faults [] (LocalLoop.fallthrough type) := by
  intro mapping world before store finalStore value state native _read _guarded ready continued evaluated
  have pure : Evaluates (TypedImperativeFor.postValues type location continued ++ actual) store
      (ForLoop.postCode ((LocalLoop.fallthrough type).rename ξ)) (LocalLoop.fallthroughValue type) store := by
    rw [TypedImperativeFor.post_rename]
    simpa only [LoopRenaming.fallthrough] using
      LocalLoop.fallthrough_evaluates type (TypedImperativeFor.postValues type location continued ++ actual) store
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound pure
  exact Or.inl ⟨SourceExecutionSize.stepSize [], context, environment, before, mapping, world, .nil, rfl,
    ⟨state.live.heaps, .refl _, .refl _, .refl _ _, .refl _⟩, state, (protocol headers keys).refl state.retained, ready⟩
end NilPost

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
  (found : source.lookupStatement? id = some node) (form : node.form = .forLoop [] condition [] [])
  (conditionFound : source.lookupExpression? condition = some conditionNode)
  (conditionLiteral : CompatibleExpressionLiterals.Literal [] conditionNode .bool (LanguageResult.success (.bool false)))
  (codeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
    (LocalLoop.iterate type (LanguageResult.success (.bool false)) (LocalLoop.fallthrough type) (LocalLoop.fallthrough type) reason)
    (LocalLoop.resultType type) ambient.definitions)
  (sourceTyped : ProtectedStateImperativeTypedSourceSites.Head source context id)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)

include conditionLiteral sourceTyped unique found form conditionFound in
private theorem loop_facts :
    CallableIndexedOwnedAdmittedForBounds.LoopFacts source (fun _ => True) context condition [] [] expected := by
  obtain ⟨_name, _form, conditionType, _requirements, _coercions⟩ := false_literal_facts conditionLiteral
  obtain ⟨control, loopContext, postContext, bodyFinal, bodyFacts,
    initializerTyped, conditionTyped, bodyTyped, postTyped⟩ :=
    ProtectedStateImperativeTypedSourceSites.for_loop unique sourceTyped found form
  cases initializerTyped
  exact CallableIndexedOwnedAdmittedForBounds.LoopFacts.of_done
    (.initializersDone conditionFound conditionType (by simpa only [conditionType] using conditionTyped)
      trivial (.body (.nil (.inl rfl))) .nil) bodyTyped postTyped

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
/-- A literal constructs the genuine false Source prefix. The admitted for
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
    let finalStore := TypedLexicalWhile.installedStore store type
      ((LanguageResult.success (.bool false)).rename ξ) ((LocalLoop.fallthrough type).rename ξ)
      (LocalLoop.fallthrough type) reason actual
    ∃ sourceSize finalMap finalWorld,
      RecursiveNamedForContracts.ForOutcome program sourceSize context evidence source environment before condition [] [] (.fallthrough environment) before ∧
      Evaluates actual store ((LocalLoop.iterate type (LanguageResult.success (.bool false))
        (LocalLoop.fallthrough type) (LocalLoop.fallthrough type) reason).rename ξ) (LocalLoop.fallthroughValue type) finalStore ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fallthrough environment) (LocalLoop.fallthroughValue type) ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld before finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before before ∧
      finalStore.read? store.length = some (.inRight .unit
        (LocalLoop.installedClosure type ((LanguageResult.success (.bool false)).rename ξ)
          ((LocalLoop.fallthrough type).rename ξ) (LocalLoop.fallthrough type) reason store.length actual)) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native) ∧
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
  let sourceSize := SourceExecutionSize.stepSize [expressionSize]
  have trace : RecursiveNamedForContracts.ForOutcome program sourceSize context evidence source environment
      before condition [] [] (.fallthrough environment) before := .control (.done expressionTrace)
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  have conditionMeaning : RecursiveNamedLoopContracts.Below sourceSize (fun child =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) (keys := keys))
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (booleans source) faults child) := by
    intro child _smaller
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful wellFormed runtime covers
      (boolean_preserves_at (headers := headers) (keys := keys) functions evidence child unique)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, reachedReady⟩ :=
    CallableIndexedOwnedAdmittedForBounds.loop_preserves_bounded_for (bridge (headers := headers) (keys := keys))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions evidence (administrativeTransport headers keys)
      (fun _ => True) sourceSize conditionMeaning
      (loop_facts found form conditionFound conditionLiteral sourceTyped unique) conditionFound
      (condition_receipt conditionFound conditionLiteral) codeTyped unique
      (fun child _smaller => nil_preserves (owner := owner) (active := active) (onError := onError)
        functions evidence definitions registered unique child)
      (fun _ _ _ child _ => nil_post_preserves functions evidence child)
      (fun _ _ _ child _ => nil_post_faults functions evidence child)
      sourceSize (Nat.le_refl _) trivial
      environments heaps locals agrees typed reference read unmapped initial seed admitted trace
  obtain ⟨_activation, nativeEvaluation, _activationRelated, _sameRecords, _activationHeap, selfRead,
      _selfUnmapped, frameRead, _stable, _snapshotHolds⟩ :=
    Tests.SourceCoreClosedOwnedFor.false_for_keeps_records (headers := headers) (keys := keys)
      functions codeTyped rfl initial selected physicalOwner stable environments heaps locals agrees typed read unmapped
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated nativeEvaluation
  obtain ⟨prefixes, snapshots, members⟩ := reached_pool_observations related
  exact ⟨sourceSize, finalMap, finalWorld, trace, evaluated, represented, finalHeaps,
    maps, worlds, frame, heapMetadata, selfRead, frameRead, reached, related, reachedReady, prefixes, snapshots, members⟩

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
      EvaluationSize nativeSize actual store ((LocalLoop.iterate type (LanguageResult.success (.bool false))
        (LocalLoop.fallthrough type) (LocalLoop.fallthrough type) reason).rename ξ) (LocalLoop.fallthroughValue type) finalStore ∧
      RecursiveNamedForContracts.ForOutcome program sourceSize context evidence source environment before condition [] [] outcome after ∧
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
    Tests.SourceCoreClosedOwnedFor.false_for_keeps_records (headers := headers) (keys := keys)
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
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, reachedReady⟩ :=
    CallableIndexedOwnedAdmittedForBounds.loop_reflects_bounded_from_tree_for (bridge (headers := headers) (keys := keys))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions evidence (administrativeTransport headers keys)
      (fun _ => True) nativeSize conditionMeaning
      (loop_facts found form conditionFound conditionLiteral sourceTyped unique) conditionFound
      (condition_receipt conditionFound conditionLiteral) codeTyped unique
      (fun child _smaller => nil_reflects (owner := owner) (active := active) (onError := onError)
        functions evidence definitions registered unique child)
      (fun _ _ _ child _ => nil_post_reflects functions evidence child) bodyTree
      nativeSize (Nat.le_refl _) trivial
      environments heaps locals agrees typed reference read unmapped initial seed admitted completed
  obtain ⟨prefixes, snapshots, members⟩ := reached_pool_observations related
  exact ⟨nativeSize, sourceSize, outcome, after, finalMap, finalWorld, completed, trace, represented,
    finalHeaps, maps, worlds, frame, heapMetadata, selfRead, frameRead, reached, related, reachedReady,
    prefixes, snapshots, members⟩


end Loop
end Tests.SourceCoreClosedAdmittedFor
