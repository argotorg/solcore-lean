import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalTreeBounds
import Solcore.Test.SourceSemantics.CoreLowering.Closed.Owned
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedNamedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileBounds
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEmptyLambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicEmptyInputRegistry
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEmptyLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceOrigin
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyReadyCatalog
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

/-!
# Closed admitted tests

Admitted and ready loops, and closed lambdas through the public API.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreClosedAdmittedFor
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedAdmittedNamedReceipt
/-! A genuine named parameter receipt constructs the exact pointwise body
callback. Its closed static profile uses no expression leaves; the original
shared mutual proof and real nested allocation producer retain the actual
parameter pool, Source exit, and independently measured native completion. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreClosedAdmittedNamedReceipt
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open Tests.SourceCoreClosedOwnedLexicalBody (noExpressions noExpressionSyntax reached_pool_observations)
open Tests.SourceCoreClosedOwnedExpressionHead (PreparedReceipts layouts PoolObservations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- The full original named static profile, real Source parameter judgments,
hook history and actual parameter pool are retained together. -/
abbrev Receipt {index : Index} (argumentsPool : State headers keys index)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (arguments : List Dynamic.Value) :=
  CallableIndexedOwnedAdmittedNamedExpressionHeads.ParameterReceipt
    (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := fun _ => noExpressions) (expressionSyntax := fun _ => noExpressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) argumentsPool header arguments

variable {index : Index} {argumentsPool : State headers keys index}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {arguments : List Dynamic.Value}
  (receipt : Receipt (registry := registry) (faults := faults) functions owner argumentsPool header arguments)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (prepared : PreparedReceipts (headers := headers)) (member : header ∈ headers)
  (captureZero : owner.key.capturePrefix = 0)
  (globals : header.globals = compiled.indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

private def marked : MarkedAllocation.Producer
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
    header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  (layouts prepared member).symm ▸ CallableIndexedOwnedNestedCanonicalState.markedProducer owner header
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    (same : first = second)
    (producer : MarkedAllocation.Producer
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      second compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    {location : Location} {native : NativeFrame}
    (ready : OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    OrdinaryAllocation.ReadyAt ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (marked (registry := registry) functions owner prepared member).toOrdinary location native :=
  ready_layout (registry := registry) functions owner (layouts prepared member)
    (CallableIndexedOwnedNestedCanonicalState.markedProducer owner header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

include wellFormed prepared member extension faithful observations in
/-- The same existing mutual proof closes this real named origin internally.
The nested wrapper uses its actual catalog slots and authenticated hook seed. -/
theorem nested_preserves (size : Nat) :
    CallableRuntimeBodyEntryContracts.PreservesAt (registry := registry) (faults := faults) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions (Program.ofChecked compiled.sourceProgram)
      (receipt.nested_entry wellFormed captureZero globals).original size := by
  have meaning := CallableRuntimeBodyMutualMeaning.Stateful.preserves_at
    (fun (_ : Unit) => CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
    functions extension (Program.ofChecked compiled.sourceProgram) faithful observations
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => marked (registry := registry) functions owner prepared member)
    (fun _ => acquire (registry := registry) functions owner prepared member)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner header)
    (CallableIndexedOwnedNestedCanonicalState.bindings owner header)
    (by intro _ context valid budget child within below scope id lowered impossible; cases impossible)
    size ()
  intro outcome after trace
  exact meaning (receipt.nested_entry wellFormed captureZero globals).original trace

include wellFormed prepared member extension faithful observations functionTypes in
/-- Native reflection keeps its original completion size and independently
returns a Source body grade at the exact same wrapped parameter entry. -/
theorem nested_reflects (size : Nat) :
    CallableRuntimeBodyEntryContracts.ReflectsAt (registry := registry) (faults := faults) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions (Program.ofChecked compiled.sourceProgram)
      (receipt.nested_entry wellFormed captureZero globals).original size := by
  have meaning := CallableRuntimeBodyMutualMeaning.Stateful.reflects_at
    (fun (_ : Unit) => CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
    functions extension (Program.ofChecked compiled.sourceProgram) faithful observations functionTypes
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => marked (registry := registry) functions owner prepared member)
    (fun _ => acquire (registry := registry) functions owner prepared member)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner header)
    (CallableIndexedOwnedNestedCanonicalState.bindings owner header)
    (by intro _ context valid budget child within below scope id lowered impossible; cases impossible)
    size ()
  intro value finalStore completed
  exact meaning (receipt.nested_entry wellFormed captureZero globals).original completed

include wellFormed prepared member captureZero globals extension faithful observations in
/-- This is exactly the revised Source callback target, including ReachedExit.
Only the nested proof is forgotten beside the same actual returned pool. -/
theorem parameter_preserves (size : Nat) :
    CallableRuntimeBodyEntryContracts.PreservesAt (registry := registry) (faults := faults) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions (Program.ofChecked compiled.sourceProgram)
      (receipt.admitted_entry wellFormed).original size :=
  CallableIndexedOwnedBodyNestedEntries.preserves_of_nested functions owner header
    (receipt.admitted_entry wellFormed).original (receipt.packet captureZero globals)
    (nested_preserves functions owner receipt wellFormed prepared member captureZero globals extension faithful observations size)

include wellFormed prepared member captureZero globals extension faithful observations functionTypes in
/-- This is exactly the revised native callback target with its actual post. -/
theorem parameter_reflects (size : Nat) :
    CallableRuntimeBodyEntryContracts.ReflectsAt (registry := registry) (faults := faults) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions (Program.ofChecked compiled.sourceProgram)
      (receipt.admitted_entry wellFormed).original size :=
  CallableIndexedOwnedBodyNestedEntries.reflects_of_nested functions owner header
    (receipt.admitted_entry wellFormed).original (receipt.packet captureZero globals)
    (nested_reflects functions owner receipt wellFormed prepared member captureZero globals extension faithful observations functionTypes size)

include wellFormed prepared member captureZero globals extension faithful observations in
/-- A finished Source callback is available at every genuine closed receipt;
its supplied continuation agreement is retained by the production interface. -/
theorem source_callbacks (budget : Nat) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.SourceBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := fun _ => noExpressions)
      (expressionSyntax := fun _ => noExpressionSyntax) (diagnosticPolicy := .reachable)
      (runtime := true) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt _agreement size _smaller
  exact parameter_preserves functions owner actualReceipt wellFormed prepared member captureZero globals extension faithful observations size

include wellFormed prepared member captureZero globals extension faithful observations functionTypes in
/-- The genuine native prefix and saved write select that same exact callback.
No comparison with its reflected Source grade is required. -/
theorem native_callbacks (budget : Nat) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.NativeBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := fun _ => noExpressions)
      (expressionSyntax := fun _ => noExpressionSyntax) (diagnosticPolicy := .reachable)
      (runtime := true) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt prefixSize bodyStore value finalStore
    _prefixRun _prefixWithin _restored size _smaller
  exact parameter_reflects functions owner actualReceipt wellFormed prepared member captureZero globals extension faithful observations functionTypes size

include wellFormed prepared member captureZero globals extension faithful observations in
/-- All observations concern the same actual returned pool. The original
argument pool and the real parameter pool both retain their ordered records. -/
theorem source_post (size : Nat) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size
      header.function header.context receipt.body.environment receipt.body.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates receipt.body.actualBody receipt.body.store (header.body.rename receipt.body.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends receipt.body.mapping finalMap ∧ WorldExtends receipt.body.world finalWorld ∧
      AdministrativePreserved receipt.body.mapping receipt.body.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend receipt.body.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: receipt.administrative)
        (Program.ofChecked compiled.sourceProgram) header.function header.context
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        receipt.body.environment receipt.body.heap after outcome ∧
      ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, receipt.body.canonical⟩,
        Relates receipt.reached reached ∧
        PoolObservations receipt.reached reached ∧ PoolObservations argumentsPool reached ∧
        CallableIndexedOwnedSourceAdmission.PostAdmission
          (CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base)
          header.context header.function.resultType outcome reached := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related⟩ :=
    parameter_preserves functions owner receipt wellFormed prepared member captureZero globals extension faithful observations size trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related, reached_pool_observations related,
    reached_pool_observations ((protocol headers keys).trans receipt.related related),
    CallableIndexedOwnedAdmittedBodyEntries.after_body
      (CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base)
      wellFormed (receipt.admitted_entry wellFormed) reached trace frame⟩

include wellFormed prepared member captureZero globals extension faithful observations functionTypes in
/-- Reflection returns its independent Source trace and adds successful deep
typing from that trace at the exact native post, alongside snapshot reads. -/
theorem native_post (size : Nat) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size receipt.body.actualBody receipt.body.store
      (header.body.rename receipt.body.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize
        header.function header.context receipt.body.environment receipt.body.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends receipt.body.mapping finalMap ∧ WorldExtends receipt.body.world finalWorld ∧
      AdministrativePreserved receipt.body.mapping receipt.body.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend receipt.body.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: receipt.administrative)
        (Program.ofChecked compiled.sourceProgram) header.function header.context
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        receipt.body.environment receipt.body.heap after outcome ∧
      ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, receipt.body.canonical⟩,
        Relates receipt.reached reached ∧
        PoolObservations receipt.reached reached ∧ PoolObservations argumentsPool reached ∧
        CallableIndexedOwnedSourceAdmission.PostAdmission
          (CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base)
          header.context header.function.resultType outcome reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related⟩ :=
    parameter_reflects functions owner receipt wellFormed prepared member captureZero globals extension faithful observations functionTypes size completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related, reached_pool_observations related,
    reached_pool_observations ((protocol headers keys).trans receipt.related related),
    CallableIndexedOwnedAdmittedBodyEntries.after_body
      (CallableIndexedOwnedIndirectCallerProtocol.of_legacy CallableIndexedOwnedCallerProtocol.base)
      wellFormed (receipt.admitted_entry wellFormed) reached trace frame⟩

end Tests.SourceCoreClosedAdmittedNamedReceipt
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedAdmittedWhile
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedLambdaPublicExecution
/-! A concrete parsed program is independently Source-typed, compiled, opened
and run through the public API. Real compiler receipts construct its complete
static family, and the public theorem produces a Source application and the
returned function-handle history. No body law or value representation is an
input to the fixture. This case is an empty unit lambda, without captures. -/

set_option autoImplicit false
set_option Elab.async false

namespace Tests.SourceCoreClosedLambdaPublicExecution
open Solcore Frontend SourceInference SourceSemantics

/-- Decidable observations of the actual checked factory. Deep Source typing
is constructed from these observations instead of assumed from checker success. -/
structure UnitFactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  expression : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = []
  returns : signature.returnTypes = [.function .unit .unit]
  inputs : function.typedBody.inputs = []
  roots : function.typedBody.roots = [.statement statement.id]
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  lambda : expression.form = .lambda [] .unit []
  expressionRaw : expression.rawType = .function .unit .unit
  expressionType : expression.type = .function .unit .unit
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = .function .unit .unit

private theorem statementRoots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]

/-- Empty lambda bodies really have unit type in the lexical context of this
actual outer return. No runtime or compiler meaning law enters this proof. -/
theorem UnitFactoryShape.statementTyping
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : UnitFactoryShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {
    type := .function .unit .unit
    hasValue := true
    sawReturn := true
    control := .returned }
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension
  have binders : TypeParameterBindersWellFormed
      (checkedBodyContext signatures signature function) := by
    simp [TypeParameterBindersWellFormed, checkedBodyContext, declarationContext,
      Context.ofSignatures, Context.forDeclaration,
      Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
  have admissible : TypeAdmissible (checkedBodyContext signatures signature function)
      (.function .unit .unit) := ⟨binders, .function (.builtin .unit) (.builtin .unit)⟩
  have expressionTyped : ExpressionHasType function.typedBody
      (checkedBodyContext signatures signature function) shape.expression.id
      (.function .unit .unit) := by
    rw [← shape.expressionType]
    refine .intro (lookupExpression?_sound shape.expressionFound)
      (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
        (.nil _ _) (by exact ⟨rfl, rfl, .inr rfl⟩)) shape.expressionRaw
      admissible (shape.expressionType ▸ admissible) ?_
    rw [shape.requirements, shape.coercions, shape.expressionType]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
    shape.returnStatement expressionTyped shape.statementType)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make() returns (function() returns ()) { return lam() {}; }"}] }

private def shape (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (UnitFactoryShape function signature) := do
  let [Node.expression expression, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "unit factory occurrence shape")
  if observed : signature.scheme.parameters = [] ∧ signature.parameterTypes = [] ∧
      signature.returnTypes = [.function .unit .unit] ∧ function.typedBody.inputs = [] ∧
      function.typedBody.roots = [.statement statement.id] ∧
      function.typedBody.lookupExpression? expression.id = some expression ∧
      function.typedBody.lookupStatement? statement.id = some statement ∧
      expression.form = .lambda [] .unit [] ∧ expression.rawType = .function .unit .unit ∧
      expression.type = .function .unit .unit ∧ expression.requirements = [] ∧ expression.coercions = [] ∧
      statement.form = .returnStmt (some expression.id) ∧ statement.type = .function .unit .unit then
    return ⟨expression, statement, observed.1, observed.2.1, observed.2.2.1,
      observed.2.2.2.1, observed.2.2.2.2.1, observed.2.2.2.2.2.1,
      observed.2.2.2.2.2.2.1, observed.2.2.2.2.2.2.2.1, observed.2.2.2.2.2.2.2.2.1,
      observed.2.2.2.2.2.2.2.2.2.1, observed.2.2.2.2.2.2.2.2.2.2.1,
      observed.2.2.2.2.2.2.2.2.2.2.2.1, observed.2.2.2.2.2.2.2.2.2.2.2.2.1,
      observed.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  else throw (IO.userError "unit factory retained source metadata")

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : program.functions = [function]
  signatures : program.signatures.functions = [signature]
  methods : program.methods = []
  sourceShape : UnitFactoryShape function signature
  nodes : function.typedBody.nodes = [.expression sourceShape.expression, .statement sourceShape.statement]

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [function], [signature] =>
      let sourceShape ← shape function signature
      if methods : program.methods = [] then
        let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
          functions := by
            intro actual member candidate candidateMember _accepted
            have sameFunction : actual = function := by simpa only [functions, List.mem_singleton] using member
            have sameSignature : candidate = signature := by simpa only [signatures, List.mem_singleton] using candidateMember
            subst actual candidate
            exact sourceShape.statementTyping program.signatures
          methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
        if nodes : function.typedBody.nodes = [.expression sourceShape.expression, .statement sourceShape.statement] then
          return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
            function, signature, functions, signatures, methods, sourceShape, nodes⟩
        else throw (IO.userError "factory complete node graph changed")
      else throw (IO.userError "unexpected unit factory methods")
    | _, _ => throw (IO.userError "unit factory declaration count")


structure CompiledFixture extends CheckedFixture where
  seeds : List SourceCompiler.Seed
  options : SourceCompiler.Options
  facadeCompiled : SourceCompiler.Compiled
  accepted : SourceCompiler.compileChecked program seeds options = .ok facadeCompiled
  recipe : SourceCoreIndexedSession.Recipe
  issued : CoreLowering.RecursiveNamedPreparedStageContracts.PublicRecipe facadeCompiled recipe
  sameProgram : recipe.compiled.sourceProgram = program

def compiledFixture : IO CompiledFixture := do
  let checked ← checkedFixture
  let signature :: _ := checked.program.signatures.functions
    | throw (IO.userError "factory signature missing")
  let seeds := [SourceCompiler.Seed.declaration signature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 100}
  match generated : SourceCoreCompiler.compileChecked checked.program seeds options with
  | .error error => throw (IO.userError (reprStr error))
  | .ok source =>
    match selected : source.artifact? with
    | none => throw (IO.userError "factory cached artifact missing")
    | some cached =>
      match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
      | .error error => throw (IO.userError (reprStr error))
      | .ok recipe =>
        match facade : SourceCoreExecution.prepare source with
        | .error error => throw (IO.userError (reprStr error))
        | .ok facadeCompiled =>
          have accepted : SourceCompiler.compileChecked checked.program seeds options = .ok facadeCompiled := by
            simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError,
              bind, Except.bind] using facade
          have sameProgram : recipe.compiled.sourceProgram = checked.program :=
            (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
              ((source.artifact_fields selected).1.trans (SourceCoreCompiler.compileChecked_program generated))
          return {
            toCheckedFixture := checked
            seeds := seeds
            options := options
            facadeCompiled := facadeCompiled
            accepted := accepted
            recipe := recipe
            issued := CoreLowering.RecursiveNamedPreparedStageContracts.public_preparation selected prepared facade
            sameProgram := sameProgram }

theorem CompiledFixture.prepared (fixture : CompiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ fixture.recipe.compiled.validationPlan.specializations) :
    Nonempty (CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row) :=
  CoreLowering.RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.issued member

theorem CompiledFixture.source_wellFormed (fixture : CompiledFixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  rw [fixture.sameProgram]
  exact fixture.wellFormed

structure ActualHeader (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) where
  prepared : CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row
  diagnostic : CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared
  header : CoreLowering.CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
    (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  aligned : CoreLowering.RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
    (CoreLowering.CallableNamedMetadata.instantiation row) header



open CoreLowering

theorem ActualHeader.terminal {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) (expression : ExpressionId) (statement : StatementNode)
    (roots : row.function.typedBody.roots = [.statement statement.id])
    (found : row.function.typedBody.lookupStatement? statement.id = some statement)
    (form : statement.form = .returnStmt (some expression)) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared ∧
      terminal.expression = expression ∧ terminal.certificate =
        CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
          (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          terminal.expression terminal.receipt.child := by
  have source : actual.header.function.source = row.function.typedBody := by
    rw [actual.aligned.function]
    exact congrArg (fun specialized => specialized.function.typedBody) actual.prepared.same
  have body : actual.header.function.body = [statement.id] := by
    rw [actual.aligned.function]
    change actual.prepared.compilation.statements = [statement.id]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, roots] at accepted
    exact (Except.ok.inj accepted).symm
  have terminalShape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      actual.header.function.source expression actual.header.function.body := by
    rw [source, body]
    exact .returning [] found form
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rw [actual.aligned.policy]; rfl) terminalShape actual.aligned.accepted
  let terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header := {
    row := row
    prepared := actual.prepared
    instantiation := CallableNamedMetadata.instantiation row
    aligned := actual.aligned
    layouts := actual.aligned.layouts
    expression := expression
    receipt := receipt
    certificate := CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression receipt.child
    certifies := by
      intro child generated
      have same : child = receipt.child := Except.ok.inj (generated.symm.trans receipt.generated)
      exact ⟨rfl, rfl, same⟩ }
  exact ⟨terminal, actual.diagnostic, rfl, rfl⟩


/-- Finite, executable checks of the same actual compiled row. None is an
execution correspondence or a supplied lambda formation certificate. -/
structure ObservedFactory (fixture : CompiledFixture) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  parameters : row.parameterSubstitution = []
  closed : row.assumptions = []
  ordinary : row.function.returnComptime = false
  inputs : row.function.typedBody.inputs = []
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  expression : ExpressionNode
  statement : StatementNode
  roots : row.function.typedBody.roots = [.statement statement.id]
  foundStatement : row.function.typedBody.lookupStatement? statement.id = some statement
  returnStatement : statement.form = .returnStmt (some expression.id)
  foundExpression : row.function.typedBody.lookupExpression? expression.id = some expression
  nodes : row.function.typedBody.nodes = [.expression expression, .statement statement]
  lambda : expression.form = .lambda [] .unit []
  owned : expression.id.occurrence.owner = row.function.typedBody.owner
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  noNativeInputs : entry.native.inputTypes = []
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    row.function.typedBody expression.id = .ok (expression, reported)

def observeFactory (fixture : CompiledFixture) : IO (ObservedFactory fixture) := do
  match rows : fixture.recipe.compiled.validationPlan.specializations with
  | [row] =>
    match target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
        (CallableNamedMetadata.instantiation row) with
    | .error _ => throw (IO.userError "factory exact target")
    | .ok key =>
      if shape : row.parameterSubstitution = [] ∧ row.assumptions = [] ∧
          row.function.returnComptime = false ∧ row.function.typedBody.inputs = [] ∧ key = row.key then
        let [Node.expression expression, Node.statement statement] := row.function.typedBody.nodes
          | throw (IO.userError "factory occurrence list")
        if observed : row.function.typedBody.roots = [.statement statement.id] ∧
            row.function.typedBody.lookupStatement? statement.id = some statement ∧
            statement.form = .returnStmt (some expression.id) ∧
            row.function.typedBody.lookupExpression? expression.id = some expression ∧
            expression.form = .lambda [] .unit [] ∧ expression.id.occurrence.owner = row.function.typedBody.owner ∧
            expression.requirements = [] ∧ expression.coercions = [] ∧
            fixture.recipe.compiled.indexed.base.locals.bindings = [] ∧
            fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true then
          match entries : fixture.recipe.compiled.indexed.entries with
          | [entry] =>
            if noNativeInputs : entry.native.inputTypes = [] then
              match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
                  row.function.typedBody expression.id with
              | .error _ => throw (IO.userError "factory actual expression reader")
              | .ok (node, reported) =>
                if same : node = expression then
                  if nodes : row.function.typedBody.nodes = [.expression expression, .statement statement] then
                    return {
                      row := row
                      member := by rw [rows]; exact .head []
                      parameters := shape.1
                      closed := shape.2.1
                      ordinary := shape.2.2.1
                      inputs := shape.2.2.2.1
                      target := by rw [target, shape.2.2.2.2]
                      expression := expression
                      statement := statement
                      roots := observed.1
                      foundStatement := observed.2.1
                      returnStatement := observed.2.2.1
                      foundExpression := observed.2.2.2.1
                      nodes := nodes
                      lambda := observed.2.2.2.2.1
                      owned := observed.2.2.2.2.2.1
                      requirements := observed.2.2.2.2.2.2.1
                      coercions := observed.2.2.2.2.2.2.2.1
                      noLocals := observed.2.2.2.2.2.2.2.2.1
                      profile := observed.2.2.2.2.2.2.2.2.2
                      entry := entry
                      entryMember := by rw [entries]; exact .head []
                      noNativeInputs := noNativeInputs
                      reported := reported
                      read := by rw [read, same] }
                  else throw (IO.userError "factory full specialized node graph changed")
                else throw (IO.userError "factory reader changed source node")
            else throw (IO.userError "factory has native inputs")
          | _ => throw (IO.userError "factory native entry count")
        else throw (IO.userError "factory retained source observations")
      else throw (IO.userError "factory retained row observations")
  | _ => throw (IO.userError "factory row count")


/-- The staged selection is obtained from the retained callable table and
original sidecar of the concrete compiler result. -/
structure ObservedStages (fixture : CompiledFixture)
    (observed : ObservedFactory fixture) where
  singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      if singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1 then
        match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
            (.named observed.row.key) with
        | .error error => throw (IO.userError (reprStr error))
        | .ok descriptor => return ⟨singletonGlobal, descriptor, native, present, sidecar, issued⟩
      else throw (IO.userError "factory global count")

def ObservedStages.registry {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem ActualHeader.complete {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [actual.header] := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled actual.prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : actual.prepared.index = 0 := by omega
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [stages.singletonGlobal] at bound
  have indexZero : index = 0 := by omega
  refine ⟨actual.header, .head [], actual.aligned.slot.trans (zero.trans indexZero.symm), ?_⟩
  rw [actual.aligned.named]
  rw [zero] at selected
  rw [indexZero] at found
  exact Option.some.inj (selected.symm.trans found)

theorem bootstrap_zero (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled)) :
    owner.key.capturePrefix = 0 := by
  have bound := owner.position.isLt
  change owner.position.val < 1 at bound
  have zero : owner.position.val = 0 := by omega
  simp only [CallableIndexedOwnedFunctionValues.OwnedKey.key,
    CallableIndexedOwnedPreparedBootstrapRootState.keys,
    CallableIndexedOwnedPreparedBootstrapRootState.key, zero, List.getElem_cons_zero]


theorem ObservedStages.inventory {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row, actual.header = packet.header := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  have target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation observed.row) = .ok prepared.named.signature.key := by
    rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
    exact observed.target
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : prepared.index = 0 := by omega
  have globals : fixture.recipe.compiled.indexed.base.globals = [prepared.named.signature] := by
    obtain ⟨first, single⟩ := List.length_eq_one_iff.mp stages.singletonGlobal
    rw [single, zero] at selected
    have same : first = prepared.named.signature := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
    exact single.trans (congrArg (fun value => [value]) same)
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := by intro binder member; simp only [observed.inputs, List.not_mem_nil] at member
    target := target
    slot := by simp only [CallableNamedMetadata.Slot, globals, zero]; simp }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned }
  exact ⟨input, rfl, packet, actual, rfl⟩



theorem ObservedStages.source_of_cached {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 1 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using stages.singletonGlobal
  have before := (List.getElem?_eq_some_iff.mp actual.prepared.selected).1
  have after := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at before after
  have same : index = actual.prepared.index := by omega
  rw [same, actual.prepared.selected] at selected
  cases Option.some.inj selected
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

theorem ObservedFactory.only_lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : observed.row.function.typedBody.lookupExpression? id = some node) :
    node.form = .lambda [] .unit [] := by
  have member := (lookupExpression?_sound found).1
  rw [observed.nodes] at member
  have same : node = observed.expression := by
    rcases List.mem_cons.mp member with same | rest
    · exact Node.expression.inj same
    · rcases List.mem_cons.mp rest with impossible | empty
      · cases impossible
      · cases empty
  exact same ▸ observed.lambda

theorem ObservedStages.association_empty {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping}
    {function : Dynamic.Closure} {native : Core.Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Core.Ty}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers keys registry faults
      mapping world function native bindings parameterCore resultCore) :
    function.body = [] ∧ function.resultType = .unit := by
  have fromSource {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      (code : CallableIndexedLambdaValues.Code fixture.recipe.compiled.indexed function scope administrative)
      (sameSource : function.source = observed.row.function.typedBody) :
      function.body = [] ∧ function.resultType = .unit := by
    have found := code.sourceFound
    rw [sameSource] at found
    have form := (observed.only_lambda found).symm.trans code.sourceForm
    exact ⟨(ExpressionForm.lambda.inj form).2.2.symm, (ExpressionForm.lambda.inj form).2.1.symm⟩
  cases association with
  | ordinary _ _ code _ support _ _ _ _ _ _ =>
    exact fromSource code (support.source.trans (stages.source_of_cached actual support.caller.selected))
  | principal _ _ code _ support _ _ _ _ _ _ =>
    exact fromSource code (support.source.trans (stages.source_of_cached actual support.principal.cached.selected))


theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

theorem ActualHeader.formation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context
      actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedEmptyLambdaFormation.of_terminal terminal
    fixture.source_wellFormed observed.profile diagnostic (stages.selected actual)
    observed.entryMember observed.noNativeInputs
    (node := observed.expression) (reported := observed.reported)
  · rw [actual.source, expression]; exact observed.foundExpression
  · exact observed.lambda
  · rw [actual.source, expression]; exact observed.owned
  · exact observed.requirements
  · exact observed.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact observed.read

theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support
      [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.formation stages terminal diagnostic expression
  exact ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual
    [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point (actual.complete stages)
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩


theorem ActualHeader.no_bindings {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.bindings = [] := by
  have inputs := actual.header.inputs
  rw [actual.source, observed.inputs] at inputs
  exact List.map_eq_nil_iff.mp inputs.symm

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

private def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its exported handle is not manufactured. -/
structure ObservedPublicRun (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [] runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observePublicRun (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "factory bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.row.key [] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed _ _) => throw (IO.userError "factory public run failed")
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "factory public run exhausted")
      | .ok (.succeeded completion) =>
        match returned : completion.value with
        | .function handle =>
          return ⟨opened.val, opened.property, fresh.val, fresh.property, session, ready,
            checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
        | _ => throw (IO.userError "factory output was not a function handle")

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  completion : SourceCoreCallableIndexedPrograms.Completion fixture.recipe.compiled.indexed
  executed : fixture.recipe.compiled.indexed.runSource observed.row.key []
    runOptions.executionFuel runOptions.inputValidationFuel = .ok completion

def observeReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedReceiver fixture observed) := do
  match executed : fixture.recipe.compiled.indexed.runSource observed.row.key []
      runOptions.executionFuel runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok completion => return ⟨completion, executed⟩


private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem ObservedPublicRun.start_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedPublicRun fixture observed) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      executed.session.IndexedAt session ∧ executed.checkpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [] runOptions.inputValidationFuel
        checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩


theorem ObservedPublicRun.metadata_at_start {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedPublicRun fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [] runOptions.inputValidationFuel
      checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  exact started.empty_registry (booted.registry_at initial)


/-- A closed fixture conclusion retains an independent Source application and
an actual returned-session history for the handle observed from the public API. -/
def PublicFactoryMeaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (executed : ObservedPublicRun fixture observed)
    (receiver : ObservedReceiver fixture observed) : Prop :=
  let compiled := fixture.recipe.compiled
  let keys := CallableIndexedOwnedPreparedBootstrapRootState.keys compiled
  let registry := receiver.completion.result.context.registry
  let faults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
  ∃ actual : ActualHeader fixture observed.row,
    ∃ headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)),
    actual.header ∈ headers ∧
    ∃ (rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment) (function : Dynamic.GlobalFunction),
    CallableIndexedOwnedFunctionValues.NamedSourceAt actual.header rawD function ∧
    ∃ (sourceSize : Nat) (source : Dynamic.Value) (after : Dynamic.Heap),
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages.registry sourceSize
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function)
      actual.header.function.context ⟨[]⟩ (.global function) [] (.value source) after ∧
    ∃ (artifact : SourceCoreIndexedSession.Artifact) (session : SourceCoreIndexedSession.Session artifact)
      (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store) (payload : Core.Value),
    ∃ caller : RecursiveNamedPublicFunctionHistory.Caller headers keys mapping world after store,
      executed.completion.session.IndexedAt session ∧
      RecursiveNamedPublicFunctionHistory.History headers keys
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys registry faults observed.profile)
        registry actual.header session mapping world after store caller
        [⟨actual.header.function.resultType, source, executed.handle, payload, actual.header.output,
          runOptions.outputValidationFuel⟩]

/-- All public theorem premises are produced by the actual checker/compiler,
bootstrap, encoder and run receipts of this fixture. No representation,
execution correspondence, static body certificate or family is supplied. -/
theorem public_factory_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (executed : ObservedPublicRun fixture observed)
    (receiver : ObservedReceiver fixture observed) :
    PublicFactoryMeaning fixture observed stages executed receiver := by
  obtain ⟨input, _row, packet, actual, sameHeader⟩ := stages.inventory
  let rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory [input] := .cons packet .nil
  have headerList : CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows = [actual.header] := by
    simp only [rows, CallableIndexedOwnedPreparedFiniteNamedInventories.headers, sameHeader]
  let stagePrepared := RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected
  let registry := receiver.completion.result.context.registry
  let faults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.expression.id observed.statement
    observed.roots observed.foundStatement observed.returnStatement
  obtain ⟨support⟩ := actual.support stages terminal diagnostic expression point (registry := registry) (faults := faults)
  let terminals : ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
      CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header := fun header member => by
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    exact same ▸ terminal
  have supports : ∀ header (member : header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows),
      CallableIndexedOwnedPreparedStagedNamedBodySupport.Support
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry header (RecursiveNamedPreparedStageScopes.registry stagePrepared) (terminals header member) faults := by
    intro header member
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    subst header
    simpa only [headerList, terminals, ObservedStages.registry, stagePrepared] using support
  have family : ∀ {mapping world function native bindings parameter result}
      (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry faults
        mapping world function native bindings parameter result),
      CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
    intro mapping world function native bindings parameter result association
    have shape := stages.association_empty actual association
    exact .empty shape.1 shape.2
  have observations : CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      (CallableIndexedOwnedContextualCellOrigins.functions
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry faults observed.profile)
      (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
    intro metadata mapping world sourceType source native type origin
    exact CallableIndexedOwnedGeneralLambdaValues.observations _ registry faults observed.profile
      (registry := metadata) (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := executed.start_receipt
  have complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) := by
    rw [headerList]
    exact actual.complete stages
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared complete
  have selectedEq : selectedHeader = actual.header := by
    have member := selected.member
    rw [headerList] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs rows session actual.header.function.context
      (actual.header.bindings.map (fun binding => binding.1.scheme.body)) [] [] := by
    rw [actual.no_bindings]
    exact .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry registry := by
    rw [executed.metadata_at_start opened sessionAt started]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt actual.header input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)) := by
    rw [sameHeader]
    exact packet.sourceAt
  obtain ⟨caller, returnedCompletion, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, typeEq, budgetEq, returnedAt, trace, fullResult,
      returnedCaller, source, payload, sourceValue, nativeValue, related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_remembers
      (inputs := [input]) (rows := rows) (distinct := by simp)
      (stagePrepared := stagePrepared)
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (profile := observed.profile) (bodyRegistry := registry) (semanticFaults := faults)
      (observations := observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member)) (namedSupport := supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := executed.fresh) (ready := .single executed.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl executed.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] actual.header.function)
      executed.started executed.executed executed.returned (actual.descriptor stages)
  exact ⟨actual, CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
    by rw [headerList]; exact .head [], input.prepared.available, _, sourceAt,
    sourceSize, source, after, sourceValue ▸ trace, artifact, returnedCompletion.session,
    finalMap, finalWorld, finalStore, payload, returnedCaller, returnedAt, retained⟩

def run : IO Unit := do
  let certified ← compiledFixture
  let observed ← observeFactory certified
  let stages ← observeStages certified observed
  let executed ← observePublicRun certified observed
  let receiver ← observeReceiver certified observed
  have _publicMeaning := public_factory_meaning certified observed stages executed receiver
  IO.println "Actual compiled unit lambda factory: Source application and exported-handle history proved through public execution"

end Tests.SourceCoreClosedLambdaPublicExecution
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedReadyNamedWhile
/-! A real named parameter receipt and a literal-false while body exercise
actual loop activation, Source admission and the reached owned records.
The literal and body callbacks are derived internally from authentic static
receipts and the shared Ready family; no execution family is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreClosedReadyNamedWhile
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open Tests.SourceCoreClosedOwnedWhile (booleans boolean_preserves_at boolean_reflects_at)
open Tests.SourceCoreClosedOwnedLexicalBody (reached_pool_observations)
open Tests.SourceCoreClosedOwnedExpressionHead (PreparedReceipts layouts PoolObservations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- Full original parameter, hook, Source and compiler receipts stay together.
The certificate admits only the compiler's ordinary Boolean literal leaf. -/
abbrev Receipt {index : Index} (argumentsPool : State headers keys index)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (arguments : List Dynamic.Value) :=
  CallableIndexedOwnedAdmittedNamedExpressionHeads.ParameterReceipt
    (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := fun header _ => booleans header.function.source)
    (expressionSyntax := fun _ _ => True) (diagnosticPolicy := .reachable) (runtime := true)
    argumentsPool header arguments

/-- This bounded Source body contains a real while condition, and both its
loop body and the remaining Unit fallthrough are empty. -/
structure FalseWhile (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) where
  statement : StatementId
  node : StatementNode
  condition : ExpressionId
  conditionNode : ExpressionNode
  body : header.function.body = [statement]
  found : header.function.source.lookupStatement? statement = some node
  form : node.form = .whileLoop condition []
  conditionFound : header.function.source.lookupExpression? condition = some conditionNode
  literal : CompatibleExpressionLiterals.Literal [] conditionNode .bool (LanguageResult.success (.bool false))
  unitResult : header.function.resultType = .unit

private theorem literal_fields {node : ExpressionNode}
    (literal : CompatibleExpressionLiterals.Literal [] node .bool (LanguageResult.success (.bool false))) :
    ∃ name, node.form = .reference name (.builtinBoolean false) ∧ node.type = .bool ∧
      node.requirements = [] ∧ node.coercions = [] := by
  cases literal with
  | bool value form type requirements coercions => exact ⟨_, form, type, requirements, coercions⟩

variable {index : Index} {argumentsPool : State headers keys index}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {arguments : List Dynamic.Value}
  (receipt : Receipt (registry := registry) (faults := faults) functions owner argumentsPool header arguments)
  (body : FalseWhile header)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include receipt body wellFormed in
/-- Authentic Source body typing supplies the condition judgment; the
independent literal/form receipts build the same original compiler Syntax. -/
theorem body_syntax : GenericImperativeMatch.Syntax header.function.source (fun _ => True) header.context
    (.statements true header.function.body) header.function.resultType := by
  have original := receipt.admitted_entry wellFormed
  have statements : ProtectedStateImperativeTypedSourceSites.Statements header.function.source header.context header.function.body :=
    CallableIndexedOwnedBodyTypedFacts.statements original.source
  rw [body.body] at statements
  have head := ProtectedStateImperativeTypedSourceSites.head statements
  have unique := header.unique
  obtain ⟨conditionTyped, _bodyTyped⟩ := ProtectedStateImperativeTypedSourceSites.while_loop unique head body.found body.form
  obtain ⟨_name, _form, conditionType, _requirements, _coercions⟩ := literal_fields body.literal
  rw [body.body]
  exact .whileLoop body.found body.form body.conditionFound conditionType
    (by simpa only [conditionType] using conditionTyped) True.intro
    (.body (.nil (.inl rfl))) (.body (.nil (.inr body.unitResult)))

include body in
/-- Construct the original false condition and Unit body trace. No Source or
native execution premise is needed to obtain this genuine finite body run. -/
theorem actual_source {environment : Dynamic.Environment} {before : Dynamic.Heap} :
    ∃ size, RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size
      header.function header.context environment before (.value .unit) before := by
  obtain ⟨name, form, _type, requirements, coercions⟩ := literal_fields body.literal
  have condition : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [], SourceExecutionSize.stepSize []])
      header.context header.function.evidence header.function.source environment before body.condition (.bool false) before := by
    refine .intro (raw := .bool false) (middle := before) (lookupExpression?_sound body.conditionFound) ?_ ?_
    · rw [form]
      exact .builtinBoolean (by simp [Dynamic.OrdinaryRequirementLayout, requirements, coercions, coercionRequirementIds])
    · rw [coercions]
      exact .nil
  refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [SourceExecutionSize.stepSize
    [SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [], SourceExecutionSize.stepSize []]]]],
    .unit (finalContext := header.context) (finalEnvironment := environment) body.unitResult ?_⟩
  rw [body.body]
  exact .singleton (lookupStatement?_sound body.found)
    (by intro expression impossible; rw [body.form] at impossible; cases impossible)
    (.whileLoop (lookupStatement?_sound body.found) body.form (.done condition))

private abbrev bridge := CallableIndexedOwnedIndirectCallerProtocol.of_legacy
  (CallableIndexedOwnedCallerProtocol.base (headers := headers) (keys := keys))

private def actual_origin := CallableIndexedOwnedBodySourceOrigin.source_origin
  (CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
  (receipt.admitted_entry wellFormed).source.runtime

private def actual_entry : CallableRuntimeBodyReadyOrigins.Entry (protocol headers keys)
    (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts header.function.source (fun _ => True))
    (actual_origin functions owner receipt wellFormed) functions :=
  CallableIndexedOwnedBodySourceOrigin.ready_entry (bridge (headers := headers) (keys := keys))
    (receipt.admitted_entry wellFormed) (body_syntax functions owner receipt body wellFormed)

variable (prepared : PreparedReceipts (headers := headers)) (member : header ∈ headers)

private def marked : MarkedAllocation.Producer (protocol headers keys)
    header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  (layouts prepared member).symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    (same : first = second)
    (producer : MarkedAllocation.Producer (protocol headers keys)
      second compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    {location : Location} {native : NativeFrame}
    (ready : OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    OrdinaryAllocation.ReadyAt ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (marked (headers := headers) (keys := keys) (registry := registry) functions prepared member).toOrdinary location native :=
  ready_layout (keys := keys) functions (layouts prepared member)
    (CallableIndexedOwnedMarkedAllocation.producer headers keys
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

include wellFormed in
private theorem literals_preserve (context : SourceSemantics.Context)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context header.function.source)
    (covers : header.function.evidence.Covers context) (size : Nat) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt
      (protocol headers keys)
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
      (Program.ofChecked compiled.sourceProgram) header.function.evidence
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (booleans header.function.source)
      (source := header.function.source) (context := context) (faults := faults) size :=
  CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at (bridge (headers := headers) (keys := keys))
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful wellFormed runtime covers
      (boolean_preserves_at (headers := headers) (keys := keys) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) (registry := registry) (context := context) (faults := faults) functions header.function.evidence size header.unique))

include wellFormed in
private theorem literals_reflect (context : SourceSemantics.Context)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context header.function.source)
    (covers : header.function.evidence.Covers context) (size : Nat) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt
      (protocol headers keys)
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
      (Program.ofChecked compiled.sourceProgram) header.function.evidence
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (booleans header.function.source)
      (source := header.function.source) (context := context) (faults := faults) size :=
  CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at (bridge (headers := headers) (keys := keys))
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful wellFormed runtime covers
      (boolean_reflects_at (headers := headers) (keys := keys) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) (registry := registry) (context := context) (faults := faults) functions header.function.evidence size))

private def actual_inputs := CallableIndexedOwnedBodyReadyCatalog.inputs
  (bridge (headers := headers) (keys := keys))
  (CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
  (receipt.admitted_entry wellFormed).source.runtime (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys) wellFormed

variable (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)

include prepared member extension faithful observations wellFormed in
private theorem family_preserves (size : Nat) :
    CallableRuntimeBodyReadyOrigins.PreservesAt (protocol headers keys)
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (actual_inputs functions owner receipt wellFormed).facts functions (Program.ofChecked compiled.sourceProgram)
      (actual_origin functions owner receipt wellFormed) size := by
  have closed := CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family.preserves_at
    (ι := Unit) (origins := fun _ => actual_origin functions owner receipt wellFormed)
    (functions := functions) (program := Program.ofChecked compiled.sourceProgram)
    (protocols := fun _ => protocol headers keys)
    (conditionGate := fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producers := fun _ => marked (headers := headers) (keys := keys) functions prepared member)
    (acquire := fun _ => acquire functions prepared member)
    (stateTransport := fun _ => administrativeTransport headers keys) (stateBindings := fun _ => CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (readinesses := fun _ => CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
    (inputs := fun _ => actual_inputs functions owner receipt wellFormed)
    (expressionMeaning := fun _ context valid _ child _ _ =>
      literals_preserve functions wellFormed context valid.2
        ((CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped).runtimeOf valid.1).covers child)
    (kitsFor := fun _ budget children => CallableIndexedOwnedBodyReadyCatalog.preserving_ready_kits
      (bridge (headers := headers) (keys := keys))
      (CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
      (receipt.admitted_entry wellFormed).source.runtime (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys) wellFormed
      functions extension faithful observations (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (marked (headers := headers) (keys := keys) functions prepared member) (acquire functions prepared member)
      (administrativeTransport headers keys) budget
      children) size
  exact closed ()

include prepared member extension faithful observations wellFormed in
private theorem family_reflects (functionTypes : FunctionRuntimeViews functions) (size : Nat) :
    CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol headers keys)
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (actual_inputs functions owner receipt wellFormed).facts functions (Program.ofChecked compiled.sourceProgram)
      (actual_origin functions owner receipt wellFormed) size := by
  have closed := CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family.reflects_at
    (ι := Unit) (origins := fun _ => actual_origin functions owner receipt wellFormed)
    (functions := functions) (program := Program.ofChecked compiled.sourceProgram)
    (protocols := fun _ => protocol headers keys)
    (conditionGate := fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producers := fun _ => marked (headers := headers) (keys := keys) functions prepared member)
    (acquire := fun _ => acquire functions prepared member)
    (stateTransport := fun _ => administrativeTransport headers keys) (stateBindings := fun _ => CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (readinesses := fun _ => CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
    (inputs := fun _ => actual_inputs functions owner receipt wellFormed)
    (expressionMeaning := fun _ context valid _ child _ _ =>
      literals_reflect functions wellFormed context valid.2
        ((CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped).runtimeOf valid.1).covers child)
    (kitsFor := fun _ budget children => CallableIndexedOwnedBodyReadyCatalog.reflecting_ready_kits
      (bridge (headers := headers) (keys := keys))
      (CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
      (receipt.admitted_entry wellFormed).source.runtime (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys) wellFormed
      functions extension faithful observations (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (marked (headers := headers) (keys := keys) functions prepared member) (acquire functions prepared member)
      (administrativeTransport headers keys) budget functionTypes
      children) size
  exact closed ()

/-- Full body semantics and observations refer to one actual returned pool.
The parameter receipt fixes the physical frame and all original entry data. -/
def BodyPost (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates receipt.body.actualBody receipt.body.store (header.body.rename receipt.body.embedding) value finalStore ∧
  FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    finalMap finalWorld header.function.resultType header.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends receipt.body.mapping finalMap ∧ WorldExtends receipt.body.world finalWorld ∧
  AdministrativePreserved receipt.body.mapping receipt.body.store finalMap finalStore ∧
  Dynamic.HeapMetadataExtend receipt.body.heap after ∧
  TypedMixedNamedBody.ReachedExit compiled.compatible.checked
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions finalMap finalWorld
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: receipt.administrative)
    (Program.ofChecked compiled.sourceProgram) header.function header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    receipt.body.environment receipt.body.heap after outcome ∧
  receipt.frameLocation ∉ finalMap ∧
  finalStore.read? receipt.frameLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state receipt.index)) ∧
  ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      finalMap, finalWorld, after, finalStore, receipt.body.canonical⟩,
    Relates receipt.reached reached ∧
    PoolObservations receipt.reached reached ∧ PoolObservations argumentsPool reached ∧
    ProtectedStateTransition.FunctionFinish.PostReady
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness (bridge (headers := headers) (keys := keys)))
      header.context outcome reached ∧
    CallableIndexedOwnedSourceAdmission.PostAdmission (bridge (headers := headers) (keys := keys))
      header.context header.function.resultType outcome reached

private theorem frame_kept {finalMap : LocationMap} {finalStore : Store}
    (preserved : AdministrativePreserved receipt.body.mapping receipt.body.store finalMap finalStore) :
    receipt.frameLocation ∉ finalMap ∧
      finalStore.read? receipt.frameLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state receipt.index)) := by
  have unmapped : receipt.frameLocation ∉ receipt.body.mapping :=
    Eq.mp (congrArg (fun location => location ∉ receipt.body.mapping) receipt.body.catalog_frame)
      receipt.body.catalog.authority.unmapped
  have retained := preserved receipt.frameLocation unmapped (List.getElem?_eq_some_iff.mp receipt.body.state.read).1
  exact ⟨retained.1, retained.2.trans receipt.body.state.read⟩

include body wellFormed prepared member extension faithful observations in
/-- A genuine false-while Source trace is constructed internally, then the
shared Ready Family returns complete semantics and the actual reached pool. -/
theorem source_post :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize
        header.function header.context receipt.body.environment receipt.body.heap (.value .unit) receipt.body.heap ∧
      BodyPost functions owner receipt (.value .unit) receipt.body.heap value finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, trace⟩ := actual_source body (environment := receipt.body.environment) (before := receipt.body.heap)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      preserved, metadata, exit, reached, related, post⟩ :=
    family_preserves functions owner receipt wellFormed prepared member extension faithful observations sourceSize
      (actual_entry functions owner receipt body wellFormed) trace
  have frame := frame_kept functions owner receipt preserved
  refine ⟨sourceSize, value, finalStore, finalMap, finalWorld, trace,
    evaluated, represented, heaps, maps, worlds, preserved, metadata, exit, frame.1, frame.2,
    reached, related, reached_pool_observations related,
    reached_pool_observations ((protocol headers keys).trans receipt.related related), post, ?_⟩
  exact CallableIndexedOwnedAdmittedBodyEntries.after_body
    (bridge (headers := headers) (keys := keys)) wellFormed (receipt.admitted_entry wellFormed) reached trace preserved

include body wellFormed prepared member extension faithful observations in
/-- Native reflection calls the shared Ready Family independently. Its Source
grade, whole result and post admission accompany the same actual native post. -/
theorem native_post (functionTypes : FunctionRuntimeViews functions) (size : Nat)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size receipt.body.actualBody receipt.body.store
      (header.body.rename receipt.body.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize
        header.function header.context receipt.body.environment receipt.body.heap outcome after ∧
      BodyPost functions owner receipt outcome after value finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      preserved, metadata, exit, reached, related, post⟩ :=
    family_reflects functions owner receipt wellFormed prepared member extension faithful observations functionTypes size
      (actual_entry functions owner receipt body wellFormed) completed
  have frame := frame_kept functions owner receipt preserved
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
    completed.sound, represented, heaps, maps, worlds, preserved, metadata, exit, frame.1, frame.2,
    reached, related, reached_pool_observations related,
    reached_pool_observations ((protocol headers keys).trans receipt.related related), post, ?_⟩
  exact CallableIndexedOwnedAdmittedBodyEntries.after_body
    (bridge (headers := headers) (keys := keys)) wellFormed (receipt.admitted_entry wellFormed) reached trace preserved

end Tests.SourceCoreClosedReadyNamedWhile
end
