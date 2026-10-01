import Solcore.SourceSemantics.CoreLowering.TypedImperativeForAllocation
import Solcore.SourceSemantics.CoreLowering.TypedForHeaderPost
import Solcore.SourceSemantics.CoreLowering.ForLoopCoreEdges

/-! Actual compatible for activation state and concrete condition/body edges.
The administrative self cell contains the real post code; all later effects
must preserve it through the common administrative-frame relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Preserves Reflects FlowRep retain)
open CompatibleExpressionPrimitives (bool_fields)

variable {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode body postCode : Expr} {selfReason : Word}

/-- One live loop activation. Its source lexical frame is fixed across
iterations; body-local allocations survive solely in the represented heap. -/
structure LoopState (values : ValuesContext) {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (context : SourceSemantics.Context) (scope : Scope) (administrative actualContext : Core.Context)
    (frameLayout : SourceCoreCallableIndexedFrames.Layout)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (contextLocation location : Location) (type : Ty) (condition body post : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) : Prop where
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions
  contextRead : ∃ native, store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native)
  contextUnmapped : contextLocation ∉ mapping
  selfTyped : world[location]? = some (OptionalCell.cellType (LocalLoop.functionType type))
  selfRead : store.read? location = some (.inRight .unit
    (LocalLoop.installedClosure type condition body post reason location actual))
  selfUnmapped : location ∉ mapping

variable {scope : Scope} {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {before after : Dynamic.Heap} {store futureStore : Store}

/-- Both the mutable ancestry frame and immutable loop code are real
administrative locations, retained through the supplied common heap frame. -/
theorem LoopState.advance
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body postCode selfReason mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after futureStore)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body postCode selfReason futureMap futureWorld after futureStore := by
  obtain ⟨native, contextRead⟩ := state.contextRead
  obtain ⟨contextUnmapped, contextRead⟩ := retain state.contextUnmapped contextRead frame
  obtain ⟨selfUnmapped, selfRead⟩ := retain state.selfUnmapped state.selfRead frame
  exact ⟨state.environments.extend maps worlds, heaps, state.locals.mono metadata, state.actualTyped.weaken worlds,
    ⟨native, contextRead⟩, contextUnmapped, worlds.lookup state.selfTyped, selfRead, selfUnmapped⟩

def Progress (values : ValuesContext) {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (before after : Dynamic.Heap) (mapping futureMap : LocationMap) (world futureWorld : StoreTyping)
    (store futureStore : Store) : Prop :=
  CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after futureStore ∧
  LocationMap.Extends mapping futureMap ∧ WorldExtends world futureWorld ∧
  AdministrativePreserved mapping store futureMap futureStore ∧ Dynamic.HeapMetadataExtend before after

theorem Progress.trans {middle : Dynamic.Heap} {middleMap : LocationMap} {middleWorld : StoreTyping} {middleStore : Store}
    (first : Progress values registry functions before middle mapping middleMap world middleWorld store middleStore)
    (second : Progress values registry functions middle after middleMap futureMap middleWorld futureWorld middleStore futureStore) :
    Progress values registry functions before after mapping futureMap world futureWorld store futureStore :=
  ⟨second.1, first.2.1.trans second.2.1, first.2.2.1.trans second.2.2.1,
    first.2.2.2.1.trans second.2.2.2.1, first.2.2.2.2.trans second.2.2.2.2⟩

theorem LoopState.progress
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body postCode selfReason mapping world before store)
    (progress : Progress values registry functions before after mapping futureMap world futureWorld store futureStore) :
    LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body postCode selfReason futureMap futureWorld after futureStore :=
  state.advance progress.1 progress.2.1 progress.2.2.1 progress.2.2.2.1 progress.2.2.2.2

variable (functions) (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension uninitialized missing in
theorem condition_preserves {condition : ExpressionId} {node : ExpressionNode}
    (tree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (unique : NodeOccurrencesUnique source)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata⟩ :=
    CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing tree found
      state.environments state.heaps state.locals actualAgrees (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)) trace
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, heaps, maps, worlds, frame, metadata⟩

include extension uninitialized missing in
theorem condition_reflects {condition : ExpressionId} {node : ExpressionNode}
    (tree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩ :=
    CompatibleExpressionTyped.reflects functions extension program evidence valid uninitialized missing tree found
      state.environments state.heaps state.locals actualAgrees (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped))
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩

/-- Run a structurally certified body under the actual Bool/Unit/self prefix.
The body-local lexical result is intentionally discharged at this loop edge. -/
theorem body_preserves {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (correct : Preserves functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : Executes false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨native, read⟩ := state.contextRead
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ))) canonical
      (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, _⟩ :=
    correct valid state.environments state.heaps state.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped))) reference read state.contextUnmapped trace
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, heaps, maps, worlds, frame, metadata⟩

theorem body_reflects {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (correct : Reflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ finalContext outcome after finalMap finalWorld,
      Executes false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨native, read⟩ := state.contextRead
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ))) canonical
      (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, _⟩ :=
    correct valid state.environments state.heaps state.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped))) reference read state.contextUnmapped
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  exact ⟨finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
