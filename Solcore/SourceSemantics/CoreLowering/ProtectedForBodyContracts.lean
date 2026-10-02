import Solcore.SourceSemantics.CoreLowering.ProtectedWhileBodyContracts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedForContracts
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForEndpoint

/-! Guarded for edges retain the actual installed loop state and canonical
named observations. Body control uses the existing five-way contract; post
contracts concern real evaluated prefixes and contain no compiler receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open TypedImperativeFor (LoopState Progress SourceLoop postValues)
open ProtectedWhile.Body (Preserves Reflects)
open TypedScopedStatements (Executes)

abbrev State (entry : ProtectedExpressionMeaning.Entry) (values : ValuesContext)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (context : SourceSemantics.Context) (scope : Scope) (administrative actualContext : Core.Context)
    (frameLayout : SourceCoreCallableIndexedFrames.Layout)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (contextLocation location : Location) (type : Ty) (condition body post : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) : Prop :=
  LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
    contextLocation location type condition body post reason mapping world heap store ∧
  entry scope mapping world heap store canonical

theorem State.advance {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel values.checked.catalog ambient}
    {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
    {frameLayout : SourceCoreCallableIndexedFrames.Layout} {environment : Dynamic.Environment}
    {canonical actual : Environment} {contextLocation location : Location} {type : Ty}
    {condition body post : Expr} {reason : Word} {mapping futureMap : LocationMap}
    {world futureWorld : StoreTyping} {before after : Dynamic.Heap} {store futureStore : Store}
    (state : State entry values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation location type condition body post reason mapping world before store)
    (progress : Progress values registry functions before after mapping futureMap world futureWorld store futureStore) :
    State entry values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation location type condition body post reason futureMap futureWorld after futureStore :=
  ⟨state.1.progress progress, transport.extend state.2 progress.2.1 progress.2.2.1 progress.2.2.2.1 progress.2.2.2.2⟩

abbrev trivialEntry : ProtectedExpressionMeaning.Entry := fun _ _ _ _ _ _ => True

theorem trivialTransport : ProtectedExpressionMeaning.Transport trivialEntry := ⟨by intros; trivial⟩

def PostPreserves {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {entry : ProtectedExpressionMeaning.Entry}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment},
    State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store →
    ∀ continued : Bool,
    Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after →
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore

def PostFaults {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {entry : ProtectedExpressionMeaning.Entry}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault},
    State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store →
    ∀ continued : Bool,
    Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after →
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore

def PostReflects {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {entry : ProtectedExpressionMeaning.Entry}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (faults : FunctionCalls.FaultRep) (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
    State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store →
    ∀ continued : Bool,
    Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ)) value finalStore →
    (∃ finalContext finalEnvironment after finalMap finalWorld,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore)

theorem postpreserves_at_of_unbounded {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {entry : ProtectedExpressionMeaning.Entry}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr)
    (correct : @PostPreserves values ambient entry functions program evidence registry source context scope administrative actualContext frameLayout environment canonical actual ξ contextLocation location type conditionCode body selfReason items code) (size : Nat) :
    @RecursiveNamedForContracts.PostPreservesAt size values ambient entry functions program evidence registry source context scope administrative actualContext frameLayout environment canonical actual ξ contextLocation location type conditionCode body selfReason items code := by
  intro mapping world before after store finalContext finalEnvironment state continued trace
  exact correct state continued trace.sound

theorem postfaults_at_of_unbounded {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {entry : ProtectedExpressionMeaning.Entry}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr)
    (correct : @PostFaults values ambient entry functions program evidence registry faults source context scope administrative actualContext frameLayout environment canonical actual ξ contextLocation location type conditionCode body selfReason items code) (size : Nat) :
    @RecursiveNamedForContracts.PostFaultsAt size values ambient entry functions program evidence registry faults source context scope administrative actualContext frameLayout environment canonical actual ξ contextLocation location type conditionCode body selfReason items code := by
  intro mapping world before after store finalContext reason state continued trace
  exact correct state continued trace.sound

theorem postreflects_at_of_unbounded {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {entry : ProtectedExpressionMeaning.Entry}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (faults : FunctionCalls.FaultRep) (items : List ForItemForm) (code : Expr)
    (correct : @PostReflects values ambient entry functions program evidence registry source context scope administrative actualContext frameLayout environment canonical actual ξ contextLocation location type conditionCode body selfReason faults items code) (size : Nat) :
    @RecursiveNamedForContracts.PostReflectsAt size values ambient entry functions program evidence registry source context scope administrative actualContext frameLayout environment canonical actual ξ contextLocation location type conditionCode body selfReason faults items code := by
  intro mapping world before store finalStore value state continued evaluated
  rcases correct state continued evaluated.sound with done | failed
  · obtain ⟨finalContext, finalEnvironment, after, finalMap, finalWorld, trace, rest⟩ := done
    obtain ⟨sourceSize, sized⟩ := SourceExecutionSize.ForItemsExecute.has_size trace
    exact .inl ⟨sourceSize, finalContext, finalEnvironment, after, finalMap, finalWorld, sized, rest⟩
  · obtain ⟨finalContext, reason, token, after, finalMap, finalWorld, trace, rest⟩ := failed
    obtain ⟨sourceSize, sized⟩ := SourceExecutionSize.ForItemsFault.has_size trace
    exact .inr ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, sized, rest⟩

variable {entry : ProtectedExpressionMeaning.Entry} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode body postCode code : Expr} {selfReason : Word}

variable {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
variable (functions) (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {certificate : GenericExpressionMeaning.Certificate}
  (meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)


theorem condition_preserves_at {size : Nat} {condition : ExpressionId} {node : ExpressionNode}
    (meaningAt : RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (_unique : NodeOccurrencesUnique source)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before condition outcome after) :
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
    meaningAt tree found
      state.1.environments state.1.heaps state.1.locals actualAgrees (.cons .unit (.cons (.cellRef state.1.selfTyped) state.1.actualTyped)) state.2 trace
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, heaps, maps, worlds, frame, metadata⟩



theorem condition_reflects_at {size : Nat} {condition : ExpressionId} {node : ExpressionNode}
    (reflectionAt : RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩ :=
    reflectionAt tree found
      state.1.environments state.1.heaps state.1.locals actualAgrees (.cons .unit (.cons (.cellRef state.1.selfTyped) state.1.actualTyped)) state.2
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩



theorem body_preserves_at {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (correct : ProtectedWhile.Body.PreservesAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨native, read⟩ := state.1.contextRead
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ))) canonical
      (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, _⟩ :=
    correct valid state.1.environments state.1.heaps state.1.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.1.selfTyped) state.1.actualTyped))) reference read state.1.contextUnmapped state.2 trace
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, heaps, maps, worlds, frame, metadata⟩


theorem body_reflects_at {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (correct : ProtectedWhile.Body.ReflectsAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨native, read⟩ := state.1.contextRead
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ))) canonical
      (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, _⟩ :=
    correct valid state.1.environments state.1.heaps state.1.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.1.selfTyped) state.1.actualTyped))) reference read state.1.contextUnmapped state.2
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata⟩

include meaning in
theorem condition_preserves {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (_unique : NodeOccurrencesUnique source)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨size, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  exact condition_preserves_at functions program evidence
    (RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning size) tree found _valid _unique agrees state sized

include reflection in
theorem condition_reflects {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    condition_reflects_at functions program evidence
      (RecursiveNamedBoundedContracts.reflects_at_of_unbounded reflection size) tree found _valid agrees state sized
  exact ⟨outcome, after, finalMap, finalWorld, trace.sound, rest⟩

theorem body_preserves {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (correct : Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : Executes false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨size, sized⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size trace
  exact body_preserves_at functions program evidence
    (ProtectedWhile.Body.preserves_at_of_unbounded functions program evidence correct size) valid agrees reference state sized

theorem body_reflects {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (correct : Reflects functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ finalContext outcome after finalMap finalWorld,
      Executes false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    body_reflects_at functions program evidence
      (ProtectedWhile.Body.reflects_at_of_unbounded functions program evidence correct size) valid agrees reference state sized
  exact ⟨finalContext, outcome, after, finalMap, finalWorld, trace.sound, rest⟩


theorem preserves_of_unprotected {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : TypedLexicalWhile.Preserves functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code) :
    Preserves functions program evidence (entry := entry)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped _installed trace
  exact correct valid environments heaps locals agrees actualTyped reference read unmapped trace

theorem reflects_of_unprotected {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : TypedLexicalWhile.Reflects functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code) :
    Reflects functions program evidence (entry := entry)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped _installed evaluated
  exact correct valid environments heaps locals agrees actualTyped reference read unmapped evaluated

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body
