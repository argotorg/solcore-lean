import Solcore.SourceSemantics.CoreLowering.Internal.Protected.WhileLoops
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.EmittedForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.EmittedPlans

/-!
# Protected contracts: for iterations

Body contracts, generic iteration and endpoints of `for` loops, and header control.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedForBodyContracts
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


theorem condition_preserves_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {condition : ExpressionId} {node : ExpressionNode}
    (meaningAt : RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (_valid : validity context) (_unique : NodeOccurrencesUnique source)
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
  apply condition_preserves_at_for (functions := functions)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
  all_goals assumption

theorem condition_reflects_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {condition : ExpressionId} {node : ExpressionNode}
    (reflectionAt : RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (_valid : validity context)
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
  apply condition_reflects_at_for (functions := functions)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
  all_goals assumption

theorem body_preserves_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (correct : RecursiveNamedLoopContracts.PreservesAtFor functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code)
    (valid : validity context)
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
  apply body_preserves_at_for (functions := functions)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
  all_goals assumption

theorem body_reflects_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (correct : RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code)
    (valid : validity context)
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
  apply body_reflects_at_for (functions := functions)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
  all_goals assumption

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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedForGenericIteration
/-! Finite for iterations combine generic condition certificates with actual
body and post edges. The recursive statement theorem supplies both contracts;
no helper or child execution is stored in a static tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open ProtectedWhile.Body (Preserves)
open TypedImperativeFor (Progress postValues SourceLoop)
open CompatibleExpressionPrimitives (bool_fields)
open ProtectedWhile.Body (Reflects)
open RecursiveNamedForContracts (Below)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)

theorem iterations_success_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.ForLoopExecutes program size context evidence source environment before condition post statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {native : CallableIndexedHistory.NativeFrame} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      Below budget (fun size => ExpressionPreservesAt protocol readiness (context := context) (source := source) (faults := faults)
        program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness guard facts functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      Below budget (fun size => PostPreservesAt protocol readiness guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      exprFacts context condition node → facts context false statements expected →
      ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native → readiness.Ready context state.retained →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ PostReady readiness context outcome reached.retained := by
  induction size using Nat.strongRecOn generalizing context finalContext evidence source environment before after condition post statements outcome with
  | ind size ih =>
    intro budget bounded certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node native faults _
      meaning conditionTree found valid unique agrees reference correct postCorrect conditionFacts bodyFacts state fixedRead guarded ready
    cases trace with
    | done conditionEvaluation =>
      obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress, conditionState, conditionRetained, conditionPost⟩ :=
        condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
      cases represented with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        exact ⟨_, nextStore, nextMap, nextWorld, Core.LoopExecution.condition_false evaluated, .fallthrough environment, progress, conditionState, conditionRetained, conditionPost.1⟩
    | nextFallthrough conditionEvaluation bodyEvaluation postEvaluation next =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
        condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
          body_preserves_at_for (protocol := protocol) (guard := guard) (readiness := readiness) (facts := facts) functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
        cases bodyRelated with
        | fallthrough _ =>
          have bodyTotal := conditionProgress.trans bodyProgress
          obtain ⟨postStore, postMap, postWorld, postEval, postProgress, postState, postRetained, postPost⟩ := (postCorrect _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) bodyState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead bodyTotal.2.2.2.1).2 guarded bodyPost false postEvaluation
          have progress := bodyTotal.trans postProgress
          let nextState := postState
          obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress, finalState, finalRetained, finalPost⟩ :=
            ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded) meaning conditionTree found valid unique agrees reference correct postCorrect conditionFacts bodyFacts nextState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded postPost
          exact ⟨result, finalStore, finalMap, finalWorld,
            ForLoop.body_fallthrough conditionEval bodyEval
              (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
              nextState.live.selfRead nativeTrace, related, progress.trans finalProgress, finalState, protocol.trans (protocol.trans (protocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩
    | nextContinue conditionEvaluation bodyEvaluation postEvaluation next =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
        condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
          body_preserves_at_for (protocol := protocol) (guard := guard) (readiness := readiness) (facts := facts) functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
        cases bodyRelated with
        | continuing _ =>
          have bodyTotal := conditionProgress.trans bodyProgress
          obtain ⟨postStore, postMap, postWorld, postEval, postProgress, postState, postRetained, postPost⟩ := (postCorrect _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) bodyState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead bodyTotal.2.2.2.1).2 guarded bodyPost true postEvaluation
          have progress := bodyTotal.trans postProgress
          let nextState := postState
          obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress, finalState, finalRetained, finalPost⟩ :=
            ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded) meaning conditionTree found valid unique agrees reference correct postCorrect conditionFacts bodyFacts nextState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded postPost
          exact ⟨result, finalStore, finalMap, finalWorld,
            ForLoop.body_continuing conditionEval bodyEval
              (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
              nextState.live.selfRead nativeTrace, related, progress.trans finalProgress, finalState, protocol.trans (protocol.trans (protocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩
    | breaks conditionEvaluation bodyEvaluation =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
        condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
          body_preserves_at_for (protocol := protocol) (guard := guard) (readiness := readiness) (facts := facts) functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
        cases bodyRelated with
        | breaking _ =>
          exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_breaking conditionEval bodyEval, .fallthrough environment, conditionProgress.trans bodyProgress, bodyState, protocol.trans conditionRetained bodyRetained, bodyPost⟩
    | returns conditionEvaluation bodyEvaluation =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
        condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
          body_preserves_at_for (protocol := protocol) (guard := guard) (readiness := readiness) (facts := facts) functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
        cases bodyRelated with
        | returned payload =>
          exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_returned conditionEval bodyEval, .returned payload, conditionProgress.trans bodyProgress, bodyState, protocol.trans conditionRetained bodyRetained, bodyPost⟩

theorem iterations_fault_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ForLoopFaults program size context evidence source environment before condition post statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {native : CallableIndexedHistory.NativeFrame} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      Below budget (fun size => ExpressionPreservesAt protocol readiness (context := context) (source := source) (faults := faults)
        program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness guard facts functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      Below budget (fun size => PostPreservesAt protocol readiness guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      Below budget (fun size => PostFaultsAt protocol readiness guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      exprFacts context condition node → facts context false statements expected →
      ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native → readiness.Ready context state.retained →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ PostReady readiness context (.fault reason) reached.retained := by
  induction size using Nat.strongRecOn generalizing context evidence source environment before after condition post statements reason with
  | ind size ih =>
    intro budget bounded certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node native faults _
      meaning conditionTree found valid unique agrees reference correct postCorrect postFailed conditionFacts bodyFacts state fixedRead guarded ready
    cases trace with
    | condition conditionFault =>
      obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress, conditionState, conditionRetained, conditionPost⟩ :=
        condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.fault conditionFault)
      cases represented with
      | fault matched => exact ⟨_, nextStore, nextMap, nextWorld, Core.LoopExecution.condition_failure evaluated, .fault matched, progress, conditionState, conditionRetained, conditionPost⟩
    | conditionType conditionEvaluation notBoolean runtimeType =>
      obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress, conditionState, conditionRetained, conditionPost⟩ :=
        condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
      cases represented with
      | value payload =>
        obtain ⟨boolean, rfl, _⟩ := bool_fields payload
        exact False.elim (notBoolean trivial)
    | body conditionEvaluation bodyFault =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
        condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
          body_preserves_at_for (protocol := protocol) (guard := guard) (readiness := readiness) (facts := facts) functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.fault bodyFault)
        cases bodyRelated with
        | fault matched => exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_failure conditionEval bodyEval, .fault matched, conditionProgress.trans bodyProgress, bodyState, protocol.trans conditionRetained bodyRetained, bodyPost⟩
    | postFallthrough conditionEvaluation bodyEvaluation postEvaluation =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
        condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
          body_preserves_at_for (protocol := protocol) (guard := guard) (readiness := readiness) (facts := facts) functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
        cases bodyRelated with
        | fallthrough _ =>
          have bodyTotal := conditionProgress.trans bodyProgress
          obtain ⟨token, postStore, postMap, postWorld, postEval, matched, postProgress, postState, postRetained, postPost⟩ :=
            (postFailed _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) bodyState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead bodyTotal.2.2.2.1).2 guarded bodyPost false postEvaluation
          exact ⟨_, postStore, postMap, postWorld,
            ForLoop.body_fallthrough_post_fault conditionEval bodyEval
              (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval),
            .fault matched, bodyTotal.trans postProgress, postState, protocol.trans (protocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
    | postContinue conditionEvaluation bodyEvaluation postEvaluation =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
        condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
          body_preserves_at_for (protocol := protocol) (guard := guard) (readiness := readiness) (facts := facts) functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
        cases bodyRelated with
        | continuing _ =>
          have bodyTotal := conditionProgress.trans bodyProgress
          obtain ⟨token, postStore, postMap, postWorld, postEval, matched, postProgress, postState, postRetained, postPost⟩ :=
            (postFailed _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) bodyState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead bodyTotal.2.2.2.1).2 guarded bodyPost true postEvaluation
          exact ⟨_, postStore, postMap, postWorld,
            ForLoop.body_continuing_post_fault conditionEval bodyEval
              (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval),
            .fault matched, bodyTotal.trans postProgress, postState, protocol.trans (protocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
    | nextFallthrough conditionEvaluation bodyEvaluation postEvaluation next =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
        condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
          body_preserves_at_for (protocol := protocol) (guard := guard) (readiness := readiness) (facts := facts) functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
        cases bodyRelated with
        | fallthrough _ =>
          have bodyTotal := conditionProgress.trans bodyProgress
          obtain ⟨postStore, postMap, postWorld, postEval, postProgress, postState, postRetained, postPost⟩ := (postCorrect _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) bodyState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead bodyTotal.2.2.2.1).2 guarded bodyPost false postEvaluation
          have progress := bodyTotal.trans postProgress
          let nextState := postState
          obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress, finalState, finalRetained, finalPost⟩ :=
            ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded) meaning conditionTree found valid unique agrees reference correct postCorrect postFailed conditionFacts bodyFacts nextState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded postPost
          exact ⟨result, finalStore, finalMap, finalWorld,
            ForLoop.body_fallthrough conditionEval bodyEval
              (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
              nextState.live.selfRead nativeTrace, related, progress.trans finalProgress, finalState, protocol.trans (protocol.trans (protocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩
    | nextContinue conditionEvaluation bodyEvaluation postEvaluation next =>
      obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
        condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
      cases conditionRelated with
      | value payload =>
        obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
        cases sameSource
        subst sameCore
        obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
          body_preserves_at_for (protocol := protocol) (guard := guard) (readiness := readiness) (facts := facts) functions program evidence validity (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
        cases bodyRelated with
        | continuing _ =>
          have bodyTotal := conditionProgress.trans bodyProgress
          obtain ⟨postStore, postMap, postWorld, postEval, postProgress, postState, postRetained, postPost⟩ := (postCorrect _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) bodyState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead bodyTotal.2.2.2.1).2 guarded bodyPost true postEvaluation
          have progress := bodyTotal.trans postProgress
          let nextState := postState
          obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress, finalState, finalRetained, finalPost⟩ :=
            ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded) meaning conditionTree found valid unique agrees reference correct postCorrect postFailed conditionFacts bodyFacts nextState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded postPost
          exact ⟨result, finalStore, finalMap, finalWorld,
            ForLoop.body_continuing conditionEval bodyEval
              (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
              nextState.live.selfRead nativeTrace, related, progress.trans finalProgress, finalState, protocol.trans (protocol.trans (protocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

section BoundedReflection
variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : Scope}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {budget : Nat}
  (reflection : Below budget (fun size => ExpressionReflectsAt protocol readiness (context := context) (source := source) (faults := faults)
        program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size))

include reflection in
theorem iterations_reflect_bounded_for (validity : SourceSemantics.Context → Prop) {condition : ExpressionId} {node : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (conditionFacts : exprFacts context condition node)
    (bodyFacts : facts context false statements expected)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness guard facts functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postCorrect : Below budget (fun size => PostReflectsAt protocol readiness guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
      ∀ {native : CallableIndexedHistory.NativeFrame},
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native → readiness.Ready context state.retained →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedForContracts.ForOutcome program sourceSize context evidence source environment before condition post statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ PostReady readiness context outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before store finalStore value state native fixedRead guarded ready evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, conditionSmaller, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionSourceSize, conditionOutcome, conditionHeap, conditionMap, conditionWorld, conditionTrace, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
      condition_reflects_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (reflection _ (Nat.lt_of_lt_of_le conditionSmaller bounded)) conditionTree found conditionFacts agrees state ready conditionEval
    cases conditionRelated with
    | fault matched =>
      cases conditionTrace with
      | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure conditionEval.sound)
        exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .fault (.condition failed), .fault matched, conditionProgress, conditionState, conditionRetained, conditionPost⟩
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      subst sameSource
      subst sameCore
      cases conditionTrace with
      | value conditionTrace =>
        cases boolean with
        | false =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false conditionEval.sound)
          exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .control (.done conditionTrace), .fallthrough environment, conditionProgress, conditionState, conditionRetained, conditionPost.1⟩
        | true =>
          obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch conditionEval.sound
          obtain ⟨bodySize, bodyStore, bodyValue, bodySmaller, bodyEval⟩ := branch.bind_computation
          obtain ⟨bodySourceSize, bodyContext, bodyOutcome, bodyHeap, bodyMap, bodyWorld, bodyTrace, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
            body_reflects_at_for (protocol := protocol) (guard := guard) (readiness := readiness) (facts := facts) functions program evidence validity
              (correct _ (Nat.lt_of_lt_of_le bodySmaller (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))) valid bodyFacts agrees reference conditionState
            (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 bodyEval
          have progress := conditionProgress.trans bodyProgress
          cases bodyRelated with
          | fault matched =>
            cases bodyTrace with
            | control impossible => exact False.elim (bodyCannotFault impossible.sound)
            | fault failed =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_failure conditionEval.sound bodyEval.sound)
              exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .fault (.body conditionTrace failed), .fault matched, progress, bodyState, protocol.trans conditionRetained bodyRetained, bodyPost⟩
          | returned payload =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_returned conditionEval.sound bodyEval.sound)
              exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .control (.returns conditionTrace bodyTrace), .returned payload, progress, bodyState, protocol.trans conditionRetained bodyRetained, bodyPost⟩
          | breaking bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_breaking conditionEval.sound bodyEval.sound)
              exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .control (.breaks conditionTrace bodyTrace), .fallthrough environment, progress, bodyState, protocol.trans conditionRetained bodyRetained, bodyPost⟩
          | fallthrough bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨postSize, postStore, postValue, postSmaller, postEval⟩ := RecursiveNamedForContracts.post_computation_size false branch bodyEval.sound
              rcases (postCorrect _ (Nat.lt_of_lt_of_le postSmaller (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))) bodyState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded bodyPost false postEval with done | failed
              · obtain ⟨postSourceSize, postContext, postEnvironment, postHeap, postMap, postWorld, postTrace, rfl, postProgress, postState, postRetained, postPost⟩ := done
                have prefixProgress := progress.trans postProgress
                let nextState := postState
                obtain ⟨nextSize, smaller, nextEval⟩ := ForLoop.next_fallthrough branch bodyEval.sound postEval.sound nextState.live.selfRead
                obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress, finalState, finalRetained, finalPost⟩ :=
                  ih nextSize (Nat.lt_trans smaller branchSmaller)
                    (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) nextState
                    (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead prefixProgress.2.2.2.1).2 guarded postPost nextEval
                cases nextTrace with
                | control nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .control (.nextFallthrough conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress, finalState, protocol.trans (protocol.trans (protocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩
                | fault nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .fault (.nextFallthrough conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress, finalState, protocol.trans (protocol.trans (protocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩
              · obtain ⟨postSourceSize, postContext, reason, token, postHeap, postMap, postWorld, postTrace, rfl, matched, postProgress, postState, postRetained, postPost⟩ := failed
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                  (ForLoop.body_fallthrough_post_fault conditionEval.sound bodyEval.sound postEval.sound)
                exact ⟨_, _, postHeap, postMap, postWorld, .fault (.postFallthrough conditionTrace bodyTrace postTrace), .fault matched, progress.trans postProgress, postState, protocol.trans (protocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
          | continuing bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨postSize, postStore, postValue, postSmaller, postEval⟩ := RecursiveNamedForContracts.post_computation_size true branch bodyEval.sound
              rcases (postCorrect _ (Nat.lt_of_lt_of_le postSmaller (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))) bodyState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded bodyPost true postEval with done | failed
              · obtain ⟨postSourceSize, postContext, postEnvironment, postHeap, postMap, postWorld, postTrace, rfl, postProgress, postState, postRetained, postPost⟩ := done
                have prefixProgress := progress.trans postProgress
                let nextState := postState
                obtain ⟨nextSize, smaller, nextEval⟩ := ForLoop.next_continuing branch bodyEval.sound postEval.sound nextState.live.selfRead
                obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress, finalState, finalRetained, finalPost⟩ :=
                  ih nextSize (Nat.lt_trans smaller branchSmaller)
                    (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) nextState
                    (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead prefixProgress.2.2.2.1).2 guarded postPost nextEval
                cases nextTrace with
                | control nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .control (.nextContinue conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress, finalState, protocol.trans (protocol.trans (protocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩
                | fault nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .fault (.nextContinue conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress, finalState, protocol.trans (protocol.trans (protocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩
              · obtain ⟨postSourceSize, postContext, reason, token, postHeap, postMap, postWorld, postTrace, rfl, matched, postProgress, postState, postRetained, postPost⟩ := failed
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                  (ForLoop.body_continuing_post_fault conditionEval.sound bodyEval.sound postEval.sound)
                exact ⟨_, _, postHeap, postMap, postWorld, .fault (.postContinue conditionTrace bodyTrace postTrace), .fault matched, progress.trans postProgress, postState, protocol.trans (protocol.trans conditionRetained bodyRetained) postRetained, postPost⟩


end BoundedReflection
end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful.WithReady

namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open ProtectedWhile.Body (Preserves)
open TypedImperativeFor (Progress postValues SourceLoop)
open CompatibleExpressionPrimitives (bool_fields)
open ProtectedWhile.Body (Reflects)
open RecursiveNamedForContracts (Below)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
theorem iterations_success_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.ForLoopExecutes program size context evidence source environment before condition post statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {native : CallableIndexedHistory.NativeFrame} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults size) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      Below budget (fun size => PostPreservesAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by

  intro budget bounded certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node native faults _
      meaning conditionTree found valid unique agrees reference correct postCorrect state fixedRead guarded
  obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, related, progress, reached, retained, _post⟩ :=
    WithReady.iterations_success_bounded_for (protocol := protocol) (guard := guard)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) (facts := fun _ _ _ _ => True) validity trace budget bounded
      (fun child strict => ProtectedWhile.Body.Stateful.WithReady.expression_preserves_trivial protocol (meaning child strict))
      conditionTree found valid unique agrees reference
      (fun child strict => ProtectedWhile.Body.Stateful.WithReady.body_preserves_trivial protocol guard functions program evidence validity (correct child strict))
      (fun child strict => WithReady.post_preserves_trivial protocol guard child functions program evidence post postCode (postCorrect child strict))
      True.intro True.intro state fixedRead guarded True.intro
  exact ⟨value, finalStore, finalMap, finalWorld, nativeTrace, related, progress, reached, retained⟩

theorem iterations_fault_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ForLoopFaults program size context evidence source environment before condition post statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {native : CallableIndexedHistory.NativeFrame} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults size) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      Below budget (fun size => PostPreservesAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      Below budget (fun size => PostFaultsAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by

  intro budget bounded certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node native faults _
      meaning conditionTree found valid unique agrees reference correct postCorrect postFailed state fixedRead guarded
  obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, related, progress, reached, retained, _post⟩ :=
    WithReady.iterations_fault_bounded_for (protocol := protocol) (guard := guard)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) (facts := fun _ _ _ _ => True) validity trace budget bounded
      (fun child strict => ProtectedWhile.Body.Stateful.WithReady.expression_preserves_trivial protocol (meaning child strict))
      conditionTree found valid unique agrees reference
      (fun child strict => ProtectedWhile.Body.Stateful.WithReady.body_preserves_trivial protocol guard functions program evidence validity (correct child strict))
      (fun child strict => WithReady.post_preserves_trivial protocol guard child functions program evidence post postCode (postCorrect child strict))
      (fun child strict => WithReady.post_faults_trivial protocol guard child functions program evidence post postCode (postFailed child strict))
      True.intro True.intro state fixedRead guarded True.intro
  exact ⟨value, finalStore, finalMap, finalWorld, nativeTrace, related, progress, reached, retained⟩

section BoundedReflection
variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : Scope}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {budget : Nat}
  (reflection : Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults size))

include reflection in
theorem iterations_reflect_bounded_for (validity : SourceSemantics.Context → Prop) {condition : ExpressionId} {node : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postCorrect : Below budget (fun size => PostReflectsAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
      ∀ {native : CallableIndexedHistory.NativeFrame},
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedForContracts.ForOutcome program sourceSize context evidence source environment before condition post statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  intro size bounded mapping world before store finalStore value state native fixedRead guarded evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress, reached, retained, _post⟩ :=
    WithReady.iterations_reflect_bounded_for (protocol := protocol) (guard := guard)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) (facts := fun _ _ _ _ => True) functions program evidence
      (fun child strict => ProtectedWhile.Body.Stateful.WithReady.expression_reflects_trivial protocol (reflection child strict))
      validity conditionTree found True.intro True.intro valid agrees reference
      (fun child strict => ProtectedWhile.Body.Stateful.WithReady.body_reflects_trivial protocol guard functions program evidence validity (correct child strict))
      (fun child strict => WithReady.post_reflects_trivial protocol guard child functions program evidence faults post postCode (postCorrect child strict))
      bodyCannotFault size bounded state fixedRead guarded True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress, reached, retained⟩

end BoundedReflection
end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful


namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open ProtectedWhile.Body (Preserves)
open TypedImperativeFor (Progress postValues SourceLoop)
open CompatibleExpressionPrimitives (bool_fields)
open ProtectedWhile.Body (Reflects)
open RecursiveNamedForContracts (Below)
section LegacyPosts
variable {entry : ProtectedExpressionMeaning.Entry} {size : Nat}
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (transport : ProtectedExpressionMeaning.Transport entry)
  {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
  {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
  {faults : FunctionCalls.FaultRep} {items : List ForItemForm} {code : Expr}

include transport in
theorem legacy_post_preserves
    (meaning : RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry)
      (registry := registry) (source := source) (context := context) (scope := scope)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) items code) :
    Stateful.PostPreservesAt (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True)
      size functions program evidence (registry := registry) (source := source) (context := context) (scope := scope)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) items code := by
  intro mapping world before after store finalContext finalEnvironment state native _read _guarded continued trace
  obtain ⟨finalStore, finalMap, finalWorld, evaluated, progress⟩ := meaning ⟨state.live, state.retained.down⟩ continued trace
  obtain ⟨reached, related⟩ := state.reach progress
    (ProtectedStateTransition.AdministrativeTransport.transition _
      (ProtectedStateTransition.Lexical.legacyTransport transport) state.retained
      progress.2.1 progress.2.2.1 progress.2.2.2.1 progress.2.2.2.2)
  exact ⟨finalStore, finalMap, finalWorld, evaluated, progress, reached, related⟩

include transport in
theorem legacy_post_faults
    (meaning : RecursiveNamedForContracts.PostFaultsAt size functions program evidence (entry := entry)
      (registry := registry) (source := source) (context := context) (scope := scope) (faults := faults)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) items code) :
    Stateful.PostFaultsAt (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True)
      size functions program evidence (registry := registry) (source := source) (context := context) (scope := scope) (faults := faults)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) items code := by
  intro mapping world before after store finalContext reason state native _read _guarded continued trace
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, progress⟩ := meaning ⟨state.live, state.retained.down⟩ continued trace
  obtain ⟨reached, related⟩ := state.reach progress
    (ProtectedStateTransition.AdministrativeTransport.transition _
      (ProtectedStateTransition.Lexical.legacyTransport transport) state.retained
      progress.2.1 progress.2.2.1 progress.2.2.2.1 progress.2.2.2.2)
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, progress, reached, related⟩

include transport in
theorem legacy_post_reflects
    (meaning : RecursiveNamedForContracts.PostReflectsAt size functions program evidence (entry := entry)
      (registry := registry) (source := source) (context := context) (scope := scope)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) faults items code) :
    Stateful.PostReflectsAt (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True)
      size functions program evidence (registry := registry) (source := source) (context := context) (scope := scope)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) faults items code := by
  intro mapping world before store finalStore value state native _read _guarded continued evaluated
  rcases meaning ⟨state.live, state.retained.down⟩ continued evaluated with success | failure
  · obtain ⟨sourceSize, finalContext, finalEnvironment, after, finalMap, finalWorld, trace, sameValue, progress⟩ := success
    obtain ⟨reached, related⟩ := state.reach progress
      (ProtectedStateTransition.AdministrativeTransport.transition _
        (ProtectedStateTransition.Lexical.legacyTransport transport) state.retained
        progress.2.1 progress.2.2.1 progress.2.2.2.1 progress.2.2.2.2)
    exact Or.inl ⟨sourceSize, finalContext, finalEnvironment, after, finalMap, finalWorld, trace, sameValue, progress, reached, related⟩
  · obtain ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, sameValue, matched, progress⟩ := failure
    obtain ⟨reached, related⟩ := state.reach progress
      (ProtectedStateTransition.AdministrativeTransport.transition _
        (ProtectedStateTransition.Lexical.legacyTransport transport) state.retained
        progress.2.1 progress.2.2.1 progress.2.2.2.1 progress.2.2.2.2)
    exact Or.inr ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, sameValue, matched, progress, reached, related⟩
end LegacyPosts

theorem iterations_success_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.ForLoopExecutes program size context evidence source environment before condition post statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
    meaning transport conditionTree found valid unique agrees reference correct postCorrect state
  obtain ⟨native, fixedRead⟩ := state.1.contextRead
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, _reached, _retained⟩ :=
    Stateful.iterations_success_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) (validity := validity) trace budget bounded
      (fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        (expressions := fun _ => certificate) functions program evidence transport (meaning child childBound))
      conditionTree found valid unique agrees reference
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.preserves_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_preserves functions program evidence transport (correct child childBound)))
      (fun child childBound => legacy_post_preserves functions program evidence transport (postCorrect child childBound))
      ⟨state.1, ⟨state.2⟩⟩ fixedRead True.intro
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩

theorem iterations_success_bounded
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.ForLoopExecutes program size context evidence source environment before condition post statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => ProtectedWhile.Body.PreservesAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      meaning transport conditionTree found valid unique agrees reference correct postCorrect state
  exact iterations_success_bounded_for (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    trace budget bounded meaning transport conditionTree found valid unique agrees reference correct postCorrect state

theorem iterations_fault_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ForLoopFaults program size context evidence source environment before condition post statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      Below budget (fun size => RecursiveNamedForContracts.PostFaultsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
    meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
  obtain ⟨native, fixedRead⟩ := state.1.contextRead
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, _reached, _retained⟩ :=
    Stateful.iterations_fault_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) (validity := validity) trace budget bounded
      (fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        (expressions := fun _ => certificate) functions program evidence transport (meaning child childBound))
      conditionTree found valid unique agrees reference
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.preserves_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_preserves functions program evidence transport (correct child childBound)))
      (fun child childBound => legacy_post_preserves functions program evidence transport (postCorrect child childBound))
      (fun child childBound => legacy_post_faults functions program evidence transport (postFailed child childBound))
      ⟨state.1, ⟨state.2⟩⟩ fixedRead True.intro
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩

theorem iterations_fault_bounded
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ForLoopFaults program size context evidence source environment before condition post statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => ProtectedWhile.Body.PreservesAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      Below budget (fun size => RecursiveNamedForContracts.PostFaultsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
  exact iterations_fault_bounded_for (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    trace budget bounded meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state

section BoundedReflection
variable {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : Scope}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {budget : Nat}
  (reflection : Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry))
  (transport : ProtectedExpressionMeaning.Transport entry)

include reflection transport in
theorem iterations_reflect_bounded_for (validity : SourceSemantics.Context → Prop) {condition : ExpressionId} {node : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postCorrect : Below budget (fun size => RecursiveNamedForContracts.PostReflectsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedForContracts.ForOutcome program sourceSize context evidence source environment before condition post statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro size bounded mapping world before store finalStore value state evaluated
  obtain ⟨native, fixedRead⟩ := state.1.contextRead
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress, _reached, _retained⟩ :=
    Stateful.iterations_reflect_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
      (reflection := fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_reflects
        (expressions := fun _ => certificate) functions program evidence transport (reflection child childBound))
      conditionTree found valid agrees reference
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.reflects_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_reflects functions program evidence transport (correct child childBound)))
      (fun child childBound => legacy_post_reflects functions program evidence transport (postCorrect child childBound))
      bodyCannotFault size bounded ⟨state.1, ⟨state.2⟩⟩ fixedRead True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress⟩

include reflection transport in
theorem iterations_reflect_bounded {condition : ExpressionId} {node : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => ProtectedWhile.Body.ReflectsAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postCorrect : Below budget (fun size => RecursiveNamedForContracts.PostReflectsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedForContracts.ForOutcome program sourceSize context evidence source environment before condition post statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  apply iterations_reflect_bounded_for (functions := functions)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
  all_goals assumption

end BoundedReflection
theorem iterations_success
    {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.ForLoopExecutes program context evidence source environment before condition post statements finalContext outcome after) :
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      PostPreserves functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
    meaning transport conditionTree found valid unique agrees reference correct postCorrect state
  obtain ⟨size, sized⟩ := SourceExecutionSize.ForLoopExecutes.has_size trace
  exact iterations_success_bounded sized size (Nat.le_refl _)
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning child)
    transport conditionTree found valid unique agrees reference
    (fun child _ => ProtectedWhile.Body.preserves_at_of_unbounded functions program evidence correct child)
    (fun child _ => postpreserves_at_of_unbounded functions program evidence post postCode postCorrect child) state

theorem iterations_fault
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForLoopFaults program context evidence source environment before condition post statements reason after) :
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry →
      ProtectedExpressionMeaning.Transport entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      PostPreserves functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      PostFaults functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
    meaning transport conditionTree found valid unique agrees reference correct postCorrect postFailed state
  obtain ⟨size, sized⟩ := SourceExecutionSize.ForLoopFaults.has_size trace
  exact iterations_fault_bounded sized size (Nat.le_refl _)
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning child)
    transport conditionTree found valid unique agrees reference
    (fun child _ => ProtectedWhile.Body.preserves_at_of_unbounded functions program evidence correct child)
    (fun child _ => postpreserves_at_of_unbounded functions program evidence post postCode postCorrect child)
    (fun child _ => postfaults_at_of_unbounded functions program evidence post postCode postFailed child) state

variable {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : Scope}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  (transport : ProtectedExpressionMeaning.Transport entry)

include reflection transport in
theorem iterations_reflect {condition : ExpressionId} {node : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Reflects functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (postCorrect : PostReflects functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode)
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat) {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ outcome after finalMap finalWorld,
        SourceLoop program context evidence source environment before condition post statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro size mapping world before store finalStore value state evaluation
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    iterations_reflect_bounded functions program evidence
      (fun child _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded reflection child)
      transport conditionTree found valid agrees reference
      (fun child _ => ProtectedWhile.Body.reflects_at_of_unbounded functions program evidence correct child)
      (fun child _ => postreflects_at_of_unbounded functions program evidence faults post postCode postCorrect child)
      bodyCannotFault size (Nat.le_refl _) state evaluation
  exact ⟨outcome, after, finalMap, finalWorld, trace.sound, rest⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedForGenericEndpoint
/-! The actual for installation and invocation surround the shared finite
proof. Post callbacks are induction results on the real captured environment;
the protected entry remains canonical through all hidden slots and effects. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep installedStore installedWorld)
open TypedImperativeFor (SourceLoop initial_state)
open ProtectedWhile.Body (Preserves Reflects)
open RecursiveNamedForContracts (Below)
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {certificate : GenericExpressionMeaning.Certificate}
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
  (transport : AdministrativeTransport protocol)
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (activation : ActivationTransfers protocol readiness)
def LoopPreservesAtFor (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol) (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment) (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_guarded : guard contextLocation native)
    (_ready : readiness.Ready context initial)
    (_trace : RecursiveNamedForContracts.ForOutcome program size context evidence source environment before condition post statements outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def LoopReflectsAtFor (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol) (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment) (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_guarded : guard contextLocation native)
    (_ready : readiness.Ready context initial)
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedForContracts.ForOutcome program sourceSize context evidence source environment before condition post statements outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩


variable {scope : Scope} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}

include transport activation in
theorem loop_preserves_bounded_for [FunctionCalls.FaultTokens faults] (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaningB : Below budget (fun size => ExpressionPreservesAt protocol readiness (context := context) (source := source) (faults := faults)
      program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size)) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionFacts : exprFacts context condition conditionNode)
    (bodyFacts : facts context false statements expected)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness guard facts functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postPreserves : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => PostPreservesAt protocol readiness guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode))
    (postFaults : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => PostFaultsAt protocol readiness guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode)) :
    ∀ size, size ≤ budget → LoopPreservesAtFor protocol readiness guard functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro size bounded valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped initial guarded ready trace
  obtain ⟨protectedState, installedProgress, installedRelated, _installedRecords⟩ :=
    ProtectedStateTransition.For.initial_state transport environments heaps locals agrees actualTyped read unmapped typed initial
  have activated := activation.ready initial protectedState.retained installedProgress.2.2.2.1
    installedRelated _installedRecords ready
  have installedRead := (TypedLexicalWhile.retain unmapped read installedProgress.2.2.2.1).2
  have postCorrect : Below budget (fun size => PostPreservesAt protocol readiness guard size functions program evidence
      (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := store.length) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) :=
    postPreserves agrees reference valid
  have postFailed : Below budget (fun size => PostFaultsAt protocol readiness guard size functions program evidence
      (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := store.length) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode) :=
    postFaults agrees reference valid
  cases trace with
  | control sourceTrace =>
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress, reached, retained, postReady⟩ :=
      iterations_success_bounded_for (protocol := protocol) (guard := guard) (readiness := readiness) (exprFacts := exprFacts) (facts := facts) validity sourceTrace budget bounded meaningB conditionTree conditionFound valid unique agrees reference correct postCorrect conditionFacts bodyFacts protectedState installedRead guarded activated
    exact ⟨value, finalStore, finalMap, finalWorld,
      by
        rw [LoopRenaming.iterate]
        apply LocalLoop.iterate_evaluates
        exact LocalLoop.invoke_success _ _ (.var rfl) protectedState.live.selfRead nativeTrace,
      represented, (installedProgress.trans progress).1,
      (installedProgress.trans progress).2.1, (installedProgress.trans progress).2.2.1,
      (installedProgress.trans progress).2.2.2.1, (installedProgress.trans progress).2.2.2.2,
      ⟨reached.retained, protocol.trans installedRelated retained, postReady⟩⟩
  | fault failed =>
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress, reached, retained, postReady⟩ :=
      iterations_fault_bounded_for (protocol := protocol) (guard := guard) (readiness := readiness) (exprFacts := exprFacts) (facts := facts) validity failed budget bounded meaningB conditionTree conditionFound valid unique agrees reference correct postCorrect postFailed conditionFacts bodyFacts protectedState installedRead guarded activated
    exact ⟨value, finalStore, finalMap, finalWorld,
      by
        rw [LoopRenaming.iterate]
        apply LocalLoop.iterate_evaluates
        exact LocalLoop.invoke_success _ _ (.var rfl) protectedState.live.selfRead nativeTrace,
      represented, (installedProgress.trans progress).1,
      (installedProgress.trans progress).2.1, (installedProgress.trans progress).2.2.1,
      (installedProgress.trans progress).2.2.2.1, (installedProgress.trans progress).2.2.2.2,
      ⟨reached.retained, protocol.trans installedRelated retained, postReady⟩⟩

include transport activation in
theorem loop_reflects_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (reflectionB : Below budget (fun size => ExpressionReflectsAt protocol readiness (context := context) (source := source) (faults := faults)
      program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size))
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionFacts : exprFacts context condition conditionNode)
    (bodyFacts : facts context false statements expected)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness guard facts functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False)
    (postReflects : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => PostReflectsAt protocol readiness guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode)) :
    ∀ size, size ≤ budget → LoopReflectsAtFor protocol readiness guard functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro size bounded valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial guarded ready evaluated
  obtain ⟨protectedState, installedProgress, installedRelated, _installedRecords⟩ :=
    ProtectedStateTransition.For.initial_state transport environments heaps locals agrees actualTyped read unmapped typed initial
  have activated := activation.ready initial protectedState.retained installedProgress.2.2.2.1
    installedRelated _installedRecords ready
  have installedRead := (TypedLexicalWhile.retain unmapped read installedProgress.2.2.2.1).2
  have postCorrect : Below budget (fun size => PostReflectsAt protocol readiness guard size functions program evidence
      (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := store.length) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode) :=
    postReflects agrees reference valid
  rw [LoopRenaming.iterate] at evaluated
  obtain ⟨entrySize, entrySmaller, nativeEntry⟩ := evaluated.iterate_entry
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress, reached, retained, postReady⟩ :=
    iterations_reflect_bounded_for (protocol := protocol) (guard := guard) (readiness := readiness) (exprFacts := exprFacts) (facts := facts) functions program evidence reflectionB validity conditionTree conditionFound conditionFacts bodyFacts valid agrees reference correct
      postCorrect bodyCannotFault entrySize (Nat.le_trans (Nat.le_of_lt entrySmaller) bounded) protectedState installedRead guarded activated nativeEntry
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
    (installedProgress.trans progress).1, (installedProgress.trans progress).2.1,
    (installedProgress.trans progress).2.2.1, (installedProgress.trans progress).2.2.2.1,
    (installedProgress.trans progress).2.2.2.2, ⟨reached.retained, protocol.trans installedRelated retained, postReady⟩⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful.WithReady
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep installedStore installedWorld)
open TypedImperativeFor (SourceLoop initial_state)
open ProtectedWhile.Body (Preserves Reflects)
open RecursiveNamedForContracts (Below)
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {certificate : GenericExpressionMeaning.Certificate}
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
  (transport : AdministrativeTransport protocol)
def LoopPreservesAtFor (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment) (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_guarded : guard contextLocation native)
    (_trace : RecursiveNamedForContracts.ForOutcome program size context evidence source environment before condition post statements outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def LoopReflectsAtFor (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment) (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_guarded : guard contextLocation native)
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedForContracts.ForOutcome program sourceSize context evidence source environment before condition post statements outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩


variable {scope : Scope} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}

include transport in
theorem loop_preserves_bounded_for [FunctionCalls.FaultTokens faults] (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaningB : Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults size)) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postPreserves : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => PostPreservesAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode))
    (postFaults : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => PostFaultsAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode)) :
    ∀ size, size ≤ budget → LoopPreservesAtFor protocol guard functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro size bounded valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped initial guarded trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, _post⟩ :=
    WithReady.loop_preserves_bounded_for functions program evidence protocol guard transport
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) (facts := fun _ _ _ _ => True) (WithReady.ActivationTransfers.trivial protocol)
      validity budget
      (fun child strict => ProtectedWhile.Body.Stateful.WithReady.expression_preserves_trivial protocol (meaningB child strict))
      conditionFound True.intro True.intro conditionTree typed unique
      (fun child strict => ProtectedWhile.Body.Stateful.WithReady.body_preserves_trivial protocol guard functions program evidence validity (correct child strict))
      (fun agrees reference valid child strict => WithReady.post_preserves_trivial protocol guard child functions program evidence post postCode (postPreserves agrees reference valid child strict))
      (fun agrees reference valid child strict => WithReady.post_faults_trivial protocol guard child functions program evidence post postCode (postFaults agrees reference valid child strict))
      size bounded valid environments heaps locals agrees actualTyped reference read unmapped initial guarded True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩

include transport in
theorem loop_reflects_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (reflectionB : Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults size))
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Below budget (fun size => ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False)
    (postReflects : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => PostReflectsAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode)) :
    ∀ size, size ≤ budget → LoopReflectsAtFor protocol guard functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro size bounded valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial guarded completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, _post⟩ :=
    WithReady.loop_reflects_bounded_for functions program evidence protocol guard transport
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) (facts := fun _ _ _ _ => True) (WithReady.ActivationTransfers.trivial protocol)
      validity budget
      (fun child strict => ProtectedWhile.Body.Stateful.WithReady.expression_reflects_trivial protocol (reflectionB child strict))
      conditionFound True.intro True.intro conditionTree typed
      (fun child strict => ProtectedWhile.Body.Stateful.WithReady.body_reflects_trivial protocol guard functions program evidence validity (correct child strict))
      bodyCannotFault
      (fun agrees reference valid child strict => WithReady.post_reflects_trivial protocol guard child functions program evidence faults post postCode (postReflects agrees reference valid child strict))
      size bounded valid environments heaps locals agrees actualTyped reference read unmapped initial guarded True.intro completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful


namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep installedStore installedWorld)
open TypedImperativeFor (SourceLoop initial_state)
open ProtectedWhile.Body (Preserves Reflects)
open RecursiveNamedForContracts (Below)
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  {certificate : GenericExpressionMeaning.Certificate}
  (meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)

def LoopPreservesFor (validity : SourceSemantics.Context → Prop) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_installed : entry scope mapping world before store canonical)
    (_trace : SourceLoop program context evidence source environment before condition post statements outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical

def LoopPreserves {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  LoopPreservesFor (entry := entry) (source := source) (context := context)
    (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals)
    (administrative := administrative) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (scope := scope) condition post statements expected type code

def LoopReflectsFor (validity : SourceSemantics.Context → Prop) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_installed : entry scope mapping world before store canonical)
    (_evaluated : Evaluates actual store (code.rename ξ) value finalStore),
    ∃ outcome after finalMap finalWorld,
      SourceLoop program context evidence source environment before condition post statements outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical

def LoopReflects {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  LoopReflectsFor (entry := entry) (source := source) (context := context)
    (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals)
    (administrative := administrative) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (scope := scope) condition post statements expected type code

variable {scope : Scope} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}

include transport in
theorem loop_preserves_bounded_for [FunctionCalls.FaultTokens faults] (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaningB : Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postPreserves : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode))
    (postFaults : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => RecursiveNamedForContracts.PostFaultsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode)) :
    ∀ size, size ≤ budget → RecursiveNamedForContracts.LoopPreservesAtFor (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro size bounded valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata, transition⟩ :=
    Stateful.loop_preserves_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) (transport := ProtectedStateTransition.Lexical.legacyTransport transport)
      (functions := functions) (program := program) (evidence := evidence) validity budget
      (fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        (expressions := fun _ => certificate) functions program evidence transport (meaningB child childBound))
      conditionFound conditionTree typed unique
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.preserves_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_preserves functions program evidence transport (correct child childBound)))
      (fun agrees reference valid child childBound => legacy_post_preserves functions program evidence transport
        (postPreserves agrees reference valid child childBound))
      (fun agrees reference valid child childBound => legacy_post_faults functions program evidence transport
        (postFaults agrees reference valid child childBound))
      size bounded valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ True.intro trace
  obtain ⟨reached, _related⟩ := transition
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata, reached.down⟩
include transport in
theorem loop_preserves_bounded [FunctionCalls.FaultTokens faults] (budget : Nat)
    (meaningB : Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => ProtectedWhile.Body.PreservesAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postPreserves : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      CompatibleExpressionLiterals.ContextValid solved context evidence →
      Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode))
    (postFaults : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      CompatibleExpressionLiterals.ContextValid solved context evidence →
      Below budget (fun size => RecursiveNamedForContracts.PostFaultsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode)) :
    ∀ size, size ≤ budget → RecursiveNamedForContracts.LoopPreservesAt (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  apply loop_preserves_bounded_for (functions := functions)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
  all_goals assumption

include transport in
theorem loop_reflects_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (reflectionB : Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry))
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False)
    (postReflects : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => RecursiveNamedForContracts.PostReflectsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode)) :
    ∀ size, size ≤ budget → RecursiveNamedForContracts.LoopReflectsAtFor (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro size bounded valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, metadata, transition⟩ :=
    Stateful.loop_reflects_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) (transport := ProtectedStateTransition.Lexical.legacyTransport transport)
      (functions := functions) (program := program) (evidence := evidence) validity budget
      (fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_reflects
        (expressions := fun _ => certificate) functions program evidence transport (reflectionB child childBound))
      conditionFound conditionTree typed
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.reflects_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_reflects functions program evidence transport (correct child childBound)))
      bodyCannotFault
      (fun agrees reference valid child childBound => legacy_post_reflects functions program evidence transport
        (postReflects agrees reference valid child childBound))
      size bounded valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ True.intro evaluated
  obtain ⟨reached, _related⟩ := transition
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, metadata, reached.down⟩
include transport in
theorem loop_reflects_bounded (budget : Nat)
    (reflectionB : Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry))
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Below budget (fun size => ProtectedWhile.Body.ReflectsAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False)
    (postReflects : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      CompatibleExpressionLiterals.ContextValid solved context evidence →
      Below budget (fun size => RecursiveNamedForContracts.PostReflectsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode)) :
    ∀ size, size ≤ budget → RecursiveNamedForContracts.LoopReflectsAt (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  apply loop_reflects_bounded_for (functions := functions)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
  all_goals assumption

include transport meaning in
theorem loop_preserves [FunctionCalls.FaultTokens faults] {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (postPreserves : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      CompatibleExpressionLiterals.ContextValid solved context evidence →
      PostPreserves functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode)
    (postFaults : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      CompatibleExpressionLiterals.ContextValid solved context evidence →
      PostFaults functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode) :
    LoopPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨size, sized⟩ := RecursiveNamedForContracts.ForOutcome.has_size trace
  exact loop_preserves_bounded functions program evidence transport size
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning child)
    conditionFound conditionTree typed unique
    (fun child _ => ProtectedWhile.Body.preserves_at_of_unbounded functions program evidence correct child)
    (fun agrees reference valid child _ => postpreserves_at_of_unbounded functions program evidence post postCode
      (postPreserves agrees reference valid) child)
    (fun agrees reference valid child _ => postfaults_at_of_unbounded functions program evidence post postCode
      (postFaults agrees reference valid) child)
    size (Nat.le_refl _) valid environments heaps locals agrees actualTyped reference read unmapped installed sized

include transport reflection in
theorem loop_reflects
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Reflects functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False)
    (postReflects : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      CompatibleExpressionLiterals.ContextValid solved context evidence →
      PostReflects functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode) :
    LoopReflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    loop_reflects_bounded functions program evidence transport size
      (fun child _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded reflection child)
      conditionFound conditionTree typed
      (fun child _ => ProtectedWhile.Body.reflects_at_of_unbounded functions program evidence correct child)
      bodyCannotFault
      (fun agrees reference valid child _ => postreflects_at_of_unbounded functions program evidence faults post postCode
        (postReflects agrees reference valid) child)
      size (Nat.le_refl _) valid environments heaps locals agrees actualTyped reference read unmapped installed sized
  exact ⟨outcome, after, finalMap, finalWorld, trace.sound, rest⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderControl
/-! Static header trees are shared with the generic grammar. A dynamic stopping
receipt pairs its actual typed prefix with the protected installed observations.
The receipt contains no meaning or execution of its syntactic continuation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Fallthrough)
abbrev Tree := GenericForHeader.Tree
abbrev Scope := GenericForHeader.Scope
abbrev ValuesContext := GenericForHeader.ValuesContext

structure TailFor (validity : SourceSemantics.Context → Prop) {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame)
    (continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    extends TypedForHeader.TailFor validity registry functions source solved evidence administrative frame globals
      contextLocation native continuation context environment heap where
  installed : entry scope mapping world heap store canonical

abbrev Tail {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame)
    (continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap) :=
  TailFor (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation context environment heap

inductive ResultFor (validity : SourceSemantics.Context → Prop) {entry : ProtectedExpressionMeaning.Entry} {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (program : Program) (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame) (type : Ty) (faults : FunctionCalls.FaultRep)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (mapping : LocationMap) (world : StoreTyping) (store : Store)
    (value : Value) (finalStore : Store) : Prop where
  | continues {finalContext finalEnvironment after}
      (tail : TailFor validity (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after)
      (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after)
      (maps : LocationMap.Extends mapping tail.mapping) (worlds : WorldExtends world tail.world)
      (preservation : AdministrativePreserved mapping store tail.mapping tail.store)
      (metadata : Dynamic.HeapMetadataExtend before after)
      (remaining : Evaluates tail.actual tail.store (tail.code.rename tail.embedding) value finalStore) :
      ResultFor validity (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
        context environment before items mapping world store value finalStore
  | fault {finalContext reason token after finalMap finalWorld}
      (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after)
      (same : value = .inLeft (LocalLoop.controlType type) (.word token)) (matched : faults reason token)
      (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (preservation : AdministrativePreserved mapping store finalMap finalStore)
      (metadata : Dynamic.HeapMetadataExtend before after) :
      ResultFor validity (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
        context environment before items mapping world store value finalStore

abbrev Result {entry : ProtectedExpressionMeaning.Entry} {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (program : Program) (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame) (type : Ty) (faults : FunctionCalls.FaultRep)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (mapping : LocationMap) (world : StoreTyping) (store : Store)
    (value : Value) (finalStore : Store) : Prop :=
  ResultFor (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
    context environment before items mapping world store value finalStore


theorem binder_context_eq {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binder : TypedBinder} (first : BinderExtends owner context binder left)
    (second : BinderExtends owner context binder right) : left = right := by
  cases first; cases second; rfl

variable {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {program : Program} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {solved : List SolvedRequirement} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {registry : SourceCoreRawMetadata.Registry} {type : Ty} {faults : FunctionCalls.FaultRep}
  {continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}

theorem ResultFor.prepend {validity : SourceSemantics.Context → Prop} {context middleContext : SourceSemantics.Context}
    {environment nextEnvironment : Dynamic.Environment} {before middle : Dynamic.Heap}
    {item : ForItemForm} {items : List ForItemForm}
    {mapping nextMap : LocationMap} {world nextWorld : StoreTyping} {store middleStore finalStore : Store}
    {contextLocation : Location} {native : NativeFrame} {value : Value}
    (head : Dynamic.ForItemExecutes program context evidence source environment before item middleContext nextEnvironment middle)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (preservation : AdministrativePreserved mapping store nextMap middleStore)
    (metadata : Dynamic.HeapMetadataExtend before middle)
    (tail : ResultFor validity (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      middleContext nextEnvironment middle items nextMap nextWorld middleStore value finalStore) :
    ResultFor validity (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before (item :: items) mapping world store value finalStore := by
  cases tail with
  | continues tail trace lastMaps lastWorlds lastFrame lastMetadata remaining =>
    exact .continues tail (.cons head trace) (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata) remaining
  | fault trace same matched heaps lastMaps lastWorlds lastFrame lastMetadata =>
    exact .fault (.tail head trace) same matched heaps (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata)


theorem Result.prepend {context middleContext : SourceSemantics.Context}
    {environment nextEnvironment : Dynamic.Environment} {before middle : Dynamic.Heap}
    {item : ForItemForm} {items : List ForItemForm}
    {mapping nextMap : LocationMap} {world nextWorld : StoreTyping} {store middleStore finalStore : Store}
    {contextLocation : Location} {native : NativeFrame} {value : Value}
    (head : Dynamic.ForItemExecutes program context evidence source environment before item middleContext nextEnvironment middle)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (preservation : AdministrativePreserved mapping store nextMap middleStore)
    (metadata : Dynamic.HeapMetadataExtend before middle)
    (tail : Result (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      middleContext nextEnvironment middle items nextMap nextWorld middleStore value finalStore) :
    Result (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before (item :: items) mapping world store value finalStore := by
  exact ResultFor.prepend head maps worlds preservation metadata tail


end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderStructuralElimination
/-! Structural eliminators use the existing static recursors. Assignment and
unary payloads describe the actual selected head. The motive depends only on
the header indices; semantic branches are supplied once by each consumer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader.Structural
open Core Frontend SourceInference
open TypedLexicalWhile (absentRequest initializedRequest sequence)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {type : Ty}
  {continuation : SourceSemantics.Context → Scope → Expr → Prop}

abbrev AssignmentPayload (values : ValuesContext) (source : TypedSource)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (definitions : DataEnvironment) :=
  ∀ {context scope assignment operator rhs},
    GenericAssignmentStatements.Head values source context (certificates context) scope
      administrative definitions assignment operator rhs → Prop

abbrev UnaryPayload := ∀ {context scope assignment}, CompatibleBitNotStatements.Head context scope assignment → Prop

structure BranchAlgebra
    (AP : AssignmentPayload values source certificates administrative definitions) (UP : UnaryPayload)
    (M : SourceSemantics.Context → Scope → List ForItemForm → Expr → Prop) : Prop where
  nil : ∀ {context scope code}, continuation context scope code → M context scope [] code
  uninitialized : ∀ {context nextContext scope binder rest body payload},
    binder.scheme.quantified = [] → BinderExtends source.owner context binder nextContext →
    source.inputs.any (fun input => decide (input.id = binder.id)) = false →
    values.checked.catalog.project binder.scheme.body = .ok payload →
    ∀ (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload)),
    annotation.original = allocation.expression → M nextContext ((binder.id, payload) :: scope) rest body →
    M context scope (.letDecl binder none :: rest) (.letE annotation.expression body)
  initialized : ∀ {context nextContext scope binder initializer initializerNode lowered body rest},
    binder.scheme.quantified = [] → BinderExtends source.owner context binder nextContext →
    source.inputs.any (fun input => decide (input.id = binder.id)) = false →
    source.lookupExpression? initializer = some initializerNode → initializerNode.type = binder.scheme.body →
    certificates context scope initializer lowered →
    ∀ (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type)),
    annotation.original = allocation.expression → M nextContext ((binder.id, lowered.type) :: scope) rest body →
    M context scope (.letDecl binder (some initializer) :: rest) (sequence type lowered.expression annotation.expression body)
  discard : ∀ {context scope expression expressionNode rest lowered body},
    source.lookupExpression? expression = some expressionNode → certificates context scope expression lowered →
    M context scope rest body →
    M context scope (.expression expression :: rest) (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  assign : ∀ {context scope assignment operator rhs rest body}
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs),
    AP head → M context scope rest body →
    M context scope (.assignValue assignment operator rhs :: rest) (head.emit body (LocalLoop.controlType type))
  bitNot : ∀ {context scope assignment rest body} (head : CompatibleBitNotStatements.Head context scope assignment),
    UP head → M context scope rest body →
    M context scope (.assignBitNot assignment :: rest) (head.emit body (LocalLoop.controlType type))

def Eliminates (AP : AssignmentPayload values source certificates administrative definitions) (UP : UnaryPayload)
    (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ M : SourceSemantics.Context → Scope → List ForItemForm → Expr → Prop,
    BranchAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (type := type) (continuation := continuation) AP UP M →
    M context scope items code

/-- Legacy payloads retain their exact original diagnostic receipts. -/
theorem of_reachable_errors {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context scope items code}
    {tree : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation context scope items code}
    (errors : Tree.ReachableErrors registry faults tree) :
    Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (type := type) (continuation := continuation)
      (values := values) (source := source) (certificates := certificates)
      (definitions := definitions) (administrative := administrative)
      (fun head => head.ReachableErrors registry faults) (fun head => head.Errors faults) context scope items code := by
  intro M algebra
  refine Tree.ErrorsFor.rec
    (motive := fun {context scope items code} _ _ => M context scope items code)
    ?_ ?_ ?_ ?_ ?_ ?_ errors
  · intro context scope code next
    exact algebra.nil next
  · intro context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining remainingErrors ih
    exact algebra.uninitialized mono extended ordinary projected allocation annotation same ih
  · intro context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same remaining remainingErrors ih
    exact algebra.initialized mono extended ordinary found sourceType initial allocation annotation same ih
  · intro context scope expression expressionNode rest lowered body found value remaining remainingErrors ih
    exact algebra.discard found value ih
  · intro context scope assignment operator rhs rest body head remaining remainingErrors receipt ih
    exact algebra.assign head receipt ih
  · intro context scope assignment rest body head remaining remainingErrors receipt ih
    exact algebra.bitNot head receipt ih

variable {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

inductive PreparedAssignment
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    {context scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs) : Prop where
  | intro (site : SourceCoreElaboration.ErrorSite)
      (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs)
      (same : head.invalid = invalidOperand site assignment.target.root operator)
      (sourceTyped : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
      (rightTyped : ExpressionHasType source context rhs assignment.target.type)
      (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
      (fuel : Nat)
      (prepared : head.PreparedAt site fuel (invalidProjection site assignment.target.root) (missingDefault site assignment.target.root)) :
      PreparedAssignment factory invalidProjection missingDefault head

inductive PreparedUnary (tracked : Bool) (source : TypedSource)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    {context scope assignment} (head : CompatibleBitNotStatements.Head context scope assignment) : Prop where
  | intro
      (writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
        WritableLocal context assignment.target.root binder.scheme.body)
      (bare : assignment.target.projections = [])
      (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
        SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
      (site : SourceCoreElaboration.ErrorSite)
      (origin : EmittedDiagnosticTokenPlan.UnaryOccursFor tracked source site assignment)
      (same : head.invalid = invalidUnary site assignment.target.root) : PreparedUnary tracked source invalidUnary head

/-- The joint recursor obtains tokens only from the same retained Plan. -/
theorem of_coupled {context scope items code}
    {tree : Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation context scope items code}
    {plan : EmittedDiagnosticPlan.Plan factory}
    (coupled : Coupled factory invalidProjection missingDefault tree plan)
    (tokens : EmittedDiagnosticTokenPlan.TokensFor factory invalidUnary plan) :
    Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (type := type) (continuation := continuation)
      (values := values) (source := source) (certificates := certificates)
      (definitions := definitions) (administrative := administrative)
      (fun head => PreparedAssignment factory invalidProjection missingDefault head)
      (fun head => PreparedUnary tracked source invalidUnary head) context scope items code := by
  intro M algebra
  have result : EmittedDiagnosticTokenPlan.TokensFor factory invalidUnary plan → M context scope items code := by
    refine Coupled.rec (motive := fun {context scope items code} _ plan _ =>
      EmittedDiagnosticTokenPlan.TokensFor factory invalidUnary plan → M context scope items code)
      ?_ ?_ ?_ ?_ ?_ ?_ coupled
    · intro context scope code next tokens
      exact algebra.nil next
    · intro context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining remainingPlan remainingCoupled ih tokens
      exact algebra.uninitialized mono extended ordinary projected allocation annotation same (ih tokens)
    · intro context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same remaining remainingPlan remainingCoupled ih tokens
      exact algebra.initialized mono extended ordinary found sourceType initial allocation annotation same (ih tokens)
    · intro context scope expression expressionNode rest lowered body found value remaining remainingPlan remainingCoupled ih tokens
      exact algebra.discard found value (ih tokens)
    · intro context scope assignment operator rhs rest body head remaining remainingPlan remainingCoupled site origin same sourceTyped rightTyped profile fuel prepared ih tokens
      cases tokens with
      | pair child _ =>
        exact algebra.assign head (.intro site origin same sourceTyped rightTyped profile fuel prepared) (ih child)
    · intro context scope assignment rest body head remaining remainingPlan remainingCoupled writable bare profile ih tokens
      cases tokens with
      | pair child unary => cases unary with
        | unary _ _ _ _ site origin same =>
          exact algebra.bitNot head (.intro writable bare profile site origin same) (ih child)
  exact result tokens

/-- This interpretation consumes the genuine unary row of an actual table. -/
theorem PreparedUnary.errors {context scope assignment} {head : CompatibleBitNotStatements.Head context scope assignment}
    {first : Nat} {table : SourceCoreAssignmentFaultSites.Table} {faults : FunctionCalls.FaultRep}
    (receipt : PreparedUnary true source (fun site root => table.reasonAt site root .bitNot) head)
    (typed : EmittedDiagnosticTokenPlan.UnaryTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (included : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep table reason token → faults reason token) : head.Errors faults := by
  cases receipt with
  | intro _ _ _ site origin same =>
    change faults (.invalidUnaryOperand .bitNot) head.invalid
    exact same.symm ▸ included _ _ (origin.prepared typed issued)
end Solcore.SourceSemantics.CoreLowering.GenericForHeader.Structural
end
