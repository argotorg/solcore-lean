import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLoopContracts
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForEndpoint
import Solcore.SourceSemantics.CoreLowering.ForHeaderNativeBounds

/-! Pointwise for contracts retain independent measured source loop/post
outcomes and original Core post/loop witnesses. A fixed outer budget selects
strictly smaller callbacks. The actual six post slots remain observed values;
no continuation agreement supplies a size or unrestricted body meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedForContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open TypedImperativeFor (LoopState Progress SourceLoop postValues)
abbrev Below := RecursiveNamedBoundedContracts.Below

inductive ForOutcome (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) :
    Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {outcome after} (trace : SourceExecutionSize.ForLoopExecutes program size context evidence source environment before condition post statements context outcome after) :
      ForOutcome program size context evidence source environment before condition post statements outcome after
  | fault {reason after} (trace : SourceExecutionSize.ForLoopFaults program size context evidence source environment before condition post statements reason after) :
      ForOutcome program size context evidence source environment before condition post statements (.fault reason) after

theorem ForOutcome.sound {program : Program} {size : Nat} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId}
    {outcome : Dynamic.ControlOutcome}
    (trace : ForOutcome program size context evidence source environment before condition post statements outcome after) :
    SourceLoop program context evidence source environment before condition post statements outcome after := by
  cases trace with
  | control trace => exact .control trace.sound
  | fault trace => exact .fault trace.sound

theorem ForOutcome.has_size {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId}
    {outcome : Dynamic.ControlOutcome}
    (trace : SourceLoop program context evidence source environment before condition post statements outcome after) :
    ∃ size, ForOutcome program size context evidence source environment before condition post statements outcome after := by
  cases trace with
  | control trace => obtain ⟨size, sized⟩ := SourceExecutionSize.ForLoopExecutes.has_size trace; exact ⟨size, .control sized⟩
  | fault trace => obtain ⟨size, sized⟩ := SourceExecutionSize.ForLoopFaults.has_size trace; exact ⟨size, .fault sized⟩

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

def PostPreservesAt (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
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
    SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after →
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore

def PostFaultsAt (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
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
    SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after →
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore

def PostReflectsAt (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
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
    EvaluationSize size (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ)) value finalStore →
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore)

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

def LoopPreservesAt (size : Nat) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
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
    (_trace : ForOutcome program size context evidence source environment before condition post statements outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical

def LoopReflectsAt (size : Nat) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
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
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      ForOutcome program sourceSize context evidence source environment before condition post statements outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical

theorem post_computation_size {size : Nat} {actual : Environment} {before bodyStore after : Store}
    {type : Ty} {location : Location} {body post : Expr} {reason : Word} {value : Value}
    (continued : Bool)
    (evaluation : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) before
      (LocalLoop.advance type (Core.LoopExecution.bodyCode body)
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).weakenAt 0)) value after)
    (bodyEval : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) before
      (Core.LoopExecution.bodyCode body) (if continued then LocalLoop.continuingValue type else LocalLoop.fallthroughValue type) bodyStore) :
    ∃ postSize postStore postValue, postSize < size ∧
      EvaluationSize postSize (postValues type location continued ++ actual) bodyStore (ForLoop.postCode post) postValue postStore :=
  ForHeaderNativeBounds.post_computation_sized continued evaluation bodyEval

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedForContracts
