import Solcore.SourceSemantics.CoreLowering.ProtectedStateFor
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedForContracts

/-! Measured post-header edges consume the actual body state. Their real
six-slot native prefix, source trace, and independent native grade remain the
existing for contract. Successful and fault edges return the actual state at
the fixed loop scope after removing any post-header binders. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Progress postValues)
open ProtectedStateTransition
universe u v
variable {Records : Type v}

def PostPreservesAt (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment},
    ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
    guard contextLocation native →
    ∀ continued : Bool,
    SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after →
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained

def PostFaultsAt (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault},
    ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
    guard contextLocation native →
    ∀ continued : Bool,
    SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after →
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained

def PostReflectsAt (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (faults : FunctionCalls.FaultRep) (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
    ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
    guard contextLocation native →
    ∀ continued : Bool,
    EvaluationSize size (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ)) value finalStore →
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained)

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful
