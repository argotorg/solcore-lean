import Solcore.SourceSemantics.CoreLowering.ProtectedStateFor
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForContracts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedForContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateWhileReady

/-! Measured post-header edges consume the actual body state. Their real
six-slot native prefix, source trace, and independent native grade remain the
existing for contract. Successful and fault edges return the actual state at
the fixed loop scope after removing any post-header binders. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Progress postValues)
open ProtectedStateTransition
universe u v
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable {Records : Type v}

/-- Readiness of the actual retained self-cell activation follows only its
real installed store/world and original administrative receipts. -/
structure ActivationTransfers (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol) where
  ready : ∀ {context : SourceSemantics.Context} {scope : Scope} {mapping : LocationMap}
    {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {type : Ty} {condition body post : Expr} {reason : Word},
    ∀ (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
      (reached : protocol.State ⟨scope, mapping, TypedLexicalWhile.installedWorld world type, heap,
        TypedLexicalWhile.installedStore store type condition body post reason actual, canonical⟩),
      AdministrativePreserved mapping store mapping
        (TypedLexicalWhile.installedStore store type condition body post reason actual) →
      protocol.Relates initial reached → protocol.records reached = protocol.records initial →
      readiness.Ready context initial → readiness.Ready context reached

theorem ActivationTransfers.trivial (protocol : Protocol.{u, v} Records) :
    ActivationTransfers protocol (Readiness.trivial protocol) where
  ready := fun _ _ _ _ _ _ => True.intro

def PostPreservesAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
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
    readiness.Ready context state.retained →
    ∀ continued : Bool,
    SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after →
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.Ready context reached.retained

def PostFaultsAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
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
    readiness.Ready context state.retained →
    ∀ continued : Bool,
    SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after →
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.FaultReady reached.retained

def PostReflectsAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
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
    readiness.Ready context state.retained →
    ∀ continued : Bool,
    EvaluationSize size (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ)) value finalStore →
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.Ready context reached.retained) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.FaultReady reached.retained)


theorem post_preserves_trivial (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr)
    (meaning : ProtectedFor.Body.Stateful.PostPreservesAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) items code) :
    PostPreservesAt protocol (Readiness.trivial protocol) guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) items code := by
  intro mapping world before after store finalContext finalEnvironment state native read guarded _ready continued trace
  obtain ⟨finalStore, finalMap, finalWorld, evaluated, progress, reached, related⟩ := meaning state read guarded continued trace
  exact ⟨finalStore, finalMap, finalWorld, evaluated, progress, reached, related, True.intro⟩

theorem post_faults_trivial (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr)
    (meaning : ProtectedFor.Body.Stateful.PostFaultsAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) (faults := faults) items code) :
    PostFaultsAt protocol (Readiness.trivial protocol) guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) (faults := faults) items code := by
  intro mapping world before after store finalContext reason state native read guarded _ready continued trace
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, progress, reached, related⟩ := meaning state read guarded continued trace
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, progress, reached, related, True.intro⟩

theorem post_reflects_trivial (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (faults : FunctionCalls.FaultRep) (items : List ForItemForm) (code : Expr)
    (meaning : ProtectedFor.Body.Stateful.PostReflectsAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) faults items code) :
    PostReflectsAt protocol (Readiness.trivial protocol) guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) faults items code := by
  intro mapping world before store finalStore value state native read guarded _ready continued completed
  rcases meaning state read guarded continued completed with good | bad
  · obtain ⟨sourceSize, finalContext, finalEnvironment, after, finalMap, finalWorld, trace, same, progress, reached, related⟩ := good
    exact Or.inl ⟨sourceSize, finalContext, finalEnvironment, after, finalMap, finalWorld, trace, same, progress, reached, related, True.intro⟩
  · obtain ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched, progress, reached, related⟩ := bad
    exact Or.inr ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched, progress, reached, related, True.intro⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful.WithReady
