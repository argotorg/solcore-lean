import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForIterations
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation

/-!
# Protected contracts: for posts

`for` posts on the protected state, the older preservation form, and expression call heads.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderPost
/-! Actual post-header producers consume the body-produced loop state. The
live prefix's binder receipt restores its reached state while preserving its
new records; pure fallthrough code closes the same original header suffix. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Progress postValues postValues_typed postValues_agree post_rename)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (producer : OrdinaryAllocation.Producer protocol layouts frameLayout
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, guard location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport protocol) (stateBindings : Bindings protocol)
  {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {type : Ty} {conditionCode body postCode : Expr} {selfReason : Word}
  {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

namespace WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → List ForItemForm → Prop)
  (itemFacts : SourceSemantics.Context → ForItemForm → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts itemFacts exprFacts assignmentFacts snapshotFacts program evidence source)
  (transfers : AllocationTransfers protocol readiness stateBindings source)

theorem post_preserves_bounded_for_with_header_result
    (validity : SourceSemantics.Context → Prop)
    {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment} {native : CallableIndexedHistory.NativeFrame}
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (headerResult : ∃ tail : TailFor protocol guard validity registry functions source solved evidence administrative frameLayout globals
        contextLocation native (TypedForHeader.Fallthrough type) finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      protocol.Relates state.retained tail.state ∧
      Nonempty (ReadyReturn protocol readiness context scope canonical finalContext tail.scope tail.canonical) ∧
      readiness.Ready finalContext tail.state ∧
      ContinuationAgreement (postValues type location continued ++ actual) store (postCode.rename ((fun index => index + 6) ∘ ξ))
        tail.actual tail.store (tail.code.rename tail.embedding)) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.Ready context reached.retained := by
  obtain ⟨tail, maps, worlds, preservation, metadata, related, ⟨returnTo⟩, tailReady, agreement⟩ := headerResult
  have progress : Progress values registry functions before after mapping tail.mapping world tail.world store tail.store :=
    ⟨tail.heaps, maps, worlds, preservation, metadata⟩
  let reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason tail.mapping tail.world after tail.store :=
    ⟨state.live.progress progress, returnTo.restore tail.state⟩
  have retained : protocol.Relates state.retained reached.retained := protocol.trans related (returnTo.related tail.state)
  have reachedReady : readiness.Ready context reached.retained := returnTo.restore_ready tail.state tailReady
  exact ⟨tail.store, tail.mapping, tail.world,
    by simpa only [post_rename] using agreement.wrap tail.toTailFor.fallthrough_evaluates,
    progress, reached, retained, reachedReady⟩

include definitions registered producer acquire stateTransport stateBindings sites transfers solved extension faithful observations in
theorem post_preserves_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (valid : validity context) (itemsFacts : facts context items)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native) (ready : readiness.Ready context state.retained)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.Ready context reached.retained := by
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.live.selfTyped state.live.actualTyped
  obtain ⟨tail, maps, worlds, preservation, metadata, related, ⟨returnTo⟩, tailReady, agreement⟩ :=
    Tree.preserves_prefix_bounded_for_with_return (solved := solved)
      (extension := extension) (faithful := faithful) (observations := observations)
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := protocol) (condition := guard) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness) (facts := facts) (itemFacts := itemFacts) (exprFacts := exprFacts)
      (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts)
      (sites := sites) (transfers := transfers) (snapshots := snapshots)
      validity extend budget assignments boundedMeaning tree valid itemsFacts
      state.live.environments state.live.heaps state.live.locals (postValues_agree agrees type location continued)
      postTyped reference read state.live.contextUnmapped state.retained guarded ready trace bounded
  exact post_preserves_bounded_for_with_header_result protocol guard functions evidence readiness validity state continued
    ⟨tail, maps, worlds, preservation, metadata, related, ⟨returnTo⟩, tailReady, agreement⟩

theorem post_fault_reachable_bounded_for_with_header_result
    {reason : Dynamic.SemanticFault}
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (headerResult : ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (postCode.rename ((fun index => index + 6) ∘ ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition readiness state.retained ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.FaultReady reached.retained := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, preservation, metadata, transition⟩ := headerResult
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preservation, metadata⟩
  obtain ⟨finalState, retained, faultReady⟩ := transition
  let reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, finalState⟩
  exact ⟨token, finalStore, finalMap, finalWorld,
    by simpa only [post_rename] using evaluated,
    matched, progress, reached, retained, faultReady⟩

include definitions registered producer acquire stateTransport stateBindings sites transfers in
theorem post_fault_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (assignmentFaults : ∀ context, validity context → AssignmentFaultPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) (itemsFacts : facts context items)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native) (ready : readiness.Ready context state.retained)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.FaultReady reached.retained := by
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.live.selfTyped state.live.actualTyped
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, preservation, metadata, transition⟩ :=
    Tree.preserves_fault_reachable_bounded_for
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := protocol) (condition := guard) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness) (facts := facts) (itemFacts := itemFacts) (exprFacts := exprFacts)
      (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts)
      (sites := sites) (transfers := transfers) (snapshots := snapshots)
      validity extend budget assignments assignmentFaults boundedMeaning tree errors valid itemsFacts
      state.live.environments state.live.heaps state.live.locals (postValues_agree agrees type location continued)
      postTyped reference read state.live.contextUnmapped state.retained guarded ready trace bounded
  exact post_fault_reachable_bounded_for_with_header_result protocol functions readiness state continued
    ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, preservation, metadata, transition⟩

theorem post_reflects_reachable_bounded_for_with_header_result
    (validity : SourceSemantics.Context → Prop)
    {items : List ForItemForm} {value : Value} {finalStore : Store} {native : CallableIndexedHistory.NativeFrame} {size : Nat}
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (headerResult : ResultAtFor protocol readiness guard validity size registry functions program source solved evidence administrative
      frameLayout globals contextLocation native type faults (TypedForHeader.Fallthrough type) context environment
      ⟨scope, mapping, world, before, store, canonical⟩ state.retained items value finalStore) :
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.Ready context reached.retained) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.FaultReady reached.retained) := by
  cases headerResult with
  | @continues sourceSize remainingSize finalContext finalEnvironment after tail trace maps worlds preservation metadata related returnReceipt tailReady remaining _ =>
    obtain ⟨returnTo⟩ := returnReceipt
    obtain ⟨same, storeEq⟩ := tail.toTailFor.fallthrough_reflects remaining.sound
    subst finalStore
    have progress : Progress values registry functions before after mapping tail.mapping world tail.world store tail.store :=
      ⟨tail.heaps, maps, worlds, preservation, metadata⟩
    let reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason tail.mapping tail.world after tail.store :=
      ⟨state.live.progress progress, returnTo.restore tail.state⟩
    have retained : protocol.Relates state.retained reached.retained := protocol.trans related (returnTo.related tail.state)
    have reachedReady : readiness.Ready context reached.retained := returnTo.restore_ready tail.state tailReady
    exact .inl ⟨sourceSize, finalContext, finalEnvironment, after, tail.mapping, tail.world, trace, same,
      progress, reached, retained, reachedReady⟩
  | @fault sourceSize finalContext reason token after finalMap finalWorld trace same matched heaps maps worlds preservation metadata transition =>
    have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
      ⟨heaps, maps, worlds, preservation, metadata⟩
    obtain ⟨finalState, retained, faultReady⟩ := transition
    let reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore :=
      ⟨state.live.progress progress, finalState⟩
    exact .inr ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched,
      progress, reached, retained, faultReady⟩

include definitions registered producer acquire stateTransport stateBindings sites transfers solved in
theorem post_reflects_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentReflectsAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionReflectsAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size))
    {items : List ForItemForm} {value : Value} {finalStore : Store}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) (itemsFacts : facts context items)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native) (ready : readiness.Ready context state.retained)
    (continued : Bool)
    {size : Nat} (evaluated : EvaluationSize size (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ)) value finalStore) (bounded : size ≤ budget) :
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.Ready context reached.retained) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.FaultReady reached.retained) := by
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.live.selfTyped state.live.actualTyped
  have result := Tree.reflects_reachable_bounded_for (solved := solved)
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := protocol) (condition := guard) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness) (facts := facts) (itemFacts := itemFacts) (exprFacts := exprFacts)
      (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts)
      (sites := sites) (transfers := transfers) (snapshots := snapshots)
      validity extend budget assignments boundedReflection tree errors valid itemsFacts
      state.live.environments state.live.heaps state.live.locals (postValues_agree agrees type location continued)
      postTyped reference read state.live.contextUnmapped state.retained guarded ready
      (by simpa only [post_rename] using evaluated) bounded
  exact post_reflects_reachable_bounded_for_with_header_result protocol guard functions program evidence readiness validity state result


end WithReady

include definitions registered producer acquire stateTransport stateBindings solved extension faithful observations in
theorem post_preserves_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  have result := WithReady.post_preserves_bounded_for
    (extension := extension) (faithful := faithful) (observations := observations)
    (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence)
    (protocol := protocol) (guard := guard) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ => True) (itemFacts := fun _ _ => True) (exprFacts := fun _ _ _ => True)
    (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
    (sites := WithReady.StaticSites.trivial program evidence source)
    (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings source)
    (snapshots := WithReady.SnapshotTransfers.trivial protocol validity program evidence source)
    validity extend budget
    (fun context valid => WithReady.assignment_prefix_trivial protocol functions program evidence source
      (certificates context) context administrative budget (assignments context valid))
    (fun context valid size smaller => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt.of_true
      protocol program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (certificates context) (boundedMeaning context valid size smaller))
    tree valid True.intro agrees reference state read guarded True.intro continued trace bounded
  obtain ⟨finalStore, finalMap, finalWorld, evaluated, progress, reached, related, _ready⟩ := result
  exact ⟨finalStore, finalMap, finalWorld, evaluated, progress, reached, related⟩

include definitions registered producer acquire stateTransport stateBindings in
theorem post_fault_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (assignmentFaults : ∀ context, validity context → AssignmentFaultPreservesAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  have result := WithReady.post_fault_reachable_bounded_for
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence)
    (protocol := protocol) (guard := guard) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ => True) (itemFacts := fun _ _ => True) (exprFacts := fun _ _ _ => True)
    (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
    (sites := WithReady.StaticSites.trivial program evidence source)
    (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings source)
    (snapshots := WithReady.SnapshotTransfers.trivial protocol validity program evidence source)
    validity extend budget
    (fun context valid => WithReady.assignment_prefix_trivial protocol functions program evidence source
      (certificates context) context administrative budget (assignments context valid))
    (fun context valid => WithReady.assignment_fault_trivial protocol functions program evidence source
      (certificates context) context administrative faults budget (assignmentFaults context valid))
    (fun context valid size smaller => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt.of_true
      protocol program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (certificates context) (boundedMeaning context valid size smaller))
    tree errors valid True.intro agrees reference state read guarded True.intro continued trace bounded
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, progress, reached, related, _ready⟩ := result
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, progress, reached, related⟩

include definitions registered producer acquire stateTransport stateBindings solved in
theorem post_reflects_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentReflectsAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size))
    {items : List ForItemForm} {value : Value} {finalStore : Store}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    (continued : Bool)
    {size : Nat} (evaluated : EvaluationSize size (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ)) value finalStore) (bounded : size ≤ budget) :
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained) := by
  have result := WithReady.post_reflects_reachable_bounded_for
    (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence)
    (protocol := protocol) (guard := guard) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ => True) (itemFacts := fun _ _ => True) (exprFacts := fun _ _ _ => True)
    (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
    (sites := WithReady.StaticSites.trivial program evidence source)
    (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings source)
    (snapshots := WithReady.SnapshotTransfers.trivial protocol validity program evidence source)
    validity extend budget
    (fun context valid => WithReady.assignment_reflection_trivial protocol functions program evidence source
      (certificates context) context administrative faults budget (assignments context valid))
    (fun context valid size smaller => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt.of_true
      protocol program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (certificates context) (boundedReflection context valid size smaller))
    tree errors valid True.intro agrees reference state read guarded True.intro continued evaluated bounded
  rcases result with ⟨sourceSize, finalContext, finalEnvironment, after, finalMap, finalWorld, trace, same, progress, reached, related, _ready⟩ |
    ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched, progress, reached, related, _ready⟩
  · exact .inl ⟨sourceSize, finalContext, finalEnvironment, after, finalMap, finalWorld, trace, same, progress, reached, related⟩
  · exact .inr ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched, progress, reached, related⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderLegacyPreservation
/-! Existing reachable diagnostic trees retain their original header prefix
contract. Their constructors cover allocations, expression discards, value
assignments and bare unary updates; no additional global model law is required. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalControl (allocate_absent allocate_initialized sequence_rename valid_extend)
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Fallthrough)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

namespace Stateful
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport protocol) (stateBindings : Bindings protocol)

namespace WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → List ForItemForm → Prop)
  (itemFacts : SourceSemantics.Context → ForItemForm → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts itemFacts exprFacts assignmentFacts snapshotFacts program evidence source)
  (transfers : AllocationTransfers protocol readiness stateBindings source)

include definitions registered producer acquire stateTransport stateBindings sites transfers in
theorem Tree.preserves_prefix_bounded_for_with_return_reachable
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry) program evidence
      source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor protocol condition validity registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      protocol.Relates state tail.state ∧
      Nonempty (ReadyReturn protocol readiness context scope canonical finalContext tail.scope tail.canonical) ∧
      readiness.Ready finalContext tail.state ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  induction errors generalizing mapping world actualContext environment canonical actual before store ξ contextLocation native finalContext finalEnvironment after size with
  | @nil context scope code next =>
    cases trace
    exact ⟨⟨⟨_, _, mapping, world, canonical, actual, actualContext, ξ, store, next, valid,
      environments, heaps, locals, agrees, actualTyped, reference, read, unmapped⟩, state, gate⟩,
      .refl _, .refl _, .refl _ _, .refl _, protocol.refl state, ⟨ReadyReturn.refl protocol readiness _ _ canonical⟩, ready, .refl _ _ _⟩
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining _remainingErrors ih =>
    cases trace with | cons first rest =>
      cases first with | letUninitialized _ other allocated =>
        cases binder_context_eq extended other
        obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationTransition⟩ :=
          TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer mono extended ordinary projected allocation annotation same
            environments heaps locals agrees actualTyped reference read allocated state ((acquire _ _ gate) state read)
        obtain ⟨nextState, allocationRelated⟩ := allocationTransition
        have nextReady := transfers.absent state nextState ready extended allocated preservation
        have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.letUninitialized mono extended allocated)
        obtain ⟨tail, maps, worlds, lastFrame, metadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
          ih (extend valid extended) nextFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            nextState gate nextReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        exact ⟨tail,
          (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
          (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
          preservation.trans lastFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata,
          protocol.trans allocationRelated tailRelated,
          ⟨ReadyReturn.then (ReadyReturn.binding stateBindings transfers extended scope canonical payload
            (.cellRef (OptionalCell.cellType payload) (store.length + 2))) tailReturn⟩, tailReady, (ContinuationAgreement.letE allocationEval).trans agreement⟩
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same remaining _remainingErrors ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with
      | letInitialized initialTrace _ other allocated =>
        cases binder_context_eq extended other
        obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
          boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact (.initialized mono) found)
            environments heaps locals agrees actualTyped state ready (.value initialTrace)
        cases represented with
        | value payload =>
          obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionTransition
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, allocationTransition⟩ :=
            TypedLexicalControl.Stateful.allocate_initialized functions definitions registered protocol producer mono extended ordinary allocation annotation same (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated middleState ((acquire _ _ gate) middleState frameRead)
          obtain ⟨nextState, allocationRelated⟩ := allocationTransition
          have nextReady := transfers.initialized middleState nextState middlePost.1 extended
            (sourceType ▸ middlePost.2) allocated allocationFrame
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.letInitialized initialTrace.sound mono extended allocated)
          obtain ⟨tail, finalMaps, finalWorlds, finalFrame, finalMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
            ih (extend valid extended) nextFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              nextState gate nextReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          refine ⟨tail,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata),
            protocol.trans expressionRelated (protocol.trans allocationRelated tailRelated),
            ⟨ReadyReturn.then (ReadyReturn.binding stateBindings transfers extended scope canonical lowered.type
              (.cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2))) tailReturn⟩, tailReady, ?_⟩
          rw [sequence_rename]
          exact (ContinuationAgreement.bind initialEval).trans ((ContinuationAgreement.letE allocationEval).trans agreement)
      | letInitializedGeneralized _ captures poly other allocated => exact False.elim (poly mono)
  | @discard context scope expression expressionNode rest lowered body found child remaining _remainingErrors ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with | expression childTrace =>
        obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
          boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact .discard found)
            environments heaps locals agrees actualTyped state ready (.value childTrace)
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionTransition
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.expression childTrace.sound)
          obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
            ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken worlds)) reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState gate middlePost.1 rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
            protocol.trans expressionRelated tailRelated, ⟨tailReturn⟩, tailReady, ?_⟩
          rw [LoopRenaming.discard]
          rw [GenericExpressionMeaning.rename_prefix] at agreement
          exact (ContinuationAgreement.bind first).trans agreement
  | @assign context scope assignment operator rhs rest body head remaining _remainingErrors _headErrors ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with | assignValue assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, assignmentTransition, prefixAgreement⟩ :=
          assignments _ valid head (sites.assignment itemFact)
            environments heaps locals agrees actualTyped state ready assigned (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        obtain ⟨middleState, assignmentRelated, middleReady⟩ := assignmentTransition
        have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignValue assigned.sound)
        obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
          ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 middleState gate middleReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
          protocol.trans assignmentRelated tailRelated, ⟨tailReturn⟩, tailReady, ?_⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).trans (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using agreement)

  | @bitNot context scope assignment rest body head remaining _remainingErrors _headErrors ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with | assignBitNot assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
          head.preserves_prefix functions program evidence
            environments heaps locals agrees actualTyped assigned.sound
        let middleState := stateTransport.extend state maps worlds preservation metadata
        have middleReady := snapshots.ready state middleState ready valid (sites.snapshot itemFact) assigned.sound locals preservation
        have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignBitNot assigned.sound)
        obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
          ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState gate middleReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
          protocol.trans (stateTransport.related state maps worlds preservation metadata) tailRelated, ⟨tailReturn⟩, tailReady, ?_⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).trans (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using agreement)

end WithReady

include definitions registered producer acquire stateTransport stateBindings in
theorem Tree.preserves_prefix_bounded_for_with_return_reachable
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol functions (registry := registry) program evidence
      source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor protocol condition validity registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      protocol.Relates state tail.state ∧
      Nonempty (ReturnTo protocol scope canonical tail.scope tail.canonical) ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  obtain ⟨tail, maps, worlds, frame, metadata, related, ⟨returnTo⟩, _ready, agreement⟩ :=
    WithReady.Tree.preserves_prefix_bounded_for_with_return_reachable (solved := solved)
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) (facts := fun _ _ => True) (itemFacts := fun _ _ => True)
      (exprFacts := fun _ _ _ => True) (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
      (sites := WithReady.StaticSites.trivial program evidence source)
      (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings source)
      (snapshots := WithReady.SnapshotTransfers.trivial protocol validity program evidence source)
      validity extend budget
      (fun context valid => WithReady.assignment_prefix_trivial protocol functions program evidence source
        (certificates context) context administrative budget (assignments context valid))
      (fun context valid size within => ProtectedWhile.Body.Stateful.WithReady.expression_preserves_trivial
        protocol (boundedMeaning context valid size within))
      tree errors valid True.intro environments heaps locals agrees actualTyped reference read unmapped state gate True.intro trace bounded
  exact ⟨tail, maps, worlds, frame, metadata, related, ⟨returnTo.toReturnTo⟩, agreement⟩

end Stateful
end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader

namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Progress postValues postValues_typed postValues_agree post_rename)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (producer : OrdinaryAllocation.Producer protocol layouts frameLayout
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, guard location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport protocol) (stateBindings : Bindings protocol)
  {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {type : Ty} {conditionCode body postCode : Expr} {selfReason : Word}
  {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

namespace WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → List ForItemForm → Prop)
  (itemFacts : SourceSemantics.Context → ForItemForm → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts itemFacts exprFacts assignmentFacts snapshotFacts program evidence source)
  (transfers : AllocationTransfers protocol readiness stateBindings source)

include definitions registered producer acquire stateTransport stateBindings sites transfers solved in
theorem post_preserves_bounded_for_reachable
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) (itemsFacts : facts context items)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native) (ready : readiness.Ready context state.retained)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.Ready context reached.retained := by
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.live.selfTyped state.live.actualTyped
  obtain ⟨tail, maps, worlds, preservation, metadata, related, ⟨returnTo⟩, tailReady, agreement⟩ :=
    Tree.preserves_prefix_bounded_for_with_return_reachable (solved := solved)
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := protocol) (condition := guard) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness) (facts := facts) (itemFacts := itemFacts) (exprFacts := exprFacts)
      (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts)
      (sites := sites) (transfers := transfers) (snapshots := snapshots)
      validity extend budget assignments boundedMeaning tree errors valid itemsFacts
      state.live.environments state.live.heaps state.live.locals (postValues_agree agrees type location continued)
      postTyped reference read state.live.contextUnmapped state.retained guarded ready trace bounded
  exact post_preserves_bounded_for_with_header_result protocol guard functions evidence readiness validity state continued
    ⟨tail, maps, worlds, preservation, metadata, related, ⟨returnTo⟩, tailReady, agreement⟩

end WithReady

include definitions registered producer acquire stateTransport stateBindings solved in
theorem post_preserves_bounded_for_reachable
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  have result := WithReady.post_preserves_bounded_for_reachable
    (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence)
    (protocol := protocol) (guard := guard) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ => True) (itemFacts := fun _ _ => True) (exprFacts := fun _ _ _ => True)
    (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
    (sites := WithReady.StaticSites.trivial program evidence source)
    (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings source)
    (snapshots := WithReady.SnapshotTransfers.trivial protocol validity program evidence source)
    validity extend budget
    (fun context valid => WithReady.assignment_prefix_trivial protocol functions program evidence source
      (certificates context) context administrative budget (assignments context valid))
    (fun context valid size smaller => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt.of_true
      protocol program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (certificates context) (boundedMeaning context valid size smaller))
    tree errors valid True.intro agrees reference state read guarded True.intro continued trace bounded
  obtain ⟨finalStore, finalMap, finalWorld, evaluated, progress, reached, related, _ready⟩ := result
  exact ⟨finalStore, finalMap, finalWorld, evaluated, progress, reached, related⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionCallsHeads
/-! The existing compositional call-head proofs consume one actual protocol
and its certified administrative transport. Every ordered child and call leaf
returns the actual post witness before the next consumer. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionCallsHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedBoundedContracts
universe u v
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {reasonAt : ExpressionId → Word}
  (unique : NodeOccurrencesUnique source)
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

namespace WithFacts
variable {Records : Type v} (stateProtocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (post : ExpressionNode → Dynamic.ExpressionOutcome → ∀ {index : ProtectedStateTransition.Index}, stateProtocol.State index → Prop)

/-- This result retains one actual input and one actual post. The post facet is
separate from the runtime relation and all original semantic/effect receipts. -/
def PreservesResult {initialIndex : ProtectedStateTransition.Index}
    (initial : stateProtocol.State initialIndex) (node : ExpressionNode)
    (lowered : SourceCoreBasic.LoweredExpr) (actual : Environment) (ξ : Renaming)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ value finalStore finalMap finalWorld,
    Evaluates actual initialIndex.store (lowered.expression.rename ξ) value finalStore ∧
    GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld node.type lowered.type faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends initialIndex.mapping finalMap ∧ WorldExtends initialIndex.world finalWorld ∧
    AdministrativePreserved initialIndex.mapping initialIndex.store finalMap finalStore ∧
    Dynamic.HeapMetadataExtend initialIndex.heap after ∧
    ∃ reached : stateProtocol.State ⟨initialIndex.scope, finalMap, finalWorld, after, finalStore, initialIndex.canonical⟩,
      stateProtocol.Relates initial reached ∧ post node outcome reached

def ReflectsResult {initialIndex : ProtectedStateTransition.Index}
    (initial : stateProtocol.State initialIndex) (node : ExpressionNode)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) (environment : Dynamic.Environment)
    (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize outcome after finalMap finalWorld,
    RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment initialIndex.heap id outcome after ∧
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld node.type lowered.type faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends initialIndex.mapping finalMap ∧ WorldExtends initialIndex.world finalWorld ∧
    AdministrativePreserved initialIndex.mapping initialIndex.store finalMap finalStore ∧
    Dynamic.HeapMetadataExtend initialIndex.heap after ∧
    ∃ reached : stateProtocol.State ⟨initialIndex.scope, finalMap, finalWorld, after, finalStore, initialIndex.canonical⟩,
      stateProtocol.Relates initial reached ∧ post node outcome reached

variable
  (facts : SourceCoreLocalCell.Scope → ExpressionId → SourceCoreBasic.LoweredExpr → ExpressionNode → Prop)
  (ready : ∀ {index : ProtectedStateTransition.Index}, stateProtocol.State index → Prop)

/-- Only the actual branch certificate is requested. Providers are fixed at
this parent, input and trace, including its authentic static and ready facets. -/
theorem head_preserves_at_with_providers
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {environment : Dynamic.Environment} {ξ : Renaming} {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (initial : stateProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (primitive : CompatibleExpressionTypedCompositions.Head compiled.compatible.checked source certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial →
      RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
      PreservesResult (registry := registry) (faults := faults) functions stateProtocol post initial node lowered actual ξ outcome after)
    (data : RecursiveNamedDataExpressionHeadBounds.Certificate calls (.initial compiled.compatible.checked)
      source context reasonAt certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial →
      RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
      PreservesResult (registry := registry) (faults := faults) functions stateProtocol post initial node lowered actual ξ outcome after)
    (builtin : BuiltinCalls.Typed.Head (.initial compiled.compatible.checked) source certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial →
      RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
      PreservesResult (registry := registry) (faults := faults) functions stateProtocol post initial node lowered actual ξ outcome after)
    (tuple : CompatibleExpressionTuples.Certificate (.initial compiled.compatible.checked) source certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial →
      RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
      PreservesResult (registry := registry) (faults := faults) functions stateProtocol post initial node lowered actual ξ outcome after)
    (call : calls certificate scope id lowered → source.lookupExpression? id = some node → facts scope id lowered node → ready initial →
      RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
      PreservesResult (registry := registry) (faults := faults) functions stateProtocol post initial node lowered actual ξ outcome after)
    (head : CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate scope id lowered)
    (parentFacts : facts scope id lowered node) (initialReady : ready initial)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    PreservesResult (registry := registry) (faults := faults) functions stateProtocol post initial node lowered actual ξ outcome after := by
  cases head with
  | primitive head => exact primitive head found parentFacts initialReady trace
  | constructor receipt form accepted sequence =>
    exact data ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩ found parentFacts initialReady trace
  | member metadata baseMetadata form layout certified =>
    exact data ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩ found parentFacts initialReady trace
  | index header keyFound form sourceType first second =>
    exact data ⟨.index header keyFound form sourceType first second, .index header keyFound form sourceType first second⟩ found parentFacts initialReady trace
  | builtin head => exact builtin head found parentFacts initialReady trace
  | tuple receipt sequence => exact tuple ⟨_, _, _, _, rfl, receipt, sequence⟩ found parentFacts initialReady trace
  | call head => exact call head found parentFacts initialReady trace

/-- The original native parent keeps its exact input and final store. Each
provider returns its independent Source grade at that same actual post. -/
theorem head_reflects_at_with_providers
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {canonical actual : Environment}
    {environment : Dynamic.Environment} {ξ : Renaming} {size : Nat} {value : Value}
    (initial : stateProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (primitive : CompatibleExpressionTypedCompositions.Head compiled.compatible.checked source certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial → EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
      ReflectsResult (program := program) (registry := registry) (faults := faults) (source := source) (context := context) functions evidence stateProtocol post initial node id lowered environment value finalStore)
    (data : RecursiveNamedDataExpressionHeadBounds.Certificate calls (.initial compiled.compatible.checked)
      source context reasonAt certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial → EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
      ReflectsResult (program := program) (registry := registry) (faults := faults) (source := source) (context := context) functions evidence stateProtocol post initial node id lowered environment value finalStore)
    (builtin : BuiltinCalls.Typed.Head (.initial compiled.compatible.checked) source certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial → EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
      ReflectsResult (program := program) (registry := registry) (faults := faults) (source := source) (context := context) functions evidence stateProtocol post initial node id lowered environment value finalStore)
    (tuple : CompatibleExpressionTuples.Certificate (.initial compiled.compatible.checked) source certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial → EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
      ReflectsResult (program := program) (registry := registry) (faults := faults) (source := source) (context := context) functions evidence stateProtocol post initial node id lowered environment value finalStore)
    (call : calls certificate scope id lowered → source.lookupExpression? id = some node → facts scope id lowered node → ready initial →
      EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
      ReflectsResult (program := program) (registry := registry) (faults := faults) (source := source) (context := context) functions evidence stateProtocol post initial node id lowered environment value finalStore)
    (head : CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate scope id lowered)
    (parentFacts : facts scope id lowered node) (initialReady : ready initial)
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ReflectsResult (program := program) (registry := registry) (faults := faults) (source := source) (context := context) functions evidence stateProtocol post initial node id lowered environment value finalStore := by
  cases head with
  | primitive head => exact primitive head found parentFacts initialReady completed
  | constructor receipt form accepted sequence =>
    exact data ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩ found parentFacts initialReady completed
  | member metadata baseMetadata form layout certified =>
    exact data ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩ found parentFacts initialReady completed
  | index header keyFound form sourceType first second =>
    exact data ⟨.index header keyFound form sourceType first second, .index header keyFound form sourceType first second⟩ found parentFacts initialReady completed
  | builtin head => exact builtin head found parentFacts initialReady completed
  | tuple receipt sequence => exact tuple ⟨_, _, _, _, rfl, receipt, sequence⟩ found parentFacts initialReady completed
  | call head => exact call head found parentFacts initialReady completed
end WithFacts

include extension faithful functionLeaves functionTypes unique missing in
/-- Compositional heads consume the actual ordered child states. -/
theorem head_preserves_at_with_calls [FunctionCalls.FaultTokens faults]
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    {Records : Type v} (stateProtocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport stateProtocol)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → ProtectedStateTransition.PreservesAt
      stateProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults child)
    (callMeaning : ProtectedStateTransition.PreservesAt
      stateProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source (calls certificate) faults size) :
    ProtectedStateTransition.PreservesAt stateProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate) faults size := by
  intro scope id lowered head node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial trace
  suffices resolved : WithFacts.PreservesResult  (registry := registry) (faults := faults)
      functions stateProtocol (fun _ _ {_} _ => True) initial node lowered actual ξ outcome after by
    simpa only [WithFacts.PreservesResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using resolved
  refine WithFacts.head_preserves_at_with_providers (functions := functions) (evidence := evidence)
    (stateProtocol := stateProtocol) (post := fun _ _ {_} _ => True)
    (facts := fun _ _ _ _ => True) (ready := fun {_} _ => True)
    (calls := calls) found initial ?_ ?_ ?_ ?_ ?_ head trivial trivial trace
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.PreservesResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedExpressionCompositionsBounds.Stateful.Head.preserves_at functions program evidence
      stateProtocol budget size within unique children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.PreservesResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedDataExpressionHeadBounds.Stateful.preserves_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence unique missing stateProtocol transport budget size within children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.PreservesResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedBuiltinHeadBounds.Stateful.Head.preserves_at (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (registry := registry) (faults := faults) functions functionLeaves program evidence unique
      stateProtocol budget size within children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.PreservesResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedTupleHeadBounds.Stateful.preserves_at (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (registry := registry) (faults := faults) functions program evidence
      stateProtocol budget size within unique children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.PreservesResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (callMeaning branch parentFound environments heaps locals agrees typed initial childTrace)

include extension faithful functionLeaves functionTypes missing in
/-- Reflection uses the same actual child posts at their native grades. -/
theorem head_reflects_at_with_calls [FunctionCalls.FaultTokens faults]
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    {Records : Type v} (stateProtocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport stateProtocol)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → ProtectedStateTransition.ReflectsAt
      stateProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults child)
    (callMeaning : ProtectedStateTransition.ReflectsAt
      stateProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source (calls certificate) faults size) :
    ProtectedStateTransition.ReflectsAt stateProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate) faults size := by
  intro scope id lowered head node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial trace
  suffices resolved : WithFacts.ReflectsResult (program := program) (source := source) (context := context) (registry := registry) (faults := faults)
      functions evidence stateProtocol (fun _ _ {_} _ => True) initial node id lowered environment value finalStore by
    simpa only [WithFacts.ReflectsResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using resolved
  refine WithFacts.head_reflects_at_with_providers (functions := functions) (evidence := evidence)
    (stateProtocol := stateProtocol) (post := fun _ _ {_} _ => True)
    (facts := fun _ _ _ _ => True) (ready := fun {_} _ => True)
    (calls := calls) found initial ?_ ?_ ?_ ?_ ?_ head trivial trivial trace
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.ReflectsResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedExpressionCompositionsBounds.Stateful.Head.reflects_at functions program evidence
      stateProtocol budget size within children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.ReflectsResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedDataExpressionHeadBounds.Stateful.reflects_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence missing stateProtocol transport budget size within children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.ReflectsResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedBuiltinHeadBounds.Stateful.Head.reflects_at (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (registry := registry) (faults := faults) functions functionLeaves program evidence
      stateProtocol budget size within children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.ReflectsResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedTupleHeadBounds.Stateful.reflects_at (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (registry := registry) (faults := faults) functions program evidence
      stateProtocol budget size within children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.ReflectsResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (callMeaning branch parentFound environments heaps locals agrees typed initial childTrace)

end Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionCallsHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
/-! The accepted Source head fixes the exact lexical context of its suffix.
These inversions require no execution trace or separate body typing premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
open Frontend SourceInference
open ProtectedStateImperativeTypedSourceSites (Statements)

private theorem suffix_of_form
    {source : TypedSource} {context next : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (contextAt : ∀ control final,
      Dynamic.StatementHasType.FormTyping source control context node.form final → final = next) :
    Statements source next rest := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton _ => exact ⟨control, next, _, .nil _ _⟩
  | cons head tail =>
    obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    have same : actual = node := Option.some.inj
      ((lookupStatement?_complete unique contains).symm.trans found)
    subst actual
    exact contextAt _ _ formTyped ▸ ⟨control, final, _, tail⟩

/-- Initialized and uninitialized lets use the actual retained binder
extension, including when Source typing admits a generalized initializer. -/
theorem let_decl
    {source : TypedSource} {context next : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : Option ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder initializer)
    (extended : BinderExtends source.owner context binder next) :
    Statements source next rest := by
  apply suffix_of_form unique typed found
  intro control final original
  rw [form] at original
  cases original with
  | letUninitialized _ actual | letInitialized _ _ actual
  | letInitializedGeneralized _ _ _ _ actual =>
    exact Dynamic.BinderExtends.functional actual extended

/-- An expression statement leaves the suffix's lexical context unchanged. -/
theorem discard
    {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {expression : ExpressionId} {semicolon : Bool}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon) :
    Statements source context rest := by
  apply suffix_of_form unique typed found
  intro control final original
  rw [form] at original
  cases original <;> rfl

/-- Plain and compound assignments share their Source context with the
remaining statements; the executable profile chooses its own supported form. -/
theorem assignment
    {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {resolution : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue resolution operator rhs) :
    Statements source context rest := by
  apply suffix_of_form unique typed found
  intro control final original
  rw [form] at original
  cases original <;> rfl

/-- A unary assignment keeps the original suffix context. -/
theorem bitNot
    {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {resolution : AssignmentResolution}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot resolution) :
    Statements source context rest := by
  apply suffix_of_form unique typed found
  intro control final original
  rw [form] at original
  cases original <;> rfl

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
end
