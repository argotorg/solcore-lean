import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderPost
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForEdges
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderReady

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
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
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

include definitions registered observations producer acquire stateTransport stateBindings sites transfers solved in
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
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
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

include definitions registered observations producer acquire stateTransport stateBindings sites transfers in
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
      (program := program) (evidence := evidence) (observations := observations)
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

include definitions registered observations producer acquire stateTransport stateBindings sites transfers solved in
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
      (program := program) (evidence := evidence) (observations := observations)
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

include definitions registered observations producer acquire stateTransport stateBindings solved in
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
    (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence) (observations := observations)
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

include definitions registered observations producer acquire stateTransport stateBindings in
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
    (program := program) (evidence := evidence) (observations := observations)
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

include definitions registered observations producer acquire stateTransport stateBindings solved in
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
    (program := program) (evidence := evidence) (observations := observations)
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
