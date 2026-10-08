import Solcore.SourceSemantics.CoreLowering.GenericForHeaderStructuralTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedForItemsAdmission
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderPost

/-! Authentic Source item typing and admission feed the existing header and
post producers at their exact reached states. The original Source and native
budgets remain independent; all binder restoration retains the real pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedForHeaderBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (postValues Progress)
open ProtectedForHeader (Tree)
open ProtectedStateTransition ProtectedForHeader.Stateful ProtectedForHeader.Stateful.WithReady
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport callerProtocol) (stateBindings : Bindings callerProtocol)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
  {control : ControlContext}
variable
  (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative ambient.definitions)
  (UP : GenericForHeader.Structural.UnaryPayload)
  (unary : ∀ {context scope assignment} (head : CompatibleBitNotStatements.Head context scope assignment),
    UP head → head.Errors faults)

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed in
theorem preserves_prefix_from_structural_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (receipt : GenericForHeader.Structural.Eliminates (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError) (type := type) (continuation := continuation)
      AP UP context scope items code)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType source control context items staticFinal)
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
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : (readiness bridge).Ready context state)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor callerProtocol condition validity registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      callerProtocol.Relates state tail.state ∧
      Nonempty (ReadyReturn callerProtocol (readiness bridge) context scope canonical finalContext tail.scope tail.canonical) ∧
      (readiness bridge).Ready finalContext tail.state ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) ∧
      finalContext = staticFinal ∧ Admission bridge context tail.state ∧
      Admission bridge staticFinal tail.state ∧ Dynamic.HeapTypesExtend before after ∧
      Dynamic.EnvironmentAgrees after staticFinal.locals finalEnvironment := by
  obtain ⟨tree⟩ := GenericForHeader.Structural.tree_of_eliminates receipt
  exact CallableIndexedOwnedAdmittedForHeaderBounds.preserves_prefix_bounded_for
    bridge functions definitions registered extension evidence faithful observations condition producer acquire
    stateTransport stateBindings unique wellFormed validity runtime covers extend budget boundedMeaning
    tree valid itemTyping environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed unary in
theorem preserves_fault_with_payload_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (receipt : GenericForHeader.Structural.Eliminates (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError) (type := type) (continuation := continuation)
      AP UP context scope items code)
    (assignmentFaults : ∀ context, validity context → AssignmentFaultPreservesWithPayloadAt callerProtocol
      (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget AP)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
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
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : (readiness bridge).Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition (readiness bridge) state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact ProtectedForHeader.Stateful.WithReady.Tree.preserves_fault_reachable_bounded_for_with_eliminator
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (protocol := callerProtocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness bridge) (facts := ProtectedStateForHeaderSourceSites.Facts source control)
      (itemFacts := ProtectedStateForHeaderSourceSites.ItemFacts source control)
      (exprFacts := ProtectedStateForHeaderSourceSites.ExpressionFacts source)
      (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
      (sites := ProtectedStateForHeaderSourceSites.sites program evidence source control unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge stateBindings source)
      AP UP unary validity
      (CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed validity runtime covers)
      extend budget
      (fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix bridge functions extension evidence
        stateTransport faithful observations unique wellFormed (runtime context valid) (covers context valid) budget (boundedMeaning context valid))
      assignmentFaults
      (fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (boundedMeaning context valid child within))
      receipt valid ⟨staticFinal, itemTyping⟩ environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered observations producer acquire stateTransport stateBindings unique wellFormed unary in
theorem reflects_with_payload_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size))    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (receipt : GenericForHeader.Structural.Eliminates (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError) (type := type) (continuation := continuation)
      AP UP context scope items code)
    (assignments : ∀ context, validity context → AssignmentReflectsWithPayloadAt callerProtocol
      (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget AP)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : (readiness bridge).Ready context state)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAtFor callerProtocol (readiness bridge) condition validity size registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment ⟨scope, mapping, world, before, store, canonical⟩ state items value finalStore := by
  exact ProtectedForHeader.Stateful.WithReady.Tree.reflects_reachable_bounded_for_with_eliminator
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (protocol := callerProtocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness bridge) (facts := ProtectedStateForHeaderSourceSites.Facts source control)
      (itemFacts := ProtectedStateForHeaderSourceSites.ItemFacts source control)
      (exprFacts := ProtectedStateForHeaderSourceSites.ExpressionFacts source)
      (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
      (sites := ProtectedStateForHeaderSourceSites.sites program evidence source control unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge stateBindings source)
      AP UP unary validity
      (CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed validity runtime covers)
      extend budget
      assignments
      (fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (boundedReflection context valid child within))
      receipt valid ⟨staticFinal, itemTyping⟩ environments heaps locals agrees actualTyped reference read unmapped state gate ready evaluated bounded

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedForHeaderBounds
