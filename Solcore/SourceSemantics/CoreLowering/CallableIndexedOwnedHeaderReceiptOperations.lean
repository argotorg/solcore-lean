import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedForHeaderBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedImperativeCatalogPayloadContracts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedForItemsAdmission
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderPost

/-! Authentic Source item typing and admission feed the existing header and
post producers at their exact reached states. The original Source and native
budgets remain independent; all binder restoration retains the real pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedHeaderReceiptOperations
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
variable (validity : SourceSemantics.Context → Prop)
  (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
  (covers : ∀ context, validity context → evidence.Covers context)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (budget : Nat)
open ProtectedStateImperativeCatalogPayload (HeaderReceiptFamily)

abbrev PrefixAt (R : HeaderReceiptFamily) : Prop :=
  ∀ {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop} {control : ControlContext}
    {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (_receipt : R type continuation context scope items code)
    (_valid : validity context) {staticFinal : SourceSemantics.Context}
    (_itemTyping : ForItemsHaveType source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_gate : condition contextLocation native) (_ready : (readiness bridge).Ready context state)
    {size : Nat} (_trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (_bounded : size ≤ budget),
    ∃ tail : TailFor callerProtocol condition validity registry functions source [] evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      callerProtocol.Relates state tail.state ∧
      Nonempty (ReadyReturn callerProtocol (readiness bridge) context scope canonical finalContext tail.scope tail.canonical) ∧
      (readiness bridge).Ready finalContext tail.state ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) ∧
      finalContext = staticFinal ∧ Admission bridge context tail.state ∧
      Admission bridge staticFinal tail.state ∧ Dynamic.HeapTypesExtend before after ∧
      Dynamic.EnvironmentAgrees after staticFinal.locals finalEnvironment

abbrev FaultAt (R : HeaderReceiptFamily) : Prop :=
  ∀ {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop} {control : ControlContext}
    {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (_receipt : R type continuation context scope items code)
    (_valid : validity context) {staticFinal : SourceSemantics.Context}
    (_itemTyping : ForItemsHaveType source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_gate : condition contextLocation native) (_ready : (readiness bridge).Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (_trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (_bounded : size ≤ budget),
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition (readiness bridge) state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

abbrev ReflectsAt (R : HeaderReceiptFamily) : Prop :=
  ∀ {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop} {control : ControlContext}
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (_receipt : R type continuation context scope items code)
    (_valid : validity context) {staticFinal : SourceSemantics.Context}
    (_itemTyping : ForItemsHaveType source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_gate : condition contextLocation native) (_ready : (readiness bridge).Ready context state)
    {size : Nat} (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (_bounded : size ≤ budget),
    ResultAtFor callerProtocol (readiness bridge) condition validity size registry functions program source [] evidence administrative frame globals contextLocation native type faults continuation
      context environment ⟨scope, mapping, world, before, store, canonical⟩ state items value finalStore

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend in
theorem legacy_PrefixAt (diagnosticPolicy : AssignmentDiagnosticPolicy) (meaning : ∀ context, validity context → RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size)) :
    PrefixAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) bridge functions evidence condition validity budget (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults) := by
  intro type continuation control context finalContext scope items code receipt valid staticFinal itemTyping mapping world actualContext environment finalEnvironment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready size trace bounded
  obtain ⟨tree, errors⟩ := receipt
  exact CallableIndexedOwnedAdmittedForHeaderBounds.preserves_prefix_bounded_for (solved := [])
    bridge functions definitions registered extension evidence faithful observations condition producer acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget meaning tree valid itemTyping environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend in
theorem legacy_FaultAt (diagnosticPolicy : AssignmentDiagnosticPolicy) (meaning : ∀ context, validity context → RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size)) :
    FaultAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence condition validity budget (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults) := by
  intro type continuation control context finalContext scope items code receipt valid staticFinal itemTyping mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
  obtain ⟨tree, errors⟩ := receipt
  exact CallableIndexedOwnedAdmittedForHeaderBounds.preserves_fault_reachable_bounded_for
    bridge functions definitions registered extension evidence faithful observations condition producer acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget meaning tree (GenericForHeader.Tree.ErrorsFor.reachable errors) valid itemTyping environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend in
theorem legacy_ReflectsAt (diagnosticPolicy : AssignmentDiagnosticPolicy)  (functionTypes : FunctionRuntimeViews functions) (reflection : ∀ context, validity context → RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size)) :
    ReflectsAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence condition validity budget (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults) := by
  intro type continuation control context scope items code receipt valid staticFinal itemTyping mapping world actualContext environment canonical actual before store finalStore value ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready size evaluated bounded
  obtain ⟨tree, errors⟩ := receipt
  exact CallableIndexedOwnedAdmittedForHeaderBounds.reflects_reachable_bounded_for (solved := [])
    bridge functions definitions registered extension evidence faithful observations condition producer acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget functionTypes reflection tree (GenericForHeader.Tree.ErrorsFor.reachable errors) valid itemTyping environments heaps locals agrees actualTyped reference read unmapped state gate ready evaluated bounded

variable (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative ambient.definitions)
  (UP : GenericForHeader.Structural.UnaryPayload)
  (unary : ∀ {context scope assignment} (head : CompatibleBitNotStatements.Head context scope assignment), UP head → head.Errors faults)

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend in
theorem prepared_PrefixAt (meaning : ∀ context, validity context → RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size))
    : PrefixAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) bridge functions evidence condition validity budget (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) AP UP) := by
  intro type continuation control context finalContext scope items code receipt valid staticFinal itemTyping mapping world actualContext environment finalEnvironment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready size trace bounded
  exact CallableIndexedOwnedPreparedForHeaderBounds.preserves_prefix_from_structural_bounded_for (solved := [])
    bridge functions definitions registered extension evidence faithful observations condition producer acquire stateTransport stateBindings unique wellFormed AP UP validity runtime covers extend budget meaning receipt valid itemTyping environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend unary in
theorem prepared_FaultAt (meaning : ∀ context, validity context → RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size))
    (assignments : ∀ context, validity context → AssignmentFaultPreservesWithPayloadAt callerProtocol (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry) program evidence source (certificates context) context administrative faults budget AP)
    : FaultAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence condition validity budget (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) AP UP) := by
  intro type continuation control context finalContext scope items code receipt valid staticFinal itemTyping mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
  exact CallableIndexedOwnedPreparedForHeaderBounds.preserves_fault_with_payload_bounded_for
    bridge functions definitions registered extension evidence faithful observations condition producer acquire stateTransport stateBindings unique wellFormed AP UP unary validity runtime covers extend budget meaning receipt assignments valid itemTyping environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend unary in
theorem prepared_ReflectsAt (reflection : ∀ context, validity context → RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size))
    (assignments : ∀ context, validity context → AssignmentReflectsWithPayloadAt callerProtocol (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry) program evidence source (certificates context) context administrative faults budget AP)
    : ReflectsAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence condition validity budget (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) AP UP) := by
  intro type continuation control context scope items code receipt valid staticFinal itemTyping mapping world actualContext environment canonical actual before store finalStore value ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready size evaluated bounded
  exact CallableIndexedOwnedPreparedForHeaderBounds.reflects_with_payload_bounded_for (solved := [])
    bridge functions definitions registered evidence observations condition producer acquire stateTransport stateBindings unique wellFormed AP UP unary validity runtime covers extend budget reflection receipt assignments valid itemTyping environments heaps locals agrees actualTyped reference read unmapped state gate ready evaluated bounded

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedHeaderReceiptOperations
