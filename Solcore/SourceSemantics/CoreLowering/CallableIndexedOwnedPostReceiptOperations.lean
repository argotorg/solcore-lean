import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedHeaderReceiptOperations
import Solcore.SourceSemantics.CoreLowering.ProtectedImperativeCatalogPayloadContracts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedForItemsAdmission
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderPost

/-! Authentic Source item typing and admission feed the existing header and
post producers at their exact reached states. The original Source and native
budgets remain independent; all binder restoration retains the real pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPostReceiptOperations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (postValues Progress postValues_typed postValues_agree post_rename)
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

variable (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative))

abbrev PrefixAt : Prop :=
  ∀ {type : Ty} {control : ControlContext} {context : SourceSemantics.Context} {scope : Scope} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {conditionCode body postCode : Expr} {selfReason : Word}
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
{items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (_payload : HP tree)
    (_valid : validity context) {staticFinal : SourceSemantics.Context}
    (_itemTyping : ForItemsHaveType source control context items staticFinal)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_guarded : condition contextLocation native) (_ready : (readiness bridge).Ready context state.retained)
    (continued : Bool)
    {size : Nat} (_trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (_bounded : size ≤ budget),
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ (readiness bridge).Ready context reached.retained

abbrev FaultAt : Prop :=
  ∀ {type : Ty} {control : ControlContext} {context : SourceSemantics.Context} {scope : Scope} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {conditionCode body postCode : Expr} {selfReason : Word}
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
{items : List ForItemForm} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (_payload : HP tree)
    (_valid : validity context) {staticFinal : SourceSemantics.Context}
    (_itemTyping : ForItemsHaveType source control context items staticFinal)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_guarded : condition contextLocation native) (_ready : (readiness bridge).Ready context state.retained)
    (continued : Bool)
    {size : Nat} (_trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (_bounded : size ≤ budget),
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ (readiness bridge).FaultReady reached.retained

abbrev ReflectsAt : Prop :=
  ∀ {type : Ty} {control : ControlContext} {context : SourceSemantics.Context} {scope : Scope} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {conditionCode body postCode : Expr} {selfReason : Word}
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
{items : List ForItemForm} {value : Value} {finalStore : Store}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (_payload : HP tree)
    (_valid : validity context) {staticFinal : SourceSemantics.Context}
    (_itemTyping : ForItemsHaveType source control context items staticFinal)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_guarded : condition contextLocation native) (_ready : (readiness bridge).Ready context state.retained)
    (continued : Bool)
    {size : Nat} (_evaluated : EvaluationSize size (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ)) value finalStore) (_bounded : size ≤ budget),
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ (readiness bridge).Ready context reached.retained) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ (readiness bridge).FaultReady reached.retained)

variable (R : HeaderReceiptFamily)
  (toReceipt : ∀ {context scope items type code}
    (tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type (TypedForHeader.Fallthrough type) context scope items code),
    HP tree → R type (TypedForHeader.Fallthrough type) context scope items code)

include toReceipt in
theorem prefixat_of_header_receipt
    (operation : CallableIndexedOwnedHeaderReceiptOperations.PrefixAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) bridge functions evidence condition validity budget R) :
    PrefixAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (certificates := certificates) (administrative := administrative) (registry := registry) bridge functions evidence condition validity budget HP := by
  intro type control context scope actualContext environment canonical actual ξ contextLocation location conditionCode body postCode selfReason mapping world before after store items finalContext finalEnvironment tree payload valid staticFinal itemTyping agrees reference state native read guarded ready continued size trace bounded
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.live.selfTyped state.live.actualTyped
  obtain ⟨tail, maps, worlds, preservation, metadata, related, ⟨returnTo⟩, tailReady, agreement, _same, _originalAdmission, _finalAdmission, _heapExtend, _locals⟩ :=
    operation (toReceipt tree payload) valid itemTyping
      state.live.environments state.live.heaps state.live.locals (postValues_agree agrees type location continued)
      postTyped reference read state.live.contextUnmapped state.retained guarded ready trace bounded
  exact ProtectedForHeader.Stateful.WithReady.post_preserves_bounded_for_with_header_result
    callerProtocol condition functions evidence (readiness bridge) validity state continued
    ⟨tail, maps, worlds, preservation, metadata, related, ⟨returnTo⟩, tailReady, agreement⟩


include toReceipt in
theorem faultat_of_header_receipt
    (operation : CallableIndexedOwnedHeaderReceiptOperations.FaultAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence condition validity budget R) :
    FaultAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence condition validity budget HP := by
  intro type control context scope actualContext environment canonical actual ξ contextLocation location conditionCode body postCode selfReason mapping world before after store items finalContext reason tree payload valid staticFinal itemTyping agrees reference state native read guarded ready continued size trace bounded
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.live.selfTyped state.live.actualTyped
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, preservation, metadata, transition⟩ :=
    operation (toReceipt tree payload) valid itemTyping
      state.live.environments state.live.heaps state.live.locals (postValues_agree agrees type location continued)
      postTyped reference read state.live.contextUnmapped state.retained guarded ready trace bounded
  exact ProtectedForHeader.Stateful.WithReady.post_fault_reachable_bounded_for_with_header_result
    callerProtocol functions (readiness bridge) state continued
    ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, preservation, metadata, transition⟩


include toReceipt in
theorem reflectsat_of_header_receipt
    (operation : CallableIndexedOwnedHeaderReceiptOperations.ReflectsAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence condition validity budget R) :
    ReflectsAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence condition validity budget HP := by
  intro type control context scope actualContext environment canonical actual ξ contextLocation location conditionCode body postCode selfReason mapping world before store items value finalStore tree payload valid staticFinal itemTyping agrees reference state native read guarded ready continued size evaluated bounded
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.live.selfTyped state.live.actualTyped
  have result := operation (toReceipt tree payload) valid itemTyping
      state.live.environments state.live.heaps state.live.locals (postValues_agree agrees type location continued)
      postTyped reference read state.live.contextUnmapped state.retained guarded ready
      (by simpa only [post_rename] using evaluated) bounded
  exact ProtectedForHeader.Stateful.WithReady.post_reflects_reachable_bounded_for_with_header_result
    callerProtocol condition functions program evidence (readiness bridge) validity state result


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPostReceiptOperations
