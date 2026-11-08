import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StatementAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForPost
import Solcore.SourceSemantics.Staging.Internal.SelectedContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState

/-!
# Owned callables: receipt operations

Operations on header and post receipts, and admission of staged projected bit-not updates.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedHeaderReceiptOperations
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

include definitions registered producer acquire stateTransport stateBindings unique wellFormed runtime covers extend unary in
theorem prepared_ReflectsAt (reflection : ∀ context, validity context → RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size))
    (assignments : ∀ context, validity context → AssignmentReflectsWithPayloadAt callerProtocol (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry) program evidence source (certificates context) context administrative faults budget AP)
    : ReflectsAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence condition validity budget (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) AP UP) := by
  intro type continuation control context scope items code receipt valid staticFinal itemTyping mapping world actualContext environment canonical actual before store finalStore value ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready size evaluated bounded
  exact CallableIndexedOwnedPreparedForHeaderBounds.reflects_with_payload_bounded_for (solved := [])
    bridge functions definitions registered evidence condition producer acquire stateTransport stateBindings unique wellFormed AP UP unary validity runtime covers extend budget reflection receipt assignments valid itemTyping environments heaps locals agrees actualTyped reference read unmapped state gate ready evaluated bounded

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedHeaderReceiptOperations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPostReceiptOperations
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedBitNotAdmission
/-! The actual typed key endpoint supplies admission for a projected unary write. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedBitNotAdmission
open Frontend SourceInference Staging.Recursive

theorem heap_after_bitNot
    {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {environment : Dynamic.Environment}
    {before getter after : Dynamic.Heap} {types : List TypeSystem.Ty} {values : List Dynamic.Value}
    {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
    (unique : NodeOccurrencesUnique source)
    (typed : SourceBitNotAssignmentValid source context assignment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (row : ExpressionsHaveTypes source context (ProjectedTarget.keys assignment.target.projections) types)
    (keyValues : Dynamic.ValuesHaveTypes context getter values types)
    (getterHeap : Dynamic.HeapWellTyped context getter)
    (getterMetadata : Dynamic.HeapTypesExtend before getter)
    (snapshot : ProjectedTarget.Snapshot environment before getter assignment.target values target)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
      getter target updated after) :
    Dynamic.HeapWellTyped context after := by
  cases typed with
  | intro targetTyped _ =>
      obtain ⟨root, savedTyped⟩ := SelectedPreservation.projected_target_typed unique locals
        getterHeap getterMetadata targetTyped row keyValues snapshot
      exact (SelectedPreservation.projected_write_bitNot savedTyped getterHeap write).1

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedBitNotAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedRankedOrdinarySupportReceipts
/-! Genuine original ranked support already contains a complete same-Code
static body. This finite projection keeps its Header, Source, certificate
family and compiler receipts; the original full history seed remains the same.
No new static rank or body execution proof is constructed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedRankedOrdinarySupportReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}
  (body : CallableIndexedOwnedFunctionValues.StaticSupport headers registry faults code)

/-- The existing receipt supplies every unrestricted support field verbatim.
Its independent static rank remains inside the original certificate family. -/
def support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults := by
  let actual := CallableIndexedLambdaNestedRuntimeCertificates.BodyAt.receipt body.2.2
  exact ⟨body.1, _, _, actual.source, actual.compilation, actual.active, actual.body⟩

/-- The selected genuine Header is unchanged. -/
theorem caller : (support body).caller = body.1 := rfl

include body in
/-- The original static receipt authenticates the same compiler prefix. -/
theorem native_prefix : administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) (support body).caller :=
  (CallableIndexedLambdaNestedRuntimeCertificates.BodyAt.receipt body.2.2).administrative

/-- The complete original ClosureFrame is retained, including raw Source. -/
theorem frame : (support body).body.frame =
    (CallableIndexedLambdaNestedRuntimeCertificates.BodyAt.receipt body.2.2).body.frame := rfl

/-- The actual original Source origin identifies this same complete seed. -/
theorem source_origin (history : History code)
    (origin : CallableIndexedOwnedFunctionValues.ActualSourceOrigin code history body) :
    CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin (support body) history :=
  ⟨origin.historyMetadata⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedRankedOrdinarySupportReceipts
end
