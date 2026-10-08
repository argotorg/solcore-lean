import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCatalogProducers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderBounds

/-! Authentic finite catalog recipes consume only their actual smaller child
results. Source facts identify visited contexts; the existing loop and post
producers keep the exact reached pools and independent Source/native grades. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogProducers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open TypedLexicalWhile (Scope ValuesContext)
open ProtectedStateImperativeCatalogReady
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
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
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (guard : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, guard location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (stateTransport : AdministrativeTransport callerProtocol) (stateBindings : Bindings callerProtocol)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
  (validity : SourceSemantics.Context → Prop)
  (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
  (covers : ∀ context, validity context → evidence.Covers context)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (budget : Nat) (diagnosticPolicy : AssignmentDiagnosticPolicy)
  {solved : List SolvedRequirement}
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)

variable {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy source invalidOperand}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
  (unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped source)
  (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep table reason token → faults reason token)

local notation "PreparedAP" => (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
local notation "PreparedUP" => (fun head => GenericForHeader.Structural.PreparedUnary true source (fun site root => table.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) head)
local notation "PreparedHP" => (fun tree => GenericImperativeMatch.Structural.PreparedHeader (factory := factory)
  (invalidProjection := invalidProjection) (missingDefault := missingDefault)
  (invalidUnary := fun site root => table.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) tree)
local notation "PreparedR" => ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
  (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions)
  (administrative := administrative) PreparedAP PreparedUP

/-- The same actual post Tree and its Plan tokens yield its structural receipt. -/
theorem post_receipt {context scope items type code}
    (tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code)
    (payload : PreparedHP tree) : PreparedR type (TypedForHeader.Fallthrough type) context scope items code := by
  obtain ⟨plan, coupled, tokens⟩ := payload
  exact GenericForHeader.Structural.of_coupled coupled tokens

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend unaryTyped issued unaryIncluded in
theorem preserving_loops
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size))
    (assignments : ∀ context, validity context → ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt callerProtocol (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry) program evidence source (certificates context) context administrative faults budget PreparedAP) :
    ProtectedStateImperativeCatalogPayload.PreservingLoopsWithPayload callerProtocol (readiness bridge) guard
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      functions program evidence validity budget
      (CallableIndexedOwnedAdmittedCatalogProducers.PreservingGoalWithReceipt bridge functions evidence guard validity budget PreparedR (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      PreparedHP (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  exact CallableIndexedOwnedAdmittedCatalogProducers.preserving_loops_with_receipts (stateTransport := stateTransport) (unique := unique)
    bridge functions evidence guard validity budget PreparedR PreparedHP
    (CallableIndexedOwnedPostReceiptOperations.prefixat_of_header_receipt (source := source) (certificates := certificates) (administrative := administrative) bridge functions evidence guard validity budget PreparedHP PreparedR (post_receipt diagnosticPolicy) (CallableIndexedOwnedHeaderReceiptOperations.prepared_PrefixAt (AP := PreparedAP) (UP := PreparedUP) bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget meaning))
    (CallableIndexedOwnedPostReceiptOperations.faultat_of_header_receipt (source := source) (certificates := certificates) (administrative := administrative) (faults := faults) bridge functions evidence guard validity budget PreparedHP PreparedR (post_receipt diagnosticPolicy) (CallableIndexedOwnedHeaderReceiptOperations.prepared_FaultAt (AP := PreparedAP) (UP := PreparedUP) (unary := (fun head receipt => GenericForHeader.Structural.PreparedUnary.errors receipt unaryTyped issued unaryIncluded)) bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget meaning assignments))
    meaning

include definitions registered observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend unaryTyped issued unaryIncluded in
theorem reflecting_loops
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size))
    (assignments : ∀ context, validity context → ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt callerProtocol (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry) program evidence source (certificates context) context administrative faults budget PreparedAP) :
    ProtectedStateImperativeCatalogPayload.ReflectingLoopsWithPayload callerProtocol (readiness bridge) guard
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      functions program evidence validity budget
      (CallableIndexedOwnedAdmittedCatalogProducers.ReflectingGoalWithReceipt bridge functions evidence guard validity budget PreparedR (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      PreparedHP (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  exact CallableIndexedOwnedAdmittedCatalogProducers.reflecting_loops_with_receipts (stateTransport := stateTransport) (unique := unique)
    bridge functions evidence guard validity budget PreparedR PreparedHP
    (CallableIndexedOwnedPostReceiptOperations.reflectsat_of_header_receipt (source := source) (certificates := certificates) (administrative := administrative) (faults := faults) bridge functions evidence guard validity budget PreparedHP PreparedR (post_receipt diagnosticPolicy) (CallableIndexedOwnedHeaderReceiptOperations.prepared_ReflectsAt (AP := PreparedAP) (UP := PreparedUP) (unary := (fun head receipt => GenericForHeader.Structural.PreparedUnary.errors receipt unaryTyped issued unaryIncluded)) bridge functions definitions registered evidence observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget reflection assignments))
    reflection

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend unaryTyped issued unaryIncluded runtimeOf in
theorem preserving_heads
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size))
    (assignments : ∀ context, validity context → ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt callerProtocol (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry) program evidence source (certificates context) context administrative faults budget PreparedAP) :
    PreservingHeads callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity budget
      (CallableIndexedOwnedAdmittedCatalogProducers.PreservingGoalWithReceipt bridge functions evidence guard validity budget PreparedR (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  exact CallableIndexedOwnedAdmittedCatalogProducers.preserving_heads_with_receipts
    bridge functions definitions registered extension evidence guard producer acquire stateTransport stateBindings unique validity extend budget runtimeOf PreparedR
    (CallableIndexedOwnedHeaderReceiptOperations.prepared_PrefixAt (AP := PreparedAP) (UP := PreparedUP) bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget meaning)
    (CallableIndexedOwnedHeaderReceiptOperations.prepared_FaultAt (AP := PreparedAP) (UP := PreparedUP) (unary := (fun head receipt => GenericForHeader.Structural.PreparedUnary.errors receipt unaryTyped issued unaryIncluded)) bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget meaning assignments)
    meaning

include definitions registered extension observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend unaryTyped issued unaryIncluded runtimeOf in
theorem reflecting_heads
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size))
    (assignments : ∀ context, validity context → ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt callerProtocol (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry) program evidence source (certificates context) context administrative faults budget PreparedAP) :
    ReflectingHeads callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity budget
      (CallableIndexedOwnedAdmittedCatalogProducers.ReflectingGoalWithReceipt bridge functions evidence guard validity budget PreparedR (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  exact CallableIndexedOwnedAdmittedCatalogProducers.reflecting_heads_with_receipts
    bridge functions definitions registered extension evidence guard producer acquire stateTransport stateBindings unique validity extend budget runtimeOf PreparedR
    (CallableIndexedOwnedHeaderReceiptOperations.prepared_ReflectsAt (AP := PreparedAP) (UP := PreparedUP) (unary := (fun head receipt => GenericForHeader.Structural.PreparedUnary.errors receipt unaryTyped issued unaryIncluded)) bridge functions definitions registered evidence observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget reflection assignments)
    reflection

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogProducers
