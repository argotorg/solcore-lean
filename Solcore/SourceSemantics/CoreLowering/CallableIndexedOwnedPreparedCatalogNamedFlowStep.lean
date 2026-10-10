import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedBodyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalFlowBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping

/-! Named F selects the exact Prepared/HeaderAt and coupled collector retained
by the actual entry profile. Its original structural head/loop producer runs
once from graded E induction hypotheses. Authentic receiving table rebuilding
and reached interpretation are explicit static obligations for that same
issuance; no finished expression or body law is stored in the profile. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedFlowStep
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedCatalogNamedProfiles (Profile)
open CallableIndexedOwnedPreparedCatalogNamedBodyContinuations (Validity FlowPreserves FlowReflects bridge body_protocol)
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {administrative : Core.Context}
  (profile : Profile (certificates := certificates) (expressionSyntax := expressionSyntax) header administrative)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : profile.receiving.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep profile.receiving.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep profile.receiving.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity header context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := certificates header)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      (factory := profile.factory) (faults := faults) (registry := registry) profile.receiving
      (bridge (headers := headers) owner header) functions table)

include wellFormed in
private theorem source_runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    header.context header.function.source := by
  obtain ⟨_facts, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields certified.typing.inputs_extend
  simpa only [header.frame.source] using certified.sourceRuntimeValid.transport fields

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- Preservation uses E at sizes at most n at the exact visited contexts. -/
theorem preserves_flow (budget : Nat)
    (meaning : ∀ context, Validity header context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) owner header)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context header.function.evidence header.function.source (certificates header context) faults size)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves (headers := headers) (registry := registry) (faults := faults) functions owner profile) := by
  have eliminated := profile.prepared_eliminator
  rw [profile.aligned.layouts, profile.aligned.globals] at eliminated
  have result := CallableIndexedOwnedContextualLambdaPreparedFlowBounds.preserves_flow
    (active := header.active) (onError := header.onError) (solved := header.solved)
    (expressionSyntax := expressionSyntax header) (certificates := certificates header)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (registry := registry) (faults := faults) (factory := profile.factory)
    profile.receiving (bridge (headers := headers) owner header) functions rfl
    (CallableIndexedAmbient.frame_registered compiled.indexed) extension header.function.evidence faithful observations
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (Origin.producer (headers := headers) (registry := registry) (.ordinary header) owner functions)
    (Origin.acquire (headers := headers) (registry := registry) (.ordinary header) owner functions)
    (Origin.transport (headers := headers) (.ordinary header) owner)
    (Origin.bindings (headers := headers) (.ordinary header) owner)
    header.unique wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (source_runtime wellFormed) meaning eliminated
  have sameValidity :
      CallableIndexedOwnedContextualLambdaPreparedFlowBounds.Validity (compiled := compiled)
        (source := header.function.source) (solved := header.solved) header.function.evidence =
      CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.Validity true header := rfl
  rw [sameValidity] at result
  dsimp only [ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt, RecursiveNamedHeaderContracts.AtMost, FlowPreserves,
    CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.FlowPreserves,
    bridge, body_protocol, CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.body_protocol] at result ⊢
  simpa only [SourceCoreCompatibleValues.Context.initial, profile.aligned.globals] using result

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- Reflection consumes strict native E grades and retains its independent
Source grade through the same original prepared producer. -/
theorem reflects_flow (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (meaning : ∀ context, Validity header context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge (headers := headers) owner header)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context header.function.evidence header.function.source (certificates header context) faults size)) :
    Below budget
      (FlowReflects (headers := headers) (registry := registry) (faults := faults) functions owner profile) := by
  have eliminated := profile.prepared_eliminator
  rw [profile.aligned.layouts, profile.aligned.globals] at eliminated
  have result := CallableIndexedOwnedContextualLambdaPreparedFlowBounds.reflects_flow
    (active := header.active) (onError := header.onError) (solved := header.solved)
    (expressionSyntax := expressionSyntax header) (certificates := certificates header)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (registry := registry) (faults := faults) (factory := profile.factory)
    profile.receiving (bridge (headers := headers) owner header) functions rfl
    (CallableIndexedAmbient.frame_registered compiled.indexed) extension header.function.evidence faithful observations
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (Origin.producer (headers := headers) (registry := registry) (.ordinary header) owner functions)
    (Origin.acquire (headers := headers) (registry := registry) (.ordinary header) owner functions)
    (Origin.transport (headers := headers) (.ordinary header) owner)
    (Origin.bindings (headers := headers) (.ordinary header) owner)
    header.unique wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (source_runtime wellFormed) functionTypes meaning eliminated
  have sameValidity :
      CallableIndexedOwnedContextualLambdaPreparedFlowBounds.Validity (compiled := compiled)
        (source := header.function.source) (solved := header.solved) header.function.evidence =
      CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.Validity true header := rfl
  rw [sameValidity] at result
  dsimp only [ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt, RecursiveNamedBoundedContracts.Below, Below, FlowReflects,
    CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.FlowReflects,
    bridge, body_protocol, CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.body_protocol] at result ⊢
  simpa only [SourceCoreCompatibleValues.Context.initial, profile.aligned.globals] using result

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedFlowStep
