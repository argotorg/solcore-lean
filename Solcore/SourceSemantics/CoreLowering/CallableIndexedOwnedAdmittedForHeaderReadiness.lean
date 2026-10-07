import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSnapshotAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderSourceSites

/-! Actual Source item facts choose admitted assignment and snapshot producers.
Every returned witness is the original child's reached pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (ValuesContext)
open ProtectedStateTransition ProtectedForHeader.Stateful.WithReady
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

variable {values : ValuesContext} {source : TypedSource}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  (transport : AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {faults : FunctionCalls.FaultRep}

include extension transport faithful observations unique wellFormed in
theorem assignment_prefix (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (budget : Nat)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source certificate faults size)) :
    AssignmentPrefixPreservesAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType source) functions (registry := registry) program evidence source certificate context administrative budget := by
  intro scope assignment operator rhs head assignmentTyped mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted updated after size trace bounded
  exact CallableIndexedOwnedAdmittedAssignmentHeads.preserves_prefix_bounded bridge functions extension evidence transport
    faithful observations head environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
    wellFormed runtime covers budget meaning trace bounded

include extension transport faithful observations unique wellFormed in
theorem assignment_fault (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (budget : Nat)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source certificate faults size)) :
    AssignmentFaultPreservesAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType source) functions (registry := registry) program evidence source certificate context administrative faults budget := by
  intro scope assignment operator rhs head assignmentTyped mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted errors reason after size trace bounded next output
  exact CallableIndexedOwnedAdmittedAssignmentHeads.preserves_fault_reachable_bounded bridge functions extension evidence transport
    faithful observations head environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
    wellFormed runtime covers budget meaning errors trace bounded next output

include extension transport faithful observations unique wellFormed in
theorem assignment_reflection (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source certificate faults size)) :
    AssignmentReflectsAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType source) functions (registry := registry) program evidence source certificate context administrative faults budget := by
  intro scope assignment operator rhs head assignmentTyped mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted errors next output value finalStore size evaluated bounded
  have result := CallableIndexedOwnedAdmittedAssignmentHeads.reflects_reachable_bounded bridge functions extension evidence transport
    faithful observations head environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
    wellFormed runtime covers budget meaning functionTypes errors evaluated bounded
  cases result with
  | fault trace same matched heaps maps worlds frame metadata reached related stable =>
    exact .fault trace same matched heaps maps worlds frame metadata ⟨reached, related, stable⟩
  | success trace heaps maps worlds frame metadata count typed reached related admitted smaller remaining =>
    exact .success trace heaps maps worlds frame metadata count typed ⟨reached, related, admitted⟩ smaller remaining

include wellFormed in
theorem snapshot_transfers (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context) :
    SnapshotTransfers callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      validity (SourceBitNotAssignmentValid source) program evidence source where
  ready := by
    intro initial reached first last context assignment environment updated admitted valid typing trace locals frame
    exact (CallableIndexedOwnedSnapshotAdmission.after_snapshot bridge first last admitted wellFormed
      (runtime context valid) (covers context valid) locals typing trace frame).1

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderReadiness
