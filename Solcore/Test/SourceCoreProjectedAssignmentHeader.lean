import Solcore.SourceSemantics.CoreLowering.ProtectedStateProjectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderControl

/-! Actual assignment Heads supply all three header callbacks for bare and
projected targets, retaining the reached success or fault state. -/
set_option autoImplicit false
namespace Tests.SourceCoreProjectedAssignmentHeader
open Solcore
open SourceSemantics SourceSemantics.CoreLowering
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {context : SourceSemantics.Context} {administrative : Core.Context}
  {faults : FunctionCalls.FaultRep} {Records : Type v}
  (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  (budget : Nat)
  (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
    ProtectedStateTransition.PreservesAt protocol (payloadModel values.checked registry functions)
      program context evidence source certificate faults size))

include extension transport faithful observations meaning in
theorem full_successful_head_discharges_header :
    ProtectedForHeader.Stateful.AssignmentPrefixPreservesAt protocol functions (registry := registry)
      program evidence source certificate context administrative budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial updated after size trace bounded
  exact ProtectedAssignmentHeads.Stateful.Head.preserves_prefix_bounded functions extension program evidence
    protocol transport faithful observations head environments heaps locals agrees actualTyped initial
    budget meaning trace bounded

include extension transport faithful observations meaning in
theorem full_fault_head_discharges_header :
    ProtectedForHeader.Stateful.AssignmentFaultPreservesAt protocol functions (registry := registry)
      program evidence source certificate context administrative faults budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial errors reason after size trace bounded next output
  exact ProtectedAssignmentHeads.Stateful.Head.preserves_fault_reachable_bounded functions extension program evidence
    protocol transport faithful observations head environments heaps locals agrees actualTyped initial
    budget meaning errors trace bounded next output

include extension transport faithful observations in
theorem full_reflected_head_discharges_header
    (functionTypes : FunctionRuntimeViews functions)
    (reflection : RecursiveNamedBoundedContracts.Below budget (fun size =>
      ProtectedStateTransition.ReflectsAt protocol (payloadModel values.checked registry functions)
        program context evidence source certificate faults size)) :
    ProtectedForHeader.Stateful.AssignmentReflectsAt protocol functions (registry := registry)
      program evidence source certificate context administrative faults budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial errors next output value finalStore size completed bounded
  exact ProtectedAssignmentHeads.Stateful.Head.reflects_reachable_bounded functions extension program evidence
    protocol transport faithful observations head environments heaps locals agrees actualTyped initial
    budget reflection functionTypes errors completed bounded


end Tests.SourceCoreProjectedAssignmentHeader
