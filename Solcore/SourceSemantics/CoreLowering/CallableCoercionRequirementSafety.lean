import Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectedInvocation

/-! Actual singleton selection excludes unavailable requirements only at reached
identities. The ordered list may repeat identities; no global ledger uniqueness
or dictionary equality is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRequirementSafety
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

abbrev UniqueAt (context : Context) (id : RequirementId) : Prop :=
  ∀ first second, ContainsRequirement context id first → ContainsRequirement context id second → first = second

theorem excludes_unavailable {context : Context} {caller : EvidenceEnvironment}
    {id : RequirementId} {goal : ProgramPredicate} {closed : TraitEvidence}
    (unique : UniqueAt context id) (produces : RequirementProducesEvidence context caller id goal closed)
    (fault : RequirementUnavailable context caller id) : False := by
  cases produces with
  | intro contains _ representation _ closes _ =>
    cases fault with
    | missing absent => exact absent _ contains.1 contains.2
    | evidence otherContains otherRepresentation failed =>
      cases unique _ _ contains otherContains
      cases representation.functional otherRepresentation
      exact closes.excludes_fault failed

theorem excludes_list_fault {context : Context} {caller returned : EvidenceEnvironment}
    {ids : List RequirementId} {goals : List ProgramPredicate} {failed : RequirementId}
    (unique : ∀ id ∈ ids, UniqueAt context id)
    (produces : RequirementsProduceEnvironment context caller ids goals returned)
    (fault : RequirementListFaults context caller ids failed) : False := by
  induction produces generalizing failed with
  | nil => cases fault
  | cons head tail ih =>
    cases fault with
    | head unavailable => exact excludes_unavailable (unique _ (by simp)) head unavailable
    | tail _ failed => exact ih (fun id member => unique id (List.mem_cons_of_mem _ member)) failed

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

/-- Each actual list row has its own singleton receipt, even when an identity
occurs again later in the list. Unrelated ledger rows are unconstrained. -/
theorem list_unique {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available returned : SourceCompilationPlan.EvidenceEnvironment}
    {ids : List RequirementId} {goals : List ProgramPredicate} {context : Context}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidenceList program caller node available ids goals = .ok returned) :
    ∀ id ∈ ids, UniqueAt context id := by
  induction ids generalizing goals returned with
  | nil => simp
  | cons id ids ih =>
    cases goals with
    | nil => cases accepted
    | cons goal goals =>
      unfold SourceCompilationPlan.exactRuntimeRequirementEvidenceList at accepted
      obtain ⟨head, headAccepted, accepted⟩ := bind_ok accepted
      obtain ⟨tail, tailAccepted, _⟩ := bind_ok accepted
      intro key member
      rcases List.mem_cons.mp member with rfl | member
      · exact CallableCoercionSelectionIdentity.primary_unique ledger headAccepted
      · exact ih tailAccepted key member

/-- Successful source selection provides the real evidence closures; actual
compiler selection identifies the ledger rows used by any competing fault. -/
theorem selected_safe {compiler : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceCompilationPlan.EvidenceEnvironment}
    {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod} {context : Context}
    {program : Program} {evidence dictionary : EvidenceEnvironment} {body : BodyInstance}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (accepted : SourceCompilationPlan.checkedCoercionMethod compiler caller node available step = .ok method)
    (selected : OperatorMethodSelected program context evidence "Coerce" "coerce" step.requirements body dictionary)
    {failed : RequirementId} (fault : RequirementListFaults context evidence step.requirements failed) : False := by
  obtain ⟨receipt⟩ := CallableCoercionMethodCertificates.of_accepted accepted
  have primaryUnique := CallableCoercionSelectionIdentity.primary_unique ledger receipt.primarySelected
  have remainingUnique := list_unique ledger receipt.methodsSelected
  cases selected with
  | intro primary _ _ _ _ _ _ _ _ _ remaining _ _ _ =>
    cases primary with
    | intro produced _ =>
      cases fault with
      | head unavailable => exact excludes_unavailable primaryUnique produced unavailable
      | tail _ failed => exact excludes_list_fault remainingUnique remaining failed

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRequirementSafety
