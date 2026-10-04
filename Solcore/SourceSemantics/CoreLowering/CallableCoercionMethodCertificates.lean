import Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedCallEvidence
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineCertificates

/-! The actual coercion selector retains the primary tree and ordered method
evidence used to check its synthetic method. These receipts concern selection
and dictionaries; they do not identify the plan's emitted closure or prove its
body semantics. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodCertificates
open Frontend SourceInference
abbrev RawEvidence := TypedTraitResolution.Evidence
abbrev Dictionary := SourceTypedRuntime.RuntimeEvidenceEnvironment

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem require_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then action else .error error) = .ok value) :
    condition ∧ action = .ok value := by
  split at accepted
  · exact ⟨‹condition›, accepted⟩
  · cases accepted

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

private theorem method_fields {program : CheckedProgram} {primary : RawEvidence}
    {methodEvidence : Dictionary} {arity : Nat} {name : String}
    {method : ExecutableImplMethods.CheckedMethod}
    (accepted : ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary methodEvidence arity name = .ok method) :
    ∃ goal implementation, primary = .byImpl goal implementation method.implementationPremises ∧
      method.methodPremises = methodEvidence := by
  cases primary with
  | byImpl goal implementation premises =>
    simp only [ExecutableImplMethods.checkMethodWithEvidenceAndArity] at accepted
    split at accepted <;> try contradiction
    try simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
    split at accepted <;> try contradiction
    try simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨implementationSignature, _, accepted⟩ := bind_ok accepted
    split at accepted <;> try contradiction
    split at accepted <;> try contradiction
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨trait, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨implementationMethod, _, accepted⟩ := bind_ok accepted
    obtain ⟨traitMethod, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    obtain ⟨genericChecked, _, accepted⟩ := bind_ok accepted
    obtain ⟨specialized, _, accepted⟩ := bind_ok accepted
    obtain ⟨_, accepted⟩ := require_ok accepted
    cases accepted
    exact ⟨goal, _, rfl, rfl⟩

open Solcore.SourceSemantics.Dynamic CallableEvidenceEnvironment
open CallableNamedMetadata (evidence environment evidence_represents)

private theorem validated_requirement {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : Dictionary} {id : RequirementId} {goal : ProgramPredicate} {raw : RawEvidence}
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available id goal = .ok raw) :
    EvidenceValid [] program.signatures.resolutionRules goal (evidence raw) := by
  have finish : ∀ selected,
      (match (TypedTraitResolution.resolve program.signatures.resolutionRules 32 goal).outcome with
        | .noSolution => Except.error (SourceTypedRuntime.RuntimeError.callEvidenceResolutionNoSolution caller.key node.id id goal)
        | .inconclusive reason => .error (.callEvidenceResolutionInconclusive caller.key node.id id reason)
        | .success chosen => if chosen == selected then .ok () else
            let .byImpl _ implementation _ := selected
            .error (.callEvidenceNotSelected caller.key node.id id goal implementation)) = .ok () →
      EvidenceValid [] program.signatures.resolutionRules goal (evidence selected) := by
    intro selected validated
    have checked : SourceCompilationPlan.validateRuntimeEvidenceSelection program.signatures caller.key 0 [goal] [selected] = .ok () := by
      split at validated <;> try contradiction
      split at validated
      · simp only [SourceCompilationPlan.validateRuntimeEvidenceSelection, *, if_true]; rfl
      · cases selected; cases validated
    have valid := CallableAuthenticatedCallEvidence.selection_valid checked
    cases valid with
    | cons head tail => exact head
  simp only [SourceCompilationPlan.exactRuntimeRequirementEvidence, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  obtain ⟨row, _, accepted⟩ := bind_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  cases retained : row.evidence with
  | implementation chosen =>
    simp only [retained] at accepted
    obtain ⟨_, validated, accepted⟩ := bind_ok accepted
    cases accepted
    exact finish _ validated
  | assumption predicate =>
    simp only [retained] at accepted
    split at accepted <;> try contradiction
    obtain ⟨_, validated, accepted⟩ := bind_ok accepted
    cases accepted
    exact finish _ validated

private theorem validated_requirements {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available returned : Dictionary} {ids : List RequirementId} {goals : List ProgramPredicate}
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidenceList program caller node available ids goals = .ok returned) :
    Forall₂ (fun goal raw => EvidenceValid [] program.signatures.resolutionRules goal (evidence raw)) goals returned := by
  induction ids generalizing goals returned with
  | nil => cases goals <;> cases accepted; exact .nil
  | cons id ids ih =>
    cases goals with
    | nil => cases accepted
    | cons goal goals =>
      unfold SourceCompilationPlan.exactRuntimeRequirementEvidenceList at accepted
      obtain ⟨head, headAccepted, accepted⟩ := bind_ok accepted
      obtain ⟨tail, tailAccepted, accepted⟩ := bind_ok accepted
      cases accepted
      exact .cons (validated_requirement headAccepted) (ih tailAccepted)

/-- The actual selector fixes each complete evidence tree and its ordered
requirement position. The trait arity and method name remain explicit. -/
structure Roots (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : Dictionary) (primaryId : RequirementId)
    (methodIds : List RequirementId) (arity : Nat) (name : String)
    (method : ExecutableImplMethods.CheckedMethod) where
  primary : RawEvidence
  methodEvidence : Dictionary
  primarySelected : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available
    primaryId (SourceCompilationPlan.runtimeEvidenceGoal primary) = .ok primary
  methodsSelected : SourceCompilationPlan.exactRuntimeRequirementEvidenceList program caller node available
    methodIds (methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal) = .ok methodEvidence
  checked : ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary methodEvidence arity name = .ok method
  shape : ∃ goal implementation, primary = .byImpl goal implementation method.implementationPremises
  methods : method.methodPremises = methodEvidence
  primaryValid : EvidenceValid [] program.signatures.resolutionRules (SourceCompilationPlan.runtimeEvidenceGoal primary) (evidence primary)
  methodsValid : Forall₂ (fun goal raw => EvidenceValid [] program.signatures.resolutionRules goal (evidence raw))
    (methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal) methodEvidence

/-- One common constructor consumes the actual primary and method selections;
neither validity nor the returned evidence is inferred from a specialization key. -/
def Roots.of_selected {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : Dictionary} {primaryId : RequirementId}
    {methodIds : List RequirementId} {arity : Nat} {name : String}
    {method : ExecutableImplMethods.CheckedMethod} {goal : ProgramPredicate}
    {goals : List ProgramPredicate} {primary : RawEvidence} {methodEvidence : Dictionary}
    (primarySelected : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available
      primaryId goal = .ok primary)
    (methodsSelected : SourceCompilationPlan.exactRuntimeRequirementEvidenceList program caller node available
      methodIds goals = .ok methodEvidence)
    (checked : ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary methodEvidence arity name = .ok method) :
    Roots program caller node available primaryId methodIds arity name method := {
  primary := primary
  methodEvidence := methodEvidence
  primarySelected := by
    have same := SourceCompilationPlan.exactRuntimeRequirementEvidence_success_goal _ _ _ _ _ _ _ primarySelected
    rwa [same]
  methodsSelected := by
    have same := SourceCompilationPlan.exactRuntimeRequirementEvidenceList_success_matches _ _ _ _ _ _ _ methodsSelected
    change methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal = _ at same
    rwa [same]
  checked := checked
  shape := by
    obtain ⟨goal, implementation, shape, _⟩ := method_fields checked
    exact ⟨goal, implementation, shape⟩
  methods := by
    obtain ⟨_, _, _, methods⟩ := method_fields checked
    exact methods
  primaryValid := by
    have same := SourceCompilationPlan.exactRuntimeRequirementEvidence_success_goal _ _ _ _ _ _ _ primarySelected
    rw [same]
    exact validated_requirement primarySelected
  methodsValid := by
    have same := SourceCompilationPlan.exactRuntimeRequirementEvidenceList_success_matches _ _ _ _ _ _ _ methodsSelected
    change methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal = _ at same
    rw [same]
    exact validated_requirements methodsSelected
}

/-- Exact roots of the returned method dictionary, taken from the real
selector. All validity facts concern complete evidence trees. -/
structure Certificate (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : Dictionary) (step : CoercionStep)
    (method : ExecutableImplMethods.CheckedMethod) where
  primary : RawEvidence
  methodEvidence : Dictionary
  primarySelected : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available
    step.requirement (SourceCompilationPlan.runtimeEvidenceGoal primary) = .ok primary
  methodsSelected : SourceCompilationPlan.exactRuntimeRequirementEvidenceList program caller node available
    step.methodRequirements (methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal) = .ok methodEvidence
  checked : ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary methodEvidence 2 "coerce" = .ok method
  shape : ∃ goal implementation, primary = .byImpl goal implementation method.implementationPremises
  methods : method.methodPremises = methodEvidence
  primaryValid : EvidenceValid [] program.signatures.resolutionRules (SourceCompilationPlan.runtimeEvidenceGoal primary) (evidence primary)
  methodsValid : Forall₂ (fun goal raw => EvidenceValid [] program.signatures.resolutionRules goal (evidence raw))
    (methodEvidence.map SourceCompilationPlan.runtimeEvidenceGoal) methodEvidence

def Certificate.roots {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : Dictionary} {step : CoercionStep}
    {method : ExecutableImplMethods.CheckedMethod}
    (receipt : Certificate program caller node available step method) :
    Roots program caller node available step.requirement step.methodRequirements 2 "coerce" method :=
  ⟨receipt.primary, receipt.methodEvidence, receipt.primarySelected, receipt.methodsSelected,
    receipt.checked, receipt.shape, receipt.methods, receipt.primaryValid, receipt.methodsValid⟩

/-- No separate premise is required for an intermediate method selection. -/
theorem of_accepted {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : Dictionary} {step : CoercionStep}
    {method : ExecutableImplMethods.CheckedMethod}
    (accepted : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method) :
    Nonempty (Certificate program caller node available step method) := by
  simp only [SourceCompilationPlan.checkedCoercionMethod, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  obtain ⟨row, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, accepted⟩ := require_ok accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  obtain ⟨_, accepted⟩ := require_ok accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  obtain ⟨primary, primarySelected, accepted⟩ := bind_ok accepted
  obtain ⟨methodEvidence, methodsSelected, accepted⟩ := bind_ok accepted
  have checked := mapError_ok accepted
  let roots := Roots.of_selected primarySelected methodsSelected checked
  exact ⟨⟨roots.primary, roots.methodEvidence, roots.primarySelected, roots.methodsSelected,
    roots.checked, roots.shape, roots.methods, roots.primaryValid, roots.methodsValid⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodCertificates
