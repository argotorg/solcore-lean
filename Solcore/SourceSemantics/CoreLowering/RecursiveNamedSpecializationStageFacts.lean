import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationBodyFacts
import Solcore.SourceSemantics.SourceStageAnalysisSoundness

/-! The stored specialization analysis is the actual successful stage pass.
Independent graph and local identity properties move from the original body
through structural substitution, so the real specialized body has a source
stage derivation. This is classification, not comptime evaluation correctness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationStageFacts
open Frontend SourceInference TypeSystem

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) : action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

variable {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}

/-- Every field of the actual stage pass result is kept by specialization. -/
theorem analyzed
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    SourceStageAnalysis.analyzeFunction specialized.function = .ok specialized.stageAnalysis := by
  unfold SourceSpecialization.specializeFunction at accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction (SourceSpecialization.applyCheckedFunction canonical generic) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
    simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
    subst specialized
    exact analysis

theorem graph_closed
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (closed : OccurrenceGraphClosed generic.typedBody) :
    OccurrenceGraphClosed specialized.function.typedBody := by
  rw [RecursiveNamedSpecializationBodyFacts.body accepted]
  exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters specialized.parameterSubstitution closed

theorem local_identities
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (owned : LocalIdentityOwnership generic.typedBody) :
    LocalIdentityOwnership specialized.function.typedBody := by
  rw [RecursiveNamedSpecializationBodyFacts.body accepted]
  exact StructuralSubstitution.LocalIdentityOwnership.applyParameters specialized.parameterSubstitution owned

/-- The original independent structural properties and actual stage pass
supply the normative whole-function stage classification. -/
theorem has_stages
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (closed : OccurrenceGraphClosed generic.typedBody)
    (owned : LocalIdentityOwnership generic.typedBody) :
    Staging.FunctionHasStages specialized.function :=
  SourceStageAnalysisSoundness.analyzeFunction_success_hasStages_of_wellFormed
    specialized.function specialized.stageAnalysis (graph_closed accepted closed)
    (local_identities accepted owned) (analyzed accepted)

/-- Independent program body typing supplies the original graph and local
identity properties. The forgeable checked carrier alone does not do so. -/
theorem has_stages_of_program {program : CheckedProgram}
    (programTyped : ProgramWellFormed (Program.ofChecked program))
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    Staging.FunctionHasStages specialized.function := by
  have definition := programTyped.functions_valid (FunctionDefinition.ofChecked generic)
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩)
  cases definition with
  | intro _ _ typed =>
    exact has_stages accepted (StructuralSubstitution.BodyDefinitionHasType.graphClosed typed)
      (StructuralSubstitution.BodyDefinitionHasType.localIdentityOwnership typed)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationStageFacts
