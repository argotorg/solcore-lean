import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceCompilation

/-! The checked local-instance factory fixes the complete candidate and the
source substitution. Its read parent remains the actual authenticated parent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaEmissionFacts
open Core Frontend SourceInference SourceCoreLocalPolymorphism

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem exactCaller_source {plan : SourceSpecializationWorklist.Plan} {binding : Binding}
    {caller : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCoreLocalEvidence.exactCaller plan binding = .ok caller) :
    caller.function.typedBody = binding.source := by
  unfold SourceCoreLocalEvidence.exactCaller at accepted
  obtain ⟨actual, _selected, accepted⟩ := bind_ok accepted
  try dsimp only at accepted
  split at accepted
  · cases accepted
  · next same =>
    try dsimp only at accepted
    split at accepted
    · cases accepted
      exact Classical.byContradiction same
    · cases accepted

/-- The one successful factory result retains the full candidate key and the
source graph selected by that same checked caller. -/
theorem prepare_facts {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared) :
    prepared.instance = candidate ∧
      prepared.substitution = candidate.origin.substitution ∧
      prepared.source = candidate.origin.source.applySubstitution candidate.origin.substitution := by
  unfold SourceCoreLocalEvidence.prepare at accepted
  obtain ⟨caller, selected, accepted⟩ := bind_ok accepted
  have source := exactCaller_source selected
  try dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨_discovered, _discovery, accepted⟩ := bind_ok accepted
    try dsimp only at accepted
    split at accepted
    · try dsimp only at accepted
      obtain ⟨⟨_active, _inherited⟩, _context, accepted⟩ := bind_ok accepted
      try dsimp only at accepted
      split at accepted
      · dsimp only [pure, Except.pure, bind, Except.bind] at accepted
        obtain ⟨_reference, _authenticated, accepted⟩ := bind_ok accepted
        try dsimp only at accepted
        split at accepted
        · cases accepted
        · try dsimp only at accepted
          obtain ⟨_checked, _validated, accepted⟩ := bind_ok accepted
          cases accepted
          exact ⟨rfl, rfl, congrArg (fun value => value.applySubstitution candidate.origin.substitution) source⟩
      · cases accepted
    · cases accepted

theorem Emission.instance {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    (emission : SourceCoreLocalEvidence.Emission program plan candidate parent) :
    emission.prepared.instance = candidate :=
  (prepare_facts emission.authentic).1

theorem Emission.substitution {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    (emission : SourceCoreLocalEvidence.Emission program plan candidate parent) :
    emission.prepared.substitution = candidate.origin.substitution :=
  (prepare_facts emission.authentic).2.1

theorem Emission.source {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    (emission : SourceCoreLocalEvidence.Emission program plan candidate parent) :
    emission.prepared.source = candidate.origin.source.applySubstitution candidate.origin.substitution :=
  (prepare_facts emission.authentic).2.2

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaEmissionFacts
