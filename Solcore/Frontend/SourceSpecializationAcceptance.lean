import Solcore.Frontend.SourceSpecialization
import Solcore.TypeSystem.SubstitutionProperties

/-!
Successful source specialization retains concrete rigid replacements.  This
proof inverts the genuine public specializeFunction receipt and consumes the
range theorem proved beside its actual canonicalSubstitution checker.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceSpecializationAcceptance

open SourceInference SourceSpecialization TypeSystem

private theorem empty_orElse {α : Type} (left right : Option α)
    (empty : left.orElse (fun _ => right) = none) :
    left = none ∧ right = none := by
  cases left with
  | none => exact ⟨rfl, empty⟩
  | some value => cases empty

private theorem concrete_flexible_closed (type : Ty)
    (accepted : firstNonConcrete type = none) :
    type.freeVariables = [] := by
  revert accepted
  induction type with
  | «variable» metavariable => intro accepted; cases accepted
  | parameter parameter => intro accepted; cases accepted
  | constructor constructorId => intro _accepted; rfl
  | application left right leftIH rightIH
  | function left right leftIH rightIH
  | product left right leftIH rightIH
  | mapping left right leftIH rightIH =>
      intro accepted
      have parts := empty_orElse (firstNonConcrete left)
        (firstNonConcrete right) accepted
      simp only [Ty.freeVariables, leftIH parts.1, rightIH parts.2]
      rfl
  | proxy inner innerIH
  | comptime inner innerIH =>
      intro accepted
      exact innerIH accepted
  | error => intro accepted; cases accepted

private theorem bind_ok {α β : Type}
    {computation : Except SourceSpecialization.Error α}
    {next : α → Except SourceSpecialization.Error β}
    {result : β} (accepted : computation.bind next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computed : computation with
  | error error => simp [computed, Except.bind] at accepted
  | ok value =>
      exact ⟨value, rfl, by
        simpa only [computed, Except.bind] using accepted⟩

/-- The actual public specialization receipt implies that every retained rigid
replacement passes the original concrete-type check. -/
theorem specializeFunction_parameterReplacement_concrete
    {signature : ProgramFunctionSignature} {function : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SpecializedFunction}
    (accepted : specializeFunction signature function supplied = .ok specialized)
    (parameter : TypeParameterId) (replacement : Ty)
    (found : specialized.parameterSubstitution.lookup? parameter =
      some replacement) :
    firstNonConcrete replacement = none := by
  unfold specializeFunction at accepted
  by_cases guard0 : (signature.id != function.declaration) = true
  · simp only [guard0] at accepted
    cases accepted
  · simp only [guard0] at accepted
    by_cases guard1 : (function.typedBody.owner != function.declaration) = true
    · simp only [guard1] at accepted
      cases accepted
    · simp only [guard1] at accepted
      by_cases guard2 : (signature.scheme.body != function.type) = true
      · simp only [guard2] at accepted
        cases accepted
      · simp only [guard2] at accepted
        by_cases guard3 : (signature.parameterComptime !=
            function.typedBody.inputs.map (·.comptime)) = true
        · simp only [guard3] at accepted
          cases accepted
        · simp only [guard3] at accepted
          by_cases guard4 : (signature.returnComptime != function.returnComptime) = true
          · simp only [guard4] at accepted
            cases accepted
          · simp only [guard4] at accepted
            obtain ⟨check0, _, accepted⟩ := bind_ok accepted
            cases check0
            obtain ⟨check1, _, accepted⟩ := bind_ok accepted
            cases check1
            obtain ⟨check2, _, accepted⟩ := bind_ok accepted
            cases check2
            obtain ⟨check3, _, accepted⟩ := bind_ok accepted
            cases check3
            obtain ⟨canonical, selected, accepted⟩ := bind_ok accepted
            obtain ⟨after0, _, accepted⟩ := bind_ok accepted
            obtain ⟨after1, _, accepted⟩ := bind_ok accepted
            obtain ⟨after2, _, accepted⟩ := bind_ok accepted
            obtain ⟨after3, _, accepted⟩ := bind_ok accepted
            cases analysis : SourceStageAnalysis.analyzeFunction
                (applyCheckedFunction canonical function) with
            | error error =>
                simp only [analysis] at accepted
                cases accepted
            | ok stages =>
                simp only [analysis, pure, Except.pure, bind, Except.bind,
                  Except.ok.injEq] at accepted
                subst specialized
                exact SourceSpecialization.canonicalSubstitution_concrete_replacements selected
                  (parameter, replacement)
                  (ParameterSubstitution.lookup?_eq_some_mem found)

/-- Thus local flexible substitutions cannot change a replacement accepted by
the genuine rigid specialization action. -/
theorem specializeFunction_parameterReplacement_flexibleClosed
    {signature : ProgramFunctionSignature} {function : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SpecializedFunction}
    (accepted : specializeFunction signature function supplied = .ok specialized)
    (parameter : TypeParameterId) (replacement : Ty)
    (found : specialized.parameterSubstitution.lookup? parameter =
      some replacement) :
    replacement.freeVariables = [] := by
  exact concrete_flexible_closed replacement
    (specializeFunction_parameterReplacement_concrete accepted parameter
      replacement found)

end Solcore.Frontend.SourceSpecializationAcceptance
