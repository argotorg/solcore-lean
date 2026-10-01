import Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata

/-! Reversing the ordered parameter ledger preserves the real instantiation
selector while changing the independently retained source metadata. Equality of
source values is transported by an explicit involution, never by identifying
parameter lists that only denote the same mapping. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableNamedReversal
open Frontend SourceInference TypeSystem

/-- Only the parameter ledger order changes; source header and evidence are
left intact. -/
def instantiation (source : DeclarationInstantiation) : DeclarationInstantiation :=
  {source with parameterSubstitution := source.parameterSubstitution.reverse}

@[simp] theorem instantiation_twice (source : DeclarationInstantiation) :
    instantiation (instantiation source) = source := by
  cases source; simp [instantiation]

private theorem exact_binding_reverse (source : ParameterSubstitution) (parameter : TypeParameterId) :
    SourceCompilationPlan.exactParameterBinding? source.reverse parameter =
      SourceCompilationPlan.exactParameterBinding? source parameter := by
  unfold SourceCompilationPlan.exactParameterBinding?
  rw [List.filter_reverse]
  generalize source.filter (fun entry => entry.1 == parameter) = entries
  cases entries with
  | nil => rfl
  | cons head rest =>
    cases rest with
    | nil => rfl
    | cons second remaining =>
      cases reversed : (head :: second :: remaining).reverse with
      | nil => rfl
      | cons first tail =>
        cases tail with
        | nil =>
          have length := congrArg List.length reversed
          simp only [List.length_reverse, List.length_cons, List.length_nil] at length
          omega
        | cons next after => rfl

/-- The matcher looks up each key exactly once and compares all entries. Its
right ledger traversal order does not alter the accepted mapping. -/
theorem substitutions_reverse_right (left right : ParameterSubstitution) :
    SourceCompilationPlan.parameterSubstitutionsEquivalent left right.reverse =
      SourceCompilationPlan.parameterSubstitutionsEquivalent left right := by
  simp only [SourceCompilationPlan.parameterSubstitutionsEquivalent, List.length_reverse,
    exact_binding_reverse, List.all_reverse]

/-- The actual compiler checks every other declaration field unchanged. -/
theorem matcher_reverse (specialized : SourceSpecialization.SpecializedFunction) (source : DeclarationInstantiation) :
    SourceCompilationPlan.specializationMatchesInstantiation specialized (instantiation source) =
      SourceCompilationPlan.specializationMatchesInstantiation specialized source := by
  simp only [SourceCompilationPlan.specializationMatchesInstantiation, instantiation, substitutions_reverse_right]

/-- Even missing/duplicate-target errors are unchanged by ledger reversal. -/
theorem target_reverse (plan : SourceCompilationPlan.Plan) (source : DeclarationInstantiation) :
    SourceCompilationPlan.exactInstantiationKey plan (instantiation source) =
      SourceCompilationPlan.exactInstantiationKey plan source := by
  simp only [SourceCompilationPlan.exactInstantiationKey, SourceCompilationPlan.specializationMatchesInstantiation,
    instantiation, substitutions_reverse_right]

def global (source : Dynamic.GlobalFunction) : Dynamic.GlobalFunction :=
  {source with instantiation := instantiation source.instantiation}

@[simp] theorem global_twice (source : Dynamic.GlobalFunction) : global (global source) = source := by
  cases source; simp [global]

def value : Dynamic.Value → Dynamic.Value
  | .global function => .global (global function)
  | other => other

@[simp] theorem value_twice (source : Dynamic.Value) : value (value source) = source := by
  cases source <;> simp [value]

theorem value_injective : Function.Injective value := by
  intro left right same
  have inverted := congrArg value same
  simpa only [value_twice] using inverted

/-- Evidence order and tree identity are preserved independently of the
parameter ledger permutation. -/
@[simp] theorem global_evidence (source : Dynamic.GlobalFunction) : (global source).evidence = source.evidence := rfl

@[simp] theorem global_type (source : Dynamic.GlobalFunction) : (global source).instantiation.type = source.instantiation.type := rfl

end Solcore.SourceSemantics.CoreLowering.CallableNamedReversal
