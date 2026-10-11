import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedRangeReceipts
import Solcore.Frontend.SourceSpecializationAcceptance

/-!
Genuine reached declaration metadata supplies nominal catalog membership and
arity. Actual specialization acceptance supplies concrete replacements. These
two receipts together form the complete canonical raw range at the catalog,
even when the original use-site admits flexible variables or rigid parameters.

This concerns the matched reached callee. An enclosing selected sidecar still
needs its own original occurrence or seed provenance for replacement formation.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedConcreteRangeReceipts
open Frontend SourceInference TypeSystem

private theorem empty_orElse {α : Type} (left right : Option α)
    (empty : left.orElse (fun _ => right) = none) :
    left = none ∧ right = none := by
  cases left with
  | none => exact ⟨rfl, empty⟩
  | some value => cases empty

private theorem applyMany_concrete (head : Ty) (arguments : List Ty)
    (concrete : SourceSpecialization.firstNonConcrete (Ty.applyMany head arguments) = none) :
    SourceSpecialization.firstNonConcrete head = none ∧
      ∀ argument ∈ arguments, SourceSpecialization.firstNonConcrete argument = none := by
  induction arguments generalizing head with
  | nil => exact ⟨concrete, by simp⟩
  | cons argument rest ih =>
      change SourceSpecialization.firstNonConcrete
        (Ty.applyMany (.application head argument) rest) = none at concrete
      have tail := ih (.application head argument) concrete
      have parts := empty_orElse (SourceSpecialization.firstNonConcrete head)
        (SourceSpecialization.firstNonConcrete argument) tail.1
      refine ⟨parts.1, ?_⟩
      intro type member
      rcases List.mem_cons.mp member with same | member
      · subst type; exact parts.2
      · exact tail.2 type member

private theorem scoped_concrete_at_catalog
    {context : Context} {variables : List TypeVarId} {type : Ty}
    (typing : TypeWellScoped context variables type) :
    SourceSpecialization.firstNonConcrete type = none →
      TypeWellScoped (Context.ofSignatures context.signatures) [] type := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => SourceSpecialization.firstNonConcrete type = none →
      TypeWellScoped (Context.ofSignatures context.signatures) [] type)
    (motive_2 := fun types _ =>
      (∀ type ∈ types, SourceSpecialization.firstNonConcrete type = none) →
        TypesWellScoped (Context.ofSignatures context.signatures) [] types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  · intro metavariable _ concrete
    cases concrete
  · intro parameter _ _ concrete
    cases concrete
  · intro builtin _concrete
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsIH concrete
    exact .nominal dataType arguments cataloged arity
      (argumentsIH (applyMany_concrete (.constructor (.declaration dataType.id))
        arguments concrete).2)
  · intro contract arguments cataloged arity _ argumentsIH concrete
    exact .contractNominal contract arguments cataloged arity
      (argumentsIH (applyMany_concrete (.constructor (.declaration contract.id))
        arguments concrete).2)
  · intro parameter result _ _ parameterIH resultIH concrete
    have parts := empty_orElse (SourceSpecialization.firstNonConcrete parameter)
      (SourceSpecialization.firstNonConcrete result) concrete
    exact .function (parameterIH parts.1) (resultIH parts.2)
  · intro left right _ _ leftIH rightIH concrete
    have parts := empty_orElse (SourceSpecialization.firstNonConcrete left)
      (SourceSpecialization.firstNonConcrete right) concrete
    exact .product (leftIH parts.1) (rightIH parts.2)
  · intro key value _ _ keyIH valueIH concrete
    have parts := empty_orElse (SourceSpecialization.firstNonConcrete key)
      (SourceSpecialization.firstNonConcrete value) concrete
    exact .mapping (keyIH parts.1) (valueIH parts.2)
  · intro inner _ innerIH concrete
    exact .proxy (innerIH concrete)
  · intro inner _ innerIH concrete
    exact .comptime (innerIH concrete)
  · intro _concrete
    exact .nil
  · intro head tail _ _ headIH tailIH concrete
    exact .cons (headIH (concrete head (List.mem_cons_self)))
      (tailIH (fun type member => concrete type (List.mem_cons_of_mem head member)))

/-- Concrete metadata retains all genuine nominal membership and arity while
discarding flexible and rigid binders which the actual concrete check excludes. -/
theorem admissible_concrete_at_catalog {context : Context} {type : Ty}
    (admissible : TypeAdmissible context type)
    (concrete : SourceSpecialization.firstNonConcrete type = none) :
    TypeWellFormed (Context.ofSignatures context.signatures) type :=
  ⟨TypeParameterBindersWellFormed.ofSignatures context.signatures,
    scoped_concrete_at_catalog admissible.typeWellScoped concrete⟩

private theorem exact_binding_entry
    {substitution : TypeSystem.ParameterSubstitution}
    {parameter : TypeParameterId} {type : Ty}
    (found : SourceCompilationPlan.exactParameterBinding? substitution parameter = some type) :
    (parameter, type) ∈ substitution ∧ substitution.lookup? parameter = some type := by
  induction substitution with
  | nil => simp [SourceCompilationPlan.exactParameterBinding?] at found
  | cons entry rest ih =>
      rcases entry with ⟨candidate, replacement⟩
      by_cases same : candidate = parameter
      · subst candidate
        cases filtered : rest.filter (fun item => item.1 == parameter) with
        | nil =>
            have typeEq : replacement = type := by
              simpa [SourceCompilationPlan.exactParameterBinding?, filtered] using found
            subst type
            exact ⟨List.mem_cons_self, by simp [TypeSystem.ParameterSubstitution.lookup?]⟩
        | cons head tail =>
            simp [SourceCompilationPlan.exactParameterBinding?, filtered] at found
      · have tailFound : SourceCompilationPlan.exactParameterBinding? rest parameter = some type := by
          simpa [SourceCompilationPlan.exactParameterBinding?, same] using found
        obtain ⟨member, lookup⟩ := ih tailFound
        exact ⟨List.mem_cons_of_mem _ member, by
          simpa [TypeSystem.ParameterSubstitution.lookup?, same] using lookup⟩

/-- Actual matching transfers admissible source replacements. The genuine
specializer then closes precisely those canonical rows, including unused ones. -/
theorem range_of_admissible_match
    {context : Context} {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    {instantiation : DeclarationInstantiation}
    (matched : CallableNamedMetadata.Matches specialized instantiation)
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures context.signatures) specialized.parameterSubstitution := by
  have equivalent := matched.substitution
  simp only [SourceCompilationPlan.parameterSubstitutionsEquivalent, Bool.and_eq_true,
    List.all_eq_true, beq_iff_eq] at equivalent
  cases admissible with
  | intro sourceSignature cataloged declaration exact range typeEq predicatesEq parameterFlags returnFlag =>
      intro parameter type member
      have rightFound := equivalent.1.2 (parameter, type) member
      have rightMember := (exact_binding_entry rightFound).1
      have leftFound := equivalent.2 (parameter, type) rightMember
      have lookup := (exact_binding_entry leftFound).2
      exact admissible_concrete_at_catalog (range parameter type rightMember)
        (SourceSpecializationAcceptance.specializeFunction_parameterReplacement_concrete
          accepted parameter type lookup)

/-- A real compiler selection and exact plan record supply the matcher for a
genuinely typed declaration occurrence. No use-site binder emptiness is needed. -/
theorem catalog_range_of_selected
    {context : Context} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {calleeSignature : SourceCoreCalls.Signature}
    {specialized : SourceSpecialization.SpecializedFunction}
    {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution}
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (selected : SourceCoreFunctions.selectedSignature policy compilation source node
      instantiation isReference = .ok (index, calleeSignature))
    (record : SourceCompilationPlan.exactSpecialization compilation.plan calleeSignature.key = .ok specialized)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures context.signatures) specialized.parameterSubstitution :=
  range_of_admissible_match
    (CallableNamedMetadata.matches_of_exact (NamedCalls.selected_signature_target selected).1 record)
    admissible accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedConcreteRangeReceipts
