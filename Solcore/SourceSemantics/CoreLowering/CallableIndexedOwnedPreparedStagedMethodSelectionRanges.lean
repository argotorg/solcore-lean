import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodInstantiation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedNamedConcreteRangeReceipts

/-! Actual implementation-head matching recovers every ordered replacement
from an admitted goal. Concrete specialization then closes its raw catalog type. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionRanges
open Frontend TypeSystem

private def applicationArguments : Ty → List Ty
  | .application head argument => applicationArguments head ++ [argument]
  | _ => []

private theorem arguments_applyMany (head : Ty) (arguments : List Ty) :
    applicationArguments (Ty.applyMany head arguments) = applicationArguments head ++ arguments := by
  induction arguments generalizing head with
  | nil => simp [Ty.applyMany]
  | cons argument rest ih =>
    change applicationArguments (Ty.applyMany (.application head argument) rest) = _
    rw [ih]
    simp [applicationArguments, List.append_assoc]

private theorem arguments_nominal (declaration : Resolved.DeclarationId) (arguments : List Ty) :
    applicationArguments (Ty.nominal declaration arguments) = arguments := by
  simp [Ty.nominal, arguments_applyMany, applicationArguments]

private theorem scoped_arguments {context : Context} {variables : List TypeVarId} {type : Ty}
    (typed : TypeWellScoped context variables type) :
    ∀ argument ∈ applicationArguments type, TypeWellScoped context variables argument := by
  cases typed with
  | nominal declaration arguments member arity typed
  | contractNominal declaration arguments member arity typed =>
    rw [arguments_nominal]
    intro argument member
    exact typed.member member
  | _ => simp [applicationArguments]

private def applicationHead : Ty → Ty
  | .application head _ => applicationHead head
  | other => other

private theorem head_applyMany (head : Ty) (arguments : List Ty) :
    applicationHead (Ty.applyMany head arguments) = applicationHead head := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument rest ih => exact ih (.application head argument)

private theorem nominal_ne_proxy (declaration : Resolved.DeclarationId) (arguments : List Ty) (inner : Ty) :
    Ty.nominal declaration arguments ≠ .proxy inner := by
  intro same
  have heads := congrArg applicationHead same
  simp [Ty.nominal, head_applyMany, applicationHead] at heads

private theorem nominal_ne_comptime (declaration : Resolved.DeclarationId) (arguments : List Ty) (inner : Ty) :
    Ty.nominal declaration arguments ≠ .comptime inner := by
  intro same
  have heads := congrArg applicationHead same
  simp [Ty.nominal, head_applyMany, applicationHead] at heads

private theorem scoped_proxy {context : Context} {variables : List TypeVarId} {type : Ty}
    (typed : TypeWellScoped context variables type) :
    ∀ inner, type = .proxy inner → TypeWellScoped context variables inner := by
  cases typed with
  | nominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_proxy declaration.id arguments inner same)
  | contractNominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_proxy declaration.id arguments inner same)
  | proxy inner => intro _ same; cases same; exact inner
  | _ => intro _ same; cases same

private theorem scoped_comptime {context : Context} {variables : List TypeVarId} {type : Ty}
    (typed : TypeWellScoped context variables type) :
    ∀ inner, type = .comptime inner → TypeWellScoped context variables inner := by
  cases typed with
  | nominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_comptime declaration.id arguments inner same)
  | contractNominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_comptime declaration.id arguments inner same)
  | comptime inner => intro _ same; cases same; exact inner
  | _ => intro _ same; cases same

private theorem occurs_applyMany (parameter : TypeParameterId) (head : Ty) (arguments : List Ty) :
    TypeParameterOccurs parameter (Ty.applyMany head arguments) ↔
      TypeParameterOccurs parameter head ∨ ∃ argument ∈ arguments, TypeParameterOccurs parameter argument := by
  induction arguments generalizing head with
  | nil => simp [Ty.applyMany]
  | cons argument rest ih =>
    change TypeParameterOccurs parameter (Ty.applyMany (.application head argument) rest) ↔ _
    rw [ih]
    simp only [TypeSystem.TypeParameterOccurs, List.mem_cons, exists_eq_or_imp, or_assoc]

private theorem occurs_nominal {parameter : TypeParameterId} {declaration : Resolved.DeclarationId} {arguments : List Ty}
    (occurs : TypeParameterOccurs parameter (Ty.nominal declaration arguments)) :
    ∃ argument ∈ arguments, TypeParameterOccurs parameter argument := by
  rcases (occurs_applyMany parameter (.constructor (.declaration declaration)) arguments).mp occurs with impossible | found
  · cases impossible
  · exact found

/-- The original well-scoped head prevents parameters from appearing in an
ill-formed nominal head with missing arguments. Each genuine occurrence recovers its replacement. -/
private theorem scoped_at_occurrence {original target : Context} {originalVariables variables : List TypeVarId}
    (substitution : TypeSystem.ParameterSubstitution) {type : Ty}
    (originalTyped : TypeWellScoped original originalVariables type) :
    ∀ parameter, TypeParameterOccurs parameter type →
      TypeWellScoped target variables (substitution.apply type) →
      TypeWellScoped target variables ((substitution.lookup? parameter).getD (.parameter parameter)) := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => ∀ parameter, TypeParameterOccurs parameter type →
      TypeWellScoped target variables (substitution.apply type) →
      TypeWellScoped target variables ((substitution.lookup? parameter).getD (.parameter parameter)))
    (motive_2 := fun types _ => ∀ type ∈ types, ∀ parameter, TypeParameterOccurs parameter type →
      TypeWellScoped target variables (substitution.apply type) →
      TypeWellScoped target variables ((substitution.lookup? parameter).getD (.parameter parameter)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ originalTyped
  · intro metavariable bound parameter occurs; cases occurs
  · intro actual bound owned parameter occurs typed
    cases occurs
    exact typed
  · intro builtin parameter occurs; cases occurs
  · intro declaration arguments cataloged arity originalTyped ih parameter occurs typed
    obtain ⟨argument, member, occurs⟩ := occurs_nominal occurs
    apply ih argument member parameter occurs
    rw [StructuralSubstitution.apply_nominal] at typed
    exact scoped_arguments typed _ (by rw [arguments_nominal]; exact List.mem_map.mpr ⟨argument, member, rfl⟩)
  · intro declaration arguments cataloged arity originalTyped ih parameter occurs typed
    obtain ⟨argument, member, occurs⟩ := occurs_nominal occurs
    apply ih argument member parameter occurs
    rw [StructuralSubstitution.apply_nominal] at typed
    exact scoped_arguments typed _ (by rw [arguments_nominal]; exact List.mem_map.mpr ⟨argument, member, rfl⟩)
  · intro left right first second leftIH rightIH parameter occurs typed
    rcases occurs with occurs | occurs
    · exact leftIH parameter occurs (typed.function_components _ _ rfl).1
    · exact rightIH parameter occurs (typed.function_components _ _ rfl).2
  · intro left right first second leftIH rightIH parameter occurs typed
    rcases occurs with occurs | occurs
    · exact leftIH parameter occurs (typed.product_components _ _ rfl).1
    · exact rightIH parameter occurs (typed.product_components _ _ rfl).2
  · intro left right first second leftIH rightIH parameter occurs typed
    rcases occurs with occurs | occurs
    · exact leftIH parameter occurs (typed.mapping_components _ _ rfl).1
    · exact rightIH parameter occurs (typed.mapping_components _ _ rfl).2
  · intro inner originalTyped ih parameter occurs typed
    exact ih parameter occurs (scoped_proxy typed _ rfl)
  · intro inner originalTyped ih parameter occurs typed
    exact ih parameter occurs (scoped_comptime typed _ rfl)
  · intro type member; cases member
  · intro head tail headTyped tailTyped headIH tailIH type member
    rcases List.mem_cons.mp member with rfl | member
    · exact headIH
    · exact tailIH type member

private theorem admissible_at_occurrence
    {original context : Context} {originalVariables : List TypeVarId}
    (substitution : TypeSystem.ParameterSubstitution) {type : Ty} {parameter : TypeParameterId}
    (originalTyped : TypeWellScoped original originalVariables type)
    (occurs : TypeParameterOccurs parameter type)
    (admitted : TypeAdmissible context (substitution.apply type)) :
    TypeAdmissible context ((substitution.lookup? parameter).getD (.parameter parameter)) := by
  have replacementScoped := scoped_at_occurrence substitution originalTyped parameter occurs admitted.typeWellScoped
  cases residual : context.residualTypeVariables with
  | false =>
    exact ⟨admitted.binders, by simpa [admissibleTypeVariables, residual] using replacementScoped⟩
  | true =>
    exact StructuralSubstitution.TypeWellScoped.toAdmissibleOfResidual admitted.binders residual replacementScoped

/-- Every original implementation parameter occurs in its well-formed head.
The genuine selected head equation identifies the admitted replacement, and
actual specialization acceptance supplies its full concrete check. -/
theorem of_selected
    {program : CheckedProgram} {primary : TypedTraitResolution.Evidence}
    {name : String} {method : ExecutableImplMethods.CheckedMethod}
    (selected : CallableCoercionMethodInstantiation.Selection program primary name method)
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (formed : CallableCoercionMethodInstantiation.Formation selected.implementation selected.declaration)
    {context : Context} (signatures : context.signatures = program.signatures)
    (admitted : PredicateAdmissible context selected.goal) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) method.specialized.parameterSubstitution := by
  let substitution := method.specialized.parameterSubstitution
  have original := wellFormed.signatures.implementations_semantic selected.implementation selected.implementationMember
  have determined := selected.determines formed
  have headEq := determined.2.2
  rw [← headEq] at admitted
  intro parameter replacement member
  have parameterMember : parameter ∈ selected.implementation.parameters := by
    rw [← selected.domain]
    exact List.mem_map.mpr ⟨(parameter, replacement), member, rfl⟩
  have lookup := StructuralSubstitution.ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup
    (selected.exact_substitution formed.parameters).domain_nodup member
  have replacementAdmitted : TypeAdmissible context replacement := by
    rcases original.parameters_in_head parameter parameterMember with occurs | ⟨argument, argumentMember, occurs⟩
    · have recovered := admissible_at_occurrence substitution original.head.subject.typeWellScoped occurs admitted.subject
      simpa only [substitution, lookup, Option.getD_some] using recovered
    · have argumentAdmitted : TypeAdmissible context (substitution.apply argument) :=
        admitted.arguments _ (List.mem_map.mpr ⟨argument, argumentMember, rfl⟩)
      have recovered := admissible_at_occurrence substitution
        (original.head.arguments argument argumentMember).typeWellScoped occurs argumentAdmitted
      simpa only [substitution, lookup, Option.getD_some] using recovered
  have concrete := SourceSpecializationAcceptance.specializeFunction_parameterReplacement_concrete
    selected.specialized parameter replacement lookup
  have closed := CallableIndexedOwnedReachedNamedConcreteRangeReceipts.admissible_concrete_at_catalog
    replacementAdmitted concrete
  simpa only [signatures] using closed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionRanges
