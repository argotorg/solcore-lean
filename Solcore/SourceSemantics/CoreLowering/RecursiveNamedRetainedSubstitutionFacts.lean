import Solcore.SourceSemantics.CoreLowering.CallableNamedCanonicalOrder
import Solcore.SourceSemantics.SubstitutionProperties

/-! Retained declaration substitutions use the reverse of canonical order.
Their records stay distinct; unique keys make their structural actions agree.
Every raw field and recursive evidence row is retained. These are syntax and
instantiation facts, with no execution or authority premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedRetainedSubstitutionFacts
open Frontend SourceInference TypeSystem StructuralSubstitution

/-- First-match lookup is invariant under reversal when every key is unique.
No condition on replacement types or their use is required. -/
theorem lookup_reverse {substitution : TypeSystem.ParameterSubstitution}
    (unique : (SourceSemantics.ParameterSubstitution.domain substitution).Nodup)
    (parameter : TypeParameterId) :
    TypeSystem.ParameterSubstitution.lookup? substitution.reverse parameter = substitution.lookup? parameter := by
  have reversedUnique : (SourceSemantics.ParameterSubstitution.domain substitution.reverse).Nodup := by
    simpa [SourceSemantics.ParameterSubstitution.domain, List.map_reverse] using
      (List.reverse_perm _).nodup_iff.mpr unique
  cases found : substitution.lookup? parameter with
  | none =>
    cases reversed : TypeSystem.ParameterSubstitution.lookup? substitution.reverse parameter with
    | none => rfl
    | some replacement =>
      have member := List.mem_reverse.mp (StructuralSubstitution.ParameterSubstitution.mem_of_lookup?_eq_some reversed)
      have actual := StructuralSubstitution.ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup unique member
      rw [found] at actual
      cases actual
  | some replacement =>
    exact StructuralSubstitution.ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup reversedUnique
      (List.mem_reverse.mpr (StructuralSubstitution.ParameterSubstitution.mem_of_lookup?_eq_some found))

/-- Raw equality uses full lookup values, before any runtime type erasure. -/
theorem apply_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) (type : TypeSystem.Ty) :
    left.apply type = right.apply type := by
  induction type <;> simp_all [TypeSystem.ParameterSubstitution.apply]

private theorem apply_function {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) : left.apply = right.apply :=
  funext (apply_congr same)

private theorem predicate_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    ProgramPredicate.applyParameters left = ProgramPredicate.applyParameters right := by
  funext predicate
  simp only [ProgramPredicate.applyParameters, apply_function same]

private theorem binder_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) : applyBinder left = applyBinder right := by
  have requirements : LocalSchemeRequirement.applyParameters left = LocalSchemeRequirement.applyParameters right := by
    funext requirement
    simp only [LocalSchemeRequirement.applyParameters, predicate_congr same]
  funext binder
  simp only [applyBinder, applyScheme, apply_function same, requirements]

private theorem declaration_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyDeclarationInstantiation left = applyDeclarationInstantiation right := by
  funext instantiation
  simp only [applyDeclarationInstantiation, apply_function same, predicate_congr same]

private theorem constructor_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyDataConstructorInstantiation left = applyDataConstructorInstantiation right := by
  funext instantiation
  simp only [applyDataConstructorInstantiation, apply_function same]

private theorem integer_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyIntegerLiteralResolution left = applyIntegerLiteralResolution right := by
  funext resolution
  simp only [applyIntegerLiteralResolution, apply_function same]

private theorem instruction_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyMatchPatternInstruction left = applyMatchPatternInstruction right := by
  funext instruction
  cases instruction <;> simp only [applyMatchPatternInstruction, integer_congr same, binder_congr same, constructor_congr same]

private theorem pattern_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyMatchPatternResolution left = applyMatchPatternResolution right := by
  funext pattern
  cases pattern <;> simp only [applyMatchPatternResolution, integer_congr same, binder_congr same,
    constructor_congr same, instruction_congr same]

private theorem match_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyMatchResolution left = applyMatchResolution right := by
  have casesEq : applyTypedMatchCase left = applyTypedMatchCase right := by
    funext arm
    simp only [applyTypedMatchCase, applyTypedMatchPattern, pattern_congr same, apply_function same]
  funext resolution
  simp only [applyMatchResolution, casesEq]

private theorem reference_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyReferenceResolution left = applyReferenceResolution right := by
  funext resolution
  cases resolution <;> simp only [applyReferenceResolution, declaration_congr same]

private theorem call_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyCallResolution left = applyCallResolution right := by
  funext resolution
  cases resolution <;> simp only [applyCallResolution, applyIndirectCallResolution, declaration_congr same, apply_function same]

private theorem expression_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyExpressionForm left = applyExpressionForm right := by
  funext form
  cases form <;> simp only [applyExpressionForm, integer_congr same, reference_congr same,
    call_congr same, constructor_congr same, binder_congr same, apply_function same]

private theorem assignment_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyAssignmentResolution left = applyAssignmentResolution right := by
  funext assignment
  simp only [applyAssignmentResolution, applyPlaceResolution, apply_function same]

private theorem forItem_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyForItemForm left = applyForItemForm right := by
  funext item
  cases item <;> simp only [applyForItemForm, binder_congr same, assignment_congr same]

private theorem statement_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyStatementForm left = applyStatementForm right := by
  funext form
  cases form <;> simp only [applyStatementForm, binder_congr same, assignment_congr same,
    match_congr same, forItem_congr same]

private theorem node_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) : applyNode left = applyNode right := by
  have coercions : applyCoercionStep left = applyCoercionStep right := by
    funext step
    simp only [applyCoercionStep, apply_function same]
  funext node
  cases node <;> simp only [applyNode, applyExpressionNode, applyStatementNode, coercions,
    expression_congr same, statement_congr same, apply_function same]

/-- All retained source fields, including nested raw substitution rows, are
mapped in their original order under extensionally equal substitutions. -/
theorem typedSource_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) (source : TypedSource) :
    applyTypedSource left source = applyTypedSource right source := by
  simp only [applyTypedSource, binder_congr same, node_congr same]

mutual
  private theorem evidence_congr {left right : TypeSystem.ParameterSubstitution}
      (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter)
      (evidence : TypedTraitResolution.Evidence) : applyEvidence left evidence = applyEvidence right evidence := by
    cases evidence with
    | byImpl goal implementation premises =>
      simp only [applyEvidence, predicate_congr same, evidences_congr same premises]

  private theorem evidences_congr {left right : TypeSystem.ParameterSubstitution}
      (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter)
      (evidences : List TypedTraitResolution.Evidence) : applyEvidences left evidences = applyEvidences right evidences := by
    cases evidences with
    | nil => rfl
    | cons head tail => simp only [applyEvidences, evidence_congr same head, evidences_congr same tail]
end

/-- Complete recursive evidence is transported; requirement IDs and order
remain exactly those of the original ledger. -/
theorem solvedRequirement_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) (row : SolvedRequirement) :
    applySolvedRequirement left row = applySolvedRequirement right row := by
  have evidenceEq : applyPredicateEvidence left row.evidence = applyPredicateEvidence right row.evidence := by
    cases row.evidence <;> simp only [applyPredicateEvidence, predicate_congr same, evidence_congr same]
  simp only [applySolvedRequirement, predicate_congr same, evidenceEq]

theorem typedSource_reverse {substitution : TypeSystem.ParameterSubstitution}
    (unique : (SourceSemantics.ParameterSubstitution.domain substitution).Nodup) (source : TypedSource) :
    applyTypedSource substitution.reverse source = applyTypedSource substitution source :=
  typedSource_congr (lookup_reverse unique) source

theorem ledger_reverse {substitution : TypeSystem.ParameterSubstitution}
    (unique : (SourceSemantics.ParameterSubstitution.domain substitution).Nodup) (rows : List SolvedRequirement) :
    rows.map (applySolvedRequirement substitution.reverse) = rows.map (applySolvedRequirement substitution) := by
  exact List.map_congr_left (fun row _ => solvedRequirement_congr (lookup_reverse unique) row)

/-- Exactness is permutation invariant and keeps every original range row. -/
theorem exact_reverse {substitution : TypeSystem.ParameterSubstitution} {parameters : List TypeParameterId}
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution parameters) :
    SourceSemantics.ParameterSubstitution.Exact substitution.reverse parameters := by
  refine ⟨exact.parameters_nodup, ?_⟩
  simpa only [SourceSemantics.ParameterSubstitution.domain, List.map_reverse] using
    (List.reverse_perm _).trans exact.domain_permutation

/-- Reversal preserves full declaration validity, including unused ranges.
The source record's substitution order is retained as the reversed list. -/
theorem valid_reverse {context : Context} {instantiation : DeclarationInstantiation}
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation) :
    SourceSemantics.DeclarationInstantiation.Valid context (CallableNamedReversal.instantiation instantiation) := by
  cases valid with
  | intro signature member declaration exact range typeEq predicates parameters result =>
    refine .intro signature member declaration (exact_reverse exact) ?_ ?_ ?_ parameters result
    · intro parameter replacement member
      exact range parameter replacement (List.mem_reverse.mp member)
    · exact typeEq.trans (apply_congr (lookup_reverse exact.domain_nodup) signature.scheme.body).symm
    · simpa only [CallableNamedReversal.instantiation, predicate_congr (lookup_reverse exact.domain_nodup)] using predicates

/-- A valid function instantiation supplies its own domain uniqueness. The
same body instance is retained without constructing an execution trace. -/
theorem instantiates_reverse {program : Program} {instantiation : DeclarationInstantiation} {body : Dynamic.BodyInstance}
    (instantiated : Dynamic.FunctionInstantiates program instantiation body) :
    Dynamic.FunctionInstantiates program (CallableNamedReversal.instantiation instantiation) body := by
  cases instantiated with
  | intro signature definition declaration owner valid source result context =>
    have unique : (SourceSemantics.ParameterSubstitution.domain instantiation.parameterSubstitution).Nodup := by
      cases valid with | intro _ _ _ exact _ _ _ _ _ => exact exact.domain_nodup
    refine .intro signature definition declaration owner (valid_reverse valid) ?_ ?_ ?_
    · exact source.trans (typedSource_reverse unique _).symm
    · exact result.trans (apply_congr (lookup_reverse unique) _).symm
    · simpa only [CallableNamedReversal.instantiation, ledger_reverse unique] using context

/-- The compiler's canonical and source-retained records use the same body,
while their complete parameter lists keep their respective order. -/
theorem retained_instantiates {program : Program} {specialized : SourceSpecialization.SpecializedFunction}
    {body : Dynamic.BodyInstance}
    (instantiated : Dynamic.FunctionInstantiates program (CallableNamedMetadata.instantiation specialized) body) :
    Dynamic.FunctionInstantiates program (CallableNamedCanonicalOrder.retainedInstantiation specialized) body :=
  instantiates_reverse instantiated

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedRetainedSubstitutionFacts
