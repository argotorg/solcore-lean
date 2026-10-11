import Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition
import Solcore.SourceSemantics.Dynamic.GeneralizedClosure

/-! Equal flexible-metavariable lookups act equally on the complete retained
source carrier and its initializer context. Quantified schemes keep their
actual masks; substitution lists need not have the same order. Materializing
the same principal descriptor with the same evidence then yields the same
ordinary closure. Runtime attachment and accepted matching are separate facts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableFlexibleSubstitutionAgreement
open Frontend SourceInference TypeSystem
open CallableAncestryProfiles.SourceComposition

private theorem masked_lookup {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (variables : List TypeVarId) :
    ∀ metavariable, (left.without variables).lookup? metavariable =
      (right.without variables).lookup? metavariable := by
  intro metavariable
  simp only [lookup_without, same metavariable]

private theorem apply_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    left.apply = right.apply :=
  funext (apply_lookup_congr same)

private theorem predicate_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    TypedTraitResolution.applySubstitution left =
      TypedTraitResolution.applySubstitution right := by
  funext predicate
  simp only [TypedTraitResolution.applySubstitution, apply_function same]

private theorem requirement_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    LocalSchemeRequirement.applySubstitution left =
      LocalSchemeRequirement.applySubstitution right := by
  funext requirement
  simp only [LocalSchemeRequirement.applySubstitution, predicate_function same]

private theorem scheme_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (scheme : Scheme) : scheme.apply left = scheme.apply right := by
  simp only [Scheme.apply, apply_lookup_congr (masked_lookup same scheme.quantified)]

private theorem binder_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    TypedBinder.applySubstitution left = TypedBinder.applySubstitution right := by
  funext binder
  have masked := masked_lookup same binder.scheme.quantified
  simp only [TypedBinder.applySubstitution, scheme_congr masked,
    requirement_function masked]

private theorem declaration_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    DeclarationInstantiation.applySubstitution left =
      DeclarationInstantiation.applySubstitution right := by
  funext value
  unfold DeclarationInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map
      (fun (entry : TypeParameterId × Ty) => (entry.1, left.apply entry.2))
    type := left.apply value.type
    predicates := value.predicates.map (TypedTraitResolution.applySubstitution left) } =
    { value with
      parameterSubstitution := value.parameterSubstitution.map
        (fun (entry : TypeParameterId × Ty) => (entry.1, right.apply entry.2))
      type := right.apply value.type
      predicates := value.predicates.map (TypedTraitResolution.applySubstitution right) }
  simp only [apply_function same, predicate_function same]

private theorem constructor_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    DataConstructorInstantiation.applySubstitution left =
      DataConstructorInstantiation.applySubstitution right := by
  funext value
  unfold DataConstructorInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map
      (fun (entry : TypeParameterId × Ty) => (entry.1, left.apply entry.2))
    payloadTypes := value.payloadTypes.map left.apply
    resultType := left.apply value.resultType } =
    { value with
      parameterSubstitution := value.parameterSubstitution.map
        (fun (entry : TypeParameterId × Ty) => (entry.1, right.apply entry.2))
      payloadTypes := value.payloadTypes.map right.apply
      resultType := right.apply value.resultType }
  simp only [apply_function same]

private theorem integer_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    IntegerLiteralResolution.applySubstitution left =
      IntegerLiteralResolution.applySubstitution right := by
  funext resolution
  simp only [IntegerLiteralResolution.applySubstitution, apply_function same]

private theorem coercion_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    CoercionStep.applySubstitution left = CoercionStep.applySubstitution right := by
  funext step
  simp only [CoercionStep.applySubstitution, apply_function same]

private theorem indirect_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    IndirectCallResolution.applySubstitution left =
      IndirectCallResolution.applySubstitution right := by
  funext resolution
  simp only [IndirectCallResolution.applySubstitution, apply_function same,
    coercion_function same]

private theorem reference_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    ReferenceResolution.applySubstitution left = ReferenceResolution.applySubstitution right := by
  funext resolution
  cases resolution <;> simp only [ReferenceResolution.applySubstitution, declaration_function same]

private theorem call_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    CallResolution.applySubstitution left = CallResolution.applySubstitution right := by
  funext resolution
  cases resolution <;> simp only [CallResolution.applySubstitution, indirect_function same,
    declaration_function same]

private theorem expression_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    ExpressionForm.applySubstitution left = ExpressionForm.applySubstitution right := by
  funext form
  cases form <;> simp only [ExpressionForm.applySubstitution, integer_function same,
    reference_function same, call_function same, constructor_function same,
    binder_function same, apply_function same]

private theorem instruction_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    MatchPatternInstruction.applySubstitution left =
      MatchPatternInstruction.applySubstitution right := by
  funext instruction
  cases instruction <;> simp only [MatchPatternInstruction.applySubstitution,
    integer_function same, binder_function same, constructor_function same]

private theorem pattern_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    MatchPatternResolution.applySubstitution left =
      MatchPatternResolution.applySubstitution right := by
  funext pattern
  cases pattern <;> simp only [MatchPatternResolution.applySubstitution,
    integer_function same, binder_function same, constructor_function same,
    instruction_function same]

private theorem match_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    MatchResolution.applySubstitution left = MatchResolution.applySubstitution right := by
  have arm_function : TypedMatchCase.applySubstitution left =
      TypedMatchCase.applySubstitution right := by
    funext arm
    simp only [TypedMatchCase.applySubstitution, TypedMatchPattern.applySubstitution,
      pattern_function same, apply_function same]
  funext resolution
  simp only [MatchResolution.applySubstitution, arm_function]

private theorem assignment_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    AssignmentResolution.applySubstitution left = AssignmentResolution.applySubstitution right := by
  funext assignment
  simp only [AssignmentResolution.applySubstitution, PlaceResolution.applySubstitution,
    apply_function same]

private theorem for_item_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    ForItemForm.applySubstitution left = ForItemForm.applySubstitution right := by
  funext item
  cases item <;> simp only [ForItemForm.applySubstitution, binder_function same,
    assignment_function same]

private theorem statement_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    StatementForm.applySubstitution left = StatementForm.applySubstitution right := by
  funext form
  cases form <;> simp only [StatementForm.applySubstitution, binder_function same,
    assignment_function same, match_function same, for_item_function same]

private theorem node_function {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) :
    Node.applySubstitution left = Node.applySubstitution right := by
  funext node
  cases node <;> simp only [Node.applySubstitution, ExpressionNode.applySubstitution,
    StatementNode.applySubstitution, coercion_function same,
    expression_function same, statement_function same, apply_function same]

/-- The full source table, binder schemes, nested declaration substitutions,
coercions and requirement metadata retain the same raw structural action. -/
theorem typedSource_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (source : TypedSource) :
    source.applySubstitution left = source.applySubstitution right := by
  simp only [TypedSource.applySubstitution, binder_function same, node_function same]

mutual
  private theorem evidence_congr {left right : Substitution}
      (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
      (evidence : TypedTraitResolution.Evidence) :
      FlexibleSubstitution.applyEvidence left evidence =
        FlexibleSubstitution.applyEvidence right evidence := by
    cases evidence with
    | byImpl goal implementation premises =>
      simp only [FlexibleSubstitution.applyEvidence, predicate_function same,
        evidences_congr same premises]

  private theorem evidences_congr {left right : Substitution}
      (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
      (evidences : List TypedTraitResolution.Evidence) :
      FlexibleSubstitution.applyEvidences left evidences =
        FlexibleSubstitution.applyEvidences right evidences := by
    cases evidences with
    | nil => rfl
    | cons head tail =>
      simp only [FlexibleSubstitution.applyEvidences, evidence_congr same head,
        evidences_congr same tail]
end

private theorem solved_requirement_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (row : SolvedRequirement) :
    FlexibleSubstitution.applySolvedRequirement left row =
      FlexibleSubstitution.applySolvedRequirement right row := by
  have evidence_eq : FlexibleSubstitution.applyPredicateEvidence left row.evidence =
      FlexibleSubstitution.applyPredicateEvidence right row.evidence := by
    cases row.evidence <;> simp only [FlexibleSubstitution.applyPredicateEvidence,
      predicate_function same, evidence_congr same]
  simp only [FlexibleSubstitution.applySolvedRequirement, predicate_function same, evidence_eq]

private theorem locals_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (locals : Resolved.LocalScope Scheme) :
    FlexibleSubstitution.applyLocals left locals =
      FlexibleSubstitution.applyLocals right locals := by
  unfold FlexibleSubstitution.applyLocals
  apply List.map_congr_left
  intro entry _
  rw [scheme_congr same entry.2]

private theorem local_requirements_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (locals : Resolved.LocalScope Scheme)
    (requirements : Resolved.LocalScope (List LocalSchemeRequirement)) :
    FlexibleSubstitution.applyLocalSchemeRequirements left locals requirements =
      FlexibleSubstitution.applyLocalSchemeRequirements right locals requirements := by
  unfold FlexibleSubstitution.applyLocalSchemeRequirements
  apply List.map_congr_left
  intro entry _
  have local_same : ∀ metavariable,
      (FlexibleSubstitution.forLocal left locals entry.1).lookup? metavariable =
        (FlexibleSubstitution.forLocal right locals entry.1).lookup? metavariable := by
    cases found : locals.lookup? entry.1 with
    | none => simpa only [FlexibleSubstitution.forLocal, found] using same
    | some scheme =>
      simpa only [FlexibleSubstitution.forLocal, found] using
        masked_lookup same scheme.quantified
  simp only [requirement_function local_same]

/-- Closing the same initializer context retains every original local mask,
assumption and recursively mapped solved evidence row. -/
theorem closeContext_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (context : SourceSemantics.Context) :
    FlexibleSubstitution.closeContext left context =
      FlexibleSubstitution.closeContext right context := by
  have solved_function : FlexibleSubstitution.applySolvedRequirement left =
      FlexibleSubstitution.applySolvedRequirement right :=
    funext (solved_requirement_congr same)
  simp only [FlexibleSubstitution.closeContext, FlexibleSubstitution.applyContext,
    locals_congr same, local_requirements_congr same, predicate_function same,
    solved_function]

/-- Lookup agreement closes all fields of one genuine principal descriptor.
The captured locations and the supplied runtime evidence are exactly shared. -/
theorem instantiate_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable)
    (function : Dynamic.GeneralizedClosure) (evidence : Dynamic.EvidenceEnvironment) :
    function.instantiate left evidence = function.instantiate right evidence := by
  simp only [Dynamic.GeneralizedClosure.instantiate, binder_function same,
    apply_function same, typedSource_congr same, closeContext_congr same]

end Solcore.SourceSemantics.CoreLowering.CallableFlexibleSubstitutionAgreement
