import Solcore.SourceSemantics.Instantiation
import Solcore.Frontend.SourceInference.Types

/-!
Declarative source-level trait entailment and retained-evidence validity.

Implementation-head instantiation is witnessed by exact simultaneous
substitutions. Trait entailment then checks a finite semantic evidence tree.
Neither relation invokes unification, bounded resolution, resolver memoization,
or a checker result. A separate representation relation connects these
semantic evidence trees to the evidence carrier retained by the executable
frontend.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend

/-- Pointwise correspondence between two lists, preserving order and length. -/
inductive Forall₂ {α β : Type} (relation : α → β → Prop) :
    List α → List β → Prop where
  | nil : Forall₂ relation [] []
  | cons {left right lefts rights}
      (head : relation left right)
      (tail : Forall₂ relation lefts rights) :
      Forall₂ relation (left :: lefts) (right :: rights)

namespace Forall₂

theorem length_eq {α β : Type} {relation : α → β → Prop}
    {left : List α} {right : List β}
    (related : Forall₂ relation left right) :
    left.length = right.length := by
  induction related with
  | nil => rfl
  | cons _ _ induction => simp [induction]

end Forall₂

private def insertVariable (variables : List TypeSystem.TypeVarId)
    (metavariable : TypeSystem.TypeVarId) : List TypeSystem.TypeVarId :=
  if metavariable ∈ variables then variables else variables ++ [metavariable]

private def appendVariables (variables : List TypeSystem.TypeVarId)
    (type : TypeSystem.Ty) : List TypeSystem.TypeVarId :=
  type.freeVariables.foldl insertVariable variables

private def insertParameter (parameters : List TypeSystem.TypeParameterId)
    (parameter : TypeSystem.TypeParameterId) :
    List TypeSystem.TypeParameterId :=
  if parameter ∈ parameters then parameters else parameters ++ [parameter]

private def appendParameters (parameters : List TypeSystem.TypeParameterId) :
    TypeSystem.Ty → List TypeSystem.TypeParameterId
  | .parameter parameter => insertParameter parameters parameter
  | .variable _
  | .constructor _
  | .error => parameters
  | .application left right
  | .function left right
  | .product left right
  | .mapping left right =>
      appendParameters (appendParameters parameters left) right
  | .proxy inner
  | .comptime inner => appendParameters parameters inner

/-- Flexible variables bound by an implementation rule, in stable
subject/argument/where-predicate order. -/
def implRuleVariables (rule : ProgramImplRule) :
    List TypeSystem.TypeVarId :=
  rule.wherePredicates.foldl
    (fun variables predicate =>
      predicate.arguments.foldl appendVariables
        (appendVariables variables predicate.subject))
    (rule.head.arguments.foldl appendVariables
      rule.head.subject.freeVariables)

/-- Rigid type parameters bound by an implementation rule, in stable
subject/argument/where-predicate order. -/
def implRuleParameters (rule : ProgramImplRule) :
    List TypeSystem.TypeParameterId :=
  rule.wherePredicates.foldl
    (fun parameters predicate =>
      predicate.arguments.foldl appendParameters
        (appendParameters parameters predicate.subject))
    (rule.head.arguments.foldl appendParameters
      (appendParameters [] rule.head.subject))

/-- A flexible variable occurs in the subject or an argument of a trait
predicate.  This is the flexible-variable analogue of
`TypeParameterOccursInPredicate`. -/
def TypeVariableOccursInPredicate
    (metavariable : TypeSystem.TypeVarId)
    (predicate : ProgramPredicate) : Prop :=
  metavariable ∈ predicate.subject.freeVariables ∨
    ∃ argument, argument ∈ predicate.arguments ∧
      metavariable ∈ argument.freeVariables

private theorem mem_insertParameter_iff
    (parameter candidate : TypeSystem.TypeParameterId)
    (parameters : List TypeSystem.TypeParameterId) :
    parameter ∈ insertParameter parameters candidate ↔
      parameter ∈ parameters ∨ parameter = candidate := by
  by_cases present : candidate ∈ parameters
  · rw [insertParameter, if_pos present]
    constructor
    · exact Or.inl
    · rintro (member | rfl)
      · exact member
      · exact present
  · simp [insertParameter, present]

private theorem mem_appendParameters_iff
    (parameter : TypeSystem.TypeParameterId)
    (parameters : List TypeSystem.TypeParameterId)
    (type : TypeSystem.Ty) :
    parameter ∈ appendParameters parameters type ↔
      parameter ∈ parameters ∨ TypeParameterOccurs parameter type := by
  induction type generalizing parameters with
  | @«variable» metavariable => simp [appendParameters, TypeParameterOccurs]
  | @«parameter» candidate =>
      simpa [appendParameters, TypeParameterOccurs, eq_comm] using
        mem_insertParameter_iff parameter candidate parameters
  | constructor constructor => simp [appendParameters, TypeParameterOccurs]
  | application left right leftInduction rightInduction =>
      rw [appendParameters, rightInduction, leftInduction]
      simp [TypeParameterOccurs, or_assoc]
  | function domain codomain domainInduction codomainInduction =>
      rw [appendParameters, codomainInduction, domainInduction]
      simp [TypeParameterOccurs, or_assoc]
  | product left right leftInduction rightInduction =>
      rw [appendParameters, rightInduction, leftInduction]
      simp [TypeParameterOccurs, or_assoc]
  | mapping key value keyInduction valueInduction =>
      rw [appendParameters, valueInduction, keyInduction]
      simp [TypeParameterOccurs, or_assoc]
  | proxy inner induction =>
      simpa [appendParameters, TypeParameterOccurs] using
        induction parameters
  | comptime inner induction =>
      simpa [appendParameters, TypeParameterOccurs] using
        induction parameters
  | error => simp [appendParameters, TypeParameterOccurs]

private theorem mem_foldl_appendParameters_iff
    (parameter : TypeSystem.TypeParameterId)
    (parameters : List TypeSystem.TypeParameterId)
    (types : List TypeSystem.Ty) :
    parameter ∈ types.foldl appendParameters parameters ↔
      parameter ∈ parameters ∨
        ∃ type, type ∈ types ∧ TypeParameterOccurs parameter type := by
  induction types generalizing parameters with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction, mem_appendParameters_iff]
      simp only [List.mem_cons]
      constructor
      · rintro ((member | occurs) | ⟨type, typeMem, typeOccurs⟩)
        · exact Or.inl member
        · exact Or.inr ⟨head, Or.inl rfl, occurs⟩
        · exact Or.inr ⟨type, Or.inr typeMem, typeOccurs⟩
      · rintro (member | ⟨type, typeMem, typeOccurs⟩)
        · exact Or.inl (Or.inl member)
        · rcases typeMem with rfl | typeMem
          · exact Or.inl (Or.inr typeOccurs)
          · exact Or.inr ⟨type, typeMem, typeOccurs⟩

private theorem mem_insertVariable_iff
    (metavariable candidate : TypeSystem.TypeVarId)
    (variables : List TypeSystem.TypeVarId) :
    metavariable ∈ insertVariable variables candidate ↔
      metavariable ∈ variables ∨ metavariable = candidate := by
  by_cases present : candidate ∈ variables
  · rw [insertVariable, if_pos present]
    constructor
    · exact Or.inl
    · rintro (member | rfl)
      · exact member
      · exact present
  · simp [insertVariable, present]

private theorem mem_foldl_insertVariable_iff
    (metavariable : TypeSystem.TypeVarId)
    (variables values : List TypeSystem.TypeVarId) :
    metavariable ∈ values.foldl insertVariable variables ↔
      metavariable ∈ variables ∨ metavariable ∈ values := by
  induction values generalizing variables with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction, mem_insertVariable_iff]
      simp only [List.mem_cons]
      exact or_assoc

theorem mem_freeVariables_application_iff
    {metavariable : TypeSystem.TypeVarId} {left right : TypeSystem.Ty} :
    metavariable ∈ (TypeSystem.Ty.application left right).freeVariables ↔
      metavariable ∈ left.freeVariables ∨
        metavariable ∈ right.freeVariables := by
  exact mem_foldl_insertVariable_iff metavariable left.freeVariables
    right.freeVariables

theorem mem_freeVariables_function_iff
    {metavariable : TypeSystem.TypeVarId} {domain codomain : TypeSystem.Ty} :
    metavariable ∈ (TypeSystem.Ty.function domain codomain).freeVariables ↔
      metavariable ∈ domain.freeVariables ∨
        metavariable ∈ codomain.freeVariables := by
  exact mem_foldl_insertVariable_iff metavariable domain.freeVariables
    codomain.freeVariables

theorem mem_freeVariables_product_iff
    {metavariable : TypeSystem.TypeVarId} {left right : TypeSystem.Ty} :
    metavariable ∈ (TypeSystem.Ty.product left right).freeVariables ↔
      metavariable ∈ left.freeVariables ∨
        metavariable ∈ right.freeVariables := by
  exact mem_foldl_insertVariable_iff metavariable left.freeVariables
    right.freeVariables

theorem mem_freeVariables_mapping_iff
    {metavariable : TypeSystem.TypeVarId} {key value : TypeSystem.Ty} :
    metavariable ∈ (TypeSystem.Ty.mapping key value).freeVariables ↔
      metavariable ∈ key.freeVariables ∨
        metavariable ∈ value.freeVariables := by
  exact mem_foldl_insertVariable_iff metavariable key.freeVariables
    value.freeVariables

private theorem mem_appendVariables_iff
    (metavariable : TypeSystem.TypeVarId)
    (variables : List TypeSystem.TypeVarId)
    (type : TypeSystem.Ty) :
    metavariable ∈ appendVariables variables type ↔
      metavariable ∈ variables ∨ metavariable ∈ type.freeVariables := by
  exact mem_foldl_insertVariable_iff metavariable variables type.freeVariables

private theorem mem_foldl_appendVariables_iff
    (metavariable : TypeSystem.TypeVarId)
    (variables : List TypeSystem.TypeVarId)
    (types : List TypeSystem.Ty) :
    metavariable ∈ types.foldl appendVariables variables ↔
      metavariable ∈ variables ∨
        ∃ type, type ∈ types ∧ metavariable ∈ type.freeVariables := by
  induction types generalizing variables with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction, mem_appendVariables_iff]
      simp only [List.mem_cons]
      constructor
      · rintro ((member | occurs) | ⟨type, typeMem, typeOccurs⟩)
        · exact Or.inl member
        · exact Or.inr ⟨head, Or.inl rfl, occurs⟩
        · exact Or.inr ⟨type, Or.inr typeMem, typeOccurs⟩
      · rintro (member | ⟨type, typeMem, typeOccurs⟩)
        · exact Or.inl (Or.inl member)
        · rcases typeMem with rfl | typeMem
          · exact Or.inl (Or.inr typeOccurs)
          · exact Or.inr ⟨type, typeMem, typeOccurs⟩

private theorem mem_foldl_predicateParameters_iff
    (parameter : TypeSystem.TypeParameterId)
    (parameters : List TypeSystem.TypeParameterId)
    (predicates : List ProgramPredicate) :
    parameter ∈ predicates.foldl
        (fun collected predicate =>
          predicate.arguments.foldl appendParameters
            (appendParameters collected predicate.subject)) parameters ↔
      parameter ∈ parameters ∨
        ∃ predicate, predicate ∈ predicates ∧
          TypeParameterOccursInPredicate parameter predicate := by
  induction predicates generalizing parameters with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction, mem_foldl_appendParameters_iff,
        mem_appendParameters_iff]
      simp only [List.mem_cons, TypeParameterOccursInPredicate]
      constructor
      · rintro (((member | subjectOccurs) | ⟨argument, argumentMem,
          argumentOccurs⟩) | ⟨predicate, predicateMem, predicateOccurs⟩)
        · exact Or.inl member
        · exact Or.inr ⟨head, Or.inl rfl, Or.inl subjectOccurs⟩
        · exact Or.inr ⟨head, Or.inl rfl,
            Or.inr ⟨argument, argumentMem, argumentOccurs⟩⟩
        · exact Or.inr ⟨predicate, Or.inr predicateMem, predicateOccurs⟩
      · rintro (member | ⟨predicate, predicateMem, predicateOccurs⟩)
        · exact Or.inl (Or.inl (Or.inl member))
        · rcases predicateMem with rfl | predicateMem
          · rcases predicateOccurs with subjectOccurs |
              ⟨argument, argumentMem, argumentOccurs⟩
            · exact Or.inl (Or.inl (Or.inr subjectOccurs))
            · exact Or.inl (Or.inr
                ⟨argument, argumentMem, argumentOccurs⟩)
          · exact Or.inr ⟨predicate, predicateMem, predicateOccurs⟩

private theorem mem_foldl_predicateVariables_iff
    (metavariable : TypeSystem.TypeVarId)
    (variables : List TypeSystem.TypeVarId)
    (predicates : List ProgramPredicate) :
    metavariable ∈ predicates.foldl
        (fun collected predicate =>
          predicate.arguments.foldl appendVariables
            (appendVariables collected predicate.subject)) variables ↔
      metavariable ∈ variables ∨
        ∃ predicate, predicate ∈ predicates ∧
          TypeVariableOccursInPredicate metavariable predicate := by
  induction predicates generalizing variables with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction, mem_foldl_appendVariables_iff,
        mem_appendVariables_iff]
      simp only [List.mem_cons, TypeVariableOccursInPredicate]
      constructor
      · rintro (((member | subjectOccurs) | ⟨argument, argumentMem,
          argumentOccurs⟩) | ⟨predicate, predicateMem, predicateOccurs⟩)
        · exact Or.inl member
        · exact Or.inr ⟨head, Or.inl rfl, Or.inl subjectOccurs⟩
        · exact Or.inr ⟨head, Or.inl rfl,
            Or.inr ⟨argument, argumentMem, argumentOccurs⟩⟩
        · exact Or.inr ⟨predicate, Or.inr predicateMem, predicateOccurs⟩
      · rintro (member | ⟨predicate, predicateMem, predicateOccurs⟩)
        · exact Or.inl (Or.inl (Or.inl member))
        · rcases predicateMem with rfl | predicateMem
          · rcases predicateOccurs with subjectOccurs |
              ⟨argument, argumentMem, argumentOccurs⟩
            · exact Or.inl (Or.inl (Or.inr subjectOccurs))
            · exact Or.inl (Or.inr
                ⟨argument, argumentMem, argumentOccurs⟩)
          · exact Or.inr ⟨predicate, predicateMem, predicateOccurs⟩

/-- The implementation-rule parameter collector covers exactly every rigid
parameter in the head and where predicates. -/
theorem mem_implRuleParameters_iff
    {parameter : TypeSystem.TypeParameterId} {rule : ProgramImplRule} :
    parameter ∈ implRuleParameters rule ↔
      TypeParameterOccursInPredicate parameter rule.head ∨
        ∃ predicate, predicate ∈ rule.wherePredicates ∧
          TypeParameterOccursInPredicate parameter predicate := by
  simp only [implRuleParameters, mem_foldl_appendParameters_iff,
    mem_appendParameters_iff, mem_foldl_predicateParameters_iff,
    TypeParameterOccursInPredicate, List.not_mem_nil, false_or]

/-- The implementation-rule variable collector covers exactly every flexible
variable in the head and where predicates. -/
theorem mem_implRuleVariables_iff
    {metavariable : TypeSystem.TypeVarId} {rule : ProgramImplRule} :
    metavariable ∈ implRuleVariables rule ↔
      TypeVariableOccursInPredicate metavariable rule.head ∨
        ∃ predicate, predicate ∈ rule.wherePredicates ∧
          TypeVariableOccursInPredicate metavariable predicate := by
  simp only [implRuleVariables, mem_foldl_appendVariables_iff,
    mem_foldl_predicateVariables_iff,
    TypeVariableOccursInPredicate]

/-- Simultaneous replacements for both binder classes in an implementation
rule. Replacement ranges are not recursively rewritten by the other map. -/
structure ImplSubstitution where
  parameters : TypeSystem.ParameterSubstitution
  variables : TypeSystem.Substitution
  deriving Repr, DecidableEq

namespace ImplSubstitution

/-- Apply rigid-parameter and flexible-variable replacements simultaneously. -/
def applyType (substitution : ImplSubstitution) :
    TypeSystem.Ty → TypeSystem.Ty
  | .variable metavariable =>
      substitution.variables.lookup? metavariable |>.getD
        (.variable metavariable)
  | .parameter parameter =>
      substitution.parameters.lookup? parameter |>.getD (.parameter parameter)
  | .constructor constructor => .constructor constructor
  | .application function argument =>
      .application (applyType substitution function)
        (applyType substitution argument)
  | .function parameter result =>
      .function (applyType substitution parameter)
        (applyType substitution result)
  | .product left right =>
      .product (applyType substitution left) (applyType substitution right)
  | .mapping key value =>
      .mapping (applyType substitution key) (applyType substitution value)
  | .proxy inner => .proxy (applyType substitution inner)
  | .comptime inner => .comptime (applyType substitution inner)
  | .error => .error

/-- Apply one rule substitution to every type position in a predicate. -/
def applyPredicate (substitution : ImplSubstitution)
    (predicate : ProgramPredicate) : ProgramPredicate := {
  predicate with
  subject := substitution.applyType predicate.subject
  arguments := predicate.arguments.map substitution.applyType
}

/-- The substitution covers every binder of the rule exactly once and no
unrelated binder. -/
structure ExactFor (substitution : ImplSubstitution)
    (rule : ProgramImplRule) : Prop where
  parameters : SourceSemantics.ParameterSubstitution.Exact
    substitution.parameters (implRuleParameters rule)
  variables : ExactSubstitution substitution.variables (implRuleVariables rule)

end ImplSubstitution

/-- One implementation head and all of its where predicates are instantiated
by a shared exact simultaneous substitution. This is the declarative impl-head
matching relation; no unifier or search procedure occurs here. -/
inductive ImplHeadInstantiates
    (rule : ProgramImplRule)
    (goal : ProgramPredicate)
    (premises : List ProgramPredicate) : Prop where
  | intro
      (substitution : ImplSubstitution)
      (exact : substitution.ExactFor rule)
      (head_eq : substitution.applyPredicate rule.head = goal)
      (premises_eq :
        rule.wherePredicates.map substitution.applyPredicate = premises) :
      ImplHeadInstantiates rule goal premises

/-- Proof objects for the declarative trait relation. Unlike the executable
carrier, assumptions may occur at any premise depth. -/
inductive TraitEvidence where
  | assumption (goal : ProgramPredicate)
  | implementation
      (goal : ProgramPredicate)
      (implId : ProgramImplId)
      (premises : List TraitEvidence)
  deriving Repr

namespace TraitEvidence

def goal : TraitEvidence → ProgramPredicate
  | .assumption goal => goal
  | .implementation goal _ _ => goal

end TraitEvidence

/-- Declarative validity of a semantic evidence tree. -/
inductive EvidenceValid
    (assumptions : List ProgramPredicate)
    (rules : List ProgramImplRule) :
    ProgramPredicate → TraitEvidence → Prop where
  | assumption
      {goal : ProgramPredicate}
      (goal_mem : goal ∈ assumptions) :
      EvidenceValid assumptions rules goal (.assumption goal)
  | implementation
      {rule : ProgramImplRule}
      {goal : ProgramPredicate}
      {implId : ProgramImplId}
      {premiseGoals : List ProgramPredicate}
      {premiseEvidence : List TraitEvidence}
      (rule_mem : rule ∈ rules)
      (id_eq : rule.id = implId)
      (head_instantiates : ImplHeadInstantiates rule goal premiseGoals)
      (premises_valid : Forall₂
        (EvidenceValid assumptions rules) premiseGoals premiseEvidence) :
      EvidenceValid assumptions rules goal
        (.implementation goal implId premiseEvidence)

/-- Fuel- and algorithm-independent trait entailment. -/
def Entails
    (assumptions : List ProgramPredicate)
    (rules : List ProgramImplRule)
    (goal : ProgramPredicate) : Prop :=
  ∃ evidence, EvidenceValid assumptions rules goal evidence

namespace EvidenceValid

mutual

/-- Semantic evidence remains valid when more explicit hypotheses become
available. -/
theorem weakenAssumptions
    {smaller larger : List ProgramPredicate}
    {rules : List ProgramImplRule}
    {goal : ProgramPredicate} {evidence : TraitEvidence}
    (included : ∀ predicate, predicate ∈ smaller → predicate ∈ larger)
    (valid : EvidenceValid smaller rules goal evidence) :
    EvidenceValid larger rules goal evidence := by
  cases valid with
  | assumption goal_mem => exact .assumption (included _ goal_mem)
  | implementation rule_mem id_eq head_instantiates premises_valid =>
      exact .implementation rule_mem id_eq head_instantiates
        (Forall₂EvidenceValid.weakenAssumptions included premises_valid)

/-- Pointwise hypothesis weakening for an evidence-premise spine. -/
theorem Forall₂EvidenceValid.weakenAssumptions
    {smaller larger : List ProgramPredicate}
    {rules : List ProgramImplRule}
    {goals : List ProgramPredicate} {evidence : List TraitEvidence}
    (included : ∀ predicate, predicate ∈ smaller → predicate ∈ larger)
    (valid : Forall₂ (EvidenceValid smaller rules) goals evidence) :
    Forall₂ (EvidenceValid larger rules) goals evidence := by
  cases valid with
  | nil => exact .nil
  | cons head tail =>
      exact .cons (EvidenceValid.weakenAssumptions included head)
        (Forall₂EvidenceValid.weakenAssumptions included tail)

end

theorem evidence_goal_eq
    {assumptions : List ProgramPredicate}
    {rules : List ProgramImplRule}
    {goal : ProgramPredicate}
    {evidence : TraitEvidence}
    (valid : EvidenceValid assumptions rules goal evidence) :
    evidence.goal = goal := by
  cases valid <;> rfl

theorem assumption_iff
    {assumptions : List ProgramPredicate}
    {rules : List ProgramImplRule}
    {goal : ProgramPredicate} :
    EvidenceValid assumptions rules goal (.assumption goal) ↔
      goal ∈ assumptions := by
  constructor
  · intro valid
    cases valid with
    | assumption goal_mem => exact goal_mem
  · exact EvidenceValid.assumption

theorem implementation_iff
    {assumptions : List ProgramPredicate}
    {rules : List ProgramImplRule}
    {goal : ProgramPredicate}
    {implId : ProgramImplId}
    {premiseEvidence : List TraitEvidence} :
    EvidenceValid assumptions rules goal
        (.implementation goal implId premiseEvidence) ↔
      ∃ rule premiseGoals,
        rule ∈ rules ∧
        rule.id = implId ∧
        ImplHeadInstantiates rule goal premiseGoals ∧
        Forall₂ (EvidenceValid assumptions rules)
          premiseGoals premiseEvidence := by
  constructor
  · intro valid
    cases valid with
    | implementation rule_mem id_eq head_instantiates premises_valid =>
        exact ⟨_, _, rule_mem, id_eq, head_instantiates, premises_valid⟩
  · rintro ⟨rule, premiseGoals, rule_mem, id_eq, head_instantiates,
      premises_valid⟩
    exact .implementation rule_mem id_eq head_instantiates premises_valid

theorem premise_count_eq
    {assumptions : List ProgramPredicate}
    {rules : List ProgramImplRule}
    {goal : ProgramPredicate}
    {implId : ProgramImplId}
    {premiseEvidence : List TraitEvidence}
    (valid : EvidenceValid assumptions rules goal
      (.implementation goal implId premiseEvidence)) :
    ∃ rule premiseGoals,
      rule ∈ rules ∧
      ImplHeadInstantiates rule goal premiseGoals ∧
      premiseGoals.length = premiseEvidence.length := by
  rw [implementation_iff] at valid
  obtain ⟨rule, premiseGoals, rule_mem, _, head_instantiates,
    premises_valid⟩ := valid
  exact ⟨rule, premiseGoals, rule_mem, head_instantiates,
    premises_valid.length_eq⟩

end EvidenceValid

namespace Entails

theorem assumption
    {assumptions : List ProgramPredicate}
    {rules : List ProgramImplRule}
    {goal : ProgramPredicate}
    (goal_mem : goal ∈ assumptions) :
    Entails assumptions rules goal :=
  ⟨.assumption goal, .assumption goal_mem⟩

theorem implementation
    {assumptions : List ProgramPredicate}
    {rules : List ProgramImplRule}
    {goal : ProgramPredicate}
    {implId : ProgramImplId}
    {premiseEvidence : List TraitEvidence}
    (valid : EvidenceValid assumptions rules goal
      (.implementation goal implId premiseEvidence)) :
    Entails assumptions rules goal :=
  ⟨.implementation goal implId premiseEvidence, valid⟩

end Entails

/-- A raw implementation-evidence tree represents a semantic tree when it
retains the same goals, implementation identities, order, and recursive
shape. -/
inductive ImplementationEvidenceRepresents :
    TypedTraitResolution.Evidence → TraitEvidence → Prop where
  | byImpl
      {goal : ProgramPredicate}
      {implId : ProgramImplId}
      {retainedPremises : List TypedTraitResolution.Evidence}
      {semanticPremises : List TraitEvidence}
      (premises : Forall₂ ImplementationEvidenceRepresents
        retainedPremises semanticPremises) :
      ImplementationEvidenceRepresents
        (.byImpl goal implId retainedPremises)
        (.implementation goal implId semanticPremises)

/-- The executable source-inference evidence carrier represents either a
semantic assumption or a recursively represented implementation tree. -/
inductive PredicateEvidenceRepresents :
    Frontend.SourceInference.PredicateEvidence → TraitEvidence → Prop where
  | assumption (goal : ProgramPredicate) :
      PredicateEvidenceRepresents (.assumption goal) (.assumption goal)
  | implementation
      {retained : TypedTraitResolution.Evidence}
      {semantic : TraitEvidence}
      (represents : ImplementationEvidenceRepresents retained semantic) :
      PredicateEvidenceRepresents (.implementation retained) semantic

namespace PredicateEvidenceRepresents

theorem goal_eq
    {retained : Frontend.SourceInference.PredicateEvidence}
    {semantic : TraitEvidence}
    (represents : PredicateEvidenceRepresents retained semantic) :
    retained.goal = semantic.goal := by
  cases represents with
  | assumption => rfl
  | implementation implementationRepresents =>
      cases implementationRepresents
      rfl

end PredicateEvidenceRepresents

/-- A retained executable evidence value is valid when it represents a valid
semantic evidence tree. This is a bridge judgment, not the definition of
trait entailment. -/
inductive RetainedEvidenceValid
    (assumptions : List ProgramPredicate)
    (rules : List ProgramImplRule)
    (goal : ProgramPredicate) :
    Frontend.SourceInference.PredicateEvidence → Prop where
  | intro
      {retained : Frontend.SourceInference.PredicateEvidence}
      {semantic : TraitEvidence}
      (represents : PredicateEvidenceRepresents retained semantic)
      (valid : EvidenceValid assumptions rules goal semantic) :
      RetainedEvidenceValid assumptions rules goal retained

namespace RetainedEvidenceValid

/-- Retained evidence is monotone in the available assumption set. -/
theorem weakenAssumptions
    {smaller larger : List ProgramPredicate}
    {rules : List ProgramImplRule}
    {goal : ProgramPredicate}
    {retained : Frontend.SourceInference.PredicateEvidence}
    (included : ∀ predicate, predicate ∈ smaller → predicate ∈ larger)
    (valid : RetainedEvidenceValid smaller rules goal retained) :
    RetainedEvidenceValid larger rules goal retained := by
  cases valid with
  | intro represents semanticValid =>
      exact .intro represents (semanticValid.weakenAssumptions included)

theorem entails
    {assumptions : List ProgramPredicate}
    {rules : List ProgramImplRule}
    {goal : ProgramPredicate}
    {retained : Frontend.SourceInference.PredicateEvidence}
    (valid : RetainedEvidenceValid assumptions rules goal retained) :
    Entails assumptions rules goal := by
  cases valid with
  | intro _ semanticValid => exact ⟨_, semanticValid⟩

theorem evidence_goal_eq
    {assumptions : List ProgramPredicate}
    {rules : List ProgramImplRule}
    {goal : ProgramPredicate}
    {retained : Frontend.SourceInference.PredicateEvidence}
    (valid : RetainedEvidenceValid assumptions rules goal retained) :
    retained.goal = goal := by
  cases valid with
  | intro represents semanticValid =>
      exact represents.goal_eq.trans semanticValid.evidence_goal_eq

end RetainedEvidenceValid

end Solcore.SourceSemantics
