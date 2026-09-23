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
