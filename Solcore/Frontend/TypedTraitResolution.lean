import Solcore.Frontend.ProgramIdentity
import Solcore.Frontend.TraitResolution
import Solcore.TypeSystem.Unification

set_option autoImplicit false

namespace Solcore.Frontend.TypedTraitResolution

open TypeSystem

/-- Resolved trait identity used by the typed class-resolution bridge. -/
abbrev TraitId := ProgramTraitId

/-- Resolved implementation identity used in generated evidence. -/
abbrev ImplId := ProgramImplId

/-- A trait obligation over semantic source types. -/
abbrev Predicate := TraitResolution.Predicate TraitId Ty

/-- A typed implementation rule. Every rigid generic parameter and flexible
variable occurring in the rule is freshened before each head match. -/
abbrev ImplRule := TraitResolution.ImplRule TraitId Ty ImplId

/-- The typed specialization of the generic resolution program. -/
abbrev Program := TraitResolution.Program TraitId Ty ImplId

/-- Evidence produced by typed trait resolution. -/
abbrev Evidence := TraitResolution.Evidence TraitId Ty ImplId

/-- Final typed trait-resolution outcome. -/
abbrev Outcome := TraitResolution.Outcome TraitId Ty ImplId

/-- The shared result of freshening and matching an implementation head.
`parameterSubstitution` follows the parameter order requested by the caller;
its range may remain open when a parameter is not determined by the head.
`wherePredicates` has the same head unifier applied in source order. -/
structure HeadMatch where
  parameterSubstitution : ParameterSubstitution
  wherePredicates : List Predicate
  deriving Repr, BEq, DecidableEq

/-- Canonical simultaneous substitution reconstructed for a successful rule
match.  Unlike sequential frontend substitutions, replacements in either map
are not recursively rewritten by the other map. -/
structure RuleMatchSubstitution where
  parameters : ParameterSubstitution
  variables : Substitution
  deriving Repr, BEq, DecidableEq

namespace RuleMatchSubstitution

def applyType (substitution : RuleMatchSubstitution) : Ty → Ty
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

def applyPredicate (substitution : RuleMatchSubstitution)
    (predicate : Predicate) : Predicate := {
  predicate with
  subject := substitution.applyType predicate.subject
  arguments := predicate.arguments.map substitution.applyType
}

end RuleMatchSubstitution

/-- Apply a flexible-variable substitution to every type position in a trait
predicate. Trait identity is already resolved and therefore unchanged. -/
def applySubstitution (substitution : Substitution)
    (predicate : Predicate) : Predicate :=
  { predicate with
    subject := substitution.apply predicate.subject
    arguments := predicate.arguments.map substitution.apply }

/-- Instantiate every rigid type position in a predicate with one shared
declaration-parameter substitution. -/
def applyParameterSubstitution (substitution : ParameterSubstitution)
    (predicate : Predicate) : Predicate :=
  { predicate with
    subject := substitution.apply predicate.subject
    arguments := predicate.arguments.map substitution.apply }

private def insertVariable (variables : List TypeVarId)
    (metavariable : TypeVarId) : List TypeVarId :=
  if metavariable ∈ variables then variables else variables ++ [metavariable]

private def appendVariables (variables : List TypeVarId)
    (type : Ty) : List TypeVarId :=
  type.freeVariables.foldl insertVariable variables

private def insertParameter (parameters : List TypeParameterId)
    (parameterId : TypeParameterId) : List TypeParameterId :=
  if parameterId ∈ parameters then parameters else parameters ++ [parameterId]

private def appendParameters (parameters : List TypeParameterId) :
    Ty → List TypeParameterId
  | .parameter parameterId => insertParameter parameters parameterId
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

/-- Flexible variables in stable subject-then-argument order. -/
def predicateVariables (predicate : Predicate) : List TypeVarId :=
  predicate.arguments.foldl appendVariables predicate.subject.freeVariables

private theorem foldl_appendVariables_map_of_freeVariables_eq
    (substitution : ParameterSubstitution)
    (preserves : ∀ type,
      (substitution.apply type).freeVariables = type.freeVariables)
    (initial : List TypeVarId) (types : List Ty) :
    (types.map substitution.apply).foldl appendVariables initial =
      types.foldl appendVariables initial := by
  induction types generalizing initial with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.foldl_cons]
      have headEq :
          appendVariables initial (substitution.apply head) =
            appendVariables initial head := by
        unfold appendVariables
        rw [preserves head]
      rw [headEq]
      exact induction _

/-- Rigid substitution does not change a predicate's ordered flexible-variable
ledger when it preserves the flexible variables of every replacement type. -/
theorem predicateVariables_applyParameterSubstitution_of_freeVariables_eq
    (substitution : ParameterSubstitution) (predicate : Predicate)
    (preserves : ∀ type,
      (substitution.apply type).freeVariables = type.freeVariables) :
    predicateVariables (applyParameterSubstitution substitution predicate) =
      predicateVariables predicate := by
  cases predicate with
  | mk trait subject arguments =>
      simp only [applyParameterSubstitution, predicateVariables]
      rw [preserves subject]
      exact foldl_appendVariables_map_of_freeVariables_eq substitution preserves
        subject.freeVariables arguments

/-- Rigid declaration parameters in stable subject-then-argument order. -/
def predicateParameters (predicate : Predicate) : List TypeParameterId :=
  predicate.arguments.foldl appendParameters
    (appendParameters [] predicate.subject)

/-- A fresh-variable lower bound for the whole predicate. -/
def predicateNextVariable (predicate : Predicate) : Nat :=
  predicate.arguments.foldl
    (fun next type => max next type.nextVariable)
    predicate.subject.nextVariable

/-- Flexible variables implicitly quantified by an implementation rule. -/
def ruleVariables (rule : ImplRule) : List TypeVarId :=
  rule.wherePredicates.foldl
    (fun variables predicate =>
      (predicateVariables predicate).foldl insertVariable variables)
    (predicateVariables rule.head)

/-- Rigid generic parameters instantiated together for each rule match. -/
def ruleParameters (rule : ImplRule) : List TypeParameterId :=
  rule.wherePredicates.foldl
    (fun parameters predicate =>
      (predicateParameters predicate).foldl insertParameter parameters)
    (predicateParameters rule.head)

private theorem insertVariable_nodup
    {variables : List TypeVarId} (metavariable : TypeVarId)
    (nodup : variables.Nodup) :
    (insertVariable variables metavariable).Nodup := by
  by_cases present : metavariable ∈ variables
  · simpa [insertVariable, present] using nodup
  · have appended : (variables ++ [metavariable]).Nodup := by
      rw [List.nodup_append]
      refine ⟨nodup, by simp, ?_⟩
      intro left left_mem right right_mem equal
      simp only [List.mem_singleton] at right_mem
      exact present ((equal.trans right_mem) ▸ left_mem)
    simpa [insertVariable, present] using appended

private theorem foldl_insertVariable_nodup
    (values : List TypeVarId) {variables : List TypeVarId}
    (nodup : variables.Nodup) :
    (values.foldl insertVariable variables).Nodup := by
  induction values generalizing variables with
  | nil => exact nodup
  | cons head tail induction =>
      exact induction (insertVariable_nodup head nodup)

private theorem appendVariables_nodup
    (type : Ty) {variables : List TypeVarId}
    (nodup : variables.Nodup) :
    (appendVariables variables type).Nodup := by
  exact foldl_insertVariable_nodup type.freeVariables nodup

private theorem foldl_appendVariables_nodup
    (types : List Ty) {variables : List TypeVarId}
    (nodup : variables.Nodup) :
    (types.foldl appendVariables variables).Nodup := by
  induction types generalizing variables with
  | nil => exact nodup
  | cons head tail induction =>
      exact induction (appendVariables_nodup head nodup)

private theorem insertParameter_nodup
    {parameters : List TypeParameterId} (parameter : TypeParameterId)
    (nodup : parameters.Nodup) :
    (insertParameter parameters parameter).Nodup := by
  by_cases present : parameter ∈ parameters
  · simpa [insertParameter, present] using nodup
  · have appended : (parameters ++ [parameter]).Nodup := by
      rw [List.nodup_append]
      refine ⟨nodup, by simp, ?_⟩
      intro left left_mem right right_mem equal
      simp only [List.mem_singleton] at right_mem
      exact present ((equal.trans right_mem) ▸ left_mem)
    simpa [insertParameter, present] using appended

private theorem foldl_insertParameter_nodup
    (values : List TypeParameterId) {parameters : List TypeParameterId}
    (nodup : parameters.Nodup) :
    (values.foldl insertParameter parameters).Nodup := by
  induction values generalizing parameters with
  | nil => exact nodup
  | cons head tail induction =>
      exact induction (insertParameter_nodup head nodup)

private theorem appendParameters_nodup
    (type : Ty) {parameters : List TypeParameterId}
    (nodup : parameters.Nodup) :
    (appendParameters parameters type).Nodup := by
  induction type generalizing parameters with
  | «variable» | constructor | error => exact nodup
  | «parameter» parameter => exact insertParameter_nodup parameter nodup
  | application left right left_induction right_induction =>
      exact right_induction (left_induction nodup)
  | function parameter result parameter_induction result_induction =>
      exact result_induction (parameter_induction nodup)
  | product left right left_induction right_induction =>
      exact right_induction (left_induction nodup)
  | mapping key value key_induction value_induction =>
      exact value_induction (key_induction nodup)
  | proxy inner induction | comptime inner induction => exact induction nodup

private theorem foldl_appendParameters_nodup
    (types : List Ty) {parameters : List TypeParameterId}
    (nodup : parameters.Nodup) :
    (types.foldl appendParameters parameters).Nodup := by
  induction types generalizing parameters with
  | nil => exact nodup
  | cons head tail induction =>
      exact induction (appendParameters_nodup head nodup)

theorem predicateVariables_nodup (predicate : Predicate) :
    (predicateVariables predicate).Nodup := by
  exact foldl_appendVariables_nodup predicate.arguments
    (Ty.freeVariables_nodup predicate.subject)

theorem predicateParameters_nodup (predicate : Predicate) :
    (predicateParameters predicate).Nodup := by
  exact foldl_appendParameters_nodup predicate.arguments
    (appendParameters_nodup predicate.subject (by simp))

private theorem foldl_predicateVariables_nodup
    (predicates : List Predicate) {variables : List TypeVarId}
    (nodup : variables.Nodup) :
    (predicates.foldl
      (fun collected predicate =>
        (predicateVariables predicate).foldl insertVariable collected)
      variables).Nodup := by
  induction predicates generalizing variables with
  | nil => exact nodup
  | cons predicate predicates induction =>
      exact induction
        (foldl_insertVariable_nodup (predicateVariables predicate) nodup)

private theorem foldl_predicateParameters_nodup
    (predicates : List Predicate) {parameters : List TypeParameterId}
    (nodup : parameters.Nodup) :
    (predicates.foldl
      (fun collected predicate =>
        (predicateParameters predicate).foldl insertParameter collected)
      parameters).Nodup := by
  induction predicates generalizing parameters with
  | nil => exact nodup
  | cons predicate predicates induction =>
      exact induction
        (foldl_insertParameter_nodup (predicateParameters predicate) nodup)

theorem ruleVariables_nodup (rule : ImplRule) :
    (ruleVariables rule).Nodup := by
  exact foldl_predicateVariables_nodup rule.wherePredicates
    (predicateVariables_nodup rule.head)

theorem ruleParameters_nodup (rule : ImplRule) :
    (ruleParameters rule).Nodup := by
  exact foldl_predicateParameters_nodup rule.wherePredicates
    (predicateParameters_nodup rule.head)

private theorem mem_insertVariable_iff
    (metavariable candidate : TypeVarId) (variables : List TypeVarId) :
    metavariable ∈ insertVariable variables candidate ↔
      metavariable ∈ variables ∨ metavariable = candidate := by
  by_cases present : candidate ∈ variables
  · simp [insertVariable, present]
    intro equal
    subst candidate
    exact present
  · simp [insertVariable, present]

private theorem mem_foldl_insertVariable_iff
    (metavariable : TypeVarId) (variables values : List TypeVarId) :
    metavariable ∈ values.foldl insertVariable variables ↔
      metavariable ∈ variables ∨ metavariable ∈ values := by
  induction values generalizing variables with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction,
        mem_insertVariable_iff metavariable head variables]
      simp only [List.mem_cons]
      constructor
      · rintro ((member | equal) | tail_member)
        · exact .inl member
        · exact .inr (.inl equal)
        · exact .inr (.inr tail_member)
      · rintro (member | equal | tail_member)
        · exact .inl (.inl member)
        · exact .inl (.inr equal)
        · exact .inr tail_member

private theorem mem_insertParameter_iff
    (parameter candidate : TypeParameterId)
    (parameters : List TypeParameterId) :
    parameter ∈ insertParameter parameters candidate ↔
      parameter ∈ parameters ∨ parameter = candidate := by
  by_cases present : candidate ∈ parameters
  · simp [insertParameter, present]
    intro equal
    subst candidate
    exact present
  · simp [insertParameter, present]

private theorem mem_foldl_insertParameter_iff
    (parameter : TypeParameterId)
    (parameters values : List TypeParameterId) :
    parameter ∈ values.foldl insertParameter parameters ↔
      parameter ∈ parameters ∨ parameter ∈ values := by
  induction values generalizing parameters with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction,
        mem_insertParameter_iff parameter head parameters]
      simp only [List.mem_cons]
      constructor
      · rintro ((member | equal) | tail_member)
        · exact .inl member
        · exact .inr (.inl equal)
        · exact .inr (.inr tail_member)
      · rintro (member | equal | tail_member)
        · exact .inl (.inl member)
        · exact .inl (.inr equal)
        · exact .inr tail_member

private theorem mem_appendVariables_iff
    (metavariable : TypeVarId) (variables : List TypeVarId) (type : Ty) :
    metavariable ∈ appendVariables variables type ↔
      metavariable ∈ variables ∨ metavariable ∈ type.freeVariables := by
  exact mem_foldl_insertVariable_iff metavariable variables type.freeVariables

private theorem mem_foldl_appendVariables_iff
    (metavariable : TypeVarId) (variables : List TypeVarId)
    (types : List Ty) :
    metavariable ∈ types.foldl appendVariables variables ↔
      metavariable ∈ variables ∨
        ∃ type, type ∈ types ∧ metavariable ∈ type.freeVariables := by
  induction types generalizing variables with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction,
        mem_appendVariables_iff metavariable variables head]
      simp only [List.mem_cons]
      constructor
      · rintro ((member | occurs) | ⟨type, type_mem, type_occurs⟩)
        · exact .inl member
        · exact .inr ⟨head, .inl rfl, occurs⟩
        · exact .inr ⟨type, .inr type_mem, type_occurs⟩
      · rintro (member | ⟨type, type_mem, type_occurs⟩)
        · exact .inl (.inl member)
        · rcases type_mem with rfl | type_mem
          · exact .inl (.inr type_occurs)
          · exact .inr ⟨type, type_mem, type_occurs⟩

private theorem mem_appendParameters_iff
    (parameter : TypeParameterId) (parameters : List TypeParameterId)
    (type : Ty) :
    parameter ∈ appendParameters parameters type ↔
      parameter ∈ parameters ∨ TypeParameterOccurs parameter type := by
  induction type generalizing parameters with
  | «variable» | constructor | error =>
      simp [appendParameters, TypeParameterOccurs]
  | «parameter» candidate =>
      simpa [appendParameters, TypeParameterOccurs, eq_comm] using
        mem_insertParameter_iff parameter candidate parameters
  | application left right left_induction right_induction =>
      rw [appendParameters, right_induction, left_induction]
      simp [TypeParameterOccurs, or_assoc]
  | function domain codomain domain_induction codomain_induction =>
      rw [appendParameters, codomain_induction, domain_induction]
      simp [TypeParameterOccurs, or_assoc]
  | product left right left_induction right_induction =>
      rw [appendParameters, right_induction, left_induction]
      simp [TypeParameterOccurs, or_assoc]
  | mapping key value key_induction value_induction =>
      rw [appendParameters, value_induction, key_induction]
      simp [TypeParameterOccurs, or_assoc]
  | proxy inner induction | comptime inner induction =>
      simpa [appendParameters, TypeParameterOccurs] using induction parameters

private theorem mem_foldl_appendParameters_iff
    (parameter : TypeParameterId) (parameters : List TypeParameterId)
    (types : List Ty) :
    parameter ∈ types.foldl appendParameters parameters ↔
      parameter ∈ parameters ∨
        ∃ type, type ∈ types ∧ TypeParameterOccurs parameter type := by
  induction types generalizing parameters with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction,
        mem_appendParameters_iff parameter parameters head]
      simp only [List.mem_cons]
      constructor
      · rintro ((member | occurs) | ⟨type, type_mem, type_occurs⟩)
        · exact .inl member
        · exact .inr ⟨head, .inl rfl, occurs⟩
        · exact .inr ⟨type, .inr type_mem, type_occurs⟩
      · rintro (member | ⟨type, type_mem, type_occurs⟩)
        · exact .inl (.inl member)
        · rcases type_mem with rfl | type_mem
          · exact .inl (.inr type_occurs)
          · exact .inr ⟨type, type_mem, type_occurs⟩

/-- A flexible binder occurs in one predicate type position. -/
def VariableOccursInPredicate (metavariable : TypeVarId)
    (predicate : Predicate) : Prop :=
  metavariable ∈ predicate.subject.freeVariables ∨
    ∃ argument, argument ∈ predicate.arguments ∧
      metavariable ∈ argument.freeVariables

/-- A rigid binder occurs in one predicate type position. -/
def ParameterOccursInPredicate (parameter : TypeParameterId)
    (predicate : Predicate) : Prop :=
  TypeParameterOccurs parameter predicate.subject ∨
    ∃ argument, argument ∈ predicate.arguments ∧
      TypeParameterOccurs parameter argument

theorem mem_predicateVariables_iff
    {metavariable : TypeVarId} {predicate : Predicate} :
    metavariable ∈ predicateVariables predicate ↔
      VariableOccursInPredicate metavariable predicate := by
  exact mem_foldl_appendVariables_iff metavariable
    predicate.subject.freeVariables predicate.arguments |>.trans (by
      simp [VariableOccursInPredicate])

theorem mem_predicateParameters_iff
    {parameter : TypeParameterId} {predicate : Predicate} :
    parameter ∈ predicateParameters predicate ↔
      ParameterOccursInPredicate parameter predicate := by
  exact mem_foldl_appendParameters_iff parameter
    (appendParameters [] predicate.subject) predicate.arguments |>.trans (by
      rw [mem_appendParameters_iff]
      simp [ParameterOccursInPredicate])

private theorem mem_foldl_predicateVariables_iff
    (metavariable : TypeVarId) (variables : List TypeVarId)
    (predicates : List Predicate) :
    metavariable ∈ predicates.foldl
        (fun collected predicate =>
          (predicateVariables predicate).foldl insertVariable collected)
        variables ↔
      metavariable ∈ variables ∨
        ∃ predicate, predicate ∈ predicates ∧
          metavariable ∈ predicateVariables predicate := by
  induction predicates generalizing variables with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction,
        mem_foldl_insertVariable_iff metavariable variables
          (predicateVariables head)]
      simp only [List.mem_cons]
      constructor
      · rintro ((member | occurs) | ⟨predicate, predicate_mem,
          predicate_occurs⟩)
        · exact .inl member
        · exact .inr ⟨head, .inl rfl, occurs⟩
        · exact .inr ⟨predicate, .inr predicate_mem, predicate_occurs⟩
      · rintro (member | ⟨predicate, predicate_mem, predicate_occurs⟩)
        · exact .inl (.inl member)
        · rcases predicate_mem with rfl | predicate_mem
          · exact .inl (.inr predicate_occurs)
          · exact .inr ⟨predicate, predicate_mem, predicate_occurs⟩

private theorem mem_foldl_predicateParameters_iff
    (parameter : TypeParameterId) (parameters : List TypeParameterId)
    (predicates : List Predicate) :
    parameter ∈ predicates.foldl
        (fun collected predicate =>
          (predicateParameters predicate).foldl insertParameter collected)
        parameters ↔
      parameter ∈ parameters ∨
        ∃ predicate, predicate ∈ predicates ∧
          parameter ∈ predicateParameters predicate := by
  induction predicates generalizing parameters with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction,
        mem_foldl_insertParameter_iff parameter parameters
          (predicateParameters head)]
      simp only [List.mem_cons]
      constructor
      · rintro ((member | occurs) | ⟨predicate, predicate_mem,
          predicate_occurs⟩)
        · exact .inl member
        · exact .inr ⟨head, .inl rfl, occurs⟩
        · exact .inr ⟨predicate, .inr predicate_mem, predicate_occurs⟩
      · rintro (member | ⟨predicate, predicate_mem, predicate_occurs⟩)
        · exact .inl (.inl member)
        · rcases predicate_mem with rfl | predicate_mem
          · exact .inl (.inr predicate_occurs)
          · exact .inr ⟨predicate, predicate_mem, predicate_occurs⟩

/-- A rule's canonical flexible domain is exactly the binders occurring in its
head or one of its ordered where predicates. -/
theorem mem_ruleVariables_iff
    {metavariable : TypeVarId} {rule : ImplRule} :
    metavariable ∈ ruleVariables rule ↔
      metavariable ∈ predicateVariables rule.head ∨
        ∃ predicate, predicate ∈ rule.wherePredicates ∧
          metavariable ∈ predicateVariables predicate := by
  exact mem_foldl_predicateVariables_iff metavariable
    (predicateVariables rule.head) rule.wherePredicates

/-- A rule's canonical rigid domain is exactly the binders occurring in its
head or one of its ordered where predicates. -/
theorem mem_ruleParameters_iff
    {parameter : TypeParameterId} {rule : ImplRule} :
    parameter ∈ ruleParameters rule ↔
      parameter ∈ predicateParameters rule.head ∨
        ∃ predicate, predicate ∈ rule.wherePredicates ∧
          parameter ∈ predicateParameters predicate := by
  exact mem_foldl_predicateParameters_iff parameter
    (predicateParameters rule.head) rule.wherePredicates

theorem mem_ruleVariables_occurs_iff
    {metavariable : TypeVarId} {rule : ImplRule} :
    metavariable ∈ ruleVariables rule ↔
      VariableOccursInPredicate metavariable rule.head ∨
        ∃ predicate, predicate ∈ rule.wherePredicates ∧
          VariableOccursInPredicate metavariable predicate := by
  rw [mem_ruleVariables_iff]
  simp only [mem_predicateVariables_iff]

theorem mem_ruleParameters_occurs_iff
    {parameter : TypeParameterId} {rule : ImplRule} :
    parameter ∈ ruleParameters rule ↔
      ParameterOccursInPredicate parameter rule.head ∨
        ∃ predicate, predicate ∈ rule.wherePredicates ∧
          ParameterOccursInPredicate parameter predicate := by
  rw [mem_ruleParameters_iff]
  simp only [mem_predicateParameters_iff]

/-- A fresh-variable lower bound covering the entire implementation rule. -/
def ruleNextVariable (rule : ImplRule) : Nat :=
  rule.wherePredicates.foldl
    (fun next predicate => max next (predicateNextVariable predicate))
    (predicateNextVariable rule.head)

private def fresheningSubstitution :
    List TypeVarId → Nat → Substitution × Nat
  | [], next => ([], next)
  | metavariable :: variables, next =>
      let (rest, finalNext) := fresheningSubstitution variables (next + 1)
      ((metavariable, .variable ⟨next⟩) :: rest, finalNext)

private def parameterFresheningSubstitution :
    List TypeParameterId → Nat → ParameterSubstitution × Nat
  | [], next => ([], next)
  | parameterId :: parameters, next =>
      let (rest, finalNext) :=
        parameterFresheningSubstitution parameters (next + 1)
      ((parameterId, .variable ⟨next⟩) :: rest, finalNext)

private structure FreshenedRule where
  rule : ImplRule
  parameterVariables : ParameterSubstitution
  variableVariables : Substitution

private def freshenRuleForParameters (parameters : List TypeParameterId)
    (rule : ImplRule) (goal : Predicate) : FreshenedRule :=
  let firstFresh := max (ruleNextVariable rule) (predicateNextVariable goal)
  let (parameterVariables, afterParameters) :=
    parameterFresheningSubstitution parameters firstFresh
  let parameterHead := applyParameterSubstitution parameterVariables rule.head
  let parameterWhere :=
    rule.wherePredicates.map (applyParameterSubstitution parameterVariables)
  let (substitution, _) :=
    fresheningSubstitution (ruleVariables rule) afterParameters
  {
    rule := {
      rule with
      head := applySubstitution substitution parameterHead
      wherePredicates := parameterWhere.map (applySubstitution substitution)
    }
    parameterVariables := parameterVariables.map fun entry =>
      (entry.1, substitution.apply entry.2)
    variableVariables := substitution
  }

/-- Instantiate rigid implementation parameters and freshen flexible variables
away from variables already present in both the goal and the stored rule. Each
mapping is shared across the head and every where predicate. -/
def freshenRuleFor (rule : ImplRule) (goal : Predicate) : ImplRule :=
  (freshenRuleForParameters (ruleParameters rule) rule goal).rule

private def argumentConstraints? : List Ty → List Ty → Option (List Constraint)
  | [], [] => some []
  | left :: lefts, right :: rights => do
      let rest ← argumentConstraints? lefts rights
      pure ({ left, right } :: rest)
  | _, _ => none

/-- Constraints for every type position of equal-trait, equal-arity heads. -/
def headConstraints? (implementation goal : Predicate) :
    Option (List Constraint) :=
  if implementation.trait = goal.trait then do
    let arguments ← argumentConstraints?
      implementation.arguments goal.arguments
    pure ({ left := implementation.subject, right := goal.subject } :: arguments)
  else
    none

/-- A successful typed matcher result paired with the canonical simultaneous
rule substitution used by the proof-facing certificate checker. -/
structure CertifiedHeadMatch where
  headMatch : HeadMatch
  substitution : RuleMatchSubstitution
  deriving Repr, BEq, DecidableEq

/-- A proof-facing successful rule match.  The domains are in the canonical
collector order and the equations are checked against the original rule, not
trusted from the unifier's internal state. -/
inductive HeadMatchCertificate (rule : ImplRule) (goal : Predicate)
    (premises : List Predicate) (substitution : RuleMatchSubstitution) : Prop where
  | intro
      (parameters_nodup : (ruleParameters rule).Nodup)
      (variables_nodup : (ruleVariables rule).Nodup)
      (parameter_domain : substitution.parameters.map Prod.fst =
        ruleParameters rule)
      (variable_domain : substitution.variables.domain = ruleVariables rule)
      (head_eq : substitution.applyPredicate rule.head = goal)
      (premises_eq : rule.wherePredicates.map substitution.applyPredicate =
        premises) :
      HeadMatchCertificate rule goal premises substitution

private def canonicalParameterSubstitution (rule : ImplRule)
    (callerSubstitution : ParameterSubstitution) : ParameterSubstitution :=
  (ruleParameters rule).map fun parameter =>
    (parameter, callerSubstitution.lookup? parameter |>.getD
      (.parameter parameter))

private def canonicalVariableSubstitution (rule : ImplRule)
    (freshenedVariables unifier : Substitution) : Substitution :=
  (ruleVariables rule).map fun metavariable =>
    let freshened := freshenedVariables.lookup? metavariable |>.getD
      (.variable metavariable)
    (metavariable, unifier.apply freshened)

/-- Certified core of detailed implementation-head matching.  Unification is
used only to propose replacements; the canonical simultaneous substitution is
then replayed against the original rule and its head is checked exactly. -/
def matchImplHeadWithParametersCertified? (parameters : List TypeParameterId)
    (rule : ImplRule) (goal : Predicate) : Option CertifiedHeadMatch :=
  let freshened := freshenRuleForParameters parameters rule goal
  match headConstraints? freshened.rule.head goal with
  | none => none
  | some constraints =>
      match (Unification.unify constraints).toOption with
      | none => none
      | some unifier =>
          let goalVariables := predicateVariables goal
          if unifier.domain.any goalVariables.contains then
            none
          else
            if applySubstitution unifier freshened.rule.head = goal then
              let callerParameters :=
                freshened.parameterVariables.map fun entry =>
                  (entry.1, unifier.apply entry.2)
              let canonical : RuleMatchSubstitution := {
                parameters := canonicalParameterSubstitution rule callerParameters
                variables := canonicalVariableSubstitution rule
                  freshened.variableVariables unifier
              }
              if canonical.applyPredicate rule.head = goal then
                let premises := rule.wherePredicates.map canonical.applyPredicate
                some {
                  headMatch := {
                    parameterSubstitution := callerParameters
                    wherePredicates := premises
                  }
                  substitution := canonical
                }
              else
                none
            else
              none

/-- Freshen a caller-supplied canonical parameter sequence, match the complete
implementation head, and expose both its inferred parameter substitution and
instantiated where predicates.  The public result shape remains compatible;
the proof-facing simultaneous substitution is available from the certified
variant and the soundness theorem below.  The legacy sequential head check is
retained, then the canonical simultaneous substitution is replayed as an
additional check, so certification can only narrow successful proposals.  The
detailed `parameterSubstitution` remains in caller-supplied order and may
differ from the certificate's canonical rigid domain when the caller includes
unused or duplicate parameters. -/
def matchImplHeadWithParameters? (parameters : List TypeParameterId)
    (rule : ImplRule) (goal : Predicate) : Option HeadMatch :=
  (matchImplHeadWithParametersCertified? parameters rule goal).map
    (·.headMatch)

/-- Every successful certified matcher execution carries a canonical exact
domain and equations checked against the original implementation rule. -/
theorem matchImplHeadWithParametersCertified?_certificate
    {parameters : List TypeParameterId} {rule : ImplRule} {goal : Predicate}
    {result : CertifiedHeadMatch}
    (matched : matchImplHeadWithParametersCertified? parameters rule goal =
      some result) :
    HeadMatchCertificate rule goal result.headMatch.wherePredicates
      result.substitution := by
  let freshened := freshenRuleForParameters parameters rule goal
  change (match headConstraints? freshened.rule.head goal with
    | none => none
    | some constraints =>
        match (Unification.unify constraints).toOption with
        | none => none
        | some unifier =>
            let goalVariables := predicateVariables goal
            if unifier.domain.any goalVariables.contains then
              none
            else
              if applySubstitution unifier freshened.rule.head = goal then
                let callerParameters :=
                  freshened.parameterVariables.map fun entry =>
                    (entry.1, unifier.apply entry.2)
                let canonical : RuleMatchSubstitution := {
                  parameters := canonicalParameterSubstitution rule
                    callerParameters
                  variables := canonicalVariableSubstitution rule
                    freshened.variableVariables unifier
                }
                if canonical.applyPredicate rule.head = goal then
                  let premises :=
                    rule.wherePredicates.map canonical.applyPredicate
                  some {
                    headMatch := {
                      parameterSubstitution := callerParameters
                      wherePredicates := premises
                    }
                    substitution := canonical
                  }
                else
                  none
              else
                none) = some result at matched
  cases constraints_eq : headConstraints? freshened.rule.head goal with
  | none => simp [constraints_eq] at matched
  | some constraints =>
      cases unifier_eq : (Unification.unify constraints).toOption with
      | none => simp [constraints_eq, unifier_eq] at matched
      | some unifier =>
          cases binds_eq :
              unifier.domain.any (predicateVariables goal).contains with
          | true => simp [constraints_eq, unifier_eq, binds_eq] at matched
          | false =>
            by_cases proposed_eq :
                applySubstitution unifier freshened.rule.head = goal
            · let callerParameters :=
                freshened.parameterVariables.map fun entry =>
                  (entry.1, unifier.apply entry.2)
              let canonical : RuleMatchSubstitution := {
                parameters := canonicalParameterSubstitution rule callerParameters
                variables := canonicalVariableSubstitution rule
                  freshened.variableVariables unifier
              }
              by_cases head_eq : canonical.applyPredicate rule.head = goal
              · have result_eq : CertifiedHeadMatch.mk
                    {
                      parameterSubstitution := callerParameters
                      wherePredicates :=
                        rule.wherePredicates.map canonical.applyPredicate
                    }
                    canonical = result := by
                  simpa [constraints_eq, unifier_eq, binds_eq, proposed_eq,
                    callerParameters, canonical, head_eq] using matched
                subst result
                apply HeadMatchCertificate.intro
                  (ruleParameters_nodup rule) (ruleVariables_nodup rule)
                · simp [canonical, canonicalParameterSubstitution,
                    List.map_map, Function.comp_def]
                · simp [canonical, canonicalVariableSubstitution,
                    Substitution.domain, List.map_map, Function.comp_def]
                · exact head_eq
                · rfl
              · exfalso
                simp [constraints_eq, unifier_eq, binds_eq, proposed_eq,
                  callerParameters, canonical, head_eq] at matched
            · simp [constraints_eq, unifier_eq, binds_eq, proposed_eq] at matched

/-- The compatibility projection of a certified match retains the same
proof-facing certificate. -/
theorem matchImplHeadWithParameters?_certificate
    {parameters : List TypeParameterId} {rule : ImplRule} {goal : Predicate}
    {result : HeadMatch}
    (matched : matchImplHeadWithParameters? parameters rule goal = some result) :
    ∃ substitution,
      HeadMatchCertificate rule goal result.wherePredicates substitution := by
  unfold matchImplHeadWithParameters? at matched
  cases certified_eq : matchImplHeadWithParametersCertified? parameters rule goal with
  | none => simp [certified_eq] at matched
  | some certified =>
      simp only [certified_eq, Option.map_some, Option.some.injEq] at matched
      subst result
      exact ⟨certified.substitution,
        matchImplHeadWithParametersCertified?_certificate certified_eq⟩

/-- Freshen, match the complete implementation head, and instantiate its where
predicates. A trait/arity mismatch or unification failure is not a candidate. -/
def matchImplHead? (rule : ImplRule) (goal : Predicate) :
    Option (List Predicate) :=
  (matchImplHeadWithParameters? (ruleParameters rule) rule goal).map
    (·.wherePredicates)

/-- Generic resolver head matching exposes the same exact simultaneous
substitution certificate as detailed matching. -/
theorem matchImplHead?_certificate
    {rule : ImplRule} {goal : Predicate} {premises : List Predicate}
    (matched : matchImplHead? rule goal = some premises) :
    ∃ substitution, HeadMatchCertificate rule goal premises substitution := by
  unfold matchImplHead? at matched
  cases detailed_eq :
      matchImplHeadWithParameters? (ruleParameters rule) rule goal with
  | none => simp [detailed_eq] at matched
  | some detailed =>
      simp only [detailed_eq, Option.map_some, Option.some.injEq] at matched
      subst premises
      exact matchImplHeadWithParameters?_certificate detailed_eq

/-- Typed head matcher accepted by the generic tabled-resolution kernel. -/
def headMatcher : TraitResolution.HeadMatcher TraitId Ty ImplId :=
  matchImplHead?

/-- Build a typed resolution program in declaration order. -/
def programOfRules (rules : List ImplRule) : Program :=
  { rules, matchHead := headMatcher }

/-- Run typed trait resolution with an implementation-chain depth bound. -/
def resolve (rules : List ImplRule) (maxDepth : Nat) (goal : Predicate) :
    TraitResolution.Report TraitId Ty ImplId :=
  TraitResolution.resolve (programOfRules rules) maxDepth goal

end Solcore.Frontend.TypedTraitResolution
