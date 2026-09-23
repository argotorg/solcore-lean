import Solcore.SourceSemantics.Program
import Solcore.SourceSemantics.Dynamic.Value

/-!
Runtime closure of source-level trait evidence.

Generic bodies may retain assumption leaves.  Invocation supplies a dictionary
environment which closes those leaves with concrete, assumption-free evidence.
The resulting tree selects an implementation method by stable catalog identity;
no trait search, overlap ranking, or evaluator result occurs in these rules.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference

/-- First-match lookup in a runtime evidence environment. -/
inductive EvidenceEnvironment.LooksUp :
    EvidenceEnvironment → ProgramPredicate → TraitEvidence → Prop where
  | head {environment : EvidenceEnvironment}
      {goal : ProgramPredicate} {evidence : TraitEvidence} :
      EvidenceEnvironment.LooksUp ((goal, evidence) :: environment)
        goal evidence
  | tail {environment : EvidenceEnvironment}
      {goal otherGoal : ProgramPredicate}
      {evidence otherEvidence : TraitEvidence}
      (different : otherGoal ≠ goal)
      (found : EvidenceEnvironment.LooksUp environment goal evidence) :
      EvidenceEnvironment.LooksUp
        ((otherGoal, otherEvidence) :: environment) goal evidence

namespace EvidenceEnvironment.LooksUp

/-- First-match evidence lookup is functional. -/
theorem functional
    {environment : EvidenceEnvironment} {goal : ProgramPredicate}
    {left right : TraitEvidence}
    (leftFound : EvidenceEnvironment.LooksUp environment goal left)
    (rightFound : EvidenceEnvironment.LooksUp environment goal right) :
    left = right := by
  induction leftFound generalizing right with
  | head =>
      cases rightFound with
      | head => rfl
      | tail different _ => exact False.elim (different rfl)
  | tail different _ induction =>
      cases rightFound with
      | head => exact False.elim (different rfl)
      | tail _ found => exact induction found

end EvidenceEnvironment.LooksUp

/-- Reflexive containment in a semantic evidence tree.  Implementation
premises are runtime dictionaries available to the selected method body. -/
inductive EvidenceSubtree : TraitEvidence → TraitEvidence → Prop where
  | self (evidence : TraitEvidence) : EvidenceSubtree evidence evidence
  | premise
      {goal : ProgramPredicate} {implementation : ProgramImplId}
      {premises : List TraitEvidence} {premise selected : TraitEvidence}
      (member : premise ∈ premises)
      (contains : EvidenceSubtree premise selected) :
      EvidenceSubtree (.implementation goal implementation premises) selected

/-- Every first-match entry of `derived` originates either in the lexical
caller dictionary or in one of the concrete evidence trees selected at this
call site.  This prevents method invocation from postulating an unrelated
closed proof merely to satisfy its generic context. -/
def EvidenceEnvironment.DerivedFrom
    (derived caller : EvidenceEnvironment)
    (roots : List TraitEvidence) : Prop :=
  ∀ goal evidence, derived.LooksUp goal evidence →
    caller.LooksUp goal evidence ∨
      ∃ root,
        root ∈ roots ∧ EvidenceSubtree root evidence ∧ evidence.goal = goal

/-- One dictionary entry has an explicit, non-forgeable origin: it is either
the caller's first-match entry for the same goal or a subtree of one of the
evidence roots produced at this call site. -/
inductive EvidenceEntryOriginates
    (caller : EvidenceEnvironment) (roots : List TraitEvidence) :
    ProgramPredicate → TraitEvidence → Prop where
  | caller
      {goal : ProgramPredicate} {evidence : TraitEvidence}
      (found : caller.LooksUp goal evidence) :
      EvidenceEntryOriginates caller roots goal evidence
  | root
      {goal : ProgramPredicate} {evidence root : TraitEvidence}
      (member : root ∈ roots)
      (subtree : EvidenceSubtree root evidence)
      (goal_eq : evidence.goal = goal) :
      EvidenceEntryOriginates caller roots goal evidence

/-- Exact source-order assembly of a callee dictionary.  Unlike the weaker
`DerivedFrom` property, this relation also fixes the environment's length,
goal order, and multiplicity to the callee's declared assumptions. -/
inductive EvidenceEnvironment.AssembledFrom
    (caller : EvidenceEnvironment) (roots : List TraitEvidence) :
    List ProgramPredicate → EvidenceEnvironment → Prop where
  | nil : EvidenceEnvironment.AssembledFrom caller roots [] []
  | cons
      {goal : ProgramPredicate} {goals : List ProgramPredicate}
      {evidence : TraitEvidence} {environment : EvidenceEnvironment}
      (head : EvidenceEntryOriginates caller roots goal evidence)
      (tail : EvidenceEnvironment.AssembledFrom caller roots goals environment) :
      EvidenceEnvironment.AssembledFrom caller roots (goal :: goals)
        ((goal, evidence) :: environment)

namespace EvidenceEnvironment.DerivedFrom

theorem empty (caller : EvidenceEnvironment) (roots : List TraitEvidence) :
    EvidenceEnvironment.DerivedFrom [] caller roots := by
  intro goal evidence lookup
  cases lookup

theorem caller
    {environment caller : EvidenceEnvironment} {roots : List TraitEvidence}
    (same : environment = caller) :
    EvidenceEnvironment.DerivedFrom environment caller roots := by
  subst environment
  intro goal evidence lookup
  exact .inl lookup

end EvidenceEnvironment.DerivedFrom

namespace EvidenceEnvironment.AssembledFrom

theorem length_eq
    {caller : EvidenceEnvironment} {roots : List TraitEvidence}
    {goals : List ProgramPredicate} {environment : EvidenceEnvironment}
    (assembled : EvidenceEnvironment.AssembledFrom caller roots goals
      environment) :
    environment.length = goals.length := by
  induction assembled with
  | nil => rfl
  | cons _ _ induction => simp [induction]

theorem derived
    {caller : EvidenceEnvironment} {roots : List TraitEvidence}
    {goals : List ProgramPredicate} {environment : EvidenceEnvironment}
    (assembled : EvidenceEnvironment.AssembledFrom caller roots goals
      environment) :
    environment.DerivedFrom caller roots := by
  intro goal evidence found
  induction assembled with
  | nil => cases found
  | @cons headGoal goals headEvidence tailEnvironment head tail induction =>
      cases found with
      | head =>
          cases head with
          | caller callerFound => exact .inl callerFound
          | root member subtree goalEq =>
              exact .inr ⟨_, member, subtree, goalEq⟩
      | tail different rest => exact induction rest

end EvidenceEnvironment.AssembledFrom

/-- Every runtime dictionary entry is a closed proof under the complete rule
catalog. -/
def EvidenceEnvironment.Valid (rules : List ProgramImplRule)
    (environment : EvidenceEnvironment) : Prop :=
  ∀ goal evidence, environment.LooksUp goal evidence →
    EvidenceValid [] rules goal evidence

/-- A runtime dictionary is closed and supplies every generic assumption of
the body whose code is about to execute. -/
def EvidenceEnvironment.Covers (context : Context)
    (environment : EvidenceEnvironment) : Prop :=
  environment.Valid context.signatures.resolutionRules ∧
    ∀ predicate, predicate ∈ context.assumptions →
      ∃ evidence, environment.LooksUp predicate evidence

/-- Replace every assumption leaf in retained semantic evidence with the
concrete evidence supplied by the invocation environment. -/
inductive EvidenceCloses (environment : EvidenceEnvironment) :
    TraitEvidence → TraitEvidence → Prop where
  | assumption
      {goal : ProgramPredicate} {evidence : TraitEvidence}
      (found : environment.LooksUp goal evidence) :
      EvidenceCloses environment (.assumption goal) evidence
  | implementation
      {goal : ProgramPredicate} {implementation : ProgramImplId}
      {openPremises closedPremises : List TraitEvidence}
      (premises : Forall₂ (EvidenceCloses environment)
        openPremises closedPremises) :
      EvidenceCloses environment
        (.implementation goal implementation openPremises)
        (.implementation goal implementation closedPremises)

namespace EvidenceCloses

/-- Closing dictionaries never changes the goal proved at the root. -/
theorem goal_eq
    {rules : List ProgramImplRule} {environment : EvidenceEnvironment}
    {openEvidence closedEvidence : TraitEvidence}
    (environmentValid : environment.Valid rules)
    (closes : EvidenceCloses environment openEvidence closedEvidence) :
    closedEvidence.goal = openEvidence.goal := by
  cases closes with
  | assumption found => exact (environmentValid _ _ found).evidence_goal_eq
  | implementation => rfl

end EvidenceCloses

/-- One stable requirement closes to an assumption-free semantic proof.  The
same ledger entry supplies the predicate, retained representation, and source
validity; a separate closed validity premise checks the invocation dictionary. -/
inductive RequirementProducesEvidence
    (context : Context) (environment : EvidenceEnvironment) :
    RequirementId → ProgramPredicate → TraitEvidence → Prop where
  | intro
      {id : RequirementId} {predicate : ProgramPredicate}
      {requirement : SolvedRequirement}
      {openEvidence closedEvidence : TraitEvidence}
      (contains : ContainsRequirement context id requirement)
      (predicate_eq : requirement.predicate = predicate)
      (representation : PredicateEvidenceRepresents requirement.evidence
        openEvidence)
      (retained_valid : SolvedRequirementValid context requirement)
      (closes : EvidenceCloses environment openEvidence closedEvidence)
      (closed_valid : EvidenceValid [] context.signatures.resolutionRules
        predicate closedEvidence) :
      RequirementProducesEvidence context environment id predicate
        closedEvidence

namespace RequirementProducesEvidence

theorem requirement_valid
    {context : Context} {environment : EvidenceEnvironment}
    {id : RequirementId} {predicate : ProgramPredicate}
    {evidence : TraitEvidence}
    (produces : RequirementProducesEvidence context environment id predicate
      evidence) :
    RequirementProves context id predicate := by
  cases produces with
  | intro contains predicate_eq _ retained_valid _ _ =>
      exact ⟨_, contains, predicate_eq, retained_valid⟩

theorem evidence_goal_eq
    {context : Context} {environment : EvidenceEnvironment}
    {id : RequirementId} {predicate : ProgramPredicate}
    {evidence : TraitEvidence}
    (produces : RequirementProducesEvidence context environment id predicate
      evidence) :
    evidence.goal = predicate := by
  cases produces with
  | intro _ _ _ _ _ closed_valid => exact closed_valid.evidence_goal_eq

theorem closed_valid
    {context : Context} {environment : EvidenceEnvironment}
    {id : RequirementId} {predicate : ProgramPredicate}
    {evidence : TraitEvidence}
    (produces : RequirementProducesEvidence context environment id predicate
      evidence) :
    EvidenceValid [] context.signatures.resolutionRules predicate evidence := by
  cases produces with
  | intro _ _ _ _ _ valid => exact valid

end RequirementProducesEvidence

/-- Close a source-ordered requirement sequence into the callee dictionary
environment with the same predicate order and multiplicity. -/
inductive RequirementsProduceEnvironment
    (context : Context) (callerEnvironment : EvidenceEnvironment) :
    List RequirementId → List ProgramPredicate →
      EvidenceEnvironment → Prop where
  | nil : RequirementsProduceEnvironment context callerEnvironment [] [] []
  | cons
      {id : RequirementId} {ids : List RequirementId}
      {predicate : ProgramPredicate} {predicates : List ProgramPredicate}
      {evidence : TraitEvidence} {environment : EvidenceEnvironment}
      (head : RequirementProducesEvidence context callerEnvironment id
        predicate evidence)
      (tail : RequirementsProduceEnvironment context callerEnvironment ids
        predicates environment) :
      RequirementsProduceEnvironment context callerEnvironment
        (id :: ids) (predicate :: predicates)
        ((predicate, evidence) :: environment)

namespace RequirementsProduceEnvironment

theorem length_eq
    {context : Context} {callerEnvironment : EvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate}
    {environment : EvidenceEnvironment}
    (produces : RequirementsProduceEnvironment context callerEnvironment ids
      predicates environment) :
    ids.length = predicates.length ∧
      predicates.length = environment.length := by
  induction produces with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ induction => exact ⟨by simp [induction.1], by simp [induction.2]⟩

/-- Every environment produced from closed requirement evidence is valid. -/
theorem valid
    {context : Context} {callerEnvironment : EvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate}
    {environment : EvidenceEnvironment}
    (produces : RequirementsProduceEnvironment context callerEnvironment ids
      predicates environment) :
    environment.Valid context.signatures.resolutionRules := by
  induction produces with
  | nil =>
      intro goal evidence found
      cases found
  | @cons id ids predicate predicates evidence environment head tail induction =>
      intro goal selected found
      cases found with
      | head => exact head.closed_valid
      | tail _ tailFound => exact induction _ _ tailFound

end RequirementsProduceEnvironment

/-- A concrete evidence root selects one source implementation method by
stable implementation identity and exact method spelling. -/
inductive EvidenceSelectsMethod (program : Program) :
    TraitEvidence → String → MethodDefinition → Prop where
  | source
      {goal : ProgramPredicate}
      {implementation : ProgramImplementationSignature}
      {premises : List TraitEvidence}
      {method : ProgramImplMethodSignature}
      {definition : MethodDefinition}
      {methodName : String}
      (implementation_mem : implementation ∈
        program.signatures.implementations)
      (goal_trait : goal.trait = implementation.head.trait)
      (method_mem : method ∈ implementation.methods)
      (method_name : method.name = methodName)
      (definition_mem : definition ∈ program.methods)
      (definition_id : definition.id = method.id) :
      EvidenceSelectsMethod program
        (.implementation goal (.declaration implementation.id) premises)
        methodName definition

/-- Resolve a requirement through the invocation dictionary and select the
source method named by an operator or coercion profile. -/
inductive RequirementSelectsMethod
    (program : Program) (context : Context)
    (environment : EvidenceEnvironment) :
    RequirementId → ProgramPredicate → String →
      MethodDefinition → TraitEvidence → Prop where
  | intro
      {id : RequirementId} {predicate : ProgramPredicate}
      {methodName : String} {definition : MethodDefinition}
      {evidence : TraitEvidence}
      (produces : RequirementProducesEvidence context environment id
        predicate evidence)
      (selects : EvidenceSelectsMethod program evidence methodName definition) :
      RequirementSelectsMethod program context environment id predicate
        methodName definition evidence

end Solcore.SourceSemantics.Dynamic
