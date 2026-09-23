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

/-- Freshen a caller-supplied canonical parameter sequence, match the complete
implementation head, and expose both its inferred parameter substitution and
instantiated where predicates.  A trait/arity mismatch, unification failure,
or attempt to bind a caller-owned goal variable is not a match. -/
def matchImplHeadWithParameters? (parameters : List TypeParameterId)
    (rule : ImplRule) (goal : Predicate) : Option HeadMatch := do
  let freshened := freshenRuleForParameters parameters rule goal
  let constraints ← headConstraints? freshened.rule.head goal
  let substitution ← (Unification.unify constraints).toOption
  let goalVariables := predicateVariables goal
  if substitution.domain.any goalVariables.contains then
    none
  else
    let matchedHead := applySubstitution substitution freshened.rule.head
    if matchedHead != goal then
      none
    else
      pure {
        parameterSubstitution := freshened.parameterVariables.map fun entry =>
          (entry.1, substitution.apply entry.2)
        wherePredicates := freshened.rule.wherePredicates.map
          (applySubstitution substitution)
      }

/-- Freshen, match the complete implementation head, and instantiate its where
predicates. A trait/arity mismatch or unification failure is not a candidate. -/
def matchImplHead? (rule : ImplRule) (goal : Predicate) :
    Option (List Predicate) :=
  (matchImplHeadWithParameters? (ruleParameters rule) rule goal).map
    (·.wherePredicates)

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
