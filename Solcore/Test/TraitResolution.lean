import Solcore.Frontend.TraitResolution

set_option autoImplicit false

namespace Tests.TraitResolution

open Solcore.Frontend.TraitResolution

inductive TestTrait where
  | show
  | equality
  | loop
  deriving Repr, BEq, DecidableEq

inductive TestTy where
  | int
  | bool
  | wildcard
  deriving Repr, BEq, DecidableEq

abbrev TestPredicate := Predicate TestTrait TestTy
abbrev TestRule := ImplRule TestTrait TestTy Nat
abbrev TestProgram := Program TestTrait TestTy Nat

private abbrev obligation (trait : TestTrait) (subject : TestTy) : TestPredicate :=
  { trait := trait, subject := subject, arguments := [] }

private abbrev eqInt := obligation .equality .int
private abbrev eqBool := obligation .equality .bool
private abbrev showInt := obligation .show .int
private abbrev showBool := obligation .show .bool
private abbrev loopInt := obligation .loop .int

private abbrev exactProgram (rules : List TestRule) : TestProgram :=
  { rules := rules, matchHead := exactHeadMatcher }

private abbrev eqIntRule (id : Nat := 0) : TestRule :=
  { id := id, head := eqInt, wherePredicates := [] }

private abbrev showIntRule (id : Nat := 1) (premises : List TestPredicate := [eqInt]) : TestRule :=
  { id := id, head := showInt, wherePredicates := premises }

theorem exact_head_and_where_predicate_produce_nested_evidence :
    (match (resolve (exactProgram [eqIntRule, showIntRule]) 2 showInt).outcome with
    | .success (.byImpl actualGoal 1 [.byImpl actualPremise 0 []]) =>
        actualGoal == showInt && actualPremise == eqInt
    | _ => false) = true := by
  decide

theorem missing_impl_is_a_definite_no_solution :
    (resolve (exactProgram [eqIntRule]) 2 showBool).outcome ==
      .noSolution := by
  rfl

theorem exhausted_depth_is_inconclusive :
    (resolve (exactProgram [eqIntRule, showIntRule]) 1 showInt).outcome ==
      .inconclusive (.depthLimit eqInt) := by
  rfl

private abbrev loopRule : TestRule :=
  { id := 4, head := loopInt, wherePredicates := [loopInt] }

theorem an_active_recursive_goal_is_an_inconclusive_cycle :
    (resolve (exactProgram [loopRule]) 8 loopInt).outcome ==
      .inconclusive (.cycle loopInt) := by
  rfl

theorem two_successful_impls_are_explicitly_ambiguous :
    (resolve (exactProgram [showIntRule 10 [], showIntRule 11 []]) 1 showInt).outcome ==
      .inconclusive (.ambiguous showInt 10 11) := by
  rfl

theorem one_success_does_not_hide_an_inconclusive_competitor :
    (resolve (exactProgram [showIntRule 10 [], showIntRule 11 [loopInt], loopRule]) 8 showInt).outcome ==
      .inconclusive (.incompleteCandidates showInt 10) := by
  rfl

private abbrev sharedPremiseProgram : TestProgram :=
  exactProgram [eqIntRule, showIntRule 1 [eqInt, eqInt]]

theorem completed_goals_are_tabled_across_sibling_predicates :
    ((match (resolve sharedPremiseProgram 2 showInt).outcome with
      | .success (.byImpl actualGoal 1 [
          .byImpl firstPremise 0 [],
          .byImpl secondPremise 0 []]) =>
            actualGoal == showInt && firstPremise == eqInt && secondPremise == eqInt
      | _ => false) &&
    (resolve sharedPremiseProgram 2 showInt).statistics.expandedGoals == 2 &&
    (resolve sharedPremiseProgram 2 showInt).statistics.memoHits == 1) = true := by
  decide

private abbrev instantiateWildcard (replacement : TestTy)
    (predicate : TestPredicate) : TestPredicate :=
  { predicate with
    subject := if predicate.subject == .wildcard then replacement else predicate.subject
    arguments := predicate.arguments.map fun argument =>
      if argument == .wildcard then replacement else argument }

/-- Tiny stand-in for the forthcoming unification boundary: a wildcard impl head
matches any subject and instantiates every wildcard in its where predicates. -/
private abbrev wildcardMatcher : HeadMatcher TestTrait TestTy Nat :=
  fun rule goal =>
    if rule.head.trait == goal.trait && rule.head.arguments == goal.arguments then
      if rule.head.subject == .wildcard then
        some (rule.wherePredicates.map (instantiateWildcard goal.subject))
      else if rule.head.subject == goal.subject then
        some rule.wherePredicates
      else
        none
    else
      none

private abbrev genericShowRule : TestRule :=
  { id := 20
    head := obligation .show .wildcard
    wherePredicates := [obligation .equality .wildcard] }

private abbrev wildcardProgram : TestProgram :=
  { rules := [eqIntRule 21, genericShowRule], matchHead := wildcardMatcher }

theorem a_head_matcher_can_instantiate_where_predicates :
    ((match (resolve wildcardProgram 2 showInt).outcome with
      | .success (.byImpl actualGoal 20 [.byImpl actualPremise 21 []]) =>
          actualGoal == showInt && actualPremise == eqInt
      | _ => false) &&
    (match (resolve wildcardProgram 2 showBool).outcome with
      | .noSolution => true
      | _ => false) &&
    eqBool == instantiateWildcard .bool (obligation .equality .wildcard)) = true := by
  decide

end Tests.TraitResolution
