import Solcore.SourceSemantics.TraitResolutionSoundness

set_option autoImplicit false

namespace Tests.TypedTraitResolution

open Solcore
open Solcore.Frontend
open Solcore.Frontend.TypedTraitResolution
open Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"typed_trait_resolution", by decide⟩], by decide⟩⟩

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨ownerModule, index⟩

private def equalityTrait := declaration 0
private def showTrait := declaration 1
private def convertTrait := declaration 2
private def boxType := declaration 3
private def equalityWordImpl := declaration 10
private def showBoxImpl := declaration 11
private def convertSameImpl := declaration 12
private def whereOnlyImpl := declaration 13

private def predicate (trait : TraitId) (subject : Ty)
    (arguments : List Ty := []) : Predicate :=
  { trait, subject, arguments }

private def equality (type : Ty) : Predicate :=
  predicate equalityTrait type

private def showPredicate (type : Ty) : Predicate :=
  predicate showTrait type

private def convert (source target : Ty) : Predicate :=
  predicate convertTrait source [target]

private def box (argument : Ty) : Ty :=
  Ty.nominal boxType [argument]

private def variable0 : Ty := .variable ⟨0⟩

private def showBoxParameter : TypeParameterId :=
  { owner := showBoxImpl, index := 0 }

private def showBoxParameterType : Ty :=
  .parameter showBoxParameter

private def equalityWordRule : ImplRule :=
  { id := equalityWordImpl
    head := equality .word
    wherePredicates := [] }

private def showBoxRule : ImplRule :=
  { id := showBoxImpl
    head := showPredicate (box showBoxParameterType)
    wherePredicates := [equality showBoxParameterType] }

private def convertSameRule : ImplRule :=
  { id := convertSameImpl
    head := convert variable0 variable0
    wherePredicates := [] }

private def whereOnlyParameter : TypeParameterId :=
  { owner := whereOnlyImpl, index := 0 }

private def whereOnlyRule : ImplRule :=
  { id := whereOnlyImpl
    head := equality .word
    wherePredicates := [convert (.parameter whereOnlyParameter) variable0] }

private def expectedFreshShowBoxRule : ImplRule :=
  { id := showBoxImpl
    head := showPredicate (box (.variable ⟨0⟩))
    wherePredicates := [equality (.variable ⟨0⟩)] }

example : freshenRuleFor showBoxRule (showPredicate (box .word)) =
    expectedFreshShowBoxRule := by
  rfl

example : matchImplHead? showBoxRule (showPredicate (box .word)) =
    some [equality .word] := by
  rfl

example : Solcore.SourceSemantics.ImplHeadInstantiates showBoxRule
    (showPredicate (box .word)) [equality .word] := by
  exact Solcore.SourceSemantics.TraitResolutionSoundness.matchImplHead?_sound
    (by rfl)

example : matchImplHeadWithParameters? [showBoxParameter] showBoxRule
    (showPredicate (box .word)) = some {
      parameterSubstitution := [(showBoxParameter, .word)]
      wherePredicates := [equality .word]
    } := by
  rfl

example : ∃ substitution, HeadMatchCertificate showBoxRule
    (showPredicate (box .word)) [equality .word] substitution := by
  exact matchImplHead?_certificate (by rfl)

example : ∃ substitution, HeadMatchCertificate showBoxRule
    (showPredicate (box .word)) [equality .word] substitution := by
  have matched : matchImplHeadWithParameters? [showBoxParameter] showBoxRule
      (showPredicate (box .word)) = some {
        parameterSubstitution := [(showBoxParameter, .word)]
        wherePredicates := [equality .word]
      } := by rfl
  exact matchImplHeadWithParameters?_certificate matched

example : ∃ substitution : RuleMatchSubstitution,
    substitution.parameters.map Prod.fst = [showBoxParameter] ∧
      substitution.variables.domain = [] ∧
      substitution.applyPredicate showBoxRule.head =
        showPredicate (box .word) ∧
      showBoxRule.wherePredicates.map substitution.applyPredicate =
        [equality .word] := by
  rcases matchImplHead?_certificate (rule := showBoxRule)
      (goal := showPredicate (box .word)) (premises := [equality .word])
      (by rfl) with ⟨substitution, certificate⟩
  cases certificate with
  | intro _ _ parameter_domain variable_domain head_eq premises_eq =>
      have parameters_eq : ruleParameters showBoxRule =
          [showBoxParameter] := by native_decide
      have variables_eq : ruleVariables showBoxRule = [] := by native_decide
      rw [parameters_eq] at parameter_domain
      rw [variables_eq] at variable_domain
      exact ⟨substitution, parameter_domain, variable_domain, head_eq,
        premises_eq⟩

example : matchImplHead? showBoxRule (equality (box .word)) = none := by
  rfl

example : matchImplHead? convertSameRule (convert .word .bool) = none := by
  rfl

example : matchImplHead? convertSameRule (convert .word .word) = some [] := by
  rfl

example : ∃ substitution : RuleMatchSubstitution,
    substitution.parameters.map Prod.fst = [] ∧
      substitution.variables.domain = [⟨0⟩] ∧
      substitution.applyPredicate convertSameRule.head =
        convert .word .word := by
  rcases matchImplHead?_certificate (rule := convertSameRule)
      (goal := convert .word .word) (premises := []) (by rfl) with
    ⟨substitution, certificate⟩
  cases certificate with
  | intro _ _ parameter_domain variable_domain head_eq _ =>
      have parameters_eq : ruleParameters convertSameRule = [] := by
        native_decide
      have variables_eq : ruleVariables convertSameRule = [⟨0⟩] := by
        native_decide
      rw [parameters_eq] at parameter_domain
      rw [variables_eq] at variable_domain
      exact ⟨substitution, parameter_domain, variable_domain, head_eq⟩

example : matchImplHead? whereOnlyRule (equality .word) =
    some [convert (.variable ⟨1⟩) (.variable ⟨2⟩)] := by
  rfl

example : Solcore.SourceSemantics.ImplHeadInstantiates whereOnlyRule
    (equality .word)
    [convert (.variable ⟨1⟩) (.variable ⟨2⟩)] := by
  exact Solcore.SourceSemantics.TraitResolutionSoundness.matchImplHead?_sound
    (by rfl)

example : ∃ substitution : RuleMatchSubstitution,
    substitution.parameters.map Prod.fst = [whereOnlyParameter] ∧
      substitution.variables.domain = [⟨0⟩] ∧
      substitution.applyPredicate whereOnlyRule.head = equality .word ∧
      whereOnlyRule.wherePredicates.map substitution.applyPredicate =
        [convert (.variable ⟨1⟩) (.variable ⟨2⟩)] := by
  rcases matchImplHead?_certificate (rule := whereOnlyRule)
      (goal := equality .word)
      (premises := [convert (.variable ⟨1⟩) (.variable ⟨2⟩)])
      (by rfl) with ⟨substitution, certificate⟩
  cases certificate with
  | intro _ _ parameter_domain variable_domain head_eq premises_eq =>
      have parameters_eq : ruleParameters whereOnlyRule =
          [whereOnlyParameter] := by native_decide
      have variables_eq : ruleVariables whereOnlyRule = [⟨0⟩] := by
        native_decide
      rw [parameters_eq] at parameter_domain
      rw [variables_eq] at variable_domain
      exact ⟨substitution, parameter_domain, variable_domain, head_eq,
        premises_eq⟩

example : (ruleParameters showBoxRule).Nodup :=
  ruleParameters_nodup showBoxRule

example : showBoxParameter ∈ ruleParameters showBoxRule := by
  rw [mem_ruleParameters_iff]
  exact .inl (by native_decide)

private def evidenceMatches : Evidence → Bool
  | .byImpl actualGoal actualImpl [
      .byImpl actualPremise actualPremiseImpl []] =>
      decide (actualGoal = showPredicate (box .word) ∧
        actualImpl = showBoxImpl ∧
        actualPremise = equality .word ∧
        actualPremiseImpl = equalityWordImpl)
  | _ => false

private def successfulResolution : Bool :=
  match (resolve [equalityWordRule, showBoxRule] 2
      (showPredicate (box .word))).outcome with
  | .success evidence => evidenceMatches evidence
  | _ => false

private def rejectedArgumentMismatch : Bool :=
  match (resolve [convertSameRule] 1 (convert .word .bool)).outcome with
  | .noSolution => true
  | _ => false

private def fresheningAvoidsGoalCollision : Bool :=
  let goal := equality (.variable ⟨5⟩)
  let freshened := freshenRuleFor showBoxRule goal
  decide (freshened.head = showPredicate (box (.variable ⟨6⟩)) ∧
    freshened.wherePredicates = [equality (.variable ⟨6⟩)])

private def concreteImplDoesNotBindGoal : Bool :=
  decide (matchImplHead? equalityWordRule (equality (.variable ⟨5⟩)) = none)

/-- Execute the typed impl-head/unification bridge without umbrella registration. -/
def testTypedTraitResolution : IO Unit := do
  assertTrue successfulResolution
    "generic impl head did not instantiate its where predicate and evidence"
  assertTrue rejectedArgumentMismatch
    "full predicate arguments were not included in impl-head unification"
  assertTrue fresheningAvoidsGoalCollision
    "impl variables were not freshened away from goal variables"
  assertTrue concreteImplDoesNotBindGoal
    "a concrete impl silently bound a caller-owned goal variable"
  assertTrue (decide (matchImplHead? showBoxRule (showPredicate (box .word)) =
      some [equality .word]))
    "typed head matcher did not expose instantiated where predicates"
  assertTrue (decide (matchImplHeadWithParameters? [showBoxParameter]
      showBoxRule (showPredicate (box .word)) = some {
        parameterSubstitution := [(showBoxParameter, .word)]
        wherePredicates := [equality .word]
      }))
    "detailed head matching did not retain the canonical ground parameter"

end Tests.TypedTraitResolution
