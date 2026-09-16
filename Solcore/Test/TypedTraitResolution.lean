import Solcore.Frontend.TypedTraitResolution

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

example : matchImplHead? showBoxRule (equality (box .word)) = none := by
  rfl

example : matchImplHead? convertSameRule (convert .word .bool) = none := by
  rfl

example : matchImplHead? convertSameRule (convert .word .word) = some [] := by
  rfl

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

end Tests.TypedTraitResolution
