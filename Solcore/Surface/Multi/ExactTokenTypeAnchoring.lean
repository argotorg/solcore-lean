import Solcore.Surface.Multi.ExactTokenProperties

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

theorem identifierPlan_wellAnchored (identifier : IdentifierOccurrence) :
    (identifierPlan identifier).WellAnchored := by
  exact TokenPlan.WellAnchored.exact _ _

theorem pathComponentPlan_wellAnchored (component : PathComponent) :
    (pathComponentPlan component).WellAnchored := by
  exact TokenPlan.WellAnchored.exact _ _

theorem externalLibraryPlan_wellAnchored
    (library : Located ExternalLibraryName) :
    (externalLibraryPlan library).WellAnchored := by
  exact TokenPlan.WellAnchored.exact _ _

theorem qualifiedNamePlan_wellAnchored (name : QualifiedName) :
    (qualifiedNamePlan name).WellAnchored := by
  unfold qualifiedNamePlan
  apply TokenPlan.WellAnchored.enclose
  apply TokenPlan.WellAnchored.append
  · exact identifierPlan_wellAnchored _
  · apply TokenPlan.WellAnchored.concat
    intro plan member
    simp only [List.mem_map] at member
    rcases member with ⟨component, _member, rfl⟩
    exact TokenPlan.WellAnchored.append
      (TokenPlan.WellAnchored.plain _)
      (identifierPlan_wellAnchored component)

mutual

private def typeAnchoringMeasure (typeExpression : TypeExpr) : Nat :=
  1 + typePayloadAnchoringMeasure typeExpression.payload

private def typePayloadAnchoringMeasure : TypeExprPayload → Nat
  | .named _ arguments => 1 + typeArgumentsAnchoringMeasure arguments
  | .proxy _ inner => 1 + typeAnchoringMeasure inner
  | .function domain codomain =>
      1 + typeAnchoringMeasure domain + typeAnchoringMeasure codomain
  | .tuple elements => 1 + typeListAnchoringMeasure elements
  | .group inner => 1 + typeAnchoringMeasure inner
  | .comptime _ inner => 1 + typeAnchoringMeasure inner

private def typeArgumentsAnchoringMeasure :
    Option (NonemptyList TypeExpr) → Nat
  | none => 0
  | some values => typeNonemptyAnchoringMeasure values

private def typeNonemptyAnchoringMeasure
    (values : NonemptyList TypeExpr) : Nat :=
  1 + typeAnchoringMeasure values.head +
    typeListAnchoringMeasure values.tail

private def typeListAnchoringMeasure : List TypeExpr → Nat
  | [] => 0
  | head :: tail =>
      1 + typeAnchoringMeasure head + typeListAnchoringMeasure tail

end

/-- Every grammar-sensitive type plan accepted by the visitor has mandatory
physical endpoints. -/
theorem typeExprPlanAt?_wellAnchored
    (atomOnly : Bool) (typeExpression : TypeExpr) (plan : TokenPlan)
    (success : typeExprPlanAt? atomOnly typeExpression = some plan) :
    plan.WellAnchored :=
  match typeExpression with
  | ⟨span, .named name none⟩ => by
      simp [typeExprPlanAt?] at success
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (qualifiedNamePlan_wellAnchored name) span
  | ⟨span, .named name (some values)⟩ => by
      simp only [typeExprPlanAt?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨argumentPlans, _argumentsEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      exact TokenPlan.WellAnchored.append
        (qualifiedNamePlan_wellAnchored name)
        (TokenPlan.WellAnchored.parens _)
  | ⟨span, .proxy marker inner⟩ => by
      simp only [typeExprPlanAt?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨innerPlan, innerEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      exact TokenPlan.WellAnchored.append
        (TokenPlan.WellAnchored.exact _ _)
        (typeExprPlanAt?_wellAnchored true inner innerPlan innerEq)
  | ⟨span, .function domain codomain⟩ => by
      cases atomOnly with
      | true => simp [typeExprPlanAt?] at success
      | false =>
          simp only [typeExprPlanAt?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨domainPlan, domainEq, success⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨codomainPlan, codomainEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          apply TokenPlan.WellAnchored.enclose
          simpa [TokenPlan.concat, TokenPlan.append] using
            TokenPlan.WellAnchored.append
              (typeExprPlanAt?_wellAnchored true domain domainPlan domainEq)
              (TokenPlan.WellAnchored.append
                (TokenPlan.WellAnchored.plain _)
                (typeExprPlanAt?_wellAnchored false codomain codomainPlan
                  codomainEq))
  | ⟨span, .tuple []⟩ => by
      simp [typeExprPlanAt?] at success
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (TokenPlan.WellAnchored.parens _) span
  | ⟨_, .tuple [_]⟩ => by
      simp [typeExprPlanAt?] at success
  | ⟨span, .tuple (first :: second :: rest)⟩ => by
      simp only [typeExprPlanAt?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨plans, _plansEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (TokenPlan.WellAnchored.parens _) span
  | ⟨span, .group inner⟩ => by
      simp only [typeExprPlanAt?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨innerPlan, _innerEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (TokenPlan.WellAnchored.parens innerPlan) span
  | ⟨span, .comptime marker inner⟩ => by
      by_cases accepted : !atomOnly && marker.payload = .comptimeModifier
      · simp only [typeExprPlanAt?, accepted, ↓reduceIte] at success
        rcases Option.bind_eq_some_iff.mp success with
          ⟨innerPlan, innerEq, resultEq⟩
        injection resultEq with planEq
        subst plan
        apply TokenPlan.WellAnchored.enclose
        exact TokenPlan.WellAnchored.append
          (TokenPlan.WellAnchored.exact _ _)
          (typeExprPlanAt?_wellAnchored false inner innerPlan innerEq)
      · simp [typeExprPlanAt?, accepted] at success
termination_by typeAnchoringMeasure typeExpression
decreasing_by
  all_goals simp_all [typeAnchoringMeasure, typePayloadAnchoringMeasure] <;>
    omega

theorem typeExprPlan?_wellAnchored
    (typeExpression : TypeExpr) (plan : TokenPlan)
    (success : typeExprPlan? typeExpression = some plan) :
    plan.WellAnchored :=
  typeExprPlanAt?_wellAnchored false typeExpression plan success

theorem typeAtomPlan?_wellAnchored
    (typeExpression : TypeExpr) (plan : TokenPlan)
    (success : typeAtomPlan? typeExpression = some plan) :
    plan.WellAnchored :=
  typeExprPlanAt?_wellAnchored true typeExpression plan success

end Solcore.Surface.Multi
