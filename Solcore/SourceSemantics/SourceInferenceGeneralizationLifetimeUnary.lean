import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeOperatorSteps

/-! A generalization created while checking a unary operand survives the
actual operator dispatch, candidate selection and result recording. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem unary
    {fuel : Nat} {context : SourceInference.Context}
    {source operand : Syntax.Expr} {operator : Syntax.Located Syntax.UnaryOp}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {child final : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .unary operator operand)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (childAccepted : inferExprFuel fuel context operand none allocated = .ok child)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have childProperties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical
    (by simp) childAccepted
  have lifetime : GeneralizationLifetime event initial.inference.next child.2 [child.1.type] := by
    simpa only [sameNext] using lifetime
  have childExpected : ∀ type ∈ expected, type.VariablesBelow child.2.inference.next :=
    fun type member => (sameNext ▸ expectedBelow type member).weaken childProperties.1.next_le
  have childSafe := lifetime.values child.1.type (List.mem_singleton_self _)
  have expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified child.2 type :=
    fun type member => lifetime.older type (expectedBelow type member)
  obtain ⟨value, state, actualChild, dispatch⟩ :=
    inferExprFuel_success_unary_facts form allocation accepted
  have sameChild := Except.ok.inj (actualChild.symm.trans childAccepted)
  cases sameChild
  have finish (result : OperatorInferenceResult)
      (operatorAccepted : inferUnaryOperator context operator.value value.type expected
        (relevantIntegerLiterals state allocated.integerLiterals.length [value]) state = .ok result)
      (recorded : recordExpressionWithExpected context source id result.type
        (.unary operator.value value.id) result.requirements expected result.state = .ok final) :
      GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
    have operatorLife := lifetime.unaryOperator catalog.catalog childProperties.2.1
      childProperties.2.2 childExpected childSafe expectedSafe operatorAccepted
    have operatorProperties := inferUnaryOperator_inferenceProperties childProperties.2.1
      childProperties.2.2 childExpected operatorAccepted
    have result := operatorLife.recordExpression catalog.catalog operatorProperties.2.1
      operatorProperties.2.2
      (fun type member => (childExpected type member).weaken operatorProperties.1.next_le)
      (operatorLife.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
      (fun type member => operatorLife.older type (expectedBelow type member)) recorded
    exact result.restrict_outputs (by intro type member; exact List.mem_append_right _ member)
  cases dispatch with
  | directFunction _ _ operatorAccepted recorded => exact finish _ operatorAccepted recorded
  | traitMethod _ operatorAccepted recorded => exact finish _ operatorAccepted recorded
  | @selectedFunction name head tail attempt _ lookup selected recorded =>
      have cataloged := functionsNamed_success_subset_catalog lookup
      have argumentsBelow : ∀ argument ∈ [value], argument.type.VariablesBelow state.inference.next := by
        intro argument member
        cases List.mem_singleton.mp member
        exact childProperties.2.2
      have argumentsSafe : ∀ argument ∈ [value], Safe binder.scheme.quantified state argument.type := by
        intro argument member
        cases List.mem_singleton.mp member
        exact childSafe
      have selectedLife := lifetime.selectCandidate catalog cataloged childProperties.2.1
        argumentsBelow childExpected argumentsSafe expectedSafe selected
      have selectedProperties := selectFunctionCandidateFrom_inferenceProperties childProperties.2.1
        argumentsBelow
        (fun signature member => catalog.formation.function_scheme_body_variablesBelow
          (cataloged member) (catalog.canonical signature (cataloged member)) _) childExpected selected
      let callee : Syntax.Expr := {
        span := operator.span
        value := .identifier {span := operator.span, value := name} }
      have recordedLife := selectedLife.recordSelected source callee name [value]
        selectedProperties.2.1 selectedProperties.2.2
        (selectedLife.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
      change recordSelectedCall source callee name [value] attempt = final at recorded
      rw [recorded] at recordedLife
      exact recordedLife.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
