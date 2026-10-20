import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeOperatorSteps
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeStateSteps

/-! Binary operands retain a created generalization through the other operand,
the actual selected operator, expected-type fitting and result recording. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem binary_suffix
    {entryNext : Nat} {context : SourceInference.Context}
    {source : Syntax.Expr} {operator : Syntax.Located Syntax.BinaryOp} {id : ExpressionId}
    {left right : InferredExpression} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State}
    {final : InferredExpression × State}
    (ready : state.InferenceReady) (catalog : LifetimeInferenceContext context)
    (leftBelow : left.type.VariablesBelow state.inference.next)
    (rightBelow : right.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (expectedBefore : ∀ type ∈ expected, type.VariablesBelow entryNext)
    (lifetime : GeneralizationLifetime event entryNext state [left.type, right.type])
    (dispatch : BinaryExpressionDispatchFacts context source id operator left right
      expected integerLiterals state final) :
    GeneralizationLifetime event entryNext final.2 [final.1.type] := by
  have leftSafe := lifetime.values left.type (by simp)
  have rightSafe := lifetime.values right.type (by simp)
  have expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type :=
    fun type member => lifetime.older type (expectedBefore type member)
  have finish (result : OperatorInferenceResult)
      (operatorAccepted : inferBinaryOperator context operator.value left.type right.type
        expected integerLiterals state = .ok result)
      (recorded : recordExpressionWithExpected context source id result.type
        (.binary left.id operator.value right.id) result.requirements expected result.state = .ok final) :
      GeneralizationLifetime event entryNext final.2 [final.1.type] := by
    have operatorLife := lifetime.binaryOperator catalog.catalog ready leftBelow rightBelow
      expectedBelow leftSafe rightSafe expectedSafe operatorAccepted
    have properties := inferBinaryOperator_inferenceProperties ready leftBelow rightBelow
      expectedBelow operatorAccepted
    have recordedLife := operatorLife.recordExpression catalog.catalog properties.2.1 properties.2.2
      (fun type member => (expectedBelow type member).weaken properties.1.next_le)
      (operatorLife.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
      (fun type member => operatorLife.older type (expectedBefore type member)) recorded
    exact recordedLife.restrict_outputs (by intro type member; exact List.mem_append_right _ member)
  cases dispatch with
  | directFunction _ _ operatorAccepted recorded => exact finish _ operatorAccepted recorded
  | traitMethod _ operatorAccepted recorded => exact finish _ operatorAccepted recorded
  | @selectedFunction name head tail attempt fitted _ lookup selected fitting recorded =>
      have cataloged := functionsNamed_success_subset_catalog lookup
      have argumentsBelow : ∀ argument ∈ [left, right], argument.type.VariablesBelow state.inference.next := by
        intro argument member
        rcases List.mem_cons.mp member with rfl | member
        · exact leftBelow
        · cases List.mem_singleton.mp member
          exact rightBelow
      have argumentsSafe : ∀ argument ∈ [left, right], Safe binder.scheme.quantified state argument.type := by
        intro argument member
        rcases List.mem_cons.mp member with rfl | member
        · exact leftSafe
        · cases List.mem_singleton.mp member
          exact rightSafe
      have boolBelow : ∀ type ∈ (some Ty.bool : Option Ty), type.VariablesBelow state.inference.next := by
        intro type member
        simp only [Option.mem_def, Option.some.injEq] at member
        subst type
        exact Ty.variablesBelow_constructor _ _
      have boolSafe : ∀ type ∈ (some Ty.bool : Option Ty), Safe binder.scheme.quantified state type := by
        intro type member
        simp only [Option.mem_def, Option.some.injEq] at member
        subst type
        exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)
      have selectedLife := lifetime.selectCandidate catalog cataloged ready argumentsBelow boolBelow
        argumentsSafe boolSafe selected
      have selectedProperties := selectFunctionCandidateFrom_inferenceProperties ready argumentsBelow
        (fun signature member => catalog.formation.function_scheme_body_variablesBelow
          (cataloged member) (catalog.canonical signature (cataloged member)) _) boolBelow selected
      have expectedAtSelection : ∀ type ∈ expected, type.VariablesBelow attempt.state.inference.next :=
        fun type member => (expectedBelow type member).weaken selectedProperties.1.next_le
      have fittedLife := selectedLife.fitExpected catalog.catalog selectedProperties.2.1
        selectedProperties.2.2 expectedAtSelection
        (selectedLife.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
        (fun type member => selectedLife.older type (expectedBefore type member)) fitting
      have fittedProperties := withExpected_inferenceProperties selectedProperties.2.1
        selectedProperties.2.2 expectedAtSelection fitting
      let callee : Syntax.Expr := {
        span := operator.span
        value := .identifier {span := operator.span, value := name} }
      have recordedLife := fittedLife.recordSelectedResult source callee name [left, right] attempt
        fitted.expression fitted.coercions fittedProperties.2.1 fittedProperties.2.2
        (fittedLife.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
      change recordSelectedCallResult source callee name [left, right] attempt
        fitted.expression fitted.coercions fitted.state = final at recorded
      rw [recorded] at recordedLife
      exact recordedLife.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

theorem binary_left
    {fuel : Nat} {context : SourceInference.Context}
    {source left right : Syntax.Expr} {operator : Syntax.Located Syntax.BinaryOp}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {leftResult rightResult final : InferredExpression × State}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .binary left operator right)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (leftAccepted : inferExprFuel fuel context left none allocated = .ok leftResult)
    (rightAccepted : inferExprFuel fuel context right none leftResult.2 = .ok rightResult)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event allocated.inference.next leftResult.2 [leftResult.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have lifetime : GeneralizationLifetime event initial.inference.next leftResult.2 [leftResult.1.type] := by
    simpa only [sameNext] using lifetime
  have leftProperties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical (by simp) leftAccepted
  have rightProperties := inferExprFuel_inferenceProperties leftProperties.2.1
    catalog.formation catalog.canonical (by simp) rightAccepted
  have allocatedWellFormed : allocated.RequirementsWellFormed := by
    rw [allocatedEq]
    exact wellFormed
  have leftWellFormed := (inferExprFuel_direct_progress leftAccepted).wellFormed allocatedWellFormed
  have afterRight := lifetime.inferExpr leftProperties.2.1 leftWellFormed catalog
    (by simp) (by simp) rightAccepted
  obtain ⟨actualLeft, leftState, actualRight, rightState, actualLeftAccepted, actualRightAccepted, dispatch⟩ :=
    inferExprFuel_success_binary_facts form allocation accepted
  have sameLeft := Except.ok.inj (actualLeftAccepted.symm.trans leftAccepted)
  cases sameLeft
  have sameRight := Except.ok.inj (actualRightAccepted.symm.trans rightAccepted)
  cases sameRight
  exact binary_suffix rightProperties.2.1 catalog
    (leftProperties.2.2.weaken rightProperties.1.next_le) rightProperties.2.2
    (fun type member => (sameNext ▸ expectedBelow type member).weaken
      (Nat.le_trans leftProperties.1.next_le rightProperties.1.next_le))
    expectedBelow afterRight dispatch

theorem binary_right
    {fuel : Nat} {context : SourceInference.Context}
    {source left right : Syntax.Expr} {operator : Syntax.Located Syntax.BinaryOp}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {leftResult rightResult final : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .binary left operator right)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (leftAccepted : inferExprFuel fuel context left none allocated = .ok leftResult)
    (rightAccepted : inferExprFuel fuel context right none leftResult.2 = .ok rightResult)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event leftResult.2.inference.next rightResult.2 [rightResult.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have leftProperties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical (by simp) leftAccepted
  have rightProperties := inferExprFuel_inferenceProperties leftProperties.2.1
    catalog.formation catalog.canonical (by simp) rightAccepted
  have both := lifetime.replaceOutputs (values := [leftResult.1.type, rightResult.1.type]) (by
    intro type member
    rcases List.mem_cons.mp member with rfl | member
    · exact lifetime.older _ leftProperties.2.2
    · exact lifetime.values _ member)
  have afterRight := both.weaken_entry (sameNext ▸ leftProperties.1.next_le)
  obtain ⟨actualLeft, leftState, actualRight, rightState, actualLeftAccepted, actualRightAccepted, dispatch⟩ :=
    inferExprFuel_success_binary_facts form allocation accepted
  have sameLeft := Except.ok.inj (actualLeftAccepted.symm.trans leftAccepted)
  cases sameLeft
  have sameRight := Except.ok.inj (actualRightAccepted.symm.trans rightAccepted)
  cases sameRight
  exact binary_suffix rightProperties.2.1 catalog
    (leftProperties.2.2.weaken rightProperties.1.next_le) rightProperties.2.2
    (fun type member => (sameNext ▸ expectedBelow type member).weaken
      (Nat.le_trans leftProperties.1.next_le rightProperties.1.next_le))
    expectedBelow afterRight dispatch

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
