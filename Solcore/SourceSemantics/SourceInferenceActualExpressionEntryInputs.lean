import Solcore.SourceSemantics.SourceInferenceActualCallProperties

/-! Lambda and constructor entries derive their input conditions from the
actual parameter-binding and constructor-instantiation prefixes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualExpressionInputs
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

private theorem expected_parts_below
    {state : State} {expected : Option Ty} {parameter result : Ty}
    (ready : state.InferenceReady)
    (below : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (parts : expected.bind (fun type => functionParts? (state.resolve type)) =
      some (parameter, result)) :
    parameter.VariablesBelow state.inference.next ∧
      result.VariablesBelow state.inference.next := by
  obtain ⟨type, member, found⟩ := Option.bind_eq_some_iff.mp parts
  have present : type ∈ expected := by simp [member]
  exact functionParts?_success_variablesBelow
    (ready.solved.variablesBelow_apply (below type present)) found

private theorem lambda_prefix_properties
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {parameters : List Ty}
    {state resultState : State} {resultType : Ty}
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (parameterBelow : (Ty.productMany parameters).VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (prefixFacts : LambdaPrefixFacts context expected annotation parameters state resultType resultState) :
    resultState.InferenceReady ∧ resultState.RequirementsWellFormed ∧
      resultType.VariablesBelow resultState.inference.next := by
  cases prefixFacts with
  | noExpectedPartsAnnotated _ _ resolved =>
    exact ⟨ready, wellFormed, resolveSourceType_success_variablesBelow resolved _⟩
  | noExpectedPartsFresh _ _ allocated =>
    have properties := fresh_eq_inferenceProperties ready allocated
    have stateEq : resultState = state.fresh.2 := (congrArg Prod.snd allocated).symm
    exact ⟨properties.2.1, stateEq ▸ State.fresh_preserves_requirementsWellFormed _ wellFormed,
      properties.2.2⟩
  | expectedPartsAnnotated parts unified _ resolved =>
    have expected := expected_parts_below ready expectedBelow parts
    exact ⟨unify_preserves_inferenceReady ready parameterBelow expected.1 unified,
      unify_preserves_requirementsWellFormed unified wellFormed,
      resolveSourceType_success_variablesBelow resolved _⟩
  | expectedPartsInferred parts unified _ =>
    have expected := expected_parts_below ready expectedBelow parts
    have progress := unify_inferenceProgress ready.solved parameterBelow expected.1 unified
    exact ⟨unify_preserves_inferenceReady ready parameterBelow expected.1 unified,
      unify_preserves_requirementsWellFormed unified wellFormed,
      expected.2.weaken progress.next_le⟩

theorem expression_lambda_body
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
      {annotation : Option Syntax.TypeExpr} {body : Syntax.Block}
      {boundParameters : List TypedBinder} {parameterTypes : List Ty}
      {parameterState bodyState : State} {resultType : Ty} {bodyResult : BlockResult}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .lambda keyword parameters annotation body)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (parametersAccepted : bindLambdaParameters context parameters.elements 0 [] allocated = .ok (boundParameters, parameterTypes, parameterState))
      (prefixFacts : LambdaPrefixFacts context expected annotation parameterTypes parameterState resultType bodyState)
      (_child : (CallIndex.statements fuel { context with loopDepth := 0 } body.value resultType bodyState bodyResult).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.statements fuel { context with loopDepth := 0 } body.value resultType bodyState bodyResult).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have parameters := bindLambdaParameters_inferenceProperties inputs.ready.allocateExpressionId parametersAccepted
  have wellFormed := (bindLambdaParameters_direct_progress parametersAccepted).wellFormed inputs.wellFormed
  have expectedBelow : ∀ type ∈ expected, type.VariablesBelow parameterState.inference.next :=
    fun type member => (inputs.bounds type member).weaken parameters.1.next_le
  have prefixProperties := lambda_prefix_properties parameters.2.1 wellFormed
    (Ty.variablesBelow_productMany parameters.2.2) expectedBelow prefixFacts
  exact ⟨prefixProperties.1, prefixProperties.2.1,
    ⟨inputs.catalog.catalog, inputs.catalog.formation, inputs.catalog.canonical⟩, prefixProperties.2.2⟩

theorem expression_contextual_constructor
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {dot : Syntax.SourceSpan} {name : Syntax.Identifier} {arguments : Option (Syntax.DelimitedList Syntax.Expr)}
      {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {typeArguments : List Ty}
      {inferred : InferredExpression} {childFinal : State}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .dotConstructor dot name arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (selected : contextualConstructorCandidate context allocated expected name.value = .ok (dataType, constructor, typeArguments))
      (_child : (CallIndex.constructorApplication fuel context source id (instantiateDataConstructor dataType constructor typeArguments) (arguments.map (·.elements) |>.getD []) expected allocated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.constructorApplication fuel context source id (instantiateDataConstructor dataType constructor typeArguments) (arguments.map (·.elements) |>.getD []) expected allocated inferred childFinal).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have bounded := contextualConstructorCandidate_success_instantiation_variablesBelow
    inputs.ready.allocateExpressionId inputs.bounds inputs.catalog.formation selected
  exact ⟨inputs.ready.allocateExpressionId, inputs.wellFormed, inputs.catalog,
    bounded.1, bounded.2, inputs.bounds⟩

theorem expression_call_constructor
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr}
      {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
      {instantiation : DataConstructorInstantiation} {instantiated childFinal : State}
      {inferred : InferredExpression}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .call callee arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (selected : constructorCalleeCandidates context allocated callee = .ok [(dataType, constructor)])
      (fresh : freshDataConstructorInstantiation dataType constructor allocated = (instantiation, instantiated))
      (_child : (CallIndex.constructorApplication fuel context source id instantiation arguments.elements expected instantiated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.constructorApplication fuel context source id instantiation arguments.elements expected instantiated inferred childFinal).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  obtain ⟨dataMember, constructorMember⟩ :=
    constructorCalleeCandidates_success_members selected dataType constructor (by simp)
  have properties := freshDataConstructorInstantiation_inferenceProperties dataType constructor
    initial.allocateExpressionId.2 inputs.ready.allocateExpressionId
    (inputs.catalog.formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember _)
  simp only [fresh] at properties
  have wellFormed := (freshDataConstructorInstantiation_direct_progress dataType constructor
    initial.allocateExpressionId.2).wellFormed inputs.wellFormed
  simp only [fresh] at wellFormed
  exact ⟨properties.2.1, wellFormed, inputs.catalog, properties.2.2.2.1,
    properties.2.2.2.2, fun type member => (inputs.bounds type member).weaken properties.1.next_le⟩

theorem expression_field_constructor
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {base : Syntax.Expr} {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
      {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
      {instantiation : DataConstructorInstantiation} {instantiated childFinal : State}
      {inferred : InferredExpression}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .field base dot name)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (selected : constructorCalleeCandidates context allocated source = .ok [(dataType, constructor)])
      (fresh : freshDataConstructorInstantiation dataType constructor allocated = (instantiation, instantiated))
      (_child : (CallIndex.constructorApplication fuel context source id instantiation [] expected instantiated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.constructorApplication fuel context source id instantiation [] expected instantiated inferred childFinal).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  obtain ⟨dataMember, constructorMember⟩ :=
    constructorCalleeCandidates_success_members selected dataType constructor (by simp)
  have properties := freshDataConstructorInstantiation_inferenceProperties dataType constructor
    initial.allocateExpressionId.2 inputs.ready.allocateExpressionId
    (inputs.catalog.formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember _)
  simp only [fresh] at properties
  have wellFormed := (freshDataConstructorInstantiation_direct_progress dataType constructor
    initial.allocateExpressionId.2).wellFormed inputs.wellFormed
  simp only [fresh] at wellFormed
  exact ⟨properties.2.1, wellFormed, inputs.catalog, properties.2.2.2.1,
    properties.2.2.2.2, fun type member => (inputs.bounds type member).weaken properties.1.next_le⟩

end Solcore.SourceSemantics.SourceInferenceExecution.ActualExpressionInputs
