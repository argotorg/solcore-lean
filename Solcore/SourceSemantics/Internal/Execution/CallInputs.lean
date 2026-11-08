import Solcore.SourceSemantics.Internal.Execution.GeneralizationEvents
import Solcore.SourceSemantics.Internal.Inference.RootedContracts
import Solcore.SourceSemantics.Internal.Privacy.Lifetimes
import Lean
import Solcore.Frontend.SourceInference.Internal.LocalReadScopes
import Solcore.SourceSemantics.Internal.Execution.Reads
import Solcore.SourceSemantics.Internal.Execution.CallGraph

/-!
# Inputs and order of calls

Each child gets its formation and allocator inputs from the parent state, and siblings occupy
ordered allocator intervals.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualExpressionEntryInputs
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualExpressionInputs
/-! Each child receives its formation and allocator inputs from the actual
parent state and the state-producing prefixes of that branch. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualExpressionInputs
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

theorem expression_group
      {fuel : Nat} {context : SourceInference.Context} {source inner : Syntax.Expr}
      {expected : Option Ty} {initial allocated final childFinal : State}
      {id : ExpressionId} {value childValue : InferredExpression}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected
        initial value final).Accepted)
      (_form : source.value = .group inner)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (_child : inferExprFuel fuel context inner expected allocated =
        .ok (childValue, childFinal))
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.expression fuel context inner expected allocated childValue childFinal).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact ⟨inputs.ready.allocateExpressionId, inputs.wellFormed, inputs.catalog, inputs.bounds⟩

theorem expression_tuple
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {elements : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
      {initial allocated final childFinal : State} {id : ExpressionId}
      {value : InferredExpression} {values : List InferredExpression}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected
        initial value final).Accepted)
      (_form : source.value = .tuple elements)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (_child : inferExprsFuel fuel context elements.elements allocated =
        .ok (values, childFinal))
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.expressions fuel context elements.elements allocated values childFinal).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact ⟨inputs.ready.allocateExpressionId, inputs.wellFormed, inputs.catalog, trivial⟩

theorem expression_call_arguments
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr}
      {values : List InferredExpression} {childFinal : State}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .call callee arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (_nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
      (_child : (CallIndex.expressions fuel context arguments.elements allocated values childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.expressions fuel context arguments.elements allocated values childFinal).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact ⟨inputs.ready.allocateExpressionId, inputs.wellFormed, inputs.catalog, trivial⟩

theorem expression_unary
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {operator : Syntax.Located Syntax.UnaryOp} {operand : Syntax.Expr}
      {inferred : InferredExpression} {childFinal : State}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .unary operator operand)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (_child : (CallIndex.expression fuel context operand none allocated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.expression fuel context operand none allocated inferred childFinal).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact ⟨inputs.ready.allocateExpressionId, inputs.wellFormed, inputs.catalog, (by intro type member; cases member)⟩

theorem expression_binary_left
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {operator : Syntax.Located Syntax.BinaryOp} {left right : Syntax.Expr}
      {leftValue : InferredExpression} {leftState : State}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .binary left operator right)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (_child : (CallIndex.expression fuel context left none allocated leftValue leftState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.expression fuel context left none allocated leftValue leftState).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact ⟨inputs.ready.allocateExpressionId, inputs.wellFormed, inputs.catalog, (by intro type member; cases member)⟩

theorem expression_index_base
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan}
      {inferred : InferredExpression} {childFinal : State}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .index base brackets key)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (_child : (CallIndex.expression fuel context base none allocated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.expression fuel context base none allocated inferred childFinal).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact ⟨inputs.ready.allocateExpressionId, inputs.wellFormed, inputs.catalog, (by intro type member; cases member)⟩

theorem expression_conditional_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {condition thenBranch elseBranch : Syntax.Expr} {question colon : Syntax.SourceSpan}
      {conditionValue : InferredExpression} {conditionState : State}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .conditional condition question thenBranch colon elseBranch)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (_child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact ⟨inputs.ready.allocateExpressionId, inputs.wellFormed, inputs.catalog, (by
      intro type member
      cases Option.some.inj (Option.mem_def.mp member)
      exact Ty.variablesBelow_constructor _ _)⟩

theorem expression_binary_right
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {operator : Syntax.Located Syntax.BinaryOp} {left right : Syntax.Expr}
      {leftValue : InferredExpression} {leftState : State}
      {rightValue : InferredExpression} {rightState : State}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .binary left operator right)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (leftAccepted : inferExprFuel fuel context left none allocated = .ok (leftValue, leftState))
      (_child : (CallIndex.expression fuel context right none leftState rightValue rightState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.expression fuel context right none leftState rightValue rightState).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have properties := inferExprFuel_inferenceProperties inputs.ready.allocateExpressionId
    inputs.catalog.formation inputs.catalog.canonical (by intro type member; cases member) leftAccepted
  exact ⟨properties.2.1, (inferExprFuel_direct_progress leftAccepted).wellFormed inputs.wellFormed,
    inputs.catalog, (by intro type member; cases member)⟩

theorem expression_call_callee
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr}
      {values : List InferredExpression} {argumentState childFinal : State} {inferred : InferredExpression}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .call callee arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (_nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
      (argumentsAccepted : inferExprsFuel fuel context arguments.elements allocated = .ok (values, argumentState))
      (_indirect : IndirectCalleeAt context callee argumentState)
      (_child : (CallIndex.expression fuel context callee none argumentState inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.expression fuel context callee none argumentState inferred childFinal).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have properties := inferExprsFuel_inferenceProperties inputs.ready.allocateExpressionId
    inputs.catalog.formation inputs.catalog.canonical argumentsAccepted
  exact ⟨properties.2.1, (inferExprsFuel_direct_progress argumentsAccepted).wellFormed inputs.wellFormed,
    inputs.catalog, (by intro type member; cases member)⟩

theorem expression_conditional_then
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {condition thenBranch elseBranch : Syntax.Expr} {question colon : Syntax.SourceSpan}
      {conditionValue : InferredExpression} {conditionState : State}
      {thenValue : InferredExpression} {thenState : State}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .conditional condition question thenBranch colon elseBranch)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (_child : (CallIndex.expression fuel context thenBranch expected conditionState thenValue thenState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.expression fuel context thenBranch expected conditionState thenValue thenState).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have conditionProperties := inferExprFuel_inferenceProperties inputs.ready.allocateExpressionId
    inputs.catalog.formation inputs.catalog.canonical (by
      intro type member
      cases Option.some.inj (Option.mem_def.mp member)
      exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have conditionExpected : ∀ type ∈ expected, type.VariablesBelow conditionState.inference.next :=
    fun type member => (inputs.bounds type member).weaken conditionProperties.1.next_le
  have conditionWellFormed := (inferExprFuel_direct_progress conditionAccepted).wellFormed inputs.wellFormed
  exact ⟨conditionProperties.2.1, conditionWellFormed, inputs.catalog, conditionExpected⟩

theorem expression_conditional_else
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {condition thenBranch elseBranch : Syntax.Expr} {question colon : Syntax.SourceSpan}
      {conditionValue : InferredExpression} {conditionState : State}
      {thenValue elseValue : InferredExpression} {thenState elseState : State}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .conditional condition question thenBranch colon elseBranch)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (thenAccepted : inferExprFuel fuel context thenBranch expected conditionState = .ok (thenValue, thenState))
      (_child : (CallIndex.expression fuel context elseBranch expected thenState elseValue elseState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.expression fuel context elseBranch expected thenState elseValue elseState).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have conditionProperties := inferExprFuel_inferenceProperties inputs.ready.allocateExpressionId
    inputs.catalog.formation inputs.catalog.canonical (by
      intro type member
      cases Option.some.inj (Option.mem_def.mp member)
      exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have conditionExpected : ∀ type ∈ expected, type.VariablesBelow conditionState.inference.next :=
    fun type member => (inputs.bounds type member).weaken conditionProperties.1.next_le
  have conditionWellFormed := (inferExprFuel_direct_progress conditionAccepted).wellFormed inputs.wellFormed
  have thenProperties := inferExprFuel_inferenceProperties conditionProperties.2.1
    inputs.catalog.formation inputs.catalog.canonical conditionExpected thenAccepted
  exact ⟨thenProperties.2.1, (inferExprFuel_direct_progress thenAccepted).wellFormed conditionWellFormed,
    inputs.catalog, fun type member => (conditionExpected type member).weaken thenProperties.1.next_le⟩

theorem expression_index_key
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {baseValue keyValue : InferredExpression}
      {baseState keyState valueState fitted childFinal : State} {keyType valueType : Ty}
      (_accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (_form : source.value = .index base brackets key)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (baseAccepted : inferExprFuel fuel context base none allocated = .ok (baseValue, baseState))
      (keyFresh : baseState.fresh = (keyType, keyState))
      (valueFresh : keyState.fresh = (valueType, valueState))
      (fitting : unify valueState baseValue.type (.mapping keyType valueType) = .ok fitted)
      (_child : (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs) : (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).Inputs := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have baseProperties := inferExprFuel_inferenceProperties inputs.ready.allocateExpressionId
    inputs.catalog.formation inputs.catalog.canonical (by intro type member; cases member) baseAccepted
  have keyProperties := fresh_eq_inferenceProperties baseProperties.2.1 keyFresh
  have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 valueFresh
  have baseBelow := baseProperties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
  have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow, valueProperties.2.2⟩
  have fittedReady := unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow fitting
  have fittedProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow fitting
  have baseWellFormed := (inferExprFuel_direct_progress baseAccepted).wellFormed inputs.wellFormed
  have valueWellFormed : valueState.RequirementsWellFormed := by
    rw [← show keyState.fresh.2 = valueState from congrArg Prod.snd valueFresh,
      ← show baseState.fresh.2 = keyState from congrArg Prod.snd keyFresh]
    exact baseWellFormed
  refine ⟨fittedReady, unify_preserves_requirementsWellFormed fitting valueWellFormed, inputs.catalog, ?_⟩
  intro type member
  cases Option.some.inj (Option.mem_def.mp member)
  exact fittedReady.solved.variablesBelow_apply (keyBelow.weaken fittedProgress.next_le)

end Solcore.SourceSemantics.SourceInferenceExecution.ActualExpressionInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualListCallInputs
/-! Exact successful prefixes supply the ordinary inputs for ordered children. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ChildStep

theorem inputs_expressions
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {initial final : State} {values : List InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.expressions fuel context sources initial values final).Inputs)
    (step : ChildStep (.expressions fuel context sources initial values final) child) : child.Inputs := by
  cases step with
  | expressions_head => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, by simp [CallIndex.InputBounds]⟩
  | expressions_tail _ head _ =>
      have properties := inferExprFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical (by simp) head
      exact ⟨properties.2.1, (inferExprFuel_direct_progress head).wellFormed inputs.wellFormed, inputs.catalog, trivial⟩

theorem inputs_statements
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult} {child : CallIndex}
    (inputs : (CallIndex.statements fuel context sources expected initial result).Inputs)
    (step : ChildStep (.statements fuel context sources expected initial result) child) : child.Inputs := by
  cases step with
  | statements_head => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, inputs.bounds⟩
  | statements_tail _ _ head _ =>
      have properties := inferStatementFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical inputs.bounds head
      exact ⟨properties.2.1, (inferStatementFuel_direct_progress head).wellFormed inputs.wellFormed,
        inputs.catalog, inputs.bounds.weaken properties.1.next_le⟩

theorem inputs_forItems
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems} {child : CallIndex}
    (inputs : (CallIndex.forItems fuel context sources initial result).Inputs)
    (step : ChildStep (.forItems fuel context sources initial result) child) : child.Inputs := by
  cases step with
  | forItems_head => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, trivial⟩
  | forItems_tail _ head _ =>
      have properties := inferForItemFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical head
      exact ⟨properties.2, (inferForItemFuel_direct_progress head).wellFormed inputs.wellFormed,
        inputs.catalog, trivial⟩

theorem inputs_constructorArguments
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {expected : List Ty} {initial final : State} {values : List InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.constructorArguments fuel context sources expected initial values final).Inputs)
    (step : ChildStep (.constructorArguments fuel context sources expected initial values final) child) : child.Inputs := by
  cases step with
  | constructorArguments_head =>
      refine ⟨inputs.ready, inputs.wellFormed, inputs.catalog, ?_⟩
      intro type member
      cases member
      exact inputs.ready.solved.variablesBelow_apply (inputs.bounds _ (by simp))
  | constructorArguments_tail _ head _ =>
      have properties := inferExprFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical
        (by intro type member; cases member; exact inputs.ready.solved.variablesBelow_apply (inputs.bounds _ (by simp))) head
      exact ⟨properties.2.1, (inferExprFuel_direct_progress head).wellFormed inputs.wellFormed,
        inputs.catalog, fun type member => (inputs.bounds type (List.mem_cons_of_mem _ member)).weaken properties.1.next_le⟩

theorem inputs_constructorApplication
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation} {sources : List Syntax.Expr} {expected : Option Ty}
    {initial final : State} {value : InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Inputs)
    (step : ChildStep (.constructorApplication fuel context source id instantiation sources expected initial value final) child) : child.Inputs := by
  cases step with
  | constructorApplication_arguments _ _ fitting _ =>
      cases expected with
      | none =>
          cases Except.ok.inj fitting
          exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, inputs.bounds.1⟩
      | some expected =>
          have expectedBelow := inputs.bounds.2.2 expected (by simp)
          have progress := unify_inferenceProgress inputs.ready.solved inputs.bounds.2.1 expectedBelow fitting
          exact ⟨unify_preserves_inferenceReady inputs.ready inputs.bounds.2.1 expectedBelow fitting,
            unify_preserves_requirementsWellFormed fitting inputs.wellFormed, inputs.catalog,
            fun type member => (inputs.bounds.1 type member).weaken progress.next_le⟩

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualMatchCallInputs
/-! Actual pattern and arm computations supply the next match-call inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ChildStep

theorem inputs_matchCases
    {fuel : Nat} {context : SourceInference.Context} {scrutinee expected : Ty}
    {saved : LexicalScope} {sources : List Syntax.MatchCase}
    {initial : State} {result : MatchCasesResult} {child : CallIndex}
    (inputs : (CallIndex.matchCases fuel context scrutinee expected saved sources initial result).Inputs)
    (step : ChildStep (.matchCases fuel context scrutinee expected saved sources initial result) child) : child.Inputs := by
  cases step with
  | matchCases_body _ patternAccepted _ =>
      have patternProperties := inferMatchPatternFuel_inferenceProperties inputs.ready inputs.bounds.1 inputs.catalog.formation patternAccepted
      exact ⟨patternProperties.2.1, (inferMatchPatternFuel_direct_progress patternAccepted).wellFormed inputs.wellFormed,
        inputs.catalog, inputs.bounds.2.1.weaken patternProperties.1.next_le⟩
  | matchCases_tail _ patternAccepted bodyAccepted _ =>
      have patternProperties := inferMatchPatternFuel_inferenceProperties inputs.ready inputs.bounds.1 inputs.catalog.formation patternAccepted
      have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1 inputs.catalog.formation inputs.catalog.canonical
        (inputs.bounds.2.1.weaken patternProperties.1.next_le) bodyAccepted
      have through := patternProperties.1.trans bodyProperties.1
      have restoredReady := (State.restoreLexicalScope_inferenceProperties inputs.ready through).2
      simp only [CallIndex.initial] at restoredReady
      rw [inputs.bounds.2.2] at restoredReady
      exact ⟨restoredReady, (inferStatementsFuel_direct_progress bodyAccepted).wellFormed
        ((inferMatchPatternFuel_direct_progress patternAccepted).wellFormed inputs.wellFormed),
        inputs.catalog, inputs.bounds.1.weaken through.next_le,
        inputs.bounds.2.1.weaken through.next_le, rfl⟩

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualMutableCallInputs
/-! Actual place, value-assignment and header prefixes supply child inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ChildStep

theorem inputs_forItem
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {value : ForItemForm} {child : CallIndex}
    (inputs : (CallIndex.forItem fuel context source initial value final).Inputs)
    (step : ChildStep (.forItem fuel context source initial value final) child) : child.Inputs := by
  cases step with
  | forItem_initializer _ _ annotation _ =>
      refine ⟨inputs.ready, inputs.wellFormed, inputs.catalog, ?_⟩
      cases annotation with
      | absent => simp [CallIndex.InputBounds]
      | present accepted =>
          intro type member
          cases member
          exact resolveSourceType_success_variablesBelow accepted _
  | forItem_expression => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, by simp [CallIndex.InputBounds]⟩
  | forItem_assignment => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, trivial⟩
  | forItem_bitnot => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, trivial⟩

theorem inputs_place
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {initial final : State} {value : PlaceResolution} {child : CallIndex}
    (inputs : (CallIndex.place fuel context source initial value final).Inputs)
    (step : ChildStep (.place fuel context source initial value final) child) : child.Inputs := by
  cases step with
  | place_group => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, trivial⟩
  | place_index_base => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, trivial⟩
  | @place_index_key fuel context source initial final result base key brackets baseValue baseState keyState valueState fitted childFinal keyType valueType keyValue _ _ baseAccepted keyFresh valueFresh fitting _ =>
      have baseProperties := inferPlaceFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical baseAccepted
      have keyProperties := fresh_eq_inferenceProperties baseProperties.2.1 keyFresh
      have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 valueFresh
      have baseBelow := baseProperties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
      have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
      have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).mpr ⟨keyBelow, valueProperties.2.2⟩
      have mappingProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow fitting
      have mappingReady := unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow fitting
      have baseWF := (inferPlaceFuel_direct_progress baseAccepted).wellFormed inputs.wellFormed
      have valueWF : valueState.RequirementsWellFormed := by
        rw [← show keyState.fresh.2 = valueState from congrArg Prod.snd valueFresh,
          ← show baseState.fresh.2 = keyState from congrArg Prod.snd keyFresh]
        exact baseWF
      refine ⟨mappingReady, unify_preserves_requirementsWellFormed fitting valueWF, inputs.catalog, ?_⟩
      intro type member
      cases member
      exact mappingReady.solved.variablesBelow_apply (keyBelow.weaken mappingProgress.next_le)

theorem inputs_assignedValue
    {fuel : Nat} {context : SourceInference.Context} {target source : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {initial final : State}
    {assignment : AssignmentResolution} {value : InferredExpression} {child : CallIndex}
    (inputs : (CallIndex.assignedValue fuel context target operator source initial assignment value final).Inputs)
    (step : ChildStep (.assignedValue fuel context target operator source initial assignment value final) child) : child.Inputs := by
  cases step with
  | assignedValue_place => exact ⟨inputs.ready, inputs.wellFormed, inputs.catalog, trivial⟩
  | @assignedValue_value fuel context target source operator initial final targetState assignment value place fitted childFinal childValue _ placeAccepted fitting _ =>
      have fitting : assignmentFit operator targetState place.type = .ok fitted := by cases operator <;> exact fitting
      have placeProperties := inferPlaceFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical placeAccepted
      have fitProperties := assignmentFit_properties placeProperties.2.1 placeProperties.2.2 fitting
      have fittedWF : fitted.RequirementsWellFormed := by
        have placeWF := (inferPlaceFuel_direct_progress placeAccepted).wellFormed inputs.wellFormed
        cases operator <;> simp only [assignmentFit] at fitting
        all_goals first
        | (change Except.ok targetState = Except.ok fitted at fitting
           cases Except.ok.inj fitting
           exact placeWF)
        | exact unify_preserves_requirementsWellFormed fitting placeWF
      refine ⟨fitProperties.2.1, fittedWF, inputs.catalog, ?_⟩
      intro type member
      cases member
      exact fitProperties.2.2

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualMatchPrefixProperties
/-! The match scrutinee prefix retains the real scalar or synthetic tuple call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

theorem matchScrutinee_properties
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial : State} {result : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (accepted : matchScrutinee fuel context span sources initial = .ok result) :
    initial.InferenceProgress result.2 ∧ result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical (by simp) accepted
  · cases run : inferExprsFuel fuel context sources initial with
    | error error => simp [run, bind, Except.bind] at accepted
    | ok pair =>
      obtain ⟨values, state⟩ := pair
      simp only [run, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      have facts := inferExprsFuel_inferenceProperties ready catalog.formation catalog.canonical run
      have progress := facts.1.trans (State.InferenceProgress.allocateExpressionId state facts.2.1.solved)
      have allocatedReady := facts.2.1.allocateExpressionId
      refine ⟨progress.trans (.recordNode _ _ allocatedReady.solved), allocatedReady.recordNode _, ?_⟩
      apply Ty.variablesBelow_productMany
      intro type member
      obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
      exact facts.2.2 value present

theorem matchScrutinee_wellFormed
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial : State} {result : InferredExpression × State}
    (wellFormed : initial.RequirementsWellFormed)
    (accepted : matchScrutinee fuel context span sources initial = .ok result) :
    result.2.RequirementsWellFormed := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact (inferExprFuel_direct_progress accepted).wellFormed wellFormed
  · cases run : inferExprsFuel fuel context sources initial with
    | error error => simp [run, bind, Except.bind] at accepted
    | ok pair =>
      obtain ⟨values, state⟩ := pair
      simp only [run, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact (inferExprsFuel_direct_progress run).wellFormed wellFormed

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualStatementCallInputs
/-! Each statement child receives inputs from its actual preceding calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

private theorem statementAllocation_inputs {initial allocated : State} {id : StatementId}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (allocation : initial.allocateStatementId = (id, allocated)) :
    allocated.InferenceReady ∧ allocated.RequirementsWellFormed ∧ allocated.inference.next = initial.inference.next := by
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact ⟨ready.allocateStatementId, wellFormed, rfl⟩

private theorem hiddenAllocation_inputs {initial allocated : State} {id : Resolved.LocalId}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (allocation : initial.allocateHiddenLocal = (id, allocated)) :
    allocated.InferenceReady ∧ allocated.RequirementsWellFormed ∧ allocated.inference.next = initial.inference.next := by
  have same : allocated = initial.allocateHiddenLocal.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact ⟨ready.allocateHiddenLocal, wellFormed, rfl⟩

namespace ChildStep

theorem inputs_statement
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult} {child : CallIndex}
    (inputs : (CallIndex.statement fuel context source expected initial result).Inputs)
    (step : ChildStep (.statement fuel context source expected initial result) child) : child.Inputs := by
  have returnBound : expected.VariablesBelow initial.inference.next := inputs.bounds
  cases step with
  | statement_initializer _ _ allocation annotation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      refine ⟨allocated.1, allocated.2.1, inputs.catalog, ?_⟩
      cases annotation with
      | absent => simp [CallIndex.InputBounds]
      | present accepted => intro type member; cases member; exact resolveSourceType_success_variablesBelow accepted _
  | statement_return _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      refine ⟨allocated.1, allocated.2.1, inputs.catalog, ?_⟩
      intro type member
      cases member
      exact allocated.2.2 ▸ returnBound
  | statement_expression _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, by simp [CallIndex.InputBounds]⟩
  | statement_block _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, by change expected.VariablesBelow _; exact allocated.2.2 ▸ returnBound⟩
  | statement_if_condition _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      refine ⟨allocated.1, allocated.2.1, inputs.catalog, ?_⟩
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _
  | statement_if_then _ _ allocation conditionAccepted _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have condition := inferExprFuel_inferenceProperties allocated.1 inputs.catalog.formation inputs.catalog.canonical
        (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
      exact ⟨condition.2.1, (inferExprFuel_direct_progress conditionAccepted).wellFormed allocated.2.1,
        inputs.catalog, (allocated.2.2 ▸ returnBound).weaken condition.1.next_le⟩
  | statement_if_else _ _ allocation conditionAccepted _ thenAccepted _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have condition := inferExprFuel_inferenceProperties allocated.1 inputs.catalog.formation inputs.catalog.canonical
        (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
      have returnBelow := (allocated.2.2 ▸ returnBound).weaken condition.1.next_le
      have thenProperties := inferStatementsFuel_inferenceProperties condition.2.1 inputs.catalog.formation inputs.catalog.canonical returnBelow thenAccepted
      exact ⟨(State.restoreLexicalScope_inferenceProperties condition.2.1 thenProperties.1).2,
        (inferStatementsFuel_direct_progress thenAccepted).wellFormed
          ((inferExprFuel_direct_progress conditionAccepted).wellFormed allocated.2.1),
        inputs.catalog, returnBelow.weaken thenProperties.1.next_le⟩
  | statement_assignment _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, trivial⟩
  | statement_bitnot _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, trivial⟩
  | statement_while_condition _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      refine ⟨allocated.1, allocated.2.1, inputs.catalog, ?_⟩
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _
  | statement_while_body _ _ allocation conditionAccepted _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have condition := inferExprFuel_inferenceProperties allocated.1 inputs.catalog.formation inputs.catalog.canonical
        (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
      exact ⟨condition.2.1, (inferExprFuel_direct_progress conditionAccepted).wellFormed allocated.2.1,
        inputs.catalog.withLoopDepth _, (allocated.2.2 ▸ returnBound).weaken condition.1.next_le⟩
  | statement_for_initializer _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, trivial⟩
  | statement_for_condition _ _ allocation initializerAccepted _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have initialized := inferForItemsFuel_inferenceProperties allocated.1 inputs.catalog.formation inputs.catalog.canonical initializerAccepted
      refine ⟨initialized.2, (inferForItemsFuel_direct_progress initializerAccepted).wellFormed allocated.2.1, inputs.catalog, ?_⟩
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _
  | statement_for_body _ _ allocation initializerAccepted conditionAccepted _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have initialized := inferForItemsFuel_inferenceProperties allocated.1 inputs.catalog.formation inputs.catalog.canonical initializerAccepted
      have condition := inferExprFuel_inferenceProperties initialized.2 inputs.catalog.formation inputs.catalog.canonical
        (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
      exact ⟨condition.2.1, (inferExprFuel_direct_progress conditionAccepted).wellFormed
        ((inferForItemsFuel_direct_progress initializerAccepted).wellFormed allocated.2.1),
        inputs.catalog.withLoopDepth _, (allocated.2.2 ▸ returnBound).weaken (initialized.1.trans condition.1).next_le⟩
  | statement_for_post _ _ allocation initializerAccepted conditionAccepted bodyAccepted _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have initialized := inferForItemsFuel_inferenceProperties allocated.1 inputs.catalog.formation inputs.catalog.canonical initializerAccepted
      have condition := inferExprFuel_inferenceProperties initialized.2 inputs.catalog.formation inputs.catalog.canonical
        (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
      have bodyProperties := inferStatementsFuel_inferenceProperties (context := {context with loopDepth := context.loopDepth + 1}) condition.2.1 inputs.catalog.formation inputs.catalog.canonical
        ((allocated.2.2 ▸ returnBound).weaken (initialized.1.trans condition.1).next_le) bodyAccepted
      exact ⟨(State.restoreLexicalScope_inferenceProperties initialized.2 (condition.1.trans bodyProperties.1)).2,
        (inferStatementsFuel_direct_progress bodyAccepted).wellFormed ((inferExprFuel_direct_progress conditionAccepted).wellFormed
          ((inferForItemsFuel_direct_progress initializerAccepted).wellFormed allocated.2.1)),
        inputs.catalog.withLoopDepth _, trivial⟩
  | statement_match_single _ _ allocation _ _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, by simp [CallIndex.InputBounds]⟩
  | statement_match_many _ _ allocation _ _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, trivial⟩
  | statement_match_cases _ _ allocation scrutineeAccepted hiddenAllocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have scrutinee := matchScrutinee_properties allocated.1 inputs.catalog scrutineeAccepted
      have hidden := hiddenAllocation_inputs scrutinee.2.1
        (matchScrutinee_wellFormed allocated.2.1 scrutineeAccepted) hiddenAllocation
      exact ⟨hidden.1, hidden.2.1, inputs.catalog, hidden.2.2 ▸ scrutinee.2.2,
        hidden.2.2 ▸ (allocated.2.2 ▸ returnBound).weaken scrutinee.1.next_le, rfl⟩
  | statement_match_default _ _ allocation scrutineeAccepted hiddenAllocation casesAccepted _ _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have scrutinee := matchScrutinee_properties allocated.1 inputs.catalog scrutineeAccepted
      have hidden := hiddenAllocation_inputs scrutinee.2.1
        (matchScrutinee_wellFormed allocated.2.1 scrutineeAccepted) hiddenAllocation
      have returnBelow := hidden.2.2 ▸ (allocated.2.2 ▸ returnBound).weaken scrutinee.1.next_le
      have casesProperties := inferMatchCasesFuel_inferenceProperties hidden.1 inputs.catalog.formation inputs.catalog.canonical
        (hidden.2.2 ▸ scrutinee.2.2) returnBelow rfl casesAccepted
      exact ⟨casesProperties.2.1, (inferMatchCasesFuel_direct_progress casesAccepted).wellFormed hidden.2.1,
        inputs.catalog, returnBelow.weaken casesProperties.1.next_le⟩

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal
/-! Ordinary checker inputs follow every actual child edge from one root. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution

theorem ChildStep.inputs {parent child : CallIndex}
    (inputs : parent.Inputs) (step : ChildStep parent child) : child.Inputs := by
  cases parent with
  | expression =>
      cases step
      all_goals first
      | solve | apply ActualExpressionInputs.expression_group <;> assumption
      | solve | apply ActualExpressionInputs.expression_tuple <;> assumption
      | solve | apply ActualExpressionInputs.expression_call_arguments <;> assumption
      | solve | apply ActualExpressionInputs.expression_unary <;> assumption
      | solve | apply ActualExpressionInputs.expression_binary_left <;> assumption
      | solve | apply ActualExpressionInputs.expression_index_base <;> assumption
      | solve | apply ActualExpressionInputs.expression_conditional_condition <;> assumption
      | solve | apply ActualExpressionInputs.expression_binary_right <;> assumption
      | solve | apply ActualExpressionInputs.expression_call_callee <;> assumption
      | solve | apply ActualExpressionInputs.expression_conditional_then <;> assumption
      | solve | apply ActualExpressionInputs.expression_conditional_else <;> assumption
      | solve | apply ActualExpressionInputs.expression_index_key <;> assumption
      | solve | apply ActualExpressionInputs.expression_lambda_body <;> assumption
      | solve | apply ActualExpressionInputs.expression_contextual_constructor <;> assumption
      | solve | apply ActualExpressionInputs.expression_call_constructor <;> assumption
      | solve | apply ActualExpressionInputs.expression_field_constructor <;> assumption
  | constructorApplication => exact ChildStep.inputs_constructorApplication inputs step
  | constructorArguments => exact ChildStep.inputs_constructorArguments inputs step
  | statements => exact ChildStep.inputs_statements inputs step
  | statement => exact ChildStep.inputs_statement inputs step
  | forItems => exact ChildStep.inputs_forItems inputs step
  | forItem => exact ChildStep.inputs_forItem inputs step
  | place => exact ChildStep.inputs_place inputs step
  | assignedValue => exact ChildStep.inputs_assignedValue inputs step
  | expressions => exact ChildStep.inputs_expressions inputs step
  | matchCases => exact ChildStep.inputs_matchCases inputs step

theorem CallOccurrence.inputs {root call : CallIndex}
    (inputs : root.Inputs) (occurrence : CallOccurrence root call) : call.Inputs := by
  induction occurrence with
  | root _ => exact inputs
  | child _ step ih => exact step.inputs ih

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualCallOrder
/-! Immediate actual children are identical or ordered by the real allocator. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

def CallIndex.Ordered (left right : CallIndex) : Prop :=
  left = right ∨ left.final.inference.next ≤ right.initial.inference.next ∨
    right.final.inference.next ≤ left.initial.inference.next

theorem ChildStep.expressions_ordered
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {initial final : State} {values : List InferredExpression} {left right : CallIndex}
    (inputs : (CallIndex.expressions fuel context sources initial values final).Inputs)
    (leftStep : ChildStep (.expressions fuel context sources initial values final) left)
    (rightStep : ChildStep (.expressions fuel context sources initial values final) right) :
    left.Ordered right := by
  cases leftStep <;> cases rightStep <;> simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualExpressionCallOrder
/-! Expression siblings follow the allocator order of their actual prefix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2500000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

private theorem fresh_order {before after : State} {type : Ty}
    (accepted : before.fresh = (type, after)) :
    before.inference.next ≤ after.inference.next := by
  have same := congrArg (fun result : Ty × State => result.2.inference.next) accepted
  simp only [State.fresh, InferState.fresh] at same
  omega

private theorem fresh_pair_order {baseState keyState valueState fitted : State}
    {keyType valueType baseType : Ty}
    (fitting : unify valueState baseType (.mapping keyType valueType) = .ok fitted)
    (valueFresh : keyState.fresh = (valueType, valueState))
    (keyFresh : baseState.fresh = (keyType, keyState)) :
    baseState.inference.next ≤ fitted.inference.next := by
  have a := fresh_order keyFresh
  have b := fresh_order valueFresh
  have c := unify_next fitting
  omega

private theorem lambdaPrefix_unique
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial : State}
    {leftType rightType : Ty} {leftState rightState : State}
    (left : LambdaPrefixFacts context expected annotation types initial leftType leftState)
    (right : LambdaPrefixFacts context expected annotation types initial rightType rightState) :
    leftType = rightType ∧ leftState = rightState := by
  cases left <;> cases right <;> simp_all

private theorem conditional_then_next
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
    {value : InferredExpression}
    {condition thenBranch elseBranch : Syntax.Expr} {question colon : Syntax.SourceSpan}
    {conditionValue thenValue : InferredExpression} {conditionState thenState : State}
    (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
    (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
    (form : source.value = .conditional condition question thenBranch colon elseBranch)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
    (thenAccepted : inferExprFuel fuel context thenBranch expected conditionState = .ok (thenValue, thenState)) :
    conditionState.inference.next ≤ thenState.inference.next := by
  have childInputs := ActualExpressionInputs.expression_conditional_then
    accepted form allocation conditionAccepted thenAccepted inputs
  exact (childInputs.progress thenAccepted).1.next_le

theorem ChildStep.expression_ordered
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial final : State} {value : InferredExpression}
    {left right : CallIndex}
    (inputs : (CallIndex.expression fuel context source expected initial value final).Inputs)
    (leftStep : ChildStep (.expression fuel context source expected initial value final) left)
    (rightStep : ChildStep (.expression fuel context source expected initial value final) right) :
    left.Ordered right := by
  cases leftStep
  all_goals try
    have thenNext := conditional_then_next inputs (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)
  all_goals cases rightStep
  case expression_conditional_condition.expression_conditional_else =>
    rename_i accepted form allocation conditionAccepted thenAccepted child
    have thenNext := conditional_then_next inputs child form thenAccepted accepted allocation
    simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals first
    | solve | grind only [lambdaPrefix_unique]
    | (have fittedNext := fresh_pair_order (by assumption) (by assumption) (by assumption)
       omega)

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualNonExpressionCallOrder
/-! Actual non-expression siblings are identical or ordered by the allocator. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

private theorem hidden_next {before after : State} {id : Resolved.LocalId}
    (accepted : before.allocateHiddenLocal = (id, after)) :
    after.inference.next = before.inference.next := by
  have same := congrArg (fun result : Resolved.LocalId × State => result.2.inference.next) accepted
  simpa only [State.allocateHiddenLocal] using same.symm

private theorem match_single_next {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {source : Syntax.Expr} {initial final terminal : State}
    {value result : InferredExpression}
    (accepted : matchScrutinee fuel context span [source] initial = .ok (result, terminal))
    (child : inferExprFuel fuel context source none initial = .ok (value, final)) :
    terminal.inference.next = final.inference.next := by
  simp only [matchScrutinee, child, Except.ok.injEq, Prod.mk.injEq] at accepted
  exact congrArg (fun s : State => s.inference.next) accepted.2.symm

private theorem match_many_next {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {initial final terminal : State}
    {values : List InferredExpression} {result : InferredExpression}
    (multiple : ∀ source, sources ≠ [source])
    (accepted : matchScrutinee fuel context span sources initial = .ok (result, terminal))
    (child : inferExprsFuel fuel context sources initial = .ok (values, final)) :
    terminal.inference.next = final.inference.next := by
  unfold matchScrutinee at accepted
  split at accepted
  next => grind
  next other =>
    simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at accepted
    have same := congrArg (fun s : State => s.inference.next) accepted.2.symm
    change terminal.inference.next = final.inference.next at same
    exact same

open Lean Meta Elab Tactic in
elab "collect_allocator_order" : tactic => withMainContext do
  let hypotheses := (← getLCtx).getFVarIds
  for theoremName in [``unify_next, ``fresh_order, ``hidden_next] do
    for hypothesis in hypotheses do
      let saved ← saveState
      try
        let proof ← mkAppM theoremName #[mkFVar hypothesis]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved prefix"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "allocator_order") proof
        setGoals [next]
      catch _ => saved.restore
  for accepted in hypotheses do
    let type ← inferType (mkFVar accepted)
    unless type.isAppOf ``Eq do continue
    unless type.getAppArgs[1]!.isAppOf ``matchScrutinee do continue
    for child in hypotheses do
      let type ← inferType (mkFVar child)
      unless type.isAppOf ``Eq do continue
      unless type.getAppArgs[1]!.isAppOf ``inferExprFuel ||
          type.getAppArgs[1]!.isAppOf ``inferExprsFuel do continue
      let saved ← saveState
      try
        let proof ← mkAppM ``match_single_next #[mkFVar accepted, mkFVar child]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved singleton"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "scrutinee_order") proof
        setGoals [next]
      catch _ => saved.restore
      for multiple in hypotheses do
        let saved ← saveState
        try
          let proof ← mkAppM ``match_many_next #[mkFVar multiple, mkFVar accepted, mkFVar child]
          let proof ← instantiateMVars proof
          if proof.hasExprMVar then throwError "unresolved tuple"
          let (_, next) ← (← getMainGoal).note (Name.mkSimple "scrutinee_order") proof
          setGoals [next]
        catch _ => saved.restore

open Lean Meta Elab Tactic in
elab "collect_child_order " inputs:term : tactic => withMainContext do
  let inputsProof ← elabTerm inputs none
  let inputsType ← whnf (← inferType inputsProof)
  let parentCall := inputsType.getAppArgs[0]!
  let info ← getConstInfoInduct ``ChildStep
  for ctor in info.ctors do
    unless ctor.getString!.startsWith (parentCall.getAppFn.constName!.getString! ++ "_") do continue
    let saved ← saveState
    try
      withoutRecover do
        let goal ← getMainGoal
        let child ← mkFreshExprMVar (mkConst ``CallIndex)
        let stepType ← mkAppM ``ChildStep #[parentCall, child]
        let step ← mkFreshExprMVar stepType
        let pending ← step.mvarId!.apply (mkConst ctor)
        setGoals pending
        evalTactic (← `(tactic| all_goals (first | assumption | rfl)))
        unless (← getUnsolvedGoals).isEmpty do throwError "Unproved actual child prefix"
        let step ← instantiateMVars step
        let ready ← mkAppM ``ChildStep.inputs #[inputsProof, step]
        let accepted ← mkAppM ``ChildStep.child_accepted #[step]
        let progress ← mkAppM ``CallIndex.Inputs.progress #[ready, accepted]
        let progress ← mkAppM ``And.left #[progress]
        let order ← mkAppM ``State.InferenceProgress.next_le #[progress]
        let proof ← instantiateMVars order
        if proof.hasExprMVar then throwError "Unresolved actual child prefix"
        let (_, next) ← goal.note (Name.mkSimple ("order_" ++ ctor.getString!)) proof
        setGoals [next]
    catch _ => saved.restore


theorem ChildStep.constructorApplication_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {source : Syntax.Expr}
    {id : ExpressionId}
    {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr}
    {expected : Option Ty}
    {initial : State}
    {value : InferredExpression}
    {final : State}
    {left right : CallIndex}
    (inputs : (CallIndex.constructorApplication fuel context source id instantiation arguments expected initial value final).Inputs)
    (leftStep : ChildStep (CallIndex.constructorApplication fuel context source id instantiation arguments expected initial value final) left)
    (rightStep : ChildStep (CallIndex.constructorApplication fuel context source id instantiation arguments expected initial value final) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.constructorArguments_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {sources : List Syntax.Expr}
    {expectedTypes : List Ty}
    {initial : State}
    {values : List InferredExpression}
    {final : State}
    {left right : CallIndex}
    (inputs : (CallIndex.constructorArguments fuel context sources expectedTypes initial values final).Inputs)
    (leftStep : ChildStep (CallIndex.constructorArguments fuel context sources expectedTypes initial values final) left)
    (rightStep : ChildStep (CallIndex.constructorArguments fuel context sources expectedTypes initial values final) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.statements_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {sources : List Syntax.Statement}
    {expectedReturn : Ty}
    {initial : State}
    {result : BlockResult}
    {left right : CallIndex}
    (inputs : (CallIndex.statements fuel context sources expectedReturn initial result).Inputs)
    (leftStep : ChildStep (CallIndex.statements fuel context sources expectedReturn initial result) left)
    (rightStep : ChildStep (CallIndex.statements fuel context sources expectedReturn initial result) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.statement_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {source : Syntax.Statement}
    {expectedReturn : Ty}
    {initial : State}
    {result : StatementResult}
    {left right : CallIndex}
    (inputs : (CallIndex.statement fuel context source expectedReturn initial result).Inputs)
    (leftStep : ChildStep (CallIndex.statement fuel context source expectedReturn initial result) left)
    (rightStep : ChildStep (CallIndex.statement fuel context source expectedReturn initial result) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.forItems_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {sources : List Syntax.ForItem}
    {initial : State}
    {result : InferredForItems}
    {left right : CallIndex}
    (inputs : (CallIndex.forItems fuel context sources initial result).Inputs)
    (leftStep : ChildStep (CallIndex.forItems fuel context sources initial result) left)
    (rightStep : ChildStep (CallIndex.forItems fuel context sources initial result) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.forItem_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {source : Syntax.ForItem}
    {initial : State}
    {value : ForItemForm}
    {final : State}
    {left right : CallIndex}
    (inputs : (CallIndex.forItem fuel context source initial value final).Inputs)
    (leftStep : ChildStep (CallIndex.forItem fuel context source initial value final) left)
    (rightStep : ChildStep (CallIndex.forItem fuel context source initial value final) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.place_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {source : Syntax.Expr}
    {initial : State}
    {value : PlaceResolution}
    {final : State}
    {left right : CallIndex}
    (inputs : (CallIndex.place fuel context source initial value final).Inputs)
    (leftStep : ChildStep (CallIndex.place fuel context source initial value final) left)
    (rightStep : ChildStep (CallIndex.place fuel context source initial value final) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.assignedValue_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp}
    {value : Syntax.Expr}
    {initial : State}
    {assignment : AssignmentResolution}
    {inferred : InferredExpression}
    {final : State}
    {left right : CallIndex}
    (inputs : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Inputs)
    (leftStep : ChildStep (CallIndex.assignedValue fuel context target operator value initial assignment inferred final) left)
    (rightStep : ChildStep (CallIndex.assignedValue fuel context target operator value initial assignment inferred final) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals cases operator <;> simp_all only [pure, Pure.pure, Except.pure]
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.matchCases_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {scrutineeType expectedReturn : Ty}
    {saved : LexicalScope}
    {cases : List Syntax.MatchCase}
    {initial : State}
    {result : MatchCasesResult}
    {left right : CallIndex}
    (inputs : (CallIndex.matchCases fuel context scrutineeType expectedReturn saved cases initial result).Inputs)
    (leftStep : ChildStep (CallIndex.matchCases fuel context scrutineeType expectedReturn saved cases initial result) left)
    (rightStep : ChildStep (CallIndex.matchCases fuel context scrutineeType expectedReturn saved cases initial result) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualCallOrderTraversal
/-! Sibling calls in every actual inference family share a call or occupy
ordered allocator intervals. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution

theorem ChildStep.ordered {parent left right : CallIndex}
    (inputs : parent.Inputs) (first : ChildStep parent left) (second : ChildStep parent right) :
    left.Ordered right := by
  cases parent <;> first
    | exact ChildStep.expression_ordered inputs first second
    | exact ChildStep.expressions_ordered inputs first second
    | exact ChildStep.constructorApplication_ordered inputs first second
    | exact ChildStep.constructorArguments_ordered inputs first second
    | exact ChildStep.statements_ordered inputs first second
    | exact ChildStep.statement_ordered inputs first second
    | exact ChildStep.forItems_ordered inputs first second
    | exact ChildStep.forItem_ordered inputs first second
    | exact ChildStep.place_ordered inputs first second
    | exact ChildStep.assignedValue_ordered inputs first second
    | exact ChildStep.matchCases_ordered inputs first second

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualLocalAllocatorPrefixes
/-! Stable local identities stay below the actual allocator in every completed
prefix. This is independent of the inference metavariable allocator. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualLocalAllocator
open Frontend SourceInference TypeSystem Detail

private theorem pure_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result :=
  by change (Except.ok value = Except.ok result) ↔ value = result; simp
private theorem throw_ne_ok {epsilon alpha : Type} (error : epsilon) (value : alpha) :
    (throw error : Except epsilon alpha) ≠ .ok value := by intro impossible; cases impossible

private theorem expression_binders {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Expr} {expected : Option Ty} {initial : State}
    {result : InferredExpression × State}
    (accepted : inferExprFuel fuel context source expected initial = .ok result) :
    result.2.localBinders = initial.localBinders :=
  congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq accepted)
private theorem expressions_binders {fuel : Nat} {context : SourceInference.Context}
    {source : List Syntax.Expr} {initial : State} {result : List InferredExpression × State}
    (accepted : inferExprsFuel fuel context source initial = .ok result) :
    result.2.localBinders = initial.localBinders :=
  congrArg LexicalScope.binders (inferExprsFuel_success_lexicalScope_eq accepted)
private theorem place_binders {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Expr} {initial : State} {result : PlaceResolution × State}
    (accepted : inferPlaceFuel fuel context source initial = .ok result) :
    result.2.localBinders = initial.localBinders :=
  congrArg LexicalScope.binders (inferPlaceFuel_success_lexicalScope_eq accepted)
private theorem assigned_binders {fuel : Nat} {context : SourceInference.Context}
    {target source : Syntax.Expr} {operator : Syntax.ValueAssignOp} {initial final : State}
    {assignment : AssignmentResolution} {value : InferredExpression}
    (accepted : inferAssignedValueFuel fuel context target operator source initial = .ok (assignment,value,final)) :
    final.localBinders = initial.localBinders :=
  congrArg LexicalScope.binders (inferAssignedValueFuel_success_lexicalScope_eq accepted)
private theorem unified_binders {initial final : State} {left right : Ty}
    (accepted : unify initial left right = .ok final) : final.localBinders = initial.localBinders :=
  congrArg LexicalScope.binders (unify_preserves_lexicalScope accepted)
private theorem cases_binders {fuel : Nat} {context : SourceInference.Context} {scrutinee expected : Ty}
    {arms : List Syntax.MatchCase} {initial : State} {result : MatchCasesResult}
    (accepted : inferMatchCasesFuel fuel context scrutinee expected initial.lexicalScope arms initial = .ok result) :
    result.state.localBinders = initial.localBinders :=
  congrArg LexicalScope.binders (inferMatchCasesFuel_success_lexicalScope_eq rfl accepted)

private theorem statement_binders (state : State) :
    state.allocateStatementId.2.localBinders = state.localBinders := rfl
private theorem statement_next (state : State) :
    state.allocateStatementId.2.nextLocal = state.nextLocal := rfl
private theorem expressionId_binders (state : State) :
    state.allocateExpressionId.2.localBinders = state.localBinders := rfl
private theorem expressionId_next (state : State) :
    state.allocateExpressionId.2.nextLocal = state.nextLocal := rfl

/-- Only a direct declaration adds a binder to the returned statement scope.
Nested bodies restore the genuine saved scope. -/
theorem statement {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Statement} {expected : Ty} {initial : State} {result : StatementResult}
    (below : initial.LocalBindersBelowNextLocal)
    (accepted : inferStatementFuel fuel context source expected initial = .ok result) :
    result.state.LocalBindersBelowNextLocal := by
  have next := inferStatementFuel_nextLocal_le accepted
  cases fuel with
  | zero => simp [inferStatementFuel] at accepted
  | succ fuel =>
    unfold inferStatementFuel at accepted
    cases form : source.value <;> simp only [form, bind, Except.bind] at accepted
    all_goals repeat' first | split at accepted
    all_goals try cases accepted
    all_goals try simp_all only [pure_ok, throw_ne_ok]
    all_goals try subst_vars
    all_goals try have exprBinders := expression_binders (by assumption)
    all_goals try have exprNext := inferExprFuel_nextLocal_le (by assumption)
    all_goals try have exprsBinders := expressions_binders (by assumption)
    all_goals try have exprsNext := inferExprsFuel_nextLocal_le (by assumption)
    all_goals try have placeBinders := place_binders (by assumption)
    all_goals try have assignedBinders := assigned_binders (by assumption)
    all_goals try have unifiedBinders := unified_binders (by assumption)
    all_goals try have casesBinders := cases_binders (by assumption)
    all_goals simp_all only [State.recordNode, State.restoreLexicalScope, State.lexicalScope,
      State.allocateBinder, State.allocateHiddenLocal, statement_binders, statement_next,
      expressionId_binders, expressionId_next]
    all_goals intro binder member
    all_goals dsimp only at *
    all_goals try exact Nat.lt_of_lt_of_le (below binder member) next
    all_goals try (rcases List.mem_cons.mp member with current | old
                   · subst binder; exact Nat.lt_succ_self _
                   · have prior := below binder old; omega)

/-- The source-ordered fold applies the same statement result bound. -/
theorem statements {fuel : Nat} {context : SourceInference.Context}
    {sources : List Syntax.Statement} {expected : Ty} {initial : State} {result : BlockResult}
    (below : initial.LocalBindersBelowNextLocal)
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result) :
    result.state.LocalBindersBelowNextLocal := by
  induction fuel generalizing sources initial result with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil =>
      simp only [inferStatementsFuel, Except.ok.injEq] at accepted
      cases accepted
      exact below
    | cons head tail =>
      cases first : inferStatementFuel fuel context head expected initial with
      | error error => simp [inferStatementsFuel, first, bind, Except.bind] at accepted
      | ok firstResult =>
        have firstBelow := statement below first
        cases tail with
        | nil =>
          simp only [inferStatementsFuel, first, bind, Except.bind, pure_ok] at accepted
          cases accepted
          exact firstBelow
        | cons next rest =>
          cases remainder : inferStatementsFuel fuel context (next :: rest) expected firstResult.state with
          | error error => simp [inferStatementsFuel, first, remainder, bind, Except.bind] at accepted
          | ok tailResult =>
            simp only [inferStatementsFuel, first, remainder, bind, Except.bind, pure_ok] at accepted
            cases accepted
            exact ih (result := tailResult) firstBelow remainder

theorem parameters {context : SourceInference.Context} {sources : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State} {result : List TypedBinder × List Ty × State}
    (below : initial.LocalBindersBelowNextLocal)
    (accepted : bindLambdaParameters context sources index seen initial = .ok result) :
    result.2.2.LocalBindersBelowNextLocal := by
  induction sources generalizing index seen initial result with
  | nil =>
    simp only [bindLambdaParameters, Except.ok.injEq] at accepted
    cases accepted
    exact below
  | cons head tail ih =>
    unfold bindLambdaParameters at accepted
    cases form : head.value <;> simp only [form, bind, Except.bind] at accepted
    all_goals repeat' first | split at accepted
    all_goals try cases accepted
    all_goals try simp_all only [pure_ok, throw_ne_ok]
    all_goals try subst_vars
    all_goals apply ih (accepted := by assumption)
    all_goals apply State.allocateBinder_preserves_localBindersBelowNextLocal
    all_goals first | exact below | exact State.fresh_preserves_localBindersBelowNextLocal initial below

theorem pattern {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Pattern}
    {expected : Ty} {initial : State} {result : TypedMatchPattern × State}
    (below : initial.LocalBindersBelowNextLocal)
    (accepted : inferMatchPatternFuel fuel context source expected initial = .ok result) :
    result.2.LocalBindersBelowNextLocal := by
  unfold inferMatchPatternFuel at accepted
  cases actual : inferMatchPatternFlatFuel fuel context source expected [] initial with
  | error error => simp [actual, bind, Except.bind] at accepted
  | ok inferred =>
    simp only [actual, bind, Except.bind, pure_ok] at accepted
    cases accepted
    exact inferMatchPatternFlatFuel_preserves_localBindersBelowNextLocal
      fuel context source expected [] initial inferred below actual

theorem lambda_prefix {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial final : State} {result : Ty}
    (below : initial.LocalBindersBelowNextLocal)
    (prefixFacts : LambdaPrefixFacts context expected annotation types initial result final) :
    final.LocalBindersBelowNextLocal := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => exact below
  | noExpectedPartsFresh _ _ allocated =>
    have same : final = initial.fresh.2 := (congrArg Prod.snd allocated).symm
    rw [same]
    exact State.fresh_preserves_localBindersBelowNextLocal _ below
  | expectedPartsAnnotated _ unified => exact unify_preserves_localBindersBelowNextLocal below unified
  | expectedPartsInferred _ unified => exact unify_preserves_localBindersBelowNextLocal below unified

theorem match_scrutinee {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {initial : State}
    {result : InferredExpression × State} (below : initial.LocalBindersBelowNextLocal)
    (accepted : matchScrutinee fuel context span sources initial = .ok result) :
    result.2.LocalBindersBelowNextLocal := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact inferExprFuel_preserves_localBindersBelowNextLocal below accepted
  · cases actual : inferExprsFuel fuel context sources initial with
    | error error => simp [actual, bind, Except.bind] at accepted
    | ok inferred =>
      simp only [actual, bind, Except.bind, pure_ok] at accepted
      cases accepted
      apply State.recordNode_preserves_localBindersBelowNextLocal
      apply State.allocateExpressionId_preserves_localBindersBelowNextLocal
      exact inferExprsFuel_preserves_localBindersBelowNextLocal below actual

end Solcore.SourceSemantics.SourceInferenceExecution.ActualLocalAllocator
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualLocalAllocatorCalls
/-! Local-allocation bounds follow actual recursive inference calls. Every
saved scope is the one retained by the parent call, rather than an arbitrary
replacement of the binder stack. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualLocalAllocator
open Frontend SourceInference TypeSystem Detail

private theorem expressionAllocation {initial allocated : State} {id : ExpressionId}
    (allocation : initial.allocateExpressionId = (id, allocated))
    (below : initial.LocalBindersBelowNextLocal) : allocated.LocalBindersBelowNextLocal := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  exact State.allocateExpressionId_preserves_localBindersBelowNextLocal initial below
private theorem statementAllocation {initial allocated : State} {id : StatementId}
    (allocation : initial.allocateStatementId = (id, allocated))
    (below : initial.LocalBindersBelowNextLocal) : allocated.LocalBindersBelowNextLocal := by
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  exact State.allocateStatementId_preserves_localBindersBelowNextLocal initial below
private theorem freshAllocation {initial allocated : State} {type : Ty}
    (allocation : initial.fresh = (type, allocated))
    (below : initial.LocalBindersBelowNextLocal) : allocated.LocalBindersBelowNextLocal := by
  have same : allocated = initial.fresh.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  exact State.fresh_preserves_localBindersBelowNextLocal initial below
private theorem hiddenAllocation {initial allocated : State} {id : Resolved.LocalId}
    (allocation : initial.allocateHiddenLocal = (id, allocated))
    (below : initial.LocalBindersBelowNextLocal) : allocated.LocalBindersBelowNextLocal := by
  have same : allocated = initial.allocateHiddenLocal.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  exact State.allocateHiddenLocal_preserves_localBindersBelowNextLocal initial below
private theorem constructorAllocation {initial allocated : State} {value : DataConstructorInstantiation}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    (allocation : freshDataConstructorInstantiation dataType constructor initial = (value, allocated))
    (below : initial.LocalBindersBelowNextLocal) : allocated.LocalBindersBelowNextLocal := by
  have same : allocated = (freshDataConstructorInstantiation dataType constructor initial).2 :=
    (congrArg Prod.snd allocation).symm
  rw [same]
  exact freshDataConstructorInstantiation_preserves_localBindersBelowNextLocal dataType constructor initial below
private theorem optionalFit {initial fitted : State} {expected : Option Ty} {result : Ty}
    (accepted : (match expected with | none => pure initial | some type => unify initial result type) =
      (Except.ok fitted : Except Error State))
    (below : initial.LocalBindersBelowNextLocal) : fitted.LocalBindersBelowNextLocal := by
  cases expected with
  | none => cases Except.ok.inj accepted; exact below
  | some type => exact unify_preserves_localBindersBelowNextLocal below accepted
private theorem assignedFit {initial fitted : State} {operator : Syntax.ValueAssignOp} {target : Ty}
    (accepted : (match operator with | .equal => pure initial | _ => unify initial target .word) =
      (Except.ok fitted : Except Error State))
    (below : initial.LocalBindersBelowNextLocal) : fitted.LocalBindersBelowNextLocal := by
  cases operator
  · cases Except.ok.inj accepted; exact below
  all_goals exact unify_preserves_localBindersBelowNextLocal below accepted

private theorem expressionRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial : State} {value : InferredExpression} {final : State}
    (accepted : inferExprFuel fuel context source expected initial = .ok (value, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  inferExprFuel_preserves_localBindersBelowNextLocal below accepted
private theorem expressionsRun {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {initial : State} {values : List InferredExpression} {final : State}
    (accepted : inferExprsFuel fuel context sources initial = .ok (values, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  inferExprsFuel_preserves_localBindersBelowNextLocal below accepted
private theorem placeRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {initial : State} {place : PlaceResolution} {final : State}
    (accepted : inferPlaceFuel fuel context source initial = .ok (place, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  inferPlaceFuel_preserves_localBindersBelowNextLocal below accepted
private theorem itemsRun {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context sources initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) : result.state.LocalBindersBelowNextLocal :=
  inferForItemsFuel_preserves_localBindersBelowNextLocal below accepted
private theorem itemRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {item : ForItemForm} {final : State}
    (accepted : inferForItemFuel fuel context source initial = .ok (item, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  inferForItemFuel_preserves_localBindersBelowNextLocal below accepted
private theorem unifyRun {initial final : State} {left right : Ty}
    (accepted : unify initial left right = .ok final)
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  unify_preserves_localBindersBelowNextLocal below accepted
private theorem statementsRun {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult}
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) : result.state.LocalBindersBelowNextLocal :=
  statements below accepted
private theorem statementRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult}
    (accepted : inferStatementFuel fuel context source expected initial = .ok result)
    (below : initial.LocalBindersBelowNextLocal) : result.state.LocalBindersBelowNextLocal :=
  statement below accepted
private theorem parametersRun {context : SourceInference.Context} {sources : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State} {bound : List TypedBinder} {types : List Ty} {final : State}
    (accepted : bindLambdaParameters context sources index seen initial = .ok (bound, types, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  parameters below accepted
private theorem patternRun {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Pattern}
    {expected : Ty} {initial : State} {checkedPattern : TypedMatchPattern} {final : State}
    (accepted : inferMatchPatternFuel fuel context source expected initial = .ok (checkedPattern, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  pattern below accepted
private theorem lambdaPrefixRun {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial final : State} {result : Ty}
    (prefixFacts : LambdaPrefixFacts context expected annotation types initial result final)
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  lambda_prefix below prefixFacts
private theorem scrutineesRun {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial : State} {value : InferredExpression} {final : State}
    (accepted : matchScrutinee fuel context span sources initial = .ok (value, final))
    (below : initial.LocalBindersBelowNextLocal) : final.LocalBindersBelowNextLocal :=
  match_scrutinee below accepted

theorem child_bound {parent child : CallIndex} (inputs : parent.Inputs)
    (below : parent.initial.LocalBindersBelowNextLocal) (step : ChildStep parent child) :
    child.initial.LocalBindersBelowNextLocal := by
  cases step
  all_goals simp only [CallIndex.initial] at below ⊢
  all_goals try solve_by_elim (maxDepth := 10) (transparency := .reducible) [
    expressionAllocation, statementAllocation, freshAllocation, hiddenAllocation,
    constructorAllocation, optionalFit, assignedFit,
    expressionRun, expressionsRun, placeRun, itemsRun, itemRun, unifyRun,
    statementsRun, statementRun, parametersRun, patternRun, lambdaPrefixRun, scrutineesRun]

  case statement_if_else fuel context source expected initial allocated id result condition thenBody elseBody
      conditionValue conditionState body thenResult elseResult accepted form allocation conditionAccepted hasElse thenAccepted child =>
    exact State.restoreLexicalScope_preserves_localBindersBelowNextLocal
      (expressionRun conditionAccepted (statementAllocation allocation below))
      (inferStatementsFuel_nextLocal_le thenAccepted)
  case statement_for_post fuel context source expected initial allocated id result span initializer post condition body
      initialized conditionValue conditionState bodyResult postResult accepted form allocation initializerAccepted conditionAccepted bodyAccepted child =>
    exact State.restoreLexicalScope_preserves_localBindersBelowNextLocal
      (itemsRun initializerAccepted (statementAllocation allocation below))
      (Nat.le_trans (inferExprFuel_nextLocal_le conditionAccepted) (inferStatementsFuel_nextLocal_le bodyAccepted))
  case assignedValue_value fuel context target value operator initial final targetState assignment inferred place
      fitted childFinal childValue accepted targetAccepted fitting child =>
    have targetBelow := placeRun targetAccepted below
    cases operator <;> dsimp only at fitting
    · cases Except.ok.inj fitting; exact targetBelow
    all_goals exact unifyRun fitting targetBelow
  case constructorApplication_arguments fuel context source id instantiation sources expected initial fitted final childFinal
      value values accepted arity fitting child =>
    cases expected with
    | none => cases Except.ok.inj fitting; exact below
    | some type => exact unifyRun fitting below
  case expression_index_key fuel context source expected initial allocated final id value base key brackets baseValue keyValue
      baseState keyState valueState fitted childFinal keyType valueType accepted form allocation baseAccepted keyFresh valueFresh fitting child =>
    exact unifyRun fitting (freshAllocation valueFresh (freshAllocation keyFresh
      (expressionRun baseAccepted (expressionAllocation allocation below))))
  case matchCases_tail fuel context scrutinee expected saved arm arms initial patternState patternValue result body tail
      accepted patternAccepted bodyAccepted child =>
    have same : initial.lexicalScope = saved := inputs.bounds.2.2
    rw [← same]
    exact State.restoreLexicalScope_preserves_localBindersBelowNextLocal below
      (Nat.le_trans (inferMatchPatternFuel_nextLocal_le patternAccepted) (inferStatementsFuel_nextLocal_le bodyAccepted))
  case statement_match_default fuel context source expected initial allocated id result scrutinees arms scrutinee
      scrutineeState hiddenState hidden checked body bodyResult accepted form allocation scrutineeAccepted hiddenAllocated casesAccepted defaultBody child =>
    exact State.LocalBindersBelowNextLocal.transport
      (congrArg LexicalScope.binders (inferMatchCasesFuel_success_lexicalScope_eq rfl casesAccepted))
      (inferMatchCasesFuel_nextLocal_le casesAccepted)
      (hiddenAllocation hiddenAllocated (scrutineesRun scrutineeAccepted (statementAllocation allocation below)))

/-- The actual root initialization supplies the bound at every reached call. -/
theorem occurrence_bound {root call : CallIndex} (inputs : root.Inputs)
    (below : root.initial.LocalBindersBelowNextLocal) (here : CallOccurrence root call) :
    call.initial.LocalBindersBelowNextLocal := by
  induction here with
  | root _ => exact below
  | child path step ih => exact child_bound (path.inputs inputs) ih step

end Solcore.SourceSemantics.SourceInferenceExecution.ActualLocalAllocator
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualLocalReadCutoff
/-! An actual inference segment bounds both retained input reads and the
lookups it executes by its resulting local allocator. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

def LocalReadCutoff (state : State) : Prop :=
  ∀ node : ExpressionNode, .expression node ∈ state.nodes →
    ∀ name binder, node.form = .reference name (.local binder) →
      binder.binderIndex < state.nextLocal

namespace CallIndex

/-- The same eleven-family traversal can be rooted at this accepted segment. -/
theorem relativeReadProgress {call : CallIndex} (accepted : call.Accepted) :
    ActualGeneralization.RelativeReadProgress call call.initial call.final := by
  cases call <;> first
  | exact ActualGeneralization.inferExprFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferConstructorApplicationFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferConstructorArgumentsFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferStatementsFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferStatementFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferForItemsFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferForItemFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferPlaceFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferAssignedValueFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferExprsFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferMatchCasesFuel_relative_read_progress accepted (.root accepted)

/-- An old reference keeps its target; a new lookup lies inside this call's
actual allocator interval. Neither alternative assumes a later checkpoint. -/
theorem localReadCutoff {call : CallIndex} (accepted : call.Accepted)
    (inputs : call.Inputs) (below : call.initial.LocalBindersBelowNextLocal)
    (allocated : call.initial.DirectRequirementsAllocated)
    (previous : LocalReadCutoff call.initial) : LocalReadCutoff call.final := by
  have relative := (relativeReadProgress accepted).calls inputs.wellFormed allocated
    (RelativeLocalRead.Origins.initial call.initial.nodes)
  intro node member name binder form
  rcases relative node member name binder form with old | current
  · obtain ⟨original, present, _, sameForm⟩ := old
    exact Nat.lt_of_lt_of_le
      (previous original present name binder (sameForm.symm.trans form)) (call.local_next accepted)
  · obtain ⟨lookup, _, sameForm, here, present⟩ := current.active
    have sameBinder : binder = lookup.binder.id := by
      exact ReferenceResolution.local.inj (ExpressionForm.reference.inj (form.symm.trans sameForm)).2
    have localBound := ActualLocalAllocator.occurrence_bound inputs below here lookup.binder present
    have interval := here.local_interval
    have advanced := (ActualLocalRead.lookupCall lookup).local_next here.accepted
    rw [sameBinder]
    exact Nat.lt_of_lt_of_le localBound (Nat.le_trans advanced interval.2)

theorem directRequirementsAllocated {call : CallIndex} (accepted : call.Accepted)
    (wellFormed : call.initial.RequirementsWellFormed)
    (allocated : call.initial.DirectRequirementsAllocated) :
    call.final.DirectRequirementsAllocated :=
  (relativeReadProgress accepted).reads.ledger.allocated wellFormed allocated

end CallIndex
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualReadCutoffPrefixes
/-! Every recursive child starts after actual state-producing prefixes.
Existing reads and completed sibling calls retain a real local-ID cutoff. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

namespace LocalReadCutoff
theorem transport {before after : State} (same : after.nodes = before.nodes)
    (next : before.nextLocal ≤ after.nextLocal) (cutoff : LocalReadCutoff before) :
    LocalReadCutoff after := by
  intro node member name binder form
  exact Nat.lt_of_lt_of_le (cutoff node (same ▸ member) name binder form) next

theorem restore {state : State} (cutoff : LocalReadCutoff state) (scope : LexicalScope) :
    LocalReadCutoff (state.restoreLexicalScope scope) := cutoff

private theorem allocated_expression {before after : State} {id : ExpressionId}
    (accepted : before.allocateExpressionId = (id, after)) :
    LocalReadCutoff before → LocalReadCutoff after := by
  have same : after = before.allocateExpressionId.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact fun proof => proof
private theorem allocated_statement {before after : State} {id : StatementId}
    (accepted : before.allocateStatementId = (id, after)) :
    LocalReadCutoff before → LocalReadCutoff after := by
  have same : after = before.allocateStatementId.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact fun proof => proof
private theorem allocated_fresh {before after : State} {type : Ty}
    (accepted : before.fresh = (type, after)) :
    LocalReadCutoff before → LocalReadCutoff after := by
  have same : after = before.fresh.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact fun proof => proof
private theorem allocated_hidden {before after : State} {id : Resolved.LocalId}
    (accepted : before.allocateHiddenLocal = (id, after)) :
    LocalReadCutoff before → LocalReadCutoff after := by
  have same : after = before.allocateHiddenLocal.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact transport rfl (Nat.le_succ _)
private theorem allocated_constructor {before after : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation}
    (accepted : freshDataConstructorInstantiation dataType constructor before = (instantiation, after)) :
    LocalReadCutoff before → LocalReadCutoff after := by
  have same : after = (freshDataConstructorInstantiation dataType constructor before).2 :=
    (congrArg Prod.snd accepted).symm
  rw [same]
  exact transport (freshDataConstructorInstantiation_nodes _ _ _)
    (LocalReadScopeProgress.Progress.freshDataConstructorInstantiation _ _ _).next
private theorem unified {before after : State} {left right : Ty}
    (accepted : unify before left right = .ok after) :
    LocalReadCutoff before → LocalReadCutoff after :=
  transport (unify_occurrenceState_eq accepted).1
    (Nat.le_of_eq (localReadScope_unify_preserves_nextLocal accepted).symm)
private theorem parameters {context : SourceInference.Context} {sources : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {before : State} {result : List TypedBinder × List Ty × State}
    (accepted : bindLambdaParameters context sources index seen before = .ok result) :
    LocalReadCutoff before → LocalReadCutoff result.2.2 :=
  transport (bindLambdaParameters_occurrenceState_eq accepted).1
    (localReadScope_bindLambdaParameters_nextLocal_le accepted)
private theorem pattern {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Pattern}
    {expected : Ty} {before : State} {result : TypedMatchPattern × State}
    (accepted : inferMatchPatternFuel fuel context source expected before = .ok result) :
    LocalReadCutoff before → LocalReadCutoff result.2 :=
  transport (inferMatchPatternFuel_occurrenceState_eq accepted).1
    (inferMatchPatternFuel_nextLocal_le accepted)
private theorem lambda_prefix {context : SourceInference.Context}
    {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {types : List Ty} {before after : State} {resultType : Ty}
    (prefixFacts : LambdaPrefixFacts context expected annotation types before resultType after) :
    LocalReadCutoff before → LocalReadCutoff after := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => exact fun proof => proof
  | noExpectedPartsFresh _ _ allocated => exact allocated_fresh allocated
  | expectedPartsAnnotated _ accepted => exact unified accepted
  | expectedPartsInferred _ accepted => exact unified accepted

/-- Each prior call uses the inputs and stable binder bounds derived from the
same genuine parent edge. The implication is consumed in execution order. -/
private theorem child_transition {parent child : CallIndex}
    (inputs : parent.Inputs) (below : parent.initial.LocalBindersBelowNextLocal)
    (allocated : parent.initial.DirectRequirementsAllocated)
    (step : ChildStep parent child) :
    LocalReadCutoff child.initial → LocalReadCutoff child.final :=
  CallIndex.localReadCutoff step.child_accepted (step.inputs inputs)
    (ActualLocalAllocator.child_bound inputs below step)
    (step.direct_prefix.allocated inputs.wellFormed allocated)

private theorem match_prefix {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Statement} {expected : Ty} {initial allocated : State} {id : StatementId}
    {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {value : InferredExpression} {final : State}
    (inputs : (CallIndex.statement (fuel + 1) context source expected initial result).Inputs)
    (below : initial.LocalBindersBelowNextLocal)
    (direct : initial.DirectRequirementsAllocated) (previous : LocalReadCutoff initial)
    (accepted : (CallIndex.statement (fuel + 1) context source expected initial result).Accepted)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated =
      .ok (value, final)) : LocalReadCutoff final := by
  have allocatedCutoff := allocated_statement allocation previous
  unfold matchScrutinee at scrutineeAccepted
  split at scrutineeAccepted
  · have step := ChildStep.statement_match_single accepted form allocation
      (by assumption) scrutineeAccepted
    exact child_transition inputs below direct step allocatedCutoff
  · cases inferred : inferExprsFuel fuel context scrutinees.elements.toList allocated with
    | error error => simp [inferred, bind, Except.bind] at scrutineeAccepted
    | ok pair =>
      have step := ChildStep.statement_match_many accepted form allocation
        (by assumption) inferred
      have cutoff := child_transition inputs below direct step allocatedCutoff
      simp only [inferred, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq]
        at scrutineeAccepted
      cases scrutineeAccepted
      intro node member name binder localForm
      simp only [State.recordNode, List.mem_append, List.mem_singleton] at member
      rcases member with old | new
      · exact cutoff node old name binder localForm
      · cases Node.expression.inj new
        cases localForm

open Lean Meta Elab Tactic in
elab "collect_cutoff_prefix" : tactic => withMainContext do
  let hypotheses := (← getLCtx).getFVarIds
  for theoremName in [
      ``allocated_expression, ``allocated_statement, ``allocated_fresh, ``allocated_hidden,
      ``allocated_constructor, ``unified, ``parameters, ``pattern, ``lambda_prefix] do
    for hypothesis in hypotheses do
      let saved ← saveState
      try
        let proof ← mkAppM theoremName #[mkFVar hypothesis]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved cutoff prefix"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "cutoff_prefix") proof
        setGoals [next]
      catch _ => saved.restore

open Lean Meta Elab Tactic in
elab "collect_actual_sibling_cutoff" : tactic => withMainContext do
  let mut inputProof : Lean.Expr := default
  let mut parent : Lean.Expr := default
  for decl in ← getLCtx do
    if decl.type.isAppOfArity ``CallIndex.Inputs 1 then
      inputProof := decl.toExpr
      parent := decl.type.appArg!
      break
  if parent == default then throwError "actual parent inputs missing"
  let constructors := (← getConstInfoInduct ``ChildStep).ctors
  for constructor in constructors do
    let saved ← saveState
    try
      let child ← mkFreshExprMVar (mkConst ``CallIndex)
      let target := mkApp2 (mkConst ``ChildStep) parent child
      let proof ← mkFreshExprMVar target
      let goals ← proof.mvarId!.apply (mkConst constructor)
      for goal in goals do
        unless ← goal.isAssigned do goal.assumption
      let proof ← instantiateMVars proof
      if proof.hasExprMVar then throwError "unresolved actual sibling"
      let belowType ← mkAppM ``State.LocalBindersBelowNextLocal #[← mkAppM ``CallIndex.initial #[parent]]
      let directType ← mkAppM ``State.DirectRequirementsAllocated #[← mkAppM ``CallIndex.initial #[parent]]
      let some below ← findLocalDeclWithType? belowType | throwError "local binder bound missing"
      let some direct ← findLocalDeclWithType? directType | throwError "direct allocation missing"
      let transition ← mkAppM ``child_transition #[inputProof, mkFVar below, mkFVar direct, proof]
      let (_, next) ← (← getMainGoal).note (Name.mkSimple "sibling_cutoff") transition
      setGoals [next]
    catch _ => saved.restore
end LocalReadCutoff

theorem ChildStep.read_cutoff {parent child : CallIndex} (inputs : parent.Inputs)
    (below : parent.initial.LocalBindersBelowNextLocal)
    (allocated : parent.initial.DirectRequirementsAllocated)
    (previous : LocalReadCutoff parent.initial) (step : ChildStep parent child) :
    LocalReadCutoff child.initial := by
  cases step
  case assignedValue_value accepted targetAccepted fitting child =>
    split at fitting
    all_goals try cases Except.ok.inj fitting
    all_goals collect_actual_sibling_cutoff
    all_goals collect_cutoff_prefix
    all_goals simp only [CallIndex.initial, CallIndex.final] at *
    all_goals solve_by_elim (maxDepth := 10) (transparency := .reducible)
      [LocalReadCutoff.restore]
  case constructorApplication_arguments accepted arity fitting child =>
    split at fitting
    all_goals try cases Except.ok.inj fitting
    all_goals collect_actual_sibling_cutoff
    all_goals collect_cutoff_prefix
    all_goals simp only [CallIndex.initial, CallIndex.final] at *
    all_goals solve_by_elim (maxDepth := 10) (transparency := .reducible)
      [LocalReadCutoff.restore]
  all_goals collect_actual_sibling_cutoff
  all_goals collect_cutoff_prefix
  all_goals simp only [CallIndex.initial, CallIndex.final] at *
  all_goals try solve_by_elim (maxDepth := 10) (transparency := .reducible)
    [LocalReadCutoff.restore]
  case statement_match_cases =>
    have scrutinee := LocalReadCutoff.match_prefix inputs below allocated previous
      (by assumption) (by assumption) (by assumption) (by assumption)
    solve_by_elim (maxDepth := 5) (transparency := .reducible)
  case statement_match_default =>
    have scrutinee := LocalReadCutoff.match_prefix inputs below allocated previous
      (by assumption) (by assumption) (by assumption) (by assumption)
    solve_by_elim (maxDepth := 5) (transparency := .reducible)

theorem CallOccurrence.read_cutoff {root call : CallIndex} (inputs : root.Inputs)
    (below : root.initial.LocalBindersBelowNextLocal)
    (allocated : root.initial.DirectRequirementsAllocated)
    (previous : LocalReadCutoff root.initial) (here : CallOccurrence root call) :
    LocalReadCutoff call.initial := by
  induction here with
  | root _ => exact previous
  | child path step ih =>
    exact step.read_cutoff (path.inputs inputs)
      (ActualLocalAllocator.occurrence_bound inputs below path)
      (path.direct_prefix.allocated inputs.wellFormed allocated) ih

end Solcore.SourceSemantics.SourceInferenceExecution
end
