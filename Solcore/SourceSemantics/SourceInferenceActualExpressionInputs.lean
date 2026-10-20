import Solcore.SourceSemantics.SourceInferenceActualCallProperties

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
