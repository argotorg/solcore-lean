import Solcore.SourceSemantics.SourceInferenceActualTemplateBackingPrimitives

/-! Template backing at the actual expression-family child entries. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualTemplateBacking
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

theorem expression_group
      {fuel : Nat} {context : SourceInference.Context} {source inner : Syntax.Expr}
      {expected : Option Ty} {initial allocated final childFinal : State}
      {id : ExpressionId} {value childValue : InferredExpression}
      (accepted : (CallIndex.expression (fuel + 1) context source expected
        initial value final).Accepted)
      (form : source.value = .group inner)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : inferExprFuel fuel context inner expected allocated =
        .ok (childValue, childFinal))
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context inner expected allocated childValue childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context inner expected allocated childValue childFinal) := .expression_group accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_tuple
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {elements : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
      {initial allocated final childFinal : State} {id : ExpressionId}
      {value : InferredExpression} {values : List InferredExpression}
      (accepted : (CallIndex.expression (fuel + 1) context source expected
        initial value final).Accepted)
      (form : source.value = .tuple elements)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : inferExprsFuel fuel context elements.elements allocated =
        .ok (values, childFinal))
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expressions fuel context elements.elements allocated values childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expressions fuel context elements.elements allocated values childFinal) := .expression_tuple accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_unary
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {operator : Syntax.Located Syntax.UnaryOp} {operand : Syntax.Expr}
      {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .unary operator operand)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : (CallIndex.expression fuel context operand none allocated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context operand none allocated inferred childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context operand none allocated inferred childFinal) := .expression_unary accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_binary_left
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {operator : Syntax.Located Syntax.BinaryOp} {left right : Syntax.Expr}
      {leftValue : InferredExpression} {leftState : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .binary left operator right)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : (CallIndex.expression fuel context left none allocated leftValue leftState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context left none allocated leftValue leftState).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context left none allocated leftValue leftState) := .expression_binary_left accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_conditional_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {condition thenBranch elseBranch : Syntax.Expr} {question colon : Syntax.SourceSpan}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .conditional condition question thenBranch colon elseBranch)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState) := .expression_conditional_condition accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_index_base
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan}
      {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .index base brackets key)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (child : (CallIndex.expression fuel context base none allocated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context base none allocated inferred childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context base none allocated inferred childFinal) := .expression_index_base accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_call_arguments
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr}
      {values : List InferredExpression} {childFinal : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .call callee arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
      (child : (CallIndex.expressions fuel context arguments.elements allocated values childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expressions fuel context arguments.elements allocated values childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expressions fuel context arguments.elements allocated values childFinal) := .expression_call_arguments accepted form allocation nonconstructor child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_contextual_constructor
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {dot : Syntax.SourceSpan} {name : Syntax.Identifier} {arguments : Option (Syntax.DelimitedList Syntax.Expr)}
      {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {typeArguments : List Ty}
      {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .dotConstructor dot name arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (selected : contextualConstructorCandidate context allocated expected name.value = .ok (dataType, constructor, typeArguments))
      (child : (CallIndex.constructorApplication fuel context source id (instantiateDataConstructor dataType constructor typeArguments) (arguments.map (·.elements) |>.getD []) expected allocated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.constructorApplication fuel context source id (instantiateDataConstructor dataType constructor typeArguments) (arguments.map (·.elements) |>.getD []) expected allocated inferred childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.constructorApplication fuel context source id (instantiateDataConstructor dataType constructor typeArguments) (arguments.map (·.elements) |>.getD []) expected allocated inferred childFinal) := .expression_contextual_constructor accepted form allocation selected child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateExpressionId

theorem expression_binary_right
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {operator : Syntax.Located Syntax.BinaryOp} {left right : Syntax.Expr}
      {leftValue : InferredExpression} {leftState : State}
      {rightValue : InferredExpression} {rightState : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .binary left operator right)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (leftAccepted : inferExprFuel fuel context left none allocated = .ok (leftValue, leftState))
      (child : (CallIndex.expression fuel context right none leftState rightValue rightState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context right none leftState rightValue rightState).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context right none leftState rightValue rightState) := .expression_binary_right accepted form allocation leftAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.expression_binary_left accepted form allocation leftAccepted)
  exact expression before backed.allocateExpressionId leftAccepted

theorem expression_conditional_then
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {condition thenBranch elseBranch : Syntax.Expr} {question colon : Syntax.SourceSpan}
      {conditionValue : InferredExpression} {conditionState : State}
      {thenValue : InferredExpression} {thenState : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .conditional condition question thenBranch colon elseBranch)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (child : (CallIndex.expression fuel context thenBranch expected conditionState thenValue thenState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context thenBranch expected conditionState thenValue thenState).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context thenBranch expected conditionState thenValue thenState) := .expression_conditional_then accepted form allocation conditionAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.expression_conditional_condition accepted form allocation conditionAccepted)
  exact expression before backed.allocateExpressionId conditionAccepted

theorem expression_conditional_else
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {condition thenBranch elseBranch : Syntax.Expr} {question colon : Syntax.SourceSpan}
      {conditionValue : InferredExpression} {conditionState : State}
      {thenValue elseValue : InferredExpression} {thenState elseState : State}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .conditional condition question thenBranch colon elseBranch)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (thenAccepted : inferExprFuel fuel context thenBranch expected conditionState = .ok (thenValue, thenState))
      (child : (CallIndex.expression fuel context elseBranch expected thenState elseValue elseState).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context elseBranch expected thenState elseValue elseState).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context elseBranch expected thenState elseValue elseState) := .expression_conditional_else accepted form allocation conditionAccepted thenAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have first := ChildStep.inputs inputs (.expression_conditional_condition accepted form allocation conditionAccepted)
  have second := ChildStep.inputs inputs (.expression_conditional_then accepted form allocation conditionAccepted thenAccepted)
  exact expression second (expression first backed.allocateExpressionId conditionAccepted) thenAccepted

theorem expression_call_callee
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr}
      {values : List InferredExpression} {argumentState childFinal : State} {inferred : InferredExpression}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .call callee arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
      (argumentsAccepted : inferExprsFuel fuel context arguments.elements allocated = .ok (values, argumentState))
      (indirect : IndirectCalleeAt context callee argumentState)
      (child : (CallIndex.expression fuel context callee none argumentState inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context callee none argumentState inferred childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context callee none argumentState inferred childFinal) := .expression_call_callee accepted form allocation nonconstructor argumentsAccepted indirect child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.expression_call_arguments accepted form allocation nonconstructor argumentsAccepted)
  exact expressions before backed.allocateExpressionId argumentsAccepted

theorem expression_lambda_body
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
      {annotation : Option Syntax.TypeExpr} {body : Syntax.Block}
      {boundParameters : List TypedBinder} {parameterTypes : List Ty}
      {parameterState bodyState : State} {resultType : Ty} {bodyResult : BlockResult}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .lambda keyword parameters annotation body)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (parametersAccepted : bindLambdaParameters context parameters.elements 0 [] allocated = .ok (boundParameters, parameterTypes, parameterState))
      (prefixFacts : LambdaPrefixFacts context expected annotation parameterTypes parameterState resultType bodyState)
      (child : (CallIndex.statements fuel { context with loopDepth := 0 } body.value resultType bodyState bodyResult).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel { context with loopDepth := 0 } body.value resultType bodyState bodyResult).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.statements fuel { context with loopDepth := 0 } body.value resultType bodyState bodyResult) := .expression_lambda_body accepted form allocation parametersAccepted prefixFacts child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have parameters := bindLambdaParameters_inferenceProperties inputs.ready.allocateExpressionId parametersAccepted
  exact (backed.allocateExpressionId.bindLambdaParameters parametersAccepted).lambdaPrefix parameters.2.1 prefixFacts

theorem expression_index_key
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {baseValue keyValue : InferredExpression}
      {baseState keyState valueState fitted childFinal : State} {keyType valueType : Ty}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .index base brackets key)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (baseAccepted : inferExprFuel fuel context base none allocated = .ok (baseValue, baseState))
      (keyFresh : baseState.fresh = (keyType, keyState))
      (valueFresh : keyState.fresh = (valueType, valueState))
      (fitting : unify valueState baseValue.type (.mapping keyType valueType) = .ok fitted)
      (child : (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal) := .expression_index_key accepted form allocation baseAccepted keyFresh valueFresh fitting child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.expression_index_base accepted form allocation baseAccepted)
  have baseBacked := expression before backed.allocateExpressionId baseAccepted
  have baseReady := (before.progress baseAccepted).2.1
  have sameKey : keyState = baseState.fresh.2 := (congrArg Prod.snd keyFresh).symm
  subst keyState
  have sameValue : valueState = baseState.fresh.2.fresh.2 := (congrArg Prod.snd valueFresh).symm
  subst valueState
  exact baseBacked.fresh.fresh.unify baseReady.fresh.fresh.solved fitting

theorem expression_call_constructor
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {callee : Syntax.Expr} {arguments : Syntax.DelimitedList Syntax.Expr}
      {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
      {instantiation : DataConstructorInstantiation} {instantiated childFinal : State}
      {inferred : InferredExpression}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .call callee arguments)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (selected : constructorCalleeCandidates context allocated callee = .ok [(dataType, constructor)])
      (fresh : freshDataConstructorInstantiation dataType constructor allocated = (instantiation, instantiated))
      (child : (CallIndex.constructorApplication fuel context source id instantiation arguments.elements expected instantiated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.constructorApplication fuel context source id instantiation arguments.elements expected instantiated inferred childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.constructorApplication fuel context source id instantiation arguments.elements expected instantiated inferred childFinal) := .expression_call_constructor accepted form allocation selected fresh child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have sameFresh : instantiated = (freshDataConstructorInstantiation dataType constructor initial.allocateExpressionId.2).2 :=
    (congrArg Prod.snd fresh).symm
  subst instantiated
  exact backed.allocateExpressionId.freshConstructor dataType constructor

theorem expression_field_constructor
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {expected : Option Ty} {initial allocated final : State} {id : ExpressionId}
      {value : InferredExpression}
      {base : Syntax.Expr} {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
      {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
      {instantiation : DataConstructorInstantiation} {instantiated childFinal : State}
      {inferred : InferredExpression}
      (accepted : (CallIndex.expression (fuel + 1) context source expected initial value final).Accepted)
      (form : source.value = .field base dot name)
      (allocation : initial.allocateExpressionId = (id, allocated))
      (selected : constructorCalleeCandidates context allocated source = .ok [(dataType, constructor)])
      (fresh : freshDataConstructorInstantiation dataType constructor allocated = (instantiation, instantiated))
      (child : (CallIndex.constructorApplication fuel context source id instantiation [] expected instantiated inferred childFinal).Accepted)
      (inputs : (CallIndex.expression (fuel + 1) context source expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.constructorApplication fuel context source id instantiation [] expected instantiated inferred childFinal).initial := by
  have step : ChildStep (CallIndex.expression (fuel + 1) context source expected initial value final) (CallIndex.constructorApplication fuel context source id instantiation [] expected instantiated inferred childFinal) := .expression_field_constructor accepted form allocation selected fresh child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have sameFresh : instantiated = (freshDataConstructorInstantiation dataType constructor initial.allocateExpressionId.2).2 :=
    (congrArg Prod.snd fresh).symm
  subst instantiated
  exact backed.allocateExpressionId.freshConstructor dataType constructor

end Solcore.SourceSemantics.SourceInferenceExecution.ActualTemplateBacking
