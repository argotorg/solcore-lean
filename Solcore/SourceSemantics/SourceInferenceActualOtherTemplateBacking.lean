import Solcore.SourceSemantics.SourceInferenceActualTemplateBackingPrimitives

/-! Raw template witnesses at actual recursive checker entries. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualTemplateBacking
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

theorem expressions_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final : State} {value : InferredExpression}
      {values : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle))
      (inputs : (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context source none initial value middle).initial := by
  have step : ChildStep (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final) (CallIndex.expression fuel context source none initial value middle) := .expressions_head accepted head
  have childInputs := step.inputs inputs
  exact backed

theorem statements_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)

      (child : (CallIndex.statement fuel context source expectedReturn initial head).Accepted)
      (inputs : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statement fuel context source expectedReturn initial head).initial := by
  have step : ChildStep (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result) (CallIndex.statement fuel context source expectedReturn initial head) := .statements_head accepted child
  have childInputs := step.inputs inputs
  exact backed

theorem forItems_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial final : State}
      {result : InferredForItems} {value : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)

      (child : (CallIndex.forItem fuel context source initial value final).Accepted)
      (inputs : (CallIndex.forItems fuel context (source :: sources) initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.forItem fuel context source initial value final).initial := by
  have step : ChildStep (CallIndex.forItems fuel context (source :: sources) initial result) (CallIndex.forItem fuel context source initial value final) := .forItems_head accepted child
  have childInputs := step.inputs inputs
  exact backed

theorem forItem_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {expected : Option Ty} {value : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .letDecl name sourceType (some initializer))
      (annotation : AnnotationExpected context sourceType expected)
      (child : (CallIndex.expression fuel context initializer expected initial value childFinal).Accepted)
      (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context initializer expected initial value childFinal).initial := by
  have step : ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.expression fuel context initializer expected initial value childFinal) := .forItem_initializer accepted form annotation child
  have childInputs := step.inputs inputs
  exact backed

theorem forItem_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {value : Syntax.Expr} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .expression value)
      (child : (CallIndex.expression fuel context value none initial inferred childFinal).Accepted)
      (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context value none initial inferred childFinal).initial := by
  have step : ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.expression fuel context value none initial inferred childFinal) := .forItem_expression accepted form child
  have childInputs := step.inputs inputs
  exact backed

theorem forItem_assignment
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignValue target operator value)
      (child : (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).Accepted)
      (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).initial := by
  have step : ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal) := .forItem_assignment accepted form child
  have childInputs := step.inputs inputs
  exact backed

theorem forItem_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan} {place : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignBitNot target operator)
      (child : (CallIndex.place fuel context target initial place childFinal).Accepted)
      (inputs : (CallIndex.forItem (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.place fuel context target initial place childFinal).initial := by
  have step : ChildStep (CallIndex.forItem (fuel + 1) context source initial result final) (CallIndex.place fuel context target initial place childFinal) := .forItem_bitnot accepted form child
  have childInputs := step.inputs inputs
  exact backed

theorem assignedValue_place
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)

      (child : (CallIndex.place fuel context target initial place targetState).Accepted)
      (inputs : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.place fuel context target initial place targetState).initial := by
  have step : ChildStep (CallIndex.assignedValue fuel context target operator value initial assignment inferred final) (CallIndex.place fuel context target initial place targetState) := .assignedValue_place accepted child
  have childInputs := step.inputs inputs
  exact backed

theorem place_group
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {inner : Syntax.Expr} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .group inner)
      (child : (CallIndex.place fuel context inner initial value childFinal).Accepted)
      (inputs : (CallIndex.place (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.place fuel context inner initial value childFinal).initial := by
  have step : ChildStep (CallIndex.place (fuel + 1) context source initial result final) (CallIndex.place fuel context inner initial value childFinal) := .place_group accepted form child
  have childInputs := step.inputs inputs
  exact backed

theorem place_index_base
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .index base brackets key)
      (child : (CallIndex.place fuel context base initial value childFinal).Accepted)
      (inputs : (CallIndex.place (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.place fuel context base initial value childFinal).initial := by
  have step : ChildStep (CallIndex.place (fuel + 1) context source initial result final) (CallIndex.place fuel context base initial value childFinal) := .place_index_base accepted form child
  have childInputs := step.inputs inputs
  exact backed

theorem constructorArguments_head
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)

      (child : (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).Accepted)
      (inputs : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).initial := by
  have step : ChildStep (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final) (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle) := .constructorArguments_head accepted child
  have childInputs := step.inputs inputs
  exact backed

theorem expressions_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final tailFinal : State} {value : InferredExpression}
      {values tailValues : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle))
      (tail : inferExprsFuel fuel context sources middle = .ok (tailValues, tailFinal))
      (inputs : (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expressions fuel context sources middle tailValues tailFinal).initial := by
  have step : ChildStep (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final) (CallIndex.expressions fuel context sources middle tailValues tailFinal) := .expressions_tail accepted head tail
  have childInputs := step.inputs inputs
  have before := ChildStep.inputs inputs (.expressions_head accepted head)
  exact expression before backed head

theorem statements_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result tail : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)
      (nonempty : sources ≠ [])
      (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
      (child : (CallIndex.statements fuel context sources expectedReturn head.state tail).Accepted)
      (inputs : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel context sources expectedReturn head.state tail).initial := by
  have step : ChildStep (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result) (CallIndex.statements fuel context sources expectedReturn head.state tail) := .statements_tail accepted nonempty headAccepted child
  have childInputs := step.inputs inputs
  have before := ChildStep.inputs inputs (.statements_head accepted headAccepted)
  exact statement before backed headAccepted

theorem forItems_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial middle : State}
      {result tail : InferredForItems} {head : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)
      (headAccepted : inferForItemFuel fuel context source initial = .ok (head, middle))
      (child : (CallIndex.forItems fuel context sources middle tail).Accepted)
      (inputs : (CallIndex.forItems fuel context (source :: sources) initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.forItems fuel context sources middle tail).initial := by
  have step : ChildStep (CallIndex.forItems fuel context (source :: sources) initial result) (CallIndex.forItems fuel context sources middle tail) := .forItems_tail accepted headAccepted child
  have childInputs := step.inputs inputs
  have before := ChildStep.inputs inputs (.forItems_head accepted headAccepted)
  exact forItem before backed headAccepted

theorem constructorArguments_tail
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      {tailValues : List InferredExpression} {tailFinal : State}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)
      (headAccepted : inferExprFuel fuel context source (some (initial.resolve expected)) initial = .ok (value, middle))
      (child : (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal).Accepted)
      (inputs : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal).initial := by
  have step : ChildStep (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final) (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal) := .constructorArguments_tail accepted headAccepted child
  have childInputs := step.inputs inputs
  have before := ChildStep.inputs inputs (.constructorArguments_head accepted headAccepted)
  exact expression before backed headAccepted

theorem assignedValue_value
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      {fitted childFinal : State} {childValue : InferredExpression}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)
      (targetAccepted : inferPlaceFuel fuel context target initial = .ok (place, targetState))
      (fitting : (match operator with | .equal => pure targetState | _ => unify targetState place.type .word) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).Accepted)
      (inputs : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).initial := by
  have step : ChildStep (CallIndex.assignedValue fuel context target operator value initial assignment inferred final) (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal) := .assignedValue_value accepted targetAccepted fitting child
  have childInputs := step.inputs inputs
  have before := ChildStep.inputs inputs (.assignedValue_place accepted targetAccepted)
  have targetBacked := ActualTemplateBacking.place before backed targetAccepted
  have targetReady := (before.progress targetAccepted).2.1
  cases operator <;> first
  | (change Except.ok targetState = Except.ok fitted at fitting
     cases Except.ok.inj fitting
     exact targetBacked)
  | exact targetBacked.unify targetReady.solved fitting

theorem place_index_key
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {baseValue : PlaceResolution}
      {baseState keyState valueState fitted childFinal : State} {keyType valueType : Ty}
      {keyValue : InferredExpression}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .index base brackets key)
      (baseAccepted : inferPlaceFuel fuel context base initial = .ok (baseValue, baseState))
      (keyFresh : baseState.fresh = (keyType, keyState))
      (valueFresh : keyState.fresh = (valueType, valueState))
      (fitting : unify valueState baseValue.type (.mapping keyType valueType) = .ok fitted)
      (child : (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).Accepted)
      (inputs : (CallIndex.place (fuel + 1) context source initial result final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).initial := by
  have step : ChildStep (CallIndex.place (fuel + 1) context source initial result final) (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal) := .place_index_key accepted form baseAccepted keyFresh valueFresh fitting child
  have childInputs := step.inputs inputs
  have before := ChildStep.inputs inputs (.place_index_base accepted form baseAccepted)
  have baseBacked := place before backed baseAccepted
  have baseReady := (before.progress baseAccepted).2.1
  have sameKey : keyState = baseState.fresh.2 := (congrArg Prod.snd keyFresh).symm
  subst keyState
  have sameValue : valueState = baseState.fresh.2.fresh.2 := (congrArg Prod.snd valueFresh).symm
  subst valueState
  exact baseBacked.fresh.fresh.unify baseReady.fresh.fresh.solved fitting

theorem constructorApplication_arguments
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
      {instantiation : DataConstructorInstantiation} {sources : List Syntax.Expr} {expected : Option Ty}
      {initial fitted final childFinal : State} {value : InferredExpression} {values : List InferredExpression}
      (accepted : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Accepted)
      (arity : sources.length = instantiation.payloadTypes.length)
      (fitting : (match expected with | none => pure initial | some type => unify initial instantiation.resultType type) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).Accepted)
      (inputs : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).initial := by
  have step : ChildStep (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final) (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal) := .constructorApplication_arguments accepted arity fitting child
  have childInputs := step.inputs inputs
  cases expected with
  | none =>
    change Except.ok initial = Except.ok fitted at fitting
    cases Except.ok.inj fitting
    exact backed
  | some type => exact backed.unify inputs.ready.solved fitting

theorem matchCases_body
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (child : (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).Accepted)
      (inputs : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).initial := by
  have step : ChildStep (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result) (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body) := .matchCases_body accepted patternAccepted child
  have childInputs := step.inputs inputs
  have progress := inferMatchPatternFuel_inferenceProperties inputs.ready inputs.bounds.1 inputs.catalog.formation patternAccepted
  exact (inferMatchPatternFuel_scope patternAccepted).templates backed
    (inferMatchPatternFuel_requirements_subset patternAccepted) progress.1.substitution_extends

theorem matchCases_tail
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      {tail : MatchCasesResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState = .ok body)
      (child : (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail).Accepted)
      (inputs : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail).initial := by
  have step : ChildStep (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result) (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail) := .matchCases_tail accepted patternAccepted bodyAccepted child
  have childInputs := step.inputs inputs
  have patternProperties := inferMatchPatternFuel_inferenceProperties inputs.ready inputs.bounds.1 inputs.catalog.formation patternAccepted
  have bodyInputs := ChildStep.inputs inputs (.matchCases_body accepted patternAccepted bodyAccepted)
  have bodyProperties := bodyInputs.progress bodyAccepted
  have rows := List.Subset.trans (inferMatchPatternFuel_requirements_subset patternAccepted)
    (inferStatementsFuel_requirements_subset bodyAccepted)
  have result := backed.restore rows (patternProperties.1.trans bodyProperties.1).substitution_extends
  change LiveTemplatesBacked (body.state.restoreLexicalScope initial.lexicalScope) at result
  rw [inputs.bounds.2.2] at result
  exact result

end Solcore.SourceSemantics.SourceInferenceExecution.ActualTemplateBacking
