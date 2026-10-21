import Solcore.SourceSemantics.SourceInferenceActualTemplateBackingPrimitives

/-! Raw template witnesses at actual recursive checker entries. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualTemplateBacking
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

theorem matchScrutinee_backed
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial : State} {result : InferredExpression × State}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (catalog : LifetimeInferenceContext context)
    (accepted : matchScrutinee fuel context span sources initial = .ok result) :
    LiveTemplatesBacked result.2 := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact backed.inferExprFuel ready catalog.formation catalog.canonical (by simp) accepted
  · cases run : inferExprsFuel fuel context sources initial with
    | error error => simp [run, bind, Except.bind] at accepted
    | ok pair =>
      obtain ⟨values, state⟩ := pair
      simp only [run, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact (backed.inferExprsFuel ready catalog run).allocateExpressionId.recordNode _

theorem statement_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {expected : Option Ty} {value : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .letDecl name sourceType (some initializer))
      (allocation : initial.allocateStatementId = (id, allocated))
      (annotation : AnnotationExpected context sourceType expected)
      (child : (CallIndex.expression fuel context initializer expected allocated value final).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context initializer expected allocated value final).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context initializer expected allocated value final) := .statement_initializer accepted form allocation annotation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_return
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .returnStmt (some value))
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final) := .statement_return accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {semicolon : Bool} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .expression value semicolon)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value none allocated inferred final).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context value none allocated inferred final).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context value none allocated inferred final) := .statement_expression accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_block
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {body : List Syntax.Statement} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .block body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.statements fuel context body expectedReturn allocated bodyResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel context body expectedReturn allocated bodyResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context body expectedReturn allocated bodyResult) := .statement_block accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_if_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {thenBody : Syntax.Block} {elseBody : Option Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .ifThen condition thenBody elseBody)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState) := .statement_if_condition accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_assignment
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .assignValue target operator value)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final) := .statement_assignment accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan}
      {place : PlaceResolution} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .assignBitNot target operator)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.place fuel context target allocated place final).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.place fuel context target allocated place final).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.place fuel context target allocated place final) := .statement_bitnot accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_while_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {body : Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .whileLoop condition body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState) := .statement_while_condition accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_for_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.forItems fuel context initializer allocated initialized).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.forItems fuel context initializer allocated initialized).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.forItems fuel context initializer allocated initialized) := .statement_for_initializer accepted form allocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_match_single
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : Syntax.Expr} {value : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (single : scrutinees.elements.toList = [scrutinee])
      (child : (CallIndex.expression fuel context scrutinee none allocated value childFinal).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context scrutinee none allocated value childFinal).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context scrutinee none allocated value childFinal) := .statement_match_single accepted form allocation single child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_match_many
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {values : List InferredExpression} {childFinal : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (multiple : ∀ scrutinee, scrutinees.elements.toList ≠ [scrutinee])
      (child : (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal) := .statement_match_many accepted form allocation multiple child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact backed.allocateStatementId

theorem statement_if_then
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {thenBody : Syntax.Block} {elseBody : Option Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      {thenResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .ifThen condition thenBody elseBody)
      (allocation : initial.allocateStatementId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (child : (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult) := .statement_if_then accepted form allocation conditionAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.statement_if_condition accepted form allocation conditionAccepted)
  exact expression before backed.allocateStatementId conditionAccepted

theorem statement_if_else
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {thenBody : Syntax.Block} {elseBody : Option Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      {body : Syntax.Block} {thenResult elseResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .ifThen condition thenBody elseBody)
      (allocation : initial.allocateStatementId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (hasElse : elseBody = some body)
      (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionState = .ok thenResult)
      (child : (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult) := .statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.statement_if_condition accepted form allocation conditionAccepted)
  have conditionBacked := expression before backed.allocateStatementId conditionAccepted
  have thenInputs := ChildStep.inputs inputs (.statement_if_then accepted form allocation conditionAccepted thenAccepted)
  exact conditionBacked.restore (inferStatementsFuel_requirements_subset thenAccepted)
    (thenInputs.progress thenAccepted).1.substitution_extends

theorem statement_while_body
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {body : Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .whileLoop condition body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (child : (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult) := .statement_while_body accepted form allocation conditionAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.statement_while_condition accepted form allocation conditionAccepted)
  exact expression before backed.allocateStatementId conditionAccepted

theorem statement_for_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (initializerAccepted : inferForItemsFuel fuel context initializer allocated = .ok initialized)
      (child : (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState) := .statement_for_condition accepted form allocation initializerAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have before := ChildStep.inputs inputs (.statement_for_initializer accepted form allocation initializerAccepted)
  exact forItems before backed.allocateStatementId initializerAccepted

theorem statement_for_body
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      {conditionValue : InferredExpression} {conditionState : State} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (initializerAccepted : inferForItemsFuel fuel context initializer allocated = .ok initialized)
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) initialized.state = .ok (conditionValue, conditionState))
      (child : (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult) := .statement_for_body accepted form allocation initializerAccepted conditionAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have first := ChildStep.inputs inputs (.statement_for_initializer accepted form allocation initializerAccepted)
  have second := ChildStep.inputs inputs (.statement_for_condition accepted form allocation initializerAccepted conditionAccepted)
  exact expression second (forItems first backed.allocateStatementId initializerAccepted) conditionAccepted

theorem statement_for_post
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      {conditionValue : InferredExpression} {conditionState : State} {bodyResult : BlockResult}
      {postResult : InferredForItems}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (initializerAccepted : inferForItemsFuel fuel context initializer allocated = .ok initialized)
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) initialized.state = .ok (conditionValue, conditionState))
      (bodyAccepted : inferStatementsFuel fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState = .ok bodyResult)
      (child : (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult) := .statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have first := ChildStep.inputs inputs (.statement_for_initializer accepted form allocation initializerAccepted)
  have second := ChildStep.inputs inputs (.statement_for_condition accepted form allocation initializerAccepted conditionAccepted)
  have third := ChildStep.inputs inputs (.statement_for_body accepted form allocation initializerAccepted conditionAccepted bodyAccepted)
  have initializerBacked := forItems first backed.allocateStatementId initializerAccepted
  have through := (second.progress conditionAccepted).1.trans (third.progress bodyAccepted).1
  exact initializerBacked.restore
    (List.Subset.trans (inferExprFuel_requirements_subset conditionAccepted) (inferStatementsFuel_requirements_subset bodyAccepted))
    through.substitution_extends

theorem statement_match_cases
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
      {checked : MatchCasesResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
      (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
      (child : (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked) := .statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have scrutineeBacked := matchScrutinee_backed backed.allocateStatementId inputs.ready.allocateStatementId inputs.catalog scrutineeAccepted
  have sameHidden : hiddenState = scrutineeState.allocateHiddenLocal.2 := (congrArg Prod.snd hiddenAllocation).symm
  subst hiddenState
  exact scrutineeBacked.allocateHiddenLocal

theorem statement_match_default
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
      {checked : MatchCasesResult}
      {body : Syntax.Block} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
      (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
      (casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked)
      (default : arms.value.defaultBody = some body)
      (child : (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).Accepted)
      (inputs : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Inputs)
      (backed : LiveTemplatesBacked initial) : LiveTemplatesBacked (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).initial := by
  have step : ChildStep (CallIndex.statement (fuel + 1) context source expectedReturn initial result) (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult) := .statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child
  have childInputs := step.inputs inputs
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  have scrutineeBacked := matchScrutinee_backed backed.allocateStatementId inputs.ready.allocateStatementId inputs.catalog scrutineeAccepted
  have sameHidden : hiddenState = scrutineeState.allocateHiddenLocal.2 := (congrArg Prod.snd hiddenAllocation).symm
  subst hiddenState
  have before := ChildStep.inputs inputs (.statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted)
  exact matchCases before scrutineeBacked.allocateHiddenLocal casesAccepted

end Solcore.SourceSemantics.SourceInferenceExecution.ActualTemplateBacking
