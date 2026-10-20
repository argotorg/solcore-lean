import Solcore.SourceSemantics.SourceInferenceNormalizedLambdaContinuation

/-! The actual for statement supplies header capture checks through its final
recorded node and threads normalized formation through both saved scopes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail

theorem inferStatementFuel_for_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .forLoop headerSpan initializer condition post body)
    (initializerIH : InferForItemsFuelFormation semantic outer fuel context initializer initial.allocateStatementId.2)
    (conditionIH : ∀ initialized : InferredForItems,
      InferExprFuelFormation semantic outer fuel context condition (some .bool) initialized.state)
    (bodyIH : ∀ state, InferStatementsFuelFormation semantic outer fuel
      {context with loopDepth := context.loopDepth + 1} body.value expectedReturn state)
    (postIH : ∀ (initialized : InferredForItems) (checkedBody : BlockResult),
      InferForItemsFuelFormation semantic outer fuel {context with loopDepth := context.loopDepth + 1} post
        (checkedBody.state.restoreLexicalScope initialized.state.lexicalScope)) :
    InferStatementFuelFormation semantic outer (fuel+1) context statement expectedReturn initial := by
  intro ready nodes formed formation returnBelow returnFormed result success continuation capture
  let id := initial.allocateStatementId.1
  let allocated := initial.allocateStatementId.2
  let loopContext := {context with loopDepth := context.loopDepth + 1}
  have allocationEq : initial.allocateStatementId = (id,allocated) := rfl
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedNodes := State.allocateStatementId_preserves_nodesBelowNextOccurrence initial nodes
  have allocatedFormed : NormalizedStateFormation semantic outer allocated := formed.congr rfl rfl
  have loopFormation : InferenceFormationContext semantic loopContext outer := formation.withLoopDepth (context.loopDepth+1)
  unfold inferStatementFuel at success
  simp only [allocationEq,form,bind,Except.bind] at success
  cases initializerRun : inferForItemsFuel fuel context initializer allocated with
  | error error => simp [initializerRun] at success
  | ok initialized =>
    simp only [initializerRun] at success
    have initProperties := inferForItemsFuel_inferenceProperties allocatedReady formation.validated formation.functionShapes initializerRun
    have initNodes := (inferForItemsFuel_occurrenceBoundExtends initializerRun).nodesBelowNextOccurrence allocatedNodes
    cases conditionRun : inferExprFuel fuel context condition (some .bool) initialized.state with
    | error error => simp [conditionRun] at success
    | ok conditionPair =>
      rcases conditionPair with ⟨checkedCondition,conditionState⟩
      simp only [conditionRun] at success
      have boolBelow : ∀ type ∈ some Ty.bool, type.VariablesBelow initialized.state.inference.next := by
        intro type member
        cases Option.mem_def.mp member
        exact Ty.variablesBelow_constructor _ _
      have boolFormed : ∀ type ∈ some Ty.bool, TypeAdmissible semantic (outer.apply type) := by
        intro type member
        cases Option.mem_def.mp member
        exact .bool formation.scope.binders
      have conditionProperties := inferExprFuel_inferenceProperties initProperties.2 formation.validated formation.functionShapes boolBelow conditionRun
      have conditionNodes := (inferExprFuel_occurrenceBoundExtends conditionRun).nodesBelowNextOccurrence initNodes
      have throughCondition := initProperties.1.trans conditionProperties.1
      cases bodyRun : inferStatementsFuel fuel loopContext body.value expectedReturn conditionState with
      | error error => simp [loopContext,bodyRun] at success
      | ok checkedBody =>
        simp only [loopContext,bodyRun] at success
        have bodyProperties := inferStatementsFuel_inferenceProperties (context := loopContext)
          conditionProperties.2.1 formation.validated formation.functionShapes
          (returnBelow.weaken throughCondition.next_le) bodyRun
        have bodyNodes := (inferStatementsFuel_occurrenceBoundExtends bodyRun).nodesBelowNextOccurrence conditionNodes
        let afterBody := checkedBody.state.restoreLexicalScope initialized.state.lexicalScope
        have restoredProperties := State.restoreLexicalScope_inferenceProperties initProperties.2
          (conditionProperties.1.trans bodyProperties.1)
        have afterBodyNodes : afterBody.NodesBelowNextOccurrence := bodyNodes
        cases postRun : inferForItemsFuel fuel loopContext post afterBody with
        | error error => simp [loopContext,afterBody,postRun] at success
        | ok checkedPost =>
          simp only [loopContext,afterBody,postRun,pure,Pure.pure,Except.pure,Except.ok.injEq] at success
          subst result
          let node : StatementNode := {
            id,span := statement.span,type := .unit,
            form := .forLoop initialized.items checkedCondition.id checkedPost.items checkedBody.statements }
          have finalCapture : NoCaptureNodes outer (checkedPost.state.nodes ++ [.statement node]) := capture
          have headerCapture := finalCapture.for_items (List.mem_append_right _ (List.mem_singleton_self _))
          have postCapture : NoCaptureNodes outer checkedPost.state.nodes :=
            finalCapture.of_prefix (List.prefix_append _ _)
          have postContinuation : outer.SemanticallyExtends checkedPost.state.inference.substitution := continuation
          have postProperties := inferForItemsFuel_inferenceProperties (context := loopContext) restoredProperties.2
            formation.validated formation.functionShapes postRun
          have bodyContinuation : outer.SemanticallyExtends checkedBody.state.inference.substitution :=
            postContinuation.trans postProperties.1.substitution_extends
          have conditionContinuation := bodyContinuation.trans bodyProperties.1.substitution_extends
          have initializerContinuation := conditionContinuation.trans conditionProperties.1.substitution_extends
          have bodyRetained : checkedBody.state.nodes <+: checkedPost.state.nodes :=
            inferForItemsFuel_preserves_nodesPrefix postRun (List.prefix_refl _) afterBodyNodes (Nat.le_refl _)
          have bodyCapture := postCapture.of_prefix bodyRetained
          have conditionRetained : conditionState.nodes <+: checkedBody.state.nodes :=
            inferStatementsFuel_preserves_nodesPrefix bodyRun (List.prefix_refl _) conditionNodes (Nat.le_refl _)
          have conditionCapture := bodyCapture.of_prefix conditionRetained
          have initializerRetained : initialized.state.nodes <+: conditionState.nodes :=
            inferExprFuel_preserves_nodesPrefix conditionRun (List.prefix_refl _) initNodes (Nat.le_refl _)
          have initializerCapture := conditionCapture.of_prefix initializerRetained
          have initFormation := initializerIH allocatedReady allocatedNodes allocatedFormed formation
            initialized initializerRun initializerContinuation initializerCapture headerCapture.1
          have conditionFormation := conditionIH initialized initProperties.2 initNodes initFormation formation
            boolBelow boolFormed (checkedCondition,conditionState) conditionRun conditionContinuation conditionCapture
          have bodyFormation := bodyIH conditionState conditionProperties.2.1 conditionNodes conditionFormation.2 loopFormation
            (returnBelow.weaken throughCondition.next_le) returnFormed checkedBody bodyRun bodyContinuation bodyCapture
          have restoredFormation : NormalizedStateFormation semantic outer afterBody :=
            initFormation.restore bodyFormation.2 initialized.state.lexicalScope (List.Subset.refl _)
          have postFormation := postIH initialized checkedBody restoredProperties.2 afterBodyNodes restoredFormation loopFormation
            checkedPost postRun postContinuation postCapture headerCapture.2
          have finalFormation := allocatedFormed.restore postFormation allocated.lexicalScope (List.Subset.refl _)
          exact ⟨.unit formation.scope.binders, finalFormation.congr rfl rfl⟩

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
