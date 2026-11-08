import Solcore.SourceSemantics.Internal.Formation.NormalizedDeclarations
import Solcore.Frontend.SourceInference.Internal.OccurrenceProperties

/-!
# Normalized lambdas and loops

Formation through a lambda body, its saved scope, and `for` statements. A private `unify_fields`
differs from the one of its neighbours, so this file stays apart.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedLambdaContinuation
/-! The real lambda body and its saved lexical scope supply normalized
formation through return unification, restoration and result recording. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceRequirementFormation SourceInferenceSoundness

/-- Loop depth does not change the actual declaration and type-formation scope. -/
theorem InferenceFormationContext.withLoopDepth
    {semantic : SourceSemantics.Context} {outer : Substitution} {context : SourceInference.Context}
    (formation : InferenceFormationContext semantic context outer) (depth : Nat) :
    InferenceFormationContext semantic {context with loopDepth := depth} outer := {
  signatures := formation.signatures
  catalog := formation.catalog
  residual := formation.residual
  assumptions := formation.assumptions
  range := formation.range
  scope := ⟨formation.scope.binders,formation.scope.signatures,formation.scope.parameters,
    formation.scope.owner,formation.scope.residual,formation.scope.catalog⟩
  canonical := formation.canonical
  validated := formation.validated
  functionShapes := formation.functionShapes
}

private theorem unify_fields {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    after.localBinders = before.localBinders ∧ after.requirements = before.requirements := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified,Detail.liftUnification,bind,Except.bind] at accepted
  | ok inference =>
    simp only [unified,Detail.liftUnification,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
    cases accepted
    exact ⟨rfl,rfl⟩

private theorem functionParts_eq {type parameter result : Ty}
    (found : functionParts? type = some (parameter,result)) : type = .function parameter result := by
  cases type <;> simp [functionParts?] at found
  rcases found with ⟨rfl,rfl⟩
  rfl

private theorem expected_parts_below
    {state : State} {expected : Option Ty} {parameter result : Ty}
    (ready : state.InferenceReady)
    (below : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (parts : expected.bind (fun type => functionParts? (state.resolve type)) = some (parameter,result)) :
    parameter.VariablesBelow state.inference.next ∧ result.VariablesBelow state.inference.next := by
  obtain ⟨type,member,found⟩ := Option.bind_eq_some_iff.mp parts
  exact functionParts?_success_variablesBelow (ready.solved.variablesBelow_apply (below type (by simp [member]))) found

private theorem expected_result_formed
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {state : State} {expected : Option Ty} {parameter result : Ty}
    (formed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends state.inference.substitution)
    (parts : expected.bind (fun type => functionParts? (state.resolve type)) = some (parameter,result)) :
    TypeAdmissible semantic (outer.apply result) := by
  obtain ⟨type,member,found⟩ := Option.bind_eq_some_iff.mp parts
  have resolved : TypeAdmissible semantic (outer.apply (state.resolve type)) :=
    (continuation type).symm ▸ formed type (by simp [member])
  rw [functionParts_eq found] at resolved
  exact resolved.function_result

private structure LambdaFormationPrefix (semantic : SourceSemantics.Context) (outer : Substitution)
    (before after : State) (resultType : Ty) : Prop where
  progress : before.InferenceProgress after
  ready : after.InferenceReady
  below : resultType.VariablesBelow after.inference.next
  occurrences : before.OccurrenceBoundExtends after
  formed : outer.SemanticallyExtends after.inference.substitution →
    NormalizedStateFormation semantic outer after ∧ TypeAdmissible semantic (outer.apply resultType)

private theorem prefix_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {parameters : List Ty} {state resultState : State} {resultType : Ty}
    (ready : state.InferenceReady)
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (parameterBelow : (Ty.productMany parameters).VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (facts : LambdaPrefixFacts context expected annotation parameters state resultType resultState) :
    LambdaFormationPrefix semantic outer state resultState resultType := by
  cases facts with
  | noExpectedPartsAnnotated parts annotation resolved =>
    exact ⟨.refl ready.solved,ready,resolveSourceType_success_variablesBelow resolved _,
      ⟨Nat.le_refl _,fun nodes => nodes⟩,fun _ => ⟨formed,resolved_annotation_normalized_formation formation resolved⟩⟩
  | noExpectedPartsFresh parts annotation allocated =>
    have typeEq : resultType = state.fresh.1 := (congrArg Prod.fst allocated).symm
    have stateEq : resultState = state.fresh.2 := (congrArg Prod.snd allocated).symm
    subst resultType resultState
    refine ⟨.fresh _ ready.solved,ready.fresh,
      (Ty.variablesBelow_variable_iff _ _).mpr (Nat.lt_succ_self _),
      ⟨Nat.le_refl _,fun nodes => nodes⟩,?_⟩
    intro _
    exact ⟨formed.congr rfl rfl,type_applySubstitution_residual formation.residual formation.range
      (.variableOfResidual formation.scope.binders formation.residual _)⟩
  | expectedPartsAnnotated parts unified annotation resolved =>
    have bounds := expected_parts_below ready expectedBelow parts
    have progress := unify_inferenceProgress ready.solved parameterBelow bounds.1 unified
    have fields := unify_fields unified
    exact ⟨progress,unify_preserves_inferenceReady ready parameterBelow bounds.1 unified,
      resolveSourceType_success_variablesBelow resolved _,unify_occurrenceBoundExtends unified,
      fun _ => ⟨formed.congr fields.1 fields.2,resolved_annotation_normalized_formation formation resolved⟩⟩
  | expectedPartsInferred parts unified annotation =>
    have bounds := expected_parts_below ready expectedBelow parts
    have progress := unify_inferenceProgress ready.solved parameterBelow bounds.1 unified
    have fields := unify_fields unified
    exact ⟨progress,unify_preserves_inferenceReady ready parameterBelow bounds.1 unified,
      bounds.2.weaken progress.next_le,unify_occurrenceBoundExtends unified,
      fun continuation => ⟨formed.congr fields.1 fields.2,
        expected_result_formed expectedFormed (continuation.trans progress.substitution_extends) parts⟩⟩

/-- The only recursive premise is the actual smaller lambda body. Terminal
capture checks are pulled through the real return unification and recording. -/
theorem inferExprFuel_lambda_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat}
    {context : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty} {initial : State}
    {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {returnType : Option Syntax.TypeExpr} {body : Syntax.Block}
    (form : expression.value = .lambda keyword parameters returnType body)
    (bodyIH : ∀ resultType state, InferStatementsFuelFormation semantic outer fuel
      {context with loopDepth := 0} body.value resultType state) :
    InferExprFuelFormation semantic outer (fuel+1) context expression expected initial := by
  intro ready nodes formed formation expectedBelow expectedFormed result accepted continuation capture
  obtain ⟨boundParameters,parameterTypes,parameterState,resultType,resultState,
    bodyResult,unifiedState,restoredState,parametersRun,prefixFacts,bodyRun,
    unified,restoredEq,recorded⟩ :=
    inferExprFuel_success_lambda_facts form (Prod.eta initial.allocateExpressionId).symm accepted
  let allocated := initial.allocateExpressionId.2
  have allocationProgress : initial.InferenceProgress allocated := .allocateExpressionId _ ready.solved
  have allocatedReady : allocated.InferenceReady := ready.allocateExpressionId
  have allocatedNodes : allocated.NodesBelowNextOccurrence := State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial nodes
  have allocatedFormed : NormalizedStateFormation semantic outer allocated := formed.congr rfl rfl
  have parameterProperties := bindLambdaParameters_inferenceProperties allocatedReady parametersRun
  have parameterFormation := bindLambdaParameters_normalized_formation formation allocatedFormed parametersRun
  have parameterNodes := (bindLambdaParameters_occurrenceBoundExtends parametersRun).nodesBelowNextOccurrence allocatedNodes
  have parameterProgress := allocationProgress.trans parameterProperties.1
  have parameterBelow := Ty.variablesBelow_productMany parameterProperties.2.2
  have entered := prefix_formation parameterProperties.2.1 formation parameterFormation.2 parameterBelow
    (fun type member => (expectedBelow type member).weaken parameterProgress.next_le) expectedFormed prefixFacts
  have resultNodes := entered.occurrences.nodesBelowNextOccurrence parameterNodes
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := {context with loopDepth := 0}) entered.ready formation.validated formation.functionShapes entered.below bodyRun
  have unifiedProgress := unify_inferenceProgress bodyProperties.2.1.solved bodyProperties.2.2
    (entered.below.weaken bodyProperties.1.next_le) unified
  have unifiedReady := unify_preserves_inferenceReady bodyProperties.2.1 bodyProperties.2.2
    (entered.below.weaken bodyProperties.1.next_le) unified
  have parametersToUnified := entered.progress.trans (bodyProperties.1.trans unifiedProgress)
  have allocatedToUnified := parameterProperties.1.trans parametersToUnified
  have restoredProperties := State.restoreLexicalScope_inferenceProperties allocatedReady allocatedToUnified
  subst restoredState
  let restored := unifiedState.restoreLexicalScope allocated.lexicalScope
  have restoreProgress : unifiedState.InferenceProgress restored :=
    .restoreLexicalScope _ _ unifiedReady.solved
  have resultToRestored := bodyProperties.1.trans (unifiedProgress.trans restoreProgress)
  have parametersToRestored := parametersToUnified.trans restoreProgress
  have initialToRestored := allocationProgress.trans restoredProperties.1
  have recordProperties := recordExpressionWithExpected_inferenceProperties restoredProperties.2
    ((Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨parametersToRestored.resolve_variablesBelow parameterBelow,
        resultToRestored.resolve_variablesBelow entered.below⟩)
    (fun type member => (expectedBelow type member).weaken initialToRestored.next_le) recorded
  have restoredContinuation := continuation.trans recordProperties.1.substitution_extends
  have bodyContinuation := restoredContinuation.trans (unifiedProgress.trans restoreProgress).substitution_extends
  have prefixContinuation := bodyContinuation.trans bodyProperties.1.substitution_extends
  have resultFormation := entered.formed prefixContinuation
  have bodyCapture : NoCaptureNodes outer bodyResult.state.nodes := by
    obtain ⟨fitted,fit,_,recordedNodes⟩ := recordExpressionWithExpected_success_nodes recorded
    rw [recordedNodes,(withExpected_occurrenceState_eq fit).1] at capture
    have previous : NoCaptureNodes outer restored.nodes := capture.of_prefix (List.prefix_append _ _)
    change NoCaptureNodes outer unifiedState.nodes at previous
    rw [(unify_occurrenceState_eq unified).1] at previous
    exact previous
  have bodyFormation := bodyIH resultType resultState entered.ready resultNodes resultFormation.1
    (formation.withLoopDepth 0) entered.below resultFormation.2 bodyResult bodyRun bodyContinuation bodyCapture
  have unifiedFields := unify_fields unified
  have unifiedFormation := bodyFormation.2.congr unifiedFields.1 unifiedFields.2
  have restoredFormation : NormalizedStateFormation semantic outer restored :=
    allocatedFormed.restore unifiedFormation allocated.lexicalScope (List.Subset.refl _)
  have productFormed : TypeAdmissible semantic (outer.apply (Ty.productMany parameterTypes)) := by
    rw [FlexibleSubstitution.apply_productMany]
    apply TypeAdmissible.productMany formation.scope.binders
    intro type member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact parameterFormation.1 original originalMember
  have functionFormed : TypeAdmissible semantic (outer.apply
      (.function (restored.resolve (Ty.productMany parameterTypes)) (restored.resolve resultType))) := by
    change TypeAdmissible semantic (.function (outer.apply (restored.resolve (Ty.productMany parameterTypes)))
      (outer.apply (restored.resolve resultType)))
    exact .function ((restoredContinuation _).symm ▸ productFormed)
      ((restoredContinuation _).symm ▸ resultFormation.2)
  have produced := recordExpressionWithExpected_normalized_formation formation.toFormationContext continuation
    functionFormed expectedFormed recorded
  exact ⟨produced.1,restoredFormation.of_new_rows
    (congrArg LexicalScope.binders (localReadScope_recordExpressionWithExpected_lexicalScope recorded)) produced.2⟩

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedForContinuation
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
end
