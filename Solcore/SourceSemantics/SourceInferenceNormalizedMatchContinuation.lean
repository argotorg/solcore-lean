import Solcore.SourceSemantics.SourceInferenceNormalizedPatternFormation

/-! Actual match inference retains normalized formation through patterns,
arm bodies, saved lexical scopes and the optional default continuation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness

theorem inferMatchCasesFuel_cons_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context}
    {scrutineeType expectedReturn : Ty} {outerScope : LexicalScope}
    {arm : Syntax.MatchCase} {rest : List Syntax.MatchCase} {initial : State}
    (bodyIH : ∀ state, InferStatementsFuelFormation semantic outer fuel context
      arm.value.body.value expectedReturn state)
    (tailIH : ∀ body : BlockResult, InferMatchCasesFuelFormation semantic outer fuel
      context scrutineeType expectedReturn outerScope rest
      (body.state.restoreLexicalScope outerScope)) :
    InferMatchCasesFuelFormation semantic outer (fuel + 1) context scrutineeType
      expectedReturn outerScope (arm :: rest) initial := by
  intro ready nodes formed formation scrutineeBelow scrutineeFormed returnBelow returnFormed
    scopeEq result accepted continuation noCapture
  subst outerScope
  unfold inferMatchCasesFuel at accepted
  simp only [bind, Except.bind] at accepted
  cases patternRun : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial with
  | error error => simp [patternRun] at accepted
  | ok patternPair =>
    rcases patternPair with ⟨pattern, patternState⟩
    simp only [patternRun] at accepted
    cases bodyRun : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState with
    | error error => simp [bodyRun] at accepted
    | ok body =>
      simp only [bodyRun] at accepted
      cases tailRun : inferMatchCasesFuel fuel context scrutineeType expectedReturn initial.lexicalScope
          rest (body.state.restoreLexicalScope initial.lexicalScope) with
      | error error => simp [tailRun] at accepted
      | ok tail =>
        simp only [tailRun, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        subst result
        have patternProperties := inferMatchPatternFuel_inferenceProperties ready
          scrutineeBelow formation.validated patternRun
        have patternNodes := (inferMatchPatternFuel_occurrenceBoundExtends patternRun).nodesBelowNextOccurrence nodes
        have returnAtPattern := returnBelow.weaken patternProperties.1.next_le
        have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1
          formation.validated formation.functionShapes returnAtPattern bodyRun
        have bodyNodes := (inferStatementsFuel_occurrenceBoundExtends bodyRun).nodesBelowNextOccurrence patternNodes
        have throughBody := patternProperties.1.trans bodyProperties.1
        have restoredProperties := State.restoreLexicalScope_inferenceProperties ready throughBody
        have restoredNodes := State.restoreLexicalScope_preserves_nodesBelowNextOccurrence
          body.state initial.lexicalScope bodyNodes
        have tailProperties := inferMatchCasesFuel_inferenceProperties restoredProperties.2
          formation.validated formation.functionShapes
          (scrutineeBelow.weaken restoredProperties.1.next_le)
          (returnBelow.weaken restoredProperties.1.next_le) (by simp) tailRun
        have bodyContinuation : outer.SemanticallyExtends body.state.inference.substitution :=
          continuation.trans tailProperties.1.substitution_extends
        have patternFormed := inferMatchPatternFuel_normalized_formation ready scrutineeBelow formation formed
          scrutineeFormed patternRun (bodyContinuation.trans bodyProperties.1.substitution_extends)
        have bodyNoCapture : NoCaptureNodes outer body.state.nodes :=
          noCapture.of_prefix (inferMatchCasesFuel_preserves_nodesPrefix
            (state := body.state.restoreLexicalScope initial.lexicalScope) (result := tail)
            tailRun List.prefix_rfl restoredNodes (Nat.le_refl _))
        have bodyFormed := bodyIH patternState patternProperties.2.1 patternNodes patternFormed formation
          returnAtPattern returnFormed body bodyRun bodyContinuation bodyNoCapture
        exact tailIH body restoredProperties.2 restoredNodes
          (formed.restore bodyFormed.2 initial.lexicalScope (by intro _ member; exact member)) formation
          (scrutineeBelow.weaken restoredProperties.1.next_le) scrutineeFormed
          (returnBelow.weaken restoredProperties.1.next_le) returnFormed (by simp)
          tail tailRun continuation noCapture

private def finishMatch (fuel : Nat) (context : SourceInference.Context)
    (statement : Syntax.Statement) (id : StatementId) (hidden : Resolved.LocalId)
    (scrutinee : InferredExpression) (arms : Syntax.Located Syntax.MatchArmsValue)
    (expectedReturn : Ty) (state : State) : Except Error StatementResult := do
  let outerScope := state.lexicalScope
  let checked ← inferMatchCasesFuel fuel context scrutinee.type expectedReturn outerScope arms.value.cases state
  let (defaultBody,state) ← match arms.value.defaultBody with
    | none => pure (none,checked.state)
    | some body => do
      let inferred ← inferStatementsFuel fuel context body.value expectedReturn checked.state
      pure (some (inferred.statements,inferred.sawReturn),inferred.state.restoreLexicalScope outerScope)
  let exhaustive := checked.hasWildcard || defaultBody.isSome ||
    exhaustsNominalConstructors context state scrutinee.type checked.cases
  if !exhaustive then throw (.nonExhaustiveMatch statement.span) else
    let requirements := checked.cases.flatMap fun arm => arm.pattern.requirements
    let defaultStatements := defaultBody.map (·.1)
    let defaultReturns := defaultBody.map (·.2) |>.getD true
    let sawReturn := checked.allReturn && defaultReturns
    let type := if sawReturn then state.resolve expectedReturn else .unit
    let state := state.recordNode (.statement {
      id := id
      span := statement.span
      type := type
      form := .matchWith {
        scrutinee := scrutinee.id
        hiddenScrutinee := hidden
        cases := checked.cases
        defaultBody := defaultStatements
        requirements := requirements
      }
    })
    pure {
      id := id
      type := type
      hasValue := sawReturn
      sawReturn := sawReturn
      state := state
    }


private theorem finishMatch_progress
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {id : StatementId} {hidden : Resolved.LocalId}
    {scrutinee : InferredExpression} {arms : Syntax.Located Syntax.MatchArmsValue}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (ready : state.InferenceReady) (nodes : state.NodesBelowNextOccurrence)
    (formation : InferenceFormationContext semantic context outer)
    (scrutineeBelow : scrutinee.type.VariablesBelow state.inference.next)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (success : finishMatch fuel context statement id hidden scrutinee arms expectedReturn state = .ok result) :
    state.InferenceProgress result.state ∧ state.nodes <+: result.state.nodes := by
  unfold finishMatch at success
  simp only [bind,Except.bind] at success
  cases casesRun : inferMatchCasesFuel fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state with
  | error error => simp [casesRun] at success
  | ok checked =>
    simp only [casesRun] at success
    have casesProperties := inferMatchCasesFuel_inferenceProperties ready formation.validated formation.functionShapes scrutineeBelow returnBelow rfl casesRun
    have casesNodes := (inferMatchCasesFuel_occurrenceBoundExtends casesRun).nodesBelowNextOccurrence nodes
    have casesPrefix := inferMatchCasesFuel_preserves_nodesPrefix casesRun List.prefix_rfl nodes (Nat.le_refl _)
    cases defaultEq : arms.value.defaultBody with
    | none =>
      simp only [defaultEq,pure,Pure.pure,Except.pure] at success
      split at success
      · cases success
      · injection success with resultEq
        subst result
        exact ⟨⟨casesProperties.1.next_le, casesProperties.1.solved, casesProperties.1.substitution_extends⟩, casesPrefix.trans (State.recordNode_nodesPrefix _ _)⟩
    | some body =>
      cases bodyRun : inferStatementsFuel fuel context body.value expectedReturn checked.state with
      | error error => simp [defaultEq,bodyRun] at success
      | ok checkedBody =>
        simp only [defaultEq,bodyRun,pure,Pure.pure,Except.pure] at success
        have bodyProperties := inferStatementsFuel_inferenceProperties casesProperties.2.1
          formation.validated formation.functionShapes (returnBelow.weaken casesProperties.1.next_le) bodyRun
        have bodyPrefix := inferStatementsFuel_preserves_nodesPrefix bodyRun List.prefix_rfl casesNodes (Nat.le_refl _)
        split at success
        · cases success
        · injection success with resultEq
          subst result
          have progress := casesProperties.1.trans bodyProperties.1
          exact ⟨⟨progress.next_le, progress.solved, progress.substitution_extends⟩,
            (casesPrefix.trans bodyPrefix).trans (State.recordNode_nodesPrefix _ _)⟩

private theorem finishMatch_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {id : StatementId} {hidden : Resolved.LocalId}
    {scrutinee : InferredExpression} {arms : Syntax.Located Syntax.MatchArmsValue}
    {expectedReturn : Ty} {state : State}
    (ready : state.InferenceReady) (nodes : state.NodesBelowNextOccurrence)
    (formed : NormalizedStateFormation semantic outer state)
    (formation : InferenceFormationContext semantic context outer)
    (scrutineeBelow : scrutinee.type.VariablesBelow state.inference.next)
    (scrutineeFormed : TypeAdmissible semantic (outer.apply scrutinee.type))
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (returnFormed : TypeAdmissible semantic (outer.apply expectedReturn))
    (casesIH : InferMatchCasesFuelFormation semantic outer fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelFormation semantic outer fuel context body.value expectedReturn checked.state)
    {result : StatementResult}
    (success : finishMatch fuel context statement id hidden scrutinee arms expectedReturn state = .ok result)
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (noCapture : NoCaptureNodes outer result.state.nodes) :
    TypeAdmissible semantic (outer.apply result.type) ∧ NormalizedStateFormation semantic outer result.state := by
  unfold finishMatch at success
  simp only [bind,Except.bind] at success
  cases casesRun : inferMatchCasesFuel fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state with
  | error error => simp [casesRun] at success
  | ok checked =>
    simp only [casesRun] at success
    have casesProperties := inferMatchCasesFuel_inferenceProperties ready formation.validated formation.functionShapes scrutineeBelow returnBelow rfl casesRun
    have casesNodes := (inferMatchCasesFuel_occurrenceBoundExtends casesRun).nodesBelowNextOccurrence nodes
    cases defaultEq : arms.value.defaultBody with
    | none =>
      simp only [defaultEq,pure,Pure.pure,Except.pure] at success
      split at success
      · cases success
      · injection success with resultEq
        subst result
        have casesFormed := casesIH ready nodes formed formation scrutineeBelow scrutineeFormed
          returnBelow returnFormed rfl checked casesRun continuation
          (noCapture.of_prefix (State.recordNode_nodesPrefix _ _))
        refine ⟨?_, casesFormed.congr rfl rfl⟩
        split
        · exact (continuation expectedReturn).symm ▸ returnFormed
        · exact .unit formation.scope.binders
    | some body =>
      cases bodyRun : inferStatementsFuel fuel context body.value expectedReturn checked.state with
      | error error => simp [defaultEq,bodyRun] at success
      | ok checkedBody =>
        simp only [defaultEq,bodyRun,pure,Pure.pure,Except.pure] at success
        have bodyProperties := inferStatementsFuel_inferenceProperties casesProperties.2.1
          formation.validated formation.functionShapes (returnBelow.weaken casesProperties.1.next_le) bodyRun
        have bodyPrefix := inferStatementsFuel_preserves_nodesPrefix bodyRun List.prefix_rfl casesNodes (Nat.le_refl _)
        split at success
        · cases success
        · injection success with resultEq
          subst result
          have bodyNoCapture : NoCaptureNodes outer checkedBody.state.nodes :=
            noCapture.of_prefix (State.recordNode_nodesPrefix _ _)
          have casesFormed := casesIH ready nodes formed formation scrutineeBelow scrutineeFormed
            returnBelow returnFormed rfl checked casesRun
            (continuation.trans bodyProperties.1.substitution_extends) (bodyNoCapture.of_prefix bodyPrefix)
          have bodyFormed := bodyIH checked body casesProperties.2.1 casesNodes casesFormed formation
            (returnBelow.weaken casesProperties.1.next_le) returnFormed checkedBody bodyRun continuation bodyNoCapture
          have restored := formed.restore bodyFormed.2 state.lexicalScope (by intro _ member; exact member)
          refine ⟨?_, restored.congr rfl rfl⟩
          split
          · exact (continuation expectedReturn).symm ▸ returnFormed
          · exact .unit formation.scope.binders

theorem inferStatementFuel_match_single_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.Located Syntax.MatchArmsValue} {source : Syntax.Expr} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .matchWith scrutinees arms)
    (single : scrutinees.elements.toList = [source])
    (casesIH : ∀ (scrutinee : InferredExpression) (state : State),
      InferMatchCasesFuelFormation semantic outer fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelFormation semantic outer fuel context body.value expectedReturn checked.state)
    (sourceIH : InferExprFuelFormation semantic outer fuel context source none initial.allocateStatementId.2) :
    InferStatementFuelFormation semantic outer (fuel+1) context statement expectedReturn initial := by
  intro ready nodes formed formation returnBelow returnFormed result success continuation noCapture
  let allocated := initial.allocateStatementId.2
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedNodes := (State.OccurrenceBoundExtends.allocateStatementId initial).nodesBelowNextOccurrence nodes
  unfold inferStatementFuel at success
  simp only [form,single,bind,Except.bind] at success
  cases sourceRun : inferExprFuel fuel context source none allocated with
  | error error => simp [allocated,sourceRun] at success
  | ok pair =>
    rcases pair with ⟨scrutinee,sourceState⟩
    simp only [allocated,sourceRun] at success
    have sourceProperties := inferExprFuel_inferenceProperties allocatedReady formation.validated formation.functionShapes (by simp) sourceRun
    have sourceNodes := (inferExprFuel_occurrenceBoundExtends sourceRun).nodesBelowNextOccurrence allocatedNodes
    let hiddenState := sourceState.allocateHiddenLocal.2
    have hiddenReady : hiddenState.InferenceReady := State.InferenceReady.allocateHiddenLocal sourceProperties.2.1
    have hiddenNodes := (State.OccurrenceBoundExtends.allocateHiddenLocal sourceState).nodesBelowNextOccurrence sourceNodes
    have finishRun : finishMatch fuel context statement initial.allocateStatementId.1 sourceState.allocateHiddenLocal.1
        scrutinee arms expectedReturn hiddenState = .ok result := success
    have finished := finishMatch_progress hiddenReady hiddenNodes formation sourceProperties.2.2
      (returnBelow.weaken sourceProperties.1.next_le) finishRun
    have sourceFormed := sourceIH allocatedReady allocatedNodes (formed.congr rfl rfl) formation
      (by simp) (by simp) (scrutinee,sourceState) sourceRun
      (continuation.trans finished.1.substitution_extends) (noCapture.of_prefix finished.2)
    exact finishMatch_formation hiddenReady hiddenNodes (sourceFormed.2.congr rfl rfl) formation
      sourceProperties.2.2 sourceFormed.1 (returnBelow.weaken sourceProperties.1.next_le) returnFormed
      (casesIH scrutinee hiddenState) bodyIH finishRun continuation noCapture

theorem inferStatementFuel_match_many_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.Located Syntax.MatchArmsValue} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .matchWith scrutinees arms)
    (notSingleton : ∀ source, scrutinees.elements.toList = [source] → False)
    (casesIH : ∀ (scrutinee : InferredExpression) (state : State),
      InferMatchCasesFuelFormation semantic outer fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelFormation semantic outer fuel context body.value expectedReturn checked.state)
    (sourcesIH : InferExprsFuelFormation semantic outer fuel context scrutinees.elements.toList initial.allocateStatementId.2) :
    InferStatementFuelFormation semantic outer (fuel+1) context statement expectedReturn initial := by
  intro ready nodes formed formation returnBelow returnFormed result success continuation noCapture
  let allocated := initial.allocateStatementId.2
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedNodes := (State.OccurrenceBoundExtends.allocateStatementId initial).nodesBelowNextOccurrence nodes
  unfold inferStatementFuel at success
  simp only [form] at success
  simp only [bind,Except.bind] at success
  cases sourcesRun : inferExprsFuel fuel context scrutinees.elements.toList initial.allocateStatementId.2 with
  | error error => simp [sourcesRun] at success
  | ok pair =>
    rcases pair with ⟨elements,elementState⟩
    simp only [sourcesRun,pure,Pure.pure,Except.pure] at success
    have properties := inferExprsFuel_inferenceProperties allocatedReady formation.validated formation.functionShapes sourcesRun
    have elementNodes := (inferExprsFuel_occurrenceBoundExtends sourcesRun).nodesBelowNextOccurrence allocatedNodes
    let tuple : InferredExpression := {id := elementState.allocateExpressionId.1,type := Ty.productMany (elements.map (·.type))}
    let tupleNode : Node := .expression {
      id := tuple.id
      span := statement.span
      type := tuple.type
      form := .tuple (elements.map (·.id)) }
    let tupleState := elementState.allocateExpressionId.2.recordNode tupleNode
    have tupleReady : tupleState.InferenceReady := State.InferenceReady.recordNode _
      (State.InferenceReady.allocateExpressionId properties.2.1)
    have tupleNodes : tupleState.NodesBelowNextOccurrence :=
      (State.OccurrenceBoundExtends.recordNode _ tupleNode
        (State.allocateExpressionId_index_lt_nextOccurrence elementState)).nodesBelowNextOccurrence
          ((State.OccurrenceBoundExtends.allocateExpressionId elementState).nodesBelowNextOccurrence elementNodes)
    have tupleBelow : tuple.type.VariablesBelow tupleState.inference.next := by
      apply Ty.variablesBelow_productMany
      intro type member
      obtain ⟨element,elementMember,rfl⟩ := List.mem_map.mp member
      exact properties.2.2 element elementMember
    let hiddenState := tupleState.allocateHiddenLocal.2
    have hiddenReady : hiddenState.InferenceReady := State.InferenceReady.allocateHiddenLocal tupleReady
    have hiddenNodes := (State.OccurrenceBoundExtends.allocateHiddenLocal tupleState).nodesBelowNextOccurrence tupleNodes
    have finishRun : finishMatch fuel context statement initial.allocateStatementId.1 tupleState.allocateHiddenLocal.1
        tuple arms expectedReturn hiddenState = .ok result := success
    have finished := finishMatch_progress hiddenReady hiddenNodes formation tupleBelow
      (returnBelow.weaken properties.1.next_le) finishRun
    have elementNoCapture : NoCaptureNodes outer elementState.nodes :=
      noCapture.of_prefix ((State.recordNode_nodesPrefix elementState.allocateExpressionId.2 tupleNode).trans finished.2)
    have elementsFormed := sourcesIH allocatedReady allocatedNodes (formed.congr rfl rfl) formation
      (elements,elementState) sourcesRun (continuation.trans finished.1.substitution_extends) elementNoCapture
    have tupleFormed : TypeAdmissible semantic (outer.apply tuple.type) := by
      change TypeAdmissible semantic (outer.apply (Ty.productMany (elements.map (·.type))))
      rw [Substitution.apply_productMany]
      apply TypeAdmissible.productMany formation.scope.binders
      intro type member
      obtain ⟨raw,rawMember,rfl⟩ := List.mem_map.mp member
      obtain ⟨element,elementMember,rfl⟩ := List.mem_map.mp rawMember
      exact elementsFormed.1 element elementMember
    exact finishMatch_formation hiddenReady hiddenNodes (elementsFormed.2.congr rfl rfl) formation
      tupleBelow tupleFormed (returnBelow.weaken properties.1.next_le) returnFormed
      (casesIH tuple hiddenState) bodyIH finishRun continuation noCapture

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
