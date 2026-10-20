import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyContracts

/-! Real match statement inference preserves scheme privacy through ordered
scrutinees, all arms, optional default inference and actual scope restoration. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

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


private theorem finishMatch_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {id : StatementId} {hidden : Resolved.LocalId}
    {scrutinee : InferredExpression} {arms : Syntax.Located Syntax.MatchArmsValue}
    {expectedReturn : Ty} {state : State}
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (bound : ∀ v ∈ protectedVars, v.index < state.inference.next)
    (live : LiveBindersSafe protectedVars state)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (scrutineeBelow : scrutinee.type.VariablesBelow state.inference.next)
    (scrutineeSafe : Safe protectedVars state scrutinee.type)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (returnSafe : Safe protectedVars state expectedReturn)
    (casesIH : InferMatchCasesFuelPrivacy protectedVars fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelPrivacy protectedVars fuel context body.value expectedReturn checked.state)
    {result : StatementResult}
    (success : finishMatch fuel context statement id hidden scrutinee arms expectedReturn state = .ok result) :
    SafeTransport protectedVars state result.state ∧ Safe protectedVars result.state result.type ∧
      LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements → PredicateSafe protectedVars result.state row.predicate := by
  unfold finishMatch at success
  simp only [bind,Except.bind] at success
  cases casesRun : inferMatchCasesFuel fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state with
  | error error => simp [casesRun] at success
  | ok checked =>
    simp only [casesRun] at success
    have casesProperties := inferMatchCasesFuel_inferenceProperties ready validated canonical scrutineeBelow returnBelow rfl casesRun
    have casesPrivacy := casesIH ready wellFormed bound live catalog validated canonical
      scrutineeBelow scrutineeSafe returnBelow returnSafe rfl checked casesRun
    cases defaultEq : arms.value.defaultBody with
    | none =>
      simp only [defaultEq,pure,Pure.pure,Except.pure] at success
      split at success
      · cases success
      · injection success with resultEq
        subst result
        refine ⟨casesPrivacy.1, ?_, casesPrivacy.2.1.transport rfl (.of_substitution_eq rfl), casesPrivacy.2.2⟩
        split
        · exact safe_resolved (state := checked.state) casesProperties.2.1 (casesPrivacy.1 _ returnSafe)
        · exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)
    | some body =>
      cases bodyRun : inferStatementsFuel fuel context body.value expectedReturn checked.state with
      | error error => simp [defaultEq,bodyRun] at success
      | ok checkedBody =>
        simp only [defaultEq,bodyRun,pure,Pure.pure,Except.pure] at success
        have bodyProperties := inferStatementsFuel_inferenceProperties casesProperties.2.1 validated canonical
          (returnBelow.weaken casesProperties.1.next_le) bodyRun
        have bodyPrivacy := bodyIH checked body casesProperties.2.1
          ((inferMatchCasesFuel_direct_progress casesRun).wellFormed wellFormed)
          (fun v member => Nat.lt_of_lt_of_le (bound v member) casesProperties.1.next_le)
          casesPrivacy.2.1 catalog validated canonical (returnBelow.weaken casesProperties.1.next_le)
          (casesPrivacy.1 _ returnSafe) checkedBody bodyRun
        have through := casesPrivacy.1.trans bodyPrivacy.1
        have restoredReady := (State.restoreLexicalScope_inferenceProperties ready
          (casesProperties.1.trans bodyProperties.1)).2
        have restoredLive := live.restore through
        have rows := new_requirements_trans casesPrivacy.2.2 bodyPrivacy.2.2.2 bodyPrivacy.1
        split at success
        · cases success
        · injection success with resultEq
          subst result
          refine ⟨through, ?_, restoredLive.transport rfl (.of_substitution_eq rfl), rows⟩
          split
          · exact safe_resolved (state := checkedBody.state.restoreLexicalScope state.lexicalScope) restoredReady (through _ returnSafe)
          · exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)

theorem inferStatementFuel_match_single_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.Located Syntax.MatchArmsValue} {source : Syntax.Expr} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .matchWith scrutinees arms)
    (single : scrutinees.elements.toList = [source])
    (casesIH : ∀ (scrutinee : InferredExpression) (state : State),
      InferMatchCasesFuelPrivacy protectedVars fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelPrivacy protectedVars fuel context body.value expectedReturn checked.state)
    (sourceIH : InferExprFuelPrivacy protectedVars fuel context source none initial.allocateStatementId.2) :
    InferStatementFuelPrivacy protectedVars (fuel+1) context statement expectedReturn initial := by
  intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
  let allocated := initial.allocateStatementId.2
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  unfold inferStatementFuel at success
  simp only [form,single,bind,Except.bind] at success
  cases sourceRun : inferExprFuel fuel context source none allocated with
  | error error => simp [allocated,sourceRun] at success
  | ok pair =>
    rcases pair with ⟨scrutinee,sourceState⟩
    simp only [allocated,sourceRun] at success
    have sourceProperties := inferExprFuel_inferenceProperties allocatedReady validated canonical (by simp) sourceRun
    have sourcePrivacy := sourceIH allocatedReady wellFormed bound (live.transport rfl allocatedPrivacy)
      catalog validated canonical (by simp) (by simp) (scrutinee,sourceState) sourceRun
    let hiddenState := sourceState.allocateHiddenLocal.2
    have hiddenReady : hiddenState.InferenceReady := State.InferenceReady.allocateHiddenLocal sourceProperties.2.1
    have hiddenPrivacy : SafeTransport protectedVars sourceState hiddenState := .of_substitution_eq rfl
    have finishRun : finishMatch fuel context statement initial.allocateStatementId.1 sourceState.allocateHiddenLocal.1
        scrutinee arms expectedReturn hiddenState = .ok result := success
    have finished := finishMatch_private hiddenReady
      ((inferExprFuel_direct_progress sourceRun).wellFormed wellFormed)
      (fun v member => Nat.lt_of_lt_of_le (bound v member) sourceProperties.1.next_le)
      (sourcePrivacy.2.2.1.transport rfl hiddenPrivacy) catalog validated canonical sourceProperties.2.2
      (hiddenPrivacy _ sourcePrivacy.2.1) (returnBelow.weaken sourceProperties.1.next_le)
      (sourcePrivacy.1 _ returnSafe) (casesIH scrutinee hiddenState) bodyIH finishRun
    exact ⟨allocatedPrivacy.trans (sourcePrivacy.1.trans (hiddenPrivacy.trans finished.1)),finished.2.1,finished.2.2.1,
      new_requirements_trans sourcePrivacy.2.2.2 finished.2.2.2 finished.1⟩


theorem inferStatementFuel_match_many_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.Located Syntax.MatchArmsValue} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .matchWith scrutinees arms)
    (notSingleton : ∀ source, scrutinees.elements.toList = [source] → False)
    (casesIH : ∀ (scrutinee : InferredExpression) (state : State),
      InferMatchCasesFuelPrivacy protectedVars fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelPrivacy protectedVars fuel context body.value expectedReturn checked.state)
    (sourcesIH : InferExprsFuelPrivacy protectedVars fuel context scrutinees.elements.toList initial.allocateStatementId.2) :
    InferStatementFuelPrivacy protectedVars (fuel+1) context statement expectedReturn initial := by
  intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
  let allocated := initial.allocateStatementId.2
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  unfold inferStatementFuel at success
  simp only [form] at success
  simp only [bind,Except.bind] at success
  cases sourcesRun : inferExprsFuel fuel context scrutinees.elements.toList initial.allocateStatementId.2 with
  | error error => simp [sourcesRun] at success
  | ok pair =>
    rcases pair with ⟨elements,elementState⟩
    simp only [sourcesRun,pure,Pure.pure,Except.pure] at success
    have properties := inferExprsFuel_inferenceProperties allocatedReady validated canonical sourcesRun
    have privacy := sourcesIH allocatedReady wellFormed bound (live.transport rfl allocatedPrivacy)
      catalog validated canonical (elements,elementState) sourcesRun
    let tuple : InferredExpression := {id := elementState.allocateExpressionId.1,type := Ty.productMany (elements.map (·.type))}
    let tupleState := elementState.allocateExpressionId.2.recordNode (.expression {
      id := tuple.id
      span := statement.span
      type := tuple.type
      form := .tuple (elements.map (·.id)) })
    have tupleReady : tupleState.InferenceReady := State.InferenceReady.recordNode _
      (State.InferenceReady.allocateExpressionId properties.2.1)
    have tuplePrivacy : SafeTransport protectedVars elementState tupleState := .of_substitution_eq rfl
    have tupleBelow : tuple.type.VariablesBelow tupleState.inference.next := by
      apply Ty.variablesBelow_productMany
      intro type member
      obtain ⟨element,elementMember,rfl⟩ := List.mem_map.mp member
      exact properties.2.2 element elementMember
    have tupleSafe : Safe protectedVars tupleState tuple.type := by
      apply safe_productMany
      intro type member
      obtain ⟨element,elementMember,rfl⟩ := List.mem_map.mp member
      exact tuplePrivacy _ (privacy.2.1 element elementMember)
    let hiddenState := tupleState.allocateHiddenLocal.2
    have hiddenReady : hiddenState.InferenceReady := State.InferenceReady.allocateHiddenLocal tupleReady
    have hiddenPrivacy : SafeTransport protectedVars tupleState hiddenState := .of_substitution_eq rfl
    have finishRun : finishMatch fuel context statement initial.allocateStatementId.1 tupleState.allocateHiddenLocal.1
        tuple arms expectedReturn hiddenState = .ok result := success
    have finished := finishMatch_private hiddenReady
      ((inferExprsFuel_direct_progress sourcesRun).wellFormed wellFormed)
      (fun v member => Nat.lt_of_lt_of_le (bound v member) properties.1.next_le)
      ((privacy.2.2.1.transport rfl tuplePrivacy).transport rfl hiddenPrivacy) catalog validated canonical tupleBelow
      (hiddenPrivacy _ tupleSafe) (returnBelow.weaken properties.1.next_le)
      (privacy.1 _ returnSafe) (casesIH tuple hiddenState) bodyIH finishRun
    exact ⟨allocatedPrivacy.trans (privacy.1.trans (tuplePrivacy.trans (hiddenPrivacy.trans finished.1))),finished.2.1,finished.2.2.1,
      new_requirements_trans privacy.2.2.2 finished.2.2.2 finished.1⟩

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
