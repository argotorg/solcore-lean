import Solcore.SourceSemantics.SourceInferenceActualCallGraph

/-! The actual match suffix, after scrutinee and hidden-identity allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

def matchCompletion (fuel : Nat) (context : SourceInference.Context)
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


theorem matchCompletion_accepted
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
    {result : StatementResult}
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result) :
    matchCompletion fuel context source id hidden scrutinee arms expectedReturn hiddenState = .ok result := by
  unfold inferStatementFuel at accepted
  simp only [allocation, form] at accepted
  unfold matchScrutinee at scrutineeAccepted
  split at scrutineeAccepted
  all_goals simp_all [matchCompletion, bind, Except.bind, pure, Pure.pure, Except.pure]
  all_goals try exact accepted
  cases sourcesRun : inferExprsFuel fuel context scrutinees.elements.toList allocated with
  | error error => simp [sourcesRun] at scrutineeAccepted
  | ok pair =>
      simp only [sourcesRun] at scrutineeAccepted accepted
      simp only [Except.ok.injEq, Prod.mk.injEq] at scrutineeAccepted
      rcases scrutineeAccepted with ⟨valueEq, stateEq⟩
      cases valueEq
      cases stateEq
      simp_all
      exact accepted

end Solcore.SourceSemantics.SourceInferenceExecution
