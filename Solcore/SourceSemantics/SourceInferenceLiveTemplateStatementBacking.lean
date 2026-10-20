import Solcore.SourceSemantics.SourceInferenceLiveTemplateBacking

/-! Statement and statement-list inference preserve real predicate backing.
Only the current let adds a binder; scoped children restore the entering stack. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

private theorem unify_binders {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    after.localBinders = before.localBinders := by
  unfold Detail.unify at accepted
  cases inference : liftUnification (before.inference.unify left right) with
  | error error => simp [inference, bind, Except.bind] at accepted
  | ok solved =>
    simp only [inference, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    rfl

private theorem scrutinee_binders
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial final : State} {value : InferredExpression}
    (accepted : SourceInferenceSoundness.inferMatchScrutineesFuel fuel context span sources initial =
      .ok (value,final)) : final.localBinders = initial.localBinders := by
  cases sources with
  | nil =>
    unfold SourceInferenceSoundness.inferMatchScrutineesFuel at accepted
    cases child : inferExprsFuel fuel context [] initial with
    | error error => simp [child, bind, Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨values,state⟩
      simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact congrArg LexicalScope.binders (inferExprsFuel_success_lexicalScope_eq child)
  | cons first rest =>
    cases rest with
    | nil =>
      have child : inferExprFuel fuel context first none initial = .ok (value,final) := by
        simpa only [SourceInferenceSoundness.inferMatchScrutineesFuel] using accepted
      exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
    | cons second tail =>
      unfold SourceInferenceSoundness.inferMatchScrutineesFuel at accepted
      cases child : inferExprsFuel fuel context (first :: second :: tail) initial with
      | error error => simp [child, bind, Except.bind] at accepted
      | ok pair =>
        rcases pair with ⟨values,state⟩
        simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        exact congrArg LexicalScope.binders (inferExprsFuel_success_lexicalScope_eq child)

private theorem nonlet_binders
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    (notLet : ∀ name annotation initializer, statement.value ≠ .letDecl name annotation initializer)
    (accepted : inferStatementFuel fuel context statement expectedReturn initial = .ok result) :
    result.state.localBinders = initial.localBinders := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at accepted
  | succ fuel =>
    cases form : statement.value with
    | letDecl name annotation initializer => exact (notLet _ _ _ form).elim
    | expression source trailing =>
      obtain ⟨value, state, child, resultEq, _⟩ :=
        inferStatementFuel_success_expression_facts form rfl accepted
      rw [resultEq]
      exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
    | assignValue target operator value =>
      obtain ⟨assignment, inferred, state, child, resultEq, _⟩ :=
        inferStatementFuel_success_assignValue_facts form rfl accepted
      rw [resultEq]
      exact congrArg LexicalScope.binders (inferAssignedValueFuel_success_lexicalScope_eq child)
    | assignBitNot target operator =>
      obtain ⟨place, state, unified, child, unification, _, resultEq, _⟩ :=
        inferStatementFuel_success_assignBitNot_facts form rfl accepted
      rw [resultEq]
      exact (unify_binders unification).trans
        (congrArg LexicalScope.binders (inferPlaceFuel_success_lexicalScope_eq child))
    | returnStmt source =>
      cases source with
      | none =>
        obtain ⟨unified, unification, _, resultEq, _⟩ :=
          inferStatementFuel_success_returnUnit_facts form rfl accepted
        rw [resultEq]
        have h := unify_binders unification
        exact h
      | some source =>
        obtain ⟨value, state, child, resultEq, _⟩ :=
          inferStatementFuel_success_returnValue_facts form rfl accepted
        rw [resultEq]
        exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
    | breakStmt =>
      obtain ⟨_, resultEq, _⟩ := inferStatementFuel_success_break_facts form rfl accepted
      rw [resultEq]
      rfl
    | continueStmt =>
      obtain ⟨_, resultEq, _⟩ := inferStatementFuel_success_continue_facts form rfl accepted
      rw [resultEq]
      rfl
    | block body =>
      obtain ⟨block, _, resultEq, _⟩ := inferStatementFuel_success_block_facts form rfl accepted
      rw [resultEq]
      rfl
    | ifThen condition thenBody elseBody =>
      cases elseBody with
      | none =>
        obtain ⟨value, state, thenResult, child, _, resultEq, _⟩ :=
          inferStatementFuel_success_ifWithoutElse_facts form rfl accepted
        rw [resultEq]
        exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
      | some elseBody =>
        obtain ⟨value, state, thenResult, elseResult, child, _, _, resultEq, _⟩ :=
          inferStatementFuel_success_ifWithElse_facts form rfl accepted
        rw [resultEq]
        exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
    | whileLoop condition body =>
      obtain ⟨value, state, bodyResult, child, _, resultEq, _⟩ :=
        inferStatementFuel_success_whileLoop_facts form rfl accepted
      rw [resultEq]
      exact congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq child)
    | forLoop span initializer condition post body =>
      obtain ⟨initializerResult, value, state, bodyResult, postResult,
          _, _, _, _, resultEq, _⟩ :=
        inferStatementFuel_success_forLoop_facts form rfl accepted
      rw [resultEq]
      rfl
    | matchWith sources arms =>
      cases defaultEq : arms.value.defaultBody with
      | none =>
        obtain ⟨value, state, hidden, hiddenState, checked, child, allocated, checkedRun,
            _, resultEq, _⟩ :=
          inferStatementFuel_success_matchWithoutDefault_facts form defaultEq rfl accepted
        have hiddenEq : hiddenState = state.allocateHiddenLocal.2 := (congrArg Prod.snd allocated).symm
        rw [resultEq]
        have same := congrArg LexicalScope.binders (inferMatchCasesFuel_success_lexicalScope_eq rfl checkedRun)
        change checked.state.localBinders = hiddenState.localBinders at same
        change checked.state.localBinders = initial.localBinders
        rw [same,hiddenEq]
        have h := scrutinee_binders child
        exact h
      | some default =>
        obtain ⟨value, state, hidden, hiddenState, checked, defaultResult, child, allocated,
            _, _, _, resultEq, _⟩ :=
          inferStatementFuel_success_matchWithDefault_facts form defaultEq rfl accepted
        have hiddenEq : hiddenState = state.allocateHiddenLocal.2 := (congrArg Prod.snd allocated).symm
        rw [resultEq]
        change hiddenState.localBinders = initial.localBinders
        rw [hiddenEq]
        have h := scrutinee_binders child
        exact h
    | assembly body => simp [Detail.inferStatementFuel,form] at accepted
    | error => simp [Detail.inferStatementFuel,form] at accepted

theorem LiveTemplatesBacked.inferStatementFuel
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (accepted : inferStatementFuel fuel context source expectedReturn initial = .ok result) :
    LiveTemplatesBacked result.state := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at accepted
  | succ fuel =>
    by_cases isLet : ∃ name annotation initializer, source.value = .letDecl name annotation initializer
    · obtain ⟨name,annotation,initializer,form⟩ := isLet
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := SourceInference.LocalLetRequirementTiming.of_initialized_accepted form accepted
        exact LocalLetRequirementTiming.Receipt.templates_result receipt backed ready validated canonical
      | none =>
        cases annotation with
        | none =>
          simp [Detail.inferStatementFuel,form] at accepted
          change (Except.error (.missingInitializer name.value) : Except SourceInference.Error StatementResult) = .ok result at accepted
          cases accepted
        | some annotation =>
          unfold Detail.inferStatementFuel at accepted
          simp only [form,bind,Except.bind] at accepted
          cases resolved : resolveSourceType context annotation with
          | error error => simp [resolved] at accepted
          | ok type =>
            simp only [resolved,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
            subst result
            have allocated : LiveTemplatesBacked initial.allocateStatementId.2 :=
              backed.congr rfl rfl rfl
            exact (allocated.generalized ready.solved _ _ _ _ _ _).congr rfl rfl rfl
    · have same := nonlet_binders (by
        intro name annotation initializer form
        exact isLet ⟨name,annotation,initializer,form⟩) accepted
      have progress := inferStatementFuel_inferenceProperties ready validated canonical returnBelow accepted
      exact backed.transport (by intro _ member; exact same ▸ member)
        (inferStatementFuel_requirements_subset accepted) progress.1.substitution_extends

theorem LiveTemplatesBacked.inferStatementsFuel
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : BlockResult}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (accepted : inferStatementsFuel fuel context sources expectedReturn initial = .ok result) :
    LiveTemplatesBacked result.state := by
  induction fuel generalizing sources initial result with
  | zero => simp [Detail.inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil =>
      simp [Detail.inferStatementsFuel] at accepted
      subst result
      exact backed
    | cons head tail =>
      cases tail with
      | nil =>
        obtain ⟨statement, statementRun, resultEq⟩ := inferStatementsFuel_success_singleton_facts accepted
        rw [resultEq]
        exact backed.inferStatementFuel ready validated canonical returnBelow statementRun
      | cons next rest =>
        obtain ⟨statement, tail, statementRun, tailRun, resultEq⟩ :=
          inferStatementsFuel_success_cons_facts accepted
        have properties := inferStatementFuel_inferenceProperties ready validated canonical returnBelow statementRun
        rw [resultEq]
        change LiveTemplatesBacked tail.state
        exact ih (result := tail) (backed.inferStatementFuel ready validated canonical returnBelow statementRun)
          properties.2.1 (returnBelow.weaken properties.1.next_le) tailRun

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
