import Solcore.SourceSemantics.SourceInferenceLiveTemplateStatementBacking

/-! Exact origins and allocation bounds of active scheme quantifiers after actual statement inference. -/
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

/-- Every binder surviving a statement is entering, monomorphic, or this
statement's actual initialized-let allocation. Nested child locals are restored. -/
theorem inferStatementFuel_quantified_origin
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    (accepted : Detail.inferStatementFuel fuel context source expectedReturn initial = .ok result) :
    ∀ binder ∈ result.state.localBinders,
      binder ∈ initial.localBinders ∨ binder.scheme.quantified = [] ∨
        ∃ childFuel, ∃ receipt : SourceInference.LocalLetRequirementTiming.Receipt childFuel context source initial result,
          binder = receipt.binding.1 := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at accepted
  | succ fuel =>
    by_cases isLet : ∃ name annotation initializer, source.value = .letDecl name annotation initializer
    · obtain ⟨name,annotation,initializer,form⟩ := isLet
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := SourceInference.LocalLetRequirementTiming.of_initialized_accepted form accepted
        intro binder member
        rw [receipt.result_binders] at member
        rcases List.mem_cons.mp member with current | entering
        · exact .inr (.inr ⟨fuel,receipt,current⟩)
        · exact .inl entering
      | none =>
        cases annotation with
        | none =>
          simp [Detail.inferStatementFuel,form] at accepted
          change (Except.error (.missingInitializer name.value) : Except SourceInference.Error StatementResult) = .ok result at accepted
          cases accepted
        | some annotation =>
          obtain ⟨type, locals, valueType, generalized, ⟨allocated,state⟩, resolved, _, typeEq,
              generalizedEq, allocation, resultEq, _⟩ :=
            inferStatementFuel_success_letAnnotatedUninitialized_facts form rfl accepted
          have closed : type.freeVariables = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro q member
            exact (Nat.not_lt_zero _) (resolveSourceType_success_variablesBelow resolved 0 q member)
          have resolveEq : initial.allocateStatementId.2.resolve type = type :=
            resolveSourceType_success_apply_eq_self initial.inference.substitution resolved
          have monomorphic : generalized.scheme.quantified = [] := by
            rw [generalizedEq, generalizeValue_scheme_quantified, typeEq]
            change List.filter _ (initial.allocateStatementId.2.resolve type).freeVariables = []
            rw [resolveEq,closed]
            rfl
          have binders := congrArg (fun p : TypedBinder × State => p.2.localBinders) allocation
          change ((initial.allocateStatementId.2.withLocals locals).allocateBinder name.value
            generalized.scheme (some name.span) false generalized.requirements).1 :: initial.localBinders =
              state.localBinders at binders
          intro binder member
          rw [resultEq] at member
          change binder ∈ state.localBinders at member
          rw [← binders] at member
          rcases List.mem_cons.mp member with current | entering
          · right; left
            rw [current]
            exact monomorphic
          · exact .inl entering
    · have same := nonlet_binders (by
        intro name annotation initializer form
        exact isLet ⟨name,annotation,initializer,form⟩) accepted
      intro binder member
      exact .inl (same ▸ member)

/-- The actual new scheme is bounded by its initializer result; all entering
quantifiers remain below the monotonically advancing inference allocator. -/
theorem activeQuantifiersBelowNext_inferStatementFuel
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    (bound : ActiveQuantifiersBelowNext initial) (ready : initial.InferenceReady)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (accepted : Detail.inferStatementFuel fuel context source expectedReturn initial = .ok result) :
    ActiveQuantifiersBelowNext result.state := by
  have progress := inferStatementFuel_inferenceProperties ready validated canonical returnBelow accepted
  intro binder member q quantified
  rcases inferStatementFuel_quantified_origin accepted binder member with entering | mono | initialized
  · exact Nat.lt_of_lt_of_le (bound binder entering q quantified) progress.1.next_le
  · simp [mono] at quantified
  · obtain ⟨childFuel,receipt,same⟩ := initialized
    subst binder
    have properties := receipt.initializer_inference ready validated canonical
    have valueBelow := properties.2.1.solved.variablesBelow_apply properties.2.2
    have newBound := activeQuantifiersBelowNext_generalizeValue receipt.ready receipt.locals
      initial.nextRequirement (receipt.ready.resolve receipt.value.type) valueBelow q quantified
    rw [receipt.inference_eq]
    exact newBound

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
