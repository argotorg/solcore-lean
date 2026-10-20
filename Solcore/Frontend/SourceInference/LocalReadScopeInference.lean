import Solcore.Frontend.SourceInference.LocalReadScopeHelpers

/-! Actual inference cannot create a reference to a retired older local ID.
Match recursion retains the genuine saved outer-scope membership. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.SourceInference.LocalReadScopeProgress
open TypeSystem Detail

@[simp] private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private def PreservesScope {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Progress initial (stateOf result)

private theorem pair_success_scope_progress {alpha : Type}
    {operation : alpha × State} {value : alpha} {next initial : State}
    (operationSubset : Progress initial operation.2)
    (success : operation = (value, next)) :
    Progress initial next := by
  simpa [success] using operationSubset

private theorem pair_eq_property {alpha beta : Type} {result : alpha × beta}
    {property : beta → Prop}
    (invariant : ∀ value state, result = (value, state) → property state) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state rfl

private theorem pair_except_property {epsilon alpha beta : Type}
    {computation : Except epsilon (alpha × beta)} {result : alpha × beta}
    {property : beta → Prop}
    (invariant : ∀ value state,
      computation = .ok (value, state) → property state)
    (success : computation = .ok result) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state success

private theorem anchored_pair_except_property {epsilon alpha beta : Type}
    {anchor : alpha × State}
    {computation : alpha → State → Except epsilon (beta × State)}
    {initial state : State} {result : beta × State}
    (_anchorInvariant : ∀ value next,
      (Except.ok anchor : Except epsilon (alpha × State)) =
          Except.ok (value, next) →
        Progress initial next)
    (invariant : ∀ value state result next,
      computation value state = .ok (result, next) →
        Progress state next)
    (success : computation anchor.1 state = .ok result) :
    Progress state result.2 := by
  rcases anchor with ⟨value, anchorState⟩
  rcases result with ⟨result, next⟩
  exact invariant value state result next success


private theorem allocateExpressionId_success_scope_progress
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.refl state) success

private theorem allocateStatementId_success_scope_progress
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.refl state) success

private theorem state_fresh_success_scope_progress
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    Progress state next :=
  pair_success_scope_progress (Progress.refl state)
    success

private theorem allocateHiddenLocal_success_scope_progress
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.allocateHiddenLocal state) success

private theorem addRequirementWithId_success_scope_progress
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.addRequirementWithId state predicate) success

private theorem addRequirementsWithIds_success_scope_progress
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.addRequirementsWithIds state predicates) success

private theorem allocateBinder_success_scope_progress
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.allocateBinder state name scheme span comptime schemeRequirements) success

private theorem freshDataConstructorInstantiation_success_scope_progress
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.freshDataConstructorInstantiation dataType constructor
      state) success

private theorem freshTypes_success_scope_progress
    {count : Nat} {state next : State} {types : List Ty}
    (success : freshTypes count state = (types, next)) :
    Progress state next :=
  pair_success_scope_progress
    (Progress.freshTypes count state) success

private theorem syntheticTuple_result_scope_progress
    {elements : List InferredExpression} {span : Syntax.SourceSpan}
    {state : State} {result : InferredExpression × State}
    (success : (pure ({
        id := state.allocateExpressionId.fst
        type := Ty.productMany (elements.map (·.type))
      }, state.allocateExpressionId.snd.recordNode (.expression {
        id := state.allocateExpressionId.fst
        span
        type := Ty.productMany (elements.map (·.type))
        form := .tuple (elements.map (·.id))
      })) : Except Error (InferredExpression × State)) = .ok result) :
    Progress state result.snd := by
  have resultEq : ({
      id := state.allocateExpressionId.fst
      type := Ty.productMany (elements.map (·.type))
    }, state.allocateExpressionId.snd.recordNode (.expression {
      id := state.allocateExpressionId.fst
      span
      type := Ty.productMany (elements.map (·.type))
      form := .tuple (elements.map (·.id))
    })) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact Progress.recordExpression _ _ (by intro _ _ impossible; cases impossible)

private theorem syntheticTuple_pair_scope_progress
    {elements : List InferredExpression} {span : Syntax.SourceSpan}
    {state : State} {result : InferredExpression × State}
    (success : ({
        id := state.allocateExpressionId.fst
        type := Ty.productMany (elements.map (·.type))
      }, state.allocateExpressionId.snd.recordNode (.expression {
        id := state.allocateExpressionId.fst
        span
        type := Ty.productMany (elements.map (·.type))
        form := .tuple (elements.map (·.id))
      })) = result) :
    Progress state result.snd := by
  rw [← success]
  exact Progress.recordExpression _ _ (by intro _ _ impossible; cases impossible)

private theorem pure_pair_result_scope_progress {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : Progress initial next)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    Progress initial result.snd := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_scope_progress {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : Progress initial state)
    (saved : scope.binders ⊆ initial.localBinders)
    (success : (value, state.restoreLexicalScope scope) = result) :
    Progress initial result.snd := by
  rw [← success]
  exact Fields.restore subset saved


private theorem hidden_start {next after : Nat} {binders afterBinders : List TypedBinder}
    {nodes afterNodes : List Node}
    (progress : Fields (next + 1) binders nodes after afterBinders afterNodes) :
    Fields next binders nodes after afterBinders afterNodes :=
  Fields.trans (Fields.advance _ _ _ _ (Nat.le_succ _)) progress

private theorem restored_start {next after : Nat} {binders afterBinders : List TypedBinder}
    {nodes afterNodes : List Node}
    (progress : Fields next binders nodes after afterBinders afterNodes) :
    Fields next binders nodes after binders afterNodes :=
  Fields.restore progress (fun _ member => member)

private theorem restored_then {bn mn an : Nat} {bb mb ab : List TypedBinder}
    {bs ms ads : List Node}
    (initialStep : Fields bn bb bs mn mb ms)
    (suffix : Fields mn bb ms an ab ads) : Fields bn bb bs an ab ads :=
  Fields.trans (Fields.restore initialStep (fun _ member => member)) suffix

private theorem restored_saved_then {bn mn an : Nat} {bb mb ab outer : List TypedBinder}
    {bs ms ads : List Node}
    (initialStep : Fields bn bb bs mn mb ms) (saved : outer ⊆ bb)
    (suffix : Fields mn outer ms an ab ads) : Fields bn bb bs an ab ads :=
  Fields.trans (Fields.restore initialStep saved) suffix

private theorem binders_self (binders : List TypedBinder) : binders ⊆ binders :=
  fun _ member => member

set_option maxHeartbeats 2000000 in
private theorem inferFuel_scope_progress_internal :
    (∀ fuel context expression expected state,
      PreservesScope Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesScope Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesScope Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesScope BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesScope StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesScope InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesScope Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesScope Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesScope (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesScope Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      outerScope.binders ⊆ state.localBinders →
      PreservesScope MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesScope Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesScope Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesScope Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesScope BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesScope StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesScope InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesScope Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesScope Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesScope (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesScope Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      outerScope.binders ⊆ state.localBinders →
      PreservesScope MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesScope at *
    intro result success
    have statementIdSubset :=
      allocateStatementId_success_scope_progress statementIdEq
    unfold inferStatementFuel at success
    simp only [statementIdEq, statementEq, bind, Except.bind] at success
    repeat' first | split at success
    all_goals try cases success
    all_goals try exact (notSingleton _ (by assumption)).elim
    all_goals try have expressionsSubset :=
      expressionsInduction _ (by assumption)
    all_goals try have casesSubset :=
      casesInduction _ _ (fun _ member => member) _ (by assumption)
    all_goals try have bodySubset :=
      bodyInduction _ _ _ (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_result_scope_progress (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_scope_progress (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_scope_progress casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_scope_progress bodySubset (by simpa only [State.lexicalScope] using (List.Subset.refl _)) (by assumption)
    all_goals try
      have restoredWhole := restored_pair_result_scope_progress
        (Progress.trans casesSubset bodySubset) (fun _ member => member) (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals try dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, State.lexicalScope, State.addRequirementWithId, State.addRequirementsWithIds, recordExpression, recordIndirectCall]
    all_goals try dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh, State.lexicalScope, State.addRequirementWithId, State.addRequirementsWithIds,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply Fields.trans (second := Fields.statement _ _ _ _)
      | apply Fields.trans (second := Fields.expression _ _ _ _
          (by change ∀ _ _, (.call _ _ (.indirect _) : ExpressionForm) = _ → _; intro _ _ impossible; cases impossible))
      | apply Fields.trans (second := Fields.expression _ _ _ _
          (by change ∀ _ _, (.constructor _ _ : ExpressionForm) = _ → _; intro _ _ impossible; cases impossible))
      | skip
    all_goals try
      exact Fields.trans statementIdSubset
        (Fields.trans expressionsSubset (Fields.trans tupleSubset (hidden_start restoredWhole)))
    all_goals try solve | grind [Fields.trans, Fields.restore, Fields.refl, hidden_start, restored_start, restored_then, restored_saved_then, binders_self]
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesScope at *
    intro result success
    unfold inferAssignedValueFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
    all_goals try rcases v with ⟨place, placeState⟩
    all_goals try rcases v_2 with ⟨inferred, resultState⟩
    all_goals
      have placeSubset := pair_except_property placeInduction rfl
    all_goals try have valueSubset :=
      valueInduction place v_1 inferred resultState (by assumption)
    all_goals try
      have valueSubset := anchored_pair_except_property placeInduction
        valueInduction (by assumption)
    all_goals try have valueSubset :=
      pair_except_property (valueInduction _ _) (by assumption)
    all_goals try have unifiedSubset :=
      Progress.unify (by assumption)
    all_goals simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals try dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, State.lexicalScope, State.addRequirementWithId, State.addRequirementsWithIds, recordExpression, recordIndirectCall]
    all_goals try dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh, State.lexicalScope, State.addRequirementWithId, State.addRequirementsWithIds,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply Fields.trans (second := Fields.statement _ _ _ _)
      | apply Fields.trans (second := Fields.expression _ _ _ _
          (by change ∀ _ _, (.call _ _ (.indirect _) : ExpressionForm) = _ → _; intro _ _ impossible; cases impossible))
      | apply Fields.trans (second := Fields.expression _ _ _ _
          (by change ∀ _ _, (.constructor _ _ : ExpressionForm) = _ → _; intro _ _ impossible; cases impossible))
      | skip
    all_goals try solve | grind [Fields.trans, Fields.restore, Fields.refl, hidden_start, restored_start, binders_self]
  case case67 =>
    unfold PreservesScope at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesScope at *
    intro result success
    try exact Progress.localIdentifier (by assumption) (by assumption) (by assumption) success
  all_goals
    first
      | unfold inferExprFuel at success
      | unfold inferConstructorApplicationFuel at success
      | unfold inferConstructorArgumentsFuel at success
      | unfold inferStatementsFuel at success
      | unfold inferStatementFuel at success
      | unfold inferForItemsFuel at success
      | unfold inferForItemFuel at success
      | unfold inferPlaceFuel at success
      | unfold inferAssignedValueFuel at success
      | unfold inferExprsFuel at success
      | unfold inferMatchCasesFuel at success
    try simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
    all_goals try rcases v with ⟨v0a, v0b⟩
    all_goals try rcases v_1 with ⟨v1a, v1b⟩
    all_goals try rcases v_2 with ⟨v2a, v2b⟩
    all_goals try rcases v_3 with ⟨v3a, v3b⟩
    all_goals try rcases v_4 with ⟨v4a, v4b⟩
    all_goals try subst_vars
    all_goals first
      | have ih1Subset := pair_eq_property ih1
      | have ih1Subset := pair_except_property ih1 (by assumption)
      | have ih1Subset := pair_except_property (ih1 _ _) (by assumption)
      | skip
    all_goals first
      | have ih2Subset := pair_eq_property ih2
      | have ih2Subset := pair_except_property ih2 (by assumption)
      | have ih2Subset := pair_except_property (ih2 _ _) (by assumption)
      | skip
    all_goals first
      | have ih3Subset := pair_eq_property ih3
      | have ih3Subset := pair_except_property ih3 (by assumption)
      | have ih3Subset := pair_except_property (ih3 _ _) (by assumption)
      | skip
    all_goals try have unifiedSubset :=
      Progress.unify (by assumption)
    all_goals try have expressionIdSubset :=
      allocateExpressionId_success_scope_progress (by assumption)
    all_goals try have statementIdSubset :=
      allocateStatementId_success_scope_progress (by assumption)
    all_goals try have freshSubset :=
      state_fresh_success_scope_progress (by assumption)
    all_goals try have hiddenLocalSubset :=
      allocateHiddenLocal_success_scope_progress (by assumption)
    all_goals try have requirementSubset :=
      addRequirementWithId_success_scope_progress (by assumption)
    all_goals try have requirementsSubset :=
      addRequirementsWithIds_success_scope_progress (by assumption)
    all_goals try have binderSubset :=
      allocateBinder_success_scope_progress (by assumption)
    all_goals try have constructorSubset :=
      freshDataConstructorInstantiation_success_scope_progress (by
        assumption)
    all_goals try have typesSubset :=
      freshTypes_success_scope_progress (by assumption)
    all_goals try have recordSubset :=
      Progress.recordExpressionWithExpected (by assumption) (by intro _ _ impossible; cases impossible)
    all_goals try have issuedRecord :=
      (Progress.addRequirementWithId _ _).trans recordSubset
    all_goals try have batchRecord :=
      (Progress.addRequirementsWithIds _ _).trans recordSubset
    all_goals try exact Fields.trans expressionIdSubset (Fields.trans (Progress.addRequirementWithId _ _) recordSubset)
    all_goals try exact Fields.trans expressionIdSubset (Fields.trans (Progress.addRequirementsWithIds _ _) recordSubset)
    all_goals try have lambdaSubset :=
      Progress.bindLambdaParameters (by assumption)
    all_goals try have afterLambdaSubset := Progress.trans lambdaSubset unifiedSubset
    all_goals try have patternSubset :=
      Progress.inferMatchPatternFuel (by assumption)
    all_goals try have unarySubset :=
      Progress.inferUnaryOperator (by assumption)
    all_goals try have binarySubset :=
      Progress.inferBinaryOperator (by assumption)
    all_goals try have selectionSubset :=
      Progress.selectFunctionCandidateFrom (by assumption)
    all_goals try have expectedSubset :=
      Progress.withExpected (by assumption)
    all_goals try have applicationSubset :=
      Progress.applyFunctionType (by assumption)
    all_goals try have builtinSubset :=
      Progress.recordBuiltinFunctionCall (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.addRequirementWithId _ _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals try dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, State.lexicalScope, State.addRequirementWithId, State.addRequirementsWithIds, recordExpression, recordIndirectCall]
    all_goals try dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh, State.lexicalScope, State.addRequirementWithId, State.addRequirementsWithIds,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply Fields.trans (second := Fields.statement _ _ _ _)
      | apply Fields.trans (second := Fields.expression _ _ _ _
          (by change ∀ _ _, (.call _ _ (.indirect _) : ExpressionForm) = _ → _; intro _ _ impossible; cases impossible))
      | apply Fields.trans (second := Fields.expression _ _ _ _
          (by change ∀ _ _, (.constructor _ _ : ExpressionForm) = _ → _; intro _ _ impossible; cases impossible))
      | skip
    all_goals try solve | grind
      [Fields.trans, Fields.restore, Fields.refl, hidden_start, restored_start, binders_self,
        Progress.unify, Progress.addRequirementWithId,
        Progress.addRequirementsWithIds,
        Progress.freshDataConstructorInstantiation,
        Progress.freshTypes,

        Progress.recordSelectedCallResult,
        Progress.recordSelectedCall,
        Progress.recordIndirectCall, Progress.recordStatement, Progress.modifyStatementNode]
  all_goals expose_names
  all_goals try solve
    | apply Fields.trans expressionIdSubset
      apply Fields.trans (ih2 v.fst v.snd rfl)
      apply Fields.trans (ih1 v.snd v_1.fst v_1.snd heq_1)
      apply Fields.trans selectionSubset
      apply Fields.trans expectedSubset
      exact Progress.recordSelectedCallResult _ _ _ _ _ _ _ _
  all_goals try solve
    | exact Fields.trans expressionIdSubset
        (restored_then (Fields.trans (Progress.trans lambdaSubset (Progress.unify heq_2))
          (Fields.trans (ih1 v_2 v_1 v_3 heq_4) unifiedSubset)) recordSubset)
  all_goals try solve
    | exact Fields.trans expressionIdSubset
        (restored_then (Fields.trans (Progress.trans lambdaSubset (Progress.unify heq_2))
          (Fields.trans (ih1 snd_1 v_1 v_2 heq_4) unifiedSubset)) recordSubset)
  all_goals try solve
    | exact Fields.trans expressionIdSubset
        (restored_then (Fields.trans lambdaSubset
          (Fields.trans (ih1 v_1 v.2.2 v_2 heq_3) unifiedSubset)) recordSubset)
  all_goals try solve
    | exact Fields.trans expressionIdSubset
        (restored_then (Fields.trans lambdaSubset
          (Fields.trans (ih1 v.2.2.fresh.1 v.2.2.fresh.2 v_1 heq_2) unifiedSubset)) recordSubset)
  all_goals try solve
    | have sameSource : source = source_1 := by grind
      rw [sameSource] at ih1
      have expressionStep := ih1 v.fst v.snd heq_1
      have casesStep := ih3 v.fst v.snd.allocateHiddenLocal.2 (fun _ member => member) v_1 heq_2
      exact Fields.trans statementIdSubset (Fields.trans expressionStep (hidden_start casesStep))
  all_goals try solve
    | have sameSource : source = source_1 := by grind
      rw [sameSource] at ih1
      have expressionStep := ih1 v.fst v.snd heq_1
      have casesStep := ih3 v.fst v.snd.allocateHiddenLocal.2 (fun _ member => member) v_1 heq_2
      have bodyStep := ih2 v_1 elseBody_1 v_2 heq_4
      exact Fields.trans statementIdSubset
        (Fields.trans expressionStep (restored_start (hidden_start (Fields.trans casesStep bodyStep))))
  all_goals try solve
    | have conditionStep := ih3 v v_1.fst v_1.snd heq_1
      have bodyStep := ih2 v_1.snd v_2 heq_2
      have postStep := ih1 v v_2 v_3 heq_3
      exact Fields.trans statementIdSubset
        (restored_start (Fields.trans ih4 (restored_then (Fields.trans conditionStep bodyStep) postStep)))
  all_goals try solve
    | have bodyStep := ih2 v.snd v_1 heq_1
      have tailStep := ih1 v_1 (fun _ member => member) v_2 heq_2
      exact Fields.trans (Fields.restore (Fields.trans patternSubset bodyStep) h) tailStep

  all_goals try solve
    | have conditionStep := ih3 v.fst v.snd rfl
      have thenStep := ih2 v.snd v_1 heq_1
      have elseStep := ih1 v.snd v_1 elseBody_1 v_2 heq_2
      exact Fields.trans statementIdSubset
        (Fields.trans conditionStep (restored_start (restored_then thenStep elseStep)))

  all_goals try solve
    | refine Fields.trans ?_ (Fields.allocate _ _ _ _ ?_)
      · grind [Fields.trans, Fields.refl]
      · rfl


theorem inferExprFuel_scope_progress
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    Progress state result.2 := by
  exact inferFuel_scope_progress_internal.1 fuel context expression
    expected state result success

theorem inferConstructorApplicationFuel_scope_progress
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_scope_progress_internal.2.1 fuel context source id
    instantiation arguments expected state result success

theorem inferConstructorArgumentsFuel_scope_progress
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_scope_progress_internal.2.2.1 fuel context sources
    expected state result success

theorem inferStatementsFuel_scope_progress
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    Progress state result.state := by
  exact inferFuel_scope_progress_internal.2.2.2.1 fuel context
    statements expectedReturn state result success

theorem inferStatementFuel_scope_progress
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result) :
    Progress state result.state := by
  exact inferFuel_scope_progress_internal.2.2.2.2.1 fuel context
    statement expectedReturn state result success

theorem inferForItemsFuel_scope_progress
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    Progress state result.state := by
  exact inferFuel_scope_progress_internal.2.2.2.2.2.1 fuel context
    items state result success

theorem inferForItemFuel_scope_progress
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_scope_progress_internal.2.2.2.2.2.2.1 fuel context
    item state result success

theorem inferPlaceFuel_scope_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_scope_progress_internal.2.2.2.2.2.2.2.1 fuel
    context target state result success

theorem inferAssignedValueFuel_scope_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    Progress state result.2.2 := by
  exact inferFuel_scope_progress_internal.2.2.2.2.2.2.2.2.1 fuel
    context target operator value state result success

theorem inferExprsFuel_scope_progress
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_scope_progress_internal.2.2.2.2.2.2.2.2.2.1 fuel
    context expressions state result success

theorem inferMatchCasesFuel_scope_progress
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (saved : outerScope.binders ⊆ state.localBinders)
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    Progress state result.state := by
  exact inferFuel_scope_progress_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state saved result success

end Solcore.Frontend.SourceInference.LocalReadScopeProgress
