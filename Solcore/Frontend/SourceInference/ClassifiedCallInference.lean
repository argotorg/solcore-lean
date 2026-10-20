import Solcore.Frontend.SourceInference.ClassifiedCallProgress

/-! Every template classified by successful inference is an actual declaration-call
requirement. The eleven paths retain the property from the initialized state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.SourceInference.ClassifiedCallEvents
open TypeSystem Detail

@[simp] private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private def PreservesClassification {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Progress initial (stateOf result)

private theorem pair_success_classified_progress {alpha : Type}
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


private theorem allocateExpressionId_success_classified_progress
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    Progress state next :=
  pair_success_classified_progress
    (Progress.refl state) success

private theorem allocateStatementId_success_classified_progress
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    Progress state next :=
  pair_success_classified_progress
    (Progress.refl state) success

private theorem state_fresh_success_classified_progress
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    Progress state next :=
  pair_success_classified_progress (Progress.refl state)
    success

private theorem allocateHiddenLocal_success_classified_progress
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    Progress state next :=
  pair_success_classified_progress
    (Progress.refl state) success

private theorem addRequirementWithId_success_classified_progress
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    Progress state next :=
  pair_success_classified_progress
    (Progress.addRequirementWithId state predicate) success

private theorem addRequirementsWithIds_success_classified_progress
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    Progress state next :=
  pair_success_classified_progress
    (Progress.addRequirementsWithIds state predicates) success

private theorem freshDataConstructorInstantiation_success_classified_progress
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    Progress state next :=
  pair_success_classified_progress
    (Progress.freshDataConstructorInstantiation dataType constructor
      state) success

private theorem freshTypes_success_classified_progress
    {count : Nat} {state next : State} {types : List Ty}
    (success : freshTypes count state = (types, next)) :
    Progress state next :=
  pair_success_classified_progress
    (Progress.freshTypes count state) success

private theorem syntheticTuple_result_classified_progress
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
  exact Progress.refl _

private theorem syntheticTuple_pair_classified_progress
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
  exact Progress.refl _

private theorem pure_pair_result_classified_progress {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : Progress initial next)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    Progress initial result.snd := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_classified_progress {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : Progress initial state)
    (success : (value, state.restoreLexicalScope scope) = result) :
    Progress initial result.snd := by
  rw [← success]
  exact Progress.trans subset
    (Progress.refl state)


set_option maxHeartbeats 2000000 in
private theorem inferFuel_classified_progress_internal :
    (∀ fuel context expression expected state,
      PreservesClassification Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesClassification Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesClassification Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesClassification BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesClassification StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesClassification InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesClassification Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesClassification Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesClassification (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesClassification Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      PreservesClassification MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesClassification Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesClassification Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesClassification Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesClassification BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesClassification StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesClassification InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesClassification Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesClassification Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesClassification (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesClassification Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesClassification MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesClassification at *
    intro result success
    have statementIdSubset :=
      allocateStatementId_success_classified_progress statementIdEq
    unfold inferStatementFuel at success
    simp only [statementIdEq, statementEq, bind, Except.bind] at success
    repeat' first | split at success
    all_goals try cases success
    all_goals try exact (notSingleton _ (by assumption)).elim
    all_goals try have expressionsSubset :=
      expressionsInduction _ (by assumption)
    all_goals try have casesSubset :=
      casesInduction _ _ _ (by assumption)
    all_goals try have bodySubset :=
      bodyInduction _ _ _ (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_result_classified_progress (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_classified_progress (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_classified_progress casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_classified_progress bodySubset (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals try dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals try dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals grind [ProgressFields.trans, ProgressFields.refl]
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesClassification at *
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
    all_goals try have selectedSubset := Progress.selectFunctionCandidateFrom (by assumption)
    all_goals try have unifiedSubset :=
      Progress.unify (by assumption)
    all_goals simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals try dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals try dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals grind [ProgressFields.trans, ProgressFields.refl]
  case case67 =>
    unfold PreservesClassification at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesClassification at *
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
      | specialize ih1 _ _ (by assumption)
      | specialize ih1 _ _ _ (by assumption)
      | specialize ih1 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih2 _ _ (by assumption)
      | specialize ih2 _ _ _ (by assumption)
      | specialize ih2 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih3 _ _ (by assumption)
      | specialize ih3 _ _ _ (by assumption)
      | specialize ih3 _ _ _ _ (by assumption)
      | skip
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
    all_goals try have selectedSubset := Progress.selectFunctionCandidateFrom (by assumption)
    all_goals try have unifiedSubset :=
      Progress.unify (by assumption)
    all_goals try have expressionIdSubset :=
      allocateExpressionId_success_classified_progress (by assumption)
    all_goals try have statementIdSubset :=
      allocateStatementId_success_classified_progress (by assumption)
    all_goals try have freshSubset :=
      state_fresh_success_classified_progress (by assumption)
    all_goals try have hiddenLocalSubset :=
      allocateHiddenLocal_success_classified_progress (by assumption)
    all_goals try have requirementSubset :=
      addRequirementWithId_success_classified_progress (by assumption)
    all_goals try have requirementsSubset :=
      addRequirementsWithIds_success_classified_progress (by assumption)
    all_goals try have constructorSubset :=
      freshDataConstructorInstantiation_success_classified_progress (by
        assumption)
    all_goals try have typesSubset :=
      freshTypes_success_classified_progress (by assumption)
    all_goals try have recordSubset :=
      Progress.recordExpressionWithExpected (by assumption)
    all_goals try exact ProgressFields.trans expressionIdSubset recordSubset
    all_goals try have issuedRecord :=
      (Progress.addRequirementWithId _ _).trans recordSubset
    all_goals try have batchRecord :=
      (Progress.addRequirementsWithIds _ _).trans recordSubset
    all_goals try exact ProgressFields.trans expressionIdSubset (ProgressFields.trans (Progress.addRequirementWithId _ _) recordSubset)
    all_goals try exact ProgressFields.trans expressionIdSubset (ProgressFields.trans (Progress.addRequirementsWithIds _ _) recordSubset)
    all_goals try have lambdaSubset :=
      Progress.bindLambdaParameters (by assumption)
    all_goals try
      have afterLambdaSubset := Progress.trans lambdaSubset
        (Progress.unify (by assumption))
    all_goals try have patternSubset :=
      Progress.inferMatchPatternFuel (by assumption)
    all_goals try have unarySubset :=
      Progress.inferUnaryOperator (by assumption)
    all_goals try have binarySubset :=
      Progress.inferBinaryOperator (by assumption)
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
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals try dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals try apply ProgressFields.trans (second := ProgressFields.generalized _ _ _ _)
    all_goals grind
      [ProgressFields.trans, ProgressFields.refl,
        Progress.addRequirementWithId,
        Progress.addRequirementsWithIds,
        Progress.freshDataConstructorInstantiation,
        Progress.freshTypes,

        Progress.recordSelectedCallResult,
        Progress.recordSelectedCall,
        Progress.recordIndirectCall, Progress.recordStatement, Progress.modifyStatementNode]


theorem inferExprFuel_classified_progress
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    Progress state result.2 := by
  exact inferFuel_classified_progress_internal.1 fuel context expression
    expected state result success

theorem inferConstructorApplicationFuel_classified_progress
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_classified_progress_internal.2.1 fuel context source id
    instantiation arguments expected state result success

theorem inferConstructorArgumentsFuel_classified_progress
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_classified_progress_internal.2.2.1 fuel context sources
    expected state result success

theorem inferStatementsFuel_classified_progress
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    Progress state result.state := by
  exact inferFuel_classified_progress_internal.2.2.2.1 fuel context
    statements expectedReturn state result success

theorem inferStatementFuel_classified_progress
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result) :
    Progress state result.state := by
  exact inferFuel_classified_progress_internal.2.2.2.2.1 fuel context
    statement expectedReturn state result success

theorem inferForItemsFuel_classified_progress
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    Progress state result.state := by
  exact inferFuel_classified_progress_internal.2.2.2.2.2.1 fuel context
    items state result success

theorem inferForItemFuel_classified_progress
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_classified_progress_internal.2.2.2.2.2.2.1 fuel context
    item state result success

theorem inferPlaceFuel_classified_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_classified_progress_internal.2.2.2.2.2.2.2.1 fuel
    context target state result success

theorem inferAssignedValueFuel_classified_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    Progress state result.2.2 := by
  exact inferFuel_classified_progress_internal.2.2.2.2.2.2.2.2.1 fuel
    context target operator value state result success

theorem inferExprsFuel_classified_progress
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_classified_progress_internal.2.2.2.2.2.2.2.2.2.1 fuel
    context expressions state result success

theorem inferMatchCasesFuel_classified_progress
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    Progress state result.state := by
  exact inferFuel_classified_progress_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state result success

/-- Classification follows all actual nested lexical scopes. -/
theorem inferStatementsFuel_classified
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : Detail.BlockResult}
    (accepted : Detail.inferStatementsFuel fuel context statements expectedReturn state = .ok result)
    (origins : Classified state) : Classified result.state :=
  inferStatementsFuel_classified_progress accepted origins

theorem initial_classified (owner : Resolved.DeclarationId)
    (parameters : TypeSystem.Environment) (comptime : List Bool) :
    Classified (State.initial owner parameters comptime) := by
  intro requirement member
  cases member

/-- Classification starts empty in the actual original function run. -/
theorem initializedStatements_classified
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {owner : Resolved.DeclarationId}
    {parameters : TypeSystem.Environment} {comptime : List Bool}
    {result : Detail.BlockResult}
    (accepted : Detail.inferStatementsFuel fuel context statements expectedReturn
      (State.initial owner parameters comptime) = .ok result) : Classified result.state :=
  inferStatementsFuel_classified accepted (initial_classified _ _ _)

end Solcore.Frontend.SourceInference.ClassifiedCallEvents
