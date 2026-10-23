import Solcore.SourceSemantics.SourceInferenceActualGeneralizationAutomation
import Solcore.SourceSemantics.SourceInferenceActualGeneralizationHeaderEvents
import Solcore.SourceSemantics.SourceInferenceGeneralizationReceiptCalls
import Solcore.SourceSemantics.SourceInferenceAssignedValueActualPrefix
import Solcore.SourceSemantics.SourceInferenceExpressionCallProvenance

/-! Every initialized declaration in successful source inference retains its
actual initializer, optional annotation, and generalization boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxErrors 15
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem Detail
variable {root : CallIndex}
open State (DirectRequirementsProgress)

local macro "actual_descend " parent:term : tactic => `(tactic|
  (apply CallOccurrence.child $parent
   first
   | (apply ChildStep.expression_group <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_tuple <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expressions_head <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expressions_tail <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statements_head <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statements_tail <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_initializer <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_return <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_expression <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_block <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_if_condition <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_if_then <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_if_else <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_assignment <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_bitnot <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_while_condition <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_while_body <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_for_initializer <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_for_condition <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_for_body <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_for_post <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.forItems_head <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.forItems_tail <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.forItem_initializer <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.forItem_expression <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.forItem_assignment <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.forItem_bitnot <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.assignedValue_place <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.assignedValue_value <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.place_group <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.place_index_base <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.place_index_key <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.constructorApplication_arguments <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.constructorArguments_head <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.constructorArguments_tail <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_unary <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_binary_left <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_binary_right <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_conditional_condition <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_conditional_then <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_conditional_else <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_lambda_body <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_index_base <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_index_key <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_call_constructor <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_call_arguments <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_call_callee <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_contextual_constructor <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.expression_field_constructor <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.matchCases_body <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.matchCases_tail <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_match_single <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_match_many <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_match_cases <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))
   | (apply ChildStep.statement_match_default <;> first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))))



@[simp] private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private theorem annotation_none {context : SourceInference.Context} {expected : Option Ty}
    (accepted : LocalLetRequirementTiming.Annotation context none expected) : expected = none := by
  cases accepted
  rfl

private theorem annotation_some {context : SourceInference.Context} {syntaxType : Syntax.TypeExpr} {expected : Option Ty}
    (accepted : LocalLetRequirementTiming.Annotation context (some syntaxType) expected) :
    ∃ type, expected = some type := by
  cases accepted
  exact ⟨_, rfl⟩

private def PreservesOrigins {alpha : Type} (stateOf : alpha → State) (indexOf : alpha → CallIndex)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → CallOccurrence root (indexOf result) → RelativeReadProgress root initial (stateOf result)

private theorem pair_success_origins_progress {alpha : Type}
    {operation : alpha × State} {value : alpha} {next initial : State}
    (operationSubset : RelativeReadProgress root initial operation.2)
    (success : operation = (value, next)) :
    RelativeReadProgress root initial next := by
  simpa [success] using operationSubset

private theorem pair_eq_property {alpha beta : Type} {result : alpha × beta}
    {property : beta → Prop} {indexOf : alpha → beta → CallIndex}
    (invariant : ∀ value state, result = (value, state) → CallOccurrence root (indexOf value state) → property state)
    (here : CallOccurrence root (indexOf result.1 result.2)) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state rfl here

private theorem pair_except_property {epsilon alpha beta : Type}
    {computation : Except epsilon (alpha × beta)} {result : alpha × beta}
    {property : beta → Prop} {indexOf : alpha → beta → CallIndex}
    (invariant : ∀ value state,
      computation = .ok (value, state) → CallOccurrence root (indexOf value state) → property state)
    (success : computation = .ok result)
    (here : CallOccurrence root (indexOf result.1 result.2)) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state success here

private theorem allocateExpressionId_success_origins_progress
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    RelativeReadProgress root state next :=
  pair_success_origins_progress
    (RelativeReadProgress.of_nodes_eq rfl (DirectRequirementsProgress.refl state)) success

private theorem allocateStatementId_success_origins_progress
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    RelativeReadProgress root state next :=
  pair_success_origins_progress
    (RelativeReadProgress.of_nodes_eq rfl (DirectRequirementsProgress.refl state)) success

private theorem state_fresh_success_origins_progress
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    RelativeReadProgress root state next :=
  pair_success_origins_progress (RelativeReadProgress.of_nodes_eq rfl (DirectRequirementsProgress.refl state))
    success

private theorem allocateHiddenLocal_success_origins_progress
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    RelativeReadProgress root state next :=
  pair_success_origins_progress
    (RelativeReadProgress.of_nodes_eq rfl (DirectRequirementsProgress.refl state)) success

private theorem addRequirementWithId_success_origins_progress
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    RelativeReadProgress root state next :=
  pair_success_origins_progress
    (RelativeReadProgress.addRequirementWithId state predicate) success

private theorem addRequirementsWithIds_success_origins_progress
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    RelativeReadProgress root state next :=
  pair_success_origins_progress
    (RelativeReadProgress.addRequirementsWithIds state predicates) success

private theorem allocateBinder_success_origins_progress
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    RelativeReadProgress root state next :=
  pair_success_origins_progress
    (RelativeReadProgress.of_nodes_eq rfl (DirectRequirementsProgress.refl state)) success

private theorem freshDataConstructorInstantiation_success_origins_progress
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    RelativeReadProgress root state next :=
  pair_success_origins_progress
    (RelativeReadProgress.freshDataConstructorInstantiation dataType constructor
      state) success

private theorem freshTypes_success_origins_progress
    {count : Nat} {state next : State} {types : List Ty}
    (success : freshTypes count state = (types, next)) :
    RelativeReadProgress root state next :=
  pair_success_origins_progress
    (RelativeReadProgress.freshTypes count state) success

private theorem syntheticTuple_result_origins_progress
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
    RelativeReadProgress root state result.snd := by
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
  exact RelativeReadProgressFields.expression _ _ _ _ _ (by intro _ _ impossible; cases impossible)

private theorem syntheticTuple_pair_origins_progress
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
    RelativeReadProgress root state result.snd := by
  rw [← success]
  exact RelativeReadProgressFields.expression _ _ _ _ _ (by intro _ _ impossible; cases impossible)

private theorem pure_pair_result_origins_progress {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : RelativeReadProgress root initial next)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    RelativeReadProgress root initial result.snd := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_origins_progress {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : RelativeReadProgress root initial state)
    (success : (value, state.restoreLexicalScope scope) = result) :
    RelativeReadProgress root initial result.snd := by
  rw [← success]
  exact RelativeReadProgress.trans subset
    (RelativeReadProgress.of_nodes_eq rfl (DirectRequirementsProgress.refl state))


set_option maxHeartbeats 2000000 in
private theorem actual_match_single {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {source : Syntax.Expr}
    {state : State} {result : InferredExpression × State}
    (single : sources = [source])
    (accepted : inferExprFuel fuel context source none state = .ok result) :
    matchScrutinee fuel context span sources state = .ok result := by
  simpa only [single, matchScrutinee] using accepted

private theorem actual_match_many {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {state : State}
    {elements : List InferredExpression} {next : State} {result : InferredExpression × State}
    (notSingle : ∀ source, sources = [source] → False)
    (accepted : inferExprsFuel fuel context sources state = .ok (elements, next))
    (tuple : (pure ({
        id := next.allocateExpressionId.1
        type := Ty.productMany (elements.map (·.type))},
      next.allocateExpressionId.2.recordNode (.expression {
        id := next.allocateExpressionId.1, span,
        type := Ty.productMany (elements.map (·.type)),
        form := .tuple (elements.map (·.id)) })) : Except Error (InferredExpression × State)) = .ok result) :
    matchScrutinee fuel context span sources state = .ok result := by
  unfold matchScrutinee
  split
  all_goals first
  | exact (notSingle _ rfl).elim
  | simpa only [accepted, bind, Except.bind] using tuple

private theorem inferFuel_origins_progress_internal :
    (∀ fuel context expression expected state,
      PreservesOrigins (root := root) Prod.snd (fun r => .expression fuel context expression expected state r.1 r.2) state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesOrigins (root := root) Prod.snd (fun r => .constructorApplication fuel context source id instantiation arguments expected state r.1 r.2) state
        (inferConstructorApplicationFuel fuel context source id instantiation arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesOrigins (root := root) Prod.snd (fun r => .constructorArguments fuel context sources expected state r.1 r.2) state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesOrigins (root := root) BlockResult.state (fun r => .statements fuel context statements expectedReturn state r) state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesOrigins (root := root) StatementResult.state (fun r => .statement fuel context statement expectedReturn state r) state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesOrigins (root := root) InferredForItems.state (fun r => .forItems fuel context items state r) state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesOrigins (root := root) Prod.snd (fun r => .forItem fuel context item state r.1 r.2) state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesOrigins (root := root) Prod.snd (fun r => .place fuel context target state r.1 r.2) state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesOrigins (root := root) (fun result => result.2.2) (fun r => .assignedValue fuel context target operator value state r.1 r.2.1 r.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesOrigins (root := root) Prod.snd (fun r => .expressions fuel context expressions state r.1 r.2) state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      PreservesOrigins (root := root) MatchCasesResult.state (fun r => .matchCases fuel context scrutineeType expectedReturn outerScope cases state r) state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesOrigins (root := root) Prod.snd (fun r => .expression fuel context expression expected state r.1 r.2) state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesOrigins (root := root) Prod.snd (fun r => .constructorApplication fuel context source id instantiation arguments expected state r.1 r.2) state
        (inferConstructorApplicationFuel fuel context source id instantiation arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesOrigins (root := root) Prod.snd (fun r => .constructorArguments fuel context sources expected state r.1 r.2) state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesOrigins (root := root) BlockResult.state (fun r => .statements fuel context statements expectedReturn state r) state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesOrigins (root := root) StatementResult.state (fun r => .statement fuel context statement expectedReturn state r) state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesOrigins (root := root) InferredForItems.state (fun r => .forItems fuel context items state r) state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesOrigins (root := root) Prod.snd (fun r => .forItem fuel context item state r.1 r.2) state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesOrigins (root := root) Prod.snd (fun r => .place fuel context target state r.1 r.2) state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesOrigins (root := root) (fun result => result.2.2) (fun r => .assignedValue fuel context target operator value state r.1 r.2.1 r.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesOrigins (root := root) Prod.snd (fun r => .expressions fuel context expressions state r.1 r.2) state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesOrigins (root := root) MatchCasesResult.state (fun r => .matchCases fuel context scrutineeType expectedReturn outerScope cases state r) state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope cases state))
  case case10 =>
    intro context source expected initial fuel id allocated allocation inner form ih
    intro result accepted here
    have original := accepted
    unfold inferExprFuel at accepted
    simp only [allocation, form, bind, Except.bind] at accepted
    cases child : inferExprFuel fuel context inner expected allocated with
    | error error => simp [child, bind, Except.bind] at accepted
    | ok pair =>
      have innerProgress := ih pair child (here.child (.expression_group original form allocation child))
      have record := RelativeReadProgress.recordExpressionWithExpected (root := root) (by simpa only [child, bind, Except.bind] using accepted)
        (by intro _ _ impossible; cases impossible)
      exact (allocateExpressionId_success_origins_progress allocation).trans (innerProgress.trans record)
  case case15 =>
    intro context source expected initial fuel id allocated allocation keyword parameters annotation body form ih
    intro result accepted here
    obtain ⟨boundParameters, parameterTypes, parameterState, resultType, resultState,
      bodyResult, unified, restored, parametersAccepted, prefixFacts, bodyAccepted,
      resultUnify, restoreEq, recorded⟩ :=
      inferExprFuel_success_lambda_facts form allocation accepted
    have prefixProgress : RelativeReadProgress root parameterState resultState := by
      cases prefixFacts with
      | noExpectedPartsAnnotated => exact RelativeReadProgress.refl _
      | noExpectedPartsFresh _ _ fresh =>
          exact state_fresh_success_origins_progress fresh
      | expectedPartsAnnotated _ fitted => exact RelativeReadProgress.unify fitted
      | expectedPartsInferred _ fitted => exact RelativeReadProgress.unify fitted
    have bodyProgress := ih resultType resultState bodyResult bodyAccepted
      (here.child (.expression_lambda_body accepted form allocation parametersAccepted prefixFacts bodyAccepted))
    have recordProgress := RelativeReadProgress.recordExpressionWithExpected (root := root) recorded
      (by intro _ _ impossible; cases impossible)
    rw [restoreEq] at recordProgress
    exact (allocateExpressionId_success_origins_progress allocation).trans
      ((RelativeReadProgress.bindLambdaParameters parametersAccepted).trans
        (prefixProgress.trans (bodyProgress.trans ((RelativeReadProgress.unify resultUnify).trans recordProgress))))
  case case16 =>
    intro context source expected initial fuel id allocated allocation callee arguments form constructorIH argumentsIH calleeIH
    intro result accepted here
    have allocationProgress := allocateExpressionId_success_origins_progress (root := root) allocation
    have dispatch := SourceInferenceSoundness.inferExprFuel_success_call_dispatch_provenance_facts form allocation accepted
    cases dispatch with
    | constructor discovery fresh application =>
      have childProgress := constructorIH _ _ result application
        (here.child (.expression_call_constructor accepted form allocation discovery fresh application))
      exact allocationProgress.trans ((freshDataConstructorInstantiation_success_origins_progress fresh).trans childProgress)
    | selected nonconstructor argumentsAccepted candidateOrigin selection recording =>
      have argumentsProgress := argumentsIH _ argumentsAccepted
        (here.child (.expression_call_arguments accepted form allocation nonconstructor argumentsAccepted))
      rw [← recording]
      exact allocationProgress.trans (argumentsProgress.trans
        ((RelativeReadProgress.selectFunctionCandidateFrom selection).trans (RelativeReadProgress.recordSelectedCall _ _ _ _ _)))
    | builtin nonconstructor argumentsAccepted recording =>
      have argumentsProgress := argumentsIH _ argumentsAccepted
        (here.child (.expression_call_arguments accepted form allocation nonconstructor argumentsAccepted))
      exact allocationProgress.trans (argumentsProgress.trans (RelativeReadProgress.recordBuiltinFunctionCall recording))
    | indirect nonconstructor argumentsAccepted indirect calleeAccepted application recording =>
      have argumentsProgress := argumentsIH _ argumentsAccepted
        (here.child (.expression_call_arguments accepted form allocation nonconstructor argumentsAccepted))
      have calleeProgress := calleeIH _ _ calleeAccepted
        (here.child (.expression_call_callee accepted form allocation nonconstructor argumentsAccepted indirect calleeAccepted))
      rw [← recording]
      exact allocationProgress.trans (argumentsProgress.trans (calleeProgress.trans
        ((RelativeReadProgress.applyFunctionType application).trans (RelativeReadProgress.recordIndirectCall _ _ _ _))))
  case case20 =>
    intro context source expected initial fuel id allocated allocation base dot name form ih
    intro result accepted here
    have original := accepted
    unfold inferExprFuel at accepted
    simp only [allocation, form, bind, Except.bind] at accepted
    cases discovery : constructorCalleeCandidates context allocated source with
    | error error => simp [discovery, bind, Except.bind] at accepted
    | ok candidates =>
      cases candidates with
      | nil =>
        simp only [discovery, bind, Except.bind] at accepted
        repeat' first | split at accepted
        all_goals cases accepted
      | cons first rest =>
        rcases first with ⟨dataType, constructor⟩
        cases rest with
        | cons second rest => simp [discovery, bind, Except.bind] at accepted
        | nil =>
          simp only [discovery, bind, Except.bind] at accepted
          generalize fresh : freshDataConstructorInstantiation dataType constructor allocated = pair at accepted
          rcases pair with ⟨instantiation, childState⟩
          have childProgress := ih instantiation childState result accepted
            (here.child (.expression_field_constructor original form allocation discovery fresh accepted))
          exact (allocateExpressionId_success_origins_progress allocation).trans
            ((freshDataConstructorInstantiation_success_origins_progress fresh).trans childProgress)
  case case34 =>
    intro context statement expected state fuel id allocated allocation name initializer form ih
    intro result accepted here
    have parentAccepted := here.accepted
    obtain ⟨receipt⟩ := LocalLetRequirementTiming.of_accepted form accepted
    have sameAnnotation : receipt.annotation = none := by
      have same := receipt.form.symm.trans form
      exact (Syntax.StatementValue.letDecl.inj same).2.1
    have sameExpected : receipt.expected = none := by
      exact annotation_none (sameAnnotation ▸ receipt.annotationAccepted)
    have sameInitializer : receipt.initializer = initializer := by
      have same := receipt.form.symm.trans form
      exact Option.some.inj (Syntax.StatementValue.letDecl.inj same).2.2
    apply RelativeReadProgress.initializedStatement (root := root) receipt accepted here
    have allocationState : state.allocateStatementId.2 = allocated := congrArg Prod.snd allocation
    rw [allocationState]
    exact ih _ (by simpa only [allocationState, sameInitializer, sameExpected] using receipt.child) (by
      simpa only [allocationState, sameInitializer, sameExpected] using
        here.child (statement_initializer_child receipt accepted))
  case case35 =>
    intro context statement expected state fuel id allocated allocation name syntaxType initializer form ih
    intro result accepted here
    have parentAccepted := here.accepted
    obtain ⟨receipt⟩ := LocalLetRequirementTiming.of_initialized_accepted form accepted
    have sameAnnotation : receipt.annotation = some syntaxType := by
      have same := receipt.form.symm.trans form
      exact (Syntax.StatementValue.letDecl.inj same).2.1
    have sameInitializer : receipt.initializer = initializer := by
      have same := receipt.form.symm.trans form
      exact Option.some.inj (Syntax.StatementValue.letDecl.inj same).2.2
    have expectedSome : ∃ type, receipt.expected = some type := by
      exact annotation_some (sameAnnotation ▸ receipt.annotationAccepted)
    obtain ⟨type, sameExpected⟩ := expectedSome
    apply RelativeReadProgress.initializedStatement (root := root) receipt accepted here
    have allocationState : state.allocateStatementId.2 = allocated := congrArg Prod.snd allocation
    rw [allocationState]
    exact ih type _ (by simpa only [allocationState, sameInitializer, sameExpected] using receipt.child) (by
      simpa only [allocationState, sameInitializer, sameExpected] using
        here.child (statement_initializer_child receipt accepted))
  case case45 =>
    intro context statement expected initial fuel id allocated allocation headerSpan initializers condition post body form initIH condIH bodyIH postIH
    intro result accepted here
    have parentAccepted := here.accepted
    have original := accepted
    unfold inferStatementFuel at accepted
    simp only [allocation, form, bind, Except.bind] at accepted
    cases initRun : inferForItemsFuel fuel context initializers allocated with
    | error error => simp [initRun, bind, Except.bind] at accepted
    | ok initResult =>
      cases condRun : inferExprFuel fuel context condition (some .bool) initResult.state with
      | error error => simp [initRun, condRun, bind, Except.bind] at accepted
      | ok pair =>
        rcases pair with ⟨test, testState⟩
        let loopContext := { context with loopDepth := context.loopDepth + 1 }
        cases bodyRun : inferStatementsFuel fuel loopContext body.value expected testState with
        | error error => simp [initRun, condRun, loopContext, bodyRun, bind, Except.bind] at accepted
        | ok bodyResult =>
          let afterBody := bodyResult.state.restoreLexicalScope initResult.state.lexicalScope
          cases postRun : inferForItemsFuel fuel loopContext post afterBody with
          | error error => simp [initRun, condRun, loopContext, bodyRun, afterBody, postRun, bind, Except.bind] at accepted
          | ok postResult =>
            simp only [initRun, condRun, bodyRun, postRun, loopContext, afterBody, bind, Except.bind,
              pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
            cases accepted
            have allocP := allocateStatementId_success_origins_progress (root := root) allocation
            have initP := initIH _ initRun (by first | assumption | actual_descend here)
            have condP := condIH initResult _ condRun (by first | assumption | actual_descend here)
            have bodyP := bodyIH testState _ bodyRun (by first | assumption | actual_descend here)
            have postP := postIH initResult bodyResult _ postRun (by first | assumption | actual_descend here)
            have history := allocP.trans (initP.trans (condP.trans (bodyP.trans postP)))
            refine ⟨⟨LocalReadEvents.inferStatementFuel_origins_progress original, ?_⟩, ?_⟩
            · intro wf direct reads events
              apply (history.events wf direct reads events).statement
              exact ⟨inferForItemsFuel_events initRun (by first | assumption | actual_descend here),
                inferForItemsFuel_events postRun (by first | assumption | actual_descend here)⟩
            · intro base wf direct calls
              exact (history.calls wf direct calls).statement _
  case case43 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources source single
      casesInduction bodyInduction expressionInduction
    unfold PreservesOrigins at *
    intro result success here
    have parentAccepted := here.accepted
    have statementIdSubset :=
      allocateStatementId_success_origins_progress (root := root) statementIdEq
    unfold inferStatementFuel at success
    simp only [statementIdEq, statementEq, bind, Except.bind] at success
    have singleSources : scrutinees.elements.toList = [source] := single
    simp only [singleSources] at success
    repeat' first | split at success
    all_goals try cases success
    all_goals try have actualScrutinee := actual_match_single (span := statement.span) (by assumption) (by assumption)
    all_goals try have actualScrutinee := actual_match_many (span := statement.span) (by assumption) (by assumption) (by first | assumption | (simpa only [exceptPure_eq_ok] using (by assumption)))
    all_goals actual_collect here
    all_goals actual_invoke
    all_goals try have expressionsSubset :=
      expressionInduction _ (by assumption) (by first | assumption | actual_descend here)
    all_goals try have casesSubset :=
      casesInduction _ _ _ (by assumption) (by first | assumption | actual_descend here)
    all_goals try have bodySubset :=
      bodyInduction _ _ _ (by assumption) (by first | assumption | actual_descend here)
    all_goals try have tupleSubset :=
      syntheticTuple_result_origins_progress (root := root) (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_origins_progress (root := root) (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_origins_progress (root := root) casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_origins_progress (root := root) bodySubset (by assumption)
    all_goals try simp_all
    all_goals try exact RelativeReadProgress.refl (root := root) _
    all_goals try exact RelativeReadProgress.of_nodes_eq (root := root) rfl (DirectRequirementsProgress.refl _)
    all_goals try exact RelativeReadProgress.recordStatement (root := root) _ _ (by trivial)
    all_goals dsimp only [RelativeReadProgress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals dsimp only [RelativeReadProgress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply RelativeReadProgressFields.trans (second := RelativeReadProgressFields.statement _ _ _ _ _ (by trivial))
      | apply RelativeReadProgressFields.trans (second := RelativeReadProgressFields.expression _ _ _ _ _
          (by change LocalReadEvents.Nonlocal (.call _ _ (.indirect _)); intro _ _ impossible; cases impossible))
      | apply RelativeReadProgressFields.trans (second := RelativeReadProgressFields.expression _ _ _ _ _
          (by change LocalReadEvents.Nonlocal (.constructor _ _); intro _ _ impossible; cases impossible))
      | skip
    all_goals grind [RelativeReadProgressFields.trans]
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesOrigins at *
    intro result success here
    have parentAccepted := here.accepted
    have statementIdSubset :=
      allocateStatementId_success_origins_progress (root := root) statementIdEq
    unfold inferStatementFuel at success
    simp only [statementIdEq, statementEq, bind, Except.bind] at success
    repeat' first | split at success
    all_goals try cases success
    all_goals try exact (notSingleton _ (by assumption)).elim
    all_goals try have actualScrutinee := actual_match_single (span := statement.span) (by assumption) (by assumption)
    all_goals try have actualScrutinee := actual_match_many (span := statement.span) (by assumption) (by assumption) (by first | assumption | (simpa only [exceptPure_eq_ok] using (by assumption)))
    all_goals actual_collect here
    all_goals actual_invoke
    all_goals try have expressionsSubset :=
      expressionsInduction _ (by assumption) (by first | assumption | actual_descend here)
    all_goals try have casesSubset :=
      casesInduction _ _ _ (by assumption) (by first | assumption | actual_descend here)
    all_goals try have bodySubset :=
      bodyInduction _ _ _ (by assumption) (by first | assumption | actual_descend here)
    all_goals try have tupleSubset :=
      syntheticTuple_result_origins_progress (root := root) (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_origins_progress (root := root) (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_origins_progress (root := root) casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_origins_progress (root := root) bodySubset (by assumption)
    all_goals try simp_all
    all_goals try exact RelativeReadProgress.refl (root := root) _
    all_goals try exact RelativeReadProgress.of_nodes_eq (root := root) rfl (DirectRequirementsProgress.refl _)
    all_goals try exact RelativeReadProgress.recordStatement (root := root) _ _ (by trivial)
    all_goals dsimp only [RelativeReadProgress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals dsimp only [RelativeReadProgress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply RelativeReadProgressFields.trans (second := RelativeReadProgressFields.statement _ _ _ _ _ (by trivial))
      | apply RelativeReadProgressFields.trans (second := RelativeReadProgressFields.expression _ _ _ _ _
          (by change LocalReadEvents.Nonlocal (.call _ _ (.indirect _)); intro _ _ impossible; cases impossible))
      | apply RelativeReadProgressFields.trans (second := RelativeReadProgressFields.expression _ _ _ _ _
          (by change LocalReadEvents.Nonlocal (.constructor _ _); intro _ _ impossible; cases impossible))
      | skip
    all_goals grind [RelativeReadProgressFields.trans]
  case case70 =>
    intro fuel context target operator value initial placeInduction valueInduction
    intro result accepted here
    rcases result with ⟨assignment, inferred, final⟩
    obtain ⟨place, placeState, fitted, placeAccepted, fitting, valueAccepted, _⟩ :=
      assignedValue_actual_prefix accepted
    have placeProgress := placeInduction _ placeAccepted
      (here.child (.assignedValue_place accepted placeAccepted))
    have valueProgress := valueInduction place fitted _ valueAccepted
      (here.child (.assignedValue_value accepted placeAccepted fitting valueAccepted))
    have fittingProgress : RelativeReadProgress root placeState fitted := by
      cases operator <;> first
      | exact RelativeReadProgress.unify fitting
      | (simp only [pure, Pure.pure, Except.pure, Except.ok.injEq] at fitting
         cases fitting
         exact RelativeReadProgress.refl _)
    exact placeProgress.trans (fittingProgress.trans valueProgress)
  case case67 =>
    intro context target state fuel inner form ih
    intro result accepted here
    have child : inferPlaceFuel fuel context inner state = .ok result := by
      simpa only [inferPlaceFuel, form] using accepted
    exact ih result child (here.child (.place_group accepted form child))
  all_goals
    intros
    unfold PreservesOrigins at *
    intro result success here
    have parentAccepted := here.accepted
    try exact RelativeReadProgress.localIdentifier (root := root) (by assumption) (by assumption) (by assumption) success here
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
    all_goals try have actualScrutinee := actual_match_single (span := statement.span) (by assumption) (by assumption)
    all_goals try have actualScrutinee := actual_match_many (span := statement.span) (by assumption) (by assumption) (by first | assumption | (simpa only [exceptPure_eq_ok] using (by assumption)))
    all_goals actual_collect here
    all_goals actual_invoke
    all_goals first
      | specialize ih1 _ _ (by assumption)
      | specialize ih1 _ _ _ (by assumption)
      | specialize ih1 _ _ _ _ (by assumption)
      | skip
    all_goals try specialize ih1 (by first | assumption | actual_descend here)
    all_goals first
      | specialize ih2 _ _ (by assumption)
      | specialize ih2 _ _ _ (by assumption)
      | specialize ih2 _ _ _ _ (by assumption)
      | skip
    all_goals try specialize ih2 (by first | assumption | actual_descend here)
    all_goals first
      | specialize ih3 _ _ (by assumption)
      | specialize ih3 _ _ _ (by assumption)
      | specialize ih3 _ _ _ _ (by assumption)
      | skip
    all_goals try specialize ih3 (by first | assumption | actual_descend here)
    all_goals first
      | have ih1Subset := pair_eq_property ih1 (by first | assumption | actual_descend here)
      | have ih1Subset := pair_except_property ih1 (by assumption) (by first | assumption | actual_descend here)
      | have ih1Subset := pair_except_property (ih1 _ _) (by assumption) (by first | assumption | actual_descend here)
      | skip
    all_goals first
      | have ih2Subset := pair_eq_property ih2 (by first | assumption | actual_descend here)
      | have ih2Subset := pair_except_property ih2 (by assumption) (by first | assumption | actual_descend here)
      | have ih2Subset := pair_except_property (ih2 _ _) (by assumption) (by first | assumption | actual_descend here)
      | skip
    all_goals first
      | have ih3Subset := pair_eq_property ih3 (by first | assumption | actual_descend here)
      | have ih3Subset := pair_except_property ih3 (by assumption) (by first | assumption | actual_descend here)
      | have ih3Subset := pair_except_property (ih3 _ _) (by assumption) (by first | assumption | actual_descend here)
      | skip
    all_goals try have unifiedSubset :=
      RelativeReadProgress.unify (root := root) (by assumption)
    all_goals try have expressionIdSubset :=
      allocateExpressionId_success_origins_progress (root := root) (by assumption)
    all_goals try have statementIdSubset :=
      allocateStatementId_success_origins_progress (root := root) (by assumption)
    all_goals try have freshSubset :=
      state_fresh_success_origins_progress (root := root) (by assumption)
    all_goals try have hiddenLocalSubset :=
      allocateHiddenLocal_success_origins_progress (root := root) (by assumption)
    all_goals try have requirementSubset :=
      addRequirementWithId_success_origins_progress (root := root) (by assumption)
    all_goals try have requirementsSubset :=
      addRequirementsWithIds_success_origins_progress (root := root) (by assumption)
    all_goals try have binderSubset :=
      allocateBinder_success_origins_progress (root := root) (by assumption)
    all_goals try have constructorSubset :=
      freshDataConstructorInstantiation_success_origins_progress (root := root) (by
        assumption)
    all_goals try have typesSubset :=
      freshTypes_success_origins_progress (root := root) (by assumption)
    all_goals try have recordSubset :=
      RelativeReadProgress.recordExpressionWithExpected (root := root) (by assumption) (by intro _ _ impossible; cases impossible)
    all_goals try have issuedRecord :=
      (RelativeReadProgress.addRequirementWithId (root := root) _ _).trans recordSubset
    all_goals try have batchRecord :=
      (RelativeReadProgress.addRequirementsWithIds (root := root) _ _).trans recordSubset
    all_goals try exact RelativeReadProgressFields.trans expressionIdSubset (RelativeReadProgressFields.trans (RelativeReadProgress.addRequirementWithId (root := root) _ _) recordSubset)
    all_goals try exact RelativeReadProgressFields.trans expressionIdSubset (RelativeReadProgressFields.trans (RelativeReadProgress.addRequirementsWithIds (root := root) _ _) recordSubset)
    all_goals try have lambdaSubset :=
      RelativeReadProgress.bindLambdaParameters (root := root) (by assumption)
    all_goals try
      have afterLambdaSubset := RelativeReadProgress.trans (root := root) lambdaSubset
        (RelativeReadProgress.unify (root := root) (by assumption))
    all_goals try have patternSubset :=
      RelativeReadProgress.inferMatchPatternFuel (root := root) (by assumption)
    all_goals try have unarySubset :=
      RelativeReadProgress.inferUnaryOperator (root := root) (by assumption)
    all_goals try have binarySubset :=
      RelativeReadProgress.inferBinaryOperator (root := root) (by assumption)
    all_goals try have selectionSubset :=
      RelativeReadProgress.selectFunctionCandidateFrom (root := root) (by assumption)
    all_goals try have expectedSubset :=
      RelativeReadProgress.withExpected (root := root) (by assumption)
    all_goals try have applicationSubset :=
      RelativeReadProgress.applyFunctionType (root := root) (by assumption)
    all_goals try have builtinSubset :=
      RelativeReadProgress.recordBuiltinFunctionCall (root := root) (by assumption)
    all_goals try simp_all
    all_goals try exact RelativeReadProgress.addRequirementWithId (root := root) _ _
    all_goals try exact RelativeReadProgress.refl (root := root) _
    all_goals try exact RelativeReadProgress.of_nodes_eq (root := root) rfl (DirectRequirementsProgress.refl _)
    all_goals try exact RelativeReadProgress.recordStatement (root := root) _ _ (by trivial)
    all_goals dsimp only [RelativeReadProgress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals dsimp only [RelativeReadProgress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply RelativeReadProgressFields.trans (second := RelativeReadProgressFields.statement _ _ _ _ _ (by trivial))
      | apply RelativeReadProgressFields.trans (second := RelativeReadProgressFields.expression _ _ _ _ _
          (by change LocalReadEvents.Nonlocal (.call _ _ (.indirect _)); intro _ _ impossible; cases impossible))
      | apply RelativeReadProgressFields.trans (second := RelativeReadProgressFields.expression _ _ _ _ _
          (by change LocalReadEvents.Nonlocal (.constructor _ _); intro _ _ impossible; cases impossible))
      | skip
    all_goals grind
      [RelativeReadProgressFields.trans,
        RelativeReadProgress.addRequirementWithId,
        RelativeReadProgress.addRequirementsWithIds,
        RelativeReadProgress.freshDataConstructorInstantiation,
        RelativeReadProgress.freshTypes,

        RelativeReadProgress.recordSelectedCallResult,
        RelativeReadProgress.recordSelectedCall,
        RelativeReadProgress.recordIndirectCall, RelativeReadProgress.recordStatement, RelativeReadProgress.modifyStatementNode]


theorem inferExprFuel_relative_read_progress
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result)
    (here : CallOccurrence root (.expression fuel context expression expected state result.1 result.2)) :
    RelativeReadProgress root state result.2 := by
  exact inferFuel_origins_progress_internal.1 fuel context expression
    expected state result success here

theorem inferConstructorApplicationFuel_relative_read_progress
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result)
    (here : CallOccurrence root (.constructorApplication fuel context source id instantiation arguments expected state result.1 result.2)) :
    RelativeReadProgress root state result.2 := by
  exact inferFuel_origins_progress_internal.2.1 fuel context source id
    instantiation arguments expected state result success here

theorem inferConstructorArgumentsFuel_relative_read_progress
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result)
    (here : CallOccurrence root (.constructorArguments fuel context sources expected state result.1 result.2)) :
    RelativeReadProgress root state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.1 fuel context sources
    expected state result success here

theorem inferStatementsFuel_relative_read_progress
    {fuel : Nat} {context : SourceInference.Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result)
    (here : CallOccurrence root (.statements fuel context statements expectedReturn state result)) :
    RelativeReadProgress root state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.1 fuel context
    statements expectedReturn state result success here

theorem inferStatementFuel_relative_read_progress
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result)
    (here : CallOccurrence root (.statement fuel context statement expectedReturn state result)) :
    RelativeReadProgress root state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.1 fuel context
    statement expectedReturn state result success here

theorem inferForItemsFuel_relative_read_progress
    {fuel : Nat} {context : SourceInference.Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result)
    (here : CallOccurrence root (.forItems fuel context items state result)) :
    RelativeReadProgress root state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.1 fuel context
    items state result success here

theorem inferForItemFuel_relative_read_progress
    {fuel : Nat} {context : SourceInference.Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result)
    (here : CallOccurrence root (.forItem fuel context item state result.1 result.2)) :
    RelativeReadProgress root state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.1 fuel context
    item state result success here

theorem inferPlaceFuel_relative_read_progress
    {fuel : Nat} {context : SourceInference.Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result)
    (here : CallOccurrence root (.place fuel context target state result.1 result.2)) :
    RelativeReadProgress root state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.1 fuel
    context target state result success here

theorem inferAssignedValueFuel_relative_read_progress
    {fuel : Nat} {context : SourceInference.Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result)
    (here : CallOccurrence root (.assignedValue fuel context target operator value state result.1 result.2.1 result.2.2)) :
    RelativeReadProgress root state result.2.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.1 fuel
    context target operator value state result success here

theorem inferExprsFuel_relative_read_progress
    {fuel : Nat} {context : SourceInference.Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result)
    (here : CallOccurrence root (.expressions fuel context expressions state result.1 result.2)) :
    RelativeReadProgress root state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.2.1 fuel
    context expressions state result success here

theorem inferMatchCasesFuel_relative_read_progress
    {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result)
    (here : CallOccurrence root (.matchCases fuel context scrutineeType expectedReturn outerScope cases state result)) :
    RelativeReadProgress root state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state result success here

theorem inferExprFuel_read_progress
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result)
    (here : CallOccurrence root (.expression fuel context expression expected state result.1 result.2)) :
    ReadProgress root state result.2 :=
  (inferExprFuel_relative_read_progress success here).readProgress

theorem inferConstructorApplicationFuel_read_progress
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result)
    (here : CallOccurrence root (.constructorApplication fuel context source id instantiation arguments expected state result.1 result.2)) :
    ReadProgress root state result.2 :=
  (inferConstructorApplicationFuel_relative_read_progress success here).readProgress

theorem inferConstructorArgumentsFuel_read_progress
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result)
    (here : CallOccurrence root (.constructorArguments fuel context sources expected state result.1 result.2)) :
    ReadProgress root state result.2 :=
  (inferConstructorArgumentsFuel_relative_read_progress success here).readProgress

theorem inferStatementsFuel_read_progress
    {fuel : Nat} {context : SourceInference.Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result)
    (here : CallOccurrence root (.statements fuel context statements expectedReturn state result)) :
    ReadProgress root state result.state :=
  (inferStatementsFuel_relative_read_progress success here).readProgress

theorem inferStatementFuel_read_progress
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result)
    (here : CallOccurrence root (.statement fuel context statement expectedReturn state result)) :
    ReadProgress root state result.state :=
  (inferStatementFuel_relative_read_progress success here).readProgress

theorem inferForItemsFuel_read_progress
    {fuel : Nat} {context : SourceInference.Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result)
    (here : CallOccurrence root (.forItems fuel context items state result)) :
    ReadProgress root state result.state :=
  (inferForItemsFuel_relative_read_progress success here).readProgress

theorem inferForItemFuel_read_progress
    {fuel : Nat} {context : SourceInference.Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result)
    (here : CallOccurrence root (.forItem fuel context item state result.1 result.2)) :
    ReadProgress root state result.2 :=
  (inferForItemFuel_relative_read_progress success here).readProgress

theorem inferPlaceFuel_read_progress
    {fuel : Nat} {context : SourceInference.Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result)
    (here : CallOccurrence root (.place fuel context target state result.1 result.2)) :
    ReadProgress root state result.2 :=
  (inferPlaceFuel_relative_read_progress success here).readProgress

theorem inferAssignedValueFuel_read_progress
    {fuel : Nat} {context : SourceInference.Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result)
    (here : CallOccurrence root (.assignedValue fuel context target operator value state result.1 result.2.1 result.2.2)) :
    ReadProgress root state result.2.2 :=
  (inferAssignedValueFuel_relative_read_progress success here).readProgress

theorem inferExprsFuel_read_progress
    {fuel : Nat} {context : SourceInference.Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result)
    (here : CallOccurrence root (.expressions fuel context expressions state result.1 result.2)) :
    ReadProgress root state result.2 :=
  (inferExprsFuel_relative_read_progress success here).readProgress

theorem inferMatchCasesFuel_read_progress
    {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result)
    (here : CallOccurrence root (.matchCases fuel context scrutineeType expectedReturn outerScope cases state result)) :
    ReadProgress root state result.state :=
  (inferMatchCasesFuel_relative_read_progress success here).readProgress

theorem inferExprFuel_origins_progress
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result)
    (here : CallOccurrence root (.expression fuel context expression expected state result.1 result.2)) :
    Progress root state result.2 :=
  (inferExprFuel_read_progress success here).progress

theorem inferConstructorApplicationFuel_origins_progress
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result)
    (here : CallOccurrence root (.constructorApplication fuel context source id instantiation arguments expected state result.1 result.2)) :
    Progress root state result.2 :=
  (inferConstructorApplicationFuel_read_progress success here).progress

theorem inferConstructorArgumentsFuel_origins_progress
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result)
    (here : CallOccurrence root (.constructorArguments fuel context sources expected state result.1 result.2)) :
    Progress root state result.2 :=
  (inferConstructorArgumentsFuel_read_progress success here).progress

theorem inferStatementsFuel_origins_progress
    {fuel : Nat} {context : SourceInference.Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result)
    (here : CallOccurrence root (.statements fuel context statements expectedReturn state result)) :
    Progress root state result.state :=
  (inferStatementsFuel_read_progress success here).progress

theorem inferStatementFuel_origins_progress
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result)
    (here : CallOccurrence root (.statement fuel context statement expectedReturn state result)) :
    Progress root state result.state :=
  (inferStatementFuel_read_progress success here).progress

theorem inferForItemsFuel_origins_progress
    {fuel : Nat} {context : SourceInference.Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result)
    (here : CallOccurrence root (.forItems fuel context items state result)) :
    Progress root state result.state :=
  (inferForItemsFuel_read_progress success here).progress

theorem inferForItemFuel_origins_progress
    {fuel : Nat} {context : SourceInference.Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result)
    (here : CallOccurrence root (.forItem fuel context item state result.1 result.2)) :
    Progress root state result.2 :=
  (inferForItemFuel_read_progress success here).progress

theorem inferPlaceFuel_origins_progress
    {fuel : Nat} {context : SourceInference.Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result)
    (here : CallOccurrence root (.place fuel context target state result.1 result.2)) :
    Progress root state result.2 :=
  (inferPlaceFuel_read_progress success here).progress

theorem inferAssignedValueFuel_origins_progress
    {fuel : Nat} {context : SourceInference.Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result)
    (here : CallOccurrence root (.assignedValue fuel context target operator value state result.1 result.2.1 result.2.2)) :
    Progress root state result.2.2 :=
  (inferAssignedValueFuel_read_progress success here).progress

theorem inferExprsFuel_origins_progress
    {fuel : Nat} {context : SourceInference.Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result)
    (here : CallOccurrence root (.expressions fuel context expressions state result.1 result.2)) :
    Progress root state result.2 :=
  (inferExprsFuel_read_progress success here).progress

theorem inferMatchCasesFuel_origins_progress
    {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result)
    (here : CallOccurrence root (.matchCases fuel context scrutineeType expectedReturn outerScope cases state result)) :
    Progress root state result.state :=
  (inferMatchCasesFuel_read_progress success here).progress

/-- Successful statement inference retains each initialized declaration's
actual generalization event, including declarations inside for headers. -/
theorem inferStatementsFuel_origins
    {fuel : Nat} {context : SourceInference.Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : Detail.BlockResult}
    (accepted : Detail.inferStatementsFuel fuel context statements expectedReturn state = .ok result)
    (here : CallOccurrence root (.statements fuel context statements expectedReturn state result))
    (ready : LocalGeneralizationEvents.Ready state) (origins : Origins root state.nodes) : Origins root result.state.nodes :=
  (inferStatementsFuel_origins_progress accepted here).events ready.wellFormed ready.allocated ready.origins origins


end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
