import Solcore.SourceSemantics.Internal.Execution.CallGraph
import Solcore.Frontend.SourceInference.Internal.LocalGeneralization
import Lean
import Solcore.Frontend.SourceInference.Internal.LocalReadScopes
import Solcore.Frontend.SourceInference.Internal.LocalReadOrigins

/-!
# Local reads of inference

Local references keep their issuing lookup, and read progress shares the generalization traversal.
This file sits below the static context, because its proofs mean `Frontend.SourceInference.Context`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualGeneralizationProgress
/-! Existing read-origin progress accompanies exact-call event inventory.
The primitives preserve the same source forms and ledger transitions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem Detail
variable {root : CallIndex}
open State (DirectRequirementsProgress)

structure ProgressFields (root : CallIndex)
    (beforeNodes : List Node) (beforeRows : List Requirement) (beforeNext : Nat) (beforeDirect : List RequirementId)
    (afterNodes : List Node) (afterRows : List Requirement) (afterNext : Nat) (afterDirect : List RequirementId) : Prop where
  reads : LocalReadEvents.ProgressFields beforeNodes beforeRows beforeNext beforeDirect afterNodes afterRows afterNext afterDirect
  events : beforeRows.map (fun requirement => requirement.id.index) = List.range beforeNext →
    beforeDirect ⊆ beforeRows.map Requirement.id →
    LocalReadEvents.OriginsFields beforeNodes beforeRows beforeNext beforeDirect →
    Origins root beforeNodes → Origins root afterNodes

abbrev Progress (root : CallIndex) (before after : State) : Prop :=
  ProgressFields root before.nodes before.requirements before.nextRequirement before.directCallRequirements
    after.nodes after.requirements after.nextRequirement after.directCallRequirements

theorem ProgressFields.trans
    {bn mn an : List Node} {br mr ar : List Requirement} {bi mi ai : Nat}
    {bd md ad : List RequirementId}
    (first : ProgressFields root bn br bi bd mn mr mi md)
    (second : ProgressFields root mn mr mi md an ar ai ad) :
    ProgressFields root bn br bi bd an ar ai ad :=
  ⟨first.reads.trans second.reads, fun wf allocated reads events =>
    second.events (first.reads.ledger.wellFormed wf)
      (first.reads.ledger.allocated wf allocated) (first.reads.origins wf allocated reads)
      (first.events wf allocated reads events)⟩

theorem ProgressFields.statement (nodes : List Node) (rows : List Requirement)
    (next : Nat) (direct : List RequirementId) (node : StatementNode) (event : Statement root node) :
    ProgressFields root nodes rows next direct (nodes ++ [.statement node]) rows next direct :=
  ⟨LocalReadEvents.ProgressFields.statement _ _ _ _ _, fun _ _ _ origins => origins.statement node event⟩

theorem ProgressFields.expression (nodes : List Node) (rows : List Requirement)
    (next : Nat) (direct : List RequirementId) (node : ExpressionNode)
    (nonlocal : LocalReadEvents.Nonlocal node.form) :
    ProgressFields root nodes rows next direct (nodes ++ [.expression node]) rows next direct :=
  ⟨LocalReadEvents.ProgressFields.expression _ _ _ _ _ nonlocal, fun _ _ _ origins => origins.expression node⟩

namespace Progress
theorem refl (state : State) : Progress root state state := ⟨LocalReadEvents.Progress.refl _, fun _ _ _ origins => origins⟩
theorem trans {before middle after : State} (first : Progress root before middle) (second : Progress root middle after) :
    Progress root before after := ProgressFields.trans first second

theorem of_nodes_eq {before after : State} (same : after.nodes = before.nodes)
    (ledger : DirectRequirementsProgress before after) : Progress root before after :=
  ⟨LocalReadEvents.Progress.of_nodes_eq same ledger, fun _ _ _ origins => same.symm ▸ origins⟩

theorem recordStatement (state : State) (node : StatementNode) (event : Statement root node) :
    Progress root state (state.recordNode (.statement node)) :=
  ⟨LocalReadEvents.Progress.recordStatement _ _, fun _ _ _ origins => origins.statement node event⟩

theorem modifyStatementNode (state : State) (id : StatementId) (modify : StatementNode → StatementNode)
    (forms : ∀ node, (modify node).form = node.form) : Progress root state (state.modifyStatementNode id modify) := by
  refine ⟨LocalReadEvents.Progress.modifyStatementNode _ _ _, ?_⟩
  intro _ _ _ origins statement present
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression node => cases same
  | statement original =>
    simp only at same
    split at same <;> cases same
    · exact (origins original member).same_form (forms original)
    · exact origins _ member

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Progress root state (state.addRequirementWithId predicate).2 :=
  of_nodes_eq rfl (.addRequirementWithId _ _)

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress root state (state.addRequirementsWithIds predicates).2 :=
  of_nodes_eq (State.addRequirementsWithIds_nodes _ _) (.addRequirementsWithIds _ _)

end Progress

theorem Origins.modifyExpressionNode {state : State} (origins : Origins root state.nodes)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode) :
    Origins root (state.modifyExpressionNode id modify).nodes := by
  intro statement present
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression node => simp only at same; split at same <;> cases same
  | statement original => cases same; exact origins _ member

theorem Origins.attachExpressionCoercions {state : State} (origins : Origins root state.nodes)
    (entries : List Detail.ExpressionCoercions) : Origins root (Detail.attachExpressionCoercions state entries).nodes := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact origins
  | cons entry rest ih => exact ih (origins.modifyExpressionNode _ _)

theorem Origins.recordExpression {state : State} (origins : Origins root state.nodes)
    (source : Syntax.Expr) (expression : InferredExpression) (form : ExpressionForm)
    (requirements : List RequirementId) (coercions : List CoercionStep) (start : Option Nat := none) :
    Origins root (Detail.recordExpression source expression form requirements coercions state start).2.nodes :=
  origins.expression _

theorem Origins.recordExpressionWithExpected {state : State} (origins : Origins root state.nodes)
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result) :
    Origins root result.2.nodes := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  have same := (Detail.withExpected_occurrenceState_eq fit).1
  exact (show Origins root fitted.state.nodes from same.symm ▸ origins).expression _

namespace Progress
theorem recordExpressionWithExpected
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : Progress root state result.2 :=
  ⟨LocalReadEvents.Progress.recordExpressionWithExpected accepted nonlocal,
    fun _ _ _ origins => origins.recordExpressionWithExpected accepted⟩

theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Progress root initial result.2 := by
  refine ⟨LocalReadEvents.Progress.localIdentifier form allocation found accepted, ?_⟩
  intro _ _ _ origins
  apply Origins.recordExpressionWithExpected (accepted := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted)
  rw [State.addRequirementsWithIds_nodes]
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  simpa only [same, State.allocateExpressionId_nodes] using origins

theorem unify {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : Progress root state next :=
  ⟨LocalReadEvents.Progress.unify accepted, fun _ _ _ origins =>
    (unify_occurrenceState_eq accepted).1.symm ▸ origins⟩

theorem withExpected
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : withExpected context state actual expected = .ok result) :
    Progress root state result.state :=
  ⟨LocalReadEvents.Progress.withExpected accepted, fun _ _ _ origins =>
    (withExpected_occurrenceState_eq accepted).1.symm ▸ origins⟩

theorem selectFunctionCandidateFrom
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    Progress root state result.state :=
  ⟨LocalReadEvents.Progress.selectFunctionCandidateFrom accepted, fun _ _ _ origins =>
    (selectFunctionCandidateFrom_occurrenceState_eq accepted).1.symm ▸ origins⟩

theorem inferUnaryOperator
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    Progress root state result.state :=
  ⟨LocalReadEvents.Progress.inferUnaryOperator success, fun _ _ _ origins =>
    (inferUnaryOperator_occurrenceState_eq success).1.symm ▸ origins⟩

theorem inferBinaryOperator
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    Progress root state result.state :=
  ⟨LocalReadEvents.Progress.inferBinaryOperator success, fun _ _ _ origins =>
    (inferBinaryOperator_occurrenceState_eq success).1.symm ▸ origins⟩

theorem applyFunctionType
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    Progress root state result.state :=
  ⟨LocalReadEvents.Progress.applyFunctionType success, fun _ _ _ origins =>
    (applyFunctionType_occurrenceState_eq success).1.symm ▸ origins⟩

theorem bindLambdaParameters
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    Progress root state result.2.2 :=
  ⟨LocalReadEvents.Progress.bindLambdaParameters success, fun _ _ _ origins =>
    (bindLambdaParameters_occurrenceState_eq success).1.symm ▸ origins⟩

theorem inferMatchPatternFuel
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress root state result.2 :=
  ⟨LocalReadEvents.Progress.inferMatchPatternFuel success, fun _ _ _ origins =>
    (inferMatchPatternFuel_occurrenceState_eq success).1.symm ▸ origins⟩

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress root state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  of_nodes_eq (Detail.freshDataConstructorInstantiation_nodes _ _ _)
    (Detail.freshDataConstructorInstantiation_direct_progress _ _ _)

theorem freshTypes (count : Nat) (state : State) : Progress root state (Detail.freshTypes count state).2 :=
  of_nodes_eq (Detail.freshTypes_nodes _ _) (Detail.freshTypes_direct_progress _ _)

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : Detail.CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress root state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  refine ⟨LocalReadEvents.Progress.recordSelectedCallResult _ _ _ _ _ _ _ _, ?_⟩
  intro _ _ _ origins
  unfold Detail.recordSelectedCallResult
  exact (origins.attachExpressionCoercions _).recordExpression _ _ _ _ _ |>.recordExpression _ _ _ _ _

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : Detail.CandidateAttemptResult) :
    Progress root attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 := recordSelectedCallResult _ _ _ _ _ _ _ _

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : Detail.IndirectApplicationResult) :
    Progress root result.state (Detail.recordIndirectCall source callee arguments result).2 := ⟨LocalReadEvents.Progress.recordIndirectCall _ _ _ _, fun _ _ _ origins => origins.recordExpression _ _ _ _ _⟩

theorem recordBuiltinFunctionCall
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Progress root state result.2 := by
  refine ⟨LocalReadEvents.Progress.recordBuiltinFunctionCall accepted, ?_⟩
  intro _ _ _ origins
  obtain ⟨calleeId, nodes⟩ := Detail.recordBuiltinFunctionCall_success_nodes accepted
  rw [nodes]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using (origins.expression _).expression _


theorem initializedStatement {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult} {expected : Ty}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result)
    (here : CallOccurrence root (.statement (fuel + 1) context statement expected initial result))
    (child : Progress root initial.allocateStatementId.2 receipt.ready) : Progress root initial result.state := by
  refine ⟨LocalReadEvents.inferStatementFuel_origins_progress accepted, ?_⟩
  intro wf allocated reads events
  have childEvents := child.events wf allocated reads events
  rw [receipt.completed]
  exact childEvents.statement _ (Origin.statement receipt here)

end Progress
end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualGeneralizationHeaderEvents
/-! Header events are recovered from the actual returned item sequence,
including the real entry state of each later initializer. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem Detail
variable {root : CallIndex}

theorem inferForItemFuel_event {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (accepted : inferForItemFuel fuel context item state = .ok result)
    (here : CallOccurrence root (.forItem fuel context item state result.1 result.2)) : Item root result.1 := by
  cases fuel with
  | zero => simp [inferForItemFuel, throw] at accepted
  | succ fuel =>
    cases form : item.value with
    | letDecl name annotation initializer =>
      cases initializer with
      | some initializer =>
        obtain ⟨receipt⟩ := LocalHeaderRequirementTiming.of_initialized_accepted form accepted
        exact Item.of_header receipt here
      | none =>
        unfold inferForItemFuel at accepted
        simp only [form, bind, Except.bind] at accepted
        repeat' first | split at accepted
        all_goals simp_all [Item, pure, Pure.pure, Except.pure, throw]
        all_goals subst_vars
        all_goals simp_all [Item]
    | expression expression | assignValue target operator value | assignBitNot target token =>
      unfold inferForItemFuel at accepted
      simp only [form, bind, Except.bind] at accepted
      repeat' first | split at accepted
      all_goals simp_all [Item, pure, Pure.pure, Except.pure, throw]
      all_goals subst_vars
      all_goals simp_all [Item]

theorem inferForItemsFuel_events {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context items state = .ok result)
    (here : CallOccurrence root (.forItems fuel context items state result)) : Items root result.items := by
  induction items generalizing state result with
  | nil =>
    simp only [inferForItemsFuel, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    intro item impossible
    cases impossible
  | cons item items ih =>
    have parentAccepted := accepted
    unfold inferForItemsFuel at accepted
    cases first : inferForItemFuel fuel context item state with
    | error error => simp [first, bind, Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨head, next⟩
      cases tail : inferForItemsFuel fuel context items next with
      | error error => simp [first, tail, bind, Except.bind, Functor.map, Except.map] at accepted
      | ok rest =>
        simp only [first, tail, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        intro value member
        rcases List.mem_cons.mp member with same | remaining
        · cases same
          exact inferForItemFuel_event first (here.child (.forItems_head parentAccepted first))
        · exact ih tail (here.child (.forItems_tail parentAccepted first tail)) value remaining

end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualLocalAllocatorInterval
/-! Local identities use `nextLocal`, independently of the type metavariable
allocator. Actual call prefixes and suffixes preserve its ordering. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

theorem CallIndex.local_next {call : CallIndex} (accepted : call.Accepted) :
    call.initial.nextLocal ≤ call.final.nextLocal := by
  cases call with
  | expression => exact inferExprFuel_nextLocal_le accepted
  | constructorApplication =>
      exact (LocalReadScopeProgress.inferConstructorApplicationFuel_scope_progress accepted).next
  | constructorArguments =>
      exact (LocalReadScopeProgress.inferConstructorArgumentsFuel_scope_progress accepted).next
  | statement => exact inferStatementFuel_nextLocal_le accepted
  | statements => exact inferStatementsFuel_nextLocal_le accepted
  | forItem => exact inferForItemFuel_nextLocal_le accepted
  | forItems => exact inferForItemsFuel_nextLocal_le accepted
  | place => exact (LocalReadScopeProgress.inferPlaceFuel_scope_progress accepted).next
  | assignedValue => exact (LocalReadScopeProgress.inferAssignedValueFuel_scope_progress accepted).next
  | expressions => exact inferExprsFuel_nextLocal_le accepted
  | matchCases => exact inferMatchCasesFuel_nextLocal_le accepted

private theorem allocated_expression {before after : State} {id : ExpressionId}
    (accepted : before.allocateExpressionId = (id, after)) :
    after.nextLocal = before.nextLocal := by
  exact (congrArg (fun result : ExpressionId × State => result.2.nextLocal) accepted).symm

private theorem allocated_statement {before after : State} {id : StatementId}
    (accepted : before.allocateStatementId = (id, after)) :
    after.nextLocal = before.nextLocal := by
  exact (congrArg (fun result : StatementId × State => result.2.nextLocal) accepted).symm

private theorem fresh_local {before after : State} {type : Ty}
    (accepted : before.fresh = (type, after)) :
    after.nextLocal = before.nextLocal := by
  exact (congrArg (fun result : Ty × State => result.2.nextLocal) accepted).symm

private theorem hidden_local {before after : State} {id : Resolved.LocalId}
    (accepted : before.allocateHiddenLocal = (id, after)) :
    before.nextLocal ≤ after.nextLocal := by
  have same := congrArg (fun result : Resolved.LocalId × State => result.2.nextLocal) accepted
  simp only [State.allocateHiddenLocal] at same
  omega

private theorem constructor_local {data : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {before after : State}
    {instantiation : DataConstructorInstantiation}
    (accepted : freshDataConstructorInstantiation data constructor before = (instantiation, after)) :
    before.nextLocal ≤ after.nextLocal := by
  have result := (LocalReadScopeProgress.Progress.freshDataConstructorInstantiation data constructor before).next
  simpa only [accepted] using result

private theorem place_local {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Expr} {before : State} {result : PlaceResolution × State}
    (accepted : inferPlaceFuel fuel context source before = .ok result) :
    before.nextLocal ≤ result.2.nextLocal :=
  (LocalReadScopeProgress.inferPlaceFuel_scope_progress accepted).next

private theorem assigned_local {fuel : Nat} {context : SourceInference.Context}
    {target source : Syntax.Expr} {operator : Syntax.ValueAssignOp} {before : State}
    {result : AssignmentResolution × InferredExpression × State}
    (accepted : inferAssignedValueFuel fuel context target operator source before = .ok result) :
    before.nextLocal ≤ result.2.2.nextLocal :=
  (LocalReadScopeProgress.inferAssignedValueFuel_scope_progress accepted).next

private theorem scrutinee_local {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {before : State}
    {result : InferredExpression × State}
    (accepted : matchScrutinee fuel context span sources before = .ok result) :
    before.nextLocal ≤ result.2.nextLocal := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact inferExprFuel_nextLocal_le accepted
  · cases child : inferExprsFuel fuel context sources before with
    | error error => simp [child, bind, Except.bind] at accepted
    | ok value =>
      have next := inferExprsFuel_nextLocal_le child
      simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact next

private theorem lambda_prefix_local {context : SourceInference.Context}
    {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {parameters : List Ty} {before after : State} {resultType : Ty}
    (prefixFacts : LambdaPrefixFacts context expected annotation parameters before resultType after) :
    before.nextLocal = after.nextLocal := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => rfl
  | noExpectedPartsFresh _ _ allocated => exact (fresh_local allocated).symm
  | expectedPartsAnnotated _ unified => exact (localReadScope_unify_preserves_nextLocal unified).symm
  | expectedPartsInferred _ unified => exact (localReadScope_unify_preserves_nextLocal unified).symm

private theorem assignment_fitting_local {operator : Syntax.ValueAssignOp}
    {before after : State} {type : Ty}
    (accepted : (match operator with | .equal => pure before | _ => unify before type .word) =
      (Except.ok after : Except Error State)) : after.nextLocal = before.nextLocal := by
  cases operator
  all_goals first
  | (cases Except.ok.inj accepted; rfl)
  | exact localReadScope_unify_preserves_nextLocal accepted

private theorem constructor_fitting_local {expected : Option Ty}
    {before after : State} {type : Ty}
    (accepted : (match expected with | none => pure before | some target => unify before type target) =
      (Except.ok after : Except Error State)) : after.nextLocal = before.nextLocal := by
  cases expected
  · cases Except.ok.inj accepted; rfl
  · exact localReadScope_unify_preserves_nextLocal accepted

open Lean Meta Elab Tactic in
elab "collect_local_allocator" : tactic => withMainContext do
  let hypotheses := (← getLCtx).getFVarIds
  for theoremName in [
      ``CallIndex.local_next, ``allocated_expression, ``allocated_statement,
      ``fresh_local, ``hidden_local, ``constructor_local, ``lambda_prefix_local,
      ``assignment_fitting_local, ``constructor_fitting_local,
      ``inferExprFuel_nextLocal_le, ``inferExprsFuel_nextLocal_le,
      ``inferStatementsFuel_nextLocal_le, ``inferStatementFuel_nextLocal_le,
      ``inferForItemsFuel_nextLocal_le, ``inferForItemFuel_nextLocal_le,
      ``inferMatchCasesFuel_nextLocal_le, ``inferMatchPatternFuel_nextLocal_le,
      ``place_local, ``assigned_local, ``scrutinee_local,
      ``localReadScope_bindLambdaParameters_nextLocal_le,
      ``localReadScope_unify_preserves_nextLocal,
      ``localReadScope_withExpected_nextLocal,
      ``localReadScope_recordExpressionWithExpected_nextLocal,
      ``localReadScope_inferUnaryOperator_nextLocal,
      ``localReadScope_inferBinaryOperator_nextLocal,
      ``localReadScope_selectFunctionCandidateFrom_nextLocal,
      ``localReadScope_applyFunctionType_nextLocal] do
    for hypothesis in hypotheses do
      let saved ← saveState
      try
        let proof ← mkAppM theoremName #[mkFVar hypothesis]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved local allocator"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "local_order") proof
        setGoals [next]
      catch _ => saved.restore

theorem ChildStep.local_prefix {parent child : CallIndex} (step : ChildStep parent child) :
    parent.initial.nextLocal ≤ child.initial.nextLocal := by
  cases step
  case assignedValue_value accepted targetAccepted fitting child =>
    split at fitting
    all_goals try (cases Except.ok.inj fitting)
    all_goals collect_local_allocator
    all_goals simp only [CallIndex.initial] at *
    all_goals omega
  case constructorApplication_arguments accepted arity fitting child =>
    split at fitting
    all_goals try (cases Except.ok.inj fitting)
    all_goals collect_local_allocator
    all_goals simp only [CallIndex.initial] at *
    all_goals omega
  all_goals collect_local_allocator
  all_goals simp only [CallIndex.initial, State.restoreLexicalScope_nextLocal] at *
  all_goals omega

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualLocalAllocatorSuffix
/-! The actual suffix of each child call cannot move the local ID allocator backwards. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private theorem exceptThrow_ne_ok {epsilon alpha : Type} (error : epsilon) (value : alpha) :
    (throw error : Except epsilon alpha) ≠ .ok value := by
  intro impossible
  cases impossible

private theorem constructor_arguments_local {fuel : Nat} {context : SourceInference.Context}
    {sources : List Syntax.Expr} {expected : List Ty} {before : State}
    {result : List InferredExpression × State}
    (accepted : inferConstructorArgumentsFuel fuel context sources expected before = .ok result) :
    before.nextLocal ≤ result.2.nextLocal :=
  (LocalReadScopeProgress.inferConstructorArgumentsFuel_scope_progress accepted).next

private theorem builtin_local {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {id : ExpressionId} {expected : Option Ty} {before : State}
    {result : InferredExpression × State}
    (accepted : recordBuiltinFunctionCall source callee name function arguments id expected before = .ok result) :
    before.nextLocal ≤ result.2.nextLocal :=
  (LocalReadScopeProgress.Progress.recordBuiltinFunctionCall accepted).next

private theorem attached_local (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).nextLocal = state.nextLocal := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      exact ih _

open Lean Meta Elab Tactic in
elab "collect_suffix_allocator" : tactic => withMainContext do
  evalTactic (← `(tactic| collect_local_allocator))
  let hypotheses := (← getLCtx).getFVarIds
  for theoremName in [``constructor_arguments_local, ``builtin_local] do
    for hypothesis in hypotheses do
      let saved ← saveState
      try
        let proof ← mkAppM theoremName #[mkFVar hypothesis]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved local suffix"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "local_suffix_order") proof
        setGoals [next]
      catch _ => saved.restore

private theorem lambdaPrefix_unique
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial : State}
    {leftType rightType : Ty} {leftState rightState : State}
    (left : LambdaPrefixFacts context expected annotation types initial leftType leftState)
    (right : LambdaPrefixFacts context expected annotation types initial rightType rightState) :
    leftType = rightType ∧ leftState = rightState := by
  cases left <;> cases right <;> simp_all

private theorem match_scrutinee_local_suffix
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState : State} {result : StatementResult}
    (accepted : inferStatementFuel (fuel+1) context source expectedReturn initial = .ok result)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState)) :
    scrutineeState.nextLocal ≤ result.state.nextLocal := by
  have completion := matchCompletion_accepted form allocation scrutineeAccepted
    (show scrutineeState.allocateHiddenLocal =
      (scrutineeState.allocateHiddenLocal.1, scrutineeState.allocateHiddenLocal.2) from rfl) accepted
  unfold matchCompletion at completion
  simp only [bind, Except.bind] at completion
  repeat' first | split at completion
  all_goals try cases completion
  all_goals try simp_all only [exceptPure_eq_ok, exceptThrow_ne_ok]
  all_goals collect_suffix_allocator
  all_goals try simp_all only [Except.ok.injEq, Prod.mk.injEq]
  all_goals try subst_vars
  all_goals simp_all only [State.recordNode, State.allocateHiddenLocal, State.restoreLexicalScope]
  all_goals omega

/-- The repeated suffix inversion only inspects the accepted parent run and
uses previously proved allocator monotonicity for its remaining recursive calls. -/
macro "finish_local_suffix" accepted:ident : tactic => `(tactic|
  first |
    all_goals try simp_all only [bind, Except.bind, pure, Pure.pure, Except.pure]
    all_goals repeat' first | split at $accepted:ident
    all_goals try cases $accepted:ident
    all_goals try simp_all only [exceptPure_eq_ok, exceptThrow_ne_ok]
    all_goals collect_suffix_allocator
    all_goals try simp_all only [Except.ok.injEq, Prod.mk.injEq]
    all_goals try subst_vars
    all_goals try simp_all only [CallIndex.final, State.allocateExpressionId_nextLocal,
      State.allocateStatementId_nextLocal, attached_local]
    all_goals try simp_all only [CallIndex.final, attached_local, State.allocateBinder,
      State.allocateHiddenLocal, State.allocateExpressionId, State.allocateStatementId,
      State.restoreLexicalScope, State.recordNode, State.fresh,
      State.addRequirementWithId, State.addRequirementsWithIds,
      recordExpression, recordSelectedCall, recordSelectedCallResult, recordIndirectCall]
    all_goals omega)

theorem ChildStep.local_suffix {parent child : CallIndex} (step : ChildStep parent child) :
    child.final.nextLocal ≤ parent.final.nextLocal := by
  cases step with
  | expression_group accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_tuple accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expressions_head accepted head =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprsFuel at accepted
      finish_local_suffix accepted
  | expressions_tail accepted head tail =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprsFuel at accepted
      finish_local_suffix accepted
  | statements_head accepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementsFuel at accepted
      finish_local_suffix accepted
  | statements_tail accepted nonempty headAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementsFuel at accepted
      finish_local_suffix accepted
  | statement_initializer accepted form allocation annotation child =>
      cases annotation
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_return accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_expression accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_block accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_if_condition accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_if_then accepted form allocation conditionAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_assignment accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_bitnot accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_while_condition accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_while_body accepted form allocation conditionAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_for_initializer accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_for_condition accepted form allocation initializerAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_for_body accepted form allocation initializerAccepted conditionAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | forItems_head accepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferForItemsFuel at accepted
      finish_local_suffix accepted
  | forItems_tail accepted headAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferForItemsFuel at accepted
      finish_local_suffix accepted
  | forItem_initializer accepted form annotation child =>
      cases annotation
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferForItemFuel at accepted
      finish_local_suffix accepted
  | forItem_expression accepted form child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferForItemFuel at accepted
      finish_local_suffix accepted
  | forItem_assignment accepted form child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferForItemFuel at accepted
      finish_local_suffix accepted
  | forItem_bitnot accepted form child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferForItemFuel at accepted
      finish_local_suffix accepted
  | assignedValue_place accepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals try simp only [CallIndex.Accepted, inferAssignedValueFuel] at accepted
      finish_local_suffix accepted
  | @assignedValue_value fuel context target value operator initial final targetState
      assignment inferred place fitted childFinal childValue accepted targetAccepted fitting child =>
      cases operator
      all_goals simp only [CallIndex.Accepted, assignmentExpected] at *
      all_goals try (simp only [pure, Pure.pure, Except.pure, Except.ok.injEq] at fitting; subst fitted)
      all_goals change inferAssignedValueFuel fuel context target _ value initial = .ok _ at accepted
      all_goals unfold inferAssignedValueFuel at accepted
      all_goals simp_all only [bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq]
      all_goals simp_all only [CallIndex.final]
      all_goals exact Nat.le_refl _
  | place_group accepted form child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferPlaceFuel at accepted
      finish_local_suffix accepted
  | place_index_base accepted form child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferPlaceFuel at accepted
      finish_local_suffix accepted
  | place_index_key accepted form baseAccepted keyFresh valueFresh fitting child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferPlaceFuel at accepted
      finish_local_suffix accepted
  | constructorApplication_arguments accepted arity fitting child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals simp only [CallIndex.Accepted, inferConstructorApplicationFuel] at accepted
      finish_local_suffix accepted
  | constructorArguments_head accepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferConstructorArgumentsFuel at accepted
      finish_local_suffix accepted
  | constructorArguments_tail accepted headAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferConstructorArgumentsFuel at accepted
      finish_local_suffix accepted
  | expression_unary accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_binary_left accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_binary_right accepted form allocation leftAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_conditional_condition accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_conditional_then accepted form allocation conditionAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_conditional_else accepted form allocation conditionAccepted thenAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_lambda_body accepted form allocation parametersAccepted prefixFacts child =>
      obtain ⟨parameters, types, parameterState, resultType, resultState, bodyResult,
        unifiedState, restoredState, parametersRun, actualPrefix, bodyRun, unified, restored, recorded⟩ :=
        inferExprFuel_success_lambda_facts form allocation accepted
      cases Except.ok.inj (parametersRun.symm.trans parametersAccepted)
      obtain ⟨sameType, sameState⟩ := lambdaPrefix_unique actualPrefix prefixFacts
      cases sameType
      cases sameState
      cases Except.ok.inj (bodyRun.symm.trans child)
      have after := localReadScope_unify_preserves_nextLocal unified
      have finish := localReadScope_recordExpressionWithExpected_nextLocal recorded
      simp only [restored, State.restoreLexicalScope_nextLocal] at finish
      simpa only [CallIndex.final] using Nat.le_of_eq (finish.trans after).symm
  | expression_index_base accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_index_key accepted form allocation baseAccepted keyFresh valueFresh fitting child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_call_constructor accepted form allocation selected fresh child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_call_arguments accepted form allocation nonconstructor child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | @expression_call_callee fuel context source expected initial allocated final id value
      callee arguments values argumentState childFinal inferred
      accepted form allocation nonconstructor argumentsAccepted indirect child =>
      obtain ⟨application, applicationRun, recorded⟩ :=
        indirectCall_actual_suffix form allocation nonconstructor argumentsAccepted indirect child accepted
      have after := localReadScope_applyFunctionType_nextLocal applicationRun
      have finish := (LocalReadScopeProgress.Progress.recordIndirectCall source inferred values application).next
      rw [recorded] at finish
      exact Nat.le_trans (Nat.le_of_eq after.symm) finish
  | expression_contextual_constructor accepted form allocation selected child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_field_constructor accepted form allocation selected fresh child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | matchCases_body accepted patternAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferMatchCasesFuel at accepted
      finish_local_suffix accepted
  | matchCases_tail accepted patternAccepted bodyAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferMatchCasesFuel at accepted
      finish_local_suffix accepted
  | statement_match_single accepted form allocation single child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | @statement_match_many fuel context source expectedReturn initial allocated id result
      scrutinees arms values childFinal accepted form allocation multiple child =>
      simp only [CallIndex.Accepted] at accepted child
      let tuple : InferredExpression := ⟨childFinal.allocateExpressionId.1, Ty.productMany (values.map (·.type))⟩
      let tupleState := childFinal.allocateExpressionId.2.recordNode (.expression {
        id := tuple.id, span := source.span, type := tuple.type, form := .tuple (values.map (·.id)) })
      have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (tuple, tupleState) := by
        unfold matchScrutinee
        split
        · rename_i sourceEq
          exact False.elim (multiple _ sourceEq)
        · simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure]
          rfl
      have after := match_scrutinee_local_suffix accepted form allocation scrutineeAccepted
      have same : tupleState.nextLocal = childFinal.nextLocal := rfl
      simpa only [same, CallIndex.final] using after
  | statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child =>
      have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
      simp only [CallIndex.Accepted] at child
      unfold matchCompletion at completion
      simp only [child, bind, Except.bind] at completion
      repeat' first | split at completion
      all_goals try cases completion
      all_goals try simp_all only [exceptPure_eq_ok, exceptThrow_ne_ok]
      all_goals collect_suffix_allocator
      all_goals try simp_all only [Except.ok.injEq, Prod.mk.injEq]
      all_goals try subst_vars
      all_goals simp_all only [CallIndex.final, State.recordNode, State.restoreLexicalScope]
      all_goals omega
  | statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child =>
      have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
      simp only [CallIndex.Accepted] at child
      unfold matchCompletion at completion
      simp only [casesAccepted, default, child, bind, Except.bind, pure, Pure.pure, Except.pure] at completion
      split at completion
      · contradiction
      · cases Except.ok.inj completion
        exact Nat.le_refl _
/-- Every actual descendant occupies an interval inside its accepted root call. -/
theorem CallOccurrence.local_interval {root call : CallIndex}
    (here : CallOccurrence root call) :
    root.initial.nextLocal ≤ call.initial.nextLocal ∧
      call.final.nextLocal ≤ root.final.nextLocal := by
  induction here with
  | root _ => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | child _ step ih =>
      exact ⟨Nat.le_trans ih.1 step.local_prefix, Nat.le_trans step.local_suffix ih.2⟩

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualReadCalls
/-! A retained local reference keeps the exact operational lookup and its
executed path from the same root call. Expression coercions may update the
record's type and requirements, while its occurrence and resolution stay fixed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualLocalRead
open Frontend SourceInference TypeSystem Detail

/-- The precise call carried by the existing operational lookup receipt. -/
def lookupCall (lookup : LocalReadEvents.Lookup) : CallIndex :=
  .expression (lookup.fuel + 1) lookup.context lookup.expression lookup.expected
    lookup.initial lookup.result.1 lookup.result.2

def Origin (root : CallIndex) (node : ExpressionNode) : Prop :=
  ∃ lookup : LocalReadEvents.Lookup,
    node.id = lookup.id ∧
    node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
    CallOccurrence root (lookupCall lookup)

def Origins (root : CallIndex) (nodes : List Node) : Prop :=
  ∀ node, .expression node ∈ nodes → ∀ name binder,
    node.form = .reference name (.local binder) → Origin root node

variable {root : CallIndex}

theorem Origins.empty : Origins root [] := by intro _ impossible; cases impossible

theorem Origin.same_occurrence {before after : ExpressionNode}
    (origin : Origin root before) (id : after.id = before.id) (form : after.form = before.form) :
    Origin root after := by
  obtain ⟨lookup, sameId, sameForm, here⟩ := origin
  exact ⟨lookup, id.trans sameId, form.trans sameForm, here⟩

theorem Origins.statement {nodes : List Node} (origins : Origins root nodes) (node : StatementNode) :
    Origins root (nodes ++ [.statement node]) := by
  intro expression member name binder form
  rcases List.mem_append.mp member with old | fresh
  · exact origins expression old name binder form
  · cases List.mem_singleton.mp fresh

theorem Origins.expression {nodes : List Node} (origins : Origins root nodes) (node : ExpressionNode)
    (origin : ∀ name binder, node.form = .reference name (.local binder) → Origin root node) :
    Origins root (nodes ++ [.expression node]) := by
  intro expression member name binder form
  rcases List.mem_append.mp member with old | fresh
  · exact origins expression old name binder form
  · cases List.mem_singleton.mp fresh
    exact origin name binder form

theorem Origins.nonlocalExpression {nodes : List Node} (origins : Origins root nodes) (node : ExpressionNode)
    (nonlocal : LocalReadEvents.Nonlocal node.form) : Origins root (nodes ++ [.expression node]) :=
  origins.expression node (fun name binder form => (nonlocal name binder form).elim)

theorem Origins.modifyStatementNode {state : State} (origins : Origins root state.nodes)
    (id : StatementId) (modify : StatementNode → StatementNode) :
    Origins root (state.modifyStatementNode id modify).nodes := by
  intro expression present name binder form
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression original => cases same; exact origins _ member name binder form
  | statement original => simp only at same; split at same <;> cases same

theorem Origins.modifyExpressionNode {state : State} (origins : Origins root state.nodes)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode)
    (forms : ∀ node, (modify node).form = node.form) :
    Origins root (state.modifyExpressionNode id modify).nodes := by
  intro expression present name binder form
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | statement original => cases same
  | expression original =>
    simp only at same
    split at same <;> cases same
    · rename_i sameId
      exact (origins _ member name binder ((forms _).symm.trans form)).same_occurrence sameId.symm (forms _)
    · exact origins _ member name binder form

theorem Origins.attachExpressionCoercions {state : State} (origins : Origins root state.nodes)
    (entries : List Detail.ExpressionCoercions) :
    Origins root (Detail.attachExpressionCoercions state entries).nodes := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact origins
  | cons entry rest ih => exact ih (origins.modifyExpressionNode _ _ (fun _ => rfl))

theorem Origins.recordExpression {state : State} (origins : Origins root state.nodes)
    (source : Syntax.Expr) (expression : InferredExpression) (form : ExpressionForm)
    (requirements : List RequirementId) (coercions : List CoercionStep) (start : Option Nat := none)
    (nonlocal : LocalReadEvents.Nonlocal form) :
    Origins root (Detail.recordExpression source expression form requirements coercions state start).2.nodes :=
  origins.nonlocalExpression _ nonlocal

theorem Origins.recordExpressionWithExpected {state : State} (origins : Origins root state.nodes)
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : Origins root result.2.nodes := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  have same := (Detail.withExpected_occurrenceState_eq fit).1
  exact (show Origins root fitted.state.nodes from same.symm ▸ origins).nonlocalExpression _ nonlocal

/-- Recording the successful local branch preserves the issuing call itself,
rather than replacing it by an arbitrary accepted lookup with the same ID. -/
theorem Lookup.record_origins (lookup : LocalReadEvents.Lookup)
    (here : CallOccurrence root (lookupCall lookup))
    (origins : Origins root lookup.initial.nodes) : Origins root lookup.result.2.nodes := by
  have allocated : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
    (congrArg Prod.snd lookup.allocation).symm
  have batchNodes : lookup.batch.2.nodes = lookup.initial.nodes := by
    simp only [LocalReadEvents.Lookup.batch, State.addRequirementsWithIds_nodes,
      LocalReadEvents.Lookup.advanced, allocated, State.allocateExpressionId_nodes]
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record lookup.recorded
  rw [recorded]
  have same : fitted.state.nodes = lookup.initial.nodes :=
    (Detail.withExpected_occurrenceState_eq fit).1.trans batchNodes
  apply (show Origins root fitted.state.nodes from same.symm ▸ origins).expression
  intro _ _ _
  exact ⟨lookup, Detail.withExpected_success_expression_id fit, rfl, here⟩

/-- Guarded lookup proves membership of the complete binder at its actual
issuing state; it does not merely recover a matching local ID. -/
theorem Origin.active {node : ExpressionNode} (origin : Origin root node) :
    ∃ lookup : LocalReadEvents.Lookup,
      node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      CallOccurrence root (lookupCall lookup) ∧
      lookup.binder ∈ lookup.initial.localBinders := by
  obtain ⟨lookup, sameId, sameForm, here⟩ := origin
  refine ⟨lookup, sameId, sameForm, here, ?_⟩
  have member := (State.lookupBinder?_eq_some_facts lookup.found).1
  have allocated : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
    (congrArg Prod.snd lookup.allocation).symm
  rw [allocated] at member
  exact member

end Solcore.SourceSemantics.SourceInferenceExecution.ActualLocalRead
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualReadProgress
/-! The existing actual-generalization traversal also retains each local-read
call. Its old progress contract remains a projection of this stronger result. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem Detail
open State (DirectRequirementsProgress)
variable {root : CallIndex}

structure ReadProgressFields (root : CallIndex)
    (beforeNodes : List Node) (beforeRows : List Requirement) (beforeNext : Nat) (beforeDirect : List RequirementId)
    (afterNodes : List Node) (afterRows : List Requirement) (afterNext : Nat) (afterDirect : List RequirementId) : Prop where
  progress : ProgressFields root beforeNodes beforeRows beforeNext beforeDirect afterNodes afterRows afterNext afterDirect
  calls : beforeRows.map (fun requirement => requirement.id.index) = List.range beforeNext →
    beforeDirect ⊆ beforeRows.map Requirement.id →
    ActualLocalRead.Origins root beforeNodes → ActualLocalRead.Origins root afterNodes

abbrev ReadProgress (root : CallIndex) (before after : State) : Prop :=
  ReadProgressFields root before.nodes before.requirements before.nextRequirement before.directCallRequirements
    after.nodes after.requirements after.nextRequirement after.directCallRequirements

namespace ReadProgressFields
variable {bn mn an : List Node} {br mr ar : List Requirement} {bi mi ai : Nat} {bd md ad : List RequirementId}

abbrev reads (value : ReadProgressFields root bn br bi bd an ar ai ad) := value.progress.reads
abbrev events (value : ReadProgressFields root bn br bi bd an ar ai ad) := value.progress.events

theorem trans (first : ReadProgressFields root bn br bi bd mn mr mi md)
    (second : ReadProgressFields root mn mr mi md an ar ai ad) :
    ReadProgressFields root bn br bi bd an ar ai ad :=
  ⟨first.progress.trans second.progress, fun wf direct calls =>
    second.calls (first.reads.ledger.wellFormed wf) (first.reads.ledger.allocated wf direct)
      (first.calls wf direct calls)⟩

theorem statement (nodes : List Node) (rows : List Requirement)
    (next : Nat) (direct : List RequirementId) (node : StatementNode) (event : Statement root node) :
    ReadProgressFields root nodes rows next direct (nodes ++ [.statement node]) rows next direct :=
  ⟨ProgressFields.statement _ _ _ _ _ event, fun _ _ calls => calls.statement node⟩

theorem expression (nodes : List Node) (rows : List Requirement)
    (next : Nat) (direct : List RequirementId) (node : ExpressionNode)
    (nonlocal : LocalReadEvents.Nonlocal node.form) :
    ReadProgressFields root nodes rows next direct (nodes ++ [.expression node]) rows next direct :=
  ⟨ProgressFields.expression _ _ _ _ _ nonlocal, fun _ _ calls => calls.nonlocalExpression node nonlocal⟩
end ReadProgressFields

namespace ReadProgress

theorem refl (state : State) : ReadProgress root state state :=
  ⟨Progress.refl state, fun _ _ calls => calls⟩

theorem trans {before middle after : State} (first : ReadProgress root before middle)
    (second : ReadProgress root middle after) : ReadProgress root before after := ReadProgressFields.trans first second

theorem of_nodes_eq {before after : State} (same : after.nodes = before.nodes)
    (ledger : DirectRequirementsProgress before after) : ReadProgress root before after :=
  ⟨Progress.of_nodes_eq same ledger, fun _ _ calls => same.symm ▸ calls⟩

theorem recordStatement (state : State) (node : StatementNode) (event : Statement root node) :
    ReadProgress root state (state.recordNode (.statement node)) :=
  ⟨Progress.recordStatement state node event, fun _ _ calls => calls.statement node⟩

theorem modifyStatementNode (state : State) (id : StatementId) (modify : StatementNode → StatementNode)
    (forms : ∀ node, (modify node).form = node.form) : ReadProgress root state (state.modifyStatementNode id modify) :=
  ⟨Progress.modifyStatementNode state id modify forms, fun _ _ calls => calls.modifyStatementNode id modify⟩

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    ReadProgress root state (state.addRequirementWithId predicate).2 :=
  of_nodes_eq rfl (.addRequirementWithId _ _)

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    ReadProgress root state (state.addRequirementsWithIds predicates).2 :=
  of_nodes_eq (State.addRequirementsWithIds_nodes _ _) (.addRequirementsWithIds _ _)

theorem recordExpressionWithExpected
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : ReadProgress root state result.2 :=
  by
  exact ⟨Progress.recordExpressionWithExpected accepted nonlocal, fun _ _ calls => calls.recordExpressionWithExpected accepted nonlocal⟩

theorem unify {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : ReadProgress root state next :=
  ⟨Progress.unify accepted, fun _ _ calls => (unify_occurrenceState_eq accepted).1.symm ▸ calls⟩

theorem withExpected
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : withExpected context state actual expected = .ok result) :
    ReadProgress root state result.state :=
  ⟨Progress.withExpected accepted, fun _ _ calls => (withExpected_occurrenceState_eq accepted).1.symm ▸ calls⟩

theorem selectFunctionCandidateFrom
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    ReadProgress root state result.state :=
  ⟨Progress.selectFunctionCandidateFrom accepted, fun _ _ calls => (selectFunctionCandidateFrom_occurrenceState_eq accepted).1.symm ▸ calls⟩

theorem inferUnaryOperator
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    ReadProgress root state result.state :=
  ⟨Progress.inferUnaryOperator success, fun _ _ calls => (inferUnaryOperator_occurrenceState_eq success).1.symm ▸ calls⟩

theorem inferBinaryOperator
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    ReadProgress root state result.state :=
  ⟨Progress.inferBinaryOperator success, fun _ _ calls => (inferBinaryOperator_occurrenceState_eq success).1.symm ▸ calls⟩

theorem applyFunctionType
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    ReadProgress root state result.state :=
  ⟨Progress.applyFunctionType success, fun _ _ calls => (applyFunctionType_occurrenceState_eq success).1.symm ▸ calls⟩

theorem bindLambdaParameters
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    ReadProgress root state result.2.2 :=
  ⟨Progress.bindLambdaParameters success, fun _ _ calls => (bindLambdaParameters_occurrenceState_eq success).1.symm ▸ calls⟩

theorem inferMatchPatternFuel
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    ReadProgress root state result.2 :=
  ⟨Progress.inferMatchPatternFuel success, fun _ _ calls => (inferMatchPatternFuel_occurrenceState_eq success).1.symm ▸ calls⟩

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    ReadProgress root state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  of_nodes_eq (Detail.freshDataConstructorInstantiation_nodes _ _ _) (Detail.freshDataConstructorInstantiation_direct_progress _ _ _)

theorem freshTypes (count : Nat) (state : State) : ReadProgress root state (Detail.freshTypes count state).2 :=
  of_nodes_eq (Detail.freshTypes_nodes _ _) (Detail.freshTypes_direct_progress _ _)

theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result)
    (here : CallOccurrence root (.expression (fuel + 1) context expression expected initial result.1 result.2)) :
    ReadProgress root initial result.2 := by
  refine ⟨Progress.localIdentifier form allocation found accepted, ?_⟩
  intro wf direct calls
  let lookup : LocalReadEvents.Lookup := ⟨fuel, context, expression, expected, initial, allocated, id,
    name, binder, result, form, allocation, found, accepted, wf, direct⟩
  exact ActualLocalRead.Lookup.record_origins lookup here calls

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : Detail.CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    ReadProgress root state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2  := by
  refine ⟨Progress.recordSelectedCallResult _ _ _ _ _ _ _ _, ?_⟩
  intro _ _ calls
  unfold Detail.recordSelectedCallResult
  exact (calls.attachExpressionCoercions _).recordExpression _ _ _ _ _ none
    (by intro _ _ impossible; cases impossible) |>.recordExpression _ _ _ _ _ none
      (by intro _ _ impossible; cases impossible)

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : Detail.CandidateAttemptResult) :
    ReadProgress root attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult _ _ _ _ _ _ _ _

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : Detail.IndirectApplicationResult) :
    ReadProgress root result.state (Detail.recordIndirectCall source callee arguments result).2  :=
  ⟨Progress.recordIndirectCall _ _ _ _, fun _ _ calls => calls.recordExpression _ _ _ _ _ none
    (by intro _ _ impossible; cases impossible)⟩

theorem recordBuiltinFunctionCall
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    ReadProgress root state result.2  := by
  refine ⟨Progress.recordBuiltinFunctionCall accepted, ?_⟩
  intro _ _ calls
  obtain ⟨calleeId, nodes⟩ := Detail.recordBuiltinFunctionCall_success_nodes accepted
  rw [nodes]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    (calls.nonlocalExpression _ (by intro _ _ impossible; cases impossible)).nonlocalExpression _
      (by intro _ _ impossible; cases impossible)

theorem initializedStatement {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult} {expected : Ty}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result)
    (here : CallOccurrence root (.statement (fuel + 1) context statement expected initial result))
    (child : ReadProgress root initial.allocateStatementId.2 receipt.ready) : ReadProgress root initial result.state  := by
  refine ⟨Progress.initializedStatement receipt accepted here child.progress, ?_⟩
  intro wf direct calls
  have childCalls := child.calls wf direct calls
  rw [receipt.completed]
  exact childCalls.statement _

end ReadProgress
end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceRelativeReadCalls
/-! A retained local reference either continues an input occurrence or keeps
its exact issuing lookup from this inference run. Coercion updates preserve
the occurrence and local target in both cases. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.RelativeLocalRead
open Frontend SourceInference TypeSystem Detail

open ActualLocalRead (lookupCall)

/-- A read either continues an input record or was issued during this run. -/
def Origin (root : CallIndex) (base : List Node) (node : ExpressionNode) : Prop :=
  (∃ previous : ExpressionNode, .expression previous ∈ base ∧
    node.id = previous.id ∧ node.form = previous.form) ∨ ActualLocalRead.Origin root node

def Origins (root : CallIndex) (base nodes : List Node) : Prop :=
  ∀ node, .expression node ∈ nodes → ∀ name binder,
    node.form = .reference name (.local binder) → Origin root base node

variable {root : CallIndex} {base : List Node}

theorem Origins.empty : Origins root base [] := by intro _ impossible; cases impossible

theorem Origin.same_occurrence {before after : ExpressionNode}
    (origin : Origin root base before) (id : after.id = before.id) (form : after.form = before.form) :
    Origin root base after := by
  rcases origin with ⟨previous, member, sameId, sameForm⟩ | current
  · exact .inl ⟨previous, member, id.trans sameId, form.trans sameForm⟩
  · exact .inr (current.same_occurrence id form)

theorem Origins.statement {nodes : List Node} (origins : Origins root base nodes) (node : StatementNode) :
    Origins root base (nodes ++ [.statement node]) := by
  intro expression member name binder form
  rcases List.mem_append.mp member with old | fresh
  · exact origins expression old name binder form
  · cases List.mem_singleton.mp fresh

theorem Origins.expression {nodes : List Node} (origins : Origins root base nodes) (node : ExpressionNode)
    (origin : ∀ name binder, node.form = .reference name (.local binder) → Origin root base node) :
    Origins root base (nodes ++ [.expression node]) := by
  intro expression member name binder form
  rcases List.mem_append.mp member with old | fresh
  · exact origins expression old name binder form
  · cases List.mem_singleton.mp fresh
    exact origin name binder form

theorem Origins.nonlocalExpression {nodes : List Node} (origins : Origins root base nodes) (node : ExpressionNode)
    (nonlocal : LocalReadEvents.Nonlocal node.form) : Origins root base (nodes ++ [.expression node]) :=
  origins.expression node (fun name binder form => (nonlocal name binder form).elim)

theorem Origins.modifyStatementNode {state : State} (origins : Origins root base state.nodes)
    (id : StatementId) (modify : StatementNode → StatementNode) :
    Origins root base (state.modifyStatementNode id modify).nodes := by
  intro expression present name binder form
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression original => cases same; exact origins _ member name binder form
  | statement original => simp only at same; split at same <;> cases same

theorem Origins.modifyExpressionNode {state : State} (origins : Origins root base state.nodes)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode)
    (forms : ∀ node, (modify node).form = node.form) :
    Origins root base (state.modifyExpressionNode id modify).nodes := by
  intro expression present name binder form
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | statement original => cases same
  | expression original =>
    simp only at same
    split at same <;> cases same
    · rename_i sameId
      exact (origins _ member name binder ((forms _).symm.trans form)).same_occurrence sameId.symm (forms _)
    · exact origins _ member name binder form

theorem Origins.attachExpressionCoercions {state : State} (origins : Origins root base state.nodes)
    (entries : List Detail.ExpressionCoercions) :
    Origins root base (Detail.attachExpressionCoercions state entries).nodes := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact origins
  | cons entry rest ih => exact ih (origins.modifyExpressionNode _ _ (fun _ => rfl))

theorem Origins.recordExpression {state : State} (origins : Origins root base state.nodes)
    (source : Syntax.Expr) (expression : InferredExpression) (form : ExpressionForm)
    (requirements : List RequirementId) (coercions : List CoercionStep) (start : Option Nat := none)
    (nonlocal : LocalReadEvents.Nonlocal form) :
    Origins root base (Detail.recordExpression source expression form requirements coercions state start).2.nodes :=
  origins.nonlocalExpression _ nonlocal

theorem Origins.recordExpressionWithExpected {state : State} (origins : Origins root base state.nodes)
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : Origins root base result.2.nodes := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  have same := (Detail.withExpected_occurrenceState_eq fit).1
  exact (show Origins root base fitted.state.nodes from same.symm ▸ origins).nonlocalExpression _ nonlocal

/-- Recording the successful local branch preserves the issuing call itself,
rather than replacing it by an arbitrary accepted lookup with the same ID. -/
theorem Lookup.record_origins (lookup : LocalReadEvents.Lookup)
    (here : CallOccurrence root (lookupCall lookup))
    (origins : Origins root base lookup.initial.nodes) : Origins root base lookup.result.2.nodes := by
  have allocated : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
    (congrArg Prod.snd lookup.allocation).symm
  have batchNodes : lookup.batch.2.nodes = lookup.initial.nodes := by
    simp only [LocalReadEvents.Lookup.batch, State.addRequirementsWithIds_nodes,
      LocalReadEvents.Lookup.advanced, allocated, State.allocateExpressionId_nodes]
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record lookup.recorded
  rw [recorded]
  have same : fitted.state.nodes = lookup.initial.nodes :=
    (Detail.withExpected_occurrenceState_eq fit).1.trans batchNodes
  apply (show Origins root base fitted.state.nodes from same.symm ▸ origins).expression
  intro _ _ _
  exact .inr ⟨lookup, Detail.withExpected_success_expression_id fit, rfl, here⟩

/-- Input reads satisfy the relative invariant without any operational origin. -/
theorem Origins.initial (base : List Node) : Origins root base base := by
  intro node member _ _ _
  exact .inl ⟨node, member, rfl, rfl⟩

/-- The earlier absolute API is recovered by resolving the input alternative. -/
theorem Origins.toActual {nodes : List Node} (relative : Origins root base nodes)
    (previous : ActualLocalRead.Origins root base) : ActualLocalRead.Origins root nodes := by
  intro node member name binder form
  rcases relative node member name binder form with old | current
  · obtain ⟨original, present, sameId, sameForm⟩ := old
    exact (previous original present name binder (sameForm.symm.trans form)).same_occurrence sameId sameForm
  · exact current

end Solcore.SourceSemantics.SourceInferenceExecution.RelativeLocalRead
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceRelativeReadProgress
/-! Relative read provenance shares the existing actual-generalization
traversal. Earlier reads need no issuing call inside the current segment;
the established exact-call contract remains available as a projection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem Detail
open State (DirectRequirementsProgress)
variable {root : CallIndex}

structure RelativeReadProgressFields (root : CallIndex)
    (beforeNodes : List Node) (beforeRows : List Requirement) (beforeNext : Nat) (beforeDirect : List RequirementId)
    (afterNodes : List Node) (afterRows : List Requirement) (afterNext : Nat) (afterDirect : List RequirementId) : Prop where
  progress : ProgressFields root beforeNodes beforeRows beforeNext beforeDirect afterNodes afterRows afterNext afterDirect
  calls : ∀ {base : List Node}, beforeRows.map (fun requirement => requirement.id.index) = List.range beforeNext →
    beforeDirect ⊆ beforeRows.map Requirement.id →
    RelativeLocalRead.Origins root base beforeNodes → RelativeLocalRead.Origins root base afterNodes

abbrev RelativeReadProgress (root : CallIndex) (before after : State) : Prop :=
  RelativeReadProgressFields root before.nodes before.requirements before.nextRequirement before.directCallRequirements
    after.nodes after.requirements after.nextRequirement after.directCallRequirements

namespace RelativeReadProgressFields
variable {bn mn an : List Node} {br mr ar : List Requirement} {bi mi ai : Nat} {bd md ad : List RequirementId}

/-- Preserve the previously published exact-call contract as a projection. -/
theorem readProgress (value : RelativeReadProgressFields root bn br bi bd an ar ai ad) :
    ReadProgressFields root bn br bi bd an ar ai ad :=
  ⟨value.progress, fun wellFormed allocated origins =>
    (value.calls wellFormed allocated (RelativeLocalRead.Origins.initial bn)).toActual origins⟩

abbrev reads (value : RelativeReadProgressFields root bn br bi bd an ar ai ad) := value.progress.reads
abbrev events (value : RelativeReadProgressFields root bn br bi bd an ar ai ad) := value.progress.events

theorem trans (first : RelativeReadProgressFields root bn br bi bd mn mr mi md)
    (second : RelativeReadProgressFields root mn mr mi md an ar ai ad) :
    RelativeReadProgressFields root bn br bi bd an ar ai ad :=
  ⟨first.progress.trans second.progress, fun {_} wf direct calls =>
    second.calls (first.reads.ledger.wellFormed wf) (first.reads.ledger.allocated wf direct)
      (first.calls wf direct calls)⟩

theorem statement (nodes : List Node) (rows : List Requirement)
    (next : Nat) (direct : List RequirementId) (node : StatementNode) (event : Statement root node) :
    RelativeReadProgressFields root nodes rows next direct (nodes ++ [.statement node]) rows next direct :=
  ⟨ProgressFields.statement _ _ _ _ _ event, fun {_} _ _ calls => calls.statement node⟩

theorem expression (nodes : List Node) (rows : List Requirement)
    (next : Nat) (direct : List RequirementId) (node : ExpressionNode)
    (nonlocal : LocalReadEvents.Nonlocal node.form) :
    RelativeReadProgressFields root nodes rows next direct (nodes ++ [.expression node]) rows next direct :=
  ⟨ProgressFields.expression _ _ _ _ _ nonlocal, fun {_} _ _ calls => calls.nonlocalExpression node nonlocal⟩
end RelativeReadProgressFields

namespace RelativeReadProgress

theorem refl (state : State) : RelativeReadProgress root state state :=
  ⟨Progress.refl state, fun {_} _ _ calls => calls⟩

theorem trans {before middle after : State} (first : RelativeReadProgress root before middle)
    (second : RelativeReadProgress root middle after) : RelativeReadProgress root before after := RelativeReadProgressFields.trans first second

theorem of_nodes_eq {before after : State} (same : after.nodes = before.nodes)
    (ledger : DirectRequirementsProgress before after) : RelativeReadProgress root before after :=
  ⟨Progress.of_nodes_eq same ledger, fun {_} _ _ calls => same.symm ▸ calls⟩

theorem recordStatement (state : State) (node : StatementNode) (event : Statement root node) :
    RelativeReadProgress root state (state.recordNode (.statement node)) :=
  ⟨Progress.recordStatement state node event, fun {_} _ _ calls => calls.statement node⟩

theorem modifyStatementNode (state : State) (id : StatementId) (modify : StatementNode → StatementNode)
    (forms : ∀ node, (modify node).form = node.form) : RelativeReadProgress root state (state.modifyStatementNode id modify) :=
  ⟨Progress.modifyStatementNode state id modify forms, fun {_} _ _ calls => calls.modifyStatementNode id modify⟩

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    RelativeReadProgress root state (state.addRequirementWithId predicate).2 :=
  of_nodes_eq rfl (.addRequirementWithId _ _)

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    RelativeReadProgress root state (state.addRequirementsWithIds predicates).2 :=
  of_nodes_eq (State.addRequirementsWithIds_nodes _ _) (.addRequirementsWithIds _ _)

theorem recordExpressionWithExpected
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : RelativeReadProgress root state result.2 :=
  by
  exact ⟨Progress.recordExpressionWithExpected accepted nonlocal, fun {_} _ _ calls => calls.recordExpressionWithExpected accepted nonlocal⟩

theorem unify {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : RelativeReadProgress root state next :=
  ⟨Progress.unify accepted, fun {_} _ _ calls => (unify_occurrenceState_eq accepted).1.symm ▸ calls⟩

theorem withExpected
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : withExpected context state actual expected = .ok result) :
    RelativeReadProgress root state result.state :=
  ⟨Progress.withExpected accepted, fun {_} _ _ calls => (withExpected_occurrenceState_eq accepted).1.symm ▸ calls⟩

theorem selectFunctionCandidateFrom
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    RelativeReadProgress root state result.state :=
  ⟨Progress.selectFunctionCandidateFrom accepted, fun {_} _ _ calls => (selectFunctionCandidateFrom_occurrenceState_eq accepted).1.symm ▸ calls⟩

theorem inferUnaryOperator
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    RelativeReadProgress root state result.state :=
  ⟨Progress.inferUnaryOperator success, fun {_} _ _ calls => (inferUnaryOperator_occurrenceState_eq success).1.symm ▸ calls⟩

theorem inferBinaryOperator
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    RelativeReadProgress root state result.state :=
  ⟨Progress.inferBinaryOperator success, fun {_} _ _ calls => (inferBinaryOperator_occurrenceState_eq success).1.symm ▸ calls⟩

theorem applyFunctionType
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    RelativeReadProgress root state result.state :=
  ⟨Progress.applyFunctionType success, fun {_} _ _ calls => (applyFunctionType_occurrenceState_eq success).1.symm ▸ calls⟩

theorem bindLambdaParameters
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    RelativeReadProgress root state result.2.2 :=
  ⟨Progress.bindLambdaParameters success, fun {_} _ _ calls => (bindLambdaParameters_occurrenceState_eq success).1.symm ▸ calls⟩

theorem inferMatchPatternFuel
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    RelativeReadProgress root state result.2 :=
  ⟨Progress.inferMatchPatternFuel success, fun {_} _ _ calls => (inferMatchPatternFuel_occurrenceState_eq success).1.symm ▸ calls⟩

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    RelativeReadProgress root state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  of_nodes_eq (Detail.freshDataConstructorInstantiation_nodes _ _ _) (Detail.freshDataConstructorInstantiation_direct_progress _ _ _)

theorem freshTypes (count : Nat) (state : State) : RelativeReadProgress root state (Detail.freshTypes count state).2 :=
  of_nodes_eq (Detail.freshTypes_nodes _ _) (Detail.freshTypes_direct_progress _ _)

theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result)
    (here : CallOccurrence root (.expression (fuel + 1) context expression expected initial result.1 result.2)) :
    RelativeReadProgress root initial result.2 := by
  refine ⟨Progress.localIdentifier form allocation found accepted, ?_⟩
  intro base wf direct calls
  let lookup : LocalReadEvents.Lookup := ⟨fuel, context, expression, expected, initial, allocated, id,
    name, binder, result, form, allocation, found, accepted, wf, direct⟩
  exact RelativeLocalRead.Lookup.record_origins lookup here calls

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : Detail.CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    RelativeReadProgress root state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2  := by
  refine ⟨Progress.recordSelectedCallResult _ _ _ _ _ _ _ _, ?_⟩
  intro base _ _ calls
  unfold Detail.recordSelectedCallResult
  exact (calls.attachExpressionCoercions _).recordExpression _ _ _ _ _ none
    (by intro _ _ impossible; cases impossible) |>.recordExpression _ _ _ _ _ none
      (by intro _ _ impossible; cases impossible)

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : Detail.CandidateAttemptResult) :
    RelativeReadProgress root attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult _ _ _ _ _ _ _ _

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : Detail.IndirectApplicationResult) :
    RelativeReadProgress root result.state (Detail.recordIndirectCall source callee arguments result).2  :=
  ⟨Progress.recordIndirectCall _ _ _ _, fun {_} _ _ calls => calls.recordExpression _ _ _ _ _ none
    (by intro _ _ impossible; cases impossible)⟩

theorem recordBuiltinFunctionCall
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    RelativeReadProgress root state result.2  := by
  refine ⟨Progress.recordBuiltinFunctionCall accepted, ?_⟩
  intro base _ _ calls
  obtain ⟨calleeId, nodes⟩ := Detail.recordBuiltinFunctionCall_success_nodes accepted
  rw [nodes]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    (calls.nonlocalExpression _ (by intro _ _ impossible; cases impossible)).nonlocalExpression _
      (by intro _ _ impossible; cases impossible)

theorem initializedStatement {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult} {expected : Ty}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result)
    (here : CallOccurrence root (.statement (fuel + 1) context statement expected initial result))
    (child : RelativeReadProgress root initial.allocateStatementId.2 receipt.ready) : RelativeReadProgress root initial result.state  := by
  refine ⟨Progress.initializedStatement receipt accepted here child.progress, ?_⟩
  intro base wf direct calls
  have childCalls := child.calls wf direct calls
  rw [receipt.completed]
  exact childCalls.statement _

end RelativeReadProgress
end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
end
