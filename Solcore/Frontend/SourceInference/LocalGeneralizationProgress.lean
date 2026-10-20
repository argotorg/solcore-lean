import Solcore.Frontend.SourceInference.LocalGeneralizationEvents

/-! The actual read-origin progress supplies each nested initializer's entry
invariants. Generalization events preserve exact statement forms. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationEvents
open TypeSystem Detail
open State (DirectRequirementsProgress)

structure ProgressFields
    (beforeNodes : List Node) (beforeRows : List Requirement) (beforeNext : Nat) (beforeDirect : List RequirementId)
    (afterNodes : List Node) (afterRows : List Requirement) (afterNext : Nat) (afterDirect : List RequirementId) : Prop where
  reads : LocalReadEvents.ProgressFields beforeNodes beforeRows beforeNext beforeDirect afterNodes afterRows afterNext afterDirect
  events : beforeRows.map (fun requirement => requirement.id.index) = List.range beforeNext →
    beforeDirect ⊆ beforeRows.map Requirement.id →
    LocalReadEvents.OriginsFields beforeNodes beforeRows beforeNext beforeDirect →
    Origins beforeNodes → Origins afterNodes

abbrev Progress (before after : State) : Prop :=
  ProgressFields before.nodes before.requirements before.nextRequirement before.directCallRequirements
    after.nodes after.requirements after.nextRequirement after.directCallRequirements

theorem ProgressFields.trans
    {bn mn an : List Node} {br mr ar : List Requirement} {bi mi ai : Nat}
    {bd md ad : List RequirementId}
    (first : ProgressFields bn br bi bd mn mr mi md)
    (second : ProgressFields mn mr mi md an ar ai ad) :
    ProgressFields bn br bi bd an ar ai ad :=
  ⟨first.reads.trans second.reads, fun wf allocated reads events =>
    second.events (first.reads.ledger.wellFormed wf)
      (first.reads.ledger.allocated wf allocated) (first.reads.origins wf allocated reads)
      (first.events wf allocated reads events)⟩

theorem ProgressFields.statement (nodes : List Node) (rows : List Requirement)
    (next : Nat) (direct : List RequirementId) (node : StatementNode) (event : Statement node) :
    ProgressFields nodes rows next direct (nodes ++ [.statement node]) rows next direct :=
  ⟨LocalReadEvents.ProgressFields.statement _ _ _ _ _, fun _ _ _ origins => origins.statement node event⟩

theorem ProgressFields.expression (nodes : List Node) (rows : List Requirement)
    (next : Nat) (direct : List RequirementId) (node : ExpressionNode)
    (nonlocal : LocalReadEvents.Nonlocal node.form) :
    ProgressFields nodes rows next direct (nodes ++ [.expression node]) rows next direct :=
  ⟨LocalReadEvents.ProgressFields.expression _ _ _ _ _ nonlocal, fun _ _ _ origins => origins.expression node⟩

namespace Progress
theorem refl (state : State) : Progress state state := ⟨LocalReadEvents.Progress.refl _, fun _ _ _ origins => origins⟩
theorem trans {before middle after : State} (first : Progress before middle) (second : Progress middle after) :
    Progress before after := ProgressFields.trans first second

theorem of_nodes_eq {before after : State} (same : after.nodes = before.nodes)
    (ledger : DirectRequirementsProgress before after) : Progress before after :=
  ⟨LocalReadEvents.Progress.of_nodes_eq same ledger, fun _ _ _ origins => same.symm ▸ origins⟩

theorem recordStatement (state : State) (node : StatementNode) (event : Statement node) :
    Progress state (state.recordNode (.statement node)) :=
  ⟨LocalReadEvents.Progress.recordStatement _ _, fun _ _ _ origins => origins.statement node event⟩

theorem modifyStatementNode (state : State) (id : StatementId) (modify : StatementNode → StatementNode)
    (forms : ∀ node, (modify node).form = node.form) : Progress state (state.modifyStatementNode id modify) := by
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
    Progress state (state.addRequirementWithId predicate).2 :=
  of_nodes_eq rfl (.addRequirementWithId _ _)

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress state (state.addRequirementsWithIds predicates).2 :=
  of_nodes_eq (State.addRequirementsWithIds_nodes _ _) (.addRequirementsWithIds _ _)

end Progress

theorem Origins.modifyExpressionNode {state : State} (origins : Origins state.nodes)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode) :
    Origins (state.modifyExpressionNode id modify).nodes := by
  intro statement present
  obtain ⟨node, member, same⟩ := List.mem_map.mp present
  cases node with
  | expression node => simp only at same; split at same <;> cases same
  | statement original => cases same; exact origins _ member

theorem Origins.attachExpressionCoercions {state : State} (origins : Origins state.nodes)
    (entries : List Detail.ExpressionCoercions) : Origins (Detail.attachExpressionCoercions state entries).nodes := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact origins
  | cons entry rest ih => exact ih (origins.modifyExpressionNode _ _)

theorem Origins.recordExpression {state : State} (origins : Origins state.nodes)
    (source : Syntax.Expr) (expression : InferredExpression) (form : ExpressionForm)
    (requirements : List RequirementId) (coercions : List CoercionStep) (start : Option Nat := none) :
    Origins (Detail.recordExpression source expression form requirements coercions state start).2.nodes :=
  origins.expression _

theorem Origins.recordExpressionWithExpected {state : State} (origins : Origins state.nodes)
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result) :
    Origins result.2.nodes := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  have same := (Detail.withExpected_occurrenceState_eq fit).1
  exact (show Origins fitted.state.nodes from same.symm ▸ origins).expression _

namespace Progress
theorem recordExpressionWithExpected
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : Progress state result.2 :=
  ⟨LocalReadEvents.Progress.recordExpressionWithExpected accepted nonlocal,
    fun _ _ _ origins => origins.recordExpressionWithExpected accepted⟩

theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Progress initial result.2 := by
  refine ⟨LocalReadEvents.Progress.localIdentifier form allocation found accepted, ?_⟩
  intro _ _ _ origins
  apply Origins.recordExpressionWithExpected (accepted := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted)
  rw [State.addRequirementsWithIds_nodes]
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  simpa only [same, State.allocateExpressionId_nodes] using origins

theorem unify {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : Progress state next :=
  ⟨LocalReadEvents.Progress.unify accepted, fun _ _ _ origins =>
    (unify_occurrenceState_eq accepted).1.symm ▸ origins⟩

theorem withExpected
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : withExpected context state actual expected = .ok result) :
    Progress state result.state :=
  ⟨LocalReadEvents.Progress.withExpected accepted, fun _ _ _ origins =>
    (withExpected_occurrenceState_eq accepted).1.symm ▸ origins⟩

theorem selectFunctionCandidateFrom
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    Progress state result.state :=
  ⟨LocalReadEvents.Progress.selectFunctionCandidateFrom accepted, fun _ _ _ origins =>
    (selectFunctionCandidateFrom_occurrenceState_eq accepted).1.symm ▸ origins⟩

theorem inferUnaryOperator
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    Progress state result.state :=
  ⟨LocalReadEvents.Progress.inferUnaryOperator success, fun _ _ _ origins =>
    (inferUnaryOperator_occurrenceState_eq success).1.symm ▸ origins⟩

theorem inferBinaryOperator
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    Progress state result.state :=
  ⟨LocalReadEvents.Progress.inferBinaryOperator success, fun _ _ _ origins =>
    (inferBinaryOperator_occurrenceState_eq success).1.symm ▸ origins⟩

theorem applyFunctionType
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    Progress state result.state :=
  ⟨LocalReadEvents.Progress.applyFunctionType success, fun _ _ _ origins =>
    (applyFunctionType_occurrenceState_eq success).1.symm ▸ origins⟩

theorem bindLambdaParameters
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    Progress state result.2.2 :=
  ⟨LocalReadEvents.Progress.bindLambdaParameters success, fun _ _ _ origins =>
    (bindLambdaParameters_occurrenceState_eq success).1.symm ▸ origins⟩

theorem inferMatchPatternFuel
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress state result.2 :=
  ⟨LocalReadEvents.Progress.inferMatchPatternFuel success, fun _ _ _ origins =>
    (inferMatchPatternFuel_occurrenceState_eq success).1.symm ▸ origins⟩

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  of_nodes_eq (Detail.freshDataConstructorInstantiation_nodes _ _ _)
    (Detail.freshDataConstructorInstantiation_direct_progress _ _ _)

theorem freshTypes (count : Nat) (state : State) : Progress state (Detail.freshTypes count state).2 :=
  of_nodes_eq (Detail.freshTypes_nodes _ _) (Detail.freshTypes_direct_progress _ _)

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : Detail.CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  refine ⟨LocalReadEvents.Progress.recordSelectedCallResult _ _ _ _ _ _ _ _, ?_⟩
  intro _ _ _ origins
  unfold Detail.recordSelectedCallResult
  exact (origins.attachExpressionCoercions _).recordExpression _ _ _ _ _ |>.recordExpression _ _ _ _ _

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : Detail.CandidateAttemptResult) :
    Progress attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 := recordSelectedCallResult _ _ _ _ _ _ _ _

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : Detail.IndirectApplicationResult) :
    Progress result.state (Detail.recordIndirectCall source callee arguments result).2 := ⟨LocalReadEvents.Progress.recordIndirectCall _ _ _ _, fun _ _ _ origins => origins.recordExpression _ _ _ _ _⟩

theorem recordBuiltinFunctionCall
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Progress state result.2 := by
  refine ⟨LocalReadEvents.Progress.recordBuiltinFunctionCall accepted, ?_⟩
  intro _ _ _ origins
  obtain ⟨calleeId, nodes⟩ := Detail.recordBuiltinFunctionCall_success_nodes accepted
  rw [nodes]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using (origins.expression _).expression _


theorem initializedStatement {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult} {expected : Ty}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (accepted : inferStatementFuel (fuel + 1) context statement expected initial = .ok result)
    (child : Progress initial.allocateStatementId.2 receipt.ready) : Progress initial result.state := by
  refine ⟨LocalReadEvents.inferStatementFuel_origins_progress accepted, ?_⟩
  intro wf allocated reads events
  have childEvents := child.events wf allocated reads events
  rw [receipt.completed]
  exact childEvents.statement _ (Origin.statement receipt ⟨wf, allocated, reads⟩)

end Progress
end Solcore.Frontend.SourceInference.LocalGeneralizationEvents
