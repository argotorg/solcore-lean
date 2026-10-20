import Solcore.Frontend.SourceInference.DirectCallCandidateOrigins

/-! Actual direct-call emitters also retain the catalog membership of their
selected declaration. This is needed to distinguish their edges from prepared
implementation-method edges at the same source occurrence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.Frontend.SourceInference.CatalogedDirectCallEvents
open TypeSystem Detail DirectCallEvents

def HasCall (catalog : List Resolved.DeclarationId) (nodes : List Node) (requirement : RequirementId) : Prop :=
  ∃ node, .expression node ∈ nodes ∧
    ∃ callee arguments instantiation,
      node.form = .call callee arguments (.declaration instantiation) ∧
      requirement ∈ node.requirements ∧ instantiation.declaration ∈ catalog

def OriginsFields (catalog : List Resolved.DeclarationId) (nodes : List Node) (direct : List RequirementId) : Prop :=
  ∀ requirement ∈ direct, HasCall catalog nodes requirement
abbrev Origins (catalog : List Resolved.DeclarationId) (state : State) : Prop :=
  OriginsFields catalog state.nodes state.directCallRequirements

def ProgressFields (catalog : List Resolved.DeclarationId)
    (beforeNodes : List Node) (beforeDirect : List RequirementId)
    (afterNodes : List Node) (afterDirect : List RequirementId) : Prop :=
  OriginsFields catalog beforeNodes beforeDirect → OriginsFields catalog afterNodes afterDirect
abbrev Progress (catalog : List Resolved.DeclarationId) (before after : State) : Prop :=
  ProgressFields catalog before.nodes before.directCallRequirements
    after.nodes after.directCallRequirements

variable {catalog : List Resolved.DeclarationId}

theorem HasCall.mono {before after : List Node} {requirement : RequirementId}
    (call : HasCall catalog before requirement) (included : before ⊆ after) :
    HasCall catalog after requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued, cataloged⟩ := call
  exact ⟨node, included member, callee, arguments, instantiation, form, issued, cataloged⟩

theorem HasCall.modifyStatementNode {state : State} {requirement : RequirementId}
    (call : HasCall catalog state.nodes requirement)
    (id : StatementId) (modify : StatementNode → StatementNode) :
    HasCall catalog (state.modifyStatementNode id modify).nodes requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued, cataloged⟩ := call
  exact ⟨node, List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, instantiation, form, issued, cataloged⟩

theorem HasCall.modifyExpressionNode {state : State} {requirement : RequirementId}
    (call : HasCall catalog state.nodes requirement)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode)
    (form : ∀ node, (modify node).form = node.form)
    (requirements : ∀ node, node.requirements ⊆ (modify node).requirements) :
    HasCall catalog (state.modifyExpressionNode id modify).nodes requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, original, issued, cataloged⟩ := call
  by_cases selected : node.id = id
  · refine ⟨{ modify node with id }, List.mem_map.mpr ⟨.expression node, member, ?_⟩,
      callee, arguments, instantiation, (form node).trans original, requirements node issued, cataloged⟩
    simp [selected]
  · refine ⟨node, List.mem_map.mpr ⟨.expression node, member, ?_⟩,
      callee, arguments, instantiation, original, issued, cataloged⟩
    simp [selected]

theorem HasCall.attachExpressionCoercions {state : State} {requirement : RequirementId}
    (call : HasCall catalog state.nodes requirement) (entries : List ExpressionCoercions) :
    HasCall catalog (attachExpressionCoercions state entries).nodes requirement := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact call
  | cons entry rest ih =>
    apply ih
    exact call.modifyExpressionNode entry.expression
      (fun node => appendExpressionCoercions node entry.coercions)
      (fun _ => rfl) (fun _ => List.subset_append_left _ _)

theorem ProgressFields.trans {bn mn an : List Node} {bd md ad : List RequirementId}
    (first : ProgressFields catalog bn bd mn md) (second : ProgressFields catalog mn md an ad) :
    ProgressFields catalog bn bd an ad := fun origins => second (first origins)

theorem ProgressFields.statement (nodes : List Node) (direct : List RequirementId)
    (statement : StatementNode) :
    ProgressFields catalog nodes direct (nodes ++ [.statement statement]) direct :=
  fun origins requirement member => (origins requirement member).mono (List.subset_append_left _ _)

theorem ProgressFields.expression (nodes : List Node) (direct : List RequirementId)
    (expression : ExpressionNode) :
    ProgressFields catalog nodes direct (nodes ++ [.expression expression]) direct :=
  fun origins requirement member => (origins requirement member).mono (List.subset_append_left _ _)

namespace Progress

theorem refl (state : State) : Progress catalog state state := fun origins => origins

theorem trans {before middle after : State}
    (first : Progress catalog before middle) (second : Progress catalog middle after) : Progress catalog before after :=
  ProgressFields.trans first second

theorem of_nodes_eq {before after : State} (nodes : after.nodes = before.nodes)
    (direct : Unchanged before after) : Progress catalog before after := by
  intro origins
  simpa only [OriginsFields, nodes, direct] using origins

theorem recordStatement (state : State) (node : StatementNode) :
    Progress catalog state (state.recordNode (.statement node)) :=
  ProgressFields.statement _ _ _

theorem modifyStatementNode (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode) :
    Progress catalog state (state.modifyStatementNode id modify) :=
  fun origins requirement member => (origins requirement member).modifyStatementNode id modify

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Progress catalog state (state.addRequirementWithId predicate).2 := of_nodes_eq rfl rfl

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress catalog state (state.addRequirementsWithIds predicates).2 :=
  of_nodes_eq (State.addRequirementsWithIds_nodes _ _) (State.addRequirementsWithIds_direct_eq _ _)

theorem recordExpression (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId) (coercions : List CoercionStep)
    (state : State) (start : Option Nat := none) :
    Progress catalog state (Detail.recordExpression source expression form requirements coercions state start).2 :=
  ProgressFields.expression _ _ _

theorem recordExpressionWithExpected
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {state : State} {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result) :
    Progress catalog state result.2 := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  exact (of_nodes_eq (withExpected_occurrenceState_eq fit).1
    (withExpected_direct_eq fit)).trans (ProgressFields.expression _ _ _)

theorem unify {state next : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok next) : Progress catalog state next :=
  of_nodes_eq (unify_occurrenceState_eq accepted).1 (unify_direct_unchanged accepted)

theorem withExpected {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    Progress catalog state result.state :=
  of_nodes_eq (withExpected_occurrenceState_eq accepted).1 (withExpected_direct_eq accepted)

theorem inferUnaryOperator
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    Progress catalog state result.state :=
  of_nodes_eq (inferUnaryOperator_occurrenceState_eq accepted).1 (inferUnaryOperator_direct_unchanged accepted)

theorem inferBinaryOperator
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    Progress catalog state result.state :=
  of_nodes_eq (inferBinaryOperator_occurrenceState_eq accepted).1 (inferBinaryOperator_direct_unchanged accepted)

theorem applyFunctionType {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (accepted : Detail.applyFunctionType context call calleeType arguments expected state = .ok result) :
    Progress catalog state result.state :=
  of_nodes_eq (applyFunctionType_occurrenceState_eq accepted).1 (applyFunctionType_direct_unchanged accepted)

theorem bindLambdaParameters {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State} {result : List TypedBinder × List Ty × State}
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    Progress catalog state result.2.2 :=
  of_nodes_eq (bindLambdaParameters_occurrenceState_eq accepted).1 (bindLambdaParameters_direct_unchanged accepted)

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress catalog state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  of_nodes_eq (Detail.freshDataConstructorInstantiation_nodes _ _ _)
    (freshDataConstructorInstantiation_direct_unchanged _ _ _)

theorem freshTypes (count : Nat) (state : State) : Progress catalog state (Detail.freshTypes count state).2 :=
  of_nodes_eq (Detail.freshTypes_nodes _ _) (freshTypes_direct_unchanged _ _)

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress catalog state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  intro origins requirement member
  have direct := recordSelectedCallResult_direct_unchanged source callee name arguments attempt result trailing state
  rw [direct] at member
  apply ((origins requirement member).attachExpressionCoercions attempt.argumentCoercions).mono
  intro node present
  exact List.mem_append_left _ (List.mem_append_left _ present)

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    Progress catalog attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult _ _ _ _ _ _ _ _

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    Progress catalog result.state (Detail.recordIndirectCall source callee arguments result).2 :=
  ProgressFields.expression _ _ _

theorem recordBuiltinFunctionCall
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Progress catalog state result.2 := by
  intro origins requirement member
  have direct := recordBuiltinFunctionCall_direct_unchanged accepted
  rw [direct] at member
  obtain ⟨calleeId, nodes⟩ := Detail.recordBuiltinFunctionCall_success_nodes accepted
  exact (origins requirement member).mono (by rw [nodes]; exact List.subset_append_left _ _)

theorem inferMatchPatternFuel {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress catalog state result.2 :=
  of_nodes_eq (inferMatchPatternFuel_occurrenceState_eq accepted).1 (inferMatchPatternFuel_direct_unchanged accepted)

theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Progress catalog initial result.2 := by
  have recorded := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  apply Progress.trans (middle := allocated)
  · rw [allocatedEq]; exact refl _
  · have recording := recordExpressionWithExpected (catalog := catalog) recorded
    refine ProgressFields.trans ?_ recording
    simp only [State.addRequirementsWithIds_nodes, State.addRequirementsWithIds_direct_eq]
    exact refl _

end Progress
end Solcore.Frontend.SourceInference.CatalogedDirectCallEvents
