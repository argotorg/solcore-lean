import Solcore.Frontend.SourceInference.LocalReadEvents
import Solcore.Frontend.SourceInference.DirectRequirementInference

/-! Authentic local-read witnesses survive the inference helpers that append
nodes or attach argument coercions to already recorded expression roots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalReadEvents
open TypeSystem
open State (DirectRequirementsProgress)

/-- Local origins depend only on the node table and the requirement ledger. -/
theorem Origins.recordNode {state : State} (origins : Origins state) (node : Node)
    (added : ∀ expression, node = .expression expression → At state expression) :
    Origins (state.recordNode node) := by
  intro expression member
  rcases List.mem_append.mp member with old | fresh
  · exact origins expression old
  · exact added expression (List.mem_singleton.mp fresh).symm

theorem Origins.recordStatement {state : State} (origins : Origins state) (node : StatementNode) :
    Origins (state.recordNode (.statement node)) :=
  origins.recordNode _ (by intro expression impossible; cases impossible)

theorem Origins.modifyStatementNode {state : State} (origins : Origins state)
    (id : StatementId) (modify : StatementNode → StatementNode) :
    Origins (state.modifyStatementNode id modify) := by
  intro expression member
  obtain ⟨node, present, same⟩ := List.mem_map.mp member
  cases node with
  | expression old =>
    simp only at same
    cases same
    exact origins _ present
  | statement old =>
    simp only at same
    split at same <;> cases same

theorem Origins.modifyExpressionNode {state : State} (origins : Origins state)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode)
    (form : ∀ node, (modify node).form = node.form)
    (start : ∀ node, (modify node).localSchemeInstantiationStart = node.localSchemeInstantiationStart)
    (requirements : ∀ node, node.requirements <+: (modify node).requirements) :
    Origins (state.modifyExpressionNode id modify) := by
  intro expression member
  obtain ⟨node, present, same⟩ := List.mem_map.mp member
  cases node with
  | statement old => cases same
  | expression old =>
    simp only at same
    split at same
    next selected =>
      cases same
      exact At.node_extension (origins old present) selected.symm (form old) (start old) (requirements old)
    next =>
      cases same
      exact origins _ present

theorem Origins.attachExpressionCoercions {state : State} (origins : Origins state)
    (entries : List Detail.ExpressionCoercions) :
    Origins (Detail.attachExpressionCoercions state entries) := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact origins
  | cons entry rest ih =>
    apply ih
    exact origins.modifyExpressionNode entry.expression
      (fun node => Detail.appendExpressionCoercions node entry.coercions)
      (fun _ => rfl) (fun _ => rfl) (fun _ => List.prefix_append _ _)

def Nonlocal (form : ExpressionForm) : Prop :=
  ∀ name binder, form ≠ .reference name (.local binder)

theorem Origins.recordExpression {state : State} (origins : Origins state)
    (source : Syntax.Expr) (expression : InferredExpression) (form : ExpressionForm)
    (requirements : List RequirementId) (coercions : List CoercionStep)
    (start : Option Nat := none) (nonlocal : Nonlocal form) :
    Origins (Detail.recordExpression source expression form requirements coercions state start).2 := by
  apply origins.recordNode
  intro node same
  cases same
  exact fun name binder impossible => False.elim (nonlocal name binder impossible)

theorem Origins.recordExpressionWithExpected {state : State} (origins : Origins state)
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : Nonlocal form) : Origins result.2 := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  have fittedOrigins := origins.of_nodes_eq (Detail.withExpected_occurrenceState_eq fit).1
    (Detail.withExpected_direct_progress fit)
  apply fittedOrigins.recordNode
  intro node same
  cases same
  exact fun name binder impossible => False.elim (nonlocal name binder impossible)

theorem Lookup.origins (lookup : Lookup) (origins : Origins lookup.initial) : Origins lookup.result.2 := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_nodes lookup.recorded
  have allocatedEq : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
    (congrArg Prod.snd lookup.allocation).symm
  have batchOrigins : Origins lookup.batch.2 := by
    apply origins.of_nodes_eq
    · change (lookup.advanced.addRequirementsWithIds lookup.predicates).2.nodes = _
      rw [State.addRequirementsWithIds_nodes]
      change lookup.allocated.nodes = _
      rw [allocatedEq]
      rfl
    · exact (show DirectRequirementsProgress lookup.initial lookup.advanced from by
        change DirectRequirementsProgress lookup.initial lookup.allocated
        rw [allocatedEq]
        exact .refl _).trans (.addRequirementsWithIds _ _)
  have fittedOrigins := batchOrigins.of_nodes_eq (Detail.withExpected_occurrenceState_eq fit).1
    (Detail.withExpected_direct_progress fit)
  intro node member
  rw [recorded] at member
  rcases List.mem_append.mp member with old | fresh
  · have afterFit : DirectRequirementsProgress fitted.state lookup.result.2 := by
      obtain ⟨actual, actualFit, _, stateEq⟩ := Detail.recordExpressionWithExpected_success_record lookup.recorded
      have sameFit : actual = fitted := Except.ok.inj (actualFit.symm.trans fit)
      subst actual
      rw [stateEq]
      exact .refl _
    exact At.extend (fittedOrigins node old) afterFit
  · cases List.mem_singleton.mp fresh
    intro _ _ _
    exact ⟨lookup, Detail.withExpected_success_expression_id fit, rfl, rfl,
      List.prefix_append _ _, State.DirectRequirementsProgress.refl lookup.result.2⟩

open Detail


theorem Origins.unify {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : Origins state → Origins next :=
  fun origins => origins.of_nodes_eq (unify_occurrenceState_eq accepted).1
    (unify_direct_progress accepted)

theorem Origins.withExpected
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : withExpected context state actual expected = .ok result) :
    Origins state → Origins result.state :=
  fun origins => origins.of_nodes_eq (withExpected_occurrenceState_eq accepted).1
    (withExpected_direct_progress accepted)

theorem Origins.selectFunctionCandidateFrom
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    Origins state → Origins result.state :=
  fun origins => origins.of_nodes_eq (selectFunctionCandidateFrom_occurrenceState_eq accepted).1
    (selectFunctionCandidateFrom_direct_progress accepted)

theorem Origins.inferUnaryOperator
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    Origins state → Origins result.state :=
  fun origins => origins.of_nodes_eq (inferUnaryOperator_occurrenceState_eq success).1
    (inferUnaryOperator_direct_progress success)

theorem Origins.inferBinaryOperator
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    Origins state → Origins result.state :=
  fun origins => origins.of_nodes_eq (inferBinaryOperator_occurrenceState_eq success).1
    (inferBinaryOperator_direct_progress success)

theorem Origins.applyFunctionType
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    Origins state → Origins result.state :=
  fun origins => origins.of_nodes_eq (applyFunctionType_occurrenceState_eq success).1
    (applyFunctionType_direct_progress success)

theorem Origins.bindLambdaParameters
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    Origins state → Origins result.2.2 :=
  fun origins => origins.of_nodes_eq (bindLambdaParameters_occurrenceState_eq success).1
    (bindLambdaParameters_direct_progress success)

theorem Origins.freshDataConstructorInstantiation {state : State} (origins : Origins state)
    (dataType : ProgramDataSignature) (constructor : ProgramDataConstructorSignature) :
    Origins (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  origins.of_nodes_eq (Detail.freshDataConstructorInstantiation_nodes _ _ _)
    (Detail.freshDataConstructorInstantiation_direct_progress _ _ _)

theorem Origins.addRequirementsWithIds {state : State} (origins : Origins state)
    (predicates : List ProgramPredicate) : Origins (state.addRequirementsWithIds predicates).2 :=
  origins.of_nodes_eq (State.addRequirementsWithIds_nodes _ _) (.addRequirementsWithIds _ _)

theorem Origins.addRequirementWithId {state : State} (origins : Origins state)
    (predicate : ProgramPredicate) : Origins (state.addRequirementWithId predicate).2 :=
  origins.of_nodes_eq rfl (.addRequirementWithId _ _)

theorem Origins.recordSelectedCallResult {state : State} (origins : Origins state)
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : Detail.CandidateAttemptResult) (result : InferredExpression) (trailing : List CoercionStep) :
    Origins (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  unfold Detail.recordSelectedCallResult
  apply Origins.recordExpression
  · apply Origins.recordExpression
    · exact origins.attachExpressionCoercions _
    · intro _ _ impossible; cases impossible
  · intro _ _ impossible; cases impossible

theorem Origins.recordSelectedCall {attempt : Detail.CandidateAttemptResult} (origins : Origins attempt.state)
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression) :
    Origins (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  origins.recordSelectedCallResult _ _ _ _ _ _ _

theorem Origins.recordIndirectCall {result : Detail.IndirectApplicationResult} (origins : Origins result.state)
    (source : Syntax.Expr) (callee : InferredExpression) (arguments : List InferredExpression) :
    Origins (Detail.recordIndirectCall source callee arguments result).2 := by
  apply origins.recordExpression
  intro _ _ impossible; cases impossible

theorem Origins.recordBuiltinFunctionCall {state : State} (origins : Origins state)
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Origins result.2 := by
  obtain ⟨calleeId, nodes⟩ := Detail.recordBuiltinFunctionCall_success_nodes accepted
  have progress := Detail.recordBuiltinFunctionCall_direct_progress accepted
  intro node member
  rw [nodes] at member
  rcases List.mem_append.mp member with old | fresh
  · exact At.extend (origins node old) progress
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Node.expression.injEq] at fresh
    rcases fresh with first | second <;> subst node
    all_goals intro _ _ impossible; cases impossible

theorem Origins.inferMatchPatternFuel
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    Origins state → Origins result.2 :=
  fun origins => origins.of_nodes_eq (inferMatchPatternFuel_occurrenceState_eq success).1
    (inferMatchPatternFuel_direct_progress success)

end Solcore.Frontend.SourceInference.LocalReadEvents
