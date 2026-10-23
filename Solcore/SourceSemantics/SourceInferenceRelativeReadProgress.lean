import Solcore.SourceSemantics.SourceInferenceActualReadProgress
import Solcore.SourceSemantics.SourceInferenceRelativeReadCalls

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
