import Solcore.Frontend.SourceInference.LocalReadOriginsHelpers

/-! Progress combines the actual ledger invariant with local-read provenance,
so recursive inference carries both from its genuine initial state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalReadEvents
open TypeSystem Detail
open State (DirectRequirementsProgress)

structure ProgressFields
    (beforeNodes : List Node) (beforeRows : List Requirement) (beforeNext : Nat) (beforeDirect : List RequirementId)
    (afterNodes : List Node) (afterRows : List Requirement) (afterNext : Nat) (afterDirect : List RequirementId) : Prop where
  ledger : RequirementLedgerProgress beforeRows beforeNext beforeDirect afterRows afterNext afterDirect
  origins : beforeRows.map (fun requirement => requirement.id.index) = List.range beforeNext →
    beforeDirect ⊆ beforeRows.map Requirement.id →
    OriginsFields beforeNodes beforeRows beforeNext beforeDirect →
    OriginsFields afterNodes afterRows afterNext afterDirect

abbrev Progress (before after : State) : Prop :=
  ProgressFields before.nodes before.requirements before.nextRequirement before.directCallRequirements
    after.nodes after.requirements after.nextRequirement after.directCallRequirements

theorem ProgressFields.trans
    {bn mn an : List Node} {br mr ar : List Requirement} {bi mi ai : Nat}
    {bd md ad : List RequirementId}
    (first : ProgressFields bn br bi bd mn mr mi md)
    (second : ProgressFields mn mr mi md an ar ai ad) :
    ProgressFields bn br bi bd an ar ai ad := by
  have ledger : RequirementLedgerProgress br bi bd ar ai ad := by
    refine ⟨first.ledger.included.trans second.ledger.included,
      fun wf => second.ledger.wellFormed (first.ledger.wellFormed wf),
      fun wf allocated => second.ledger.allocated (first.ledger.wellFormed wf)
        (first.ledger.allocated wf allocated), ?_⟩
    intro wf id member
    obtain ⟨requirement, present, same⟩ := List.mem_map.mp member
    subst id
    exact (second.ledger.existing (first.ledger.wellFormed wf) requirement.id
      (List.mem_map.mpr ⟨requirement, first.ledger.included present, rfl⟩)).trans
      (first.ledger.existing wf requirement.id (List.mem_map.mpr ⟨requirement, present, rfl⟩))
  exact ⟨ledger, fun wf allocated origins => second.origins (first.ledger.wellFormed wf)
    (first.ledger.allocated wf allocated) (first.origins wf allocated origins)⟩

theorem ProgressFields.statement (nodes : List Node) (rows : List Requirement)
    (next : Nat) (direct : List RequirementId) (statement : StatementNode) :
    ProgressFields nodes rows next direct (nodes ++ [.statement statement]) rows next direct := by
  refine ⟨⟨fun _ member => member, id, fun _ allocated => allocated, fun _ _ _ => Iff.rfl⟩, ?_⟩
  intro _ _ origins node member
  rcases List.mem_append.mp member with old | fresh
  · exact origins node old
  · cases List.mem_singleton.mp fresh

theorem ProgressFields.expression (nodes : List Node) (rows : List Requirement)
    (next : Nat) (direct : List RequirementId) (expression : ExpressionNode)
    (nonlocal : Nonlocal expression.form) :
    ProgressFields nodes rows next direct (nodes ++ [.expression expression]) rows next direct := by
  refine ⟨⟨fun _ member => member, id, fun _ allocated => allocated, fun _ _ _ => Iff.rfl⟩, ?_⟩
  intro _ _ origins node member
  rcases List.mem_append.mp member with old | fresh
  · exact origins node old
  · cases List.mem_singleton.mp fresh
    exact fun name binder same => False.elim (nonlocal name binder same)

namespace Progress

theorem refl (state : State) : Progress state state := ⟨DirectRequirementsProgress.refl _, fun _ _ origins => origins⟩

theorem trans {before middle after : State} (first : Progress before middle) (second : Progress middle after) :
    Progress before after :=
  ⟨DirectRequirementsProgress.trans first.ledger second.ledger,
   fun wf allocated origins => second.origins (first.ledger.wellFormed wf)
     (first.ledger.allocated wf allocated) (first.origins wf allocated origins)⟩

theorem of_nodes_eq {before after : State} (same : after.nodes = before.nodes)
    (ledger : DirectRequirementsProgress before after) : Progress before after :=
  ⟨ledger, fun _ _ origins => Origins.of_nodes_eq origins same ledger⟩

theorem recordStatement (state : State) (node : StatementNode) :
    Progress state (state.recordNode (.statement node)) :=
  ⟨DirectRequirementsProgress.refl _, fun _ _ origins => Origins.recordStatement origins _⟩

theorem modifyStatementNode (state : State) (id : StatementId) (modify : StatementNode → StatementNode) :
    Progress state (state.modifyStatementNode id modify) :=
  ⟨DirectRequirementsProgress.refl _, fun _ _ origins => Origins.modifyStatementNode origins _ _⟩

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Progress state (state.addRequirementWithId predicate).2 :=
  ⟨DirectRequirementsProgress.addRequirementWithId _ _, fun _ _ origins => Origins.addRequirementWithId origins _⟩

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress state (state.addRequirementsWithIds predicates).2 :=
  ⟨DirectRequirementsProgress.addRequirementsWithIds _ _, fun _ _ origins => Origins.addRequirementsWithIds origins _⟩

theorem recordExpression (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId) (coercions : List CoercionStep)
    (state : State) (start : Option Nat := none) (nonlocal : Nonlocal form) :
    Progress state (Detail.recordExpression source expression form requirements coercions state start).2 :=
  ⟨DirectRequirementsProgress.refl _, fun _ _ origins => Origins.recordExpression origins _ _ _ _ _ _ nonlocal⟩

theorem recordExpressionWithExpected
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : Nonlocal form) : Progress state result.2 :=
  ⟨Detail.recordExpressionWithExpected_direct_progress accepted,
    fun _ _ origins => Origins.recordExpressionWithExpected origins accepted nonlocal⟩

theorem unify {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : Progress state next :=
  ⟨Detail.unify_direct_progress accepted, fun _ _ origins => Origins.unify accepted origins⟩

theorem withExpected
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : withExpected context state actual expected = .ok result) :
    Progress state result.state :=
  ⟨Detail.withExpected_direct_progress accepted, fun _ _ origins => Origins.withExpected accepted origins⟩

theorem selectFunctionCandidateFrom
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    Progress state result.state :=
  ⟨Detail.selectFunctionCandidateFrom_direct_progress accepted, fun _ _ origins => Origins.selectFunctionCandidateFrom accepted origins⟩

theorem inferUnaryOperator
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    Progress state result.state :=
  ⟨Detail.inferUnaryOperator_direct_progress success, fun _ _ origins => Origins.inferUnaryOperator success origins⟩

theorem inferBinaryOperator
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    Progress state result.state :=
  ⟨Detail.inferBinaryOperator_direct_progress success, fun _ _ origins => Origins.inferBinaryOperator success origins⟩

theorem applyFunctionType
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    Progress state result.state :=
  ⟨Detail.applyFunctionType_direct_progress success, fun _ _ origins => Origins.applyFunctionType success origins⟩

theorem bindLambdaParameters
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    Progress state result.2.2 :=
  ⟨Detail.bindLambdaParameters_direct_progress success, fun _ _ origins => Origins.bindLambdaParameters success origins⟩

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  ⟨Detail.freshDataConstructorInstantiation_direct_progress _ _ _,
    fun _ _ origins => Origins.freshDataConstructorInstantiation origins _ _⟩

theorem freshTypes (count : Nat) (state : State) : Progress state (Detail.freshTypes count state).2 :=
  Progress.of_nodes_eq (Detail.freshTypes_nodes _ _) (Detail.freshTypes_direct_progress _ _)

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : Detail.CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 :=
  ⟨Detail.recordSelectedCallResult_direct_progress _ _ _ _ _ _ _ _,
    fun _ _ origins => Origins.recordSelectedCallResult origins _ _ _ _ _ _ _⟩

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : Detail.CandidateAttemptResult) :
    Progress attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  ⟨Detail.recordSelectedCall_direct_progress _ _ _ _ _,
    fun _ _ origins => Origins.recordSelectedCall origins _ _ _ _⟩

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : Detail.IndirectApplicationResult) :
    Progress result.state (Detail.recordIndirectCall source callee arguments result).2 :=
  ⟨Detail.recordIndirectCall_direct_progress _ _ _ _,
    fun _ _ origins => Origins.recordIndirectCall origins _ _ _⟩

theorem recordBuiltinFunctionCall
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Progress state result.2 :=
  ⟨Detail.recordBuiltinFunctionCall_direct_progress accepted,
    fun _ _ origins => Origins.recordBuiltinFunctionCall origins accepted⟩

theorem inferMatchPatternFuel
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress state result.2 :=
  ⟨Detail.inferMatchPatternFuel_direct_progress success,
    fun _ _ origins => Origins.inferMatchPatternFuel success origins⟩

theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Progress initial result.2 := by
  have recorded := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  refine ⟨?_, ?_⟩
  · have afterRecord := Detail.recordExpressionWithExpected_direct_progress recorded
    have afterAllocation : DirectRequirementsProgress initial allocated := by
      rw [allocatedEq]
      exact .refl _
    exact afterAllocation.trans ((DirectRequirementsProgress.addRequirementsWithIds
      { allocated with inference := { allocated.inference with
          next := (binder.scheme.instantiateWithSubstitution allocated.inference.next).next } } _).trans afterRecord)
  · intro wf direct origins
    let lookup : Lookup := ⟨fuel, context, expression, expected, initial, allocated, id,
      name, binder, result, form, allocation, found, accepted, wf, direct⟩
    exact lookup.origins origins

end Progress
end Solcore.Frontend.SourceInference.LocalReadEvents
