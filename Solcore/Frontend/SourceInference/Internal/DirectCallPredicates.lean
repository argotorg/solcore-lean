import Solcore.Frontend.SourceInference.Internal.DirectCallOrigins
import Lean

/-!
# Direct call predicates

Direct-call requirements keep their raw ledger row, their catalog declaration and their exact
predicate.
-/

section
-- leanmerge: from Solcore.Frontend.SourceInference.CatalogedDirectCallProgress
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
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.CatalogedDirectCallCandidate
/-! The actual selected candidate supplies the ordinary catalog declaration
before its newly issued requirement batch is recorded on the source call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.CatalogedDirectCallEvents
open TypeSystem Detail DirectCallEvents
variable {catalog : List Resolved.DeclarationId}

/-- Recording discharges the exact pending batch together with its actual
selected declaration. No typing judgment is used to identify that declaration. -/
theorem recordSelectedCallResult_pending
    {before state : State} {attempt : CandidateAttemptResult}
    (nodes : state.nodes = before.nodes)
    (direct : state.directCallRequirements = before.directCallRequirements ++ attempt.signatureRequirements)
    (cataloged : attempt.instantiation.declaration ∈ catalog)
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (result : InferredExpression) (trailing : List CoercionStep) :
    Progress catalog before (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  intro origins requirement member
  rw [recordSelectedCallResult_direct_unchanged, direct] at member
  rcases List.mem_append.mp member with prior | fresh
  · have original : HasCall catalog state.nodes requirement := by
      rw [nodes]
      exact origins requirement prior
    apply (original.attachExpressionCoercions attempt.argumentCoercions).mono
    intro node present
    exact List.mem_append_left _ (List.mem_append_left _ present)
  · let calleeId := (Detail.attachExpressionCoercions state attempt.argumentCoercions).allocateExpressionId.1
    let callNode : ExpressionNode := {
      id := result.id, span := source.span, type := result.type
      form := .call calleeId (arguments.map (·.id)) (.declaration attempt.instantiation)
      requirements := coercionRequirements attempt.callCoercions ++ attempt.signatureRequirements ++
        coercionRequirements trailing
      coercions := attempt.callCoercions ++ trailing }
    refine ⟨callNode, ?_, calleeId, arguments.map (·.id), attempt.instantiation, rfl, ?_, cataloged⟩
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (List.mem_append_right _ fresh)

theorem selected_catalog
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {attempt : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok attempt)
    (cataloged : candidates ⊆ context.signatures.functions) :
    attempt.instantiation.declaration ∈ context.signatures.functions.map (·.id) := by
  obtain ⟨signature, present, selected⟩ := selectFunctionCandidateFrom_success_candidate accepted
  rw [tryFunctionCandidate_some_instantiation selected]
  exact List.mem_map.mpr ⟨signature, cataloged present, rfl⟩

namespace Progress

theorem selectAndRecord
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {attempt : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok attempt)
    (cataloged : candidates ⊆ context.signatures.functions)
    (source callee : Syntax.Expr) :
    Progress (context.signatures.functions.map (·.id)) state
      (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult_pending (selectFunctionCandidateFrom_occurrenceState_eq accepted).1
    (selectFunctionCandidateFrom_direct_batch accepted) (selected_catalog accepted cataloged)
    source callee name arguments _ _

theorem selectFitAndRecord
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected selectedExpected : Option Ty} {state : State}
    {attempt : CandidateAttemptResult} {fitted : ExpectationResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call selectedExpected state = .ok attempt)
    (fit : Detail.withExpected context attempt.state attempt.result expected = .ok fitted)
    (cataloged : candidates ⊆ context.signatures.functions)
    (source callee : Syntax.Expr) :
    Progress (context.signatures.functions.map (·.id)) state
      (Detail.recordSelectedCallResult source callee name arguments attempt
        fitted.expression fitted.coercions fitted.state).2 :=
  recordSelectedCallResult_pending
    ((withExpected_occurrenceState_eq fit).1.trans (selectFunctionCandidateFrom_occurrenceState_eq accepted).1)
    ((withExpected_direct_eq fit).trans (selectFunctionCandidateFrom_direct_batch accepted))
    (selected_catalog accepted cataloged) source callee name arguments _ _

end Progress
end Solcore.Frontend.SourceInference.CatalogedDirectCallEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.CatalogedDirectCallInference
/-! Every direct-call requirement issued by successful inference retains an
actual declaration-call emitter and selected ordinary declaration through all eleven recursive inference paths. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.SourceInference.CatalogedDirectCallEvents
open TypeSystem Detail
variable {catalog : List Resolved.DeclarationId}

/-- Give the mutual recursor's inaccessible context binder a stable local name;
this changes only elaboration names and does not introduce any proof premise. -/
elab "cataloged_call_context" : tactic => Lean.Elab.Tactic.withMainContext do
  for declaration in ← Lean.getLCtx do
    if declaration.type.isConstOf ``Context then
      let goal ← Lean.Elab.Tactic.getMainGoal
      Lean.Elab.Tactic.replaceMainGoal [← goal.rename declaration.fvarId `context]
      return
  throwError "missing actual inference context"

@[simp] private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private def PreservesOrigins (catalog : List Resolved.DeclarationId) {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Progress catalog initial (stateOf result)

private theorem pair_success_origins_progress {alpha : Type}
    {operation : alpha × State} {value : alpha} {next initial : State}
    (operationSubset : Progress catalog initial operation.2)
    (success : operation = (value, next)) :
    Progress catalog initial next := by
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
        Progress catalog initial next)
    (invariant : ∀ value state result next,
      computation value state = .ok (result, next) →
        Progress catalog state next)
    (success : computation anchor.1 state = .ok result) :
    Progress catalog state result.2 := by
  rcases anchor with ⟨value, anchorState⟩
  rcases result with ⟨result, next⟩
  exact invariant value state result next success


private theorem allocateExpressionId_success_origins_progress
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.refl state) success

private theorem allocateStatementId_success_origins_progress
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.refl state) success

private theorem state_fresh_success_origins_progress
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog) (Progress.refl state)
    success

private theorem allocateHiddenLocal_success_origins_progress
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.refl state) success

private theorem addRequirementWithId_success_origins_progress
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.addRequirementWithId state predicate) success

private theorem addRequirementsWithIds_success_origins_progress
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.addRequirementsWithIds state predicates) success

private theorem allocateBinder_success_origins_progress
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.refl state) success

private theorem freshDataConstructorInstantiation_success_origins_progress
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.freshDataConstructorInstantiation dataType constructor
      state) success

private theorem freshTypes_success_origins_progress
    {count : Nat} {state next : State} {types : List Ty}
    (success : freshTypes count state = (types, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.freshTypes count state) success

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
    Progress catalog state result.snd := by
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
  exact ProgressFields.expression _ _ _

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
    Progress catalog state result.snd := by
  rw [← success]
  exact ProgressFields.expression _ _ _

private theorem pure_pair_result_origins_progress {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : Progress catalog initial next)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    Progress catalog initial result.snd := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_origins_progress {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : Progress catalog initial state)
    (success : (value, state.restoreLexicalScope scope) = result) :
    Progress catalog initial result.snd := by
  rw [← success]
  exact Progress.trans subset
    (Progress.refl state)


set_option maxHeartbeats 2000000 in
private theorem inferFuel_origins_progress_internal :
    (∀ fuel context expression expected state,
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesOrigins (context.signatures.functions.map (·.id)) BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesOrigins (context.signatures.functions.map (·.id)) StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesOrigins (context.signatures.functions.map (·.id)) InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesOrigins (context.signatures.functions.map (·.id)) (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      PreservesOrigins (context.signatures.functions.map (·.id)) MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesOrigins at *
    intro result success
    have statementIdSubset :=
      allocateStatementId_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) statementIdEq
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
      syntheticTuple_result_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_origins_progress casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_origins_progress bodySubset (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply ProgressFields.trans (second := ProgressFields.statement _ _ _)
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _)
      | skip
    all_goals grind [ProgressFields.trans]
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesOrigins at *
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
      Progress.unify (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply ProgressFields.trans (second := ProgressFields.statement _ _ _)
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _)
      | skip
    all_goals grind [ProgressFields.trans]
  case case67 =>
    unfold PreservesOrigins at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesOrigins at *
    intro result success
    try exact Progress.localIdentifier (by assumption) (by assumption) (by assumption) success
  all_goals cataloged_call_context
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
    all_goals try have unifiedSubset :=
      Progress.unify (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have expressionIdSubset :=
      allocateExpressionId_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have statementIdSubset :=
      allocateStatementId_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have freshSubset :=
      state_fresh_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have hiddenLocalSubset :=
      allocateHiddenLocal_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have requirementSubset :=
      addRequirementWithId_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have requirementsSubset :=
      addRequirementsWithIds_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have binderSubset :=
      allocateBinder_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals have constructorProgress :=
      Progress.freshDataConstructorInstantiation (catalog := context.signatures.functions.map (·.id))
    all_goals try have constructorSubset :=
      freshDataConstructorInstantiation_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by
        assumption)
    all_goals try have typesSubset :=
      freshTypes_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have recordSubset :=
      Progress.recordExpressionWithExpected (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try exact ProgressFields.trans expressionIdSubset recordSubset
    all_goals try have issuedRecord :=
      (Progress.addRequirementWithId (catalog := (context.signatures.functions.map (·.id))) _ _).trans recordSubset
    all_goals try have batchRecord :=
      (Progress.addRequirementsWithIds (catalog := (context.signatures.functions.map (·.id))) _ _).trans recordSubset
    all_goals try exact ProgressFields.trans expressionIdSubset (ProgressFields.trans (Progress.addRequirementWithId (catalog := (context.signatures.functions.map (·.id))) _ _) recordSubset)
    all_goals try exact ProgressFields.trans expressionIdSubset (ProgressFields.trans (Progress.addRequirementsWithIds (catalog := (context.signatures.functions.map (·.id))) _ _) recordSubset)
    all_goals try have lambdaSubset :=
      Progress.bindLambdaParameters (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try
      have afterLambdaSubset := Progress.trans lambdaSubset
        (Progress.unify (catalog := (context.signatures.functions.map (·.id))) (by assumption))
    all_goals try have patternSubset :=
      Progress.inferMatchPatternFuel (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have unarySubset :=
      Progress.inferUnaryOperator (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have binarySubset :=
      Progress.inferBinaryOperator (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have expectedSubset :=
      Progress.withExpected (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have applicationSubset :=
      Progress.applyFunctionType (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have builtinSubset :=
      Progress.recordBuiltinFunctionCall (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.addRequirementWithId (catalog := (context.signatures.functions.map (·.id))) _ _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals try apply ProgressFields.trans (second := Progress.selectAndRecord (by assumption) (by first | exact functionsNamed_success_subset_catalog (by assumption) | exact qualifiedFunctionsNamed_success_subset_catalog (by assumption)) _ _)
    all_goals try apply ProgressFields.trans (second := Progress.selectFitAndRecord (by assumption) (by assumption) (by first | exact functionsNamed_success_subset_catalog (by assumption) | exact qualifiedFunctionsNamed_success_subset_catalog (by assumption)) _ _)
    all_goals first
      | apply ProgressFields.trans (second := ProgressFields.statement _ _ _)
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _)
      | skip
    all_goals grind
      [ProgressFields.trans,
        Progress.addRequirementWithId,
        Progress.addRequirementsWithIds,
        Progress.freshDataConstructorInstantiation,
        Progress.freshTypes,

        Progress.recordSelectedCallResult,
        Progress.recordSelectedCall,
        Progress.recordIndirectCall, Progress.recordStatement, Progress.modifyStatementNode]


theorem inferExprFuel_origins_progress
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2 := by
  exact inferFuel_origins_progress_internal.1 fuel context expression
    expected state result success

theorem inferConstructorApplicationFuel_origins_progress
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2 := by
  exact inferFuel_origins_progress_internal.2.1 fuel context source id
    instantiation arguments expected state result success

theorem inferConstructorArgumentsFuel_origins_progress
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.1 fuel context sources
    expected state result success

theorem inferStatementsFuel_origins_progress
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.1 fuel context
    statements expectedReturn state result success

theorem inferStatementFuel_origins_progress
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.1 fuel context
    statement expectedReturn state result success

theorem inferForItemsFuel_origins_progress
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.1 fuel context
    items state result success

theorem inferForItemFuel_origins_progress
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.1 fuel context
    item state result success

theorem inferPlaceFuel_origins_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.1 fuel
    context target state result success

theorem inferAssignedValueFuel_origins_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.1 fuel
    context target operator value state result success

theorem inferExprsFuel_origins_progress
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.2.1 fuel
    context expressions state result success

theorem inferMatchCasesFuel_origins_progress
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state result success

/-- The actual traversal preserves call emitters through nested lexical scopes. -/
theorem inferStatementsFuel_origins
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : Detail.BlockResult}
    (accepted : Detail.inferStatementsFuel fuel context statements expectedReturn state = .ok result)
    (origins : Origins (context.signatures.functions.map (·.id)) state) : Origins (context.signatures.functions.map (·.id)) result.state :=
  inferStatementsFuel_origins_progress accepted origins

theorem initial_origins (catalog : List Resolved.DeclarationId) (owner : Resolved.DeclarationId)
    (parameters : TypeSystem.Environment) (comptime : List Bool) :
    Origins catalog (State.initial owner parameters comptime) := by
  intro requirement member
  cases member

/-- The original initialized inference call supplies every direct emitter;
no node provenance premise is needed at this boundary. -/
theorem initializedStatements_origins
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {owner : Resolved.DeclarationId}
    {parameters : TypeSystem.Environment} {comptime : List Bool}
    {result : Detail.BlockResult}
    (accepted : Detail.inferStatementsFuel fuel context statements expectedReturn
      (State.initial owner parameters comptime) = .ok result) : Origins (context.signatures.functions.map (·.id)) result.state :=
  inferStatementsFuel_origins accepted (initial_origins _ _ _ _)

end Solcore.Frontend.SourceInference.CatalogedDirectCallEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.DirectCallPredicateIssuance
/-! Selected declaration candidates retain their actual ordered raw
requirement IDs and predicates before any source body typing theorem. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.DirectCallPredicateEvents
open TypeSystem Detail

theorem tryFunctionCandidate_correspond
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State} {signature : ProgramFunctionSignature}
    {result : CandidateAttemptResult}
    (accepted : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    RequirementPredicatesCorrespond result.state.requirements
      result.instantiation.predicates result.signatureRequirements := by
  unfold tryFunctionCandidate at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals exact State.addRequirementsWithIds_correspond _ _

theorem selectFunctionCandidateFrom_correspond
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    RequirementPredicatesCorrespond result.state.requirements
      result.instantiation.predicates result.signatureRequirements := by
  obtain ⟨signature, _, selected⟩ := selectFunctionCandidateFrom_success_candidate accepted
  exact tryFunctionCandidate_correspond selected

end Solcore.Frontend.SourceInference.DirectCallPredicateEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.DirectCallPredicateProgress
/-! Preserve each direct-call requirement row together with its issuing call
and the exact predicate on that call. Catalog membership distinguishes the
ordinary selected declaration from inserted implementation-method edges. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.Frontend.SourceInference.DirectCallPredicateEvents
open TypeSystem Detail DirectCallEvents

def HasCall (catalog : List Resolved.DeclarationId) (nodes : List Node) (requirement : Requirement) : Prop :=
  ∃ node, .expression node ∈ nodes ∧
    ∃ callee arguments instantiation,
      node.form = .call callee arguments (.declaration instantiation) ∧
      requirement.id ∈ node.requirements ∧ instantiation.declaration ∈ catalog ∧
      requirement.predicate ∈ instantiation.predicates

def OriginsFields (catalog : List Resolved.DeclarationId) (nodes : List Node)
    (direct : List RequirementId) (requirements : List Requirement) : Prop :=
  ∀ id ∈ direct, ∃ requirement ∈ requirements, requirement.id = id ∧ HasCall catalog nodes requirement
abbrev Origins (catalog : List Resolved.DeclarationId) (state : State) : Prop :=
  OriginsFields catalog state.nodes state.directCallRequirements state.requirements

def ProgressFields (catalog : List Resolved.DeclarationId)
    (beforeNodes : List Node) (beforeDirect : List RequirementId) (beforeRequirements : List Requirement)
    (afterNodes : List Node) (afterDirect : List RequirementId) (afterRequirements : List Requirement) : Prop :=
  OriginsFields catalog beforeNodes beforeDirect beforeRequirements →
    OriginsFields catalog afterNodes afterDirect afterRequirements
abbrev Progress (catalog : List Resolved.DeclarationId) (before after : State) : Prop :=
  ProgressFields catalog before.nodes before.directCallRequirements before.requirements
    after.nodes after.directCallRequirements after.requirements

variable {catalog : List Resolved.DeclarationId}

theorem HasCall.mono {before after : List Node} {requirement : Requirement}
    (call : HasCall catalog before requirement) (included : before ⊆ after) :
    HasCall catalog after requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued, cataloged, predicate⟩ := call
  exact ⟨node, included member, callee, arguments, instantiation, form, issued, cataloged, predicate⟩

theorem HasCall.modifyStatementNode {state : State} {requirement : Requirement}
    (call : HasCall catalog state.nodes requirement)
    (id : StatementId) (modify : StatementNode → StatementNode) :
    HasCall catalog (state.modifyStatementNode id modify).nodes requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued, cataloged, predicate⟩ := call
  exact ⟨node, List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, instantiation, form, issued, cataloged, predicate⟩

theorem HasCall.modifyExpressionNode {state : State} {requirement : Requirement}
    (call : HasCall catalog state.nodes requirement)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode)
    (form : ∀ node, (modify node).form = node.form)
    (requirements : ∀ node, node.requirements ⊆ (modify node).requirements) :
    HasCall catalog (state.modifyExpressionNode id modify).nodes requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, original, issued, cataloged, predicate⟩ := call
  by_cases selected : node.id = id
  · refine ⟨{ modify node with id }, List.mem_map.mpr ⟨.expression node, member, ?_⟩,
      callee, arguments, instantiation, (form node).trans original, requirements node issued, cataloged, predicate⟩
    simp [selected]
  · refine ⟨node, List.mem_map.mpr ⟨.expression node, member, ?_⟩,
      callee, arguments, instantiation, original, issued, cataloged, predicate⟩
    simp [selected]

theorem HasCall.attachExpressionCoercions {state : State} {requirement : Requirement}
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
    {br mr ar : List Requirement}
    (first : ProgressFields catalog bn bd br mn md mr)
    (second : ProgressFields catalog mn md mr an ad ar) :
    ProgressFields catalog bn bd br an ad ar := fun origins => second (first origins)

theorem ProgressFields.mono {bn an : List Node} {bd ad : List RequirementId}
    {br ar : List Requirement}
    (nodes : ∀ requirement, HasCall catalog bn requirement → HasCall catalog an requirement)
    (direct : ad ⊆ bd) (requirements : br ⊆ ar) :
    ProgressFields catalog bn bd br an ad ar := by
  intro origins id member
  obtain ⟨row, present, same, call⟩ := origins id (direct member)
  exact ⟨row, requirements present, same, nodes row call⟩

theorem ProgressFields.statement (nodes : List Node) (direct : List RequirementId)
    (statement : StatementNode) {requirements : List Requirement} :
    ProgressFields catalog nodes direct requirements (nodes ++ [.statement statement]) direct requirements :=
  ProgressFields.mono (fun _ call => call.mono (List.subset_append_left _ _)) (fun _ h => h) (fun _ h => h)

theorem ProgressFields.expression (nodes : List Node) (direct : List RequirementId)
    (expression : ExpressionNode) {requirements : List Requirement} :
    ProgressFields catalog nodes direct requirements (nodes ++ [.expression expression]) direct requirements :=
  ProgressFields.mono (fun _ call => call.mono (List.subset_append_left _ _)) (fun _ h => h) (fun _ h => h)

namespace Progress

theorem refl (state : State) : Progress catalog state state := fun origins => origins

theorem trans {before middle after : State}
    (first : Progress catalog before middle) (second : Progress catalog middle after) : Progress catalog before after :=
  ProgressFields.trans first second

theorem of_nodes_eq {before after : State} (nodes : after.nodes = before.nodes)
    (direct : Unchanged before after) (requirements : before.requirements ⊆ after.requirements) :
    Progress catalog before after :=
  ProgressFields.mono (fun _ call => by simpa only [nodes] using call)
    (fun _ h => by simpa only [direct] using h) requirements

theorem recordStatement (state : State) (node : StatementNode) :
    Progress catalog state (state.recordNode (.statement node)) :=
  ProgressFields.statement _ _ _

theorem modifyStatementNode (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode) :
    Progress catalog state (state.modifyStatementNode id modify) :=
  ProgressFields.mono (fun _ call => call.modifyStatementNode id modify) (fun _ h => h) (fun _ h => h)

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Progress catalog state (state.addRequirementWithId predicate).2 := of_nodes_eq rfl rfl (State.addRequirementWithId_requirements_subset _ _)

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress catalog state (state.addRequirementsWithIds predicates).2 :=
  of_nodes_eq (State.addRequirementsWithIds_nodes _ _) (State.addRequirementsWithIds_direct_eq _ _) (State.addRequirementsWithIds_requirements_subset _ _)

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
    (withExpected_direct_eq fit) (Detail.withExpected_requirements_subset fit)).trans (ProgressFields.expression _ _ _)

theorem unify {state next : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok next) : Progress catalog state next :=
  of_nodes_eq (unify_occurrenceState_eq accepted).1 (unify_direct_unchanged accepted) (Detail.unify_requirements_subset accepted)

theorem withExpected {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    Progress catalog state result.state :=
  of_nodes_eq (withExpected_occurrenceState_eq accepted).1 (withExpected_direct_eq accepted) (Detail.withExpected_requirements_subset accepted)

theorem inferUnaryOperator
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    Progress catalog state result.state :=
  of_nodes_eq (inferUnaryOperator_occurrenceState_eq accepted).1 (inferUnaryOperator_direct_unchanged accepted) (Detail.inferUnaryOperator_requirements_subset accepted)

theorem inferBinaryOperator
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    Progress catalog state result.state :=
  of_nodes_eq (inferBinaryOperator_occurrenceState_eq accepted).1 (inferBinaryOperator_direct_unchanged accepted) (Detail.inferBinaryOperator_requirements_subset accepted)

theorem applyFunctionType {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (accepted : Detail.applyFunctionType context call calleeType arguments expected state = .ok result) :
    Progress catalog state result.state :=
  of_nodes_eq (applyFunctionType_occurrenceState_eq accepted).1 (applyFunctionType_direct_unchanged accepted) (Detail.applyFunctionType_requirements_subset accepted)

theorem bindLambdaParameters {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State} {result : List TypedBinder × List Ty × State}
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    Progress catalog state result.2.2 :=
  of_nodes_eq (bindLambdaParameters_occurrenceState_eq accepted).1 (bindLambdaParameters_direct_unchanged accepted) (Detail.bindLambdaParameters_requirements_subset accepted)

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress catalog state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  of_nodes_eq (Detail.freshDataConstructorInstantiation_nodes _ _ _)
    (freshDataConstructorInstantiation_direct_unchanged _ _ _)
    (Detail.freshDataConstructorInstantiation_requirements_subset _ _ _)

theorem freshTypes (count : Nat) (state : State) : Progress catalog state (Detail.freshTypes count state).2 :=
  of_nodes_eq (Detail.freshTypes_nodes _ _) (freshTypes_direct_unchanged _ _) (Detail.freshTypes_requirements_subset _ _)

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress catalog state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  intro origins requirement member
  have direct := recordSelectedCallResult_direct_unchanged source callee name arguments attempt result trailing state
  rw [direct] at member
  obtain ⟨row, present, same, call⟩ := origins requirement member
  refine ⟨row, Detail.recordSelectedCallResult_requirements_subset _ _ _ _ _ _ _ _ present, same, ?_⟩
  apply (call.attachExpressionCoercions attempt.argumentCoercions).mono
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
  obtain ⟨row, present, same, call⟩ := origins requirement member
  exact ⟨row, Detail.recordBuiltinFunctionCall_requirements_subset accepted present, same,
    call.mono (by rw [nodes]; exact List.subset_append_left _ _)⟩

theorem inferMatchPatternFuel {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress catalog state result.2 :=
  of_nodes_eq (inferMatchPatternFuel_occurrenceState_eq accepted).1 (inferMatchPatternFuel_direct_unchanged accepted) (Detail.inferMatchPatternFuel_requirements_subset accepted)

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
    apply ProgressFields.mono (fun _ call => call) (fun _ h => h)
    exact State.addRequirementsWithIds_requirements_subset
      { allocated with inference := { allocated.inference with
        next := (binder.scheme.instantiateWithSubstitution allocated.inference.next).next } } _

end Progress
end Solcore.Frontend.SourceInference.DirectCallPredicateEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.DirectCallPredicateCandidate
/-! The actual selected candidate supplies the ordinary catalog declaration
before its newly issued requirement batch is recorded on the source call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.DirectCallPredicateEvents
open TypeSystem Detail DirectCallEvents
variable {catalog : List Resolved.DeclarationId}

theorem correspond_member {requirements : List Requirement}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (corresponds : RequirementPredicatesCorrespond requirements predicates ids)
    {id : RequirementId} (member : id ∈ ids) :
    ∃ predicate ∈ predicates, ({ id, predicate } : Requirement) ∈ requirements := by
  induction corresponds with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | rest
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨predicate, present, row⟩ := ih rest
      exact ⟨predicate, List.mem_cons_of_mem _ present, row⟩

/-- Recording discharges the exact pending batch together with its actual
selected declaration. No typing judgment is used to identify that declaration. -/
theorem recordSelectedCallResult_pending
    {before state : State} {attempt : CandidateAttemptResult}
    (nodes : state.nodes = before.nodes)
    (direct : state.directCallRequirements = before.directCallRequirements ++ attempt.signatureRequirements)
    (cataloged : attempt.instantiation.declaration ∈ catalog)
    (requirements : before.requirements ⊆ state.requirements)
    (corresponds : RequirementPredicatesCorrespond state.requirements
      attempt.instantiation.predicates attempt.signatureRequirements)
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (result : InferredExpression) (trailing : List CoercionStep) :
    Progress catalog before (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  intro origins requirement member
  rw [recordSelectedCallResult_direct_unchanged, direct] at member
  rcases List.mem_append.mp member with prior | fresh
  · obtain ⟨row, present, same, call⟩ := origins requirement prior
    have original : HasCall catalog state.nodes row := by
      rw [nodes]
      exact call
    refine ⟨row, Detail.recordSelectedCallResult_requirements_subset _ _ _ _ _ _ _ _
      (requirements present), same, ?_⟩
    apply (original.attachExpressionCoercions attempt.argumentCoercions).mono
    intro node present
    exact List.mem_append_left _ (List.mem_append_left _ present)
  · obtain ⟨predicate, predicateMem, row⟩ := correspond_member corresponds fresh
    refine ⟨{ id := requirement, predicate },
      Detail.recordSelectedCallResult_requirements_subset _ _ _ _ _ _ _ _ row, rfl, ?_⟩
    let calleeId := (Detail.attachExpressionCoercions state attempt.argumentCoercions).allocateExpressionId.1
    let callNode : ExpressionNode := {
      id := result.id, span := source.span, type := result.type
      form := .call calleeId (arguments.map (·.id)) (.declaration attempt.instantiation)
      requirements := coercionRequirements attempt.callCoercions ++ attempt.signatureRequirements ++
        coercionRequirements trailing
      coercions := attempt.callCoercions ++ trailing }
    refine ⟨callNode, ?_, calleeId, arguments.map (·.id), attempt.instantiation, rfl, ?_, cataloged, predicateMem⟩
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (List.mem_append_right _ fresh)

theorem selected_catalog
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {attempt : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok attempt)
    (cataloged : candidates ⊆ context.signatures.functions) :
    attempt.instantiation.declaration ∈ context.signatures.functions.map (·.id) := by
  obtain ⟨signature, present, selected⟩ := selectFunctionCandidateFrom_success_candidate accepted
  rw [tryFunctionCandidate_some_instantiation selected]
  exact List.mem_map.mpr ⟨signature, cataloged present, rfl⟩

namespace Progress

theorem selectAndRecord
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {attempt : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok attempt)
    (cataloged : candidates ⊆ context.signatures.functions)
    (source callee : Syntax.Expr) :
    Progress (context.signatures.functions.map (·.id)) state
      (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult_pending (selectFunctionCandidateFrom_occurrenceState_eq accepted).1
    (selectFunctionCandidateFrom_direct_batch accepted) (selected_catalog accepted cataloged)
    (Detail.selectFunctionCandidateFrom_requirements_subset accepted)
    (selectFunctionCandidateFrom_correspond accepted)
    source callee name arguments _ _

theorem selectFitAndRecord
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected selectedExpected : Option Ty} {state : State}
    {attempt : CandidateAttemptResult} {fitted : ExpectationResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call selectedExpected state = .ok attempt)
    (fit : Detail.withExpected context attempt.state attempt.result expected = .ok fitted)
    (cataloged : candidates ⊆ context.signatures.functions)
    (source callee : Syntax.Expr) :
    Progress (context.signatures.functions.map (·.id)) state
      (Detail.recordSelectedCallResult source callee name arguments attempt
        fitted.expression fitted.coercions fitted.state).2 :=
  recordSelectedCallResult_pending
    ((withExpected_occurrenceState_eq fit).1.trans (selectFunctionCandidateFrom_occurrenceState_eq accepted).1)
    ((withExpected_direct_eq fit).trans (selectFunctionCandidateFrom_direct_batch accepted))
    (selected_catalog accepted cataloged)
    ((Detail.selectFunctionCandidateFrom_requirements_subset accepted).trans
      (Detail.withExpected_requirements_subset fit))
    (RequirementPredicatesCorrespond.mono
      (Detail.withExpected_requirements_subset fit)
      (selectFunctionCandidateFrom_correspond accepted)) source callee name arguments _ _

end Progress
end Solcore.Frontend.SourceInference.DirectCallPredicateEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.DirectCallPredicateInference
/-! Every direct-call requirement issued by successful inference retains an
actual raw ledger row, declaration-call predicate and selected ordinary declaration through all eleven recursive inference paths. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.SourceInference.DirectCallPredicateEvents
open TypeSystem Detail
variable {catalog : List Resolved.DeclarationId}

/-- Give the mutual recursor's inaccessible context binder a stable local name;
this changes only elaboration names and does not introduce any proof premise. -/
elab "predicate_call_context" : tactic => Lean.Elab.Tactic.withMainContext do
  for declaration in ← Lean.getLCtx do
    if declaration.type.isConstOf ``Context then
      let goal ← Lean.Elab.Tactic.getMainGoal
      Lean.Elab.Tactic.replaceMainGoal [← goal.rename declaration.fvarId `context]
      return
  throwError "missing actual inference context"

@[simp] private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private def PreservesOrigins (catalog : List Resolved.DeclarationId) {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Progress catalog initial (stateOf result)

private theorem pair_success_origins_progress {alpha : Type}
    {operation : alpha × State} {value : alpha} {next initial : State}
    (operationSubset : Progress catalog initial operation.2)
    (success : operation = (value, next)) :
    Progress catalog initial next := by
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
        Progress catalog initial next)
    (invariant : ∀ value state result next,
      computation value state = .ok (result, next) →
        Progress catalog state next)
    (success : computation anchor.1 state = .ok result) :
    Progress catalog state result.2 := by
  rcases anchor with ⟨value, anchorState⟩
  rcases result with ⟨result, next⟩
  exact invariant value state result next success


private theorem allocateExpressionId_success_origins_progress
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.refl state) success

private theorem allocateStatementId_success_origins_progress
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.refl state) success

private theorem state_fresh_success_origins_progress
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog) (Progress.refl state)
    success

private theorem allocateHiddenLocal_success_origins_progress
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.refl state) success

private theorem addRequirementWithId_success_origins_progress
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.addRequirementWithId state predicate) success

private theorem addRequirementsWithIds_success_origins_progress
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.addRequirementsWithIds state predicates) success

private theorem allocateBinder_success_origins_progress
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.refl state) success

private theorem freshDataConstructorInstantiation_success_origins_progress
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.freshDataConstructorInstantiation dataType constructor
      state) success

private theorem freshTypes_success_origins_progress
    {count : Nat} {state next : State} {types : List Ty}
    (success : freshTypes count state = (types, next)) :
    Progress catalog state next :=
  pair_success_origins_progress (catalog := catalog)
    (Progress.freshTypes count state) success

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
    Progress catalog state result.snd := by
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
  exact ProgressFields.expression _ _ _

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
    Progress catalog state result.snd := by
  rw [← success]
  exact ProgressFields.expression _ _ _

private theorem pure_pair_result_origins_progress {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : Progress catalog initial next)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    Progress catalog initial result.snd := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_origins_progress {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : Progress catalog initial state)
    (success : (value, state.restoreLexicalScope scope) = result) :
    Progress catalog initial result.snd := by
  rw [← success]
  exact Progress.trans subset
    (Progress.refl state)


set_option maxHeartbeats 2000000 in
private theorem inferFuel_origins_progress_internal :
    (∀ fuel context expression expected state,
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesOrigins (context.signatures.functions.map (·.id)) BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesOrigins (context.signatures.functions.map (·.id)) StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesOrigins (context.signatures.functions.map (·.id)) InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesOrigins (context.signatures.functions.map (·.id)) (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      PreservesOrigins (context.signatures.functions.map (·.id)) MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesOrigins (context.signatures.functions.map (·.id)) MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesOrigins at *
    intro result success
    have statementIdSubset :=
      allocateStatementId_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) statementIdEq
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
      syntheticTuple_result_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_origins_progress casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_origins_progress bodySubset (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply ProgressFields.trans (second := ProgressFields.statement _ _ _)
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _)
      | skip
    all_goals grind [ProgressFields.trans]
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesOrigins at *
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
      Progress.unify (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals first
      | apply ProgressFields.trans (second := ProgressFields.statement _ _ _)
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _)
      | skip
    all_goals grind [ProgressFields.trans]
  case case67 =>
    unfold PreservesOrigins at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesOrigins at *
    intro result success
    try exact Progress.localIdentifier (by assumption) (by assumption) (by assumption) success
  all_goals predicate_call_context
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
    all_goals try have unifiedSubset :=
      Progress.unify (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have expressionIdSubset :=
      allocateExpressionId_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have statementIdSubset :=
      allocateStatementId_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have freshSubset :=
      state_fresh_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have hiddenLocalSubset :=
      allocateHiddenLocal_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have requirementSubset :=
      addRequirementWithId_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have requirementsSubset :=
      addRequirementsWithIds_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have binderSubset :=
      allocateBinder_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals have constructorProgress :=
      Progress.freshDataConstructorInstantiation (catalog := context.signatures.functions.map (·.id))
    all_goals try have constructorSubset :=
      freshDataConstructorInstantiation_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by
        assumption)
    all_goals try have typesSubset :=
      freshTypes_success_origins_progress (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have recordSubset :=
      Progress.recordExpressionWithExpected (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try exact ProgressFields.trans expressionIdSubset recordSubset
    all_goals try have issuedRecord :=
      (Progress.addRequirementWithId (catalog := (context.signatures.functions.map (·.id))) _ _).trans recordSubset
    all_goals try have batchRecord :=
      (Progress.addRequirementsWithIds (catalog := (context.signatures.functions.map (·.id))) _ _).trans recordSubset
    all_goals try exact ProgressFields.trans expressionIdSubset (ProgressFields.trans (Progress.addRequirementWithId (catalog := (context.signatures.functions.map (·.id))) _ _) recordSubset)
    all_goals try exact ProgressFields.trans expressionIdSubset (ProgressFields.trans (Progress.addRequirementsWithIds (catalog := (context.signatures.functions.map (·.id))) _ _) recordSubset)
    all_goals try have lambdaSubset :=
      Progress.bindLambdaParameters (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try
      have afterLambdaSubset := Progress.trans lambdaSubset
        (Progress.unify (catalog := (context.signatures.functions.map (·.id))) (by assumption))
    all_goals try have patternSubset :=
      Progress.inferMatchPatternFuel (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have unarySubset :=
      Progress.inferUnaryOperator (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have binarySubset :=
      Progress.inferBinaryOperator (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have expectedSubset :=
      Progress.withExpected (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have applicationSubset :=
      Progress.applyFunctionType (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try have builtinSubset :=
      Progress.recordBuiltinFunctionCall (catalog := (context.signatures.functions.map (·.id))) (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.addRequirementWithId (catalog := (context.signatures.functions.map (·.id))) _ _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.recordStatement _ _
    all_goals dsimp only [Progress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall]
    all_goals dsimp only [Progress, State.recordNode, State.allocateExpressionId,
      State.allocateStatementId, State.allocateHiddenLocal, State.allocateBinder,
      State.restoreLexicalScope, State.withLocals, State.fresh,
      Detail.recordExpression, Detail.recordIndirectCall] at *
    all_goals try apply ProgressFields.trans (second := Progress.selectAndRecord (by assumption) (by first | exact functionsNamed_success_subset_catalog (by assumption) | exact qualifiedFunctionsNamed_success_subset_catalog (by assumption)) _ _)
    all_goals try apply ProgressFields.trans (second := Progress.selectFitAndRecord (by assumption) (by assumption) (by first | exact functionsNamed_success_subset_catalog (by assumption) | exact qualifiedFunctionsNamed_success_subset_catalog (by assumption)) _ _)
    all_goals first
      | apply ProgressFields.trans (second := ProgressFields.statement _ _ _)
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _)
      | skip
    all_goals grind
      [ProgressFields.trans,
        Progress.addRequirementWithId,
        Progress.addRequirementsWithIds,
        Progress.freshDataConstructorInstantiation,
        Progress.freshTypes,

        Progress.recordSelectedCallResult,
        Progress.recordSelectedCall,
        Progress.recordIndirectCall, Progress.recordStatement, Progress.modifyStatementNode]


theorem inferExprFuel_origins_progress
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2 := by
  exact inferFuel_origins_progress_internal.1 fuel context expression
    expected state result success

theorem inferConstructorApplicationFuel_origins_progress
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2 := by
  exact inferFuel_origins_progress_internal.2.1 fuel context source id
    instantiation arguments expected state result success

theorem inferConstructorArgumentsFuel_origins_progress
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.1 fuel context sources
    expected state result success

theorem inferStatementsFuel_origins_progress
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.1 fuel context
    statements expectedReturn state result success

theorem inferStatementFuel_origins_progress
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.1 fuel context
    statement expectedReturn state result success

theorem inferForItemsFuel_origins_progress
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.1 fuel context
    items state result success

theorem inferForItemFuel_origins_progress
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.1 fuel context
    item state result success

theorem inferPlaceFuel_origins_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.1 fuel
    context target state result success

theorem inferAssignedValueFuel_origins_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.1 fuel
    context target operator value state result success

theorem inferExprsFuel_origins_progress
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.2.1 fuel
    context expressions state result success

theorem inferMatchCasesFuel_origins_progress
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    Progress (context.signatures.functions.map (·.id)) state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state result success

/-- The actual traversal preserves call emitters through nested lexical scopes. -/
theorem inferStatementsFuel_origins
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : Detail.BlockResult}
    (accepted : Detail.inferStatementsFuel fuel context statements expectedReturn state = .ok result)
    (origins : Origins (context.signatures.functions.map (·.id)) state) : Origins (context.signatures.functions.map (·.id)) result.state :=
  inferStatementsFuel_origins_progress accepted origins

theorem initial_origins (catalog : List Resolved.DeclarationId) (owner : Resolved.DeclarationId)
    (parameters : TypeSystem.Environment) (comptime : List Bool) :
    Origins catalog (State.initial owner parameters comptime) := by
  intro requirement member
  cases member

/-- The original initialized inference call supplies every direct emitter;
no node provenance premise is needed at this boundary. -/
theorem initializedStatements_origins
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {owner : Resolved.DeclarationId}
    {parameters : TypeSystem.Environment} {comptime : List Bool}
    {result : Detail.BlockResult}
    (accepted : Detail.inferStatementsFuel fuel context statements expectedReturn
      (State.initial owner parameters comptime) = .ok result) : Origins (context.signatures.functions.map (·.id)) result.state :=
  inferStatementsFuel_origins accepted (initial_origins _ _ _ _)

end Solcore.Frontend.SourceInference.DirectCallPredicateEvents
end
