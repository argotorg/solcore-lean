import Solcore.Frontend.SourceInference.ClassifiedCallHelpers
import Solcore.Frontend.SourceInference.DirectCallCandidateOrigins

/-! Classified templates are a subset of actual declaration-call IDs. The
relation follows only these two inventories, so unrelated state changes are
transparent. Generalized allocation is the sole operation adding templates. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.ClassifiedCallEvents
open TypeSystem Detail

def Classified (state : State) : Prop :=
  state.localSchemeAssumptions ⊆ state.directCallRequirements

def ProgressFields (beforeTemplates beforeDirect afterTemplates afterDirect : List RequirementId) : Prop :=
  (beforeTemplates ⊆ beforeDirect) → (afterTemplates ⊆ afterDirect)
abbrev Progress (before after : State) : Prop :=
  ProgressFields before.localSchemeAssumptions before.directCallRequirements
    after.localSchemeAssumptions after.directCallRequirements

theorem ProgressFields.trans {bt bd mt md ats ad : List RequirementId}
    (first : ProgressFields bt bd mt md) (second : ProgressFields mt md ats ad) :
    ProgressFields bt bd ats ad := fun prior => second (first prior)

theorem ProgressFields.refl (templates direct : List RequirementId) :
    ProgressFields templates direct templates direct := id

namespace Progress

theorem refl (state : State) : Progress state state := id

theorem trans {before middle after : State} (first : Progress before middle) (second : Progress middle after) :
    Progress before after := fun prior => second (first prior)

theorem of_eq {before after : State}
    (templates : after.localSchemeAssumptions = before.localSchemeAssumptions)
    (direct : after.directCallRequirements = before.directCallRequirements) : Progress before after := by
  intro classified
  change after.localSchemeAssumptions ⊆ after.directCallRequirements
  rwa [templates, direct]

theorem of_direct_extension {before after : State}
    (templates : after.localSchemeAssumptions = before.localSchemeAssumptions)
    (direct : before.directCallRequirements ⊆ after.directCallRequirements) : Progress before after := by
  intro classified requirement member
  exact direct (classified (templates ▸ member))

theorem recordStatement (state : State) (node : StatementNode) :
    Progress state (state.recordNode (.statement node)) := refl _
theorem modifyStatementNode (state : State) (id : StatementId) (modify : StatementNode → StatementNode) :
    Progress state (state.modifyStatementNode id modify) := refl _

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Progress state (state.addRequirementWithId predicate).2 := refl _
theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress state (state.addRequirementsWithIds predicates).2 :=
  of_eq (Unchanged.addRequirementsWithIds _ _) (State.addRequirementsWithIds_direct_eq _ _)

end Progress

namespace Progress
theorem recordExpression (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId) (coercions : List CoercionStep)
    (state : State) (start : Option Nat := none) :
    Progress state (Detail.recordExpression source expression form requirements coercions state start).2 :=
  of_eq (recordExpression_classified_unchanged _ _ _ _ _ _ _) (DirectCallEvents.recordExpression_direct_unchanged _ _ _ _ _ _ _)

theorem recordExpressionWithExpected
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {state : State} {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result) :
    Progress state result.2 :=
  of_eq (recordExpressionWithExpected_classified_unchanged accepted) (DirectCallEvents.recordExpressionWithExpected_direct_unchanged accepted)

theorem unify {state next : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok next) : Progress state next :=
  of_eq (unify_classified_unchanged accepted) (DirectCallEvents.unify_direct_unchanged accepted)

theorem withExpected {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    Progress state result.state :=
  of_eq (withExpected_classified_eq accepted) (withExpected_direct_eq accepted)

theorem inferUnaryOperator
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_eq (inferUnaryOperator_classified_unchanged accepted) (DirectCallEvents.inferUnaryOperator_direct_unchanged accepted)

theorem inferBinaryOperator
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_eq (inferBinaryOperator_classified_unchanged accepted) (DirectCallEvents.inferBinaryOperator_direct_unchanged accepted)

theorem applyFunctionType {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (accepted : Detail.applyFunctionType context call calleeType arguments expected state = .ok result) :
    Progress state result.state :=
  of_eq (applyFunctionType_classified_unchanged accepted) (DirectCallEvents.applyFunctionType_direct_unchanged accepted)

theorem bindLambdaParameters {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State} {result : List TypedBinder × List Ty × State}
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    Progress state result.2.2 :=
  of_eq (bindLambdaParameters_classified_unchanged accepted) (DirectCallEvents.bindLambdaParameters_direct_unchanged accepted)

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  of_eq (freshDataConstructorInstantiation_classified_unchanged _ _ _) (DirectCallEvents.freshDataConstructorInstantiation_direct_unchanged _ _ _)

theorem freshTypes (count : Nat) (state : State) : Progress state (Detail.freshTypes count state).2 :=
  of_eq (freshTypes_classified_unchanged _ _) (DirectCallEvents.freshTypes_direct_unchanged _ _)

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 :=
  of_eq (recordSelectedCallResult_classified_unchanged _ _ _ _ _ _ _ _) (DirectCallEvents.recordSelectedCallResult_direct_unchanged _ _ _ _ _ _ _ _)

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    Progress attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  of_eq (recordSelectedCall_classified_unchanged _ _ _ _ _) (DirectCallEvents.recordSelectedCall_direct_unchanged _ _ _ _ _)

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    Progress result.state (Detail.recordIndirectCall source callee arguments result).2 :=
  of_eq (recordIndirectCall_classified_unchanged _ _ _ _) (DirectCallEvents.recordIndirectCall_direct_unchanged _ _ _ _)

theorem recordBuiltinFunctionCall
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Progress state result.2 :=
  of_eq (recordBuiltinFunctionCall_classified_unchanged accepted) (DirectCallEvents.recordBuiltinFunctionCall_direct_unchanged accepted)

theorem inferMatchPatternFuel {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress state result.2 :=
  of_eq (inferMatchPatternFuel_classified_unchanged accepted) (DirectCallEvents.inferMatchPatternFuel_direct_unchanged accepted)

theorem selectFunctionCandidateFrom
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : Detail.selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) : Progress state result.state := by
  apply of_direct_extension (selectFunctionCandidateFrom_classified_unchanged accepted)
  rw [DirectCallEvents.selectFunctionCandidateFrom_direct_batch accepted]
  exact List.subset_append_left _ _

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
  apply Progress.trans (middle := allocated)
  · rw [allocatedEq]; exact refl _
  · have recording := recordExpressionWithExpected recorded
    refine ProgressFields.trans ?_ recording
    simp only [Unchanged.addRequirementsWithIds, State.addRequirementsWithIds_direct_eq]
    exact refl _

end Progress
private theorem requirement_contains {ids : List RequirementId} {id : RequirementId}
    (member : ids.contains id = true) : id ∈ ids := by
  induction ids with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.contains_cons, Bool.or_eq_true] at member
    rcases member with same | later
    · apply List.mem_cons.mpr
      apply Or.inl
      have indices : id.index = head.index := by
        change (id.index == head.index) = true at same
        exact beq_iff_eq.mp same
      cases id; cases head; cases indices; rfl
    · exact List.mem_cons_of_mem _ (ih later)

/-- The generalizer selects templates only from genuine direct-call IDs. -/
theorem generalized_template_direct (state : State) (locals : TypeSystem.Environment)
    (cutoff : Nat) (type : Ty) (template : LocalSchemeRequirement)
    (member : template ∈ (Detail.generalizeValue state locals cutoff type).requirements) :
    template.templateRequirement ∈ state.directCallRequirements := by
  unfold Detail.generalizeValue at member
  dsimp only at member
  obtain ⟨raw, eligible, selected⟩ := List.mem_filterMap.mp member
  have classified := (List.mem_filter.mp eligible).2
  simp only [Bool.and_eq_true] at classified
  have direct := classified.1
  split at selected
  · cases selected
    exact requirement_contains direct
  · contradiction


/-- Adding exactly the templates selected by the real generalizer preserves
classification as declaration-call requirements. -/
theorem Progress.allocateGeneralized (state : State) (locals : Environment)
    (cutoff : Nat) (type : Ty) (name : String) (span : Option Syntax.SourceSpan) (comptime : Bool) :
    Progress state ((state.withLocals locals).allocateBinder name
      (generalizeValue state locals cutoff type).scheme span comptime
      (generalizeValue state locals cutoff type).requirements).2 := by
  intro classified requirement member
  rcases List.mem_append.mp member with old | added
  · exact classified old
  · obtain ⟨template, selected, same⟩ := List.mem_map.mp added
    subst requirement
    exact generalized_template_direct state locals cutoff type template selected

theorem ProgressFields.generalized (state : State) (locals : Environment) (cutoff : Nat) (type : Ty) :
    ProgressFields state.localSchemeAssumptions state.directCallRequirements
      (state.localSchemeAssumptions ++ (generalizeValue state locals cutoff type).requirements.map
        (fun requirement => requirement.templateRequirement)) state.directCallRequirements := by
  intro classified requirement member
  rcases List.mem_append.mp member with old | added
  · exact classified old
  · obtain ⟨template, selected, same⟩ := List.mem_map.mp added
    subst requirement
    exact generalized_template_direct state locals cutoff type template selected

theorem Progress.allocateEmpty (state : State) (name : String) (scheme : Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool) :
    Progress state (state.allocateBinder name scheme span comptime []).2 := by
  intro classified
  simpa [State.allocateBinder] using classified

end Solcore.Frontend.SourceInference.ClassifiedCallEvents
