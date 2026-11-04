import Solcore.Frontend.SourceInference.Internal.ExpressionProperties

/-!
# Local read origins

Local references keep the lookup that issued their requirements, and direct-call classification
follows the inference steps.
-/

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalReadRequirementOrigins
/-! Requirement identities issued by the actual local-reference branch. -/

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.Frontend.SourceInference
open TypeSystem

namespace State

/-- Every recorded direct-call identity names an allocated ledger row. -/
def DirectRequirementsAllocated (state : State) : Prop :=
  state.directCallRequirements ⊆ state.requirements.map Requirement.id

theorem addRequirementsWithIds_direct_eq (state : State)
    (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.directCallRequirements =
      state.directCallRequirements := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest ih =>
    exact ih (state.addRequirementWithId predicate).2

/-- A local lookup's fresh batch cannot contain an earlier direct-call ID. -/
theorem addRequirementsWithIds_not_direct (state : State)
    (predicates : List ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed)
    (allocated : state.DirectRequirementsAllocated)
    {id : RequirementId}
    (member : id ∈ (state.addRequirementsWithIds predicates).1) :
    id ∉ (state.addRequirementsWithIds predicates).2.directCallRequirements := by
  rw [addRequirementsWithIds_direct_eq]
  intro direct
  exact addRequirementsWithIds_ids_fresh state predicates wellFormed id member
    (allocated direct)

/-- Marking a newly allocated direct-call batch does not reclassify any row
that was present before that allocation. -/
theorem addRequirementsWithIds_mark_existing (state : State)
    (predicates : List ProgramPredicate)
    (wellFormed : state.RequirementsWellFormed)
    {id : RequirementId} (prior : id ∈ state.requirements.map Requirement.id) :
    id ∈ ((state.addRequirementsWithIds predicates).2.markDirectCallRequirements
      (state.addRequirementsWithIds predicates).1).directCallRequirements ↔
      id ∈ state.directCallRequirements := by
  change id ∈ (state.addRequirementsWithIds predicates).2.directCallRequirements ++
    (state.addRequirementsWithIds predicates).1 ↔ _
  rw [List.mem_append, addRequirementsWithIds_direct_eq]
  constructor
  · rintro (old | fresh)
    · exact old
    · exact False.elim
        (addRequirementsWithIds_ids_fresh state predicates wellFormed id fresh prior)
  · exact Or.inl

end State

namespace Detail

theorem commitCoercionPlan_direct_eq (state : State)
    (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.directCallRequirements =
      state.directCallRequirements := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest ih =>
    change (commitCoercionPlan
      ((state.addRequirementWithId step.predicate).2.addRequirementsWithIds
        step.methodPredicates).2 rest).2.directCallRequirements = _
    rw [ih, State.addRequirementsWithIds_direct_eq]
    rfl

/-- Coercion requirements remain operational; expected-type fitting never
marks either old or newly issued rows as declaration-call templates. -/
theorem withExpected_direct_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : withExpected context state actual expected = .ok result) :
    result.state.directCallRequirements = state.directCallRequirements := by
  unfold withExpected at accepted
  split at accepted
  · cases accepted
    rfl
  · split at accepted
    · cases accepted
      rfl
    · split at accepted
      all_goals try contradiction
      all_goals
        simp only [bind, Except.bind] at accepted
        split at accepted
        · contradiction
        · split at accepted
          · contradiction
          · cases accepted
            exact commitCoercionPlan_direct_eq _ _

theorem recordExpressionWithExpected_direct_eq
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (accepted : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
    result.2.directCallRequirements = state.directCallRequirements := by
  obtain ⟨fitted, accepted, _, same⟩ :=
    recordExpressionWithExpected_success_record accepted
  rw [same]
  exact withExpected_direct_eq accepted

/-- Every operational ledger row participates in the executable barrier,
regardless of the initializer's cutoff. -/
theorem operational_requirement_blocks
    (state : State) (cutoff : Nat) {requirement : Requirement}
    (present : requirement ∈ state.requirements)
    (operational : requirement.id ∉ state.directCallRequirements) :
    requirement ∈ generalizeValueBlockingRequirements state cutoff := by
  have split : requirement ∈ state.requirements.take cutoff ++
      state.requirements.drop cutoff := by
    simpa only [List.take_append_drop] using present
  rw [mem_generalizeValueBlockingRequirements_iff]
  rcases List.mem_append.mp split with before | after
  · exact .inl before
  · exact .inr ⟨after, operational⟩

/-- The real local-reference branch reissues each predicate into a fresh
operational row and keeps it in the final ledger after expected-type fitting. -/
theorem inferExprFuel_localIdentifier_operational
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State}
    {id : ExpressionId} {name : Syntax.Identifier} {binder : TypedBinder}
    {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : inferExprFuel (fuel + 1) context expression expected initial = .ok result)
    (wellFormed : initial.RequirementsWellFormed)
    (directAllocated : initial.DirectRequirementsAllocated) :
    let start := allocated.inference.next
    let instantiated := binder.scheme.instantiateWithSubstitution start
    let advanced : State :=
      { allocated with inference := { allocated.inference with next := instantiated.next } }
    let predicates := binder.schemeRequirements.map fun requirement =>
      applyPredicate advanced
        (TypedTraitResolution.applySubstitution instantiated.substitution requirement.predicate)
    let batch := advanced.addRequirementsWithIds predicates
    RequirementPredicatesCorrespond result.2.requirements predicates batch.1 ∧
      (∀ requirement ∈ result.2.requirements, requirement.id ∈ batch.1 →
        ∀ cutoff, requirement ∈ generalizeValueBlockingRequirements result.2 cutoff) := by
  dsimp only
  let start := allocated.inference.next
  let instantiated := binder.scheme.instantiateWithSubstitution start
  let advanced : State :=
    { allocated with inference := { allocated.inference with next := instantiated.next } }
  let predicates := binder.schemeRequirements.map fun requirement =>
    applyPredicate advanced
      (TypedTraitResolution.applySubstitution instantiated.substitution requirement.predicate)
  let batch := advanced.addRequirementsWithIds predicates
  have recorded := inferExprFuel_success_localIdentifier_record form allocation found accepted
  change recordExpressionWithExpected context expression id
    (advanced.resolve instantiated.body) (.reference name.value (.local binder.id))
    batch.1 expected batch.2 (some start) = .ok result at recorded
  have sameAllocated : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have advancedWellFormed : advanced.RequirementsWellFormed := by
    change allocated.RequirementsWellFormed
    rw [sameAllocated]
    exact wellFormed
  have advancedDirectAllocated : advanced.DirectRequirementsAllocated := by
    change allocated.DirectRequirementsAllocated
    rw [sameAllocated]
    exact directAllocated
  refine ⟨(State.addRequirementsWithIds_correspond advanced predicates).mono
    (recordExpressionWithExpected_requirements_subset recorded), ?_⟩
  intro requirement present issued cutoff
  apply operational_requirement_blocks result.2 cutoff present
  rw [recordExpressionWithExpected_direct_eq recorded]
  exact State.addRequirementsWithIds_not_direct advanced predicates
    advancedWellFormed advancedDirectAllocated issued

end Detail
end Solcore.Frontend.SourceInference
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.DirectRequirementProgress
/-! Inference may mark newly issued declaration-call requirements. It cannot
change the classification of an earlier operational requirement. -/

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.Frontend.SourceInference
open TypeSystem
/-- The ledger-only relation makes updates to unrelated inference fields
transparent to the recursive traversal. -/
structure RequirementLedgerProgress
    (beforeRows : List Requirement) (beforeNext : Nat) (beforeDirect : List RequirementId)
    (afterRows : List Requirement) (afterNext : Nat) (afterDirect : List RequirementId) : Prop where
  included : beforeRows ⊆ afterRows
  wellFormed : beforeRows.map (fun requirement => requirement.id.index) = List.range beforeNext →
    afterRows.map (fun requirement => requirement.id.index) = List.range afterNext
  allocated : beforeRows.map (fun requirement => requirement.id.index) = List.range beforeNext →
    beforeDirect ⊆ beforeRows.map Requirement.id → afterDirect ⊆ afterRows.map Requirement.id
  existing : beforeRows.map (fun requirement => requirement.id.index) = List.range beforeNext →
    ∀ id ∈ beforeRows.map Requirement.id, id ∈ afterDirect ↔ id ∈ beforeDirect

namespace State

abbrev DirectRequirementsProgress (before after : State) : Prop :=
  RequirementLedgerProgress before.requirements before.nextRequirement before.directCallRequirements
    after.requirements after.nextRequirement after.directCallRequirements

namespace DirectRequirementsProgress

theorem refl (state : State) : DirectRequirementsProgress state state :=
  ⟨fun _ member => member, id, fun _ allocated => allocated, fun _ _ _ => Iff.rfl⟩

theorem trans {first second third : State}
    (left : DirectRequirementsProgress first second)
    (right : DirectRequirementsProgress second third) : DirectRequirementsProgress first third := by
  refine ⟨left.included.trans right.included,
    fun wf => right.wellFormed (left.wellFormed wf),
    fun wf allocated => right.allocated (left.wellFormed wf) (left.allocated wf allocated), ?_⟩
  intro wf id member
  have secondMember : id ∈ second.requirements.map Requirement.id := by
    obtain ⟨requirement, present, same⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨requirement, left.included present, same⟩
  exact (right.existing (left.wellFormed wf) id secondMember).trans
    (left.existing wf id member)

theorem of_direct_eq {before after : State}
    (included : before.requirements ⊆ after.requirements)
    (wellFormed : before.RequirementsWellFormed → after.RequirementsWellFormed)
    (same : after.directCallRequirements = before.directCallRequirements) :
    DirectRequirementsProgress before after := by
  refine ⟨included, wellFormed, ?_, ?_⟩
  · intro _ allocated id present
    rw [same] at present
    obtain ⟨requirement, member, eq⟩ := List.mem_map.mp (allocated present)
    exact List.mem_map.mpr ⟨requirement, included member, eq⟩
  · intro _ _ _
    rw [same]

theorem of_fields_eq {before after : State}
    (requirements : after.requirements = before.requirements)
    (next : after.nextRequirement = before.nextRequirement)
    (direct : after.directCallRequirements = before.directCallRequirements) :
    DirectRequirementsProgress before after := by
  apply of_direct_eq (by rw [requirements]; exact fun _ member => member) ?_ direct
  simp only [RequirementsWellFormed, requirements, next, imp_self]

theorem inference (state : State) (inference : InferState) :
    DirectRequirementsProgress state {state with inference} := of_fields_eq rfl rfl rfl

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    DirectRequirementsProgress state (state.addRequirementWithId predicate).2 :=
  of_direct_eq (State.addRequirementWithId_requirements_subset state predicate)
    (State.addRequirementWithId_preserves_requirementsWellFormed state predicate) rfl

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    DirectRequirementsProgress state (state.addRequirementsWithIds predicates).2 :=
  of_direct_eq (State.addRequirementsWithIds_requirements_subset state predicates)
    (State.addRequirementsWithIds_preserves_requirementsWellFormed state predicates)
    (State.addRequirementsWithIds_direct_eq state predicates)

private theorem correspondence_ids {requirements : List Requirement}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (rows : RequirementPredicatesCorrespond requirements predicates ids) :
    ids ⊆ requirements.map Requirement.id := by
  induction rows with
  | nil => simp
  | @cons predicate id predicates ids present tail ih =>
    intro selected member
    rcases List.mem_cons.mp member with same | later
    · subst selected
      exact List.mem_map.mpr ⟨_, present, rfl⟩
    · exact ih later

theorem addRequirementsWithIds_mark (state : State) (predicates : List ProgramPredicate) :
    DirectRequirementsProgress state
      ((state.addRequirementsWithIds predicates).2.markDirectCallRequirements
        (state.addRequirementsWithIds predicates).1) := by
  refine ⟨State.addRequirementsWithIds_requirements_subset state predicates,
    State.addRequirementsWithIds_preserves_requirementsWellFormed state predicates, ?_, ?_⟩
  · intro wf allocated id member
    rcases List.mem_append.mp member with prior | issued
    · exact (addRequirementsWithIds state predicates).allocated wf allocated prior
    · exact correspondence_ids (State.addRequirementsWithIds_correspond state predicates) issued
  · exact fun wf id member => State.addRequirementsWithIds_mark_existing state predicates wf member

end DirectRequirementsProgress
end State

namespace Detail
open State (DirectRequirementsProgress)

theorem withExpected_direct_progress
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : withExpected context state actual expected = .ok result) :
    DirectRequirementsProgress state result.state :=
  .of_direct_eq (withExpected_requirements_subset accepted)
    (withExpected_preserves_requirementsWellFormed accepted) (withExpected_direct_eq accepted)

theorem candidateWithExpected_direct_progress
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : candidateWithExpected context state actual expected = .ok (some result)) :
    DirectRequirementsProgress state result.state := by
  unfold candidateWithExpected at accepted
  cases fitted : withExpected context state actual expected with
  | ok value =>
    simp only [fitted, Except.ok.injEq, Option.some.injEq] at accepted
    subst result
    exact withExpected_direct_progress fitted
  | error error =>
    cases error <;> simp_all
    rename_i error
    cases error <;> simp_all

theorem fitArguments_direct_progress
    {context : Context} {state : State} {arguments : List InferredExpression}
    {parameters : List Ty} {result : ArgumentFitResult}
    (accepted : fitArguments context state arguments parameters = .ok (some result)) :
    DirectRequirementsProgress state result.state := by
  induction arguments generalizing state parameters result with
  | nil =>
    cases parameters <;> simp_all [fitArguments]
    subst result
    exact .refl _
  | cons argument arguments ih =>
    cases parameters with
    | nil => simp [fitArguments] at accepted
    | cons parameter parameters =>
      unfold fitArguments at accepted
      cases fitted : candidateWithExpected context state argument (some parameter) with
      | error error => simp [fitted, bind, Except.bind] at accepted
      | ok value =>
        cases value with
        | none => simp [fitted, bind, Except.bind] at accepted
        | some fit =>
          simp only [fitted, bind, Except.bind] at accepted
          cases remaining : fitArguments context fit.state arguments parameters with
          | error error => simp [remaining] at accepted
          | ok value =>
            cases value with
            | none => simp [remaining] at accepted
            | some tail =>
              simp only [remaining, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at accepted
              subst result
              exact (candidateWithExpected_direct_progress fitted).trans (ih (result := tail) remaining)

/-- The sole inference operation that marks direct-call rows allocates its
signature predicates after argument/result fitting, then marks exactly them. -/
theorem tryFunctionCandidate_direct_progress
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (accepted : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    DirectRequirementsProgress state result.state := by
  unfold tryFunctionCandidate at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals have argumentsProgress := fitArguments_direct_progress (by assumption)
  all_goals have resultProgress := candidateWithExpected_direct_progress (by assumption)
  all_goals
    exact (DirectRequirementsProgress.inference state _).trans
      (argumentsProgress.trans (resultProgress.trans
        (DirectRequirementsProgress.addRequirementsWithIds_mark _ _)))

end Detail
end Solcore.Frontend.SourceInference
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.DirectRequirementInference
/-! Direct-call classification follows actual successful inference steps. -/
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.Detail
open TypeSystem
open State (DirectRequirementsProgress)

private theorem pureState_eq {state next : State}
    (accepted : (pure state : Except Error State) = .ok next) : state = next :=
  Except.ok.inj accepted

@[simp] private theorem exceptPure_eq_ok {epsilon alpha : Type}
    (value result : alpha) : ((pure value : Except epsilon alpha) = .ok result) ↔ value = result :=
  by change (Except.ok value = Except.ok result) ↔ value = result; simp

theorem unify_direct_progress {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : DirectRequirementsProgress state next := by
  unfold unify at accepted
  cases unified : state.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at accepted
  cases accepted
  exact .refl _

theorem freshTypes_direct_progress (count : Nat) (state : State) :
    DirectRequirementsProgress state (freshTypes count state).2 := by
  induction count generalizing state with
  | zero => exact .refl _
  | succ count ih => exact ih state.fresh.2

theorem freshDataConstructorInstantiation_direct_progress
    (dataType : ProgramDataSignature) (constructor : ProgramDataConstructorSignature) (state : State) :
    DirectRequirementsProgress state (freshDataConstructorInstantiation dataType constructor state).2 := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ => (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldProgress (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      DirectRequirementsProgress accumulator.2 (parameters.foldl step accumulator).2 := by
    induction parameters generalizing accumulator with
    | nil => exact .refl _
    | cons parameter parameters ih => exact ih (step accumulator parameter)
  exact foldProgress dataType.parameters ([], state)

theorem attachExpressionCoercions_direct_progress (state : State) (entries : List ExpressionCoercions) :
    DirectRequirementsProgress state (attachExpressionCoercions state entries) := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact .refl _
  | cons entry rest ih =>
    simp only [List.foldl_cons]
    exact ih (state.modifyExpressionNode entry.expression fun node => appendExpressionCoercions node entry.coercions)

theorem recordExpression_direct_progress
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    (localSchemeInstantiationStart : Option Nat := none) :
    DirectRequirementsProgress state
      (recordExpression source expression form requirements coercions state localSchemeInstantiationStart).2 :=
  .refl _

theorem recordExpressionWithExpected_direct_progress
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State} {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (accepted : recordExpressionWithExpected context source id type form requirements expected
      state localSchemeInstantiationStart = .ok result) : DirectRequirementsProgress state result.2 :=
  .of_direct_eq (recordExpressionWithExpected_requirements_subset accepted)
    (recordExpressionWithExpected_preserves_requirementsWellFormed accepted)
    (recordExpressionWithExpected_direct_eq accepted)

theorem recordSelectedCallResult_direct_progress
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep) (state : State) :
    DirectRequirementsProgress state
      (recordSelectedCallResult source callee name arguments attempt result trailingCoercions state).2 :=
  attachExpressionCoercions_direct_progress state attempt.argumentCoercions

theorem recordSelectedCall_direct_progress
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    DirectRequirementsProgress attempt.state (recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult_direct_progress source callee name arguments attempt attempt.result [] attempt.state

theorem recordIndirectCall_direct_progress (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    DirectRequirementsProgress result.state (recordIndirectCall source callee arguments result).2 := .refl _

theorem selectFunctionCandidateFrom_direct_progress
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    DirectRequirementsProgress state result.state := by
  obtain ⟨signature, _, selected⟩ := selectFunctionCandidateFrom_success_candidate accepted
  exact tryFunctionCandidate_direct_progress selected

theorem inferUnaryOperator_direct_progress
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    DirectRequirementsProgress state result.state := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedProgress := unify_direct_progress (by assumption)
  all_goals first
    | exact .refl _
    | exact unifiedProgress
    | exact DirectRequirementsProgress.addRequirementsWithIds _ _
    | exact unifiedProgress.trans (DirectRequirementsProgress.addRequirementsWithIds _ _)
    | exact (unify_direct_progress (state := state) (by assumption)).trans unifiedProgress
    | exact (unify_direct_progress (state := state) (by assumption)).trans
        (unifiedProgress.trans (DirectRequirementsProgress.addRequirementsWithIds _ _))

theorem inferBinaryOperator_direct_progress
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    DirectRequirementsProgress state result.state := by
  unfold inferBinaryOperator binaryOperatorTail at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedProgress := unify_direct_progress (by assumption)
  all_goals first
    | exact .refl _
    | exact unifiedProgress
    | exact DirectRequirementsProgress.addRequirementsWithIds _ _
    | exact unifiedProgress.trans (DirectRequirementsProgress.addRequirementsWithIds _ _)
    | exact (unify_direct_progress (state := state) (by assumption)).trans unifiedProgress
    | exact (unify_direct_progress (state := state) (by assumption)).trans
        (unifiedProgress.trans (DirectRequirementsProgress.addRequirementsWithIds _ _))


private theorem fresh_direct_progress (state : State) :
    DirectRequirementsProgress state state.fresh.2 := .refl _

theorem applyFunctionType_direct_progress
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    DirectRequirementsProgress state result.state := by
  unfold applyFunctionType at success
  cases partsResult : functionParts? (state.resolve calleeType) with
  | some parts =>
      rcases parts with ⟨parameter, returnType⟩
      simp only [partsResult] at success
      cases argumentResult : withExpected context state
          { id := call, type := Ty.productMany (arguments.map (fun x => x.type)) }
          (some parameter) with
      | error error =>
          simp [argumentResult, bind, Except.bind] at success
      | ok fittedArgument =>
          simp only [argumentResult, bind, Except.bind] at success
          cases resultResult : withExpected context fittedArgument.state
              { id := call, type := returnType } expected with
          | error error =>
              simp [resultResult] at success
          | ok fittedResult =>
              simp only [resultResult] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := fittedArgument.coercions
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              exact DirectRequirementsProgress.trans
                (withExpected_direct_progress argumentResult)
                (withExpected_direct_progress resultResult)
  | none =>
      simp only [partsResult] at success
      generalize freshResultEq : state.fresh = freshResult at success
      rcases freshResult with ⟨resultType, freshState⟩
      cases unifyResult : unify freshState calleeType
          (.function (Ty.productMany (arguments.map fun x => x.type))
            resultType) with
      | error error =>
          simp [unifyResult, bind, Except.bind] at success
      | ok unifiedState =>
          simp only [unifyResult, bind, Except.bind] at success
          cases resultResult : withExpected context unifiedState
              { id := call, type := resultType } expected with
          | error error =>
              simp [resultResult] at success
          | ok fittedResult =>
              simp only [resultResult] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := []
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              have freshSubset :
                  DirectRequirementsProgress state freshState := by
                have subset := fresh_direct_progress state
                rw [freshResultEq] at subset
                exact subset
              exact DirectRequirementsProgress.trans freshSubset
                (DirectRequirementsProgress.trans (unify_direct_progress unifyResult)
                  (withExpected_direct_progress resultResult))

theorem bindLambdaParameters_direct_progress
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    DirectRequirementsProgress state result.2.2 := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [bindLambdaParameters] at success
      injection success with resultEq
      subst result
      exact .refl _
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [bindLambdaParameters, parameterValue, bind, Except.bind]
            at success
      | inferred name =>
          simp only [bindLambdaParameters, parameterValue] at success
          simp only [bind, Except.bind] at success
          repeat' first | split at success
          all_goals try simp_all only [exceptPure_eq_ok]
          all_goals try simp_all
          all_goals
            subst result
            subst_vars
            have tailSubset := induction _ _ _ (by assumption)
            simpa [State.fresh, State.allocateBinder] using tailSubset
      | typed marker name sourceType =>
          simp only [bindLambdaParameters, parameterValue] at success
          cases typeResult : resolveSourceType context sourceType with
          | error error =>
              simp [typeResult, bind, Except.bind] at success
          | ok type =>
              simp only [typeResult, bind, Except.bind] at success
              repeat' first | split at success
              all_goals try simp_all only [exceptPure_eq_ok]
              all_goals try simp_all
              all_goals
                subst result
                subst_vars
                have tailSubset := induction _ _ _ (by assumption)
                simpa [State.allocateBinder] using tailSubset

theorem unifyBuiltinFunctionArgumentsEqual_direct_progress
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next) :
    DirectRequirementsProgress state next := by
  induction arguments generalizing parameters state next with
  | nil =>
      simp only [unifyBuiltinFunctionArgumentsEqual] at success
      injection success with nextEq
      subst next
      exact .refl _
  | cons argument arguments induction =>
      cases parameters with
      | nil =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          injection success with nextEq
          subst next
          exact .refl _
      | cons parameter parameters =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          cases unifyResult : unify state argument.type parameter with
          | error error =>
              simp [unifyResult, bind, Except.bind] at success
          | ok unified =>
              simp only [unifyResult, bind, Except.bind] at success
              exact DirectRequirementsProgress.trans
                (unify_direct_progress unifyResult)
                (induction success)


theorem recordBuiltinFunctionCall_direct_progress
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  unfold recordBuiltinFunctionCall at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have argumentsProgress := unifyBuiltinFunctionArgumentsEqual_direct_progress (by assumption)
  all_goals try have unifiedProgress := unify_direct_progress (by assumption)
  all_goals first
    | exact argumentsProgress
    | exact argumentsProgress.trans unifiedProgress


private theorem progress_compose
    {r1 r2 r3 : List Requirement} {n1 n2 n3 : Nat} {d1 d2 d3 : List RequirementId}
    (left : RequirementLedgerProgress r1 n1 d1 r2 n2 d2)
    (right : RequirementLedgerProgress r2 n2 d2 r3 n3 d3) :
    RequirementLedgerProgress r1 n1 d1 r3 n3 d3 := by
  refine ⟨left.included.trans right.included,
    fun wf => right.wellFormed (left.wellFormed wf),
    fun wf allocated => right.allocated (left.wellFormed wf) (left.allocated wf allocated), ?_⟩
  intro wf id member
  have secondMember : id ∈ r2.map Requirement.id := by
    obtain ⟨requirement, present, same⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨requirement, left.included present, same⟩
  exact (right.existing (left.wellFormed wf) id secondMember).trans (left.existing wf id member)

private def PreservesDirectRequirements {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → DirectRequirementsProgress initial (stateOf result)

private theorem inferMatchPatternFlatFuel_direct_progress_internal
    (fuel : Nat) (context : Context) (pattern : Syntax.Pattern)
    (expected : Ty) (seen : List String) (state : State) :
    PreservesDirectRequirements InferredPattern.state state
      (inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      PreservesDirectRequirements InferredPattern.state state
        (inferMatchPatternFlatFuel fuel context pattern expected seen state))
    (motive2 := fun fuel patterns expected seen state =>
      PreservesDirectRequirements InferredPatterns.state state
        (inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  all_goals
    intros
    unfold PreservesDirectRequirements at *
    intro result success
    simp_all [inferMatchPatternFlatFuel, inferMatchPatternsFlatFuel, bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
    all_goals try have unifyProgress := unify_direct_progress (by assumption)
    all_goals try specialize ih1 _ _ _ heq
    all_goals try specialize ih1 _ _ heq
    all_goals try specialize ih2 _ heq
    all_goals try simp_all [State.fresh, State.allocateBinder]
    all_goals first
      | exact .refl _
      | assumption
      | exact DirectRequirementsProgress.addRequirementWithId _ _
      | exact (DirectRequirementsProgress.addRequirementWithId _ _).trans unifyProgress
      | grind [progress_compose, freshDataConstructorInstantiation_direct_progress,
          freshTypes_direct_progress]

theorem inferMatchPatternFuel_direct_progress
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    DirectRequirementsProgress state result.2 := by
  unfold inferMatchPatternFuel at success
  cases flatResult :
      inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error =>
      simp [flatResult, bind, Except.bind] at success
  | ok inferred =>
      simp only [flatResult, bind, Except.bind] at success
      change Except.ok ({
        source := inferred.source
        type := inferred.state.resolve expected
        resolution := inferred.resolution
        requirements := inferred.requirements
      }, inferred.state) = Except.ok result at success
      injection success with resultEq
      subst result
      exact inferMatchPatternFlatFuel_direct_progress_internal fuel context pattern
        expected [] state inferred flatResult


private theorem pair_success_direct_progress {alpha : Type}
    {operation : alpha × State} {value : alpha} {next initial : State}
    (operationSubset : DirectRequirementsProgress initial operation.2)
    (success : operation = (value, next)) :
    DirectRequirementsProgress initial next := by
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
        DirectRequirementsProgress initial next)
    (invariant : ∀ value state result next,
      computation value state = .ok (result, next) →
        DirectRequirementsProgress state next)
    (success : computation anchor.1 state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  rcases anchor with ⟨value, anchorState⟩
  rcases result with ⟨result, next⟩
  exact invariant value state result next success


private theorem allocateExpressionId_success_direct_progress
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (DirectRequirementsProgress.refl state) success

private theorem allocateStatementId_success_direct_progress
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (DirectRequirementsProgress.refl state) success

private theorem state_fresh_success_direct_progress
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress (DirectRequirementsProgress.refl state)
    success

private theorem allocateHiddenLocal_success_direct_progress
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (DirectRequirementsProgress.refl state) success

private theorem addRequirementWithId_success_direct_progress
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (DirectRequirementsProgress.addRequirementWithId state predicate) success

private theorem addRequirementsWithIds_success_direct_progress
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (DirectRequirementsProgress.addRequirementsWithIds state predicates) success

private theorem allocateBinder_success_direct_progress
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (DirectRequirementsProgress.refl state) success

private theorem freshDataConstructorInstantiation_success_direct_progress
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (freshDataConstructorInstantiation_direct_progress dataType constructor
      state) success

private theorem freshTypes_success_direct_progress
    {count : Nat} {state next : State} {types : List Ty}
    (success : freshTypes count state = (types, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (freshTypes_direct_progress count state) success

private theorem syntheticTuple_result_direct_progress
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
    DirectRequirementsProgress state result.snd := by
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
  exact DirectRequirementsProgress.trans
    (DirectRequirementsProgress.refl state)
    (DirectRequirementsProgress.refl state)

private theorem syntheticTuple_pair_direct_progress
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
    DirectRequirementsProgress state result.snd := by
  rw [← success]
  exact DirectRequirementsProgress.trans
    (DirectRequirementsProgress.refl state)
    (DirectRequirementsProgress.refl state)

private theorem pure_pair_result_direct_progress {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : DirectRequirementsProgress initial next)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    DirectRequirementsProgress initial result.snd := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_direct_progress {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : DirectRequirementsProgress initial state)
    (success : (value, state.restoreLexicalScope scope) = result) :
    DirectRequirementsProgress initial result.snd := by
  rw [← success]
  exact DirectRequirementsProgress.trans subset
    (DirectRequirementsProgress.refl state)


set_option maxHeartbeats 2000000 in
private theorem inferFuel_direct_progress_internal :
    (∀ fuel context expression expected state,
      PreservesDirectRequirements Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesDirectRequirements Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesDirectRequirements Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesDirectRequirements BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesDirectRequirements StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesDirectRequirements InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesDirectRequirements Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesDirectRequirements Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesDirectRequirements (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesDirectRequirements Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      PreservesDirectRequirements MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesDirectRequirements Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesDirectRequirements Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesDirectRequirements Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesDirectRequirements BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesDirectRequirements StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesDirectRequirements InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesDirectRequirements Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesDirectRequirements Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesDirectRequirements (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesDirectRequirements Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesDirectRequirements MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesDirectRequirements at *
    intro result success
    have statementIdSubset :=
      allocateStatementId_success_direct_progress statementIdEq
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
      syntheticTuple_result_direct_progress (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_direct_progress (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_direct_progress casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_direct_progress bodySubset (by assumption)
    all_goals try simp_all
    all_goals try exact DirectRequirementsProgress.refl _
    all_goals dsimp only [State.DirectRequirementsProgress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall] at *
    all_goals grind [progress_compose]
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesDirectRequirements at *
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
      unify_direct_progress (by assumption)
    all_goals simp_all
    all_goals try exact DirectRequirementsProgress.refl _
    all_goals dsimp only [State.DirectRequirementsProgress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall] at *
    all_goals grind [progress_compose]
  case case67 =>
    unfold PreservesDirectRequirements at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesDirectRequirements at *
    intro result success
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
      unify_direct_progress (by assumption)
    all_goals try have expressionIdSubset :=
      allocateExpressionId_success_direct_progress (by assumption)
    all_goals try have statementIdSubset :=
      allocateStatementId_success_direct_progress (by assumption)
    all_goals try have freshSubset :=
      state_fresh_success_direct_progress (by assumption)
    all_goals try have hiddenLocalSubset :=
      allocateHiddenLocal_success_direct_progress (by assumption)
    all_goals try have requirementSubset :=
      addRequirementWithId_success_direct_progress (by assumption)
    all_goals try have requirementsSubset :=
      addRequirementsWithIds_success_direct_progress (by assumption)
    all_goals try have binderSubset :=
      allocateBinder_success_direct_progress (by assumption)
    all_goals try have constructorSubset :=
      freshDataConstructorInstantiation_success_direct_progress (by
        assumption)
    all_goals try have typesSubset :=
      freshTypes_success_direct_progress (by assumption)
    all_goals try have recordSubset :=
      recordExpressionWithExpected_direct_progress (by assumption)
    all_goals try have issuedRecord :=
      (DirectRequirementsProgress.addRequirementWithId _ _).trans recordSubset
    all_goals try have batchRecord :=
      (DirectRequirementsProgress.addRequirementsWithIds _ _).trans recordSubset
    all_goals try have lambdaSubset :=
      bindLambdaParameters_direct_progress (by assumption)
    all_goals try
      have afterLambdaSubset := DirectRequirementsProgress.trans lambdaSubset
        (unify_direct_progress (by assumption))
    all_goals try have patternSubset :=
      inferMatchPatternFuel_direct_progress (by assumption)
    all_goals try have unarySubset :=
      inferUnaryOperator_direct_progress (by assumption)
    all_goals try have binarySubset :=
      inferBinaryOperator_direct_progress (by assumption)
    all_goals try have selectionSubset :=
      selectFunctionCandidateFrom_direct_progress (by assumption)
    all_goals try have expectedSubset :=
      withExpected_direct_progress (by assumption)
    all_goals try have applicationSubset :=
      applyFunctionType_direct_progress (by assumption)
    all_goals try have builtinSubset :=
      recordBuiltinFunctionCall_direct_progress (by assumption)
    all_goals try simp_all
    all_goals try exact DirectRequirementsProgress.addRequirementWithId _ _
    all_goals try exact DirectRequirementsProgress.refl _
    all_goals dsimp only [State.DirectRequirementsProgress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall] at *
    all_goals grind
      [progress_compose,
        State.DirectRequirementsProgress.addRequirementWithId,
        State.DirectRequirementsProgress.addRequirementsWithIds,
        freshDataConstructorInstantiation_direct_progress,
        freshTypes_direct_progress,
        recordExpression_direct_progress,
        recordSelectedCallResult_direct_progress,
        recordSelectedCall_direct_progress,
        recordIndirectCall_direct_progress]

theorem inferExprFuel_direct_progress
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    DirectRequirementsProgress state result.2 := by
  exact inferFuel_direct_progress_internal.1 fuel context expression
    expected state result success

theorem inferConstructorApplicationFuel_direct_progress
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  exact inferFuel_direct_progress_internal.2.1 fuel context source id
    instantiation arguments expected state result success

theorem inferConstructorArgumentsFuel_direct_progress
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  exact inferFuel_direct_progress_internal.2.2.1 fuel context sources
    expected state result success

theorem inferStatementsFuel_direct_progress
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    DirectRequirementsProgress state result.state := by
  exact inferFuel_direct_progress_internal.2.2.2.1 fuel context
    statements expectedReturn state result success

theorem inferStatementFuel_direct_progress
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result) :
    DirectRequirementsProgress state result.state := by
  exact inferFuel_direct_progress_internal.2.2.2.2.1 fuel context
    statement expectedReturn state result success

theorem inferForItemsFuel_direct_progress
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    DirectRequirementsProgress state result.state := by
  exact inferFuel_direct_progress_internal.2.2.2.2.2.1 fuel context
    items state result success

theorem inferForItemFuel_direct_progress
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  exact inferFuel_direct_progress_internal.2.2.2.2.2.2.1 fuel context
    item state result success

theorem inferPlaceFuel_direct_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  exact inferFuel_direct_progress_internal.2.2.2.2.2.2.2.1 fuel
    context target state result success

theorem inferAssignedValueFuel_direct_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    DirectRequirementsProgress state result.2.2 := by
  exact inferFuel_direct_progress_internal.2.2.2.2.2.2.2.2.1 fuel
    context target operator value state result success

theorem inferExprsFuel_direct_progress
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  exact inferFuel_direct_progress_internal.2.2.2.2.2.2.2.2.2.1 fuel
    context expressions state result success

theorem inferMatchCasesFuel_direct_progress
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    DirectRequirementsProgress state result.state := by
  exact inferFuel_direct_progress_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state result success

end Solcore.Frontend.SourceInference.Detail
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalReadEvents
/-! Local references retain the actual inference lookup that issued their
requirements. Later argument coercions may append requirements to the node;
the original batch and its operational classification remain identifiable. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference
open TypeSystem
namespace LocalReadEvents

structure Lookup where
  fuel : Nat
  context : Context
  expression : Syntax.Expr
  expected : Option Ty
  initial : State
  allocated : State
  id : ExpressionId
  name : Syntax.Identifier
  binder : TypedBinder
  result : InferredExpression × State
  form : expression.value = .identifier name
  allocation : initial.allocateExpressionId = (id, allocated)
  found : allocated.lookupBinder? name.value = some binder
  accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result
  wellFormed : initial.RequirementsWellFormed
  directAllocated : initial.DirectRequirementsAllocated

def Lookup.advanced (lookup : Lookup) : State :=
  { lookup.allocated with inference := { lookup.allocated.inference with
      next := (lookup.binder.scheme.instantiateWithSubstitution lookup.allocated.inference.next).next } }

def Lookup.predicates (lookup : Lookup) : List ProgramPredicate :=
  lookup.binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate lookup.advanced
      (TypedTraitResolution.applySubstitution
        (lookup.binder.scheme.instantiateWithSubstitution lookup.allocated.inference.next).substitution
        requirement.predicate)

def Lookup.batch (lookup : Lookup) : List RequirementId × State :=
  lookup.advanced.addRequirementsWithIds lookup.predicates

/-- The witness is a real successful lookup. Its original fresh requirement
batch remains a prefix even if later argument fitting extends this node. -/
def OriginFields (rows : List Requirement) (next : Nat) (direct : List RequirementId)
    (node : ExpressionNode) : Prop :=
  ∃ lookup : Lookup,
    node.id = lookup.id ∧
    node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
    node.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
    lookup.batch.1 <+: node.requirements ∧
    RequirementLedgerProgress lookup.result.2.requirements lookup.result.2.nextRequirement
      lookup.result.2.directCallRequirements rows next direct

def Origin (after : State) (node : ExpressionNode) : Prop :=
  OriginFields after.requirements after.nextRequirement after.directCallRequirements node

def AtFields (rows : List Requirement) (next : Nat) (direct : List RequirementId)
    (node : ExpressionNode) : Prop :=
  ∀ name binder, node.form = .reference name (.local binder) → OriginFields rows next direct node

def At (after : State) (node : ExpressionNode) : Prop :=
  AtFields after.requirements after.nextRequirement after.directCallRequirements node

def OriginsFields (nodes : List Node) (rows : List Requirement) (next : Nat) (direct : List RequirementId) : Prop :=
  ∀ node, Node.expression node ∈ nodes → AtFields rows next direct node

def Origins (state : State) : Prop :=
  OriginsFields state.nodes state.requirements state.nextRequirement state.directCallRequirements

theorem Lookup.recorded (lookup : Lookup) :
    Detail.recordExpressionWithExpected lookup.context lookup.expression lookup.id
      (lookup.advanced.resolve
        (lookup.binder.scheme.instantiateWithSubstitution lookup.allocated.inference.next).body)
      (.reference lookup.name.value (.local lookup.binder.id)) lookup.batch.1 lookup.expected
      lookup.batch.2 (some lookup.allocated.inference.next) = .ok lookup.result :=
  Detail.inferExprFuel_success_localIdentifier_record lookup.form lookup.allocation lookup.found lookup.accepted

theorem Lookup.node (lookup : Lookup) :
    ∃ node, Node.expression node ∈ lookup.result.2.nodes ∧ Origin lookup.result.2 node := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_nodes lookup.recorded
  let node : ExpressionNode := {
    id := fitted.expression.id
    span := lookup.expression.span
    type := fitted.expression.type
    form := .reference lookup.name.value (.local lookup.binder.id)
    requirements := lookup.batch.1 ++ Detail.coercionRequirements fitted.coercions
    coercions := fitted.coercions
    localSchemeInstantiationStart := some lookup.allocated.inference.next }
  refine ⟨node, ?_, lookup, ?_, rfl, rfl, ?_, State.DirectRequirementsProgress.refl lookup.result.2⟩
  · rw [recorded]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · exact Detail.withExpected_success_expression_id fit
  · exact List.prefix_append _ _

theorem Origin.extend {before after : State} {node : ExpressionNode}
    (origin : Origin before node) (progress : State.DirectRequirementsProgress before after) :
    Origin after node := by
  obtain ⟨lookup, id, form, start, batchPrefix, previous⟩ := origin
  exact ⟨lookup, id, form, start, batchPrefix, State.DirectRequirementsProgress.trans previous progress⟩

theorem Origin.node_extension {state : State} {before after : ExpressionNode}
    (origin : Origin state before)
    (id : after.id = before.id) (form : after.form = before.form)
    (start : after.localSchemeInstantiationStart = before.localSchemeInstantiationStart)
    (requirements : before.requirements <+: after.requirements) : Origin state after := by
  obtain ⟨lookup, actualId, actualForm, actualStart, batchPrefix, progress⟩ := origin
  exact ⟨lookup, id.trans actualId, form.trans actualForm, start.trans actualStart,
    batchPrefix.trans requirements, progress⟩

theorem At.extend {before after : State} {node : ExpressionNode}
    (origin : At before node) (progress : State.DirectRequirementsProgress before after) : At after node :=
  fun name binder form => Origin.extend (origin name binder form) progress

theorem At.node_extension {state : State} {before after : ExpressionNode}
    (origin : At state before)
    (id : after.id = before.id) (form : after.form = before.form)
    (start : after.localSchemeInstantiationStart = before.localSchemeInstantiationStart)
    (requirements : before.requirements <+: after.requirements) : At state after := by
  intro name binder selected
  exact Origin.node_extension (origin name binder (form.symm.trans selected)) id form start requirements

theorem Origins.of_nodes_eq {before after : State}
    (origins : Origins before) (same : after.nodes = before.nodes)
    (progress : State.DirectRequirementsProgress before after) : Origins after := by
  intro node member
  exact At.extend (origins node (same ▸ member)) progress

private theorem correspondence_ids {requirements : List Requirement}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (rows : RequirementPredicatesCorrespond requirements predicates ids) :
    ids ⊆ requirements.map Requirement.id := by
  induction rows with
  | nil => simp
  | @cons predicate id predicates ids present tail ih =>
    intro selected member
    rcases List.mem_cons.mp member with same | later
    · subst selected
      exact List.mem_map.mpr ⟨_, present, rfl⟩
    · exact ih later

/-- Operational status follows from the actual local branch, then travels
through the real inference progress to the node's final ledger. -/
theorem Origin.operational {state : State} {node : ExpressionNode}
    (origin : Origin state node) :
    ∃ lookup : Lookup,
      node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      node.localSchemeInstantiationStart = some lookup.allocated.inference.next ∧
      lookup.batch.1 <+: node.requirements ∧
      RequirementPredicatesCorrespond state.requirements lookup.predicates lookup.batch.1 ∧
      (∀ requirement ∈ state.requirements, requirement.id ∈ lookup.batch.1 →
        ∀ cutoff, requirement ∈ Detail.generalizeValueBlockingRequirements state cutoff) := by
  obtain ⟨lookup, id, form, start, batchPrefix, progress⟩ := origin
  have issuedFacts := Detail.inferExprFuel_localIdentifier_operational lookup.form lookup.allocation lookup.found
    lookup.accepted lookup.wellFormed lookup.directAllocated
  change RequirementPredicatesCorrespond lookup.result.2.requirements lookup.predicates lookup.batch.1 ∧ _ at issuedFacts
  refine ⟨lookup, id, form, start, batchPrefix, issuedFacts.1.mono progress.included, ?_⟩
  intro requirement present issued cutoff
  apply Detail.operational_requirement_blocks state cutoff present
  have allocatedEq : lookup.allocated = lookup.initial.allocateExpressionId.2 :=
    (congrArg Prod.snd lookup.allocation).symm
  have advancedWF : lookup.advanced.RequirementsWellFormed := by
    change lookup.allocated.RequirementsWellFormed
    rw [allocatedEq]
    exact lookup.wellFormed
  have advancedDirect : lookup.advanced.DirectRequirementsAllocated := by
    change lookup.allocated.DirectRequirementsAllocated
    rw [allocatedEq]
    exact lookup.directAllocated
  have batchWF := State.addRequirementsWithIds_preserves_requirementsWellFormed
    lookup.advanced lookup.predicates advancedWF
  have resultWF := Detail.recordExpressionWithExpected_preserves_requirementsWellFormed lookup.recorded batchWF
  have batchMember : requirement.id ∈ lookup.result.2.requirements.map Requirement.id :=
    correspondence_ids issuedFacts.1 issued
  intro direct
  have earlier := (progress.existing resultWF requirement.id batchMember).mp direct
  have recorded := lookup.recorded
  rw [Detail.recordExpressionWithExpected_direct_eq recorded] at earlier
  exact State.addRequirementsWithIds_not_direct lookup.advanced lookup.predicates advancedWF advancedDirect issued earlier

end LocalReadEvents
end Solcore.Frontend.SourceInference
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalReadOriginsHelpers
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
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalReadOriginsProgress
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
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.LocalReadOriginsInference
/-! Every local reference in successful source inference retains its actual
lookup and freshly issued operational requirements. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Solcore.Frontend.SourceInference.LocalReadEvents
open TypeSystem Detail
open State (DirectRequirementsProgress)

@[simp] private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private def PreservesOrigins {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Progress initial (stateOf result)

private theorem pair_success_origins_progress {alpha : Type}
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


private theorem allocateExpressionId_success_origins_progress
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl state)) success

private theorem allocateStatementId_success_origins_progress
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl state)) success

private theorem state_fresh_success_origins_progress
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    Progress state next :=
  pair_success_origins_progress (Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl state))
    success

private theorem allocateHiddenLocal_success_origins_progress
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl state)) success

private theorem addRequirementWithId_success_origins_progress
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.addRequirementWithId state predicate) success

private theorem addRequirementsWithIds_success_origins_progress
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.addRequirementsWithIds state predicates) success

private theorem allocateBinder_success_origins_progress
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl state)) success

private theorem freshDataConstructorInstantiation_success_origins_progress
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    Progress state next :=
  pair_success_origins_progress
    (Progress.freshDataConstructorInstantiation dataType constructor
      state) success

private theorem freshTypes_success_origins_progress
    {count : Nat} {state next : State} {types : List Ty}
    (success : freshTypes count state = (types, next)) :
    Progress state next :=
  pair_success_origins_progress
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
  exact ⟨DirectRequirementsProgress.refl state, fun _ _ origins =>
    Origins.recordNode origins _ (by intro node same; cases same; intro _ _ impossible; cases impossible)⟩

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
    Progress state result.snd := by
  rw [← success]
  exact ⟨DirectRequirementsProgress.refl state, fun _ _ origins =>
    Origins.recordNode origins _ (by intro node same; cases same; intro _ _ impossible; cases impossible)⟩

private theorem pure_pair_result_origins_progress {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : Progress initial next)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    Progress initial result.snd := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_origins_progress {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : Progress initial state)
    (success : (value, state.restoreLexicalScope scope) = result) :
    Progress initial result.snd := by
  rw [← success]
  exact Progress.trans subset
    (Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl state))


set_option maxHeartbeats 2000000 in
private theorem inferFuel_origins_progress_internal :
    (∀ fuel context expression expected state,
      PreservesOrigins Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesOrigins Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesOrigins Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesOrigins BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesOrigins StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesOrigins InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesOrigins Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesOrigins Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesOrigins (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesOrigins Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      PreservesOrigins MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesOrigins Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesOrigins Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesOrigins Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesOrigins BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesOrigins StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesOrigins InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesOrigins Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesOrigins Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesOrigins (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesOrigins Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesOrigins MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesOrigins at *
    intro result success
    have statementIdSubset :=
      allocateStatementId_success_origins_progress statementIdEq
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
      syntheticTuple_result_origins_progress (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_origins_progress (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_origins_progress casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_origins_progress bodySubset (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl _)
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
      | apply ProgressFields.trans (second := ProgressFields.statement _ _ _ _ _)
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _ _ _
          (by change Nonlocal (.call _ _ (.indirect _)); intro _ _ impossible; cases impossible))
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _ _ _
          (by change Nonlocal (.constructor _ _); intro _ _ impossible; cases impossible))
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
      Progress.unify (by assumption)
    all_goals simp_all
    all_goals try exact Progress.refl _
    all_goals try exact Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl _)
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
      | apply ProgressFields.trans (second := ProgressFields.statement _ _ _ _ _)
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _ _ _
          (by change Nonlocal (.call _ _ (.indirect _)); intro _ _ impossible; cases impossible))
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _ _ _
          (by change Nonlocal (.constructor _ _); intro _ _ impossible; cases impossible))
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
      Progress.unify (by assumption)
    all_goals try have expressionIdSubset :=
      allocateExpressionId_success_origins_progress (by assumption)
    all_goals try have statementIdSubset :=
      allocateStatementId_success_origins_progress (by assumption)
    all_goals try have freshSubset :=
      state_fresh_success_origins_progress (by assumption)
    all_goals try have hiddenLocalSubset :=
      allocateHiddenLocal_success_origins_progress (by assumption)
    all_goals try have requirementSubset :=
      addRequirementWithId_success_origins_progress (by assumption)
    all_goals try have requirementsSubset :=
      addRequirementsWithIds_success_origins_progress (by assumption)
    all_goals try have binderSubset :=
      allocateBinder_success_origins_progress (by assumption)
    all_goals try have constructorSubset :=
      freshDataConstructorInstantiation_success_origins_progress (by
        assumption)
    all_goals try have typesSubset :=
      freshTypes_success_origins_progress (by assumption)
    all_goals try have recordSubset :=
      Progress.recordExpressionWithExpected (by assumption) (by intro _ _ impossible; cases impossible)
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
    all_goals try have selectionSubset :=
      Progress.selectFunctionCandidateFrom (by assumption)
    all_goals try have expectedSubset :=
      Progress.withExpected (by assumption)
    all_goals try have applicationSubset :=
      Progress.applyFunctionType (by assumption)
    all_goals try have builtinSubset :=
      Progress.recordBuiltinFunctionCall (by assumption)
    all_goals try simp_all
    all_goals try exact Progress.addRequirementWithId _ _
    all_goals try exact Progress.refl _
    all_goals try exact Progress.of_nodes_eq rfl (DirectRequirementsProgress.refl _)
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
      | apply ProgressFields.trans (second := ProgressFields.statement _ _ _ _ _)
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _ _ _
          (by change Nonlocal (.call _ _ (.indirect _)); intro _ _ impossible; cases impossible))
      | apply ProgressFields.trans (second := ProgressFields.expression _ _ _ _ _
          (by change Nonlocal (.constructor _ _); intro _ _ impossible; cases impossible))
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
    Progress state result.2 := by
  exact inferFuel_origins_progress_internal.1 fuel context expression
    expected state result success

theorem inferConstructorApplicationFuel_origins_progress
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_origins_progress_internal.2.1 fuel context source id
    instantiation arguments expected state result success

theorem inferConstructorArgumentsFuel_origins_progress
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.1 fuel context sources
    expected state result success

theorem inferStatementsFuel_origins_progress
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    Progress state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.1 fuel context
    statements expectedReturn state result success

theorem inferStatementFuel_origins_progress
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result) :
    Progress state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.1 fuel context
    statement expectedReturn state result success

theorem inferForItemsFuel_origins_progress
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    Progress state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.1 fuel context
    items state result success

theorem inferForItemFuel_origins_progress
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.1 fuel context
    item state result success

theorem inferPlaceFuel_origins_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.1 fuel
    context target state result success

theorem inferAssignedValueFuel_origins_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    Progress state result.2.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.1 fuel
    context target operator value state result success

theorem inferExprsFuel_origins_progress
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    Progress state result.2 := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.2.1 fuel
    context expressions state result success

theorem inferMatchCasesFuel_origins_progress
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    Progress state result.state := by
  exact inferFuel_origins_progress_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state result success

/-- The actual statement traversal preserves local lookup events from its genuine
initial ledger and node table. -/
theorem inferStatementsFuel_origins
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : Detail.BlockResult}
    (accepted : Detail.inferStatementsFuel fuel context statements expectedReturn state = .ok result)
    (wellFormed : state.RequirementsWellFormed) (allocated : state.DirectRequirementsAllocated)
    (origins : Origins state) : Origins result.state :=
  (inferStatementsFuel_origins_progress accepted).origins wellFormed allocated origins

/-- A final local reference yields its real inference call and its original
operational requirement batch, including subsequent argument coercion updates. -/
theorem inferStatementsFuel_local_lookup
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : Detail.BlockResult}
    (accepted : Detail.inferStatementsFuel fuel context statements expectedReturn state = .ok result)
    (wellFormed : state.RequirementsWellFormed) (allocated : state.DirectRequirementsAllocated)
    (origins : Origins state) {node : ExpressionNode}
    (member : Node.expression node ∈ result.state.nodes) {name : String} {binder : Resolved.LocalId}
    (form : node.form = .reference name (.local binder)) : Origin result.state node :=
  inferStatementsFuel_origins accepted wellFormed allocated origins node member name binder form

end Solcore.Frontend.SourceInference.LocalReadEvents
end
