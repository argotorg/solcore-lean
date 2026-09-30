import Solcore.SourceSemantics.SourceInferenceStatementLedgerInvariant

/-!
The expression half of recursive requirement/template-ledger preservation.
The invariant is indexed by an arbitrary pending template suffix: expression
inference may inspect and extend the requirement ledger, but it neither owns
nor materializes that suffix.  Lambda bodies delegate only their actual
statement trace to the smaller-fuel statement callback.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

namespace RecursiveLedgerInvariant

/-- Updating an expression node cannot change the statement-only template
inventory. -/
private theorem modifyExpressionNode_templateIds_eq
    (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode) :
    sourceLocalSchemeTemplateIds
        ((state.modifyExpressionNode id modify).toTypedSource []) =
      sourceLocalSchemeTemplateIds (state.toTypedSource []) := by
  cases state with
  | mk owner inference locals inputs localBinders nextLocal nextOccurrence nodes
      integerLiterals integerPatterns nextRequirement requirements
      directCallRequirements localSchemeAssumptions =>
      simp only [State.modifyExpressionNode, State.toTypedSource,
        sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
        initializedLetBindings]
      induction nodes with
      | nil => rfl
      | cons node rest induction =>
          cases node with
          | expression node =>
              by_cases same : node.id = id <;> simp [same, induction]
          | statement node =>
              simp [induction]

/-- Replace state components irrelevant to qualified-template tracking, while
retaining every already allocated requirement row. -/
private theorem transportStable
    {before after : State} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant before pending)
    (wellFormed : after.RequirementsWellFormed)
    (assumptionsEq : after.localSchemeAssumptions =
      before.localSchemeAssumptions)
    (templatesEq : sourceLocalSchemeTemplateIds (after.toTypedSource []) =
      sourceLocalSchemeTemplateIds (before.toTypedSource []))
    (requirementsSubset : before.requirements ⊆ after.requirements) :
    RecursiveLedgerInvariant after pending := by
  constructor
  · exact wellFormed
  · constructor
    · rw [assumptionsEq, templatesEq]
      exact tracked.templates.classified
    · rw [assumptionsEq]
      exact tracked.templates.unique
    · intro id member
      rw [assumptionsEq] at member
      rcases List.mem_map.mp (tracked.templates.covered id member) with
        ⟨requirement, requirementMember, requirementId⟩
      exact List.mem_map.mpr
        ⟨requirement, requirementsSubset requirementMember, requirementId⟩

/-- The operator resolver changes the ledger state through only these two
canonical operations.  Keeping that operational fact separate prevents the
large recursive invariant from being expanded by branch simplification. -/
private inductive LedgerEvolution : State → State → Prop where
  | refl (state : State) : LedgerEvolution state state
  | unify {state next : State} {left right : Ty}
      (success : Detail.unify state left right = .ok next) :
      LedgerEvolution state next
  | addRequirements (state : State) (predicates : List ProgramPredicate) :
      LedgerEvolution state (state.addRequirementsWithIds predicates).2
  | trans {first second third : State}
      (head : LedgerEvolution first second)
      (tail : LedgerEvolution second third) :
      LedgerEvolution first third

private theorem LedgerEvolution.preserve
    {initial final : State} (evolution : LedgerEvolution initial final)
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant final pending := by
  induction evolution with
  | refl => exact tracked
  | unify success => exact tracked.unify success
  | addRequirements state predicates =>
      exact ⟨State.addRequirementsWithIds_preserves_requirementsWellFormed
          state predicates tracked.requirements,
        tracked.templates.addRequirementsWithIds predicates⟩
  | trans head tail headInduction tailInduction =>
      exact tailInduction (headInduction tracked)

/-- Allocating one fresh type metavariable changes neither ledger. -/
theorem fresh {state : State} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending) :
    RecursiveLedgerInvariant state.fresh.2 pending := by
  apply transportStable tracked
  · exact State.fresh_preserves_requirementsWellFormed state
      tracked.requirements
  · rfl
  · rfl
  · exact State.fresh_requirements_subset state

/-- Freshening every parameter of a data-constructor instantiation is a fold
of ordinary metavariable allocations and therefore preserves both ledgers. -/
theorem freshDataConstructorInstantiation
    {state : State} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) :
    RecursiveLedgerInvariant
      (Detail.freshDataConstructorInstantiation dataType constructor state).2
      pending := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldPreserves (parameters : List TypeParameterId)
      (accumulator : List Ty × State)
      (accumulatorTracked :
        RecursiveLedgerInvariant accumulator.2 pending) :
      RecursiveLedgerInvariant
        (parameters.foldl step accumulator).2 pending := by
    induction parameters generalizing accumulator with
    | nil => exact accumulatorTracked
    | cons parameter parameters induction =>
        simp only [List.foldl_cons]
        exact induction (step accumulator parameter)
          (accumulatorTracked.fresh)
  unfold Detail.freshDataConstructorInstantiation
  exact foldPreserves dataType.parameters ([], state) tracked

/-- Replacing only inference unification metadata changes neither ledger. -/
theorem withInference {state : State} {inference : InferState}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending) :
    RecursiveLedgerInvariant { state with inference } pending := by
  apply transportStable tracked
  · exact tracked.requirements
  · rfl
  · rfl
  · exact fun _ member => member

/-- Recording literal-origin metadata changes neither ledger. -/
theorem withIntegerLiterals {state : State}
    {integerLiterals : List IntegerLiteralOrigin}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending) :
    RecursiveLedgerInvariant { state with integerLiterals } pending := by
  apply transportStable tracked
  · exact tracked.requirements
  · rfl
  · rfl
  · exact fun _ member => member

/-- Lambda parameters are monomorphic and own no qualified requirements, so
entering one parameter preserves the ambient pending suffix. -/
theorem allocateBinderWithoutRequirements
    {state : State} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (name : String) (scheme : Scheme)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false) :
    RecursiveLedgerInvariant
      (state.allocateBinder name scheme span comptime []).2 pending := by
  constructor
  · exact State.allocateBinder_preserves_requirementsWellFormed state name
      scheme span comptime [] tracked.requirements
  · simpa using tracked.templates.allocateBinder name scheme span comptime []
      (by simp) (by simp) (by simp)

/-- Canonical batch requirement allocation preserves the template ledger and
extends its coverage ledger. -/
theorem addRequirementsWithIds {state : State}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (predicates : List ProgramPredicate) :
    RecursiveLedgerInvariant
      (state.addRequirementsWithIds predicates).2 pending := by
  exact ⟨State.addRequirementsWithIds_preserves_requirementsWellFormed
      state predicates tracked.requirements,
    tracked.templates.addRequirementsWithIds predicates⟩

/-- The singleton allocation specialization. -/
theorem addRequirementWithId {state : State}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (predicate : ProgramPredicate) :
    RecursiveLedgerInvariant (state.addRequirementWithId predicate).2
      pending := by
  simpa [State.addRequirementsWithIds] using
    tracked.addRequirementsWithIds [predicate]

/-- Direct-call provenance changes neither canonical ledger. -/
theorem markDirectCallRequirements {state : State}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (requirements : List RequirementId) :
    RecursiveLedgerInvariant
      (state.markDirectCallRequirements requirements) pending := by
  apply transportStable tracked
  · exact State.markDirectCallRequirements_preserves_requirementsWellFormed
      state requirements tracked.requirements
  · rfl
  · rfl
  · exact State.markDirectCallRequirements_requirements_subset state
      requirements

/-- Rewriting coercion metadata on an already-recorded expression leaves the
statement-template inventory untouched. -/
theorem modifyExpressionNode {state : State}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode) :
    RecursiveLedgerInvariant (state.modifyExpressionNode id modify)
      pending := by
  apply transportStable tracked
  · exact State.modifyExpressionNode_preserves_requirementsWellFormed
      state id modify tracked.requirements
  · rfl
  · exact modifyExpressionNode_templateIds_eq state id modify
  · exact State.modifyExpressionNode_requirements_subset state id modify

/-- Attaching committed coercion paths only rewrites expression nodes. -/
theorem attachExpressionCoercions {state : State}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (entries : List Detail.ExpressionCoercions) :
    RecursiveLedgerInvariant
      (Detail.attachExpressionCoercions state entries) pending := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact tracked
  | cons entry rest induction =>
      simp only [List.foldl_cons]
      exact induction (tracked.modifyExpressionNode entry.expression fun node =>
        Detail.appendExpressionCoercions node entry.coercions)

/-- Committing a coercion plan only allocates ordinary use-site
requirements. -/
theorem commitCoercionPlan {state : State}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (plan : List Detail.PlannedCoercionStep) :
    RecursiveLedgerInvariant (Detail.commitCoercionPlan state plan).2
      pending := by
  induction plan generalizing state with
  | nil => exact tracked
  | cons step rest induction =>
      simp only [Detail.commitCoercionPlan]
      exact induction
        ((tracked.addRequirementWithId step.predicate).addRequirementsWithIds
          step.methodPredicates)

/-- Expected-type fitting changes only inference metadata or commits a
coercion plan, hence preserves an arbitrary pending template suffix. -/
theorem withExpected
    {context : Frontend.SourceInference.Context} {state : State}
    {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.withExpected context state actual expected = .ok result) :
    RecursiveLedgerInvariant result.state pending := by
  cases expected with
  | none =>
      simp [Detail.withExpected] at success
      subst result
      exact tracked
  | some expectedType =>
      unfold Detail.withExpected at success
      cases unified : state.inference.unify actual.type expectedType with
      | ok inference =>
          simp [unified] at success
          subst result
          exact tracked.withInference
      | error error =>
          cases error with
          | mismatch left right =>
              simp only [unified, bind, Except.bind] at success
              cases planResult : Detail.coercionPlan? context state
                  (state.resolve actual.type) (state.resolve expectedType) with
              | error failure =>
                  simp [planResult] at success
              | ok planOption =>
                  cases planOption with
                  | none =>
                      simp [planResult] at success
                  | some plan =>
                      simp [planResult] at success
                      subst result
                      exact tracked.commitCoercionPlan plan
          | occursCheck _ _ =>
              simp [unified] at success
          | exhausted =>
              simp [unified] at success

/-- The successful-candidate wrapper returns an unchanged expected-fitting
result. -/
theorem candidateWithExpected_some
    {context : Frontend.SourceInference.Context} {state : State}
    {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.candidateWithExpected context state actual expected =
      .ok (some result)) :
    RecursiveLedgerInvariant result.state pending := by
  unfold Detail.candidateWithExpected at success
  cases fittedSuccess : Detail.withExpected context state actual expected with
  | ok fitted =>
      simp [fittedSuccess] at success
      subst result
      exact tracked.withExpected fittedSuccess
  | error error =>
      cases error with
      | unification unification =>
          cases unification <;> simp [fittedSuccess] at success
      | _ => simp [fittedSuccess] at success

/-- Fitting a source-ordered argument list preserves the pending suffix. -/
theorem fitArguments_some
    {context : Frontend.SourceInference.Context}
    {state : State} {arguments : List InferredExpression}
    {parameters : List Ty} {result : Detail.ArgumentFitResult}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.fitArguments context state arguments parameters =
      .ok (some result)) :
    RecursiveLedgerInvariant result.state pending := by
  induction arguments generalizing state parameters result with
  | nil =>
      cases parameters with
      | nil =>
          simp [Detail.fitArguments] at success
          subst result
          exact tracked
      | cons parameter rest =>
          simp [Detail.fitArguments] at success
  | cons argument rest induction =>
      cases parameters with
      | nil =>
          simp [Detail.fitArguments] at success
      | cons parameter parameters =>
          unfold Detail.fitArguments at success
          cases headSuccess : Detail.candidateWithExpected context state
              argument (some parameter) with
          | error error =>
              simp [headSuccess, bind, Except.bind] at success
          | ok headOption =>
              cases headOption with
              | none =>
                  simp [headSuccess, bind, Except.bind] at success
              | some head =>
                  simp only [headSuccess, bind, Except.bind] at success
                  cases tailSuccess : Detail.fitArguments context head.state
                      rest parameters with
                  | error error =>
                      simp [tailSuccess, bind, Except.bind] at success
                  | ok tailOption =>
                      cases tailOption with
                      | none =>
                          simp [tailSuccess, bind, Except.bind] at success
                      | some tail =>
                          simp [tailSuccess] at success
                          rcases success with rfl
                          simpa using induction (result := tail)
                            (tracked.candidateWithExpected_some headSuccess)
                            tailSuccess

/-- Checking one concrete overload candidate preserves the pending template
suffix when the candidate succeeds. -/
theorem tryFunctionCandidate_some
    {context : Frontend.SourceInference.Context}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature}
    {result : Detail.CandidateAttemptResult}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.tryFunctionCandidate context arguments
      integerLiteralOrigins call expected state signature = .ok (some result)) :
    RecursiveLedgerInvariant result.state pending := by
  unfold Detail.tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have argumentLedger :=
    tracked.withInference.fitArguments_some (by assumption)
  all_goals try have resultLedger :=
    argumentLedger.candidateWithExpected_some (by assumption)
  all_goals try simp_all only [exceptPure_eq_ok]
  all_goals try subst result
  all_goals solve_by_elim (maxDepth := 20)
    [RecursiveLedgerInvariant.addRequirementsWithIds,
      RecursiveLedgerInvariant.markDirectCallRequirements]

/-- Overload ranking returns an unchanged successful concrete attempt. -/
theorem selectFunctionCandidateFrom
    {context : Frontend.SourceInference.Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : Detail.CandidateAttemptResult}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.selectFunctionCandidateFrom context name candidates
      arguments integerLiteralOrigins call expected state = .ok result) :
    RecursiveLedgerInvariant result.state pending := by
  obtain ⟨signature, _, candidateSuccess⟩ :=
    Detail.selectFunctionCandidateFrom_success_candidate success
  exact tracked.tryFunctionCandidate_some candidateSuccess

/-- The executable expression recorder is the expression-node specialization
of the lower-level ledger-preserving recorder. -/
private theorem recordExpressionOperation
    {state : State} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep)
    (localSchemeInstantiationStart : Option Nat := none) :
    RecursiveLedgerInvariant
      (Detail.recordExpression source expression form requirements coercions
        state localSchemeInstantiationStart).2 pending := by
  unfold Detail.recordExpression
  exact tracked.recordExpression {
    id := expression.id
    span := source.span
    type := expression.type
    form
    requirements
    coercions
    localSchemeInstantiationStart
  }

/-- Expected-type fitting followed by one expression-node append preserves
the recursive ledger invariant. -/
theorem recordExpressionWithExpected
    {context : Frontend.SourceInference.Context} {source : Syntax.Expr}
    {id : ExpressionId} {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    {localSchemeInstantiationStart : Option Nat}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
    RecursiveLedgerInvariant result.2 pending := by
  unfold Detail.recordExpressionWithExpected at success
  cases fittedSuccess : Detail.withExpected context state { id, type }
      expected with
  | error error =>
      simp [fittedSuccess, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedSuccess, bind, Except.bind, pure, Pure.pure,
        Except.pure] at success
      have resultEq : Detail.recordExpression source fitted.expression form
          (requirements ++ Detail.coercionRequirements fitted.coercions)
          fitted.coercions fitted.state localSchemeInstantiationStart =
          result := by
        simpa only [Except.ok.injEq] using success
      rw [← resultEq]
      exact (tracked.withExpected fittedSuccess).recordExpressionOperation source
        fitted.expression form
        (requirements ++ Detail.coercionRequirements fitted.coercions)
        fitted.coercions localSchemeInstantiationStart

/-- The selected-call recorder rewrites only argument expression nodes and
then appends its synthetic callee and call expression nodes. -/
theorem recordSelectedCallResult
    {state : State} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression)
    (attempt : Detail.CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep) :
    RecursiveLedgerInvariant
      (Detail.recordSelectedCallResult source callee name arguments attempt
        result trailingCoercions state).2 pending := by
  let attached := Detail.attachExpressionCoercions state
    attempt.argumentCoercions
  have attachedLedger : RecursiveLedgerInvariant attached pending :=
    tracked.attachExpressionCoercions attempt.argumentCoercions
  let allocation := attached.allocateExpressionId
  have allocatedLedger :
      RecursiveLedgerInvariant allocation.2 pending :=
    attachedLedger.allocateExpressionId
  let calleeExpression : InferredExpression := {
    id := allocation.1
    type := allocation.2.resolve attempt.instantiation.type
  }
  have calleeLedger := allocatedLedger.recordExpressionOperation callee
    calleeExpression
    (.reference name (.declaration attempt.instantiation)) [] []
  change RecursiveLedgerInvariant
    (Detail.recordExpression source result
      (.call allocation.1 (arguments.map (·.id))
        (.declaration attempt.instantiation))
      (Detail.coercionRequirements attempt.callCoercions ++
        attempt.signatureRequirements ++
        Detail.coercionRequirements trailingCoercions)
      (attempt.callCoercions ++ trailingCoercions)
      (Detail.recordExpression callee calleeExpression
        (.reference name (.declaration attempt.instantiation)) [] []
        allocation.2).2).2 pending
  exact calleeLedger.recordExpressionOperation source result
    (.call allocation.1 (arguments.map (·.id))
      (.declaration attempt.instantiation))
    (Detail.coercionRequirements attempt.callCoercions ++
      attempt.signatureRequirements ++
      Detail.coercionRequirements trailingCoercions)
    (attempt.callCoercions ++ trailingCoercions)

theorem recordSelectedCall
    {attempt : Detail.CandidateAttemptResult}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant attempt.state pending)
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) :
    RecursiveLedgerInvariant
      (Detail.recordSelectedCall source callee name arguments attempt).2
      pending := by
  exact tracked.recordSelectedCallResult source callee name arguments attempt
    attempt.result []

/-- The indirect-call recorder appends one expression node. -/
theorem recordIndirectCall
    {application : Detail.IndirectApplicationResult}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant application.state pending)
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) :
    RecursiveLedgerInvariant
      (Detail.recordIndirectCall source callee arguments application).2
      pending := by
  unfold Detail.recordIndirectCall
  exact tracked.recordExpressionOperation source application.result _ _ _

/-- Pairwise fixed-builtin argument unification preserves both ledgers. -/
theorem unifyBuiltinFunctionArgumentsEqual
    {arguments : List InferredExpression} {parameters : List Ty}
    {state final : State} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.unifyBuiltinFunctionArgumentsEqual arguments parameters
      state = .ok final) :
    RecursiveLedgerInvariant final pending := by
  induction arguments generalizing parameters state final with
  | nil =>
      simp [Detail.unifyBuiltinFunctionArgumentsEqual] at success
      subst final
      exact tracked
  | cons argument rest induction =>
      cases parameters with
      | nil =>
          simp [Detail.unifyBuiltinFunctionArgumentsEqual] at success
          subst final
          exact tracked
      | cons parameter parameters =>
          unfold Detail.unifyBuiltinFunctionArgumentsEqual at success
          cases headSuccess : Detail.unify state argument.type parameter with
          | error error =>
              simp [headSuccess, bind, Except.bind] at success
          | ok headState =>
              simp only [headSuccess, bind, Except.bind] at success
              exact induction (tracked.unify headSuccess) success

/-- Applying an indirect function type uses only fresh allocation,
unification, and expected-type fitting. -/
theorem applyFunctionType
    {context : Frontend.SourceInference.Context} {call : ExpressionId}
    {calleeType : Ty} {arguments : List InferredExpression}
    {expected : Option Ty} {state : State}
    {result : Detail.IndirectApplicationResult}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.applyFunctionType context call calleeType arguments
      expected state = .ok result) :
    RecursiveLedgerInvariant result.state pending := by
  unfold Detail.applyFunctionType at success
  cases partsEq : Detail.functionParts? (state.resolve calleeType) with
  | some parts =>
      rcases parts with ⟨parameter, returnType⟩
      simp only [partsEq, bind, Except.bind] at success
      cases argumentSuccess : Detail.withExpected context state
          { id := call, type := Ty.productMany (arguments.map (·.type)) }
          (some parameter) with
      | error error =>
          simp [argumentSuccess, bind, Except.bind] at success
      | ok fittedArgument =>
          simp only [argumentSuccess, bind, Except.bind] at success
          cases resultSuccess : Detail.withExpected context fittedArgument.state
              { id := call, type := returnType } expected with
          | error error =>
              simp [resultSuccess, bind, Except.bind] at success
          | ok fittedResult =>
              simp [resultSuccess, bind, Except.bind] at success
              subst result
              exact (tracked.withExpected argumentSuccess).withExpected
                resultSuccess
  | none =>
      simp only [partsEq, bind, Except.bind] at success
      let resultType := state.fresh.1
      let freshState := state.fresh.2
      cases unifySuccess : Detail.unify freshState calleeType
          (.function (Ty.productMany (arguments.map (·.type))) resultType) with
      | error error =>
          simp [resultType, freshState, unifySuccess, bind, Except.bind]
            at success
      | ok unifiedState =>
          simp only [resultType, freshState, unifySuccess, bind, Except.bind]
            at success
          cases resultSuccess : Detail.withExpected context unifiedState
              { id := call, type := resultType } expected with
          | error error =>
              change
                Except.bind (Detail.withExpected context unifiedState
                    { id := call, type := resultType } expected) (fun fitted =>
                  Except.ok {
                      result := fitted.expression
                      argumentCoercions := []
                      callCoercions := fitted.coercions
                      state := fitted.state
                    }) = Except.ok result at success
              rw [resultSuccess] at success
              change Except.error error = Except.ok result at success
              cases success
          | ok fittedResult =>
              change
                Except.bind (Detail.withExpected context unifiedState
                    { id := call, type := resultType } expected) (fun fitted =>
                  Except.ok {
                      result := fitted.expression
                      argumentCoercions := []
                      callCoercions := fitted.coercions
                      state := fitted.state
                    }) = Except.ok result at success
              simp only [resultSuccess] at success
              injection success with resultEq
              subst result
              exact ((tracked.fresh.unify unifySuccess).withExpected
                resultSuccess)

/-- The fixed-builtin call path performs only unification, occurrence
allocation, and two expression-node appends. -/
theorem recordBuiltinFunctionCall
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.recordBuiltinFunctionCall source callee name function
      arguments call expected state = .ok result) :
    RecursiveLedgerInvariant result.2 pending := by
  unfold Detail.recordBuiltinFunctionCall at success
  simp only [bind, Except.bind] at success
  split at success
  next arityMatches =>
    cases argumentsSuccess : Detail.unifyBuiltinFunctionArgumentsEqual
        arguments function.parameterTypes state with
    | error error =>
        simp [argumentsSuccess, bind, Except.bind] at success
    | ok argumentsState =>
        simp only [argumentsSuccess, bind, Except.bind] at success
        have argumentsLedger :=
          tracked.unifyBuiltinFunctionArgumentsEqual argumentsSuccess
        cases expected with
        | none =>
            simp only [pure, Pure.pure, Except.pure] at success
            let allocation := argumentsState.allocateExpressionId
            let calleeExpression : InferredExpression := {
              id := allocation.1
              type := function.type
            }
            have calleeLedger :=
              argumentsLedger.allocateExpressionId.recordExpressionOperation callee
                calleeExpression (.reference name (.builtinFunction function))
                [] []
            let callExpression : InferredExpression := {
              id := call
              type := allocation.2.resolve function.returnType
            }
            have resultEq :
                Detail.recordExpression source callExpression
                  (.call allocation.1 (arguments.map (·.id))
                    (.builtinFunction function)) [] []
                  (Detail.recordExpression callee calleeExpression
                    (.reference name (.builtinFunction function)) [] []
                    allocation.2).2 = result := by
              simpa [allocation, calleeExpression, callExpression,
                Detail.recordExpression, State.recordNode, State.resolve] using
                success
            rw [← resultEq]
            exact calleeLedger.recordExpressionOperation source callExpression
              (.call allocation.1 (arguments.map (·.id))
                (.builtinFunction function)) [] []
        | some expectedType =>
            cases expectedSuccess : Detail.unify argumentsState
                function.returnType expectedType with
            | error error =>
                simp [expectedSuccess, bind, Except.bind] at success
            | ok expectedState =>
                simp only [expectedSuccess, bind, Except.bind] at success
                let allocation := expectedState.allocateExpressionId
                let calleeExpression : InferredExpression := {
                  id := allocation.1
                  type := function.type
                }
                have calleeLedger :=
                  (argumentsLedger.unify expectedSuccess).allocateExpressionId
                    |>.recordExpressionOperation callee calleeExpression
                      (.reference name (.builtinFunction function)) [] []
                let callExpression : InferredExpression := {
                  id := call
                  type := allocation.2.resolve function.returnType
                }
                have resultEq :
                    Detail.recordExpression source callExpression
                      (.call allocation.1 (arguments.map (·.id))
                        (.builtinFunction function)) [] []
                      (Detail.recordExpression callee calleeExpression
                        (.reference name (.builtinFunction function)) [] []
                        allocation.2).2 = result := by
                  simpa [allocation, calleeExpression, callExpression,
                    Detail.recordExpression, State.recordNode, State.resolve]
                    using success
                rw [← resultEq]
                exact calleeLedger.recordExpressionOperation source callExpression
                  (.call allocation.1 (arguments.map (·.id))
                    (.builtinFunction function)) [] []
  next arityMismatch =>
    simp at success

private theorem bindLambdaParametersResult
    {context : Frontend.SourceInference.Context}
    {parameters : List Syntax.LambdaParameter} {index : Nat}
    {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.bindLambdaParameters context parameters index seen state =
      .ok result) :
    RecursiveLedgerInvariant result.2.2 pending := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [Detail.bindLambdaParameters] at success
      injection success with resultEq
      subst result
      exact tracked
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [Detail.bindLambdaParameters, parameterValue, bind,
            Except.bind] at success
      | inferred name =>
          simp only [Detail.bindLambdaParameters, parameterValue] at success
          simp only [bind, Except.bind] at success
          repeat' first | split at success
          all_goals try simp_all only [exceptPure_eq_ok]
          all_goals try simp_all
          all_goals
            subst result
            subst_vars
            have tailLedger := induction _ _ _
              (tracked.fresh.allocateBinderWithoutRequirements name.value
                (.mono state.fresh.1) (some parameter.span)) (by assumption)
            exact tailLedger
      | typed marker name sourceType =>
          simp only [Detail.bindLambdaParameters, parameterValue] at success
          cases resolution : Detail.resolveSourceType context sourceType with
          | error error =>
              simp [resolution, bind, Except.bind] at success
          | ok parameterType =>
              simp only [resolution, bind, Except.bind] at success
              repeat' first | split at success
              all_goals try simp_all only [exceptPure_eq_ok]
              all_goals try simp_all
              all_goals
                subst result
                subst_vars
                have tailLedger := induction _ _ _
                  (tracked.allocateBinderWithoutRequirements name.value
                    (.mono parameterType) (some parameter.span) marker.isSome)
                  (by assumption)
                exact tailLedger

/-! The public projection names the three returned components explicitly. -/
theorem bindLambdaParameters
    {context : Frontend.SourceInference.Context}
    {parameters : List Syntax.LambdaParameter} {index : Nat}
    {seen : List String} {state final : State}
    {binders : List TypedBinder} {types : List Ty}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.bindLambdaParameters context parameters index seen state =
      .ok (binders, types, final)) :
    RecursiveLedgerInvariant final pending := by
  exact bindLambdaParametersResult tracked success

private abbrev finishOperatorLedger
    (context : Frontend.SourceInference.Context)
    (dispatch : Detail.OperatorDispatch)
    (operand builtin builtinResult resultType : Ty)
    (parameterTypes : List Ty) (hasOpenLiteralOperand : Bool)
    (state : State) : Except Error Detail.OperatorInferenceResult :=
  if operand = builtin then
    pure { type := builtinResult, requirements := [], state }
  else
    match dispatch with
    | .function name =>
        if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
              builtin operand ||
            Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand
              builtin operand then
          pure { type := resultType, requirements := [], state }
        else
          throw (.unknownVariable name)
    | .traitMethod traitName methodName => do
        match ← Detail.operatorTrait? context traitName with
        | some trait =>
            let predicates ← Detail.operatorTraitPredicates context trait
              methodName operand parameterTypes [resultType]
            let (requirements, state) :=
              state.addRequirementsWithIds predicates
            pure { type := resultType, requirements, state }
        | none =>
            if Detail.isDeferredBuiltinOperatorTarget state
                  hasOpenLiteralOperand builtin operand ||
                Detail.isStagedIntegerOperatorTarget state
                  hasOpenLiteralOperand builtin operand then
              pure { type := resultType, requirements := [], state }
            else
              throw (.operatorNotSupported traitName operand)

private theorem finishOperatorLedger_evolution
    {context : Frontend.SourceInference.Context}
    {dispatch : Detail.OperatorDispatch}
    {operand builtin builtinResult resultType : Ty}
    {parameterTypes : List Ty} {hasOpenLiteralOperand : Bool}
    {state : State} {result : Detail.OperatorInferenceResult}
    (success : finishOperatorLedger context dispatch operand builtin
      builtinResult resultType parameterTypes hasOpenLiteralOperand state =
        .ok result) :
    LedgerEvolution state result.state := by
  unfold finishOperatorLedger at success
  by_cases builtinMatch : operand = builtin
  · simp only [builtinMatch, if_true] at success
    injection success with resultEq
    subst result
    exact .refl state
  · simp only [builtinMatch, if_false] at success
    cases dispatch with
    | function name =>
        cases deferredResult :
            (Detail.isDeferredBuiltinOperatorTarget state
                hasOpenLiteralOperand builtin operand ||
              Detail.isStagedIntegerOperatorTarget state
                hasOpenLiteralOperand builtin operand) with
        | false => simp [deferredResult] at success
        | true =>
            simp only [deferredResult, if_true] at success
            injection success with resultEq
            subst result
            exact .refl state
    | traitMethod traitName methodName =>
        cases traitResult : Detail.operatorTrait? context traitName with
        | error error =>
            simp [traitResult, bind, Except.bind] at success
        | ok traitOption =>
            cases traitOption with
            | none =>
                simp only [traitResult, bind, Except.bind] at success
                cases deferredResult :
                    (Detail.isDeferredBuiltinOperatorTarget state
                        hasOpenLiteralOperand builtin operand ||
                      Detail.isStagedIntegerOperatorTarget state
                        hasOpenLiteralOperand builtin operand) with
                | false => simp [deferredResult] at success
                | true =>
                    simp only [deferredResult, if_true] at success
                    injection success with resultEq
                    subst result
                    exact .refl state
            | some trait =>
                simp only [traitResult, bind, Except.bind] at success
                cases predicatesResult : Detail.operatorTraitPredicates context
                    trait methodName operand parameterTypes [resultType] with
                | error error =>
                    simp [predicatesResult, bind, Except.bind] at success
                | ok predicates =>
                    simp only [predicatesResult, bind, Except.bind] at success
                    change Except.ok {
                      type := resultType
                      requirements :=
                        (state.addRequirementsWithIds predicates).1
                      state := (state.addRequirementsWithIds predicates).2
                    } = Except.ok result at success
                    injection success with resultEq
                    subst result
                    exact .addRequirements state predicates

private abbrev finishUnaryOperatorLedger
    (context : Frontend.SourceInference.Context)
    (operator : Syntax.UnaryOp) (operandType : Ty)
    (hasOpenLiteralOperand : Bool) (state : State) :
    Except Error Detail.OperatorInferenceResult :=
  let operand := state.resolve operandType
  let builtin := match operator with
    | .logicalNot => Ty.bool
    | .bitNot => Ty.word
  finishOperatorLedger context (Detail.unaryOperatorDispatch operator)
    operand builtin builtin
    (if operator == Syntax.UnaryOp.logicalNot then .bool else operand)
    [operand] hasOpenLiteralOperand state

private theorem finishUnaryOperatorLedger_evolution
    {context : Frontend.SourceInference.Context}
    {operator : Syntax.UnaryOp} {operandType : Ty}
    {hasOpenLiteralOperand : Bool} {state : State}
    {result : Detail.OperatorInferenceResult}
    (success : finishUnaryOperatorLedger context operator operandType
      hasOpenLiteralOperand state = .ok result) :
    LedgerEvolution state result.state := by
  exact finishOperatorLedger_evolution
    (by simpa only [finishUnaryOperatorLedger] using success)

private abbrev finishBinaryOperatorLedger
    (context : Frontend.SourceInference.Context)
    (operator : Syntax.BinaryOp) (left : Ty)
    (hasOpenLiteralOperand : Bool) (state : State) :
    Except Error Detail.OperatorInferenceResult :=
  let operand := state.resolve left
  let builtin := Detail.binaryBuiltinType operator
  finishOperatorLedger context (Detail.binaryOperatorDispatch operator)
    operand builtin
    (if Detail.binaryResultIsBool operator then .bool else builtin)
    (if Detail.binaryResultIsBool operator then .bool else operand)
    [operand, operand] hasOpenLiteralOperand state

private theorem finishBinaryOperatorLedger_evolution
    {context : Frontend.SourceInference.Context}
    {operator : Syntax.BinaryOp} {left : Ty}
    {hasOpenLiteralOperand : Bool} {state : State}
    {result : Detail.OperatorInferenceResult}
    (success : finishBinaryOperatorLedger context operator left
      hasOpenLiteralOperand state = .ok result) :
    LedgerEvolution state result.state := by
  exact finishOperatorLedger_evolution
    (by simpa only [finishBinaryOperatorLedger] using success)

/-- Unary operator resolution only performs unification and canonical
requirement allocation. -/
theorem inferUnaryOperator
    {context : Frontend.SourceInference.Context}
    {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : Detail.OperatorInferenceResult}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    RecursiveLedgerInvariant result.state pending := by
  let hasOpenLiteralOperand :=
    Detail.isOpenIntegerLiteralTarget state integerLiterals operandType
  unfold Detail.inferUnaryOperator at success
  cases expected with
  | none =>
      simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at success
      have tailSuccess : finishUnaryOperatorLedger context operator operandType
          hasOpenLiteralOperand state = .ok result := by
        change finishUnaryOperatorLedger context operator operandType
          hasOpenLiteralOperand state = .ok result at success
        exact success
      exact (finishUnaryOperatorLedger_evolution tailSuccess).preserve tracked
  | some expectedType =>
      cases skipResult :
          (operator == Syntax.UnaryOp.logicalNot ||
            (state.resolve operandType).freeVariables.isEmpty ||
              !hasOpenLiteralOperand) with
      | true =>
          simp only [hasOpenLiteralOperand, skipResult, if_true, bind,
            Except.bind, pure, Pure.pure, Except.pure] at success
          have tailSuccess : finishUnaryOperatorLedger context operator
              operandType hasOpenLiteralOperand state = .ok result := by
            change finishUnaryOperatorLedger context operator operandType
              hasOpenLiteralOperand state = .ok result at success
            exact success
          exact (finishUnaryOperatorLedger_evolution tailSuccess).preserve
            tracked
      | false =>
          simp only [hasOpenLiteralOperand, skipResult, Bool.false_eq_true,
            if_false] at success
          cases unifyResult : Detail.unify state (state.resolve operandType)
              expectedType with
          | error error =>
              simp [unifyResult, bind, Except.bind] at success
          | ok fittedState =>
              simp only [unifyResult, bind, Except.bind] at success
              have tailSuccess : finishUnaryOperatorLedger context operator
                  operandType hasOpenLiteralOperand fittedState = .ok result := by
                change finishUnaryOperatorLedger context operator operandType
                  hasOpenLiteralOperand fittedState = .ok result at success
                exact success
              exact (LedgerEvolution.trans (.unify unifyResult)
                (finishUnaryOperatorLedger_evolution tailSuccess)).preserve
                  tracked

/-- Binary operator resolution has the same ledger-only effect. -/
theorem inferBinaryOperator
    {context : Frontend.SourceInference.Context}
    {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : Detail.OperatorInferenceResult}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    RecursiveLedgerInvariant result.state pending := by
  let hasOpenLiteralOperand :=
    Detail.isOpenIntegerLiteralTarget state integerLiterals left ||
      Detail.isOpenIntegerLiteralTarget state integerLiterals right
  unfold Detail.inferBinaryOperator at success
  cases unifyResult : Detail.unify state left right with
  | error error =>
      simp [unifyResult, bind, Except.bind] at success
  | ok unifiedState =>
      simp only [unifyResult, bind, Except.bind] at success
      cases expected with
      | none =>
          simp only [bind, Except.bind, pure, Pure.pure, Except.pure]
            at success
          have tailSuccess : finishBinaryOperatorLedger context operator left
              hasOpenLiteralOperand unifiedState = .ok result := by
            change finishBinaryOperatorLedger context operator left
              hasOpenLiteralOperand unifiedState = .ok result at success
            exact success
          exact (LedgerEvolution.trans (.unify unifyResult)
            (finishBinaryOperatorLedger_evolution tailSuccess)).preserve tracked
      | some expectedType =>
          cases skipResult :
              (Detail.binaryResultIsBool operator ||
                (unifiedState.resolve left).freeVariables.isEmpty ||
                  !hasOpenLiteralOperand) with
          | true =>
              simp only [hasOpenLiteralOperand, skipResult, if_true, bind,
                Except.bind, pure, Pure.pure, Except.pure] at success
              have tailSuccess : finishBinaryOperatorLedger context operator
                  left hasOpenLiteralOperand unifiedState = .ok result := by
                change finishBinaryOperatorLedger context operator left
                  hasOpenLiteralOperand unifiedState = .ok result at success
                exact success
              exact (LedgerEvolution.trans (.unify unifyResult)
                (finishBinaryOperatorLedger_evolution tailSuccess)).preserve
                  tracked
          | false =>
              simp only [hasOpenLiteralOperand, skipResult,
                Bool.false_eq_true, if_false] at success
              cases fittedResult : Detail.unify unifiedState
                  (unifiedState.resolve left) expectedType with
              | error error =>
                  simp [fittedResult, bind, Except.bind] at success
              | ok fittedState =>
                  simp only [fittedResult, bind, Except.bind] at success
                  have tailSuccess : finishBinaryOperatorLedger context operator
                      left hasOpenLiteralOperand fittedState = .ok result := by
                    change finishBinaryOperatorLedger context operator left
                      hasOpenLiteralOperand fittedState = .ok result at success
                    exact success
                  exact (LedgerEvolution.trans (.unify unifyResult)
                    (LedgerEvolution.trans (.unify fittedResult)
                      (finishBinaryOperatorLedger_evolution tailSuccess)))
                        |>.preserve tracked

end RecursiveLedgerInvariant

/-- Source-ordered argument traversal preserves an arbitrary pending suffix
using only the actual smaller-fuel head and tail traces. -/
theorem inferExprsFuelLedgerPreservation_step
    {fuel : Nat}
    (exprIH : ∀ childFuel, childFuel < fuel →
      InferExprFuelLedgerPreservation childFuel)
    (exprsIH : ∀ childFuel, childFuel < fuel →
      InferExprsFuelLedgerPreservation childFuel) :
    InferExprsFuelLedgerPreservation fuel := by
  intro context expressions initial final inferred pending success initialLedger
  cases fuel with
  | zero =>
      simp [Detail.inferExprsFuel] at success
  | succ childFuel =>
      cases expressions with
      | nil =>
          simp [Detail.inferExprsFuel] at success
          rcases success with ⟨rfl, rfl⟩
          exact initialLedger
      | cons expression rest =>
          unfold Detail.inferExprsFuel at success
          cases headSuccess : Detail.inferExprFuel childFuel context expression
              none initial with
          | error error =>
              simp [headSuccess, bind, Except.bind] at success
          | ok head =>
              rcases head with ⟨headExpression, headState⟩
              simp only [headSuccess, bind, Except.bind] at success
              cases tailSuccess : Detail.inferExprsFuel childFuel context rest
                  headState with
              | error error =>
                  simp [tailSuccess, bind, Except.bind] at success
              | ok tail =>
                  rcases tail with ⟨tailExpressions, tailState⟩
                  simp only [tailSuccess, bind, Except.bind, pure, Pure.pure,
                    Except.pure, Except.ok.injEq] at success
                  rcases success with ⟨rfl, rfl⟩
                  exact exprsIH childFuel (Nat.lt_succ_self childFuel)
                    tailSuccess
                    (exprIH childFuel (Nat.lt_succ_self childFuel)
                      headSuccess initialLedger)

/-- Constructor payload traversal is structurally recursive at one fixed
fuel.  Once expression preservation is known at that fuel, list induction
closes the whole traversal. -/
theorem inferConstructorArgumentsFuelLedgerPreservation_of_expr
    {fuel : Nat}
    (exprSound : InferExprFuelLedgerPreservation fuel) :
    InferConstructorArgumentsFuelLedgerPreservation fuel := by
  intro context arguments expected initial final inferred pending success
    initialLedger
  induction arguments generalizing expected initial final inferred with
  | nil =>
      cases expected with
      | nil =>
          simp [Detail.inferConstructorArgumentsFuel] at success
          rcases success with ⟨rfl, rfl⟩
          exact initialLedger
      | cons expected rest =>
          simp [Detail.inferConstructorArgumentsFuel] at success
  | cons argument rest induction =>
      cases expected with
      | nil =>
          simp [Detail.inferConstructorArgumentsFuel] at success
      | cons expectedType expectedRest =>
          unfold Detail.inferConstructorArgumentsFuel at success
          cases headSuccess : Detail.inferExprFuel fuel context argument
              (some (initial.resolve expectedType)) initial with
          | error error =>
              simp [headSuccess, bind, Except.bind] at success
          | ok head =>
              rcases head with ⟨headExpression, headState⟩
              simp only [headSuccess, bind, Except.bind] at success
              cases tailSuccess : Detail.inferConstructorArgumentsFuel fuel
                  context rest expectedRest headState with
              | error error =>
                  simp [tailSuccess, bind, Except.bind] at success
              | ok tail =>
                  rcases tail with ⟨tailExpressions, tailState⟩
                  simp only [tailSuccess, bind, Except.bind, pure, Pure.pure,
                    Except.pure, Except.ok.injEq] at success
                  rcases success with ⟨rfl, rfl⟩
                  exact induction tailSuccess
                    (exprSound headSuccess initialLedger)

/-- Constructor application adds only ordinary argument expression nodes and
its own constructor expression node. -/
theorem inferConstructorApplicationFuelLedgerPreservation_of_arguments
    {fuel : Nat}
    (argumentsSound :
      InferConstructorArgumentsFuelLedgerPreservation fuel) :
    InferConstructorApplicationFuelLedgerPreservation fuel := by
  intro context source id instantiation arguments expected initial final
    inferred pending success initialLedger
  unfold Detail.inferConstructorApplicationFuel at success
  simp only [bind, Except.bind] at success
  split at success
  next arityMatches =>
    cases expected with
    | none =>
        simp only [pure, Pure.pure, Except.pure] at success
        cases argumentsSuccess : Detail.inferConstructorArgumentsFuel fuel
            context arguments instantiation.payloadTypes initial with
        | error error =>
            simp [argumentsSuccess, bind, Except.bind] at success
        | ok payload =>
            rcases payload with ⟨payloadExpressions, payloadState⟩
            simp only [argumentsSuccess, bind, Except.bind] at success
            exact (argumentsSound argumentsSuccess initialLedger)
              |>.recordExpressionWithExpected success
    | some expectedType =>
        cases unifySuccess : Detail.unify initial instantiation.resultType
            expectedType with
        | error error =>
            simp [unifySuccess, bind, Except.bind] at success
        | ok fittedState =>
            simp only [unifySuccess, bind, Except.bind] at success
            cases argumentsSuccess : Detail.inferConstructorArgumentsFuel fuel
                context arguments instantiation.payloadTypes fittedState with
            | error error =>
                simp [argumentsSuccess, bind, Except.bind] at success
            | ok payload =>
                rcases payload with ⟨payloadExpressions, payloadState⟩
                simp only [argumentsSuccess, bind, Except.bind] at success
                exact (argumentsSound argumentsSuccess
                    (initialLedger.unify unifySuccess))
                  |>.recordExpressionWithExpected success
  next arityMismatch =>
    simp at success

end Solcore.SourceSemantics.SourceInferenceSoundness
