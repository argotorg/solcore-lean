import Solcore.SourceSemantics.SourceInferenceLedgerInvariant

/-!
The source-ordered statement-list half of recursive ledger preservation.
Only the actual head and tail computations returned by the executable
inference function are passed to the smaller-fuel induction hypotheses.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

namespace RecursiveLedgerInvariant

theorem unify {state next : State} {left right : Ty}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (success : Detail.unify state left right = .ok next) :
    RecursiveLedgerInvariant next pending := by
  unfold Detail.unify at success
  cases unification : state.inference.unify left right with
  | error error =>
      simp [unification, Detail.liftUnification, bind, Except.bind] at success
  | ok inference =>
      simp only [unification, Detail.liftUnification, bind, Except.bind] at success
      change Except.ok { state with inference } = Except.ok next at success
      injection success with nextEq
      subst next
      constructor
      · change state.RequirementsWellFormed
        exact tracked.requirements
      · constructor
        · change state.localSchemeAssumptions.Perm
            (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ pending)
          exact tracked.templates.classified
        · change state.localSchemeAssumptions.Nodup
          exact tracked.templates.unique
        · change ∀ id, id ∈ state.localSchemeAssumptions →
            id ∈ state.requirements.map (fun requirement => requirement.id)
          exact tracked.templates.covered

/-- Reserving a statement occurrence does not touch either ledger. -/
theorem allocateStatementId {state : State}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending) :
    RecursiveLedgerInvariant state.allocateStatementId.2 pending := by
  constructor
  · exact State.allocateStatementId_preserves_requirementsWellFormed
      state tracked.requirements
  · constructor
    · change state.localSchemeAssumptions.Perm
        (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ pending)
      exact tracked.templates.classified
    · change state.localSchemeAssumptions.Nodup
      exact tracked.templates.unique
    · change ∀ id, id ∈ state.localSchemeAssumptions →
        id ∈ state.requirements.map (fun requirement => requirement.id)
      exact tracked.templates.covered

/-- A statement without initialized `let` bindings does not materialize any
qualified template identities when it is recorded. -/
theorem recordStatement_noBindings {state : State}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (node : StatementNode)
    (noBindings : statementInitializedLetBindings node.form = []) :
    RecursiveLedgerInvariant (state.recordNode (.statement node)) pending := by
  constructor
  · exact State.recordNode_preserves_requirementsWellFormed state
      (.statement node) tracked.requirements
  · apply TemplateTracking.recordNode
    simpa [nodeLocalSchemeTemplateIds, noBindings] using tracked.templates

/-- Materialize exactly the templates allocated by an initialized `let` or
the combined `for` header, leaving enclosing pending templates untouched. -/
theorem recordStatement {state : State}
    {pending : List RequirementId} (node : StatementNode)
    (tracked : RecursiveLedgerInvariant state
      (pending ++ nodeLocalSchemeTemplateIds (.statement node))) :
    RecursiveLedgerInvariant (state.recordNode (.statement node)) pending := by
  exact ⟨State.recordNode_preserves_requirementsWellFormed state
      (.statement node) tracked.requirements,
    tracked.templates.recordNode⟩

/-- A generalized header or statement binder contributes a pending suffix
whose IDs are the exact qualified requirement templates of that binder. -/
theorem allocateGeneralizedValue {state : State}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending)
    (locals : TypeSystem.Environment) (requirementStart : Nat)
    (type : Ty) (name : String)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false) :
    let generalized := Detail.generalizeValue state locals requirementStart
      type
    RecursiveLedgerInvariant
      ((state.withLocals locals).allocateBinder name generalized.scheme span
        comptime generalized.requirements).2
      (pending ++ generalized.requirements.map fun requirement =>
        requirement.templateRequirement) := by
  dsimp only
  constructor
  · exact State.allocateBinder_preserves_requirementsWellFormed
      (state.withLocals locals) name
      (Detail.generalizeValue state locals requirementStart type).scheme
      span comptime
      (Detail.generalizeValue state locals requirementStart type).requirements
      (State.withLocals_preserves_requirementsWellFormed state locals
        tracked.requirements)
  · exact tracked.templates.allocateGeneralizedValue tracked.requirements
      locals requirementStart type name span comptime

theorem restoreLexicalScope {state : State}
    {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant state pending) (scope : LexicalScope) :
    RecursiveLedgerInvariant (state.restoreLexicalScope scope) pending := by
  exact ⟨State.restoreLexicalScope_preserves_requirementsWellFormed state
      scope tracked.requirements,
    tracked.templates.restoreLexicalScope scope⟩

end RecursiveLedgerInvariant

/-- A binder without an initializer starts its generalization barrier at the
current end of the canonical requirement ledger, so it has no newly
introduced qualified-template rows. -/
theorem generalizeValue_requirements_empty_at_next
    (state : State) (locals : TypeSystem.Environment) (type : Ty)
    (wellFormed : state.RequirementsWellFormed) :
    (Detail.generalizeValue state locals state.nextRequirement type
      ).requirements = [] := by
  have lengthEq : state.requirements.length = state.nextRequirement := by
    have congruent := congrArg List.length wellFormed
    simpa [State.RequirementsWellFormed] using congruent
  simp [Detail.generalizeValue, ← lengthEq]

/-- The allocation/materialization pair used by an initialized source let
moves its generalized requirement IDs from `pending` into the recorded
statement node without changing ambient pending IDs. -/
theorem generalizedInitializedLet_record_ledger
    {state binderState : State} {pending : List RequirementId}
    {locals : TypeSystem.Environment} {requirementStart : Nat}
    {type : Ty} {name : Syntax.Identifier}
    {generalized : Detail.GeneralizedValue} {binder : TypedBinder}
    {id : StatementId} {span : Syntax.SourceSpan}
    {initializer : ExpressionId}
    (tracked : RecursiveLedgerInvariant state pending)
    (generalizedEq : generalized = Detail.generalizeValue state locals
      requirementStart type)
    (bindingEq : (state.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false generalized.requirements =
        (binder, binderState)) :
    RecursiveLedgerInvariant
      (binderState.recordNode (.statement {
        id, span, type := .unit,
        form := .letDecl binder (some initializer) })) pending := by
  have allocatedTracked : RecursiveLedgerInvariant binderState
      (pending ++ generalized.requirements.map fun requirement =>
        requirement.templateRequirement) := by
    simpa [← generalizedEq, bindingEq] using
      tracked.allocateGeneralizedValue locals requirementStart type
        name.value (some name.span)
  have binderRequirementsEq : binder.schemeRequirements =
      generalized.requirements := by
    have projected := congrArg
      (fun pair : TypedBinder × State => pair.1.schemeRequirements) bindingEq
    simpa [State.allocateBinder] using projected.symm
  apply RecursiveLedgerInvariant.recordStatement
  simpa [nodeLocalSchemeTemplateIds, statementInitializedLetBindings,
    binderRequirementsEq] using allocatedTracked

/-- An uninitialized declaration allocates no qualified requirement rows at
the current canonical ledger boundary, so its node has no pending templates
to materialize. -/
theorem generalizedUninitializedLet_record_ledger
    {state binderState : State} {pending : List RequirementId}
    {locals : TypeSystem.Environment} {type : Ty}
    {name : Syntax.Identifier}
    {generalized : Detail.GeneralizedValue} {binder : TypedBinder}
    {id : StatementId} {span : Syntax.SourceSpan}
    (tracked : RecursiveLedgerInvariant state pending)
    (generalizedEq : generalized = Detail.generalizeValue state locals
      state.nextRequirement type)
    (bindingEq : (state.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false generalized.requirements =
        (binder, binderState)) :
    RecursiveLedgerInvariant
      (binderState.recordNode (.statement {
        id, span, type := .unit, form := .letDecl binder none })) pending := by
  have requirementsEmpty : generalized.requirements = [] := by
    rw [generalizedEq]
    exact generalizeValue_requirements_empty_at_next state locals type
      tracked.requirements
  have allocatedTracked : RecursiveLedgerInvariant binderState pending := by
    have trackedWithPending :=
      tracked.allocateGeneralizedValue locals state.nextRequirement type
        name.value (some name.span)
    dsimp only at trackedWithPending
    rw [← generalizedEq, bindingEq] at trackedWithPending
    simpa [requirementsEmpty] using trackedWithPending
  exact allocatedTracked.recordStatement_noBindings _ rfl

/-- Actual unannotated initializer inference, generalized-binder allocation,
and node recording preserve the ambient canonical ledger. -/
theorem inferStatementFuel_letUnannotatedInitialized_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {pending : List RequirementId}
    (statementEq : statement.value =
      .letDecl name none (some initializer))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (expressionIH : InferExprFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
  have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
    simpa [allocationEq] using tracked.allocateStatementId
  obtain ⟨_, initializerState, locals, valueType, generalized, binding,
      initializerSuccess, _, _, generalizedEq, bindingEq, resultEq, _⟩ :=
    inferStatementFuel_success_letUnannotatedInitialized_facts statementEq
      allocationEq success
  rcases binding with ⟨binder, binderState⟩
  rw [resultEq]
  exact generalizedInitializedLet_record_ledger
    (expressionIH initializerSuccess allocatedTracked) generalizedEq bindingEq

/-- The annotated initialized-let branch differs only in source-type
resolution and the initializer's expected type. -/
theorem inferStatementFuel_letAnnotatedInitialized_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expectedReturn : Ty} {initial : State}
    {result : Detail.StatementResult} {pending : List RequirementId}
    (statementEq : statement.value =
      .letDecl name (some sourceType) (some initializer))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (expressionIH : InferExprFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
  have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
    simpa [allocationEq] using tracked.allocateStatementId
  obtain ⟨_, _, initializerState, locals, valueType, generalized, binding,
      _, initializerSuccess, _, _, generalizedEq, bindingEq, resultEq, _⟩ :=
    inferStatementFuel_success_letAnnotatedInitialized_facts statementEq
      allocationEq success
  rcases binding with ⟨binder, binderState⟩
  rw [resultEq]
  exact generalizedInitializedLet_record_ledger
    (expressionIH initializerSuccess allocatedTracked) generalizedEq bindingEq

/-- Resolving an annotation without an initializer allocates no new
qualified templates, so its recorded declaration preserves the ambient
pending suffix. -/
theorem inferStatementFuel_letAnnotatedUninitialized_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {pending : List RequirementId}
    (statementEq : statement.value =
      .letDecl name (some sourceType) none)
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
  have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
    simpa [allocationEq] using tracked.allocateStatementId
  obtain ⟨_, locals, valueType, generalized, binding, _, _, _,
      generalizedEq, bindingEq, resultEq, _⟩ :=
    inferStatementFuel_success_letAnnotatedUninitialized_facts statementEq
      allocationEq success
  rcases binding with ⟨binder, binderState⟩
  rw [resultEq]
  exact generalizedUninitializedLet_record_ledger allocatedTracked
    generalizedEq bindingEq

/-- The bare-return branch only unifies and records a template-free node. -/
theorem inferStatementFuel_returnUnit_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {pending : List RequirementId}
    (statementEq : statement.value = .returnStmt none)
    (success : Detail.inferStatementFuel fuel context statement expectedReturn
      initial = .ok result)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at success
  | succ childFuel =>
      rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
      have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
        simpa [allocationEq] using tracked.allocateStatementId
      obtain ⟨unified, unifiedSuccess, _, resultEq, _⟩ :=
        inferStatementFuel_success_returnUnit_facts statementEq allocationEq
          success
      rw [resultEq]
      exact (allocatedTracked.unify unifiedSuccess).recordStatement_noBindings
        _ rfl

/-- `break` records a template-free node after the statement occurrence. -/
theorem inferStatementFuel_break_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {pending : List RequirementId}
    (statementEq : statement.value = .breakStmt)
    (success : Detail.inferStatementFuel fuel context statement expectedReturn
      initial = .ok result)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at success
  | succ childFuel =>
      rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
      have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
        simpa [allocationEq] using tracked.allocateStatementId
      obtain ⟨_, resultEq, _⟩ :=
        inferStatementFuel_success_break_facts statementEq allocationEq success
      rw [resultEq]
      exact allocatedTracked.recordStatement_noBindings _ rfl

/-- `continue` has the same ledger effect as `break`. -/
theorem inferStatementFuel_continue_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {pending : List RequirementId}
    (statementEq : statement.value = .continueStmt)
    (success : Detail.inferStatementFuel fuel context statement expectedReturn
      initial = .ok result)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  cases fuel with
  | zero => simp [Detail.inferStatementFuel] at success
  | succ childFuel =>
      rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
      have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
        simpa [allocationEq] using tracked.allocateStatementId
      obtain ⟨_, resultEq, _⟩ :=
        inferStatementFuel_success_continue_facts statementEq allocationEq
          success
      rw [resultEq]
      exact allocatedTracked.recordStatement_noBindings _ rfl

/-- An expression statement records no local-scheme templates after its
actual child expression inference. -/
theorem inferStatementFuel_expression_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expression : Syntax.Expr}
    {trailingSemicolon : Bool} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {pending : List RequirementId}
    (statementEq : statement.value =
      .expression expression trailingSemicolon)
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (expressionIH : InferExprFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
  have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
    simpa [allocationEq] using tracked.allocateStatementId
  obtain ⟨_, expressionState, expressionSuccess, resultEq, _⟩ :=
    inferStatementFuel_success_expression_facts statementEq allocationEq
      success
  rw [resultEq]
  exact (expressionIH expressionSuccess allocatedTracked).recordStatement_noBindings
    _ rfl

/-- A value return has the same ledger effect as its actual child expression
followed by a template-free return node. -/
theorem inferStatementFuel_returnValue_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {value : Syntax.Expr}
    {expectedReturn : Ty} {initial : State}
    {result : Detail.StatementResult} {pending : List RequirementId}
    (statementEq : statement.value = .returnStmt (some value))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (expressionIH : InferExprFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
  have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
    simpa [allocationEq] using tracked.allocateStatementId
  obtain ⟨_, valueState, valueSuccess, resultEq, _⟩ :=
    inferStatementFuel_success_returnValue_facts statementEq allocationEq
      success
  rw [resultEq]
  exact (expressionIH valueSuccess allocatedTracked).recordStatement_noBindings
    _ rfl

/-- A value assignment delegates all ledger-changing work to its actual
place/value traversal. -/
theorem inferStatementFuel_assignValue_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : Ty} {initial : State}
    {result : Detail.StatementResult} {pending : List RequirementId}
    (statementEq : statement.value =
      .assignValue targetExpression operator value)
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (assignmentIH : InferAssignedValueFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
  have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
    simpa [allocationEq] using tracked.allocateStatementId
  obtain ⟨_, _, assignmentState, assignmentSuccess, resultEq, _⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq
      success
  rw [resultEq]
  exact (assignmentIH assignmentSuccess allocatedTracked).recordStatement_noBindings
    _ rfl

/-- Bit-not assignment follows its actual place traversal with a Word
unification and a template-free statement node. -/
theorem inferStatementFuel_assignBitNot_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {pending : List RequirementId}
    (statementEq : statement.value =
      .assignBitNot targetExpression operatorSpan)
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (placeIH : InferPlaceFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
  have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
    simpa [allocationEq] using tracked.allocateStatementId
  obtain ⟨_, placeState, unified, placeSuccess, unifiedSuccess, _,
      resultEq, _⟩ :=
    inferStatementFuel_success_assignBitNot_facts statementEq allocationEq
      success
  rw [resultEq]
  exact ((placeIH placeSuccess allocatedTracked).unify unifiedSuccess).recordStatement_noBindings
    _ rfl

/-- A nested block preserves the ambient pending suffix; every initialized
let in its body is materialized by its own statement node. -/
theorem inferStatementFuel_block_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {body : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State}
    {result : Detail.StatementResult} {pending : List RequirementId}
    (statementEq : statement.value = .block body)
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (statementsIH : InferStatementsFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
  have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
    simpa [allocationEq] using tracked.allocateStatementId
  obtain ⟨bodyResult, bodySuccess, resultEq, _⟩ :=
    inferStatementFuel_success_block_facts statementEq allocationEq success
  rw [resultEq]
  exact ((statementsIH bodySuccess allocatedTracked).restoreLexicalScope
    allocated.lexicalScope).recordStatement_noBindings _ rfl

/-- A `while` loop preserves ambient pending templates through condition,
body, lexical restoration, and its final template-free node. -/
theorem inferStatementFuel_whileLoop_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {pending : List RequirementId}
    (statementEq : statement.value = .whileLoop condition body)
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (expressionIH : InferExprFuelLedgerPreservation fuel)
    (statementsIH : InferStatementsFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
  have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
    simpa [allocationEq] using tracked.allocateStatementId
  obtain ⟨_, conditionState, bodyResult, conditionSuccess, bodySuccess,
      resultEq, _⟩ :=
    inferStatementFuel_success_whileLoop_facts statementEq allocationEq
      success
  rw [resultEq]
  exact ((statementsIH bodySuccess
    (expressionIH conditionSuccess allocatedTracked)).restoreLexicalScope
      conditionState.lexicalScope).recordStatement_noBindings _ rfl

/-- The no-else conditional preserves the ambient pending template suffix. -/
theorem inferStatementFuel_ifWithoutElse_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {pending : List RequirementId}
    (statementEq : statement.value = .ifThen condition thenBody none)
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (expressionIH : InferExprFuelLedgerPreservation fuel)
    (statementsIH : InferStatementsFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
  have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
    simpa [allocationEq] using tracked.allocateStatementId
  obtain ⟨_, conditionState, thenResult, conditionSuccess, thenSuccess,
      resultEq, _⟩ :=
    inferStatementFuel_success_ifWithoutElse_facts statementEq allocationEq
      success
  rw [resultEq]
  exact ((statementsIH thenSuccess
    (expressionIH conditionSuccess allocatedTracked)).restoreLexicalScope
      conditionState.lexicalScope).recordStatement_noBindings _ rfl

/-- Both arms of a conditional traverse the same ambient pending suffix in
source order; restoring the first arm's scope does not restore its ledgers. -/
theorem inferStatementFuel_ifWithElse_ledger
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {pending : List RequirementId}
    (statementEq : statement.value =
      .ifThen condition thenBody (some elseBody))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (expressionIH : InferExprFuelLedgerPreservation fuel)
    (statementsIH : InferStatementsFuelLedgerPreservation fuel)
    (tracked : RecursiveLedgerInvariant initial pending) :
    RecursiveLedgerInvariant result.state pending := by
  rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
  have allocatedTracked : RecursiveLedgerInvariant allocated pending := by
    simpa [allocationEq] using tracked.allocateStatementId
  obtain ⟨_, conditionState, thenResult, elseResult, conditionSuccess,
      thenSuccess, elseSuccess, resultEq, _⟩ :=
    inferStatementFuel_success_ifWithElse_facts statementEq allocationEq
      success
  rw [resultEq]
  have thenTracked : RecursiveLedgerInvariant
      (thenResult.state.restoreLexicalScope conditionState.lexicalScope)
      pending :=
    (statementsIH thenSuccess
      (expressionIH conditionSuccess allocatedTracked)).restoreLexicalScope
        conditionState.lexicalScope
  exact ((statementsIH elseSuccess thenTracked).restoreLexicalScope
    conditionState.lexicalScope).recordStatement_noBindings _ rfl

/-- A successful statement list preserves the canonical requirement and
qualified-template ledgers once the actual smaller-fuel head and tail calls
preserve them. -/
theorem inferStatementsFuelLedgerPreservation_step
    {fuel : Nat}
    (statementIH : ∀ childFuel, childFuel < fuel →
      InferStatementFuelLedgerPreservation childFuel)
    (statementsIH : ∀ childFuel, childFuel < fuel →
      InferStatementsFuelLedgerPreservation childFuel) :
    InferStatementsFuelLedgerPreservation fuel := by
  intro context statements expectedReturn initial result pending success
    initialLedger
  cases fuel with
  | zero =>
      simp [Detail.inferStatementsFuel] at success
  | succ childFuel =>
      cases statements with
      | nil =>
          have resultEq := inferStatementsFuel_success_nil_facts success
          subst result
          exact initialLedger
      | cons statement rest =>
          cases rest with
          | nil =>
              obtain ⟨head, headSuccess, resultEq⟩ :=
                inferStatementsFuel_success_singleton_facts success
              subst result
              exact statementIH childFuel (Nat.lt_succ_self childFuel)
                headSuccess initialLedger
          | cons next rest =>
              obtain ⟨head, tail, headSuccess, tailSuccess, resultEq⟩ :=
                inferStatementsFuel_success_cons_facts success
              have tailLedger :=
                statementsIH childFuel (Nat.lt_succ_self childFuel)
                tailSuccess
                (statementIH childFuel (Nat.lt_succ_self childFuel)
                  headSuccess initialLedger)
              simpa [resultEq] using tailLedger

end Solcore.SourceSemantics.SourceInferenceSoundness
