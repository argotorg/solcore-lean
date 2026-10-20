import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts
import Solcore.SourceSemantics.SourceInferenceGeneralizedStatementRecording
import Solcore.SourceSemantics.SourceInferenceClosedLeftUnificationPrivacy

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open SourceInferenceStatementsSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}

theorem statement_break
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (form : statement.value = .breakStmt)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨_, resultEq, _⟩ :=
    inferStatementFuel_success_break_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨active, localTyping, agreement⟩ :=
    inferStatementFuel_success_break_sound form rfl boundary.accepted boundary.invariant.active (bodyRoots selected)
  have typing := (boundary.rawSubtree.finalized selected.body.resources).subgraph.statement
    localTyping (.inl rfl)
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact boundary.operational.allocateStatementId.recordStatement _ rfl
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simp [resultEq, State.recordNode]
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  exact ⟨target, _, invariant, boundary.actual, operational, typing, agreement⟩

theorem statement_continue
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (form : statement.value = .continueStmt)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨_, resultEq, _⟩ :=
    inferStatementFuel_success_continue_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨active, localTyping, agreement⟩ :=
    inferStatementFuel_success_continue_sound form rfl boundary.accepted boundary.invariant.active (bodyRoots selected)
  have typing := (boundary.rawSubtree.finalized selected.body.resources).subgraph.statement
    localTyping (.inl rfl)
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact boundary.operational.allocateStatementId.recordStatement _ rfl
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simp [resultEq, State.recordNode]
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  exact ⟨target, _, invariant, boundary.actual, operational, typing, agreement⟩

/-- Bare return uses its real closed-left unification. The ambient return type
may be a fresh lambda variable; no expected-return privacy premise is needed. -/
theorem statement_returnUnit
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (form : statement.value = .returnStmt none)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨unified, accepted, _, resultEq, _⟩ :=
    inferStatementFuel_success_returnUnit_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨active, localTyping, agreement⟩ :=
    inferStatementFuel_success_returnUnit_sound form rfl boundary.accepted boundary.invariant.active
      boundary.extension (bodyRoots selected)
  have typing := (boundary.rawSubtree.finalized selected.body.resources).subgraph.statement
    localTyping (.inl rfl)
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have unifiedOperational := boundary.operational.allocateStatementId.unifyClosedLeft allocatedInvariant.ready
    (Ty.variablesBelow_constructor 0 _) allocatedInvariant.returnBelow accepted
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact unifiedOperational.recordStatement _ rfl
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have same := congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope accepted)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using same
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq) typing
  exact ⟨target, _, invariant, boundary.actual, operational, typing, agreement⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
