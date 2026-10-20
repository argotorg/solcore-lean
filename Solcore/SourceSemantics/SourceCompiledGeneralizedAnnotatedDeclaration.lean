import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts
import Solcore.SourceSemantics.SourceInferenceGeneralizedStatementRecording
import Solcore.SourceSemantics.SourceInferenceGeneralizedLambdaParameters

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

theorem statement_annotatedUninitialized
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .letDecl name (some sourceType) none)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have parameters := boundary.scope.canonical checked
  have signaturesEq := (RecursiveExpressionInvariant.ofStatement boundary.invariant).signatures_eq_whole.trans boundary.scope.signatures.symm
  have parametersEq := boundary.invariant.typeParametersEq.trans boundary.scope.parameters.symm
  have ownerEq : target.currentDeclaration = some inferenceContext.scope.genericOwner := by
    rw [boundary.scope.owner]
    exact boundary.invariant.declarationEq
  obtain ⟨resolvedType, locals, valueType, generalized, binding,
      resolution, _localsEq, valueTypeEq, generalizedEq, bindingEq, resultEq, _contains⟩ :=
    inferStatementFuel_success_letAnnotatedUninitialized_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨wellFormed, _closedScheme, _closedRequirements, _generalizes⟩ :=
    resolvedAnnotationBinderFacts_afterSubstitution
      (target := target) (outer := selected.body.finalized.substitution)
      resolution valueTypeEq generalizedEq bindingEq parameters signaturesEq parametersEq ownerEq
  have resolvedByState : initial.allocateStatementId.2.resolve resolvedType = resolvedType := by
    simpa [State.resolve, InferState.resolve] using
      Detail.resolveSourceType_success_apply_eq_self initial.allocateStatementId.2.inference.substitution resolution
  have valueClosed : valueType.freeVariables = [] := by
    rw [valueTypeEq]
    change (initial.allocateStatementId.2.resolve resolvedType).freeVariables = []
    rw [resolvedByState]
    exact StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil wellFormed
  have schemeEq : generalized.scheme = .mono valueType := by
    rw [generalizedEq]
    exact (generalizeValue_closed_facts initial.allocateStatementId.2 locals
      initial.allocateStatementId.2.nextRequirement valueType target valueClosed).1
  have requirementsEq : generalized.requirements = [] := by
    rw [generalizedEq]
    exact (generalizeValue_closed_facts initial.allocateStatementId.2 locals
      initial.allocateStatementId.2.nextRequirement valueType target valueClosed).2.1
  have allocatedIsolated := activeSchemeQuantifierIsolation_allocateStatementId boundary.invariant.schemeIsolation rfl
  have bindingIsolated : ActiveSchemeQuantifierIsolation binding.2 := by
    rw [← bindingEq, schemeEq, requirementsEq]
    exact activeSchemeQuantifierIsolation_allocateMonoBinder
      (initial.allocateStatementId.2.withLocals locals) name.value valueType (some name.span)
      (activeSchemeQuantifierIsolation_transport allocatedIsolated rfl)
      (by intro metavariable member; simp [valueClosed] at member)
  have bindingOperational : GeneralizedActualStateInvariant binding.2 (evidenceSource selected) := by
    rw [← bindingEq, schemeEq, requirementsEq]
    apply (boundary.operational.allocateStatementId.withLocals locals).allocateMonoBinder
    intro binder member
    exact ProtectedVariables.safe_closed _ _
      (by intro metavariable present; simp [valueClosed] at present)
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact bindingOperational.recordStatement _ rfl
  have isolation : ActiveSchemeQuantifierIsolation result.state := by
    rw [resultEq]
    exact activeSchemeQuantifierIsolation_transport bindingIsolated rfl
  obtain ⟨finalContext, facts, active, localTyping, agreement⟩ :=
    inferStatementFuel_success_letAnnotatedUninitialized_sound form rfl boundary.accepted parameters
      signaturesEq parametersEq ownerEq boundary.invariant.active boundary.invariant.bindersBelow
      (bodyRoots selected)
  have typing := (boundary.rawSubtree.finalized selected.body.resources).subgraph.statement localTyping (.inl rfl)
  have invariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension isolation typing
  exact ⟨finalContext, facts, invariant, boundary.actual.of_statement typing, operational, typing, agreement⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
