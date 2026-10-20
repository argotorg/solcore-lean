import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts
import Solcore.SourceSemantics.SourceInferenceGeneralizedStatementRecording
import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open SourceInferenceStatementsSoundness

theorem statement_returnValue
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expression : Syntax.Expr} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .returnStmt (some expression))
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target
      (selected.body.finalized.substitution.apply expectedReturn)) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have resources := selected.body.resources
  generalize allocationEq : initial.allocateStatementId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  obtain ⟨inferred, childState, childSuccess, provenance⟩ :=
    inferStatementFuel_success_returnValue_child_provenance form allocationEq
      boundary.accepted boundary.invariant.nodesBelow (bodyRoots selected)
  obtain ⟨actualInferred, actualState, actualSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_returnValue_facts form allocationEq boundary.accepted (bodyRoots selected)
  rw [childSuccess] at actualSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
  have childSubstitutionEq : childState.inference.substitution = result.state.inference.substitution := by
    simp [resultEq, State.recordNode]
  have childEdge : DirectChild (result.state.toTypedSource (bodyRoots selected))
      (.statement result.id) (.expression inferred.id) :=
    directChild_statement_reference containsRaw (by simp [StatementForm.references])
  have containsFinal := (boundary.rawSubtree.finalized resources).containsStatement containsRaw
  have childCovered : TemplateScopeCovered selected.body.finalized.typedSource target
      (.expression inferred.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      boundary.covered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references]
  have childActualCovered : ActualContext.Covers selected.body.finalized frames (.expression inferred.id) :=
    boundary.actualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references])
  have allocatedInvariant := RecursiveExpressionInvariant.ofStatement
    (boundary.invariant.allocateStatementId allocationEq)
  have allocatedOperational : GeneralizedActualStateInvariant allocated (evidenceSource selected) := by
    rw [← show initial.allocateStatementId.2 = allocated from congrArg Prod.snd allocationEq]
    exact boundary.operational.allocateStatementId
  have childExtension : selected.body.finalized.substitution.SemanticallyExtends
      childState.inference.substitution := childSubstitutionEq ▸ boundary.extension
  have childLiterals : childState.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    simpa [resultEq, State.recordNode] using boundary.integerLiterals
  have expectedBelow : ∀ type ∈ (some expectedReturn : Option Ty),
      type.VariablesBelow allocated.inference.next := by
    intro type member
    cases Option.mem_def.mp member
    exact (boundary.invariant.allocateStatementId allocationEq).returnBelow
  have expectedSafe : ∀ binder ∈ allocated.localBinders, ∀ type ∈ (some expectedReturn : Option Ty),
      ProtectedVariables.Safe binder.scheme.quantified allocated type := by
    intro binder present type member
    cases Option.mem_def.mp member
    have stateEq : initial.allocateStatementId.2 = allocated := congrArg Prod.snd allocationEq
    rw [← stateEq] at present ⊢
    exact returnSafe binder present
  have typed := recursive ({
    accepted := childSuccess
    interfaces := boundary.interfaces
    extension := childExtension
    scope := boundary.scope
    invariant := allocatedInvariant
    actual := boundary.actual
    operational := allocatedOperational
    expectedBelow := expectedBelow
    expectedAdmissible := by
      intro type member
      cases Option.mem_def.mp member
      exact returnAdmissible
    expectedSafe := expectedSafe
    integerPatterns := List.Subset.trans provenance.integerPatternsSubset boundary.integerPatterns
    integerLiterals := childLiterals
    requirements := List.Subset.trans provenance.requirementsSubset boundary.requirements
    covered := childCovered
    actualCovered := childActualCovered
    rawSubtree := (boundary.rawSubtree.child childEdge).monoBefore provenance.sourceExtension } :
    RootedExpressionBoundary selected childFuel inferenceContext expression (some expectedReturn)
      allocated inferred childState frames target)
  have childActive := allocatedInvariant.active.inferExprFuel childSuccess
  have childOperational := allocatedOperational.ofExpression allocatedInvariant.ready
    (boundary.scope.catalog checked) (boundary.scope.formation checked)
    (boundary.scope.functionsCanonical checked) expectedBelow expectedSafe childSuccess
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have childEq := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq childSuccess)
    have allocationScope := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using childEq.trans allocationScope
  have expectedEq := Detail.inferExprFuel_expected_type_apply_eq childSuccess childExtension
  have valueTyping : ExpressionHasType selected.body.finalized.typedSource target inferred.id
      (selected.body.finalized.substitution.apply expectedReturn) := expectedEq ▸ typed
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact childActive.recordNode _
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact childOperational.recordStatement _ rfl
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth } target result.id target {
        type := selected.body.finalized.substitution.apply expectedReturn
        hasValue := true, sawReturn := true, control := .returned } := by
    apply StatementHasType.returnValue containsFinal rfl valueTyping
    change selected.body.finalized.substitution.apply result.type = _
    rw [resultEq]
    exact childExtension expectedReturn
  have agreement : StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution result {
      type := selected.body.finalized.substitution.apply expectedReturn
      hasValue := true, sawReturn := true, control := .returned } := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.returned childExtension
  have finalInvariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq)
    typing
  exact ⟨target, _, finalInvariant, boundary.actual, operational, typing, agreement⟩

/-- The selected function signature supplies both return-input conditions
from actual checking. Lambda return inputs use their own fresh prefix. -/
theorem statement_function_returnValue
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {expression : Syntax.Expr} {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .returnStmt (some expression))
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      (Ty.productMany selected.signature.returnTypes) initial result frames target) :
    StatementConclusion selected inferenceContext (Ty.productMany selected.signature.returnTypes) result frames target := by
  let expectedReturn := Ty.productMany selected.signature.returnTypes
  have signatureParameters := selected.canonical checked
  have returnClosed : expectedReturn.VariablesBelow 0 := selected.returns_closed checked
  have declarationEq := (ProgramEnvironment.declaration?_sound selected.body.declared).2
  have baseFormed := (selected.header checked).return_types
  have resultTypes : TypesWellFormed target selected.signature.returnTypes :=
    StructuralSubstitution.TypesWellFormed.transportContext (RecursiveExpressionInvariant.ofStatement boundary.invariant).signatures_eq_whole
      boundary.invariant.typeParametersEq (by
        change target.currentDeclaration = some selected.signature.id
        simpa only [checkingContext, context, ProgramTypeScope.ofDeclaration, declarationEq, checkedBodyContext, declarationContext, Context.withResidualTypeVariables, Context.withSolvedRequirements, Context.withAssumptions, Context.forDeclaration]
          using boundary.invariant.declarationEq) baseFormed
  have returnFormed : TypeWellFormed target expectedReturn := {
    binders := (RecursiveExpressionInvariant.ofStatement boundary.invariant).typeParameterBinders
      (by simpa only [checkingContext, context, ProgramTypeScope.ofDeclaration, declarationEq] using signatureParameters)
    typeWellScoped := StructuralSubstitution.TypesWellScoped.productMany
      (StructuralSubstitution.TypesWellFormed.toTypesWellScoped resultTypes) }
  have returnFixed : selected.body.finalized.substitution.apply expectedReturn = expectedReturn :=
    Ty.apply_eq_self_of_domain_disjoint_freeVariables _ _
      (fun metavariable _ occurs => False.elim (Nat.not_lt_zero _ (returnClosed metavariable occurs)))
  have returnAdmissible : TypeAdmissible target
      (selected.body.finalized.substitution.apply expectedReturn) :=
    returnFixed.symm ▸ TypeAdmissible.ofWellFormed returnFormed
  exact statement_returnValue checked recursive form boundary
    (fun binder _ => ProtectedVariables.safe_closed _ _ returnClosed) returnAdmissible

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
