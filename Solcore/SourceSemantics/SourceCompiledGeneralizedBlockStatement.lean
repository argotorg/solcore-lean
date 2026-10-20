import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledProvenanceStatementContracts
import Solcore.SourceSemantics.SourceInferenceGeneralizedStatementRecording
import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences
import Solcore.SourceSemantics.SourceInferencePrivacyScopeRetention

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution
open SourceInferenceStatementsSoundness

theorem statement_block
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {body : List Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .block body)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (recursive : ∀ {bodyResult : Detail.BlockResult},
      StatementsBoundary selected childFuel inferenceContext body expectedReturn
        initial.allocateStatementId.2 bodyResult frames target →
      StatementsConclusion selected inferenceContext expectedReturn bodyResult frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  have resources := selected.body.resources
  obtain ⟨bodyResult, bodySuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_block_facts form rfl boundary.accepted (bodyRoots selected)
  obtain ⟨other, otherSuccess, _, bodyExtension, bodyPatterns, bodyRequirements⟩ :=
    inferStatementFuel_success_block_child_provenance form rfl boundary.accepted
      boundary.invariant.nodesBelow (bodyRoots selected)
  rw [bodySuccess] at otherSuccess
  have same := (Except.ok.inj otherSuccess).symm
  subst other
  have allocatedInvariant := boundary.invariant.allocateStatementId rfl
  have bodySubstitution : selected.body.finalized.substitution.SemanticallyExtends
      bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using boundary.extension
  have containsFinal := (boundary.rawSubtree.finalized resources).containsStatement containsRaw
  have childEdge : ∀ child ∈ bodyResult.statements,
      DirectChild (result.state.toTypedSource (bodyRoots selected))
        (.statement result.id) (.statement child) := by
    intro child member
    exact directChild_statement_reference containsRaw (by simp [StatementForm.references, member])
  have finalEdge : ∀ child ∈ bodyResult.statements,
      DirectChild selected.body.finalized.typedSource (.statement result.id) (.statement child) :=
    fun child member => (boundary.rawSubtree.finalized resources).directChild (childEdge child member)
  have bodyLiterals : bodyResult.state.integerLiterals ⊆ selected.body.returned.integerLiterals := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using boundary.integerLiterals
  obtain ⟨bodyContext, bodyFacts, bodyInvariant, _, bodyOperational, bodyTyping, bodyAgreement⟩ :=
    recursive ({
      accepted := bodySuccess
      interfaces := boundary.interfaces
      extension := bodySubstitution
      scope := boundary.scope
      invariant := allocatedInvariant
      actual := boundary.actual
      operational := boundary.operational.allocateStatementId
      rawSubtrees := fun child member =>
        (boundary.rawSubtree.child (childEdge child member)).monoBefore bodyExtension
      integerPatterns := List.Subset.trans bodyPatterns boundary.integerPatterns
      integerLiterals := bodyLiterals
      requirements := List.Subset.trans bodyRequirements boundary.requirements
      covered := fun child member => TemplateScopeCovered.statementChild
        boundary.covered resources.graph_closed (finalEdge child member) (fun _ present => present)
      actualCovered := fun child member => boundary.actualCovered.statement_reference
        containsFinal (by simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
          StatementForm.references, member]) } :
      StatementsBoundary selected childFuel inferenceContext body expectedReturn
        initial.allocateStatementId.2 bodyResult frames target)
  let facts : StatementFacts := {
    type := bodyFacts.type
    hasValue := bodyFacts.sawReturn
    sawReturn := bodyFacts.sawReturn
    control := bodyFacts.control.eraseValue }
  have active : ActiveLocalContextInvariant result.state selected.body.finalized.substitution target := by
    rw [resultEq]
    exact allocatedInvariant.active.restoreLexicalScope_recordNode _
  have operational : GeneralizedActualStateInvariant result.state (evidenceSource selected) := by
    rw [resultEq]
    exact (bodyOperational.restoreSaved boundary.operational.allocateStatementId.origins
      (ProtectedVariables.inferStatementsFuel_binders_subset bodySuccess)).recordStatement _ rfl
  have typing : StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth } target result.id target facts := by
    apply StatementHasType.block containsFinal rfl bodyTyping
    change selected.body.finalized.substitution.apply result.type = bodyFacts.type
    rw [resultEq]
    exact bodyAgreement.type_eq.symm
  have agreement : StatementResultMatchesFactsAfterSubstitution
      selected.body.finalized.substitution result facts := by
    rw [resultEq]
    exact StatementResultMatchesFactsAfterSubstitution.block bodyAgreement _ _
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simp [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope]
  have finalInvariant := boundary.invariant.of_retained_statement_typing boundary.accepted
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow boundary.accepted)
    boundary.extension (activeSchemeQuantifierIsolation_transport boundary.invariant.schemeIsolation bindersEq)
    typing
  exact ⟨target, facts, finalInvariant, boundary.actual, operational, typing, agreement⟩


/-- Reuse the block typing proof with its actual, fixed child call. -/
theorem statement_block_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : StatementsRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {body : List Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result))
    (form : statement.value = .block body)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  apply statement_block checked form boundary
  intro bodyResult childBoundary
  apply recursive (descend here (.statement_block boundary.accepted form rfl childBoundary.accepted))
    (fun binder member => returnSafe binder member) returnAdmissible childBoundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
