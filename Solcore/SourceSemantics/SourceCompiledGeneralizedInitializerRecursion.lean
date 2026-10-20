import Solcore.SourceSemantics.SourceCompiledGeneralizedInitializerInvariant
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionRooted
import Solcore.SourceSemantics.SourceInferenceSelectedLetCoverage

/-! The actual initialized statement consumes the smaller generalized
expression contract. Its retained child subtree, annotation, scope frame and
operational state all come from the same receipt and parent boundary. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.RetainedInitializer
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

private theorem annotation_admissible
    {inferenceContext : SourceInference.Context} {target : SourceSemantics.Context}
    {annotation : Option Syntax.TypeExpr} {expected : Option Ty} {outer : Substitution}
    (canonical : SignatureParametersWellFormed inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signatures : target.signatures = inferenceContext.signatures)
    (parameters : target.typeParameters = inferenceContext.typeParameters)
    (owner : target.currentDeclaration = some inferenceContext.scope.genericOwner)
    (accepted : LocalLetRequirementTiming.Annotation inferenceContext annotation expected) :
    ∀ type ∈ expected, TypeAdmissible target (outer.apply type) := by
  cases accepted with
  | none => simp
  | some accepted =>
      intro type present
      cases Option.mem_some_iff.mp present
      rw [Detail.resolveSourceType_success_apply_eq_self _ accepted]
      exact TypeAdmissible.ofWellFormed
        (resolveSourceType_success_typeWellFormed canonical signatures parameters owner accepted)

theorem statement_of_expressionSoundness
    (continuation : RetainedInitializer selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {expectedReturn : Ty} {target : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (scope : CheckingScope selected continuation.inferenceContext)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (invariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn
      selected.body.finalized continuation.entry target)
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (operational : GeneralizedActualStateInvariant continuation.entry (evidenceSource selected))
    (rawSubtree : RawSubtreePreserved
      (continuation.result.state.toTypedSource (bodyRoots selected)) (evidenceSource selected)
      (.statement continuation.result.id))
    (patterns : continuation.result.state.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (literals : continuation.result.state.integerLiterals ⊆ selected.body.returned.integerLiterals)
    (requirements : continuation.result.state.requirements ⊆ selected.body.returned.requirements)
    (covered : TemplateScopeCovered selected.body.finalized.typedSource target
      (.statement continuation.entry.allocateStatementId.1))
    (actualCovered : ActualContext.Covers selected.body.finalized frames
      (.statement continuation.entry.allocateStatementId.1))
    (barrier : GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
      selected.body.finalized.substitution target (localSchemeTemplateIds continuation.initializerBinding.binder))
    (childSound : ExpressionRootedSoundness selected continuation.childFuel) :
    ∃ finalContext,
      RecursiveStatementInvariant (checkingContext selected) expectedReturn
        selected.body.finalized continuation.result.state finalContext ∧
      ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
      GeneralizedActualStateInvariant continuation.result.state (evidenceSource selected) ∧
      StatementHasType selected.body.finalized.typedSource
        { returnType := selected.body.finalized.substitution.apply expectedReturn
          loopDepth := continuation.inferenceContext.loopDepth }
        target continuation.result.id finalContext
        { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
      StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution continuation.result
        { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } := by
  apply continuation.statement_of_child_recursive checked scope operational invariant actual actualCovered barrier
  intro childInvariant childActual childActualCovered
  have rawContains : ContainsStatement
      (continuation.result.state.toTypedSource (bodyRoots selected)) continuation.entry.allocateStatementId.1 {
        id := continuation.entry.allocateStatementId.1, span := source.span, type := .unit
        form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id) } :=
    ⟨continuation.receipt.recorded, rfl⟩
  have resultId : continuation.result.id = continuation.entry.allocateStatementId.1 :=
    congrArg Detail.StatementResult.id continuation.receipt.completed
  have edge : DirectChild (continuation.result.state.toTypedSource (bodyRoots selected))
      (.statement continuation.result.id) (.expression continuation.receipt.value.id) := by
    rw [resultId]
    exact directChild_statement_reference rawContains (by simp [StatementForm.references])
  have readyExtension : TypingSourceExtends
      (continuation.receipt.ready.toTypedSource (bodyRoots selected))
      (continuation.result.state.toTypedSource (bodyRoots selected)) := by
    refine ⟨congrArg (fun result : Detail.StatementResult => result.state.owner)
      continuation.receipt.completed, ⟨[.statement {
        id := continuation.entry.allocateStatementId.1, span := source.span, type := .unit
        form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id) }], ?_⟩⟩
    exact (congrArg (fun result : Detail.StatementResult => result.state.nodes)
      continuation.receipt.completed).symm
  have rawChild := (rawSubtree.child edge).monoBefore readyExtension
  have finalContains : ContainsStatement selected.body.finalized.typedSource
      continuation.entry.allocateStatementId.1
      (({ id := continuation.entry.allocateStatementId.1, span := source.span, type := .unit
          form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id) } :
        StatementNode).applySubstitution selected.body.finalized.substitution) := by
    rw [selected.body.resources.source_eq]
    exact FlexibleSubstitution.ContainsStatement.applySubstitution _ ⟨continuation.original_retained, rfl⟩
  have childCovered : TemplateScopeCovered selected.body.finalized.typedSource
      (localSchemeInitializerContext target continuation.initializerBinding.binder)
      (.expression continuation.receipt.value.id) :=
    templateScopeCovered_letInitializer selected.body.resources.graph_closed finalContains rfl covered
  apply childSound
  refine {
    accepted := continuation.receipt.child
    interfaces
    extension := continuation.substitution
    scope
    invariant := childInvariant
    actual := childActual
    operational := operational.allocateStatementId
    expectedBelow := continuation.receipt.annotationAccepted.variablesBelow _
    expectedAdmissible := ?_
    expectedSafe := ?_
    integerPatterns := ?_
    integerLiterals := ?_
    requirements := ?_
    covered := childCovered
    actualCovered := childActualCovered
    rawSubtree := rawChild }
  · exact annotation_admissible (scope.canonical checked)
      (childInvariant.signatures_eq_whole.trans scope.signatures.symm)
      (childInvariant.typeParametersEq.trans scope.parameters.symm)
      (childInvariant.declarationEq.trans (congrArg some scope.owner.symm))
      continuation.receipt.annotationAccepted
  · intro binder member type present
    exact safe_closed _ _ (continuation.receipt.annotationAccepted.variablesBelow 0 type present)
  · simpa only [continuation.receipt.completed, LocalLetRequirementTiming.finish,
      State.recordNode, State.allocateBinder, State.withLocals] using patterns
  · simpa only [continuation.receipt.completed, LocalLetRequirementTiming.finish,
      State.recordNode, State.allocateBinder, State.withLocals] using literals
  · simpa only [continuation.receipt.completed, LocalLetRequirementTiming.finish,
      State.recordNode, State.allocateBinder, State.withLocals] using requirements

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.RetainedInitializer
