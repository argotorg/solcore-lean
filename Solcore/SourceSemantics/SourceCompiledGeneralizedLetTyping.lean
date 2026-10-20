import Solcore.SourceSemantics.SourceCompiledInitializedPriorCertificate

/-! Consume the actual selected initializer certificate in the ordinary source
statement judgment and carry its lexical extension to following statements. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : Selected compiled row fuel} {source : Syntax.Statement}

/-- The concrete certificate installs the very binder allocated by the actual
receipt. Its statement is typed in the same final source as its initializer. -/
theorem InitializerContinuation.statement_of_certificate
    (continuation : InitializerContinuation selected source)
    {target : SourceSemantics.Context} {frames : List InitializedLetBinding}
    {control : ControlContext}
    (invariant : RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry target)
    (actual : ActualContext
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized frames target)
    (certificate : UnannotatedInitializedLetCertificate
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
      target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id) :
    ∃ finalContext,
      ActiveLocalContextInvariant continuation.result.state selected.body.finalized.substitution finalContext ∧
      ActualContext
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized frames finalContext ∧
      StatementHasType selected.body.finalized.typedSource control target continuation.result.id finalContext {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
      StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution continuation.result {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } := by
  let finalContext := target.withLocal continuation.receipt.binding.1.id
    (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution).scheme
    (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution).schemeRequirements
  have readyInvariant : ActiveLocalContextInvariant continuation.receipt.ready
      selected.body.finalized.substitution target :=
    (invariant.active.allocateStatementId rfl).inferExprFuel continuation.receipt.child
  have readyBelow := Detail.inferExprFuel_preserves_localBindersBelowNextLocal
    (State.allocateStatementId_preserves_localBindersBelowNextLocal _ invariant.bindersBelow)
    continuation.receipt.child
  have quantifiedNodup :
      (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution).scheme.quantified.Nodup :=
    Detail.generalizeValue_scheme_quantified_nodup _ _ _ _
  have schemeFormed : SchemeWellFormed target
      (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution).scheme :=
    StructuralSubstitution.SchemeWellFormed.ofLocalSchemeInitializerAdmissible
      certificate.initializer_type.type_admissible quantifiedNodup
  have monoRequirements :
      (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution).scheme.quantified = [] →
      (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution).schemeRequirements = [] := by
    intro mono
    have empty := Detail.generalizeValue_requirements_empty_of_quantified_eq_nil
      continuation.receipt.ready continuation.receipt.locals continuation.entry.nextRequirement
      (continuation.receipt.ready.resolve continuation.receipt.value.type) mono
    change (continuation.receipt.generalized.requirements.map
      (fun requirement => requirement.applySubstitution
        (selected.body.finalized.substitution.without continuation.receipt.binding.1.scheme.quantified))) = []
    simp only [show continuation.receipt.generalized.requirements = [] from empty, List.map_nil]
  have bindingInvariant : ActiveLocalContextInvariant continuation.receipt.binding.2
      selected.body.finalized.substitution finalContext :=
    (readyInvariant.withLocals continuation.receipt.locals).allocateBinder_of_localBindersBelowNextLocal
      continuation.receipt.name.value continuation.receipt.generalized.scheme (some continuation.receipt.name.span)
      false continuation.receipt.generalized.requirements rfl
      (State.withLocals_preserves_localBindersBelowNextLocal _ _ readyBelow)
      schemeFormed certificate.requirements_well_formed
  have extended : BinderExtends continuation.receipt.ready.owner target
      (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution) finalContext :=
    (readyInvariant.aligned.withLocals continuation.receipt.locals).binderExtends_of_allocateBinder
      (State.withLocals_preserves_localBindersBelowNextLocal _ _ readyBelow)
      rfl schemeFormed certificate.quantified_fresh monoRequirements
  let node : StatementNode := {
    id := continuation.entry.allocateStatementId.1, span := source.span, type := .unit,
    form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id) }
  have retained : ContainsStatement
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
      node.id node := ⟨continuation.original_retained,rfl⟩
  have finalizedRetained : ContainsStatement selected.body.finalized.typedSource node.id
      (node.applySubstitution selected.body.finalized.substitution) := by
    rw [selected.body.resources.source_eq]
    exact FlexibleSubstitution.ContainsStatement.applySubstitution _ retained
  have owner := selected.body.resources.graph_closed.wellFormed.nodesOwned
    (.statement (node.applySubstitution selected.body.finalized.substitution)) finalizedRetained.1
  have sourceOwner :
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).owner =
      continuation.receipt.ready.owner := by
    rw [Detail.inferExprFuel_preserves_owner continuation.receipt.child]
    have finalOwner : selected.body.finalized.typedSource.owner = continuation.entry.owner := owner.symm
    rw [selected.body.resources.source_eq] at finalOwner
    exact finalOwner
  have semanticExtension : BinderExtends
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).owner target
      (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution) finalContext :=
    sourceOwner.symm ▸ extended
  have typing : StatementHasType
      ((selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).applySubstitution
        selected.body.finalized.substitution)
      control target node.id finalContext {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } := by
    by_cases mono :
        (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution).scheme.quantified = []
    · have empty := monoRequirements mono
      have initializerContext : localSchemeInitializerContext target
          (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution) = target := by
        rw [localSchemeInitializerContext_eq_withTypeVariables _ _ empty, mono]
        exact Context.withTypeVariables_nil _
      have generalized := certificate.generalizes
      rw [localSchemeTemplateIds_eq_nil _ empty] at generalized
      exact letInitializedMonomorphicStatementHasType_afterSubstitution retained
        (initializerContext ▸ certificate.initializer_type) mono
        ((SchemeGeneralizesExcept_nil target _).mp generalized) semanticExtension
    · exact letInitializedGeneralizedStatementHasType_afterSubstitution retained mono
        certificate.requirements_well_formed certificate.generalizes certificate.initializer_type semanticExtension
  have actualTyping : StatementHasType selected.body.finalized.typedSource control target
      continuation.result.id finalContext {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } := by
    rw [selected.body.resources.source_eq]
    have resultId := congrArg Detail.StatementResult.id continuation.receipt.completed
    exact resultId.symm ▸ typing
  refine ⟨finalContext,?_,actual.of_statement actualTyping,actualTyping,?_⟩
  · rw [continuation.receipt.completed]
    exact bindingInvariant.recordNode _
  · rw [continuation.receipt.completed]
    constructor <;> rfl

/-- The exact smaller initializer proof is consumed all the way through the
source statement and its following lexical context. Prior privacy and qualified
predicate formation come from actual inference and finalization. -/
theorem InitializedPriorPrivate.statement_of_child
    {raw : Workspace.RawWorkspace} {control : ControlContext}
    {continuation : InitializerContinuation selected source}
    (privateVars : InitializedPriorPrivate continuation)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (invariant : RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry target)
    (actual : ActualContext
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized frames target)
    (covered : ActualContext.Covers selected.body.finalized frames
      (.statement continuation.entry.allocateStatementId.1))
    (barrier : GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
      selected.body.finalized.substitution target
      (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)))
    (child :
      RecursiveExpressionInvariant
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized continuation.entry.allocateStatementId.2
        (localSchemeInitializerContext target continuation.initializerBinding.binder) →
      ActualContext
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized (frames ++ [continuation.initializerBinding])
        (localSchemeInitializerContext target continuation.initializerBinding.binder) →
      ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
        (.expression continuation.receipt.value.id) →
      ExpressionHasType selected.body.finalized.typedSource
        (localSchemeInitializerContext target continuation.initializerBinding.binder)
        continuation.receipt.value.id
        (selected.body.finalized.substitution.apply continuation.receipt.value.type)) :
    ∃ finalContext,
      ActiveLocalContextInvariant continuation.result.state selected.body.finalized.substitution finalContext ∧
      ActualContext
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized frames finalContext ∧
      StatementHasType selected.body.finalized.typedSource control target continuation.result.id finalContext {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
      StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution continuation.result {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } := by
  exact continuation.statement_of_certificate invariant actual
    (privateVars.certificate_of_child checked invariant actual covered barrier child)

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
