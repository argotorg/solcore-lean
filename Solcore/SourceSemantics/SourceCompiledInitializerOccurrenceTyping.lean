import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledInitializerOccurrence

/-! The initialized declaration consumer uses the minimal actual occurrence.
Its certificate, child frame and final-source statement judgment are identical
to the earlier retained producer, without its unused suffix privacy fields. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness

namespace BodyInitializerOccurrence
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

theorem original_retained (continuation : BodyInitializerOccurrence selected source) :
    .statement {
      id := continuation.entry.allocateStatementId.1, span := source.span, type := .unit,
      form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id) } ∈ selected.body.returned.nodes :=
  continuation.recorded

theorem no_capture (continuation : BodyInitializerOccurrence selected source) :
    Detail.LocalBinderInstantiationNoCapture selected.body.finalized.substitution continuation.receipt.binding.1 :=
  selected.body.resources.local_no_capture _ continuation.retained

theorem substitution (continuation : BodyInitializerOccurrence selected source) :
    selected.body.finalized.substitution.SemanticallyExtends continuation.receipt.ready.inference.substitution :=
  continuation.extension

theorem finalPredicates (continuation : BodyInitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.signature.id)
    (residual : target.residualTypeVariables = true) :
    ∀ requirement ∈ (continuation.receipt.binding.1.applySubstitution
        selected.body.finalized.substitution).schemeRequirements,
      PredicateAdmissible (localSchemeInitializerContext target
        (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)) requirement.predicate := by
  apply selected.originalBindingPredicates checked signatures parameters owner residual
    (initializer := .expression continuation.receipt.value.id)
  intro requirement member
  apply List.mem_flatMap.mpr
  refine ⟨({ binder := continuation.receipt.binding.1
             initializer := .expression continuation.receipt.value.id } : InitializedLetBinding),
    ?_, List.mem_map.mpr ⟨requirement, member, rfl⟩⟩
  apply List.mem_flatMap.mpr
  refine ⟨.statement { id := continuation.entry.allocateStatementId.1
                       span := source.span
                       type := .unit
                       form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id) },
    continuation.original_retained, ?_⟩
  exact List.mem_singleton_self _


/-- The exact generalized binder keeps the final type returned by its actual
initializer. The actual finalizer excludes quantifier capture and absorbs the
initializer's inference substitution. -/
theorem finalBody (continuation : BodyInitializerOccurrence selected source) :
    (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution).scheme.body =
      selected.body.finalized.substitution.apply continuation.receipt.value.type := by
  have restriction : selected.body.finalized.substitution.without
      continuation.receipt.binding.1.scheme.quantified = selected.body.finalized.substitution :=
    FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain _ _
      continuation.no_capture.quantified_fresh
  have body : continuation.receipt.binding.1.scheme.body =
      continuation.receipt.ready.resolve continuation.receipt.value.type := by
    change continuation.receipt.generalized.scheme.body = _
    exact Detail.generalizeValue_scheme_body _ _ _ _
  rw [FlexibleSubstitution.applyTypedBinder_scheme]
  change (selected.body.finalized.substitution.without
    continuation.receipt.binding.1.scheme.quantified).apply continuation.receipt.binding.1.scheme.body = _
  rw [restriction, body]
  exact continuation.substitution continuation.receipt.value.type

/-- The child typing result supplied by the recursive call is converted to
this allocated binder's scheme body without changing the initializer or context. -/
theorem initializerTyping (continuation : BodyInitializerOccurrence selected source)
    {target : SourceSemantics.Context}
    (typed : ExpressionHasType selected.body.finalized.typedSource
      (localSchemeInitializerContext target
        (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution))
      continuation.receipt.value.id
      (selected.body.finalized.substitution.apply continuation.receipt.value.type)) :
    ExpressionHasType
      ((selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).applySubstitution
        selected.body.finalized.substitution)
      (localSchemeInitializerContext target
        (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution))
      continuation.receipt.value.id
      (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution).scheme.body := by
  rw [← selected.body.resources.source_eq, continuation.finalBody]
  exact typed

/-- The generalized initializer consumer now uses the real selected receipt,
finalizer, and producer formation. There is no monomorphism or whole-body typing
premise. Prior quantifier blocking comes from the actual prefix; the selected-scope barrier remains explicit. -/
theorem certificate (continuation : BodyInitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry target)
    (barrier : GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
      selected.body.finalized.substitution target
      (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)))
    (typed : ExpressionHasType selected.body.finalized.typedSource
      (localSchemeInitializerContext target
        (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution))
      continuation.receipt.value.id
      (selected.body.finalized.substitution.apply continuation.receipt.value.type)) :
    UnannotatedInitializedLetCertificate
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
      target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id := by
  have declarationEq := (ProgramEnvironment.declaration?_sound selected.body.declared).2
  have owner : target.currentDeclaration = some selected.signature.id := by
    simpa only [context, ProgramTypeScope.ofDeclaration, declarationEq] using invariant.declarationEq
  have retained : continuation.receipt.binding.1 ∈
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).initializedLetBinders := by
    exact List.mem_flatMap.mpr ⟨_, continuation.original_retained, List.mem_singleton_self _⟩
  have templates : ∀ requirement ∈ continuation.receipt.binding.1.schemeRequirements,
      ContainsLocalSchemeTemplate
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
        {binder := continuation.receipt.binding.1,
          initializer := .expression continuation.receipt.value.id, requirement} := by
    intro requirement member
    exact containsLocalSchemeTemplate_of_retainedLet
      ⟨continuation.original_retained, rfl⟩ (TypingSourceExtends.refl _) member
  exact unannotatedInitializedLetCertificate_of_finalBarrier_retained selected.body.resources
    (source := selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
    (state := continuation.receipt.ready) (final := continuation.receipt.binding.2)
    (name := continuation.receipt.name) (generalized := continuation.receipt.generalized)
    rfl rfl rfl invariant.signaturesEq invariant.assumptionsMono invariant.solvedRequirementsEq
    retained templates barrier
    (continuation.finalPredicates checked invariant.signatures_eq_whole invariant.typeParametersEq owner invariant.residual)
    (priorQuantifiersBlockedAt_of_activeQuantifiersAvoided invariant.active.aligned
      continuation.priorAvoided) (continuation.initializerTyping typed)

def initializerBinding (continuation : BodyInitializerOccurrence selected source) : InitializedLetBinding :=
  ⟨continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution,
    .expression continuation.receipt.value.id⟩

/-- The same actual let occurrence opens its exact initializer scope at the
state used by the real child call. This step does not assume source monomorphism. -/
theorem enter (continuation : BodyInitializerOccurrence selected source)
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
      (.statement continuation.entry.allocateStatementId.1)) :
    RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry.allocateStatementId.2
      (localSchemeInitializerContext target continuation.initializerBinding.binder) ∧
    ActualContext
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized (frames ++ [continuation.initializerBinding])
      (localSchemeInitializerContext target continuation.initializerBinding.binder) ∧
    ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
      (.expression continuation.receipt.value.id) := by
  have allocated : RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry.allocateStatementId.2 target := {
    invariant with
    active := invariant.active.allocateStatementId rfl
    ready := invariant.ready.allocateStatementId
    bindersBelow := State.allocateStatementId_preserves_localBindersBelowNextLocal _ invariant.bindersBelow
    nodesBelow := State.allocateStatementId_preserves_nodesBelowNextOccurrence _ invariant.nodesBelow
    schemeIsolation := activeSchemeQuantifierIsolation_allocateStatementId invariant.schemeIsolation rfl }
  let statement : StatementNode := {
    id := continuation.entry.allocateStatementId.1
    span := source.span
    type := .unit
    form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id) }
  have recorded : ContainsStatement selected.body.finalized.typedSource statement.id
      (statement.applySubstitution selected.body.finalized.substitution) := by
    rw [selected.body.resources.source_eq]
    exact FlexibleSubstitution.ContainsStatement.applySubstitution _
      ⟨continuation.original_retained, rfl⟩
  have retained : continuation.initializerBinding ∈ initializedLetBindings selected.body.finalized.typedSource := by
    apply List.mem_flatMap.mpr
    refine ⟨.statement (statement.applySubstitution selected.body.finalized.substitution), recorded.1, ?_⟩
    simp [statement, StatementNode.applySubstitution, StatementForm.applySubstitution,
      statementInitializedLetBindings, initializerBinding]
  have edge : DirectChild selected.body.finalized.typedSource
      (.statement continuation.entry.allocateStatementId.1) continuation.initializerBinding.initializer := by
    apply directChild_statement_reference recorded
    simp [statement, StatementNode.applySubstitution, StatementForm.applySubstitution,
      StatementForm.references, initializerBinding]
  exact ⟨allocated.generalizedInitializer continuation.initializerBinding.binder,
    actual.enter covered continuation.initializerBinding retained edge⟩

/-- Apply the concrete child typing step after opening the actual receipt's
scope, then assemble the existing generalized-let certificate. The callback is
restricted to this one child, so it can be the smaller recursive typing case. -/
theorem certificate_of_child (continuation : BodyInitializerOccurrence selected source)
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
    UnannotatedInitializedLetCertificate
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
      target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id := by
  have entry := continuation.enter invariant actual covered
  exact continuation.certificate checked invariant barrier (child entry.1 entry.2.1 entry.2.2)


/-- The concrete certificate installs the very binder allocated by the actual
receipt. Its statement is typed in the same final source as its initializer. -/
theorem statement_of_certificate
    (continuation : BodyInitializerOccurrence selected source)
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


theorem statement_of_child
    {raw : Workspace.RawWorkspace} {control : ControlContext}
    (continuation : BodyInitializerOccurrence selected source)
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
    (continuation.certificate_of_child checked invariant actual covered barrier child)


end BodyInitializerOccurrence
namespace InitializerOccurrence
export BodyInitializerOccurrence (original_retained no_capture substitution finalPredicates finalBody initializerTyping certificate initializerBinding enter certificate_of_child statement_of_certificate statement_of_child)
end InitializerOccurrence

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
