import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledInitializerPredicateFormation

/-! Assemble the existing generalized-let certificate at the exact selected
initializer boundary. Child expression typing remains the recursive input;
formation of its retained predicates comes from the actual whole-body producer
proof. Barrier and prior-quantifier conditions are kept explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

/-- The exact generalized binder keeps the final type returned by its actual
initializer. The actual finalizer excludes quantifier capture and absorbs the
initializer's inference substitution. -/
theorem finalBody (continuation : InitializerContinuation selected source) :
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
theorem initializerTyping (continuation : InitializerContinuation selected source)
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
premise. The two generalization conditions are not inferred from checker success. -/
theorem certificate (continuation : InitializerContinuation selected source)
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
    (prior : PriorQuantifiersBlockedAt continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type) target)
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
    prior (continuation.initializerTyping typed)

def initializerBinding (continuation : InitializerContinuation selected source) : InitializedLetBinding :=
  ⟨continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution,
    .expression continuation.receipt.value.id⟩

/-- The same actual let occurrence opens its exact initializer scope at the
state used by the real child call. This step does not assume source monomorphism. -/
theorem enter (continuation : InitializerContinuation selected source)
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
theorem certificate_of_child (continuation : InitializerContinuation selected source)
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
    (prior : PriorQuantifiersBlockedAt continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type) target)
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
  exact continuation.certificate checked invariant barrier prior (child entry.1 entry.2.1 entry.2.2)

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerContinuation
