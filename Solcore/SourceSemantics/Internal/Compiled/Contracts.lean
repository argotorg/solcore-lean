import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Compiled.PrivateDescent
import Solcore.SourceSemantics.SourceInferenceRetainedInitializerState
import Solcore.SourceSemantics.SourceInferenceActualRootedContracts
import Solcore.SourceSemantics.SourceInferenceActualCallGraph
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionState
import Solcore.SourceSemantics.SourceInferenceExpressionDispatchSoundness
import Solcore.SourceSemantics.SourceInferenceSelectedForItemTransport
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionListState
import Solcore.SourceSemantics.SourceInferenceActiveHeaderPrivacy
import Solcore.SourceSemantics.SourceInferenceGeneralizedPatternState
import Solcore.SourceSemantics.SourceInferenceHeaderReturnPrivacy

/-!
# Contracts of generalized checking

The recursive expression and statement contracts for one selected body and its finalizer.
Generalized let typing and initializers are stated here, because the contracts use them. The
operational state of lists, headers and scrutinees sits at the same height.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedLetTyping
/-! Consume the actual selected initializer certificate in the ordinary source
statement judgment and carry its lexical extension to following statements. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedInitializer
/-! Generalized initializer typing for actual nested inference contexts. The
carrier keeps one selected body/finalizer and the exact recorded declaration,
without imposing whole-state node-prefix preservation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness

structure RetainedInitializer {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) (source : Syntax.Statement) where
  childFuel : Nat
  inferenceContext : SourceInference.Context
  entry : State
  result : Detail.StatementResult
  receipt : LocalLetRequirementTiming.Receipt childFuel inferenceContext source entry result
  privacy : InitializedStatementReceiptPrivate selected receipt

namespace RetainedInitializer
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

theorem original_retained (continuation : RetainedInitializer selected source) :
    .statement {
      id := continuation.entry.allocateStatementId.1, span := source.span, type := .unit,
      form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id) } ∈ selected.body.returned.nodes :=
  continuation.privacy.recorded

theorem no_capture (continuation : RetainedInitializer selected source) :
    Detail.LocalBinderInstantiationNoCapture selected.body.finalized.substitution continuation.receipt.binding.1 :=
  selected.body.resources.local_no_capture _ continuation.privacy.retained

theorem substitution (continuation : RetainedInitializer selected source) :
    selected.body.finalized.substitution.SemanticallyExtends continuation.receipt.ready.inference.substitution :=
  continuation.privacy.extension

theorem finalPredicates (continuation : RetainedInitializer selected source)
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
theorem finalBody (continuation : RetainedInitializer selected source) :
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
theorem initializerTyping (continuation : RetainedInitializer selected source)
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
theorem certificate (continuation : RetainedInitializer selected source)
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
      continuation.privacy.priorAvoided) (continuation.initializerTyping typed)

def initializerBinding (continuation : RetainedInitializer selected source) : InitializedLetBinding :=
  ⟨continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution,
    .expression continuation.receipt.value.id⟩

/-- The same actual let occurrence opens its exact initializer scope at the
state used by the real child call. This step does not assume source monomorphism. -/
theorem enter (continuation : RetainedInitializer selected source)
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
theorem certificate_of_child (continuation : RetainedInitializer selected source)
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
    (continuation : RetainedInitializer selected source)
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
    (continuation : RetainedInitializer selected source)
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


end RetainedInitializer

/-- The actual reached block supplies one receipt with its exact private
initializer and retained statement. The child inference context is unchanged. -/
theorem PrivateBlockContinuation.retained_initializer
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ continuation : RetainedInitializer selected source,
      continuation.inferenceContext = block.inferenceContext := by
  obtain ⟨childFuel,entry,result,receipt,privacy⟩ := block.initialized_statement checked position form
  exact ⟨⟨childFuel,block.inferenceContext,entry,result,receipt,privacy⟩,rfl⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedInitializerState
/-! The selected initializer's semantic and operational continuations share
the same receipt and finalizer. Only its own retained binder is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.RetainedInitializer
open Frontend SourceInference TypeSystem SourceInferenceSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

theorem operational (continuation : RetainedInitializer selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (signatures : continuation.inferenceContext.signatures = compiled.program.signatures)
    (ready : continuation.entry.InferenceReady)
    (entering : GeneralizedActualStateInvariant continuation.entry
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))) :
    GeneralizedActualStateInvariant continuation.result.state
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) := by
  have formation : ProgramSignatureFormationValidated continuation.inferenceContext.signatures :=
    signatures.symm ▸ Frontend.checkProgram_success_signature_formation checked
  have catalog : SignatureCatalogWellFormed continuation.inferenceContext.signatures :=
    signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked
  have canonical : ∀ signature ∈ continuation.inferenceContext.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes) := by
    intro signature member
    rw [signatures] at member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  apply entering.ofRetainedInitializer continuation.receipt selected.body.resources ready catalog formation canonical
    continuation.privacy.retained
  rw [continuation.receipt.inference_eq]
  exact continuation.privacy.extension

theorem statement_of_child_with_state
    {raw : Workspace.RawWorkspace} {control : ControlContext}
    (continuation : RetainedInitializer selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (signatures : continuation.inferenceContext.signatures = compiled.program.signatures)
    (entering : GeneralizedActualStateInvariant continuation.entry
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)))
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
      GeneralizedActualStateInvariant continuation.result.state
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) ∧
      StatementHasType selected.body.finalized.typedSource control target continuation.result.id finalContext {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
      StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution continuation.result {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } := by
  obtain ⟨finalContext,active,actualFinal,typed,matching⟩ :=
    continuation.statement_of_child checked invariant actual covered barrier child
  exact ⟨finalContext,active,actualFinal,
    continuation.operational checked signatures invariant.ready entering,typed,matching⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.RetainedInitializer
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionContracts
/-! Recursive expression contracts use one selected body and its actual
finalizer. Their boundaries retain the concrete inference call and source
records; generalized locals use the operational invariant without a
monomorphism restriction. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

abbrev checkingContext (selected : BodySelection compiled row fuel) : SourceInference.Context :=
  context compiled.program.environment compiled.program.signatures
    selected.signature selected.body.declaration

abbrev bodyRoots (selected : BodySelection compiled row fuel) : List NodeId :=
  selected.body.body.statements.map NodeId.statement

abbrev evidenceSource (selected : BodySelection compiled row fuel) : TypedSource :=
  selected.body.returned.toTypedSource (bodyRoots selected)

/-- Lexical descent may change loop depth while preserving the actual
declaration's static type environment. -/
structure CheckingScope (selected : BodySelection compiled row fuel)
    (inferenceContext : SourceInference.Context) : Prop where
  signatures : inferenceContext.signatures = (checkingContext selected).signatures
  owner : inferenceContext.scope.genericOwner = (checkingContext selected).scope.genericOwner
  parameters : inferenceContext.typeParameters = (checkingContext selected).typeParameters
  assumptions : inferenceContext.assumptions = (checkingContext selected).assumptions

theorem CheckingScope.refl (selected : BodySelection compiled row fuel) :
    CheckingScope selected (checkingContext selected) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem CheckingScope.withLoopDepth {selected : BodySelection compiled row fuel}
    {inferenceContext : SourceInference.Context} (scope : CheckingScope selected inferenceContext)
    (depth : Nat) :
    CheckingScope selected { inferenceContext with loopDepth := depth } :=
  ⟨scope.signatures, scope.owner, scope.parameters, scope.assumptions⟩

theorem CheckingScope.formation {raw : Workspace.RawWorkspace}
    {selected : BodySelection compiled row fuel} {inferenceContext : SourceInference.Context}
    (scope : CheckingScope selected inferenceContext)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ProgramSignatureFormationValidated inferenceContext.signatures :=
  scope.signatures.symm ▸ Frontend.checkProgram_success_signature_formation checked

theorem CheckingScope.catalog {raw : Workspace.RawWorkspace}
    {selected : BodySelection compiled row fuel} {inferenceContext : SourceInference.Context}
    (scope : CheckingScope selected inferenceContext)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    SignatureCatalogWellFormed inferenceContext.signatures :=
  scope.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked

theorem CheckingScope.functionsCanonical {raw : Workspace.RawWorkspace}
    {selected : BodySelection compiled row fuel} {inferenceContext : SourceInference.Context}
    (scope : CheckingScope selected inferenceContext)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes) := by
  intro candidate member
  rw [scope.signatures] at member
  exact (Frontend.checkProgram_success_function_signature_shape checked member).2

theorem CheckingScope.canonical {raw : Workspace.RawWorkspace}
    {selected : BodySelection compiled row fuel} {inferenceContext : SourceInference.Context}
    (scope : CheckingScope selected inferenceContext)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters := by
  have canonical := selected.canonical checked
  have declarationEq := (ProgramEnvironment.declaration?_sound selected.body.declared).2
  rw [scope.owner, scope.parameters]
  simpa only [checkingContext, context, ProgramTypeScope.ofDeclaration, declarationEq] using canonical

structure ExpressionCallBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (expression : Syntax.Expr) (expected : Option Ty)
    (initial : State) (inferred : InferredExpression) (resultState : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferExprFuel childFuel inferenceContext expression expected initial =
    .ok (inferred, resultState)
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends
    resultState.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveExpressionInvariant (checkingContext selected)
    selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next
  expectedAdmissible : ∀ type ∈ expected,
    TypeAdmissible target (selected.body.finalized.substitution.apply type)
  expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
    ProtectedVariables.Safe binder.scheme.quantified initial type
  integerPatterns : resultState.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : resultState.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : resultState.requirements ⊆ selected.body.returned.requirements
  covered : TemplateScopeCovered selected.body.finalized.typedSource target (.expression inferred.id)
  actualCovered : ActualContext.Covers selected.body.finalized frames (.expression inferred.id)

structure RetainedExpressionBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (expression : Syntax.Expr) (expected : Option Ty)
    (initial : State) (inferred : InferredExpression) (resultState : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop
    extends ExpressionCallBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target where
  proper : ProperDescendantsPreserved selected.body.finalized.substitution
    (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
    (.expression inferred.id)
  rawProper : RawProperDescendantsPreserved
    (resultState.toTypedSource (bodyRoots selected)) (evidenceSource selected) (.expression inferred.id)
  expressionRequirements : ExpressionRequirementsRetainedAt
    (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource inferred.id
  coercionPrimaries : ExpressionCoercionPrimariesRetainedAt
    (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource inferred.id
  operatorSite : ExpressionOperatorSiteRetainedAt
    (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource inferred.id
  directChildren : ExpressionDirectChildrenRetainedAt
    (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource inferred.id

structure RootedExpressionBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (expression : Syntax.Expr) (expected : Option Ty)
    (initial : State) (inferred : InferredExpression) (resultState : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop
    extends ExpressionCallBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target where
  rawSubtree : RawSubtreePreserved (resultState.toTypedSource (bodyRoots selected))
    (evidenceSource selected) (.expression inferred.id)

def ExpressionRetainedSoundness (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    RetainedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target →
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred

def ExpressionRootedSoundness (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    RootedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target →
    ExpressionHasType selected.body.finalized.typedSource target inferred.id
      (selected.body.finalized.substitution.apply inferred.type)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionRooted
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}

theorem RootedExpressionBoundary.finalSubtree
    (boundary : RootedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target) :
    SubtreePreserved selected.body.finalized.substitution
      (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      (.expression inferred.id) := by
  rw [selected.body.resources.source_eq]
  exact boundary.rawSubtree.substituted _

theorem RootedExpressionBoundary.finalNodes
    (boundary : RootedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target) :
    ExpressionNodesPreservedAt [inferred.id]
      ((resultState.toTypedSource (bodyRoots selected)).applySubstitution selected.body.finalized.substitution)
      selected.body.finalized.typedSource := by
  intro id node member contains
  have same : id = inferred.id := by simpa using member
  subst id
  exact boundary.finalSubtree.subgraph.containsExpression contains (.inl rfl)

theorem RootedExpressionBoundary.retained
    (boundary : RootedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target) :
    RetainedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target := by
  refine { boundary.toExpressionCallBoundary with
    proper := boundary.finalSubtree.proper
    rawProper := boundary.rawSubtree.proper
    expressionRequirements := ?_
    coercionPrimaries := ExpressionCoercionPrimariesRetainedAt.ofExpressionNodesPreservedAt _ boundary.finalNodes
    operatorSite := ExpressionOperatorSiteRetainedAt.ofExpressionNodesPreservedAt _ boundary.finalNodes
    directChildren := ExpressionDirectChildrenRetainedAt.ofExpressionNodesPreservedAt boundary.finalNodes }
  intro node requirement contains member
  have found := boundary.finalNodes (by simp)
    (FlexibleSubstitution.ContainsExpression.applySubstitution _ contains)
  apply found.primaryRequirementOccursAt
  simpa [ExpressionNode.applySubstitution] using member

/-- Root preservation upgrades retained expression typing using the same
selected finalizer's formation proof for that actual recorded node. -/
theorem RootedExpressionBoundary.typing_of_base {raw : Workspace.RawWorkspace}
    (boundary : RootedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (base : ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred) :
    ExpressionHasType selected.body.finalized.typedSource target inferred.id
      (selected.body.finalized.substitution.apply inferred.type) := by
  cases base with
  | @intro node rawType plan contains typeEq formType rawAdmissible requirements =>
      have member : Node.expression node ∈ (evidenceSource selected).nodes :=
        boundary.rawSubtree.nodes (.expression node) contains.1
          (.inl (congrArg NodeId.expression contains.2))
      have canonical := boundary.scope.canonical checked
      have finalAdmissible : TypeAdmissible target
          (selected.body.finalized.substitution.apply inferred.type) := by
        have formed := selected.body.resources.expressionTypeAdmissible_in_active member
          (boundary.invariant.typeParameterBinders (by
            simpa [boundary.scope.owner, boundary.scope.parameters] using canonical))
          boundary.invariant.signatures_eq_whole boundary.invariant.typeParametersEq
          boundary.invariant.declarationEq boundary.invariant.residual
        simpa only [typeEq] using formed
      exact (ExpressionTypingBase.intro contains typeEq formType rawAdmissible requirements
        ).expressionHasType boundary.finalNodes finalAdmissible


/-- The original unrestricted recursive API uses the shared final-node step. -/
theorem expressionRooted_of_retained {raw : Workspace.RawWorkspace}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (sound : ExpressionRetainedSoundness selected childFuel) :
    ExpressionRootedSoundness selected childFuel := by
  intro inferenceContext expression expected initial resultState inferred frames target boundary
  exact boundary.typing_of_base checked (sound boundary.retained)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledProvenanceExpressionContracts
/-! The original semantic boundaries are reused with a separate predicate on
the exact inference call. Actual execution provenance can restrict recursion;
the existing unrestricted APIs use the constantly true predicate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

def ExpressionRetainedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.expression childFuel inferenceContext expression expected initial inferred resultState) →
    RetainedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target →
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred

def ExpressionRootedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.expression childFuel inferenceContext expression expected initial inferred resultState) →
    RootedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target →
    ExpressionHasType selected.body.finalized.typedSource target inferred.id
      (selected.body.finalized.substitution.apply inferred.type)

/-- An unrestricted proof can be used at any retained call predicate. -/
theorem expressionRetainedSoundnessFor_restrict
    {provenance : CallIndex → Prop}
    {selected : BodySelection compiled row fuel} {childFuel : Nat}
    (sound : ExpressionRetainedSoundness selected childFuel) :
    ExpressionRetainedSoundnessFor provenance selected childFuel :=
  fun _ boundary => sound boundary

theorem expressionRetainedSoundnessFor_true
    {selected : BodySelection compiled row fuel} {childFuel : Nat}
    (sound : ExpressionRetainedSoundness selected childFuel) :
    ExpressionRetainedSoundnessFor (fun _ => True) selected childFuel :=
  fun _ boundary => sound boundary

theorem expressionRetainedSoundness_of_true
    {selected : BodySelection compiled row fuel} {childFuel : Nat}
    (sound : ExpressionRetainedSoundnessFor (fun _ => True) selected childFuel) :
    ExpressionRetainedSoundness selected childFuel :=
  fun boundary => sound trivial boundary

/-- Both provenance modes share the same final-node formation proof. -/
theorem expressionRooted_of_retained_for {raw : Workspace.RawWorkspace}
    {provenance : CallIndex → Prop}
    {selected : BodySelection compiled row fuel} {childFuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (sound : ExpressionRetainedSoundnessFor provenance selected childFuel) :
    ExpressionRootedSoundnessFor provenance selected childFuel := by
  intro inferenceContext expression expected initial resultState inferred frames target here boundary
  exact boundary.typing_of_base checked (sound here boundary.retained)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionList
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

/-- Ordered expression inference threads generalized operational state between
actual calls and checks each returned child in the same selected source. -/
theorem expressionsRooted_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance) :
    ∀ childFuel : Nat,
    (∀ smaller, smaller < childFuel → ExpressionRetainedSoundnessFor provenance selected smaller) →
    ∀ {inferenceContext : SourceInference.Context} {expressions : List Syntax.Expr}
      {initial resultState : State} {inferred : List InferredExpression}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.expressions childFuel inferenceContext expressions initial inferred resultState) →
    Detail.inferExprsFuel childFuel inferenceContext expressions initial = .ok (inferred, resultState) →
    ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource →
    selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution →
    CheckingScope selected inferenceContext →
    RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target →
    ActualContext (checkingContext selected) selected.body.finalized frames target →
    GeneralizedActualStateInvariant initial (evidenceSource selected) →
    (∀ argument ∈ inferred, RawSubtreePreserved (resultState.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.expression argument.id)) →
    resultState.integerPatterns ⊆ selected.body.returned.integerPatterns →
    resultState.integerLiterals ⊆ selected.body.returned.integerLiterals →
    resultState.requirements ⊆ selected.body.returned.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered selected.body.finalized.typedSource target
      (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers selected.body.finalized frames (.expression argument.id)) →
    ExpressionsHaveTypes selected.body.finalized.typedSource target (inferred.map (·.id))
      (inferred.map fun argument => selected.body.finalized.substitution.apply argument.type) := by
  intro childFuel
  induction childFuel with
  | zero =>
    intro recursive inferenceContext expressions initial resultState inferred frames target here success
    simp [Detail.inferExprsFuel] at success
  | succ childFuel induction =>
    intro recursive inferenceContext expressions initial resultState inferred frames target here success
      interfaces extension scope invariant actual operational rawPreserved
      integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
    have signatureFormation := scope.formation checked
    have functionsCanonical := scope.functionsCanonical checked
    have catalog := scope.catalog checked
    cases expressions with
    | nil =>
      simp only [Detail.inferExprsFuel, Except.ok.injEq, Prod.mk.injEq] at success
      cases success.1
      exact .nil target
    | cons expression rest =>
      have parentAccepted := success
      unfold Detail.inferExprsFuel at success
      cases headSuccess : Detail.inferExprFuel childFuel inferenceContext expression none initial with
      | error error => simp [headSuccess, bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨head, headState⟩
        simp only [headSuccess, bind, Except.bind] at success
        cases tailSuccess : Detail.inferExprsFuel childFuel inferenceContext rest headState with
        | error error => simp [tailSuccess] at success
        | ok pair =>
          rcases pair with ⟨tail, tailState⟩
          simp only [tailSuccess, pure, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          have headProperties := Detail.inferExprFuel_inferenceProperties invariant.ready
            signatureFormation functionsCanonical (by simp) headSuccess
          have tailProperties := Detail.inferExprsFuel_inferenceProperties headProperties.2.1
            signatureFormation functionsCanonical tailSuccess
          have headExtension := extension.trans tailProperties.1.substitution_extends
          have headInvariant := invariant.ofExpression signatureFormation functionsCanonical
            (by simp) headExtension headSuccess
          have headOperational := operational.ofExpression invariant.ready catalog signatureFormation
            functionsCanonical (by simp) (by simp) headSuccess
          have headToFinal := inferExprsFuel_success_typingSourceExtends_under_bound
            tailSuccess headInvariant.nodesBelow (bodyRoots selected)
          have headHere := descend here (ChildStep.expressions_head parentAccepted headSuccess)
          have tailHere := descend here (ChildStep.expressions_tail parentAccepted headSuccess tailSuccess)
          have headTyped := expressionRooted_of_retained_for checked
            (recursive childFuel (Nat.lt_succ_self childFuel)) headHere ({
              accepted := headSuccess
              interfaces := interfaces
              extension := headExtension
              scope := scope
              invariant := invariant
              actual := actual
              operational := operational
              expectedBelow := by simp
              expectedAdmissible := by simp
              expectedSafe := by simp
              integerPatterns := List.Subset.trans
                (Detail.inferExprsFuel_integerPatterns_subset tailSuccess) integerPatternsSubset
              integerLiterals := List.Subset.trans
                (Detail.inferExprsFuel_integerLiterals_subset tailSuccess) integerLiteralsSubset
              requirements := List.Subset.trans
                (Detail.inferExprsFuel_requirements_subset tailSuccess) requirementsSubset
              covered := covered head (by simp)
              actualCovered := actualCovered head (by simp)
              rawSubtree := (rawPreserved head (by simp)).monoBefore headToFinal } :
              RootedExpressionBoundary selected childFuel inferenceContext expression none
                initial head headState frames target)
          have tailTyped := induction
            (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self childFuel)))
            tailHere tailSuccess interfaces extension scope headInvariant actual headOperational
            (fun argument member => rawPreserved argument (List.mem_cons_of_mem _ member))
            integerPatternsSubset integerLiteralsSubset requirementsSubset
            (fun argument member => covered argument (List.mem_cons_of_mem _ member))
            (fun argument member => actualCovered argument (List.mem_cons_of_mem _ member))
          exact .cons headTyped tailTyped

/-- Compatibility with unrestricted recursive typing. -/
theorem expressionsRooted
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ∀ childFuel : Nat,
    (∀ smaller, smaller < childFuel → ExpressionRetainedSoundness selected smaller) →
    ∀ {inferenceContext : SourceInference.Context} {expressions : List Syntax.Expr}
      {initial resultState : State} {inferred : List InferredExpression}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    Detail.inferExprsFuel childFuel inferenceContext expressions initial = .ok (inferred, resultState) →
    ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource →
    selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution →
    CheckingScope selected inferenceContext →
    RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target →
    ActualContext (checkingContext selected) selected.body.finalized frames target →
    GeneralizedActualStateInvariant initial (evidenceSource selected) →
    (∀ argument ∈ inferred, RawSubtreePreserved (resultState.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.expression argument.id)) →
    resultState.integerPatterns ⊆ selected.body.returned.integerPatterns →
    resultState.integerLiterals ⊆ selected.body.returned.integerLiterals →
    resultState.requirements ⊆ selected.body.returned.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered selected.body.finalized.typedSource target
      (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers selected.body.finalized frames (.expression argument.id)) →
    ExpressionsHaveTypes selected.body.finalized.typedSource target (inferred.map (·.id))
      (inferred.map fun argument => selected.body.finalized.substitution.apply argument.type) := by
  intro childFuel recursive inferenceContext expressions initial resultState inferred frames target
    success interfaces extension scope invariant actual operational rawPreserved
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
  exact expressionsRooted_for (provenance := fun _ => True) checked true_childClosed childFuel
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary) trivial
    success interfaces extension scope invariant actual operational rawPreserved
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedStatementInvariant
/-! Statement typing in a retained final source closes the recursive state
invariant using the actual inference call. Only the lexical context fields
are read from the judgment, so the source need not be the intermediate table. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem RecursiveStatementInvariant.of_retained_statement_typing
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {finalized : Frontend.SourceInference.Result}
    {initialContext finalContext : SourceSemantics.Context}
    {semanticSource : TypedSource} {facts : StatementFacts}
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial initialContext)
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (resultActive : ActiveLocalContextInvariant result.state
      finalized.substitution finalContext)
    (resultBindersBelow : result.state.LocalBindersBelowNextLocal)
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (resultSchemeIsolation : ActiveSchemeQuantifierIsolation result.state)
    (typing : StatementHasType
      semanticSource
      { returnType := finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      initialContext result.id finalContext facts) :
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      result.state finalContext := by
  have properties := Detail.inferStatementFuel_inferenceProperties
    initialInvariant.ready signatureFormation functionsCanonical
    initialInvariant.returnBelow success
  have fields := statementHasType_nonlocal_fields_eq typing
  refine {
    active := resultActive
    ready := properties.2.1
    returnBelow := initialInvariant.returnBelow.weaken properties.1.next_le
    bindersBelow := resultBindersBelow
    nodesBelow := (Detail.inferStatementFuel_occurrenceBoundExtends success
      ).nodesBelowNextOccurrence initialInvariant.nodesBelow
    schemeIsolation := resultSchemeIsolation
    substitutionExtension := resultSubstitutionExtension
    signaturesEq := fields.1.trans initialInvariant.signaturesEq
    typeParametersEq := fields.2.1.trans initialInvariant.typeParametersEq
    declarationEq := fields.2.2.1.trans initialInvariant.declarationEq
    residual := fields.2.2.2.1.trans initialInvariant.residual
    solvedRequirementsEq := fields.2.2.2.2.1.trans
      initialInvariant.solvedRequirementsEq
    assumptionsMono := ?_
  }
  rw [fields.2.2.2.2.2]
  exact initialInvariant.assumptionsMono

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts
/-! Ordinary statements retain their actual call and the same selected final
source. Initialized statements supply their own concrete allocation barrier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open SourceInferenceStatementsSoundness

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure StatementBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (statement : Syntax.Statement) (expectedReturn : Ty)
    (initial : State) (result : Detail.StatementResult)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferStatementFuel childFuel inferenceContext statement expectedReturn initial =
    .ok result
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends
    result.state.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn
    selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  rawSubtree : RawSubtreePreserved (result.state.toTypedSource (bodyRoots selected))
    (evidenceSource selected) (.statement result.id)
  integerPatterns : result.state.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : result.state.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : result.state.requirements ⊆ selected.body.returned.requirements
  covered : TemplateScopeCovered selected.body.finalized.typedSource target (.statement result.id)
  actualCovered : ActualContext.Covers selected.body.finalized frames (.statement result.id)

def StatementConclusion (selected : BodySelection compiled row fuel)
    (inferenceContext : SourceInference.Context) (expectedReturn : Ty)
    (result : Detail.StatementResult)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop :=
  ∃ finalContext facts,
    RecursiveStatementInvariant (checkingContext selected) expectedReturn
      selected.body.finalized result.state finalContext ∧
    ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
    GeneralizedActualStateInvariant result.state (evidenceSource selected) ∧
    StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      target result.id finalContext facts ∧
    StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution result facts

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedForContracts
/-! Header items use their actual result and the same selected final source.
Their local bindings and expression references remain attached to that source. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure ForItemBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context) (item : Syntax.ForItem)
    (expectedReturn : Ty) (initial : State) (inferred : ForItemForm) (final : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferForItemFuel childFuel inferenceContext item initial = .ok (inferred, final)
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends final.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  rawReferences : ∀ reference ∈ inferred.references,
    RawSubtreePreserved (final.toTypedSource (bodyRoots selected)) (evidenceSource selected) reference
  integerPatterns : final.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : final.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : final.requirements ⊆ selected.body.returned.requirements
  owner : selected.body.finalized.typedSource.owner = initial.owner
  covered : ForItemReferencesCovered selected.body.finalized.typedSource
    selected.body.finalized.substitution target inferred
  bindingsRetained : ForItemBindingRetained (evidenceSource selected) inferred
  actualCovered : ∀ reference ∈ inferred.references,
    ActualContext.Covers selected.body.finalized frames reference
  actualBindings : ActualForItemBindings selected.body.finalized frames inferred

def ForItemConclusion (selected : BodySelection compiled row fuel)
    (inferenceContext : SourceInference.Context) (expectedReturn : Ty)
    (inferred : ForItemForm) (final : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop :=
  ∃ finalContext,
    RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized final finalContext ∧
    ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
    GeneralizedActualStateInvariant final (evidenceSource selected) ∧
    ForItemHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      target (inferred.applySubstitution selected.body.finalized.substitution) finalContext

structure ForItemsBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context) (items : List Syntax.ForItem)
    (expectedReturn : Ty) (initial : State) (result : Detail.InferredForItems)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferForItemsFuel childFuel inferenceContext items initial = .ok result
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  rawReferences : ∀ item ∈ result.items, ∀ reference ∈ item.references,
    RawSubtreePreserved (result.state.toTypedSource (bodyRoots selected)) (evidenceSource selected) reference
  integerPatterns : result.state.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : result.state.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : result.state.requirements ⊆ selected.body.returned.requirements
  owner : selected.body.finalized.typedSource.owner = initial.owner
  covered : ForItemsReferencesCovered selected.body.finalized.typedSource
    selected.body.finalized.substitution target result.items
  bindingsRetained : ForItemsBindingsRetained (evidenceSource selected) result.items
  actualCovered : ∀ item ∈ result.items, ∀ reference ∈ item.references,
    ActualContext.Covers selected.body.finalized frames reference
  actualBindings : ActualForItemsBindings selected.body.finalized frames result.items

def ForItemsConclusion (selected : BodySelection compiled row fuel)
    (inferenceContext : SourceInference.Context) (expectedReturn : Ty)
    (result : Detail.InferredForItems)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop :=
  ∃ finalContext,
    RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized result.state finalContext ∧
    ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
    GeneralizedActualStateInvariant result.state (evidenceSource selected) ∧
    ForItemsHaveType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      target (result.items.map (ForItemForm.applySubstitution selected.body.finalized.substitution)) finalContext

def ForItemRootedSoundness (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {item : Syntax.ForItem} {expectedReturn : Ty}
    {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    ForItemBoundary selected childFuel inferenceContext item expectedReturn initial inferred final frames target →
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target

def ForItemsRootedSoundness (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {items : List Syntax.ForItem} {expectedReturn : Ty}
    {initial : State} {result : Detail.InferredForItems}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    ForItemsBoundary selected childFuel inferenceContext items expectedReturn initial result frames target →
    ForItemsConclusion selected inferenceContext expectedReturn result frames target

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedExpressionListState
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.ofExpressions
    {fuel : Nat} {context : SourceInference.Context} {expressions : List Syntax.Expr}
    {initial final : State} {inferred : List InferredExpression} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferExprsFuel fuel context expressions initial = .ok (inferred, final)) :
    GeneralizedActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have properties := Detail.inferExprsFuel_inferenceProperties ready formation canonical accepted
  have binders : final.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders (Detail.inferExprsFuel_success_lexicalScope_eq accepted)
  refine ⟨⟨pending, (actualLedgerFamily fuel).expressions accepted ledger⟩,
    invariant.origins.inferExprsFuel accepted,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders properties.1.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member)
      (Detail.inferExprsFuel_requirements_subset accepted) properties.1.substitution_extends⟩
  intro binder member
  have old : binder ∈ initial.localBinders := binders ▸ member
  exact (inferExprsFuel_private binder.scheme.quantified fuel context expressions initial
    ready ledger.requirements (invariant.quantifiersBelow binder old) (invariant.privacy binder old)
    catalog formation canonical _ accepted).2.2.1

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedHeaderInitializerState
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.ofRetainedHeader
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {item : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (invariant : GeneralizedActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (retained : result.1.initializedLetBinders ⊆ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.2.inference.substitution)
    (accepted : Detail.inferForItemFuel fuel context item initial = .ok result) :
    GeneralizedActualStateInvariant result.2 (evidenceState.toTypedSource roots) := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending ++ result.1.localSchemeTemplateIds, (actualLedgerFamily fuel).statements.forItem accepted ledger⟩,
    activeBinderCaptureOrigins_inferForItemFuel invariant.origins retained accepted,
    activeQuantifiersBelowNext_inferForItemFuel invariant.quantifiersBelow ready formation canonical accepted,
    invariant.privacy.inferForItemFuel resources ready ledger.requirements invariant.quantifiersBelow
      catalog formation canonical invariant.backed invariant.origins retained extension accepted,
    invariant.backed.inferForItemFuel ready formation canonical accepted⟩

theorem LocalHeaderRequirementTiming.Receipt.schemeIsolation
    {fuel : Nat} {context : SourceInference.Context} {item : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context item initial result)
    (ready : receipt.ready.InferenceReady)
    (priorAvoided : Avoids (activeSchemeQuantifiers initial) (receipt.ready.resolve receipt.value.type))
    (isolated : ActiveSchemeQuantifierIsolation initial)
    (resultPrivate : ActiveQuantifiersPrivate result.2) : ActiveSchemeQuantifierIsolation result.2 := by
  have body : receipt.binding.1.scheme.body = receipt.ready.resolve receipt.value.type := by
    change receipt.generalized.scheme.body = _
    exact Detail.generalizeValue_scheme_body _ _ _ _
  intro binder member q quantified free
  have casesQuantified : q ∈ receipt.binding.1.scheme.quantified ∨ q ∈ activeSchemeQuantifiers initial := by
    simpa only [activeSchemeQuantifiers, receipt.result_binders, List.flatMap_cons, List.mem_append] using quantified
  rcases casesQuantified with fresh | prior
  · have selectedMember : receipt.binding.1 ∈ result.2.localBinders := by
      rw [receipt.result_binders]
      exact List.mem_cons_self
    have safe := (resultPrivate receipt.binding.1 selectedMember binder member).1 q free
    have occurs : q ∈ (receipt.ready.resolve receipt.value.type).freeVariables := (List.mem_filter.mp fresh).1
    have outside := ready.solved.apply_variables_outside_domain receipt.value.type q occurs
    have fixed : result.2.resolve (.variable q) = .variable q := by
      simp only [State.resolve, InferState.resolve, receipt.inference_eq, Substitution.apply,
        (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside, Option.getD_none]
    exact safe q (by simp only [fixed, Ty.freeVariables, List.mem_singleton]) fresh
  · rw [receipt.result_binders] at member
    rcases List.mem_cons.mp member with rfl | member
    · have occurs := (List.mem_filter.mp free).1
      rw [body] at occurs
      exact priorAvoided q occurs prior
    · exact isolated binder member q prior free

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedScrutineeState
/-! The real single or multiple match-scrutinee call provides the operational
arm-entry state and privacy for the returned scrutinee type. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

private theorem record_expression {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) (node : ExpressionNode) :
    GeneralizedActualStateInvariant (state.recordNode (.expression node)) source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ledger.recordExpression node⟩, invariant.origins.congr_localBinders rfl,
    invariant.quantifiersBelow, invariant.privacy.congr rfl rfl, invariant.backed.congr rfl rfl rfl⟩

theorem GeneralizedActualStateInvariant.ofMatchScrutinees
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial final : State}
    {inferred : InferredExpression} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : inferMatchScrutineesFuel fuel context span sources initial = .ok (inferred, final)) :
    GeneralizedActualStateInvariant final source ∧
      Safe (activeSchemeQuantifiers final) final inferred.type := by
  have finish (elements : List InferredExpression) (after : State)
      (acceptedElements : Detail.inferExprsFuel fuel context sources initial = .ok (elements, after))
      (recorded : (pure ({
          id := after.allocateExpressionId.1
          type := Ty.productMany (elements.map (·.type))
        },
        after.allocateExpressionId.2.recordNode (.expression {
          id := after.allocateExpressionId.1, span,
          type := Ty.productMany (elements.map (·.type)), form := .tuple (elements.map (·.id))})) :
          Except Error (InferredExpression × State)) = .ok (inferred, final)) :
      GeneralizedActualStateInvariant final source ∧
        Safe (activeSchemeQuantifiers final) final inferred.type := by
    have pairEq := Except.ok.inj recorded
    cases pairEq
    have afterInvariant := invariant.ofExpressions ready catalog formation canonical acceptedElements
    have privacy := inferExprsFuel_private (activeSchemeQuantifiers initial) fuel context sources initial
      ready invariant.requirements (activeSchemeQuantifiers_below_next invariant.quantifiersBelow)
      invariant.privacy.all_live catalog formation canonical _ acceptedElements
    have binders : after.localBinders = initial.localBinders :=
      congrArg LexicalScope.binders (Detail.inferExprsFuel_success_lexicalScope_eq acceptedElements)
    refine ⟨record_expression afterInvariant.allocateExpressionId _, ?_⟩
    change Safe (activeSchemeQuantifiers after) after (Ty.productMany (elements.map (·.type)))
    apply safe_productMany
    intro type member
    obtain ⟨element, present, rfl⟩ := List.mem_map.mp member
    simpa only [activeSchemeQuantifiers, binders] using privacy.2.1 element present
  cases sources with
  | nil =>
    unfold inferMatchScrutineesFuel at accepted
    cases elementsAccepted : Detail.inferExprsFuel fuel context [] initial with
    | error error => simp [elementsAccepted, bind, Except.bind] at accepted
    | ok result =>
      obtain ⟨elements, after⟩ := result
      simp only [elementsAccepted, bind, Except.bind] at accepted
      exact finish elements after elementsAccepted accepted
  | cons first rest =>
    cases rest with
    | nil =>
      have expressionAccepted : Detail.inferExprFuel fuel context first none initial = .ok (inferred, final) :=
        accepted
      exact ⟨invariant.ofExpression ready catalog formation canonical (by simp) (by simp) expressionAccepted,
        invariant.expression_result_private ready catalog formation canonical expressionAccepted⟩
    | cons second tail =>
      unfold inferMatchScrutineesFuel at accepted
      cases elementsAccepted : Detail.inferExprsFuel fuel context (first :: second :: tail) initial with
      | error error => simp [elementsAccepted, bind, Except.bind] at accepted
      | ok result =>
        obtain ⟨elements, after⟩ := result
        simp only [elementsAccepted, bind, Except.bind] at accepted
        exact finish elements after elementsAccepted accepted

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceHeaderSequenceReturnPrivacy
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

/-- Return-type privacy follows the actual ordered header calls and their retained binders. -/
theorem GeneralizedActualStateInvariant.forItems_return_safe
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : Detail.InferredForItems} {expectedReturn : Ty}
    (invariant : GeneralizedActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (retained : result.items.flatMap ForItemForm.initializedLetBinders ⊆
      (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (returnSafe : ∀ binder ∈ initial.localBinders, Safe binder.scheme.quantified initial expectedReturn)
    (accepted : Detail.inferForItemsFuel fuel context sources initial = .ok result) :
    ∀ binder ∈ result.state.localBinders, Safe binder.scheme.quantified result.state expectedReturn := by
  induction sources generalizing initial result with
  | nil =>
    simp only [Detail.inferForItemsFuel, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    subst result
    exact returnSafe
  | cons head tail induction =>
    cases headRun : Detail.inferForItemFuel fuel context head initial with
    | error error => simp [Detail.inferForItemsFuel, headRun, bind, Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨item, state⟩
      cases tailRun : Detail.inferForItemsFuel fuel context tail state with
      | error error => simp [Detail.inferForItemsFuel, headRun, tailRun, bind, Except.bind] at accepted
      | ok rest =>
        simp only [Detail.inferForItemsFuel, headRun, tailRun, bind, Except.bind,
          pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        subst result
        have headProperties := Detail.inferForItemFuel_inferenceProperties ready formation canonical headRun
        have tailProperties := Detail.inferForItemsFuel_inferenceProperties headProperties.2 formation canonical tailRun
        have headRetained : item.initializedLetBinders ⊆ (evidenceState.toTypedSource roots).initializedLetBinders := by
          intro binder member
          apply retained
          exact List.mem_append_left _ member
        have tailRetained : rest.items.flatMap ForItemForm.initializedLetBinders ⊆
            (evidenceState.toTypedSource roots).initializedLetBinders := by
          intro binder member
          apply retained
          exact List.mem_append_right _ member
        have middle := invariant.ofRetainedHeader resources ready catalog formation canonical headRetained
          (extension.trans tailProperties.1.substitution_extends) headRun
        have safe := inferForItemFuel_return_safe resources ready invariant.requirements invariant.quantifiersBelow
          invariant.privacy catalog formation canonical invariant.backed invariant.origins headRetained
          (extension.trans tailProperties.1.substitution_extends)
          returnBelow returnSafe headRun
        exact induction (result := rest) middle headProperties.2 tailRetained extension
          (returnBelow.weaken headProperties.1.next_le) safe tailRun

end Solcore.SourceSemantics.SourceInferenceSoundness
end
