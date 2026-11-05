import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Compiled.Contracts
import Solcore.SourceSemantics.SourceInferenceRetainedInitializerState
import Solcore.SourceSemantics.SourceInferenceSelectedLetCoverage
import Solcore.SourceSemantics.SourceInferenceGeneralizationReceiptCalls
import Solcore.SourceSemantics.Internal.Compiled.Origins
import Solcore.SourceSemantics.SourceInferenceSelectedAttachedChild
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionState
import Solcore.SourceSemantics.SourceInferenceExpressionDispatchSoundness

/-!
# Initializer occurrences

The semantic initializer carrier keeps its computation, its final source occurrence and its
operational state. The initialized statement consumes the smaller expression contract through this
boundary.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerOccurrence
/-! The semantic initializer carrier retains only the actual computation,
its final source occurrence and the facts used by typing. Prior quantifier
avoidance is derived from the actual entering operational invariant; no
whole-suffix privacy law is carried into recursive typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness

structure BodyInitializerOccurrence {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) (source : Syntax.Statement) where
  childFuel : Nat
  inferenceContext : SourceInference.Context
  entry : State
  result : Detail.StatementResult
  receipt : LocalLetRequirementTiming.Receipt childFuel inferenceContext source entry result
  ready : receipt.ready.InferenceReady
  extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution
  recorded : .statement {
    id := entry.allocateStatementId.1, span := source.span, type := .unit
    form := .letDecl receipt.binding.1 (some receipt.value.id) } ∈ selected.body.returned.nodes
  priorAvoided : ProtectedVariables.Avoids (activeSchemeQuantifiers entry)
    (receipt.ready.resolve receipt.value.type)

namespace BodyInitializerOccurrence
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    {inferenceContext : SourceInference.Context} {entry : State} {result : Detail.StatementResult}

/-- An actual accepted initializer and its exact retained statement suffice.
The ready state and prior-variable avoidance are produced by that inference. -/
def ofReceipt (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected inferenceContext)
    (receipt : LocalLetRequirementTiming.Receipt childFuel inferenceContext source entry result)
    (ready : entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant entry (evidenceSource selected))
    (recorded : .statement {
      id := entry.allocateStatementId.1, span := source.span, type := .unit
      form := .letDecl receipt.binding.1 (some receipt.value.id) } ∈ selected.body.returned.nodes)
    (extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    BodyInitializerOccurrence selected source where
  childFuel
  inferenceContext
  entry
  result
  receipt
  ready := (receipt.initializer_inference ready (scope.formation checked)
    (scope.functionsCanonical checked)).2.1
  extension := by rwa [receipt.inference_eq] at extension
  recorded
  priorAvoided := ProtectedVariables.LocalLetRequirementTiming.Receipt.value_avoids_active receipt
    ready operational.requirements operational.quantifiersBelow operational.privacy
    (scope.catalog checked) (scope.formation checked) (scope.functionsCanonical checked)

theorem retained (occurrence : BodyInitializerOccurrence selected source) :
    occurrence.receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders :=
  List.mem_flatMap.mpr ⟨_, occurrence.recorded, List.mem_singleton_self _⟩

end BodyInitializerOccurrence

def RetainedInitializer.toOccurrence {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    (continuation : RetainedInitializer selected source) : BodyInitializerOccurrence selected source where
  childFuel := continuation.childFuel
  inferenceContext := continuation.inferenceContext
  entry := continuation.entry
  result := continuation.result
  receipt := continuation.receipt
  ready := continuation.privacy.ready
  extension := continuation.privacy.extension
  recorded := continuation.privacy.recorded
  priorAvoided := continuation.privacy.priorAvoided

/-- Ordinary callers keep their exact original selection witness. -/
abbrev InitializerOccurrence {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) (source : Syntax.Statement) :=
  BodyInitializerOccurrence selected.toBodySelection source

namespace InitializerOccurrence
export BodyInitializerOccurrence (ofReceipt retained)
end InitializerOccurrence

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceProducer
/-! The recursive statement boundary constructs its initializer occurrence
directly from that actual call and retained subtree, including inside an
expression or lambda. No separately indexed block continuation is required. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness

theorem of_accepted {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {source : Syntax.Statement}
    {entry : State} {result : Detail.StatementResult} {expectedReturn : Ty}
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (scope : CheckingScope selected inferenceContext)
    (form : source.value = .letDecl name annotation (some initializer))
    (accepted : Detail.inferStatementFuel (childFuel + 1) inferenceContext source expectedReturn entry = .ok result)
    (ready : entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant entry (evidenceSource selected))
    (rawSubtree : RawSubtreePreserved (result.state.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.statement result.id))
    (extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    ∃ occurrence : BodyInitializerOccurrence selected source,
      occurrence.childFuel = childFuel ∧
      occurrence.inferenceContext = inferenceContext ∧
      occurrence.entry = entry ∧ occurrence.result = result := by
  obtain ⟨receipt⟩ := LocalLetRequirementTiming.of_initialized_accepted form accepted
  have idEq : result.id = entry.allocateStatementId.1 :=
    congrArg Detail.StatementResult.id receipt.completed
  have recorded : .statement {
      id := entry.allocateStatementId.1, span := source.span, type := .unit
      form := .letDecl receipt.binding.1 (some receipt.value.id) } ∈ selected.body.returned.nodes := by
    apply rawSubtree.nodes _ receipt.recorded
    exact .inl (congrArg NodeId.statement idEq.symm)
  exact ⟨ofReceipt checked scope receipt ready operational recorded extension, rfl, rfl, rfl, rfl⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
export BodyInitializerOccurrence (of_accepted)
end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceTyping
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceState
/-! The selected initializer's semantic and operational continuations share
the same receipt and finalizer. Only its own retained binder is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence
open Frontend SourceInference TypeSystem SourceInferenceSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

theorem operational (continuation : BodyInitializerOccurrence selected source)
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
    continuation.retained
  rw [continuation.receipt.inference_eq]
  exact continuation.extension

theorem statement_of_child_with_state
    {raw : Workspace.RawWorkspace} {control : ControlContext}
    (continuation : BodyInitializerOccurrence selected source)
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

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
export BodyInitializerOccurrence (operational statement_of_child_with_state)
end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceInvariant
/-! The actual generalized binder preserves raw lexical quantifier isolation.
Resolved privacy alone is insufficient: the proof also uses the exact freshly
generalized variables, which the solved initializer substitution leaves fixed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

theorem schemeIsolation (continuation : BodyInitializerOccurrence selected source)
    (isolated : ActiveSchemeQuantifierIsolation continuation.entry)
    (resultPrivate : ActiveQuantifiersPrivate continuation.result.state) :
    ActiveSchemeQuantifierIsolation continuation.result.state := by
  have body : continuation.receipt.binding.1.scheme.body =
      continuation.receipt.ready.resolve continuation.receipt.value.type := by
    change continuation.receipt.generalized.scheme.body = _
    exact Detail.generalizeValue_scheme_body _ _ _ _
  intro binder member q quantified free
  have casesQuantified :
      q ∈ continuation.receipt.binding.1.scheme.quantified ∨
      q ∈ activeSchemeQuantifiers continuation.entry := by
    simpa only [activeSchemeQuantifiers, continuation.receipt.result_binders,
      List.flatMap_cons, List.mem_append] using quantified
  rcases casesQuantified with fresh | prior
  · have selectedMember : continuation.receipt.binding.1 ∈ continuation.result.state.localBinders := by
      rw [continuation.receipt.result_binders]
      exact List.mem_cons_self
    have safe := (resultPrivate continuation.receipt.binding.1 selectedMember binder member).1 q free
    have occurs : q ∈ (continuation.receipt.ready.resolve continuation.receipt.value.type).freeVariables :=
      (List.mem_filter.mp fresh).1
    have outside := continuation.ready.solved.apply_variables_outside_domain
      continuation.receipt.value.type q occurs
    have fixed : continuation.result.state.resolve (.variable q) = .variable q := by
      simp only [State.resolve, InferState.resolve, continuation.receipt.inference_eq,
        Substitution.apply, (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside,
        Option.getD_none]
    exact safe q (by simp only [fixed, Ty.freeVariables, List.mem_singleton]) fresh
  · rw [continuation.receipt.result_binders] at member
    rcases List.mem_cons.mp member with rfl | member
    · have occurs := (List.mem_filter.mp free).1
      rw [body] at occurs
      exact continuation.priorAvoided q occurs prior
    · exact isolated binder member q prior free

theorem statement_of_child_recursive
    {raw : Workspace.RawWorkspace} {expectedReturn : Ty}
    (continuation : BodyInitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (scope : CheckingScope selected continuation.inferenceContext)
    (entering : GeneralizedActualStateInvariant continuation.entry
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)))
    (invariant : RecursiveStatementInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      expectedReturn selected.body.finalized continuation.entry target)
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
      RecursiveStatementInvariant (checkingContext selected) expectedReturn
        selected.body.finalized continuation.result.state finalContext ∧
      ActualContext
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized frames finalContext ∧
      GeneralizedActualStateInvariant continuation.result.state
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) ∧
      StatementHasType selected.body.finalized.typedSource
        { returnType := selected.body.finalized.substitution.apply expectedReturn,
          loopDepth := continuation.inferenceContext.loopDepth } target continuation.result.id finalContext {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
      StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution continuation.result {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } := by
  obtain ⟨finalContext, active, actualFinal, operational, typed, matching⟩ :=
    continuation.statement_of_child_with_state checked scope.signatures entering
      (.ofStatement invariant) actual covered barrier child
  have accepted := initializedReceipt_accepted continuation.receipt expectedReturn
  have extension : selected.body.finalized.substitution.SemanticallyExtends
      continuation.result.state.inference.substitution := by
    rw [continuation.receipt.inference_eq]
    exact continuation.substitution
  have finalInvariant := invariant.of_retained_statement_typing accepted
    (scope.formation checked) (scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow accepted)
    extension (continuation.schemeIsolation invariant.schemeIsolation operational.privacy) typed
  exact ⟨finalContext, finalInvariant, actualFinal, operational, typed, matching⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
export BodyInitializerOccurrence (schemeIsolation statement_of_child_recursive)
end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceRecursion
/-! The actual initialized statement consumes the smaller generalized
expression contract. Its retained child subtree, annotation, scope frame and
operational state all come from the same receipt and parent boundary. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables SourceInferenceExecution

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

theorem statement_of_expressionSoundness_for {provenance : CallIndex → Prop}
    (continuation : BodyInitializerOccurrence selected source)
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
    (childHere : provenance (.expression continuation.childFuel continuation.inferenceContext
      continuation.receipt.initializer continuation.receipt.expected continuation.entry.allocateStatementId.2
      continuation.receipt.value continuation.receipt.ready))
    (childSound : ExpressionRootedSoundnessFor provenance selected continuation.childFuel) :
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
  apply childSound childHere
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

theorem statement_of_expressionSoundness
    (continuation : BodyInitializerOccurrence selected source)
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
  exact continuation.statement_of_expressionSoundness_for (provenance := fun _ => True) checked scope interfaces invariant actual
    operational rawSubtree patterns literals requirements covered actualCovered barrier True.intro
    (fun _ boundary => childSound boundary)

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.BodyInitializerOccurrence

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
export BodyInitializerOccurrence (statement_of_expressionSoundness)
end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedInitializedConnection
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {source : Syntax.Statement} {expectedReturn : Ty}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}

theorem StatementBoundary.initializerOccurrence
    {inferenceContext : SourceInference.Context} {initial : State} {result : Detail.StatementResult}
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext source
      expectedReturn initial result frames target)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ occurrence : BodyInitializerOccurrence selected source,
      occurrence.childFuel = childFuel ∧ occurrence.inferenceContext = inferenceContext ∧
      occurrence.entry = initial ∧ occurrence.result = result :=
  BodyInitializerOccurrence.of_accepted checked boundary.scope form boundary.accepted boundary.invariant.ready
    boundary.operational boundary.rawSubtree boundary.extension

/-- The concrete occurrence and its selected-scope barrier feed the same
statement conclusion consumed by source-order sequencing. -/
theorem statement_initialized_for {provenance : CallIndex → Prop}
    (occurrence : BodyInitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (recursive : ExpressionRootedSoundnessFor provenance selected occurrence.childFuel)
    (here : provenance (.statement (occurrence.childFuel + 1) occurrence.inferenceContext source
      expectedReturn occurrence.entry occurrence.result))
    (boundary : StatementBoundary selected (occurrence.childFuel + 1)
      occurrence.inferenceContext source expectedReturn occurrence.entry occurrence.result frames target)
    (barrier : GeneralizationBarrierTransport occurrence.receipt.ready occurrence.receipt.locals
      occurrence.entry.nextRequirement (occurrence.receipt.ready.resolve occurrence.receipt.value.type)
      selected.body.finalized.substitution target (localSchemeTemplateIds occurrence.initializerBinding.binder)) :
    StatementConclusion selected occurrence.inferenceContext expectedReturn occurrence.result frames target := by
  have idEq : occurrence.result.id = occurrence.entry.allocateStatementId.1 :=
    congrArg Detail.StatementResult.id occurrence.receipt.completed
  obtain ⟨finalContext, invariant, actual, operational, typing, agreement⟩ :=
    occurrence.statement_of_expressionSoundness_for checked boundary.scope boundary.interfaces boundary.invariant
      boundary.actual boundary.operational boundary.rawSubtree boundary.integerPatterns boundary.integerLiterals
      boundary.requirements (idEq ▸ boundary.covered) (idEq ▸ boundary.actualCovered) barrier
      (descend here (statement_initializer_child occurrence.receipt boundary.accepted)) recursive
  exact ⟨finalContext, _, invariant, actual, operational, typing, agreement⟩

theorem statement_initialized
    (occurrence : BodyInitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRootedSoundness selected occurrence.childFuel)
    (boundary : StatementBoundary selected (occurrence.childFuel + 1)
      occurrence.inferenceContext source expectedReturn occurrence.entry occurrence.result frames target)
    (barrier : GeneralizationBarrierTransport occurrence.receipt.ready occurrence.receipt.locals
      occurrence.entry.nextRequirement (occurrence.receipt.ready.resolve occurrence.receipt.value.type)
      selected.body.finalized.substitution target (localSchemeTemplateIds occurrence.initializerBinding.binder)) :
    StatementConclusion selected occurrence.inferenceContext expectedReturn occurrence.result frames target := by
  exact statement_initialized_for (provenance := fun _ => True) occurrence checked true_childClosed
    (fun _ boundary => recursive boundary) True.intro boundary barrier

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedInitializerInvariant
/-! The actual generalized binder preserves raw lexical quantifier isolation.
Resolved privacy alone is insufficient: the proof also uses the exact freshly
generalized variables, which the solved initializer substitution leaves fixed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.RetainedInitializer
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

theorem schemeIsolation (continuation : RetainedInitializer selected source)
    (isolated : ActiveSchemeQuantifierIsolation continuation.entry)
    (resultPrivate : ActiveQuantifiersPrivate continuation.result.state) :
    ActiveSchemeQuantifierIsolation continuation.result.state := by
  have body : continuation.receipt.binding.1.scheme.body =
      continuation.receipt.ready.resolve continuation.receipt.value.type := by
    change continuation.receipt.generalized.scheme.body = _
    exact Detail.generalizeValue_scheme_body _ _ _ _
  intro binder member q quantified free
  have casesQuantified :
      q ∈ continuation.receipt.binding.1.scheme.quantified ∨
      q ∈ activeSchemeQuantifiers continuation.entry := by
    simpa only [activeSchemeQuantifiers, continuation.receipt.result_binders,
      List.flatMap_cons, List.mem_append] using quantified
  rcases casesQuantified with fresh | prior
  · have selectedMember : continuation.receipt.binding.1 ∈ continuation.result.state.localBinders := by
      rw [continuation.receipt.result_binders]
      exact List.mem_cons_self
    have safe := (resultPrivate continuation.receipt.binding.1 selectedMember binder member).1 q free
    have occurs : q ∈ (continuation.receipt.ready.resolve continuation.receipt.value.type).freeVariables :=
      (List.mem_filter.mp fresh).1
    have outside := continuation.privacy.ready.solved.apply_variables_outside_domain
      continuation.receipt.value.type q occurs
    have fixed : continuation.result.state.resolve (.variable q) = .variable q := by
      simp only [State.resolve, InferState.resolve, continuation.receipt.inference_eq,
        Substitution.apply, (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside,
        Option.getD_none]
    exact safe q (by simp only [fixed, Ty.freeVariables, List.mem_singleton]) fresh
  · rw [continuation.receipt.result_binders] at member
    rcases List.mem_cons.mp member with rfl | member
    · have occurs := (List.mem_filter.mp free).1
      rw [body] at occurs
      exact continuation.privacy.priorAvoided q occurs prior
    · exact isolated binder member q prior free

theorem statement_of_child_recursive
    {raw : Workspace.RawWorkspace} {expectedReturn : Ty}
    (continuation : RetainedInitializer selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (scope : CheckingScope selected continuation.inferenceContext)
    (entering : GeneralizedActualStateInvariant continuation.entry
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)))
    (invariant : RecursiveStatementInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      expectedReturn selected.body.finalized continuation.entry target)
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
      RecursiveStatementInvariant (checkingContext selected) expectedReturn
        selected.body.finalized continuation.result.state finalContext ∧
      ActualContext
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized frames finalContext ∧
      GeneralizedActualStateInvariant continuation.result.state
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) ∧
      StatementHasType selected.body.finalized.typedSource
        { returnType := selected.body.finalized.substitution.apply expectedReturn,
          loopDepth := continuation.inferenceContext.loopDepth } target continuation.result.id finalContext {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
      StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution continuation.result {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } := by
  obtain ⟨finalContext, active, actualFinal, operational, typed, matching⟩ :=
    continuation.statement_of_child_with_state checked scope.signatures entering
      (.ofStatement invariant) actual covered barrier child
  have accepted := initializedReceipt_accepted continuation.receipt expectedReturn
  have extension : selected.body.finalized.substitution.SemanticallyExtends
      continuation.result.state.inference.substitution := by
    rw [continuation.receipt.inference_eq]
    exact continuation.substitution
  have finalInvariant := invariant.of_retained_statement_typing accepted
    (scope.formation checked) (scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow accepted)
    extension (continuation.schemeIsolation invariant.schemeIsolation operational.privacy) typed
  exact ⟨finalContext, finalInvariant, actualFinal, operational, typed, matching⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.RetainedInitializer
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedInitializerRecursion
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedInitializedStatement
/-! A generalized initialized statement is indexed by the actual selected
receipt. Its barrier concerns that one allocation; it is not a law over
arbitrary checker calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure InitializedStatementBoundary (selected : BodySelection compiled row fuel)
    (source : Syntax.Statement) (expectedReturn : Ty)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) where
  continuation : RetainedInitializer selected source
  scope : CheckingScope selected continuation.inferenceContext
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  invariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn
    selected.body.finalized continuation.entry target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant continuation.entry (evidenceSource selected)
  rawSubtree : RawSubtreePreserved
    (continuation.result.state.toTypedSource (bodyRoots selected)) (evidenceSource selected)
    (.statement continuation.result.id)
  patterns : continuation.result.state.integerPatterns ⊆ selected.body.returned.integerPatterns
  literals : continuation.result.state.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : continuation.result.state.requirements ⊆ selected.body.returned.requirements
  covered : TemplateScopeCovered selected.body.finalized.typedSource target
    (.statement continuation.entry.allocateStatementId.1)
  actualCovered : ActualContext.Covers selected.body.finalized frames
    (.statement continuation.entry.allocateStatementId.1)
  barrier : GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
    continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
    selected.body.finalized.substitution target (localSchemeTemplateIds continuation.initializerBinding.binder)

def InitializedStatementConclusion {selected : BodySelection compiled row fuel}
    {source : Syntax.Statement} {expectedReturn : Ty}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : InitializedStatementBoundary selected source expectedReturn frames target) : Prop :=
  ∃ finalContext,
    RecursiveStatementInvariant (checkingContext selected) expectedReturn
      selected.body.finalized boundary.continuation.result.state finalContext ∧
    ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
    GeneralizedActualStateInvariant boundary.continuation.result.state (evidenceSource selected) ∧
    StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := boundary.continuation.inferenceContext.loopDepth }
      target boundary.continuation.result.id finalContext
      { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
    StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution boundary.continuation.result
      { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit }

theorem InitializedStatementBoundary.sound {raw : Workspace.RawWorkspace}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement} {expectedReturn : Ty}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : InitializedStatementBoundary selected source expectedReturn frames target)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (childSound : ExpressionRootedSoundness selected boundary.continuation.childFuel) :
    InitializedStatementConclusion boundary :=
  boundary.continuation.statement_of_expressionSoundness checked boundary.scope boundary.interfaces
    boundary.invariant boundary.actual boundary.operational boundary.rawSubtree
    boundary.patterns boundary.literals boundary.requirements boundary.covered boundary.actualCovered
    boundary.barrier childSound

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedRetainedExpressionList
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

/-- Arguments whose roots gain coercion metadata retain their original raw typing while actual inference threads generalized state through the argument list. -/
theorem expressionsRetainedBases_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ∀ childFuel : Nat,
    (∀ smaller, smaller < childFuel → ExpressionRetainedSoundnessFor provenance selected smaller) →
    ∀ {inferenceContext : SourceInference.Context} {expressions : List Syntax.Expr}
      {initial resultState : State} {inferred : List InferredExpression}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    OrderedExpressionCalls provenance inferenceContext childFuel expressions initial inferred resultState →
    Detail.inferExprsFuel childFuel inferenceContext expressions initial = .ok (inferred, resultState) →
    ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource →
    selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution →
    CheckingScope selected inferenceContext →
    RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target →
    ActualContext (checkingContext selected) selected.body.finalized frames target →
    GeneralizedActualStateInvariant initial (evidenceSource selected) →
    (∀ argument ∈ inferred, AttachedChildPreserved selected.body.finalized.substitution
      (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      selected.body.finalized.typedSource (evidenceSource selected) argument.id) →
    resultState.integerPatterns ⊆ selected.body.returned.integerPatterns →
    resultState.integerLiterals ⊆ selected.body.returned.integerLiterals →
    resultState.requirements ⊆ selected.body.returned.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered selected.body.finalized.typedSource target
      (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers selected.body.finalized frames (.expression argument.id)) →
    ArgumentTypingBasesValid (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  intro childFuel
  induction childFuel with
  | zero =>
    intro recursive inferenceContext expressions initial resultState inferred frames target calls success
    simp [Detail.inferExprsFuel] at success
  | succ childFuel induction =>
    intro recursive inferenceContext expressions initial resultState inferred frames target calls success
      interfaces extension scope invariant actual operational rawPreserved
      integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
    have signatureFormation := scope.formation checked
    have functionsCanonical := scope.functionsCanonical checked
    have catalog := scope.catalog checked
    cases expressions with
    | nil =>
      simp only [Detail.inferExprsFuel, Except.ok.injEq, Prod.mk.injEq] at success
      cases success.1
      exact .nil
    | cons expression rest =>
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
          obtain ⟨headHere, tailCalls⟩ := calls.split headSuccess
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
          have headPreserved := (rawPreserved head (by simp)).monoBefore headToFinal
          have headTyped := (recursive childFuel (Nat.lt_succ_self childFuel)) headHere ({
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
            proper := headPreserved.finalized
            rawProper := headPreserved.raw
            expressionRequirements := headPreserved.requirements
            coercionPrimaries := headPreserved.coercions
            operatorSite := headPreserved.operators
            directChildren := headPreserved.children } :
            RetainedExpressionBoundary selected childFuel inferenceContext expression none
              initial head headState frames target)
          have tailTyped := induction
            (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self childFuel)))
            tailCalls tailSuccess interfaces extension scope headInvariant actual headOperational
            (fun argument member => rawPreserved argument (List.mem_cons_of_mem _ member))
            integerPatternsSubset integerLiteralsSubset requirementsSubset
            (fun argument member => covered argument (List.mem_cons_of_mem _ member))
            (fun argument member => actualCovered argument (List.mem_cons_of_mem _ member))
          exact .cons (headTyped.weakenNodeSource headToFinal.nodes_prefix) tailTyped

/-- Existing unrestricted argument typing uses the same proof body. -/
theorem expressionsRetainedBases
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
    (∀ argument ∈ inferred, AttachedChildPreserved selected.body.finalized.substitution
      (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      selected.body.finalized.typedSource (evidenceSource selected) argument.id) →
    resultState.integerPatterns ⊆ selected.body.returned.integerPatterns →
    resultState.integerLiterals ⊆ selected.body.returned.integerLiterals →
    resultState.requirements ⊆ selected.body.returned.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered selected.body.finalized.typedSource target
      (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers selected.body.finalized frames (.expression argument.id)) →
    ArgumentTypingBasesValid (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  intro childFuel recursive inferenceContext expressions initial resultState inferred frames target
    success interfaces extension scope invariant actual operational rawPreserved
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
  exact expressionsRetainedBases_for (provenance := fun _ => True) checked childFuel
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary)
    (OrderedExpressionCalls.of_accepted success) success
    interfaces extension scope invariant actual operational rawPreserved
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedStatementsContracts
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open SourceInferenceStatementsSoundness

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure StatementsBoundary (selected : BodySelection compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (statements : List Syntax.Statement) (expectedReturn : Ty)
    (initial : State) (result : Detail.BlockResult)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferStatementsFuel childFuel inferenceContext statements expectedReturn initial =
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
  rawSubtrees : ∀ child ∈ result.statements,
    RawSubtreePreserved (result.state.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.statement child)
  integerPatterns : result.state.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : result.state.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : result.state.requirements ⊆ selected.body.returned.requirements
  covered : ∀ child ∈ result.statements,
    TemplateScopeCovered selected.body.finalized.typedSource target (.statement child)
  actualCovered : ∀ child ∈ result.statements,
    ActualContext.Covers selected.body.finalized frames (.statement child)

def StatementsConclusion (selected : BodySelection compiled row fuel)
    (inferenceContext : SourceInference.Context) (expectedReturn : Ty)
    (result : Detail.BlockResult)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop :=
  ∃ finalContext facts,
    RecursiveStatementInvariant (checkingContext selected) expectedReturn
      selected.body.finalized result.state finalContext ∧
    ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
    GeneralizedActualStateInvariant result.state (evidenceSource selected) ∧
    StatementsHaveType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      target result.statements finalContext facts ∧
    BlockResultMatchesFactsAfterSubstitution selected.body.finalized.substitution result facts

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceBoundary
/-! A generalized initialized statement is indexed by the actual selected
receipt. Its barrier concerns that allocation and remains an explicit
premise until the actual call reachability is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure InitializedOccurrenceBoundary (selected : BodySelection compiled row fuel)
    (source : Syntax.Statement) (expectedReturn : Ty)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) where
  occurrence : BodyInitializerOccurrence selected source
  scope : CheckingScope selected occurrence.inferenceContext
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces
    (checkingContext selected).signatures selected.body.finalized.solvedRequirements
    selected.body.finalized.typedSource
  invariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn
    selected.body.finalized occurrence.entry target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant occurrence.entry (evidenceSource selected)
  rawSubtree : RawSubtreePreserved
    (occurrence.result.state.toTypedSource (bodyRoots selected)) (evidenceSource selected)
    (.statement occurrence.result.id)
  patterns : occurrence.result.state.integerPatterns ⊆ selected.body.returned.integerPatterns
  literals : occurrence.result.state.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : occurrence.result.state.requirements ⊆ selected.body.returned.requirements
  covered : TemplateScopeCovered selected.body.finalized.typedSource target
    (.statement occurrence.entry.allocateStatementId.1)
  actualCovered : ActualContext.Covers selected.body.finalized frames
    (.statement occurrence.entry.allocateStatementId.1)
  barrier : GeneralizationBarrierTransport occurrence.receipt.ready occurrence.receipt.locals
    occurrence.entry.nextRequirement (occurrence.receipt.ready.resolve occurrence.receipt.value.type)
    selected.body.finalized.substitution target (localSchemeTemplateIds occurrence.initializerBinding.binder)

def InitializerOccurrenceConclusion {selected : BodySelection compiled row fuel}
    {source : Syntax.Statement} {expectedReturn : Ty}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : InitializedOccurrenceBoundary selected source expectedReturn frames target) : Prop :=
  ∃ finalContext,
    RecursiveStatementInvariant (checkingContext selected) expectedReturn
      selected.body.finalized boundary.occurrence.result.state finalContext ∧
    ActualContext (checkingContext selected) selected.body.finalized frames finalContext ∧
    GeneralizedActualStateInvariant boundary.occurrence.result.state (evidenceSource selected) ∧
    StatementHasType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := boundary.occurrence.inferenceContext.loopDepth }
      target boundary.occurrence.result.id finalContext
      { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
    StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution boundary.occurrence.result
      { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit }

theorem InitializedOccurrenceBoundary.sound {raw : Workspace.RawWorkspace}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement} {expectedReturn : Ty}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : InitializedOccurrenceBoundary selected source expectedReturn frames target)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (childSound : ExpressionRootedSoundness selected boundary.occurrence.childFuel) :
    InitializerOccurrenceConclusion boundary :=
  boundary.occurrence.statement_of_expressionSoundness checked boundary.scope boundary.interfaces
    boundary.invariant boundary.actual boundary.operational boundary.rawSubtree
    boundary.patterns boundary.literals boundary.requirements boundary.covered boundary.actualCovered
    boundary.barrier childSound

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end
