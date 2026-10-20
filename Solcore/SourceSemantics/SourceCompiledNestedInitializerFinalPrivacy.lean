import Solcore.SourceSemantics.SourceCompiledSelectedStatementResume
import Solcore.SourceSemantics.SourceCompiledNestedInitializerResume
import Solcore.SourceSemantics.SourceCompiledNestedTemplatePrivacy
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyReturnFinalization

/-! A selected outer declaration, a declaration inside its actual lambda
initializer, every remaining statement and the actual finalizer form one
privacy continuation. The outer binder's templates come from compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledGeneralizedSoundness

structure NestedInitializerFinalPrivacy
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} (selected : Selected compiled row fuel)
    (outerSource innerSource : Syntax.Statement) where
  outer : InitializerOccurrence selected outerSource
  nested : NestedInitializerResume outer innerSource
  final : ∀ type, Safe nested.inner.receipt.binding.1.scheme.quantified
    nested.inner.receipt.ready type →
    Avoids nested.inner.receipt.binding.1.scheme.quantified
      (selected.body.finalized.substitution.apply type)
  outerValue : Avoids nested.inner.receipt.binding.1.scheme.quantified
    (selected.body.finalized.substitution.apply outer.receipt.value.type)
  olderTypes : ∀ type, type.VariablesBelow outer.entry.inference.next →
    Avoids nested.inner.receipt.binding.1.scheme.quantified
      (selected.body.finalized.substitution.apply type)
  disjoint : ∀ q ∈ nested.inner.receipt.binding.1.scheme.quantified,
    q ∉ outer.receipt.binding.1.scheme.quantified
  newRows : ∀ requirement ∈ selected.body.body.state.requirements,
    requirement ∉ nested.inner.receipt.ready.requirements →
    ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
      Avoids nested.inner.receipt.binding.1.scheme.quantified
        (selected.body.finalized.substitution.apply type)

theorem Selected.nestedLambdaPrivacy
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.plan.specializations)
    (selected : Selected compiled row options.checkingFuel)
    {outerIndex innerIndex : Nat} {outerSource innerSource : Syntax.Statement}
    (outerPosition : selected.signature.source.value.body.value[outerIndex]? = some outerSource)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (outerForm : outerSource.value = .letDecl name annotation (some initializer))
    {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {returnAnnotation : Option Syntax.TypeExpr} {body : Syntax.Block}
    (lambdaForm : initializer.value = .lambda keyword parameters returnAnnotation body)
    (innerPosition : body.value[innerIndex]? = some innerSource)
    {innerName : Syntax.Identifier} {innerAnnotation : Option Syntax.TypeExpr}
    {innerInitializer : Syntax.Expr}
    (innerForm : innerSource.value = .letDecl innerName innerAnnotation (some innerInitializer)) :
    Nonempty (NestedInitializerFinalPrivacy selected outerSource innerSource) := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  let scope : CheckingScope selected.toBodySelection (checkingContext selected.toBodySelection) := .refl selected.toBodySelection
  obtain ⟨resume⟩ := selected.statementResume checked outerPosition
  obtain ⟨childFuel,receipt,_,_⟩ := resume.toOccurrence.initialized outerForm
    (scope.formation checked) (scope.functionsCanonical checked)
  have retained : resume.result.state.nodes <+: selected.body.returned.nodes := by
    rw [selected.body.returned_nodes]
    exact resume.retained
  let outer := InitializerOccurrence.ofReceipt checked scope receipt resume.ready
    resume.entryInvariant.1 (retained.subset receipt.recorded)
    (progress.final_substitution.trans resume.continuation.substitution_extends)
  have initializerEq : receipt.initializer = initializer := by
    have same := receipt.form.symm.trans outerForm
    simp only [Syntax.StatementValue.letDecl.injEq, Option.some.injEq] at same
    exact same.2.2
  have actualLambda : outer.receipt.initializer.value =
      .lambda keyword parameters returnAnnotation body := by
    change receipt.initializer.value = _
    rw [initializerEq]
    exact lambdaForm
  obtain ⟨nested⟩ := InitializerOccurrence.lambdaResume (selected := selected) outer checked scope resume.ready resume.entryNodesBelow
    resume.entryInvariant.1 resume.entryInvariant.2.2 retained actualLambda innerPosition innerForm
  have added := SourceCompiledNestedTemplatePrivacy.outer_binder_safe
    accepted member outer nested.inner nested.valueSafe
  have unchanged : SafeTransport nested.inner.receipt.binding.1.scheme.quantified
      receipt.ready resume.result.state :=
    .of_substitution_eq (congrArg InferState.substitution receipt.inference_eq)
  have live : LiveBindersSafe nested.inner.receipt.binding.1.scheme.quantified resume.result.state := by
    intro binder present
    rw [receipt.result_binders] at present
    rcases List.mem_cons.mp present with rfl | old
    · exact added
    · apply BinderSafe.transport (nested.live binder ?_) unchanged
      change binder ∈ receipt.ready.localBinders
      rw [receipt.ready_binders]
      exact old
  have bound : ∀ q ∈ nested.inner.receipt.binding.1.scheme.quantified,
      q.index < resume.result.state.inference.next := by
    intro q quantified
    rw [receipt.inference_eq]
    exact nested.bound q quantified
  have older : ∀ type, type.VariablesBelow resume.entry.inference.next →
      Safe nested.inner.receipt.binding.1.scheme.quantified resume.result.state type :=
    fun type below => unchanged type (nested.olderSafe type below)
  have closed : (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 :=
    Ty.variablesBelow_productMany
      ((formation.functions selected.signature selected.signatureMember).2.1.variablesBelow 0)
  have resultSafe : Safe nested.inner.receipt.binding.1.scheme.quantified
      resume.result.state resume.result.type := by
    have resultType : resume.result.type = .unit :=
      congrArg Detail.StatementResult.type receipt.completed
    rw [resultType]
    exact safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.freeVariables, Ty.unit])
  have suffix := resume.resume _ bound live (safe_closed _ _ closed) resultSafe older
  refine ⟨{
    outer, nested
    final := fun type safe => selected.finishPrivacy checked _ type
      (suffix.1 type (unchanged type (nested.transport type safe)))
    outerValue := selected.finishPrivacy checked _ _ (suffix.1 _ (unchanged _ nested.valueSafe))
    olderTypes := fun type below => selected.finishPrivacy checked _ type (suffix.1 type (older type below))
    disjoint := ?_
    newRows := ?_ }⟩
  · intro q innerMember outerMember
    exact nested.valueSafe q (List.mem_filter.mp outerMember).1 innerMember
  · intro requirement present fresh type typeMember
    apply selected.finishPrivacy checked _ type
    by_cases earlier : requirement ∈ receipt.ready.requirements
    · exact suffix.1 type (unchanged type (nested.newRows requirement earlier fresh type typeMember))
    · apply suffix.2.2.2 requirement present _ type typeMember
      have same : resume.result.state.requirements = receipt.ready.requirements :=
        congrArg (fun result : Detail.StatementResult => result.state.requirements) receipt.completed
      simpa only [same] using earlier

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
