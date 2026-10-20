import Solcore.SourceSemantics.SourceCompiledNestedInitializerPrivacy

/-! The exact initialized statement is retained alongside its private receipt,
so later consumers use the same initializer occurrence and binder allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

structure InitializedStatementReceiptPrivate
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    {childFuel : Nat} {inferenceContext : SourceInference.Context} {source : Syntax.Statement}
    {entry : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt childFuel inferenceContext source entry result) : Prop
    extends InitializedReceiptPrivate selected receipt where
  recorded : Node.statement {
    id := entry.allocateStatementId.1
    span := source.span
    type := .unit
    form := .letDecl receipt.binding.1 (some receipt.value.id) } ∈ selected.body.returned.nodes

namespace PrivateBlockContinuation
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : Selected compiled row fuel}

theorem initialized_statement (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ childFuel entry result, ∃ receipt : LocalLetRequirementTiming.Receipt childFuel block.inferenceContext source entry result,
      InitializedStatementReceiptPrivate selected receipt := by
  obtain ⟨occurrence⟩ := block.position checked position
  have formation := block.toBlockContinuation.formation checked
  have canonical := block.toBlockContinuation.canonical checked
  obtain ⟨childFuel,receipt,ready,bodyContinuation⟩ :=
    occurrence.toActiveStatementPrivacyOccurrence.toBackedStatementPrivacyOccurrence.toStatementPrivacyOccurrence.toOccurrence.initialized
      form formation canonical
  have progress := selected.inferenceProgress checked
  have resultExtension := Substitution.SemanticallyExtends.trans progress.final_substitution
    (occurrence.continuation.trans block.continuation).substitution_extends
  have readyExtension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at resultExtension
  have retainedNodes := occurrence.retained.trans block.retainedSource.nodes_prefix
  have retainedBinder : receipt.binding.1 ∈
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).initializedLetBinders := by
    unfold TypedSource.initializedLetBinders
    exact List.mem_flatMap.mpr ⟨_,retainedNodes.subset receipt.recorded,List.mem_singleton_self _⟩
  have live := ProtectedVariables.LocalLetRequirementTiming.Receipt.active_privacy selected.body.resources receipt
    occurrence.ready occurrence.entryWellFormed formation canonical occurrence.entryTemplates occurrence.entryOrigins
    retainedNodes resultExtension
  have properties := receipt.initializer_inference occurrence.ready formation canonical
  have bound : ∀ q ∈ receipt.binding.1.scheme.quantified, q.index < occurrence.result.state.inference.next := by
    intro q member
    have below := properties.2.1.solved.variablesBelow_apply properties.2.2
    have actual := below q (List.mem_filter.mp member).1
    rwa [receipt.inference_eq]
  have tail := block.after_unchanged_occurrence occurrence rfl (List.Subset.refl _) rfl
    receipt.binding.1.scheme.quantified bound live
  have templates := ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before receipt
    occurrence.entryTemplates occurrence.ready occurrence.entryWellFormed formation canonical
  have prior := ProtectedVariables.LocalLetRequirementTiming.Receipt.value_avoids_active receipt occurrence.ready
    occurrence.entryWellFormed occurrence.entryBound occurrence.entryPrivate
    (block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked) formation canonical
  refine ⟨childFuel,occurrence.entry,occurrence.result,receipt,
    { toInitializedReceiptPrivate :=
        ⟨ready,readyExtension,retainedBinder,occurrence.entryOrigins.congr_localBinders receipt.ready_binders,
          templates,prior,?_,?_⟩
      recorded := retainedNodes.subset receipt.recorded }⟩
  · intro type safe
    apply selected.finishPrivacy checked _ type
    apply tail.1 type
    exact SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq) type safe
  · intro requirement member fresh type typeMember
    apply selected.finishPrivacy checked _ type
    apply tail.2.2 requirement member _ type typeMember
    have same : occurrence.result.state.requirements = receipt.ready.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) receipt.completed
    simpa only [same] using fresh

end PrivateBlockContinuation
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
