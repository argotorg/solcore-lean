import Solcore.SourceSemantics.SourceCompiledActualLifetimeTraversal
import Solcore.SourceSemantics.SourceCompiledActualCaptureOrigins
import Solcore.SourceSemantics.SourceCompiledActualTemplateBacking
import Solcore.SourceSemantics.SourceInferenceRawStatementLifetime
import Solcore.SourceSemantics.SourceInferenceRawHeaderLifetime

/-! Every reached initialized declaration starts a lifetime from the real
entry invariants, then carries it through all actual enclosing calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open ProtectedVariables SourceCompiledGeneralizedSoundness SourceInferenceExecution
namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {checkingFuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}
    (selected : BodySelection compiled named.specialized checkingFuel)

theorem statementReceipt_retained
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    (here : selected.InferenceCall (.statement (fuel + 1) context source expectedReturn initial result))
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result) :
    receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders := by
  apply (selected.actualCall_binders_retained here).nodes
  exact List.mem_flatMap.mpr ⟨_, receipt.recorded, by
    simp [Node.initializedLetBinders, StatementForm.initializedLetBinders]⟩

theorem headerReceipt_retained
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (here : selected.InferenceCall (.forItem (fuel + 1) context source initial result.1 result.2))
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result) :
    receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders := by
  apply (selected.actualCall_binders_retained here).returned ⟨receipt.binding.1, .expression receipt.value.id⟩
  change _ ∈ forItemInitializedLetBindings result.1
  rw [congrArg forItemInitializedLetBindings receipt.recorded]
  exact List.mem_singleton_self _

theorem statement_lifetime
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    (here : selected.InferenceCall (.statement (fuel + 1) context source expectedReturn initial result))
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected)) :
    ∃ ready extension,
      GeneralizationLifetime
        (RawStatementLifetime.event (finalized := selected.body.finalized)
          receipt ready extension retained (selected.statementReceipt_retained here receipt))
        selected.inferenceCall.initial.inference.next selected.body.body.state [] := by
  have inputs := selected.actualCall_inputs checked here
  obtain ⟨ready, extension, seed⟩ := RawStatementLifetime.lifetime selected.body.resources receipt
    inputs.ready inputs.wellFormed inputs.catalog.catalog inputs.catalog.formation inputs.catalog.canonical
    (selected.actualCall_liveTemplatesBacked checked here)
    (selected.actualCall_captureOrigins checked here) retained
    (selected.statementReceipt_retained here receipt) (selected.actualCall_final_extension checked here)
  exact ⟨ready, extension, (CallOccurrence.lifetime artifact checked position here seed).restrict_outputs (by simp)⟩

theorem header_lifetime
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (here : selected.InferenceCall (.forItem (fuel + 1) context source initial result.1 result.2))
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected)) :
    ∃ ready extension,
      GeneralizationLifetime
        (RawHeaderLifetime.event (finalized := selected.body.finalized)
          receipt ready extension retained (selected.headerReceipt_retained here receipt))
        selected.inferenceCall.initial.inference.next selected.body.body.state [] := by
  have inputs := selected.actualCall_inputs checked here
  obtain ⟨ready, extension, seed⟩ := RawHeaderLifetime.lifetime selected.body.resources receipt
    inputs.ready inputs.wellFormed inputs.catalog.catalog inputs.catalog.formation inputs.catalog.canonical
    (selected.actualCall_liveTemplatesBacked checked here)
    (selected.actualCall_captureOrigins checked here) retained
    (selected.headerReceipt_retained here receipt) (selected.actualCall_final_extension checked here)
  exact ⟨ready, extension, (CallOccurrence.lifetime artifact checked position here seed).restrict_outputs (by simp)⟩

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
