import Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
import Solcore.SourceSemantics.SourceCompiledLocalBindings

/-! Actual worklist binding membership selects the original checker event.
The selected binder keeps its stable identity and quantified variables through
both real substitutions, while its full scheme transformation remains explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
open Frontend SourceInference SourceSpecializationWorklist TypeSystem

structure BindingEvent {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel) (binding : LocalLambdaBinding) where
  selected : StatementNode
  selectedPresent : .statement selected ∈ row.function.typedBody.nodes
  selectedForm : selected.form = .letDecl binding.binder (some binding.initializer)
  original : StatementNode
  originalBinder : TypedBinder
  originalPresent : .statement original ∈ receipt.body.state.nodes
  sameStatement : original.id = selected.id
  originalForm : original.form = .letDecl originalBinder (some binding.initializer)
  transformed : SourceSpecialization.applyBinder row.parameterSubstitution
    (originalBinder.applySubstitution receipt.substitution) = binding.binder
  sameLocal : originalBinder.id = binding.binder.id
  sameQuantified : originalBinder.scheme.quantified = binding.binder.scheme.quantified
  event : LocalGeneralizationEvents.Origin originalBinder binding.initializer

/-- A collector member is the exact binder of a real selected statement, so
its original event is selected without assuming uniqueness merely from an ID. -/
theorem InferredSelectedBody.binding_event {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (receipt : InferredSelectedBody compiled row fuel) {binding : LocalLambdaBinding}
    (member : binding ∈ localLambdaBindings row.function.typedBody) :
    Nonempty (BindingEvent receipt binding) := by
  obtain ⟨selected, selectedPresent, selectedForm⟩ := localLambdaBindings_statement_origin member
  obtain ⟨original, binder, originalPresent, sameId, originalForm, transformed, event⟩ :=
    receipt.initialized_event selectedPresent selectedForm
  have sameLocal := congrArg TypedBinder.id transformed
  change binder.id = binding.binder.id at sameLocal
  have sameQuantified := congrArg (fun value : TypedBinder => value.scheme.quantified) transformed
  change binder.scheme.quantified = binding.binder.scheme.quantified at sameQuantified
  exact ⟨⟨selected, selectedPresent, selectedForm, original, binder, originalPresent,
    sameId, originalForm, transformed, sameLocal, sameQuantified, event⟩⟩

/-- Selected compilation supplies both actual instance membership and the
original event; no assumed checker generalization or specialization law is used. -/
theorem compile_binding_events {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ receipt : InferredSelectedBody compiled row options.checkingFuel,
      ∃ instances, localLambdaInstances row.function.typedBody = .ok instances ∧
        ∀ value ∈ instances,
          value.binding ∈ localLambdaBindings row.function.typedBody ∧
          LocalLambdaInstance.ReadOrigin row.function.typedBody value ∧
          Nonempty (BindingEvent receipt value.binding) := by
  obtain ⟨receipt⟩ := compile_selected_body accepted member
  obtain ⟨instances, discovered, bindings⟩ := SourceCompiledLocalBindings.compile_binding_origins accepted member
  refine ⟨receipt, instances, discovered, ?_⟩
  intro value present
  have binding := bindings value present
  exact ⟨binding.1, binding.2.1, receipt.binding_event binding.1⟩

end Solcore.SourceSemantics.SourceCompiledLocalGeneralizationEvents
