import Solcore.SourceSemantics.SourceCompiledFinalizedGeneralizationBoundaries
import Solcore.SourceSemantics.SourceInferenceGeneralizedInitializerContext
import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences

/-! The selected worklist's original binder enters the initializer context of
the same successful finalizer. Retained source membership and the parent-child
edge are derived from its actual inference receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness SourceSpecializationWorklist

namespace FinalizedBindingEvent
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
  {fuel : Nat} {selected : Selected compiled row fuel} {binding : LocalLambdaBinding}

def initializerBinding (event : FinalizedBindingEvent selected binding) : InitializedLetBinding :=
  ⟨event.originalBinder.applySubstitution selected.body.finalized.substitution,
    .expression binding.initializer⟩

theorem finalized_statement (event : FinalizedBindingEvent selected binding) :
    ContainsStatement selected.body.finalized.typedSource event.original.id
      (event.original.applySubstitution selected.body.finalized.substitution) := by
  rw [selected.body.resources.source_eq]
  apply FlexibleSubstitution.ContainsStatement.applySubstitution
  refine ⟨?_, rfl⟩
  change .statement event.original ∈ selected.body.returned.nodes
  rw [selected.body.returned_nodes]
  exact event.originalPresent

theorem initializer_retained (event : FinalizedBindingEvent selected binding) :
    event.initializerBinding ∈ initializedLetBindings selected.body.finalized.typedSource := by
  unfold initializedLetBindings
  apply List.mem_flatMap.mpr
  refine ⟨.statement (event.original.applySubstitution selected.body.finalized.substitution),
    event.finalized_statement.1, ?_⟩
  simp [StatementNode.applySubstitution, event.originalForm, StatementForm.applySubstitution,
    statementInitializedLetBindings, initializerBinding]

theorem initializer_edge (event : FinalizedBindingEvent selected binding) :
    DirectChild selected.body.finalized.typedSource (.statement event.original.id)
      event.initializerBinding.initializer := by
  apply directChild_statement_reference event.finalized_statement
  simp [StatementNode.applySubstitution, event.originalForm, StatementForm.applySubstitution,
    StatementForm.references, initializerBinding]

/-- Entering the actual retained child preserves the recursive type invariant
and extends the same lexical initializer stack. No initializer typing is an
input to this boundary step. -/
theorem enter (event : FinalizedBindingEvent selected binding)
    {state : State} {context : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (invariant : RecursiveExpressionInvariant
      (SourceCompiledLocalFinalization.context compiled.program.environment
        compiled.program.signatures selected.signature selected.body.declaration)
      selected.body.finalized state context)
    (actual : ActualContext
      (SourceCompiledLocalFinalization.context compiled.program.environment
        compiled.program.signatures selected.signature selected.body.declaration)
      selected.body.finalized frames context)
    (covered : ActualContext.Covers selected.body.finalized frames (.statement event.original.id)) :
    RecursiveExpressionInvariant
      (SourceCompiledLocalFinalization.context compiled.program.environment
        compiled.program.signatures selected.signature selected.body.declaration)
      selected.body.finalized state (localSchemeInitializerContext context event.initializerBinding.binder) ∧
    ActualContext
      (SourceCompiledLocalFinalization.context compiled.program.environment
        compiled.program.signatures selected.signature selected.body.declaration)
      selected.body.finalized (frames ++ [event.initializerBinding])
      (localSchemeInitializerContext context event.initializerBinding.binder) ∧
    ActualContext.Covers selected.body.finalized (frames ++ [event.initializerBinding])
      (.expression binding.initializer) := by
  have child := actual.enter covered event.initializerBinding event.initializer_retained event.initializer_edge
  exact ⟨invariant.generalizedInitializer event.initializerBinding.binder, child⟩

end FinalizedBindingEvent
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
