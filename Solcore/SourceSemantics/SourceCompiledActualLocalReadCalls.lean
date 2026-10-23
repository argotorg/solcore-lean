import Solcore.SourceSemantics.SourceCompiledActualGeneralizationOrigins
import Solcore.SourceSemantics.SourceCompiledLocalReadOrigins

/-! A cached ordinary or method body supplies every local reference's exact
issuing lookup and actual call path. Finalization and parameter substitution
preserve that occurrence and local identity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceCompiledGeneralizedSoundness
open SourceInferenceExecution

namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

/-- The real empty body entry closes the retained read-call inventory. -/
theorem actual_local_read_calls (selected : BodySelection compiled row fuel) :
    ActualLocalRead.Origins selected.inferenceCall (evidenceSource selected).nodes := by
  have traced := ActualGeneralization.inferStatementsFuel_read_progress selected.body.inferred
    selected.inferenceCall_root
  have calls := traced.calls (State.initial_requirementsWellFormed _ _ _)
    (by intro id impossible; cases impossible) ActualLocalRead.Origins.empty
  change ActualLocalRead.Origins selected.inferenceCall selected.body.returned.nodes
  rw [selected.body.returned_nodes]
  exact calls

/-- The exact specialized source reference is mapped back through both actual
substitutions to the same raw read produced by body inference. -/
theorem specialized_local_read_call (selected : BodySelection compiled row fuel)
    {node : ExpressionNode} (member : .expression node ∈ row.function.typedBody.nodes)
    {name : String} {binder : Resolved.LocalId}
    (form : node.form = .reference name (.local binder)) :
    ActualLocalRead.Origin selected.inferenceCall node := by
  rw [selected.source] at member
  obtain ⟨finalNode, finalMember, finalId, finalForm, _, _⟩ :=
    SourceCompiledLocalReadOrigins.specialized_local_read_original member form
  rw [selected.body.resources.source_eq] at finalMember
  obtain ⟨rawNode, rawMember, rawId, rawForm, _, _⟩ :=
    SourceCompiledLocalReadOrigins.solved_local_read_original finalMember finalForm
  have origin := selected.actual_local_read_calls rawNode rawMember name binder rawForm
  exact origin.same_occurrence (rawId.trans finalId).symm (form.trans rawForm.symm)

/-- The issuing binder is the complete binder returned by guarded lookup in
its actual lexical scope, not merely an ID matched in the final node table. -/
theorem specialized_local_read_active (selected : BodySelection compiled row fuel)
    {node : ExpressionNode} (member : .expression node ∈ row.function.typedBody.nodes)
    {name : String} {binder : Resolved.LocalId}
    (form : node.form = .reference name (.local binder)) :
    ∃ lookup : LocalReadEvents.Lookup,
      node.id = lookup.id ∧
      node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      selected.InferenceCall (ActualLocalRead.lookupCall lookup) ∧
      lookup.binder ∈ lookup.initial.localBinders :=
  (selected.specialized_local_read_call member form).active

/-- Every completed cache position has the same actual checker body and
exact read paths, including late ordinary and implementation-method rows. -/
theorem cached_local_read_calls {raw : Workspace.RawWorkspace}
    {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    ∃ selected : BodySelection compiled named.specialized fuel,
      ∀ node : ExpressionNode, .expression node ∈ named.specialized.function.typedBody.nodes →
      ∀ name binder, node.form = .reference name (.local binder) →
        ActualLocalRead.Origin selected.inferenceCall node := by
  have member := CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  have origin := CoreLowering.CallablePreparedFinalCatalogOrigins.of_default_preparation
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached) _ member
  rw [(compiled.artifact_fields artifact).1] at origin
  obtain ⟨selected⟩ := SourceBodyTemplateScope.catalog_selection checked origin
  exact ⟨selected, fun _ member _ _ form => selected.specialized_local_read_call member form⟩

/-- Successful raw public compilation supplies the checker premise of the
cache-wide exact local-read theorem. -/
theorem compile_local_read_calls {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {cached : SourceCoreUnifiedCompilation.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    (artifact : compiled.artifact? = some cached)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    ∃ selected : BodySelection compiled named.specialized options.checkingFuel,
      ∀ node : ExpressionNode, .expression node ∈ named.specialized.function.typedBody.nodes →
      ∀ name binder, node.form = .reference name (.local binder) →
        ActualLocalRead.Origin selected.inferenceCall node :=
  cached_local_read_calls artifact (SourceCoreCompiler.compile_checked_source accepted) position

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
