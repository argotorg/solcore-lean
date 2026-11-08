import Solcore.SourceSemantics.Internal.Execution.BinderRetention
import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Compiled.Contracts
import Solcore.SourceSemantics.Internal.Execution.CallInputs
import Solcore.SourceSemantics.Internal.Execution.CallGraph
import Solcore.Frontend.SourceInference.Internal.LocalReadScopes
import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.Internal.Execution.GeneralizationEvents
import Solcore.SourceSemantics.Internal.Inference.CaptureOrigins
import Solcore.SourceSemantics.Internal.Execution.GeneralizationCoverage
import Solcore.SourceSemantics.Internal.Prepared.TemplateScope
import Solcore.SourceSemantics.Internal.Compiled.Origins
import Solcore.SourceSemantics.Internal.Execution.TemplateBacking
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.LambdaCompilation
import Solcore.SourceSemantics.Internal.Execution.NodeShapes
import Solcore.SourceSemantics.Internal.Inference.ShapeClosure

/-!
# Entries of actual calls

What a selected body supplies at every reached inference call: binders, inputs, graph closure,
scope, capture origins, template backing and allocator bounds. The lexical order of discovered local
bodies follows from them.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualBinderRetention
/-! Each actual inference call retains its complete initialized binder
metadata in the selected body's evidence source, including loop headers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution
open SourceCompiledGeneralizedSoundness

namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem actualCall_binders_retained (selected : BodySelection compiled row fuel)
    {call : CallIndex} (here : selected.InferenceCall call) :
    call.CaptureRetained (evidenceSource selected) := by
  have retained := here.initialized_binders
  have rootInventory :
      selected.inferenceCall.initializedBinders = (evidenceSource selected).initializedLetBinders := by
    simp only [CallIndex.initializedBinders, inferenceCall, CallIndex.final,
      CallIndex.returnedBindings, List.map_nil, List.append_nil, evidenceSource,
      TypedSource.initializedLetBinders, State.toTypedSource, selected.body.returned_nodes]
  rw [rootInventory] at retained
  constructor
  · intro binder present
    exact retained (List.mem_append_left _ present)
  · intro binding present
    exact retained (List.mem_append_right _ (List.mem_map.mpr ⟨binding, present, rfl⟩))

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualBodyInputs
/-! The selected body's original initialization supplies ordinary inference
inputs at the root. Actual child-call provenance transports those inputs
through the same successful computation, for ordinary functions and methods. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness SourceInferenceExecution

namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

/-- Readiness and the return allocator bound belong to the actual checked
body. The initial requirement ledger and signature catalog are also derived
internally, without an executable profile or semantic body-typing premise. -/
theorem inferenceCall_inputs (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program) :
    selected.inferenceCall.Inputs := by
  have progress := selected.inferenceProgress checked
  have scope := CheckingScope.refl selected
  exact {
    ready := progress.initialReady
    wellFormed := State.initial_requirementsWellFormed _ _ _
    catalog := ⟨scope.catalog checked, scope.formation checked, scope.functionsCanonical checked⟩
    bounds := progress.returnBelow }

/-- Every reached inference call receives the same root's actual state,
catalog and allocator prerequisites through the real child edges. -/
theorem actualCall_inputs (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    call.Inputs :=
  CallOccurrence.inputs (selected.inferenceCall_inputs checked) here

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualCallGraphClosure
/-! Empty actual body initialization supplies graph closure at every reached
call and at the exact pre-generalization initializer checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution

theorem childEdgesExist_of_nodesClosed {state : State} (closed : NodesClosed state.nodes)
    (roots : List NodeId) : ChildEdgesExist (state.toTypedSource roots) :=
  closed

namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem actualCall_nodesClosed (selected : BodySelection compiled row fuel)
    {call : CallIndex} (here : selected.InferenceCall call) :
    NodesClosed call.initial.nodes :=
  here.nodesClosed NodesClosed.nil

/-- Both closure and the returned root come from the same initializer run. -/
theorem statement_initializer_graph (selected : BodySelection compiled row fuel)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {entry : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.statement (childFuel + 1) context source expectedReturn entry result)) :
    NodesClosed receipt.ready.nodes ∧
      NodeIdsPresent [.expression receipt.value.id] receipt.ready.nodes := by
  have graph := Detail.inferExprFuel_occurrenceGraph receipt.child
  exact ⟨graph.graph.closed (selected.actualCall_nodesClosed here), graph.returned⟩

theorem header_initializer_graph (selected : BodySelection compiled row fuel)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {entry : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.forItem (childFuel + 1) context source entry result.1 result.2)) :
    NodesClosed receipt.ready.nodes ∧
      NodeIdsPresent [.expression receipt.value.id] receipt.ready.nodes := by
  have graph := Detail.inferExprFuel_occurrenceGraph receipt.child
  exact ⟨graph.graph.closed (selected.actualCall_nodesClosed here), graph.returned⟩

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualCallScope
/-! Actual inference descent preserves the selected declaration's static
checking context. Changes to loop depth do not introduce a different catalog,
generic owner, type-parameter scope or assumption set. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics
open Frontend SourceInference TypeSystem
open SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness

namespace SourceInferenceExecution
theorem ChildStep.checkingScope
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {parent child : CallIndex}
    (step : ChildStep parent child)
    (scope : CheckingScope selected parent.context) :
    CheckingScope selected child.context := by
  cases step <;> exact ⟨scope.signatures, scope.owner, scope.parameters, scope.assumptions⟩
end SourceInferenceExecution

namespace SourceCompiledLocalFinalization.BodySelection
open SourceInferenceExecution

theorem actualCall_scope
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    {call : CallIndex} (here : selected.InferenceCall call) :
    CheckingScope selected call.context := by
  induction here with
  | root _ => exact CheckingScope.refl selected
  | child _ step ih => exact step.checkingScope ih

end SourceCompiledLocalFinalization.BodySelection
end Solcore.SourceSemantics
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualCaptureOrigins
/-! Capture origins at every reached inference entry come from the actual
root initialization and the same body's retained declaration inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference SourceInferenceSoundness

theorem CallOccurrence.captureOrigins
    {root call : CallIndex} {whole : TypedSource}
    (here : CallOccurrence root call) (inputs : root.Inputs)
    (origins : ActiveBinderCaptureOrigins root.initial whole)
    (retained : ∀ {prior}, CallOccurrence root prior → prior.CaptureRetained whole) :
    ActiveBinderCaptureOrigins call.initial whole := by
  induction here with
  | root accepted => exact origins
  | child prior step ih =>
    exact step.captureOrigins (prior.inputs inputs) ih
      (fun next => retained (.child prior next))

end Solcore.SourceSemantics.SourceInferenceExecution

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness SourceInferenceExecution
namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem inferenceCall_captureOrigins (selected : BodySelection compiled row fuel) :
    ActiveBinderCaptureOrigins selected.inferenceCall.initial (evidenceSource selected) := by
  apply activeBinderCaptureOrigins_initial_mono
  intro entry member
  obtain ⟨parameter, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem actualCall_captureOrigins (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    ActiveBinderCaptureOrigins call.initial (evidenceSource selected) :=
  here.captureOrigins (selected.inferenceCall_inputs checked) selected.inferenceCall_captureOrigins
    (fun prior => selected.actualCall_binders_retained prior)

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualGeneralizationOrigins
/-! The original selected-body inference supplies every initialized binding's
exact execution path. This covers ordinary and method bodies with the same
checking receipt and preserves the original binder and initializer identities. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceCompiledGeneralizedSoundness
open SourceInferenceExecution

namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

/-- Empty initial source and ledgers provide the inventory's prerequisites.
No semantic source-typing or compilation-profile premise is required. -/
theorem actual_generalization_origins (selected : BodySelection compiled row fuel) :
    ActualGeneralization.Origins selected.inferenceCall (evidenceSource selected).nodes := by
  have ready : LocalGeneralizationEvents.Ready (initial selected.signature selected.body.declaration) := by
    refine ⟨State.initial_requirementsWellFormed _ _ _, ?_, ?_⟩
    · intro id impossible
      exact False.elim (List.not_mem_nil impossible)
    · intro node impossible
      exact False.elim (List.not_mem_nil impossible)
  have origins := ActualGeneralization.inferStatementsFuel_origins selected.body.inferred
    selected.inferenceCall_root ready ActualGeneralization.Origins.empty
  change ActualGeneralization.Origins selected.inferenceCall selected.body.returned.nodes
  rw [selected.body.returned_nodes]
  exact origins

/-- Each complete raw initialized binding comes from an actual statement or
header receipt reached by this same selected body's successful inference. -/
theorem actual_initialized_origin (selected : BodySelection compiled row fuel)
    {binding : InitializedLetBinding}
    (member : binding ∈ initializedLetBindings (evidenceSource selected)) :
    ∃ initializer, binding.initializer = .expression initializer ∧
      ActualGeneralization.Origin selected.inferenceCall binding.binder initializer :=
  selected.actual_generalization_origins.initialized member

/-- Every completed ordinary or method cache row has the same original
checking body and a complete inventory of actual generalization calls. -/
theorem cached_initialized_origins {raw : Workspace.RawWorkspace}
    {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    ∃ selected : BodySelection compiled named.specialized fuel,
      ∀ binding ∈ initializedLetBindings (evidenceSource selected),
        ∃ initializer, binding.initializer = .expression initializer ∧
          ActualGeneralization.Origin selected.inferenceCall binding.binder initializer := by
  have member := CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  have origin := CoreLowering.CallablePreparedFinalCatalogOrigins.of_default_preparation
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached) _ member
  rw [(compiled.artifact_fields artifact).1] at origin
  obtain ⟨selected⟩ := SourceBodyTemplateScope.catalog_selection checked origin
  exact ⟨selected, fun _ member => selected.actual_initialized_origin member⟩

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualLocalReadCalls
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledActualTemplateBacking
/-! The actual initialized body, including a cached method body, supplies
raw local-template witnesses throughout its reached inference calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceInferenceExecution ProtectedVariables
namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem inferenceCall_liveTemplatesBacked (selected : BodySelection compiled row fuel) :
    LiveTemplatesBacked selected.inferenceCall.initial :=
  LiveTemplatesBacked.initial _ _ _

theorem actualCall_liveTemplatesBacked (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    LiveTemplatesBacked call.initial :=
  here.liveTemplatesBacked (selected.inferenceCall_inputs checked)
    selected.inferenceCall_liveTemplatesBacked

/-- Each prepared ordinary or method cache row supplies these same witnesses
at all calls in its original successful inference. -/
theorem cached_liveTemplatesBacked
    {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    ∃ selected : BodySelection compiled named.specialized fuel,
      ∀ call, selected.InferenceCall call → LiveTemplatesBacked call.initial := by
  have member := CoreLowering.RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  have origin := CoreLowering.CallablePreparedFinalCatalogOrigins.of_default_preparation
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached) _ member
  rw [(compiled.artifact_fields artifact).1] at origin
  obtain ⟨selected⟩ := SourceBodyTemplateScope.catalog_selection checked origin
  exact ⟨selected, fun _ here => selected.actualCall_liveTemplatesBacked checked here⟩

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerAllocationBounds
/-! Recorded initialized binders stay below the actual local allocator at
every reached call and at the exact ready state of its initializer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution
open LocalGeneralizationBoundaries
namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

private theorem annotationExpected {context : SourceInference.Context}
    {source : Option Syntax.TypeExpr} {type : Option Ty}
    (annotation : LocalLetRequirementTiming.Annotation context source type) :
    AnnotationExpected context source type := by
  cases annotation with
  | none => exact .absent
  | some accepted => exact .present accepted

private theorem initial_ready (selected : BodySelection compiled row fuel) :
    LocalGeneralizationEvents.Ready selected.inferenceCall.initial := by
  refine ⟨State.initial_requirementsWellFormed _ _ _, ?_, ?_⟩
  · intro id impossible
    exact False.elim (List.not_mem_nil impossible)
  · intro node impossible
    exact False.elim (List.not_mem_nil impossible)

theorem actualCall_initializedAllocated (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    InitializedBindersAllocated call.initial :=
  (here.boundaries_prefix (selected.inferenceCall_inputs checked)).initializedAllocated
    (initial_ready selected) (State.initial_localBindersBelowNextLocal _ _ _)
    (InitializedBindersAllocated.empty rfl)

theorem actualCall_final_initializedAllocated (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    InitializedBindersAllocated call.final := by
  have inputs := selected.inferenceCall_inputs checked
  have entryProgress := here.boundaries_prefix inputs
  exact (entryProgress.trans (call.boundaryProgress (here.inputs inputs) here.accepted)).initializedAllocated
    (initial_ready selected) (State.initial_localBindersBelowNextLocal _ _ _)
    (InitializedBindersAllocated.empty rfl)

/-- The statement receipt and its actual recursive edge select the same
initializer result; the bound is derived from the forward successful computation. -/
theorem statement_initializer_allocated (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {entry : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.statement (childFuel + 1) context source expectedReturn entry result)) :
    InitializedBindersAllocated receipt.ready := by
  have annotation := annotationExpected receipt.annotationAccepted
  have step := ChildStep.statement_initializer here.accepted receipt.form rfl annotation receipt.child
  exact selected.actualCall_final_initializedAllocated checked (.child here step)

/-- The same actual checkpoint is available for initializer and post headers. -/
theorem header_initializer_allocated (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {entry : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.forItem (childFuel + 1) context source entry result.1 result.2)) :
    InitializedBindersAllocated receipt.ready := by
  have annotation := annotationExpected receipt.annotationAccepted
  have step := ChildStep.forItem_initializer here.accepted receipt.form annotation receipt.child
  exact selected.actualCall_final_initializedAllocated checked (.child here step)

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerReadCutoff
/-! Actual body initialization supplies read cutoffs at every reached call
and at the exact initializer return state used for generalization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceExecution
namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem actualCall_read_cutoff (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    LocalReadCutoff call.initial :=
  here.read_cutoff (selected.inferenceCall_inputs checked)
    (State.initial_localBindersBelowNextLocal _ _ _)
    (by intro id impossible; cases impossible)
    (by intro node impossible; cases impossible)

theorem actualCall_final_read_cutoff (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    LocalReadCutoff call.final := by
  have inputs := selected.inferenceCall_inputs checked
  exact CallIndex.localReadCutoff here.accepted (here.inputs inputs)
    (ActualLocalAllocator.occurrence_bound inputs
      (State.initial_localBindersBelowNextLocal _ _ _) here)
    (here.direct_prefix.allocated inputs.wellFormed (by intro id impossible; cases impossible))
    (selected.actualCall_read_cutoff checked here)

/-- The statement receipt and its actual recursive edge select the same
initializer result; no final-table cutoff is moved backwards. -/
theorem statement_initializer_read_cutoff (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {entry : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.statement (childFuel + 1) context source expectedReturn entry result)) :
    LocalReadCutoff receipt.ready := by
  have annotation := annotationExpected receipt.annotationAccepted
  have step := ChildStep.statement_initializer here.accepted receipt.form rfl annotation receipt.child
  exact selected.actualCall_final_read_cutoff checked (.child here step)

/-- The same actual checkpoint is available for initializer and post headers. -/
theorem header_initializer_read_cutoff (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {entry : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.forItem (childFuel + 1) context source entry result.1 result.2)) :
    LocalReadCutoff receipt.ready := by
  have annotation := annotationExpected receipt.annotationAccepted
  have step := ChildStep.forItem_initializer here.accepted receipt.form annotation receipt.child
  exact selected.actualCall_final_read_cutoff checked (.child here step)

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalLexicalSubtree
/-! A real cached body uses the same flexible finalizer and rigid application
when a discovered lambda record is recovered at an earlier initializer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceSpecializationWorklist CoreLowering.GeneralizedLocalLexicalSubtree
namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat}

/-- Recover a complete original record from a real specialized lambda body.
The earlier closure premise is for this actual preserved initializer subtree. -/
theorem local_lambda_node_before (selected : BodySelection compiled row fuel)
    {before : TypedSource} {localInstance : LocalLambdaInstance} {nodes : List Node} {node : Node}
    (preserved : RawSubtreePreserved before
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
      (.expression localInstance.binding.initializer))
    (beforeClosed : ChildEdgesExist before)
    (present : NodeId.expression localInstance.binding.initializer ∈ nodeIds before)
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : node ∈ nodes) :
    ∃ original, original ∈ before.nodes ∧ original.id = node.id ∧
      SourceSpecialization.applyNode row.parameterSubstitution
        (original.applySubstitution selected.body.finalized.substitution) = node := by
  have graph : OccurrenceGraphClosed row.function.typedBody := by
    rw [selected.source]
    exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters
      row.parameterSubstitution selected.body.resources.graph_closed
  have path := body_node_descends graph.wellFormed.nodeOccurrencesUnique
    graph.wellFormed.childEdgesExist accepted member
  have contains : ContainsNode row.function.typedBody node.id node :=
    ⟨localLambdaBodyNodes_members accepted member, rfl⟩
  rw [selected.source] at path contains
  have finalPath := StructuralSubstitution.descends_of_applyParameters path
  obtain ⟨finalized, finalizedContains, finalSame⟩ :=
    StructuralSubstitution.containsNode_of_applyParameters contains
  rw [selected.body.resources.source_eq] at finalPath finalizedContains
  have rawPath := FlexibleSubstitution.descends_of_applySubstitution finalPath
  obtain ⟨original, originalContains, originalSame⟩ :=
    FlexibleSubstitution.containsNode_of_applySubstitution finalizedContains
  have unique : NodeOccurrencesUnique
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) := by
    have result := selected.body.resources.graph_closed.wellFormed.nodeOccurrencesUnique
    rw [selected.body.resources.source_eq] at result
    simpa only [NodeOccurrencesUnique, FlexibleSubstitution.applyTypedSource_nodeOccurrenceIds]
      using result
  refine ⟨original, preserved.node_inverse beforeClosed present unique originalContains.1
    (.inr (by simpa only [originalContains.2] using rawPath)),
    originalContains.2, ?_⟩
  rw [originalSame]
  exact finalSame

/-- The actual local reference keeps its target binder and identity when it is
recovered from the earlier initializer table. Coercion metadata is preserved
exactly by the two source substitutions. -/
theorem local_lambda_read_before (selected : BodySelection compiled row fuel)
    {before : TypedSource} {localInstance : LocalLambdaInstance} {nodes : List Node}
    {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (preserved : RawSubtreePreserved before
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
      (.expression localInstance.binding.initializer))
    (beforeClosed : ChildEdgesExist before)
    (present : NodeId.expression localInstance.binding.initializer ∈ nodeIds before)
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : Node.expression read ∈ nodes)
    (form : read.form = .reference name (.local binder)) :
    ∃ original : ExpressionNode, Node.expression original ∈ before.nodes ∧
      original.id = read.id ∧ original.form = .reference name (.local binder) ∧
      original.requirements = read.requirements ∧
      original.localSchemeInstantiationStart = read.localSchemeInstantiationStart := by
  obtain ⟨raw, rawMember, _, same⟩ :=
    selected.local_lambda_node_before preserved beforeClosed present accepted member
  have mapped : Node.expression read ∈
      (SourceSpecialization.applyTypedSource row.parameterSubstitution
        (before.applySubstitution selected.body.finalized.substitution)).nodes :=
    List.mem_map.mpr ⟨raw.applySubstitution selected.body.finalized.substitution,
      List.mem_map.mpr ⟨raw, rawMember, rfl⟩, same⟩
  obtain ⟨finalized, finalMember, finalId, finalForm, finalRequirements, finalStart⟩ :=
    SourceCompiledLocalReadOrigins.specialized_local_read_original mapped form
  obtain ⟨original, originalMember, originalId, originalForm, originalRequirements, originalStart⟩ :=
    SourceCompiledLocalReadOrigins.solved_local_read_original finalMember finalForm
  exact ⟨original, originalMember, originalId.trans finalId, originalForm,
    originalRequirements.trans finalRequirements, originalStart.trans finalStart⟩

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalLexicalOrder
/-! Actual discovery bindings retain their original initialized checker call.
The enclosing local allocator is taken from that same receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceSpecializationWorklist SourceInferenceExecution
open SourceCompiledGeneralizedSoundness
namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat}

/-- Return-type unification preserves the actual node table selected for
finalization, so a reached child keeps its syntax in that same evidence source. -/
theorem actualCall_final_nodeShapes (selected : BodySelection compiled row fuel)
    {call : CallIndex} (here : selected.InferenceCall call) :
    NodeShapesPreserved call.final.nodes (evidenceSource selected).nodes := by
  have shapes := CallOccurrence.finalNodeShapes here
  change NodeShapesPreserved call.final.nodes selected.body.body.state.nodes at shapes
  change NodeShapesPreserved call.final.nodes selected.body.returned.nodes
  rw [selected.body.returned_nodes]
  exact shapes

/-- Rigid and flexible finalization retain both the actual owner ID and its
initializer ID. The recovered call is reached by this same body inference. -/
theorem local_lambda_actual_origin (selected : BodySelection compiled row fuel)
    {binding : LocalLambdaBinding}
    (member : binding ∈ localLambdaBindings row.function.typedBody) :
    ∃ rawBinder : TypedBinder,
      rawBinder.id = binding.binder.id ∧
      ActualGeneralization.Origin selected.inferenceCall rawBinder binding.initializer := by
  obtain ⟨statement, statementMember, statementForm⟩ :=
    localLambdaBindings_statement_origin member
  rw [selected.source] at statementMember
  obtain ⟨finalized, finalBinder, finalMember, _, finalForm, rigid⟩ :=
    SourceCompiledLocalGeneralizationEvents.specialized_initialized_statement_original
      statementMember statementForm
  rw [selected.body.resources.source_eq] at finalMember
  obtain ⟨raw, rawBinder, rawMember, _, rawForm, flexible⟩ :=
    SourceCompiledLocalGeneralizationEvents.solved_initialized_statement_original finalMember finalForm
  have initialized : ({binder := rawBinder, initializer := .expression binding.initializer} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected) := by
    apply List.mem_flatMap.mpr
    refine ⟨.statement raw, rawMember, ?_⟩
    change _ ∈ statementInitializedLetBindings raw.form
    rw [rawForm]
    exact List.mem_singleton_self _
  obtain ⟨initializer, initSame, actual⟩ := selected.actual_initialized_origin initialized
  have sameInitializer : initializer = binding.initializer :=
    (NodeId.expression.inj initSame).symm
  refine ⟨rawBinder, ?_, sameInitializer ▸ actual⟩
  have rigidId := congrArg TypedBinder.id rigid
  have flexibleId := congrArg TypedBinder.id flexible
  exact flexibleId.trans rigidId

/-- Recover the earlier syntax of an actual discovered lambda node. Both
substitutions apply to the retained raw record; only its shape is required at
the earlier checkpoint. -/
theorem local_lambda_node_before_shape (selected : BodySelection compiled row fuel)
    {before : TypedSource} {localInstance : LocalLambdaInstance} {nodes : List Node} {node : Node}
    (preserved : NodeShapesPreserved before.nodes (evidenceSource selected).nodes)
    (beforeClosed : ChildEdgesExist before)
    (present : NodeId.expression localInstance.binding.initializer ∈ nodeIds before)
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : node ∈ nodes) :
    ∃ earlier ∈ before.nodes, ∃ raw : Node,
      SameNodeShape earlier raw ∧
      SourceSpecialization.applyNode row.parameterSubstitution
        (raw.applySubstitution selected.body.finalized.substitution) = node := by
  have graph : OccurrenceGraphClosed row.function.typedBody := by
    rw [selected.source]
    exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters
      row.parameterSubstitution selected.body.resources.graph_closed
  have path := CoreLowering.GeneralizedLocalLexicalSubtree.body_node_descends
    graph.wellFormed.nodeOccurrencesUnique graph.wellFormed.childEdgesExist accepted member
  have contains : ContainsNode row.function.typedBody node.id node :=
    ⟨localLambdaBodyNodes_members accepted member, rfl⟩
  rw [selected.source] at path contains
  have finalPath := StructuralSubstitution.descends_of_applyParameters path
  obtain ⟨finalized, finalizedContains, finalSame⟩ :=
    StructuralSubstitution.containsNode_of_applyParameters contains
  rw [selected.body.resources.source_eq] at finalPath finalizedContains
  have rawPath := FlexibleSubstitution.descends_of_applySubstitution finalPath
  obtain ⟨raw, rawContains, rawSame⟩ :=
    FlexibleSubstitution.containsNode_of_applySubstitution finalizedContains
  have unique : NodeOccurrencesUnique (evidenceSource selected) := by
    have result := selected.body.resources.graph_closed.wellFormed.nodeOccurrencesUnique
    rw [selected.body.resources.source_eq] at result
    simpa only [NodeOccurrencesUnique, FlexibleSubstitution.applyTypedSource_nodeOccurrenceIds]
      using result
  obtain ⟨earlier, earlierMember, shape⟩ :=
    SourceInferenceSoundness.NodeShapesPreserved.node_inverse preserved beforeClosed present unique
      rawContains.1 (.inr (by simpa only [rawContains.2] using rawPath))
  refine ⟨earlier, earlierMember, raw, shape, ?_⟩
  rw [rawSame]
  exact finalSame

/-- Coercion metadata does not affect the local target recovered at the
initializer checkpoint. -/
theorem local_lambda_read_before_shape (selected : BodySelection compiled row fuel)
    {before : TypedSource} {localInstance : LocalLambdaInstance} {nodes : List Node}
    {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (preserved : NodeShapesPreserved before.nodes (evidenceSource selected).nodes)
    (beforeClosed : ChildEdgesExist before)
    (present : NodeId.expression localInstance.binding.initializer ∈ nodeIds before)
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : Node.expression read ∈ nodes)
    (form : read.form = .reference name (.local binder)) :
    ∃ earlier : ExpressionNode, Node.expression earlier ∈ before.nodes ∧
      earlier.id = read.id ∧ earlier.form = .reference name (.local binder) := by
  obtain ⟨earlier, earlierMember, raw, shape, same⟩ :=
    selected.local_lambda_node_before_shape preserved beforeClosed present accepted member
  have mapped : Node.expression read ∈
      (SourceSpecialization.applyTypedSource row.parameterSubstitution
        (({owner := before.owner, inputs := [], roots := [], nodes := [raw]} : TypedSource).applySubstitution selected.body.finalized.substitution)).nodes :=
    List.mem_map.mpr ⟨raw.applySubstitution selected.body.finalized.substitution,
      List.mem_map.mpr ⟨raw, List.mem_singleton_self _, rfl⟩, same⟩
  obtain ⟨finalized, finalMember, finalId, finalForm, _, _⟩ :=
    SourceCompiledLocalReadOrigins.specialized_local_read_original mapped form
  obtain ⟨original, originalMember, originalId, originalForm, _, _⟩ :=
    SourceCompiledLocalReadOrigins.solved_local_read_original finalMember finalForm
  have rawEq : Node.expression original = raw := List.mem_singleton.mp originalMember
  rw [← rawEq] at shape
  cases earlier with
  | statement _ => cases shape
  | expression earlier =>
    exact ⟨earlier, earlierMember, shape.1.trans (originalId.trans finalId),
      shape.2.trans originalForm⟩


/-- The same statement initializer supplies its actual read cutoff. The graph
and shape arguments are filled by the actual-prefix and actual-suffix producers
in the final connection. -/
private theorem statement_read_lt
    {raw : Workspace.RawWorkspace}
    (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance} {nodes : List Node}
    {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {entry : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.statement (childFuel + 1) context source expectedReturn entry result))
    (sameBinder : receipt.binding.1.id = localInstance.binding.binder.id)
    (sameInitializer : receipt.value.id = localInstance.binding.initializer)
    (preserved : NodeShapesPreserved receipt.ready.nodes (evidenceSource selected).nodes)
    (closed : ChildEdgesExist (receipt.ready.toTypedSource []))
    (present : NodeId.expression receipt.value.id ∈ nodeIds (receipt.ready.toTypedSource []))
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : Node.expression read ∈ nodes)
    (form : read.form = .reference name (.local binder)) :
    binder.binderIndex < localInstance.binding.binder.id.binderIndex := by
  have root : NodeId.expression localInstance.binding.initializer ∈
      nodeIds (receipt.ready.toTypedSource []) := sameInitializer ▸ present
  obtain ⟨earlier, earlierMember, _, earlierForm⟩ :=
    selected.local_lambda_read_before_shape preserved closed root accepted member form
  have before := selected.statement_initializer_read_cutoff checked receipt here
    earlier earlierMember name binder earlierForm
  rw [← sameBinder]
  exact before

private theorem header_read_lt
    {raw : Workspace.RawWorkspace}
    (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance} {nodes : List Node}
    {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {entry : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source entry result)
    (here : selected.InferenceCall
      (.forItem (childFuel + 1) context source entry result.1 result.2))
    (sameBinder : receipt.binding.1.id = localInstance.binding.binder.id)
    (sameInitializer : receipt.value.id = localInstance.binding.initializer)
    (preserved : NodeShapesPreserved receipt.ready.nodes (evidenceSource selected).nodes)
    (closed : ChildEdgesExist (receipt.ready.toTypedSource []))
    (present : NodeId.expression receipt.value.id ∈ nodeIds (receipt.ready.toTypedSource []))
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : Node.expression read ∈ nodes)
    (form : read.form = .reference name (.local binder)) :
    binder.binderIndex < localInstance.binding.binder.id.binderIndex := by
  have root : NodeId.expression localInstance.binding.initializer ∈
      nodeIds (receipt.ready.toTypedSource []) := sameInitializer ▸ present
  obtain ⟨earlier, earlierMember, _, earlierForm⟩ :=
    selected.local_lambda_read_before_shape preserved closed root accepted member form
  have before := selected.header_initializer_read_cutoff checked receipt here
    earlier earlierMember name binder earlierForm
  rw [← sameBinder]
  exact before


private theorem annotation_expected {context : SourceInference.Context}
    {source : Option Syntax.TypeExpr} {type : Option Ty}
    (annotation : LocalLetRequirementTiming.Annotation context source type) :
    AnnotationExpected context source type := by
  cases annotation with
  | none => exact .absent
  | some accepted => exact .present accepted

/-- An actual direct lexical body can only read a binder allocated before its
own declaration. The initialized owner and every graph/cutoff fact are derived
from this same checked body's real recursive path. -/
theorem local_lambda_read_binder_lt
    {raw : Workspace.RawWorkspace}
    (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin row.function.typedBody localInstance)
    {nodes : List Node} {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : Node.expression read ∈ nodes)
    (form : read.form = .reference name (.local binder)) :
    binder.binderIndex < localInstance.binding.binder.id.binderIndex := by
  obtain ⟨rawBinder, same, actual⟩ := selected.local_lambda_actual_origin origin.binding_member
  generalize initializerEq : localInstance.binding.initializer = initializer at actual
  cases actual with
  | statement receipt here =>
      have graph := selected.statement_initializer_graph receipt here
      have step := ChildStep.statement_initializer here.accepted receipt.form rfl
        (annotation_expected receipt.annotationAccepted) receipt.child
      have shapes := selected.actualCall_final_nodeShapes (.child here step)
      exact statement_read_lt selected checked receipt here same initializerEq.symm shapes graph.1
        (graph.2 (List.mem_singleton_self _)) accepted member form
  | header receipt here =>
      have graph := selected.header_initializer_graph receipt here
      have step := ChildStep.forItem_initializer here.accepted receipt.form
        (annotation_expected receipt.annotationAccepted) receipt.child
      have shapes := selected.actualCall_final_nodeShapes (.child here step)
      exact header_read_lt selected checked receipt here same initializerEq.symm shapes graph.1
        (graph.2 (List.mem_singleton_self _)) accepted member form

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalCanonicalReadOrder
/-! Local reads on any canonical path beneath an actual initializer existed
before that declaration's local identity was allocated. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceSpecializationWorklist SourceInferenceExecution
open SourceCompiledGeneralizedSoundness
namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat}

/-- Invert any canonical descendant of the initializer, including paths into
nested lambda bodies that the direct lexical collector intentionally skips. -/
theorem local_lambda_descendant_node_before_shape (selected : BodySelection compiled row fuel)
    {before : TypedSource} {initializer : ExpressionId} {node : Node}
    (preserved : NodeShapesPreserved before.nodes (evidenceSource selected).nodes)
    (closed : ChildEdgesExist before)
    (present : NodeId.expression initializer ∈ nodeIds before)
    (member : node ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression initializer) node.id) :
    ∃ earlier ∈ before.nodes, ∃ raw : Node, SameNodeShape earlier raw ∧
      SourceSpecialization.applyNode row.parameterSubstitution
        (raw.applySubstitution selected.body.finalized.substitution) = node := by
  have contains : ContainsNode row.function.typedBody node.id node := ⟨member, rfl⟩
  rw [selected.source] at path contains
  have finalPath := StructuralSubstitution.descends_of_applyParameters path
  obtain ⟨finalized, finalizedContains, finalSame⟩ :=
    StructuralSubstitution.containsNode_of_applyParameters contains
  rw [selected.body.resources.source_eq] at finalPath finalizedContains
  have rawPath := FlexibleSubstitution.descends_of_applySubstitution finalPath
  obtain ⟨raw, rawContains, rawSame⟩ :=
    FlexibleSubstitution.containsNode_of_applySubstitution finalizedContains
  have unique : NodeOccurrencesUnique (evidenceSource selected) := by
    have result := selected.body.resources.graph_closed.wellFormed.nodeOccurrencesUnique
    rw [selected.body.resources.source_eq] at result
    simpa only [NodeOccurrencesUnique, FlexibleSubstitution.applyTypedSource_nodeOccurrenceIds] using result
  obtain ⟨earlier, earlierMember, shape⟩ :=
    SourceInferenceSoundness.NodeShapesPreserved.node_inverse preserved closed present unique
      rawContains.1 (.inr (by simpa only [rawContains.2] using rawPath))
  refine ⟨earlier, earlierMember, raw, shape, ?_⟩
  rw [rawSame]
  exact finalSame

/-- Coercion metadata does not affect the local target recovered at the
initializer checkpoint. -/
theorem local_lambda_descendant_read_before_shape (selected : BodySelection compiled row fuel)
    {before : TypedSource} {initializer : ExpressionId}
    {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (preserved : NodeShapesPreserved before.nodes (evidenceSource selected).nodes)
    (beforeClosed : ChildEdgesExist before)
    (present : NodeId.expression initializer ∈ nodeIds before)
    (member : Node.expression read ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression initializer) (.expression read.id))
    (form : read.form = .reference name (.local binder)) :
    ∃ earlier : ExpressionNode, Node.expression earlier ∈ before.nodes ∧
      earlier.id = read.id ∧ earlier.form = .reference name (.local binder) := by
  obtain ⟨earlier, earlierMember, raw, shape, same⟩ :=
    selected.local_lambda_descendant_node_before_shape preserved beforeClosed present member path
  have mapped : Node.expression read ∈
      (SourceSpecialization.applyTypedSource row.parameterSubstitution
        (({owner := before.owner, inputs := [], roots := [], nodes := [raw]} : TypedSource).applySubstitution selected.body.finalized.substitution)).nodes :=
    List.mem_map.mpr ⟨raw.applySubstitution selected.body.finalized.substitution,
      List.mem_map.mpr ⟨raw, List.mem_singleton_self _, rfl⟩, same⟩
  obtain ⟨finalized, finalMember, finalId, finalForm, _, _⟩ :=
    SourceCompiledLocalReadOrigins.specialized_local_read_original mapped form
  obtain ⟨original, originalMember, originalId, originalForm, _, _⟩ :=
    SourceCompiledLocalReadOrigins.solved_local_read_original finalMember finalForm
  have rawEq : Node.expression original = raw := List.mem_singleton.mp originalMember
  rw [← rawEq] at shape
  cases earlier with
  | statement _ => cases shape
  | expression earlier =>
    exact ⟨earlier, earlierMember, shape.1.trans (originalId.trans finalId),
      shape.2.trans originalForm⟩


/-- Actual retained reads need only their canonical path from the initializer;
no membership in a separately collected lexical-body table is required. -/
theorem local_lambda_descendant_read_binder_lt
    {raw : Workspace.RawWorkspace}
    (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin row.function.typedBody localInstance)
    {read : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (member : Node.expression read ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody
      (.expression localInstance.binding.initializer) (.expression read.id))
    (form : read.form = .reference name (.local binder)) :
    binder.binderIndex < localInstance.binding.binder.id.binderIndex := by
  obtain ⟨rawBinder, same, actual⟩ := selected.local_lambda_actual_origin origin.binding_member
  generalize initializerEq : localInstance.binding.initializer = initializer at actual
  have actualPath := path
  rw [initializerEq] at actualPath
  cases actual with
  | statement receipt here =>
      have graph := selected.statement_initializer_graph receipt here
      have step := ChildStep.statement_initializer here.accepted receipt.form rfl
        (annotation_expected receipt.annotationAccepted) receipt.child
      have shapes := selected.actualCall_final_nodeShapes (.child here step)
      obtain ⟨earlier, earlierMember, _, earlierForm⟩ :=
        selected.local_lambda_descendant_read_before_shape
          (before := receipt.ready.toTypedSource []) shapes graph.1
          (graph.2 (List.mem_singleton_self _)) member actualPath form
      have before := selected.statement_initializer_read_cutoff checked receipt here
        earlier earlierMember name binder earlierForm
      rw [← same]
      exact before
  | header receipt here =>
      have graph := selected.header_initializer_graph receipt here
      have step := ChildStep.forItem_initializer here.accepted receipt.form
        (annotation_expected receipt.annotationAccepted) receipt.child
      have shapes := selected.actualCall_final_nodeShapes (.child here step)
      obtain ⟨earlier, earlierMember, _, earlierForm⟩ :=
        selected.local_lambda_descendant_read_before_shape
          (before := receipt.ready.toTypedSource []) shapes graph.1
          (graph.2 (List.mem_singleton_self _)) member actualPath form
      have before := selected.header_initializer_read_cutoff checked receipt here
        earlier earlierMember name binder earlierForm
      rw [← same]
      exact before

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalLexicalAllocation
/-! Initialized owners inside a discovered lexical body were recorded before
its enclosing declaration. The actual ready graph retains their full binder
record, and the same local allocator bounds their stable identities. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceSpecializationWorklist SourceInferenceExecution
open SourceCompiledGeneralizedSoundness
open LocalGeneralizationBoundaries
namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat}

/-- Invert any canonical descendant of the initializer, including paths into
nested lambda bodies that the direct lexical collector intentionally skips. -/
private theorem node_before_shape (selected : BodySelection compiled row fuel)
    {before : TypedSource} {initializer : ExpressionId} {node : Node}
    (preserved : NodeShapesPreserved before.nodes (evidenceSource selected).nodes)
    (closed : ChildEdgesExist before)
    (present : NodeId.expression initializer ∈ nodeIds before)
    (member : node ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression initializer) node.id) :
    ∃ earlier ∈ before.nodes, ∃ raw : Node, SameNodeShape earlier raw ∧
      SourceSpecialization.applyNode row.parameterSubstitution
        (raw.applySubstitution selected.body.finalized.substitution) = node := by
  have contains : ContainsNode row.function.typedBody node.id node := ⟨member, rfl⟩
  rw [selected.source] at path contains
  have finalPath := StructuralSubstitution.descends_of_applyParameters path
  obtain ⟨finalized, finalizedContains, finalSame⟩ :=
    StructuralSubstitution.containsNode_of_applyParameters contains
  rw [selected.body.resources.source_eq] at finalPath finalizedContains
  have rawPath := FlexibleSubstitution.descends_of_applySubstitution finalPath
  obtain ⟨raw, rawContains, rawSame⟩ :=
    FlexibleSubstitution.containsNode_of_applySubstitution finalizedContains
  have unique : NodeOccurrencesUnique (evidenceSource selected) := by
    have result := selected.body.resources.graph_closed.wellFormed.nodeOccurrencesUnique
    rw [selected.body.resources.source_eq] at result
    simpa only [NodeOccurrencesUnique, FlexibleSubstitution.applyTypedSource_nodeOccurrenceIds] using result
  obtain ⟨earlier, earlierMember, shape⟩ :=
    SourceInferenceSoundness.NodeShapesPreserved.node_inverse preserved closed present unique
      rawContains.1 (.inr (by simpa only [rawContains.2] using rawPath))
  refine ⟨earlier, earlierMember, raw, shape, ?_⟩
  rw [rawSame]
  exact finalSame

/-- The complete raw initialized binding is recovered at the earlier table;
only node syntax, rather than expression typing metadata, must be preserved. -/
theorem local_lambda_initialized_before_shape (selected : BodySelection compiled row fuel)
    {before : TypedSource} {initializer : ExpressionId} {node : Node}
    {nested : InitializedLetBinding}
    (preserved : NodeShapesPreserved before.nodes (evidenceSource selected).nodes)
    (closed : ChildEdgesExist before)
    (present : NodeId.expression initializer ∈ nodeIds before)
    (nodeMember : node ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression initializer) node.id)
    (member : nested ∈ initializedLetBindings {row.function.typedBody with nodes := [node]}) :
    ∃ original ∈ initializedLetBindings before,
      StructuralSubstitution.applyInitializedLetBinding row.parameterSubstitution
        (FlexibleSubstitution.applyInitializedLetBinding selected.body.finalized.substitution original) = nested := by
  have localMember := member
  simp only [initializedLetBindings, List.flatMap_singleton] at localMember
  obtain ⟨earlier, earlierMember, rawNode, shape, same⟩ :=
    node_before_shape selected preserved closed present nodeMember path
  have singleton : nested ∈ initializedLetBindings
      (SourceSpecialization.applyTypedSource row.parameterSubstitution
        (({before with nodes := [rawNode]} : TypedSource).applySubstitution selected.body.finalized.substitution)) := by
    simpa only [SourceSpecialization.applyTypedSource, TypedSource.applySubstitution,
      List.map_singleton, initializedLetBindings, List.flatMap_singleton, same] using localMember
  change nested ∈ initializedLetBindings
    (StructuralSubstitution.applyTypedSource row.parameterSubstitution
      (({before with nodes := [rawNode]} : TypedSource).applySubstitution
        selected.body.finalized.substitution)) at singleton
  rw [StructuralSubstitution.initializedLetBindings_applyTypedSource,
    FlexibleSubstitution.initializedLetBindings_applySubstitution] at singleton
  obtain ⟨finalized, finalMember, finalSame⟩ := List.mem_map.mp singleton
  obtain ⟨original, originalMember, originalSame⟩ := List.mem_map.mp finalMember
  refine ⟨original, ?_, ?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨earlier, earlierMember, ?_⟩
    cases earlier with
    | expression expression =>
      cases rawNode with
      | expression rawExpression => cases originalMember
      | statement rawStatement => cases shape
    | statement statement =>
      cases rawNode with
      | expression rawExpression => cases shape
      | statement rawStatement =>
        change original ∈ statementInitializedLetBindings statement.form
        rw [shape.2]
        simpa only [initializedLetBindings, List.flatMap_singleton] using originalMember
  · rw [originalSame]
    exact finalSame

private theorem local_lambda_initialized_le (selected : BodySelection compiled row fuel)
    {state : State} {initializer : ExpressionId} {node : Node}
    {nested : InitializedLetBinding}
    (preserved : NodeShapesPreserved state.nodes (evidenceSource selected).nodes)
    (closed : ChildEdgesExist (state.toTypedSource []))
    (present : NodeId.expression initializer ∈ nodeIds (state.toTypedSource []))
    (allocated : InitializedBindersAllocated state)
    (nodeMember : node ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression initializer) node.id)
    (member : nested ∈ initializedLetBindings {row.function.typedBody with nodes := [node]}) :
    nested.binder.id.binderIndex ≤ state.nextLocal := by
  obtain ⟨original, originalMember, same⟩ := selected.local_lambda_initialized_before_shape
    preserved closed present nodeMember path member
  have bound := initialized_binding_allocated allocated originalMember
  have idEq := congrArg (fun binding : InitializedLetBinding => binding.binder.id.binderIndex) same
  change original.binder.id.binderIndex = nested.binder.id.binderIndex at idEq
  exact idEq ▸ bound

/-- Both forms of initialized declaration use their exact actual ready state. -/
theorem local_lambda_initialized_binder_le
    {raw : Workspace.RawWorkspace} (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin row.function.typedBody localInstance)
    {node : Node} {nested : InitializedLetBinding}
    (nodeMember : node ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression localInstance.binding.initializer) node.id)
    (member : nested ∈ initializedLetBindings {row.function.typedBody with nodes := [node]}) :
    nested.binder.id.binderIndex ≤ localInstance.binding.binder.id.binderIndex := by
  obtain ⟨rawBinder, same, actual⟩ := selected.local_lambda_actual_origin origin.binding_member
  generalize initializerEq : localInstance.binding.initializer = initializer at actual
  have actualPath := path
  rw [initializerEq] at actualPath
  cases actual with
  | statement receipt here =>
    have graph := selected.statement_initializer_graph receipt here
    have step := ChildStep.statement_initializer here.accepted receipt.form rfl
      (annotation_expected receipt.annotationAccepted) receipt.child
    have bound := selected.local_lambda_initialized_le
      (selected.actualCall_final_nodeShapes (.child here step)) graph.1
      (graph.2 (List.mem_singleton_self _))
      (selected.statement_initializer_allocated checked receipt here) nodeMember actualPath member
    rw [← same]
    exact bound
  | header receipt here =>
    have graph := selected.header_initializer_graph receipt here
    have step := ChildStep.forItem_initializer here.accepted receipt.form
      (annotation_expected receipt.annotationAccepted) receipt.child
    have bound := selected.local_lambda_initialized_le
      (selected.actualCall_final_nodeShapes (.child here step)) graph.1
      (graph.2 (List.mem_singleton_self _))
      (selected.header_initializer_allocated checked receipt here) nodeMember actualPath member
    rw [← same]
    exact bound

private theorem item_ids (item : ForItemForm) :
    List.Sublist ((forItemInitializedLetBindings item).map fun binding => binding.binder.id)
      (forItemDefinedLocalIds item) := by
  cases item <;> try exact .refl _
  rename_i binder initializer
  cases initializer <;> simp [forItemInitializedLetBindings, forItemDefinedLocalIds]

private theorem flatMap_sublist {α β : Type} (values : List α) (f g : α → List β)
    (each : ∀ value, List.Sublist (f value) (g value)) : List.Sublist (values.flatMap f) (values.flatMap g) := by
  induction values with
  | nil => exact .refl _
  | cons head rest ih => exact (each head).append ih

private theorem form_ids (form : StatementForm) :
    List.Sublist ((statementInitializedLetBindings form).map fun binding => binding.binder.id)
      (statementDefinedLocalIds form) := by
  cases form <;> try exact List.nil_sublist _
  case letDecl binder initializer =>
    cases initializer <;> simp [statementInitializedLetBindings, statementDefinedLocalIds]
  case forLoop initial condition post body =>
    simp only [statementInitializedLetBindings, statementDefinedLocalIds, List.map_append, List.map_flatMap]
    exact (flatMap_sublist initial _ _ item_ids).append (flatMap_sublist post _ _ item_ids)

private theorem initialized_defined {source : TypedSource} {binding : InitializedLetBinding}
    (member : binding ∈ initializedLetBindings source) : binding.binder.id ∈ definedLocalIds source := by
  obtain ⟨node, present, bound⟩ := List.mem_flatMap.mp member
  cases node with
  | expression _ => cases bound
  | statement statement =>
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨.statement statement, present, ?_⟩
    exact (form_ids statement.form).subset (List.mem_map.mpr ⟨binding, bound, rfl⟩)

/-- A distinct initialized owner in the actual lexical body precedes its
containing declaration. Its owner declaration is derived from source identity
ownership, so different full IDs cannot hide equal local allocator indices. -/
theorem local_lambda_initialized_binder_lt
    {raw : Workspace.RawWorkspace} (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin row.function.typedBody localInstance)
    {node : Node} {nested : InitializedLetBinding}
    (nodeMember : node ∈ row.function.typedBody.nodes)
    (path : Descends row.function.typedBody (.expression localInstance.binding.initializer) node.id)
    (member : nested ∈ initializedLetBindings {row.function.typedBody with nodes := [node]})
    (different : nested.binder.id ≠ localInstance.binding.binder.id) :
    nested.binder.id.binderIndex < localInstance.binding.binder.id.binderIndex := by
  have bound := selected.local_lambda_initialized_binder_le checked origin nodeMember path member
  have ownership : LocalIdentityOwnership row.function.typedBody := by
    rw [selected.source]
    exact StructuralSubstitution.LocalIdentityOwnership.applyParameters row.parameterSubstitution
      selected.body.resources.local_identity_ownership
  have nestedGlobal : nested ∈ initializedLetBindings row.function.typedBody := by
    apply List.mem_flatMap.mpr
    refine ⟨node, nodeMember, ?_⟩
    simpa only [initializedLetBindings, List.flatMap_singleton] using member
  obtain ⟨statement, statementMember, statementForm⟩ :=
    localLambdaBindings_statement_origin origin.binding_member
  have targetGlobal : (⟨localInstance.binding.binder,
      .expression localInstance.binding.initializer⟩ : InitializedLetBinding) ∈
      initializedLetBindings row.function.typedBody := by
    apply List.mem_flatMap.mpr
    refine ⟨.statement statement, statementMember, ?_⟩
    change _ ∈ statementInitializedLetBindings statement.form
    rw [statementForm]
    exact List.mem_singleton_self _
  have owners := (ownership.owned _ (initialized_defined nestedGlobal)).trans
    (ownership.owned _ (initialized_defined targetGlobal)).symm
  have indices : nested.binder.id.binderIndex ≠ localInstance.binding.binder.id.binderIndex := by
    intro equal
    apply different
    have eta (id : Resolved.LocalId) : id = ⟨id.owner, id.binderIndex⟩ := by cases id; rfl
    calc
      nested.binder.id = ⟨nested.binder.id.owner, nested.binder.id.binderIndex⟩ := eta _
      _ = ⟨localInstance.binding.binder.id.owner, localInstance.binding.binder.id.binderIndex⟩ := by rw [owners, equal]
      _ = localInstance.binding.binder.id := (eta _).symm
  omega

theorem local_lambda_direct_initialized_binder_lt
    {raw : Workspace.RawWorkspace} (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin row.function.typedBody localInstance)
    {nodes : List Node} {nested : InitializedLetBinding}
    (accepted : localLambdaBodyNodes row.function.typedBody localInstance = .ok nodes)
    (member : nested ∈ initializedLetBindings {row.function.typedBody with nodes := nodes})
    (different : nested.binder.id ≠ localInstance.binding.binder.id) :
    nested.binder.id.binderIndex < localInstance.binding.binder.id.binderIndex := by
  obtain ⟨node, nodeMember, binding⟩ := List.mem_flatMap.mp member
  have graph : OccurrenceGraphClosed row.function.typedBody := by
    rw [selected.source]
    exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters
      row.parameterSubstitution selected.body.resources.graph_closed
  have path := CoreLowering.GeneralizedLocalLexicalSubtree.body_node_descends
    graph.wellFormed.nodeOccurrencesUnique graph.wellFormed.childEdgesExist accepted nodeMember
  apply selected.local_lambda_initialized_binder_lt checked origin
    (localLambdaBodyNodes_members accepted nodeMember) path ?_ different
  simpa only [initializedLetBindings, List.flatMap_singleton] using binding

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledLocalReadAllocatorBounds
/-! The actual body entry and exact issuing lookup determine each local
reference's stable-identity bound. This is not a bound at an unrelated later
initializer checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceCompiledGeneralizedSoundness
open SourceInferenceExecution
namespace BodySelection
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {raw : Workspace.RawWorkspace}

theorem actualCall_localBound (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {call : CallIndex} (here : selected.InferenceCall call) :
    call.initial.LocalBindersBelowNextLocal :=
  ActualLocalAllocator.occurrence_bound (selected.inferenceCall_inputs checked)
    (State.initial_localBindersBelowNextLocal _ _ _) here

/-- The full binder returned by this real lookup was already allocated on
entry to the issuing expression call. -/
theorem specialized_local_read_bound (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {node : ExpressionNode} (member : .expression node ∈ row.function.typedBody.nodes)
    {name : String} {binder : Resolved.LocalId} (form : node.form = .reference name (.local binder)) :
    ∃ lookup : LocalReadEvents.Lookup,
      node.id = lookup.id ∧ node.form = .reference lookup.name.value (.local lookup.binder.id) ∧
      selected.InferenceCall (ActualLocalRead.lookupCall lookup) ∧
      lookup.binder ∈ lookup.initial.localBinders ∧
      binder = lookup.binder.id ∧ binder.binderIndex < lookup.initial.nextLocal := by
  obtain ⟨lookup, sameId, sameForm, here, present⟩ := selected.specialized_local_read_active member form
  have sameBinder : binder = lookup.binder.id := by
    have same := form.symm.trans sameForm
    exact ReferenceResolution.local.inj (ExpressionForm.reference.inj same).2
  refine ⟨lookup, sameId, sameForm, here, present, sameBinder, ?_⟩
  rw [sameBinder]
  exact selected.actualCall_localBound checked here lookup.binder present

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end
