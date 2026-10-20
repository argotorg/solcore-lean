import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalApplicationMeaning
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedProvenance
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeApplicationBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport

/-! The scoped call port is discharged from the actual materialized compiler,
Source closure frame and issued public diagnostics. No body execution law is
supplied by its consumer. The reached caller retains the restored owned pool. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open GeneralizedLocalMaterializedAssociation
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {named : SourceCoreGeneralFunctions.Function}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  {invocation : Staging.Recursive.Scope}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "receivedFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "base" => CallableIndexedOwnedBodyRestorationAdmission.bridge

private theorem post_at {index : ProtectedStateTransition.Index} {type : TypeSystem.Ty}
    {outcome : Staging.Recursive.Outcome} (returned : callerProtocol.State index)
    (pool : State headers keys index) (same : bridge.pool returned = pool)
    (post : PostAdmission base context type outcome pool) :
    PostAdmission bridge context type outcome returned := by
  cases outcome with
  | value value => exact ⟨same ▸ post.rows, post.successful⟩
  | fault failure => cases failure with
    | semantic reason => exact ⟨same ▸ post.rows, post.successful⟩
    | stage _ _ _ =>
      change CallableIndexedOwnedIndirectExpressionHeads.StableRows (bridge.pool returned)
      rw [same]
      exact post

include receiver extension runtime selectedBodies in
/-- The original graded Source call determines both actual execution and its
public result, with no new runtime or body assumptions. -/
theorem preserves_selected (size : Nat) :
    CellAwareScopeApplicationBounds.PreservesAt bridge context model named stages invocation receivedFaults size := by
  intro scope mapping world environment canonical before store function native bindings parameter result sources values
    association raw frame arguments heaps initial admitted _authority _physical owner _ownerFrame atFrame outcome after trace
  cases association with
  | viewed material view _typed =>
    obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
    obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, represented, finalHeaps, maps, worlds,
        preserved, metadata, effect, pool, related, post⟩ :=
      GeneralizedLocalApplicationMeaning.preserves (faults := receivedFaults) material view inputs functions extension owner (bridge.pool initial)
        atFrame frame raw admitted.rows runtime (selectedBodies) (material.body_uninitialized receiver)
        (fun _ _ proof => proof) arguments heaps trace
    obtain ⟨returned, samePool, returnedRelated⟩ := bridge.restore initial pool maps worlds preserved metadata related
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
      preserved, metadata, effect, returned, returnedRelated, post_at bridge returned pool samePool post⟩

include receiver extension runtime selectedBodies in
/-- Native completion selects the real child scope and reconstructs its
original Source call, retaining exactly the same returned caller. -/
theorem reflects_selected (size : Nat) :
    CellAwareScopeApplicationBounds.ReflectsAt bridge context model named stages invocation receivedFaults size := by
  intro scope mapping world environment canonical before store function native bindings parameter result sources values
    association raw frame arguments heaps initial admitted _authority _physical owner _ownerFrame atFrame value finalStore completed
  cases association with
  | viewed material view _typed =>
    obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
    obtain ⟨sidecar, _accepted, selected⟩ := material.scope_at
    obtain ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, represented, finalHeaps, maps, worlds,
        preserved, metadata, effect, pool, related, post⟩ :=
      GeneralizedLocalApplicationMeaning.reflects (faults := receivedFaults) (registry := stages) material view inputs functions extension owner (bridge.pool initial)
        atFrame frame raw admitted.rows runtime (selectedBodies) (material.body_uninitialized receiver)
        (fun _ _ proof => proof) arguments heaps (.anonymous selected) completed.sound
    obtain ⟨returned, samePool, returnedRelated⟩ := bridge.restore initial pool maps worlds preserved metadata related
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
      preserved, metadata, effect, returned, returnedRelated, post_at bridge returned pool samePool post⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include receiver extension runtime wellFormed in
theorem preserves (size : Nat) :
    CellAwareScopeApplicationBounds.PreservesAt bridge context model named stages invocation receivedFaults size := by
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed)  <;> assumption

include receiver extension runtime wellFormed in
theorem reflects (size : Nat) :
    CellAwareScopeApplicationBounds.ReflectsAt bridge context model named stages invocation receivedFaults size := by
  apply reflects_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed)  <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedApplicationBounds
