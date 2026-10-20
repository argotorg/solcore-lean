import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalApplicationMeaning
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedProvenance
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedArgumentRows
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport
import Solcore.SourceSemantics.CoreLowering.RecursivePublicPackedArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectClosureApplicationBounds

/-! A retained materialized handle uses its authentic owned frame at the current
public caller. Actual packed input typing supplies its Source argument row;
zero, singleton and multiple arguments keep the original packing convention. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedPackedApplication
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open GeneralizedLocalMaterializedAssociation
open CellAwarePublicApplicationResult (ResultAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled))
  (heapTyped : Dynamic.HeapWellTyped context before)
  {function : Dynamic.Closure} {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (member : Association compiled mapping world function native bindings parameterCore resultCore)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (atFrame : member.AtFrame owner.key.frameLocation)
  (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function parameter result))
  {packedSource : Dynamic.Value} {packedNative : Value}
  (packedTyped : Dynamic.ValueHasType context before packedSource parameter)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (packedRelated : ValueRep compiled.compatible.checked completion.result.context.registry functions
    mapping world parameter packedSource packedNative parameterCore)
  (heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
      (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)

include profile runtime heapTyped member calleeTyped packedTyped packedRelated in
private theorem arguments :
    ∃ sources values,
      Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      packedNative = DataPatternValues.packValues values ∧
      CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values ∧
      CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before sources ∧
      Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function := by
  obtain ⟨parameterEq, _resultEq, signatures, code, covers, _captures⟩ := calleeTyped.closure_function_inv
  have frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function :=
    ⟨signatures.trans runtime.signatures, code.owner, code, code.requirement_ledger.idsUnique, covers⟩
  have sourceBundle : parameter = TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) := by
    rw [member.source_binders]
    exact parameterEq
  have packed := packedRelated
  rw [sourceBundle, GeneralizedLocalMaterializedArgumentRows.parameter_core member frame profile] at packed
  obtain ⟨sources, values, packing, nativeEq, represented⟩ := RecursivePublicPackedArguments.arguments bindings
    (GeneralizedLocalMaterializedArgumentRows.projected_bindings member frame) packed
  have length : bindings.length = function.parameters.length := by
    simpa only [List.length_map] using congrArg List.length member.source_binders
  have arity := represented.length.1.symm.trans length
  have sourceTyped := packing.unpackTypes (parameterEq ▸ packedTyped) (by simpa only [List.length_map] using arity)
  have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime calleeTyped heapTyped
    sourceTyped packing parameterEq.symm arity
  exact ⟨sources, values, packing, arity, nativeEq, represented, raw, frame⟩

include profile receiver extension stable runtime selectedBodies heapTyped atFrame calleeTyped packedTyped packedRelated heaps in
/-- The original packed Source call constructs the actual handle payload
execution and returns the same mixed heap and restored caller pool. -/
theorem preserves {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    (arity : sources.length = function.parameters.length)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages size invocation context
      before (.closure function) sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨decoded, values, decodedPacking, decodedArity, nativeEq, represented, raw, frame⟩ :=
    arguments functions profile runtime heapTyped member calleeTyped packedTyped packedRelated
  have same : decoded = sources := decodedPacking.injective_of_length_eq packing (decodedArity.trans arity.symm)
  subst decoded
  have resultEq := calleeTyped.closure_function_inv.2.1
  subst result
  cases member with
  | viewed material view _typed =>
    obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
    obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, representedResult, finalHeaps,
        maps, worlds, preserved, metadata, _effect, returned, related, post⟩ :=
      GeneralizedLocalApplicationMeaning.preserves (faults := callFaults) material view inputs functions extension owner caller
        atFrame frame raw stable runtime selectedBodies (material.body_uninitialized receiver) (fun _ _ proof => proof)
        represented heaps trace
    obtain ⟨nativeSize, measured⟩ := evaluation_has_size evaluated
    have padded : EvaluationSize nativeSize (view.native :: packedNative :: tail) store
        CallableIndexedLambdaCalls.applyPayload value finalStore := by
      rw [nativeEq]
      exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail measured
    exact ⟨value, finalStore, finalMap, finalWorld, padded.sound, representedResult, finalHeaps,
      maps, worlds, preserved, metadata, returned, related, post⟩

include profile receiver extension stable runtime selectedBodies heapTyped atFrame calleeTyped packedTyped packedRelated heaps in
/-- Completion of the actual handle payload reconstructs its ordered Source
arguments and call, even when its lexical frame belongs to a different owner. -/
theorem reflects {invocation : Staging.Recursive.Scope} {tail : Environment}
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources,
      Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize invocation context
          before (.closure function) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions cells caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, values, packing, arity, nativeEq, represented, raw, frame⟩ :=
    arguments functions profile runtime heapTyped member calleeTyped packedTyped packedRelated
  have resultEq := calleeTyped.closure_function_inv.2.1
  subst result
  cases member with
  | viewed material view _typed =>
    obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
    obtain ⟨sidecar, _accepted, selected⟩ := material.scope_at
    have evaluation : EvaluationSize size [view.native, DataPatternValues.packValues values] store
        CallableIndexedLambdaCalls.applyPayload value finalStore := by
      rw [← nativeEq]
      exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail completed
    obtain ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, representedResult, finalHeaps,
        maps, worlds, preserved, metadata, _effect, returned, related, post⟩ :=
      GeneralizedLocalApplicationMeaning.reflects (faults := callFaults) (registry := callStages)
        material view inputs functions extension owner caller atFrame frame raw stable runtime selectedBodies
        (material.body_uninitialized receiver) (fun _ _ proof => proof) represented heaps (.anonymous selected) evaluation.sound
    exact ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace,
      representedResult, finalHeaps, maps, worlds, preserved, metadata, returned, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedPackedApplication
