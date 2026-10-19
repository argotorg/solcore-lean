import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialReceiver
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicHistorySourceInputs
import Solcore.SourceSemantics.Staging.SelectedRecursivePreservation
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionFailureStep

/-! A completed initial failure reflects the original staged Source fault and
retains its exact physical state without any prior or fabricated handle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataFailureStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall Call State SourceCall)
open SelectedCompilationPublicSessionInitial (Started)
open SelectedCompilationPhysicalProgramSupport (Support stagePrepared)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} (rows : Inventory inputs)
  (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
  (anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (support : Support recipe.compiled (headers rows) (keys recipe.compiled) initial)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
    (Program.ofChecked recipe.compiled.sourceProgram)
    (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled))
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

include selectedBodies in
theorem first_failure
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (returned : SourceCoreExecution.Session publicArtifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (start : Started rows prepared header call)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (descriptor : SourceCoreCallableContracts.Descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : State rows anchor initial support.profile recipe returned [],
      SourceCall anchor header invocation ⟨[]⟩ arguments (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨receiving, contextAt, receiverIssued, receiverExtension⟩ :=
    SelectedCompilationPublicInitialReceiver.of_started support start
  have receiverRegistry := congrArg SourceCoreCompatibleValues.Context.registry contextAt
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry receiving.result.context.registry := by
    rw [receiverRegistry]
    exact .refl _
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts rows).receipts header start.selected.member
  obtain ⟨physicalCaller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct)
      (profile := support.profile) (completion := receiving)
      (bodyRegistry := initial.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      (bodyTyping := support.bodyTyping) (prepared := prepared) (selected := start.selected)
      (opened := start.opened) (fresh := start.fresh) (ready := start.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl session) (atSession := start.atSession)
      (started := start.started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor support.bodyTyping).2
  obtain ⟨actual, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, failed, returnedAt, trace, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.public_run_failed_reflects
      (stagePrepared := stagePrepared recipe.compiled) (completion := receiving)
      (functions := SelectedCompilationPhysicalProgramSupport.functions support)
      (packet := support.bodies header start.selected.member)
      (reflectsBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.reflects_bodies support receiverIssued receiverExtension
          header start.selected.member selected budget)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := physicalCaller.physical) (bodyTyping := support.bodyTyping)
      (selected := start.selected) (caller := physicalCaller.base.val)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := start.started) (invocation := invocation)
      call.started start.atCheckpoint failedCall descriptor
  obtain ⟨failure, outcomeEq⟩ : ∃ failure, outcome = .fault failure := by
    have represented := result.2.1
    cases represented with
    | value _ => have impossible := failed.2.1; cases impossible
    | fault _ => exact ⟨_, rfl⟩
  subst outcome
  have fault : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      receiving.result.diagnostics failure reason := by
    have represented := result.2.1
    cases represented with
    | fault matched =>
      have decoded := failed.2.1
      simp only [Core.LanguageResult.decode?] at decoded
      cases decoded
      exact matched
  have contexts := (SelectedCompilationPublicReturnedValues.header_context_supports
    header anchor support.bodyTyping).1
  have callerHeap := heapTyped.transportContext contexts
  have callerArguments := argumentsTyped.transportContext contexts
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.SelectedPreservation.applies_fault selectedBodies
    (SelectedCompilationPublicHistorySourceInputs.header_runtime support.bodyTyping anchor) callerHeap
    (SelectedCompilationPublicHistorySourceInputs.source_typed support.bodyTyping sourceAt anchor ⟨[]⟩)
    packing (packing.hasType callerArguments) trace
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first_failed rfl start.started start.selected
    failed result reached ⟨related, post⟩ preserved.1
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result physicalCaller.physical result
  have returnedRegistry : actual.RegistryAt receiving.result.context.registry := by
    have actualValues := failed.2.2.2.2.1.trans start.started.values
    exact (congrArg SourceCoreCompatibleValues.Context.registry actualValues).trans receiverRegistry.symm
  let next : State rows anchor initial support.profile recipe returned [] := {
    artifact := start.artifact
    session := actual
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := start.started.recipe_eq
    receiving := receiving
    issued := receiverIssued
    extension := receiverExtension
    registry := returnedRegistry
    history := ⟨retained, physicalRetained⟩ }
  exact ⟨failure, next, ⟨rawD, function, sourceSize, sourceAt, trace⟩, fault⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataFailureStep
