import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialReceiver
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialArguments
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarStep

/-! A genuine first scalar completion establishes an empty retained-handle
history and the exact Source outcome, heap and physical store. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataScalarStep
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicScalarResults (ScalarOutput)
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
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem first_scalar
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (scalar : ScalarOutput) (call : Call session key publicArguments options)
    (returned : call.completion.value = scalar.publicValue)
    (start : Started rows prepared header call.toStartedCall)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (rawType : header.function.resultType = scalar.sourceType)
    (nativeType : header.output = scalar.nativeType)
    (descriptor : SourceCoreCallableContracts.Descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ after : State rows anchor initial support.profile recipe call.completion.session [],
      SourceCall anchor header invocation ⟨[]⟩ arguments (.value scalar.source) after.heap := by
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
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.public_run_succeeded_reflects
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
      call.started start.atCheckpoint call.executed descriptor
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first rfl start.started start.selected succeeded result
    reached ⟨related, post⟩ .skip
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result physicalCaller.physical result
  have atRecipe : start.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact atRecipe => by cases artifact; exact atRecipe
    exact convert _ start.started.recipe_eq
  have requested := start.started.original.result_type_at atRecipe start.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result start.selected).2
  rw [resultType, rawType] at requested
  have represented := result.2.1
  rw [nativeType] at represented
  have outcomeValue := scalar.source_value succeeded requested (valueEq.symm.trans returned) represented
  have returnedRegistry := start.started.returned_registry succeeded
  rw [← receiverRegistry] at returnedRegistry
  let next : State rows anchor initial support.profile recipe call.completion.session [] := {
    artifact := start.artifact, session := actual.session, mapping := finalMap, world := finalWorld,
    heap := after, store := finalStore, caller := reached, atSession := returnedAt,
    atRecipe := start.started.recipe_eq, receiving := receiving, issued := receiverIssued,
    extension := receiverExtension, registry := returnedRegistry, history := ⟨retained, physicalRetained⟩ }
  exact ⟨next, rawD, function, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialDataScalarStep
