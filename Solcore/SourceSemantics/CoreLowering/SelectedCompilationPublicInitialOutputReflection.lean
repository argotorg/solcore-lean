import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedDirectForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialArguments
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionScalarStep

/-! Initial public success reflects to a complete Source value and heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialOutputReflection
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationStageClosedDirectForward.Output (ReturnedValue)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicPhysicalSessionState (StartedCall Call State SourceCall PlainValue)
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

theorem first_output
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : Call session key publicArguments options)
    (start : Started rows prepared header call.toStartedCall)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (descriptor : SourceCoreCallableContracts.Descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ source, ∃ after : State rows anchor initial support.profile recipe call.completion.session [],
      SourceCall anchor header invocation ⟨[]⟩ arguments (.value source) after.heap ∧
      PlainValue anchor header invocation ⟨[]⟩ arguments source after.heap ∧
      ReturnedValue call.completion after header.function.resultType source options.outputValidationFuel := by
  have startupRegistry := start.registry rows prepared header simple
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry initial.result.context.registry := by
    rw [startupRegistry, support.registry]
    exact .refl _
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts rows).receipts header start.selected.member
  obtain ⟨physicalCaller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct)
      (profile := support.profile) (completion := initial)
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
      (stagePrepared := stagePrepared recipe.compiled) (completion := initial)
      (functions := SelectedCompilationPhysicalProgramSupport.functions support)
      (packet := support.bodies header start.selected.member)
      (reflectsBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.reflects_bodies support support.issued (.refl _)
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
  rw [resultType] at requested
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨source, sourceValue, represented, _heaps, _world, _returned, _related, _stable, _typed, _valueTyped⟩ :=
    RecursiveNamedPublicReturnedValues.returned_value result decoded
  have returnedRegistry := start.started.returned_registry succeeded
  rw [startupRegistry, ← support.registry] at returnedRegistry
  let next : State rows anchor initial support.profile recipe call.completion.session [] := {
    artifact := start.artifact, session := actual.session, mapping := finalMap, world := finalWorld,
    heap := after, store := finalStore, caller := reached, atSession := returnedAt,
    atRecipe := start.started.recipe_eq, receiving := initial, issued := support.issued,
    extension := .refl _, registry := returnedRegistry, history := ⟨retained, physicalRetained⟩ }
  have lifted : SourceCall anchor header invocation ⟨[]⟩ arguments (.value source) next.heap :=
    ⟨rawD, function, sourceSize, sourceAt, sourceValue ▸ trace⟩
  have encoded := (succeeded.reimports_payload requested decoded).2
  rw [← valueEq] at encoded
  exact ⟨source, next, lifted, lifted.value_plain, header.function.resultType,
    payload, header.output, rfl, encoded, represented⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialOutputReflection
