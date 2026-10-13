import Solcore.Test.SourceCoreRecursiveIndexSelection
import Solcore.Test.SourceCoreRecursiveIndexRuntime
import Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionSteps

/-! The original physical cache slot identifies each automatic catalog Header.
The original public observations retain their complete execution receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CertifiedPublicSession (EligibleRow Issued Initial)

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}

theorem selected_row (row : ObservedRow fixture signature) :
    ∃ selected : EligibleRow fixture.recipe.compiled row.row.key,
      selected.named.specialized = row.row := by
  obtain ⟨prepared⟩ := fixture.prepared row.member
  obtain ⟨_signatureEq, indexEq⟩ := row.prepared_slot prepared
  refine ⟨⟨prepared.named, row.index, row.global, indexEq ▸ prepared.selected,
    row.slot, row.globalKey, ?_⟩, prepared.same⟩
  rw [prepared.same]
  refine ⟨prepared.origin, ?_, row.ordinary, row.inputsOrdinary⟩
  simp only [row.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
    List.not_mem_nil, false_implies, implies_true]

theorem header_of_member (row : ObservedRow fixture signature)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (member : header ∈ headers rows)
    (specialized : header.named.specialized = row.row) :
    ∃ actual : ActualHeader fixture row.row, actual.header = header := by
  obtain ⟨input, packet, _retained, sameHeader⟩ := rows.mem_headers header member
  subst header
  have sameRow : input.row = row.row := input.prepared.same.symm.trans
    ((congrArg (·.specialized) packet.aligned.named.symm).trans specialized)
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation input.row =
      CallableNamedMetadata.instantiation input.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation,
      sameRow, row.parameters]
  let actual : ActualHeader fixture input.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
    header := packet.header
    aligned := by simpa only [metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  have transported : ∀ (left right : SourceSpecialization.SpecializedFunction)
      (same : left = right) (value : ActualHeader fixture left),
      (same ▸ value : ActualHeader fixture right).header = value.header := by
    intro left right same value
    cases same
    rfl
  exact ⟨sameRow ▸ actual, transported _ _ sameRow actual⟩

def firstCall {row : ObservedRow fixture signature} (first : ObservedPublicRun fixture row) :
    RecursiveNamedPublicPhysicalSessionState.FunctionCall first.session row.row.key [.word seed] runOptions :=
  ⟨⟨⟨first.checkpoint, first.started⟩, first.completion, first.executed⟩, first.handle, first.returned⟩

def functionCall {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key arguments) :
    RecursiveNamedPublicPhysicalSessionState.FunctionCall session key arguments runOptions :=
  ⟨⟨⟨call.checkpoint, call.started⟩, call.completion, call.executed⟩, call.handle, call.returned⟩

/-- The first successful export keeps the actual requested raw function type. -/
theorem initial_handle_type {issued : Issued fixture.recipe}
    {row : ObservedRow fixture signature} {first : ObservedPublicRun fixture row}
    (initial : Initial issued (firstCall first).toCall.toStartedCall) :
    first.handle.sourceType = initial.header.function.resultType := by
  obtain ⟨checkpoint, started, resumed⟩ := first.executed
  have same : checkpoint = first.checkpoint := Except.ok.inj (started.symm.trans first.started)
  subst checkpoint
  obtain ⟨_actual, _generation, _value, _store, _done, exported, valueEq, _typeEq, _budgetEq, _atSession⟩ :=
    resumed.indexed_succeeded initial.start.atCheckpoint
  have atRecipe : initial.start.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe → artifact.RecipeAt fixture.recipe :=
      fun artifact atRecipe => by cases artifact; exact atRecipe
    exact convert _ initial.start.started.recipe_eq
  have requested := initial.start.started.original.result_type_at atRecipe initial.start.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result initial.start.selected).2
  rw [resultType] at requested
  exact exported.function_source_type requested (valueEq.symm.trans first.returned)

end Tests.SourceCoreRecursiveIndex.CompilerProfile
