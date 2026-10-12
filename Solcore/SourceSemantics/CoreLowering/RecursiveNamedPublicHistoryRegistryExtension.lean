import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning

/-! A real input encoder may extend the current metadata table. The entire
history moves to that table without changing its session, heap, captures or
ordered entries. No metadata can be recovered from a larger unrelated table. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryRegistryExtension
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open RecursiveNamedPublicFunctionHistory (History Entry Caller Result IssuedEntry)

private theorem outcome_extend
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient}
    {registry future : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Core.Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.Outcome} {native : Core.Value}
    (represented : RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world sourceType type faults outcome native)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked future functions) mapping world sourceType type faults outcome native := by
  cases represented with
  | value related => exact .value (related.extend extension (.refl _) (.refl _))
  | fault related => exact .fault related

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry future : SourceCoreRawMetadata.Registry}
  {anchor : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world heap store}

private theorem named_result
    {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world}
    {arguments : List Core.Value} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    {native : Core.Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    {faults : RecursiveStageMeaning.FaultRep}
    (result : Result (functions := functions) (receiving := registry) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    Result (functions := functions) (receiving := future) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults :=
  ⟨result.1, outcome_extend result.2.1 extension,
    CompatibleHeap.HeapRepresents.extend_registry result.2.2.1 extension, result.2.2.2⟩

private theorem packed_result
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    {native : Core.Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    {faults : RecursiveStageMeaning.FaultRep}
    (result : RecursivePublicApplicationResult.ResultAt (registry := registry) functions caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    RecursivePublicApplicationResult.ResultAt (registry := future) functions caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults :=
  ⟨outcome_extend result.1 extension,
    CompatibleHeap.HeapRepresents.extend_registry result.2.1 extension, result.2.2⟩

private theorem issued_entry {artifact : Artifact} {before after : Session artifact} {entry : Entry}
    (receipt : IssuedEntry headers keys functions registry anchor before after entry) :
    IssuedEntry headers keys functions future anchor before after entry := by
  cases receipt with
  | named prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded wellFormed =>
      exact .named prepared inputs rows packet member bodyRegistry future faults profile anchor
        issuance atRecipe handleValue encoded wellFormed
  | builtin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      exact .builtin prepared headers keys bodyRegistry future faults profile anchor issuance atRecipe handleValue encoded

/-- Only a forward extension of the actual metadata table is used. Every
historical result, including a failed call, keeps its original state and order. -/
theorem extend_history {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    History headers keys functions future anchor session mapping world heap store caller entries := by
  induction history with
  | first sameCompiled started selected succeeded result reached post addition =>
      exact .first sameCompiled started selected succeeded (named_result result extension) reached post addition
  | next prior sameCompiled started selected succeeded result reached post addition ih =>
      exact .next ih sameCompiled started selected succeeded (named_result result extension) reached post addition
  | first_failed sameCompiled started selected failed result reached post heapTyped =>
      exact .first_failed sameCompiled started selected failed (named_result result extension) reached post heapTyped
  | failed prior sameCompiled started selected failed result reached post heapTyped ih =>
      exact .failed ih sameCompiled started selected failed (named_result result extension) reached post heapTyped
  | packed_next prior started succeeded result reached post addition ih =>
      exact .packed_next ih started succeeded (packed_result result extension) reached post addition
  | packed_failed prior started failed result reached post heapTyped ih =>
      exact .packed_failed ih started failed (packed_result result extension) reached post heapTyped
  | packed_export_error prior started exported result reached post ih =>
      exact .packed_export_error ih started exported (packed_result result extension) reached post
  | issued prior continued ih => exact .issued ih continued
  | remember_issued prior receipt ih => exact .remember_issued ih (issued_entry receipt)
  | restored prior restored ih => exact .restored ih restored

/-- A history retains the genuine entry selected by its first named startup,
including when that call failed or later handles were restored. -/
theorem indexed_entry {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries) :
    ∃ entry, entry ∈ compiled.indexed.entries := by
  induction history with
  | first _ _ selected _ _ _ _ _ =>
      obtain ⟨_, entry, member, _⟩ := selected
      exact ⟨entry, member⟩
  | first_failed _ _ selected _ _ _ _ _ =>
      obtain ⟨_, entry, member, _⟩ := selected
      exact ⟨entry, member⟩
  | next _ _ _ _ _ _ _ _ _ ih => exact ih
  | failed _ _ _ _ _ _ _ _ _ ih => exact ih
  | packed_next _ _ _ _ _ _ _ ih => exact ih
  | packed_failed _ _ _ _ _ _ _ ih => exact ih
  | packed_export_error _ _ _ _ _ _ ih => exact ih
  | issued _ _ ih => exact ih
  | remember_issued _ _ ih => exact ih
  | restored _ _ ih => exact ih

/-- The first actual root fixes a retained named header even if its result
contains no function handle. Later session transitions preserve that origin. -/
theorem named_header {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries) :
    ∃ header, header ∈ headers := by
  induction history with
  | first _ _ selected _ _ _ _ _ => exact ⟨_, selected.1⟩
  | first_failed _ _ selected _ _ _ _ _ => exact ⟨_, selected.1⟩
  | next _ _ _ _ _ _ _ _ _ ih => exact ih
  | failed _ _ _ _ _ _ _ _ _ ih => exact ih
  | packed_next _ _ _ _ _ _ _ ih => exact ih
  | packed_failed _ _ _ _ _ _ _ ih => exact ih
  | packed_export_error _ _ _ _ _ _ ih => exact ih
  | issued _ _ ih => exact ih
  | remember_issued _ _ ih => exact ih
  | restored _ _ ih => exact ih

/-- The retained named row gives the genuine compiler diagnostic inventory.
No fallback entry or unrelated native execution is used. -/
theorem diagnostics_present {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries) :
    ∃ program, compiled.indexed.base.diagnostics = some program := by
  obtain ⟨header, _⟩ := named_header history
  obtain ⟨diagnostics, _, actual, _⟩ := NamedCalls.compiled_at compiled.indexed header.selected
  exact ⟨diagnostics, actual⟩

/-- The original accepted packed encoder supplies the extension. This keeps
history at the exact table used to decode this call's eventual public result. -/
theorem at_packed_start
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {recipe : Recipe}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    (started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt session handle argument inputFuel
      checkpoint recipe world store parameter result nativeParameter nativeResult callable packed encodedValues) :
    SourceCoreRawMetadata.Extends registry encodedValues.registry ∧
    History headers keys functions encodedValues.registry anchor session mapping world heap store caller entries := by
  obtain ⟨before, encoded, actualRegistry, _owner, _accepted, _value, sameRegistry⟩ := started.raw
  have same : before = registry := actualRegistry.symm.trans atRegistry
  have extended : SourceCoreRawMetadata.Extends registry encodedValues.registry := by
    rw [← same, ← sameRegistry]
    exact encoded.preserves
  exact ⟨extended, extend_history history extended⟩

/-- Named startup extends the same history using the complete actual ordered
input vector, including values that introduce constructor or mapping metadata. -/
theorem at_named_start
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {recipe : Recipe} {root : Root recipe.compiled}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    {inputFuel : Nat} {checkpoint : Checkpoint artifact} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key arguments inputFuel
      checkpoint recipe root world store native encodedValues) :
    SourceCoreRawMetadata.Extends registry encodedValues.registry ∧
    History headers keys functions encodedValues.registry anchor session mapping world heap store caller entries := by
  have extended := started.original.metadata_extension atRegistry
  have actual := started.values
  cases checkpoint
  change _ = encodedValues at actual
  dsimp only at extended
  rw [actual] at extended
  exact ⟨extended, extend_history history extended⟩

/-- Current handle identity and the actual packed encoder derive input meaning
in the very table used by public output decoding. Heap and capture meaning
come from the retained history, with no receiving-registry assumption. -/
theorem at_packed_input
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {recipe : Recipe} (sameCompiled : recipe.compiled = compiled)
    {entry : Entry} (member : entry ∈ entries)
    {sourceParameter sourceResult : TypeSystem.Ty}
    (entryType : entry.sourceType = .function sourceParameter sourceResult)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context sourceParameter argument source)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    (started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt session entry.handle argument inputFuel
      checkpoint recipe world store parameter result nativeParameter nativeResult callable packed encodedValues) :
    SourceCoreRawMetadata.Extends registry encodedValues.registry ∧
    History headers keys functions encodedValues.registry anchor session mapping world heap store caller entries ∧
    ValueRep compiled.compatible.checked encodedValues.registry functions mapping world
      sourceParameter source packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context heap source sourceParameter := by
  cases sameCompiled
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨parameterView, _resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨extended, current⟩ := at_packed_start history atRegistry started
  obtain ⟨represented, typed⟩ := started.history_input_compatible current input parameterView (.refl _)
  exact ⟨extended, current, represented, typed⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryRegistryExtension
