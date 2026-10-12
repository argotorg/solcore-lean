import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicOutputSelections
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicIssuedHistoryEntries
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
import Solcore.SourceSemantics.CoreLowering.RecursivePublicApplicationResult

/-! Finite histories retain function exports through later completed calls.
Every new state is the returned pool of an actual semantic result, and every
new function is the corresponding public export. Captured references keep their
identity while later calls supply the current heap contents and native world. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
  (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (receiving : SourceCoreRawMetadata.Registry)
  (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))

abbrev Caller (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) :=
  State headers keys ⟨[], mapping, world, heap, store,
    SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩

variable {headers keys functions receiving anchor}

abbrev Result {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (owner : OwnedKey keys) (caller : Caller headers keys mapping world heap store)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (capture : NamedCapture headers owner.key header mapping world) (arguments : List Core.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) (native : Core.Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) (faults : RecursiveStageMeaning.FaultRep) :=
  CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
    (registry := receiving) (payloads := arguments) functions owner caller header capture
    anchor.function.context outcome after native finalStore finalMap finalWorld faults

variable {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {owner : OwnedKey keys} {caller : Caller headers keys mapping world heap store}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}

/-- Remembering a result is an observation of this actual export, not a
representation premise. Successful calls may also retain the history only. -/
inductive Addition {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (completion : Completion artifact) (fuel : Nat) (sourceType : TypeSystem.Ty) (nativeType : Core.Ty)
    (outcome : Staging.Recursive.Outcome) (native : Core.Value) : List Entry → Prop where
  | skip : Addition checkpoint completion fuel sourceType nativeType outcome native []
  | remember {source : Dynamic.Value} {payload : Core.Value} {handle : SourceCorePublicValues.Handle}
      (requested : checkpoint.ResultTypeAt sourceType)
      (sourceValue : outcome = .value source)
      (nativeValue : native = .inRight .word payload)
      (handleValue : completion.value = .function handle) :
      Addition checkpoint completion fuel sourceType nativeType outcome native
        [⟨sourceType, source, handle, payload, nativeType, fuel⟩]

  | select {source : Dynamic.Value} {payload : Core.Value} {entries : List Entry}
      (requested : checkpoint.ResultTypeAt sourceType)
      (sourceValue : outcome = .value source)
      (nativeValue : native = .inRight .word payload)
      (selection : RecursiveNamedPublicOutputSelections.Selection sourceType completion.value)
      (selected : RecursiveNamedPublicOutputSelections.Selected selection source payload nativeType fuel entries) :
      Addition checkpoint completion fuel sourceType nativeType outcome native entries

inductive History (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
    (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (receiving : SourceCoreRawMetadata.Registry)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram)) {artifact : Artifact} :
    (session : Session artifact) → (mapping : LocationMap) → (world : StoreTyping) →
    (heap : Dynamic.Heap) → (store : Store) → Caller headers keys mapping world heap store → List Entry → Prop where
  | first {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store}
      {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
      {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
      {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      {added : List Entry} {recipe : Recipe} {root : Root compiled}
      {encodedValues : SourceCoreCompatibleValues.Context}
      (sameCompiled : recipe.compiled = compiled)
      (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
        recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
      (selected : RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) headers root header)
      (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
      (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached)
      (addition : Addition checkpoint completion outputFuel header.function.resultType header.output outcome native added) :
      History headers keys functions receiving anchor completion.session finalMap finalWorld after finalStore
        reached added
  | next {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions receiving anchor session mapping world heap store caller entries)
      {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
      {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
      {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      {added : List Entry} {recipe : Recipe} {root : Root compiled}
      {encodedValues : SourceCoreCompatibleValues.Context}
      (sameCompiled : recipe.compiled = compiled)
      (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
        recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
      (selected : RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) headers root header)
      (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
      (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached)
      (addition : Addition checkpoint completion outputFuel header.function.resultType header.output outcome native added) :
      History headers keys functions receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ added)
  | failed {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions receiving anchor session mapping world heap store caller entries)
      {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
      {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
      {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel : Nat}
      {returned : Session artifact} {reason : Core.Word}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      {recipe : Recipe} {root : Root compiled}
      {encodedValues : SourceCoreCompatibleValues.Context}
      (sameCompiled : recipe.compiled = compiled)
      (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
        recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
      (selected : RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) headers root header)
      (failed : checkpoint.FailedResultAt executionFuel native finalStore reason returned)
      (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached)
      (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
      History headers keys functions receiving anchor returned finalMap finalWorld after finalStore
        reached entries
  | packed_next {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions receiving anchor session mapping world heap store caller entries)
      {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
      {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
      {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      (started : checkpoint.HandleStart session handle argument inputFuel)
      (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
      (result : RecursivePublicApplicationResult.ResultAt (registry := receiving) functions caller
        anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context sourceType outcome reached) :
      History headers keys functions receiving anchor completion.session finalMap finalWorld after finalStore
        reached entries
  | issued {session next : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions receiving anchor session mapping world heap store caller entries)
      (continued : session.IssuanceChain next) :
      History headers keys functions receiving anchor next mapping world heap store caller entries
  | remember_issued {session next : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry} {entry : Entry}
      (prior : History headers keys functions receiving anchor session mapping world heap store caller entries)
      (receipt : IssuedEntry headers keys functions receiving anchor session next entry) :
      History headers keys functions receiving anchor next mapping world heap store caller (entries ++ [entry])
  | restored {session next : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions receiving anchor session mapping world heap store caller entries)
      (restored : session.RestoredAt next) :
      History headers keys functions receiving anchor next mapping world heap store caller entries

def EntriesAt {artifact : Artifact} (session : Session artifact)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (entries : List Entry) : Prop :=
  ∀ entry ∈ entries,
    session.EncodesAt entry.fuel entry.sourceType (.function entry.handle) entry.native ∧
    ValueRep compiled.compatible.checked receiving functions mapping world
      entry.sourceType entry.source entry.native entry.nativeType ∧
    Dynamic.ValueHasType anchor.function.context heap entry.source entry.sourceType

private theorem current_result {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (reached : Caller headers keys finalMap finalWorld after finalStore)
    (post : Relates caller reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
        CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
        header.function.resultType outcome reached) :
    completion.session.NativeAt finalWorld finalStore ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
    StableRows reached ∧ Dynamic.HeapWellTyped anchor.function.context after := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨_source, _outcome, _represented, heaps, worldEq, _returned, _related, _stable, typed, _valueTyped⟩ :=
    RecursiveNamedPublicReturnedValues.returned_value result decoded
  exact ⟨worldEq.symm ▸ succeeded.native_at.2, heaps, post.2.rows, typed⟩

private theorem addition_entries {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {completion : Completion artifact} {added : List Entry}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (addition : Addition checkpoint completion outputFuel header.function.resultType header.output outcome native added) :
    EntriesAt (functions := functions) (receiving := receiving) (anchor := anchor)
      completion.session finalMap finalWorld after added := by
  cases addition with
  | skip => intro entry member; cases member
  | @remember source payload handle requested sourceValue nativeValue handleValue =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
      rw [handleValue] at imported
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        RecursiveNamedPublicReturnedValues.returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      intro entry member
      have sameEntry := List.mem_singleton.mp member
      subst entry
      exact ⟨imported, represented, valueTyped⟩

  | @select source payload entries requested sourceValue nativeValue selection selected =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        RecursiveNamedPublicReturnedValues.returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
      exact RecursiveNamedPublicOutputSelections.Selected.current selection represented valueTyped encodedAt rfl payloadAt selected

/-- Every retained handle is represented at the current actual caller. This
projection derives all entry laws by induction over genuine successful calls. -/
theorem History.current {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions receiving anchor session mapping world heap store caller entries) :
    session.NativeAt world store ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world heap store ∧
    StableRows caller ∧ Dynamic.HeapWellTyped anchor.function.context heap ∧
    EntriesAt (functions := functions) (receiving := receiving) (anchor := anchor) session mapping world heap entries := by
  induction history with
  | first sameCompiled started selected succeeded result reached post addition =>
      have actual := current_result succeeded result reached post
      exact ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2, addition_entries succeeded result addition⟩
  | next prior sameCompiled started selected succeeded result reached post addition ih =>
      have actual := current_result succeeded result reached post
      refine ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2, ?_⟩
      intro entry member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry old
        exact ⟨succeeded.encodes_function started.original imported,
          represented.extend (.refl _) result.2.2.2.1 result.2.2.2.2.1,
          typed.mono result.2.2.2.2.2.2.1⟩
      · exact addition_entries succeeded result addition entry added
  | failed prior sameCompiled started selected failed result reached post heapTyped ih =>
      have heaps := result.2.2.1
      have nativeAt : _ := heaps.runtime_hasTypes.world_eq.symm ▸ failed.native_at
      refine ⟨nativeAt, heaps, post.2.rows, heapTyped, ?_⟩
      intro entry member
      obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry member
      exact ⟨failed.encodes_function started.original imported,
        represented.extend (.refl _) result.2.2.2.1 result.2.2.2.2.1,
        typed.mono result.2.2.2.2.2.2.1⟩
  | packed_next prior started succeeded result reached post ih =>
      obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
      obtain ⟨_source, _outcome, _represented, heaps, worldEq, _returned, _related, _stable, typed, _valueTyped⟩ :=
        RecursivePublicApplicationResult.returned_value result decoded
      refine ⟨worldEq.symm ▸ succeeded.native_at.2, heaps, post.2.rows, typed, ?_⟩
      intro entry member
      obtain ⟨imported, represented, valueTyped⟩ := ih.2.2.2.2 entry member
      exact ⟨succeeded.encodes_function_from started.initial_registry imported,
        represented.extend (.refl _) result.2.2.1 result.2.2.2.1,
        valueTyped.mono result.2.2.2.2.2.1⟩
  | issued prior continued ih =>
      refine ⟨continued.same_runtime.native_at ih.1, ih.2.1, ih.2.2.1, ih.2.2.2.1, ?_⟩
      intro entry member
      obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry member
      exact ⟨continued.encodes_function imported, represented, typed⟩
  | @remember_issued session next mapping world heap store caller entries entry prior receipt ih =>
      obtain ⟨same, imported, represented, typed⟩ := receipt.current caller ih.1
      refine ⟨same.native_at ih.1, ih.2.1, ih.2.2.1, ih.2.2.2.1, ?_⟩
      intro entry member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨oldImported, oldRepresented, oldTyped⟩ := ih.2.2.2.2 entry old
        exact ⟨receipt.chain.encodes_function oldImported, oldRepresented, oldTyped⟩
      · have sameEntry := List.mem_singleton.mp added
        subst entry
        exact ⟨imported, represented, typed⟩
  | restored prior restored ih =>
      refine ⟨restored.same_runtime.native_at ih.1, ih.2.1, ih.2.2.1, ih.2.2.2.1, ?_⟩
      intro entry member
      obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry member
      exact ⟨restored.encodes_function imported, represented, typed⟩

/-- Direct invocation of a retained handle returns the same ordered history
at its actual new session, with captures interpreted in the resulting heap. -/
theorem History.after_packed_success
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
    {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
    {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    (history : History headers keys functions receiving anchor session mapping world heap store caller entries)
    (started : checkpoint.HandleStart session handle argument inputFuel)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : RecursivePublicApplicationResult.ResultAt (registry := receiving) functions caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions receiving anchor completion.session finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2
  exact ⟨reached, related, .packed_next history started succeeded result reached ⟨related, post⟩⟩

private theorem success_shape {payload : Core.Value}
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (decoded : LanguageResult.decode? native = some (.succeeded payload)) :
    ∃ source, outcome = .value source ∧ native = .inRight .word payload := by
  cases result.2.1 with
  | value represented =>
      simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
      subst payload
      exact ⟨_, rfl, rfl⟩
  | fault represented => cases decoded

section Success
variable {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
  {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
  {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
  {recipe : Recipe} {root : Root compiled} {encodedValues : SourceCoreCompatibleValues.Context}

/-- The first actual success establishes the current state before any exports
have been retained for later input. -/
theorem first_success
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions receiving anchor completion.session finalMap finalWorld after finalStore
        reached [] := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, related, .first sameCompiled started selected succeeded result reached ⟨related, post⟩ .skip⟩

/-- An intervening success retains all earlier handles, including when its
own public result is ordinary data. -/
theorem History.after_success
    (history : History headers keys functions receiving anchor session mapping world heap store caller entries)
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions receiving anchor completion.session finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  refine ⟨reached, related, ?_⟩
  simpa only [List.append_nil] using History.next history sameCompiled started selected succeeded result
    reached ⟨related, post⟩ Addition.skip

/-- The first retained function is selected from the actual successful Source
outcome and exported native payload. -/
theorem first_remembered
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    {handle : SourceCorePublicValues.Handle} (handleValue : completion.value = .function handle) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore)
      (source : Dynamic.Value) (payload : Core.Value),
      outcome = .value source ∧ native = .inRight .word payload ∧ Relates caller reached ∧
      History headers keys functions receiving anchor completion.session finalMap finalWorld after finalStore
        reached [⟨header.function.resultType, source, handle, payload, header.output, outputFuel⟩] := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨source, sourceValue, nativeValue⟩ := success_shape result decoded
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, source, payload, sourceValue, nativeValue, related,
    .first sameCompiled started selected succeeded result reached ⟨related, post⟩
      (.remember requested sourceValue nativeValue handleValue)⟩

/-- Each later export appends its exact Source/native pair to the complete
ordered collection. No earlier entry is dropped or replaced. -/
theorem History.remember_success
    (history : History headers keys functions receiving anchor session mapping world heap store caller entries)
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    {handle : SourceCorePublicValues.Handle} (handleValue : completion.value = .function handle) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore)
      (source : Dynamic.Value) (payload : Core.Value),
      outcome = .value source ∧ native = .inRight .word payload ∧ Relates caller reached ∧
      History headers keys functions receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ [⟨header.function.resultType, source, handle, payload, header.output, outputFuel⟩]) := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨source, sourceValue, nativeValue⟩ := success_shape result decoded
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, source, payload, sourceValue, nativeValue, related,
    .next history sameCompiled started selected succeeded result reached ⟨related, post⟩
      (.remember requested sourceValue nativeValue handleValue)⟩

private theorem collected_addition
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType completion.value) :
    ∃ added : List Entry, added.map Entry.handle = selection.handles ∧
      Addition checkpoint completion outputFuel header.function.resultType header.output outcome native added := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨source, sourceValue, nativeValue⟩ := success_shape result decoded
  obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
  obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
    RecursiveNamedPublicReturnedValues.returned_value result decoded
  have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
  subst actual
  obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
  obtain ⟨added, selected, handles, _meanings⟩ := selection.collect represented valueTyped encodedAt rfl payloadAt
  exact ⟨added, handles, .select requested sourceValue nativeValue selection selected⟩

/-- A first successful result can retain any selected function leaves inside
products. The original export supplies all leaf values and recursive budgets. -/
theorem first_collected
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType completion.value) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions receiving anchor completion.session finalMap finalWorld after finalStore
        reached added := by
  obtain ⟨added, handles, addition⟩ := collected_addition requested succeeded result selection
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, added, handles, related,
    .first sameCompiled started selected succeeded result reached ⟨related, post⟩ addition⟩

/-- Collecting a product result appends all selected function leaves while
retaining earlier closures at the actual returned heap and session. -/
theorem History.collect_success
    (history : History headers keys functions receiving anchor session mapping world heap store caller entries)
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType completion.value) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ added) := by
  obtain ⟨added, handles, addition⟩ := collected_addition requested succeeded result selection
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, added, handles, related,
    .next history sameCompiled started selected succeeded result reached ⟨related, post⟩ addition⟩

/-- A failed call retains earlier functions once Source heap preservation is
proved for its actual fault trace. Public adapters derive that condition. -/
theorem History.after_failure
    (history : History headers keys functions receiving anchor session mapping world heap store caller entries)
    {returned : Session artifact} {reason : Core.Word}
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (failed : checkpoint.FailedResultAt executionFuel native finalStore reason returned)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions receiving anchor returned finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, related, .failed history sameCompiled started selected failed result
    reached ⟨related, post⟩ heapTyped⟩

end Success

section Issuance
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory)

/-- A fresh named issuance joins the retained functions at the same current
caller. The native payload and Source meaning come from actual preparation,
issuance and the current pool, including after previous mutations. -/
theorem History.remember_named
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (Input compiled)) (rows : Inventory inputs)
    {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {caller : Caller (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled) mapping world heap store}
    {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (history : History (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled)
      (CallableIndexedOwnedContextualCellOrigins.functions
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled) bodyRegistry faults profile)
      registry anchor session mapping world heap store caller entries)
    {issued : Completion artifact} {issuanceFuel : Nat}
    (issuance : session.NamedIssuedAt packet.header.named.signature.key issuanceFuel issued)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    {handle : Handle} (handleValue : issued.value = .function handle)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ native, History (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled)
      (CallableIndexedOwnedContextualCellOrigins.functions
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled) bodyRegistry faults profile)
      registry anchor issued.session mapping world heap store caller
      (entries ++ [⟨packet.header.named.specialized.function.type,
        .global (CallableNamedReversal.global (CallableNamedMetadata.global
          packet.header.named.specialized input.prepared.available)), handle, native,
        CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType,
        issuanceFuel⟩]) := by
  obtain ⟨native, encoded, _represented, _typed⟩ :=
    RecursiveNamedPublicCurrentFactoryValues.Session.named_value_represents_current
      prepared inputs rows packet member bodyRegistry registry faults profile caller anchor
      issuance history.current.1 (.refl _) atRecipe handleValue wellFormed
  exact ⟨native, .remember_issued history (.named prepared inputs rows packet member
    bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded wellFormed)⟩

/-- Fresh builtin issuance appends its exact closed callable while all earlier
closures retain the same captured state and registry identities. -/
theorem History.remember_builtin
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {caller : Caller headers keys mapping world heap store}
    {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (history : History headers keys
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      registry anchor session mapping world heap store caller entries)
    {issued : Completion artifact} {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : session.BuiltinIssuedAt function issuanceFuel issued)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    {handle : Handle} (handleValue : issued.value = .function handle) :
    ∃ native, History headers keys
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      registry anchor issued.session mapping world heap store caller
      (entries ++ [⟨function.type, .builtin ⟨function⟩, handle, native,
        CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function),
        issuanceFuel⟩]) := by
  obtain ⟨native, _same, _type, encoded, _represented, _typed⟩ :=
    RecursiveNamedPublicBuiltinArgumentReceipts.Session.builtin_value_represents_after
      prepared headers keys bodyRegistry registry faults profile mapping anchor.function.context heap
      issuance (.refl _) atRecipe handleValue (world := world)
  exact ⟨native, .remember_issued history (.builtin prepared headers keys bodyRegistry registry faults profile
    anchor issuance atRecipe handleValue encoded)⟩
end Issuance

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
