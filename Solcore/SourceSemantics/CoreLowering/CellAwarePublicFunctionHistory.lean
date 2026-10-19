import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputCollection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicOutputSelections
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicIssuedHistoryEntries
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory

/-! Finite histories retain function exports through later completed calls.
Every new state is the returned pool of an actual semantic result, and every
new function is the corresponding public export. Captured references keep their
identity while later calls supply the current heap contents and native world. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicFunctionHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedPublicFunctionHistory (Addition Entry IssuedEntry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
  (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (receiving : SourceCoreRawMetadata.Registry)
  (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))

abbrev Caller (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) :=
  State headers keys ⟨[], mapping, world, heap, store,
    SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩

variable {headers keys functions cells receiving anchor}

abbrev Result {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (owner : OwnedKey keys) (caller : Caller headers keys mapping world heap store)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (capture : NamedCapture headers owner.key header mapping world) (arguments : List Core.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) (native : Core.Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) (faults : RecursiveStageMeaning.FaultRep) :=
  CellAwarePublicApplicationResult.NamedResultAt
    (registry := receiving) functions cells owner caller header capture arguments
    anchor.function.context outcome after native finalStore finalMap finalWorld faults

variable {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {owner : OwnedKey keys} {caller : Caller headers keys mapping world heap store}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}

inductive History (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
    (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
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
      (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached)
      (addition : Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel header.function.resultType header.output outcome native added) :
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached added
  | next {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
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
      (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached)
      (addition : Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel header.function.resultType header.output outcome native added) :
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ added)
  | first_export_error {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store}
      {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
      {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
      {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
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
      (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
      (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached) :
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached []
  | next_export_error {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
      {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
      {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
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
      (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
      (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached) :
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries
  | first_failed {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store}
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
      (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached)
      (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached []
  | failed {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
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
      (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached)
      (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries
  | packed_next {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
      {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
      {sourceType : TypeSystem.Ty} {nativeType : Core.Ty} {added : List Entry}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      (started : checkpoint.HandleStart session handle argument inputFuel)
      (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
      (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
        anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context sourceType outcome reached)
      (addition : Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel sourceType nativeType outcome native added) :
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ added)
  | packed_failed {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
      {argument : SourceCorePublicValues.Value} {inputFuel executionFuel : Nat}
      {returned : Session artifact} {reason : Core.Word}
      {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      (started : checkpoint.HandleStart session handle argument inputFuel)
      (failed : checkpoint.FailedResultAt executionFuel native finalStore reason returned)
      (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
        anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context sourceType outcome reached)
      (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries
  | packed_export_error {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
      {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
      {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      (started : checkpoint.HandleStart session handle argument inputFuel)
      (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
      (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
        anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context sourceType outcome reached) :
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries
  | issued {session next : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      (continued : session.IssuanceChain next) :
      History headers keys functions cells receiving anchor next mapping world heap store caller entries
  | remember_issued {session next : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry} {entry : Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      (receipt : IssuedEntry headers keys functions receiving anchor session next entry) :
      History headers keys functions cells receiving anchor next mapping world heap store caller (entries ++ [entry])
  | restored {session next : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      (restored : session.RestoredAt next) :
      History headers keys functions cells receiving anchor next mapping world heap store caller entries

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
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (reached : Caller headers keys finalMap finalWorld after finalStore)
    (post : Relates caller reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
        CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
        header.function.resultType outcome reached) :
    completion.session.NativeAt finalWorld finalStore ∧
    GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
    StableRows reached ∧ Dynamic.HeapWellTyped anchor.function.context after := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨_source, _outcome, _represented, heaps, worldEq, _returned, _related, _stable, typed, _valueTyped⟩ :=
    CellAwarePublicApplicationResult.named_returned_value result decoded
  exact ⟨worldEq.symm ▸ succeeded.native_at.2, heaps, post.2.rows, typed⟩

private theorem current_export_error_result {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
    (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (reached : Caller headers keys finalMap finalWorld after finalStore)
    (post : Relates caller reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
        CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
        header.function.resultType outcome reached) :
    returned.NativeAt finalWorld finalStore ∧
    GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
    StableRows reached ∧ Dynamic.HeapWellTyped anchor.function.context after := by
  obtain ⟨payload, decoded⟩ := exported.succeeded
  obtain ⟨_source, _outcome, _represented, heaps, worldEq, _returned, _related, _stable, typed, _valueTyped⟩ :=
    CellAwarePublicApplicationResult.named_returned_value result decoded
  exact ⟨worldEq.symm ▸ exported.native_at, heaps, post.2.rows, typed⟩

private theorem addition_entries {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {completion : Completion artifact} {added : List Entry}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (addition : Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel header.function.resultType header.output outcome native added) :
    EntriesAt (functions := functions) (receiving := receiving) (anchor := anchor)
      completion.session finalMap finalWorld after added := by
  cases addition with
  | skip => intro entry member; cases member
  | @remember source payload handle requested sourceValue nativeValue handleValue =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
      rw [handleValue] at imported
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.named_returned_value result decoded
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
        CellAwarePublicApplicationResult.named_returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
      exact RecursiveNamedPublicOutputSelections.Selected.current selection represented valueTyped encodedAt rfl payloadAt selected


  | @selectCompatible source payload entries expected requested compatible sourceValue nativeValue selection selected =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.named_returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
      exact RecursiveNamedPublicOutputSelections.Selected.current selection represented valueTyped encodedAt compatible payloadAt selected

  | @selectNestedCompatible source payload entries expected requested compatible sourceValue nativeValue selection selected =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.named_returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      exact selected.current represented valueTyped

private theorem packed_addition_entries {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {completion : Completion artifact} {added : List Entry}
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
    (addition : Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel sourceType nativeType outcome native added) :
    EntriesAt (functions := functions) (receiving := receiving) (anchor := anchor)
      completion.session finalMap finalWorld after added := by
  cases addition with
  | skip => intro entry member; cases member
  | @remember source payload handle requested sourceValue nativeValue handleValue =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
      rw [handleValue] at imported
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.returned_value result decoded
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
        CellAwarePublicApplicationResult.returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
      exact RecursiveNamedPublicOutputSelections.Selected.current selection represented valueTyped encodedAt rfl payloadAt selected
  | @selectCompatible source payload entries expected requested compatible sourceValue nativeValue selection selected =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
      exact RecursiveNamedPublicOutputSelections.Selected.current selection represented valueTyped encodedAt compatible payloadAt selected

  | @selectNestedCompatible source payload entries expected requested compatible sourceValue nativeValue selection selected =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      exact selected.current represented valueTyped

/-- Every retained handle is represented at the current actual caller. This
projection derives all entry laws by induction over genuine successful calls. -/
theorem History.current {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries) :
    session.NativeAt world store ∧
    GenericHeap.CellHeapRepresents cells mapping world heap store ∧
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
  | first_export_error sameCompiled started selected exported result reached post =>
      have actual := current_export_error_result exported result reached post
      exact ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2, by intro entry member; cases member⟩
  | next_export_error prior sameCompiled started selected exported result reached post ih =>
      have actual := current_export_error_result exported result reached post
      refine ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2, ?_⟩
      intro entry member
      obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry member
      exact ⟨exported.encodes_function_from started.original.initial_registry imported,
        represented.extend (.refl _) result.2.2.2.1 result.2.2.2.2.1,
        typed.mono result.2.2.2.2.2.2.1⟩
  | first_failed sameCompiled started selected failed result reached post heapTyped =>
      have heaps := result.2.2.1
      have nativeAt : _ := heaps.runtime_hasTypes.world_eq.symm ▸ failed.native_at
      exact ⟨nativeAt, heaps, post.2.rows, heapTyped, by intro entry member; cases member⟩
  | failed prior sameCompiled started selected failed result reached post heapTyped ih =>
      have heaps := result.2.2.1
      have nativeAt : _ := heaps.runtime_hasTypes.world_eq.symm ▸ failed.native_at
      refine ⟨nativeAt, heaps, post.2.rows, heapTyped, ?_⟩
      intro entry member
      obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry member
      exact ⟨failed.encodes_function started.original imported,
        represented.extend (.refl _) result.2.2.2.1 result.2.2.2.2.1,
        typed.mono result.2.2.2.2.2.2.1⟩
  | packed_next prior started succeeded result reached post addition ih =>
      obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
      obtain ⟨_source, _outcome, _represented, heaps, worldEq, _returned, _related, _stable, typed, _valueTyped⟩ :=
        CellAwarePublicApplicationResult.returned_value result decoded
      refine ⟨worldEq.symm ▸ succeeded.native_at.2, heaps, post.2.rows, typed, ?_⟩
      intro entry member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨imported, represented, valueTyped⟩ := ih.2.2.2.2 entry old
        exact ⟨succeeded.encodes_function_from started.initial_registry imported,
          represented.extend (.refl _) result.2.2.1 result.2.2.2.1,
          valueTyped.mono result.2.2.2.2.2.1⟩
      · exact packed_addition_entries succeeded result addition entry added
  | packed_failed prior started failed result reached post heapTyped ih =>
      have heaps := result.2.1
      have nativeAt : _ := heaps.runtime_hasTypes.world_eq.symm ▸ failed.native_at
      refine ⟨nativeAt, heaps, post.2.rows, heapTyped, ?_⟩
      intro entry member
      obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry member
      exact ⟨failed.encodes_function_from started.initial_registry imported,
        represented.extend (.refl _) result.2.2.1 result.2.2.2.1,
        typed.mono result.2.2.2.2.2.1⟩
  | packed_export_error prior started exported result reached post ih =>
      obtain ⟨payload, decoded⟩ := exported.succeeded
      obtain ⟨_source, _outcome, _represented, heaps, worldEq, _returned, _related, _stable, typed, _valueTyped⟩ :=
        CellAwarePublicApplicationResult.returned_value result decoded
      refine ⟨worldEq.symm ▸ exported.native_at, heaps, post.2.rows, typed, ?_⟩
      intro entry member
      obtain ⟨imported, represented, valueTyped⟩ := ih.2.2.2.2 entry member
      exact ⟨exported.encodes_function_from started.initial_registry imported,
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
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (started : checkpoint.HandleStart session handle argument inputFuel)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2
  refine ⟨reached, related, ?_⟩
  simpa only [List.append_nil] using History.packed_next history started succeeded result reached ⟨related, post⟩ Addition.skip

/-- Selected direct output functions join the existing history at the same
returned caller. The public request may erase annotations from the semantic
result; the real reimport is related by runtime type compatibility. -/
theorem History.collect_packed_success
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
    {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
    {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
    {sourceType expected : TypeSystem.Ty} {nativeType : Core.Ty}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (started : checkpoint.HandleStart session handle argument inputFuel)
    (requested : checkpoint.ResultTypeAt expected)
    (compatible : SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType expected)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
    (selection : RecursiveNamedPublicOutputSelections.Selection sourceType completion.value) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore)
      (source : Dynamic.Value) (payload : Core.Value) (added : List Entry),
      outcome = .value source ∧ native = .inRight .word payload ∧
      RecursiveNamedPublicOutputSelections.Selected selection source payload nativeType outputFuel added ∧
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ added) := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  have nativeValue : native = .inRight .word payload := by
    have represented := result.1
    cases represented with
    | value represented =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
        subst payload
        rfl
    | fault represented => cases decoded
  obtain ⟨source, sourceValue, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
    CellAwarePublicApplicationResult.returned_value result decoded
  obtain ⟨_sourceType, encoded, encodedAt, payloadAt⟩ := succeeded.reimports_payload requested decoded
  obtain ⟨added, selected, handles, _meanings⟩ := selection.collect represented valueTyped encodedAt compatible payloadAt
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2
  exact ⟨reached, source, payload, added, sourceValue, nativeValue, selected, handles, related,
    .packed_next history started succeeded result reached ⟨related, post⟩
      (.selectCompatible requested compatible sourceValue nativeValue selection selected)⟩

/-- Constructor payloads and ordered mapping rows may export further functions.
Their real raw encoder and the current receiver metadata determine the exact
leaf identities before they join the existing history. -/
theorem History.collect_packed_nested_success
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {recipe : Recipe} (sameCompiled : recipe.compiled = compiled)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
    {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
    {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
    {sourceType expected : TypeSystem.Ty} {nativeType : Core.Ty}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (started : checkpoint.HandleStart session handle argument inputFuel)
    (requested : checkpoint.ResultTypeAt expected)
    (compatible : SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType expected)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
    {actualRegistry : SourceCoreRawMetadata.Registry}
    (atRegistry : completion.session.RegistryAt actualRegistry)
    (extension : SourceCoreRawMetadata.Extends receiving actualRegistry)
    (selection : RecursiveNamedPublicNestedOutputSelections.Selection sourceType completion.value) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore)
      (source : Dynamic.Value) (payload : Core.Value) (added : List Entry),
      outcome = .value source ∧ native = .inRight .word payload ∧
      RecursiveNamedPublicNestedOutputSelections.Selected compiled.compatible.checked completion.session
        selection source payload nativeType outputFuel added ∧
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ added) := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  have nativeValue : native = .inRight .word payload := by
    have represented := result.1
    cases represented with
    | value represented =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
        subst payload
        rfl
    | fault represented => cases decoded
  obtain ⟨source, sourceValue, represented, _heaps, _world, _returned, _related, _stable, _typed, _valueTyped⟩ :=
    CellAwarePublicApplicationResult.returned_value result decoded
  obtain ⟨_sourceType, encoded, encodedAt, payloadAt⟩ := succeeded.reimports_payload requested decoded
  have before := atRegistry.symm ▸ extension
  obtain ⟨added, selected, handles⟩ := selection.collect atRecipe
    (congrArg (fun compiled => compiled.compatible.checked) sameCompiled).symm represented
    encodedAt compatible payloadAt before
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2
  exact ⟨reached, source, payload, added, sourceValue, nativeValue, selected, handles, related,
    .packed_next history started succeeded result reached ⟨related, post⟩
      (.selectNestedCompatible requested compatible sourceValue nativeValue selection selected)⟩

/-- A failed direct invocation keeps all earlier handles at its returned heap.
The public semantic consumer derives heap typing from the Source fault trace. -/
theorem History.after_packed_failure
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
    {argument : SourceCorePublicValues.Value} {inputFuel executionFuel : Nat}
    {returned : Session artifact} {reason : Core.Word}
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (started : checkpoint.HandleStart session handle argument inputFuel)
    (failed : checkpoint.FailedResultAt executionFuel native finalStore reason returned)
    (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
    (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2
  exact ⟨reached, related, .packed_failed history started failed result reached ⟨related, post⟩ heapTyped⟩

/-- A successful native call whose public export failed still retains all
previous handles and the same successful Source after-heap. -/
theorem History.after_packed_export_error
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
    {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat} {generation : ExportGeneration}
    {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (started : checkpoint.HandleStart session handle argument inputFuel)
    (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
    (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2
  exact ⟨reached, related, .packed_export_error history started exported result reached ⟨related, post⟩⟩

private theorem success_shape {payload : Core.Value}
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
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
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached [] := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, related, .first sameCompiled started selected succeeded result reached ⟨related, post⟩ .skip⟩

/-- An intervening success retains all earlier handles, including when its
own public result is ordinary data. -/
theorem History.after_success
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  refine ⟨reached, related, ?_⟩
  simpa only [List.append_nil] using History.next history sameCompiled started selected succeeded result
    reached ⟨related, post⟩ Addition.skip

/-- An initial successful native call establishes the current Source state
even when the public output cannot be exported. -/
theorem first_export_error
    {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached [] := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, related, .first_export_error sameCompiled started selected exported result reached ⟨related, post⟩⟩

/-- A following named export error preserves the prior ordered handles at
the successful Source after-heap without registering an output handle. -/
theorem History.after_export_error
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, related, .next_export_error history sameCompiled started selected exported result reached ⟨related, post⟩⟩

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
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    {handle : SourceCorePublicValues.Handle} (handleValue : completion.value = .function handle) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore)
      (source : Dynamic.Value) (payload : Core.Value),
      outcome = .value source ∧ native = .inRight .word payload ∧ Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
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
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    {handle : SourceCorePublicValues.Handle} (handleValue : completion.value = .function handle) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore)
      (source : Dynamic.Value) (payload : Core.Value),
      outcome = .value source ∧ native = .inRight .word payload ∧ Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
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
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType completion.value) :
    ∃ added : List Entry, added.map Entry.handle = selection.handles ∧
      Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel header.function.resultType header.output outcome native added := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨source, sourceValue, nativeValue⟩ := success_shape result decoded
  obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
  obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
    CellAwarePublicApplicationResult.named_returned_value result decoded
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
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType completion.value) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached added := by
  obtain ⟨added, handles, addition⟩ := collected_addition requested succeeded result selection
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, added, handles, related,
    .first sameCompiled started selected succeeded result reached ⟨related, post⟩ addition⟩

/-- Collecting a product result appends all selected function leaves while
retaining earlier closures at the actual returned heap and session. -/
theorem History.collect_success
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType completion.value) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ added) := by
  obtain ⟨added, handles, addition⟩ := collected_addition requested succeeded result selection
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, added, handles, related,
    .next history sameCompiled started selected succeeded result reached ⟨related, post⟩ addition⟩

/-- A first failed call establishes an empty retained history at its actual
returned state. The public bootstrap adapter derives final heap typing. -/
theorem first_failure
    {returned : Session artifact} {reason : Core.Word}
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (failed : checkpoint.FailedResultAt executionFuel native finalStore reason returned)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached [] := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, related, .first_failed sameCompiled started selected failed result
    reached ⟨related, post⟩ heapTyped⟩

/-- A failed call retains earlier functions once Source heap preservation is
proved for its actual fault trace. Public adapters derive that condition. -/
theorem History.after_failure
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    {returned : Session artifact} {reason : Core.Word}
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (failed : checkpoint.FailedResultAt executionFuel native finalStore reason returned)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, related, .failed history sameCompiled started selected failed result
    reached ⟨related, post⟩ heapTyped⟩

end Success

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicFunctionHistory
