import Solcore.SourceSemantics.CoreLowering.CellAwareNamedParameterEntry
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCellAllocationProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalParameterAdmission
import Solcore.SourceSemantics.CoreLowering.NamedCallMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping

/-! The actual named hook installs its authenticated seed and allocates the real
parameters in the mixed heap. Its continuation restores the saved physical
caller, while retaining every body write and marked allocation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedOwnedAdmittedBodyEntries
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : CallableIndexedOwnedFunctionValues.Header compiled program)
  (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}

/-- Source facts, actual compiler fields and the reached authority suffice.
There is no premise concerning this named body's execution. -/
theorem prepare
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (sameGlobals : header.globals = compiled.indexed.base.globals.length)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      header.named.signature.key = .ok header.named.specialized)
    (wellFormed : ProgramWellFormed program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (stable : StableRows caller) :
    ∃ environment finalHeap finalCanonical finalActual finalContext finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment finalHeap ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        environment finalCanonical compiled.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld finalHeap finalStore ∧
      SourceReceipt program header.function header.context environment finalHeap ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext compiled.indexed.layouts.definitions ∧
      AdministrativePreserved mapping
        (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame compiled.indexed.ancestry.graph.table
            ((compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key)).getD Word.zero))))
        finalMap finalStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld finalHeap finalStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) header.named.signature.key []
        finalMap finalWorld finalHeap finalStore environment ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        Relates caller reached ∧ StableRows reached ∧
      ∃ physical : CellAwareScopePhysical.Physical compiled header.named header.context
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          finalCanonical finalMap finalWorld finalHeap finalStore environment,
        physical.location = owner.key.frameLocation ∧
      (∀ {value bodyStore}, Evaluates finalActual finalStore (header.body.rename finalEmbedding) value bodyStore →
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value
          (bodyStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current))) ∧
      (∀ {value bodyStore}, Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value bodyStore →
        ∃ reachedStore, Evaluates finalActual finalStore (header.body.rename finalEmbedding) value reachedStore ∧
          bodyStore = reachedStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current)) := by
  obtain ⟨_facts, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have empty : header.function.context.locals = [] := by
    rw [header.frame.context]
    exact certified.locals_empty
  have ownership : LocalIdentityOwnership header.function.source := by
    rw [header.frame.source]
    exact certified.local_identity_ownership
  let row := caller.rows owner.position
  have rowLocation : row.authority.frameLocation = owner.key.frameLocation := row.frame_eq
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [rowLocation] using row.authority.unmapped
  have current : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame row.authority.current) := by
    simpa only [rowLocation] using row.authority.frame.read
  obtain ⟨origin, index, selected, frame, emitted⟩ := CallableIndexedFormation.namedBody_receipt compiled.indexed.ancestry header.hook
  have history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named origin) (some (CallableIndexedNamedGeneration.state header.named)) := by
    rw [← frame]
    exact named_complete compiled.indexed.ancestry.graph (CallableIndexedNamedGeneration.seed compiled.indexed selected record)
  let installed := install caller owner.position (.stable history)
  have written : store.write? owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)) =
      some (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp current).1, rfl⟩
  have referenceTyped : world[owner.key.frameLocation]? = some compiled.indexed.ancestry.layout.frame.type := by
    simpa only [rowLocation] using row.authority.typed
  have installedHeaps := heaps.write_administrative
    (fun found => unmapped (List.mem_of_getElem? found)) referenceTyped
    (encode_runtime_typed world header.registered (.state index)) written
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) headers keys
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
  let initial : State headers keys ⟨[], mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), capture.canonical⟩ := installed
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer owner.key.frameLocation (.state index) := by
    intro index reached read
    exact CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position read history
  let actual := .unit :: encode compiled.indexed.ancestry.layout.frame row.authority.current ::
    DataPatternValues.packValues payloads :: capture.captured
  let embedding := Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift)
  have layout : EnvironmentsAgree embedding (DataPatternValues.packValues payloads :: capture.canonical) actual :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift capture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame row.authority.current)) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := compiled.indexed.layouts.definitions))
    (.cons (encode_runtime_typed world header.registered row.authority.current)
      (.cons (CallableIndexedParameters.Arguments.pack_typed represented) capture.typed))
  obtain ⟨environment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld, finalEmbedding,
      allocated, environments, finalHeaps, sourceReceipt, agrees, finalTyped, agreement, preserved,
      effect, lexical, reached, related, physical, locationEq, nativeEq⟩ :=
    CellAwareNamedParameterEntry.parameters header sameLayouts sameGlobals wellFormed empty ownership (.state index) origin selected history
      represented capture.environments installedHeaps heapTyped argumentsTyped layout actualTyped owner.key.frameLocation
      (by simpa only [sameGlobals] using capture.reference) (Store.write?_reads_written written) unmapped producer initial ready
  have finalStable := GeneralizedLocalParameterAdmission.after_parameters caller reached owner.position
    (fun i _ => stable i) history preserved
  have fullEffect := (CellAwareScopeAuthority.Effect.set_unmapped store
    (encode compiled.indexed.ancestry.layout.frame (.state index)) unmapped).trans effect
  have reference : (DataPatternValues.packValues payloads :: capture.captured)[capture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  have renamed : header.code.rename capture.embedding.lift = withFrame
      (.var (capture.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (header.parameterCode.rename capture.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have next : Evaluates (encode compiled.indexed.ancestry.layout.frame row.authority.current ::
      DataPatternValues.packValues payloads :: capture.captured) store
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) store := by
    rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
    exact CallableIndexedContextFrames.literal_evaluates _ _ _ _
  refine ⟨environment, finalHeap, finalCanonical, finalActual, _, finalStore, finalMap, finalWorld, finalEmbedding,
    allocated, environments, finalHeaps, sourceReceipt, agrees, finalTyped, ?_, fullEffect, lexical,
    reached, (install_related caller owner.position (.stable history)).trans related, finalStable,
    physical, locationEq, ?_, ?_⟩
  · simpa only [selected, Option.getD_some, frame] using preserved
  · intro value bodyStore evaluated
    have parameterRun := agreement.wrap evaluated
    simp only [embedding, GenericExpressionMeaning.rename_prefix] at parameterRun
    rw [renamed]
    exact CallableContextFrames.withFrame_evaluates (.var reference) current next parameterRun
  · intro value bodyStore evaluated
    rw [renamed] at evaluated
    obtain ⟨installedValue, nextStore, reachedStore, actualNext, parameterRun, restored⟩ :=
      CallableContextFrames.withFrame_reflects (.var reference) current evaluated
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic actualNext next
    refine ⟨reachedStore, agreement.unwrap ?_, restored⟩
    simpa only [embedding, GenericExpressionMeaning.rename_prefix] using parameterRun

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedEntry
