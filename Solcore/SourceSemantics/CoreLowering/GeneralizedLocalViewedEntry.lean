import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOwnedBodyEntry
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalParameterAdmission
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntryEffects
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedCall
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls

/-! The actual outer wrapper installs its read-time view, then the real marked
parameter prefix enters the selected lambda. The public caller remains the
saved physical row, even when it differs from the read-time context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalViewedEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedOwnedFunctionState
open GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  (material : Materialization compiled mapping world function) (view : View material)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (atFrame : view.location = owner.key.frameLocation)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "instances" => GeneralizedLocalInstanceValues.model compiled.indexed
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances
local notation "temporaryStore" => store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame view.transient)

abbrev Entry := GeneralizedLocalBodyEntry.Entry (values := .initial compiled.compatible.checked)
  material.origin material.captured material.code inputs functions registry cells arguments nativeArguments before
  temporaryStore owner.key.frameLocation view.callerNative view.callerGhost view.caller view.id view.recipe

include atFrame in
/-- Actual view installation and parameter allocation construct the reached
owned state and descriptor-preserving effect, without a body execution premise. -/
theorem prepare
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world
      material.code.receipt.loweredParameters arguments nativeArguments)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller) :
    ∃ entry : Entry (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
      (before := before) (store := store) material view inputs functions owner,
    ∃ reached : State headers keys
      ⟨material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
      Relates caller reached ∧ CallableIndexedOwnedIndirectExpressionHeads.StableRows reached ∧
      CellAwareScopeAuthority.Effect instances mapping world before store
        entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store ∧
      (∀ {value bodyStore}, Evaluates entry.entry.actualBody entry.entry.store
        (material.code.receipt.body.rename entry.entry.embedding) value bodyStore →
        Evaluates [view.native, DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload
          value (bodyStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current))) ∧
      (∀ {value finalStore}, Evaluates [view.native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore →
        ∃ bodyStore, Evaluates entry.entry.actualBody entry.entry.store
          (material.code.receipt.body.rename entry.entry.embedding) value bodyStore ∧
          finalStore = bodyStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current)) := by
  let row := caller.rows owner.position
  have rowLocation : row.authority.frameLocation = owner.key.frameLocation := row.frame_eq
  have unmapped : owner.key.frameLocation ∉ mapping := by
    have absent := row.authority.unmapped
    simp only [rowLocation] at absent
    exact absent
  have reference : material.captured.canonical[material.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [← atFrame]
    exact view.lexicalReference
  have current : store.read? view.location = some
      (encode compiled.indexed.ancestry.layout.frame row.authority.current) := by
    rw [atFrame, ← rowLocation]
    exact row.authority.frame.read
  have reading := read_history view.carried view.recipe.read view.recipe.readAccepted
  let temporary := install caller owner.position reading
  have written : store.write? owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame view.transient) =
      some temporaryStore := Store.write?_eq_some_iff.mpr ⟨by
        have bound := (List.getElem?_eq_some_iff.mp current).1
        simpa only [atFrame] using bound, rfl⟩
  have referenceTyped : world[owner.key.frameLocation]? = some compiled.indexed.ancestry.layout.frame.type := by
    have typed := row.authority.typed
    simp only [rowLocation] at typed
    exact typed
  have installedHeaps := heaps.write_administrative
    (fun found => unmapped (List.mem_of_getElem? found)) referenceTyped
    (encode_runtime_typed world (CallableIndexedAmbient.frame_registered compiled.indexed) view.transient) written
  obtain ⟨entry, _added, _length, _spine, reached, related⟩ :=
    GeneralizedLocalOwnedBodyEntry.parameters_with_state material.origin material.captured material.code inputs functions
      GeneralizedLocalDescriptorHeap.ordinary_cells represented owner temporary view.carried view.recipe
      installedHeaps locals reference (Store.write?_reads_written written)
  have stableAway := GeneralizedLocalParameterAdmission.away_after_install caller owner.position stable reading
  have rows := GeneralizedLocalParameterAdmission.after_parameters temporary reached owner.position stableAway
    entry.nextHistory entry.entry.frame
  have effect := (CellAwareScopeAuthority.Effect.set_unmapped store
    (encode compiled.indexed.ancestry.layout.frame view.transient) unmapped).trans
    (GeneralizedLocalBodyEntry.Entry.scope_effect (values := .initial compiled.compatible.checked)
      (prepared := compiled.indexed) material.origin material.captured material.code inputs
      functions registry cells arguments nativeArguments before temporaryStore owner.key.frameLocation
      view.callerNative view.callerGhost view.caller view.id view.recipe entry instances)
  have outer := GeneralizedLocalReadView.agreement view.reference current
    (parameter := material.code.receipt.parameterCore) (result := material.code.receipt.resultCore)
    (id := view.id) (target := material.code.descriptor.id) (caller := view.callerNative)
    (identity := .inLeft .word .unit)
    (innerBody := material.code.body.rename material.captured.embedding.lift.lift)
    (innerEnvironment := encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual)
    (argument := DataPatternValues.packValues nativeArguments)
  refine ⟨entry, reached, (install_related caller owner.position reading).trans related, rows, effect, ?_, ?_⟩
  · intro value bodyStore evaluated
    have inner := entry.wrap evaluated
    change Evaluates (DataPatternValues.packValues nativeArguments ::
      encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual)
      temporaryStore (material.code.body.rename material.captured.embedding.lift.lift) value
      (bodyStore.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame view.transient)) at inner
    rw [← atFrame] at inner
    have applied := outer.1 inner
    have full : Evaluates [view.native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value
        ((bodyStore.set view.location (encode compiled.indexed.ancestry.layout.frame view.transient)).set view.location
          (encode compiled.indexed.ancestry.layout.frame row.authority.current)) :=
      .apply (.second (.first (.var rfl))) (.var rfl) applied
    simpa only [List.set_set, atFrame] using full
  · intro value finalStore evaluated
    cases evaluated with
    | apply callee argument applied =>
      have expected : Evaluates [view.native, DataPatternValues.packValues nativeArguments] store
          (.second (.first (.var 0)))
          (.closure material.code.receipt.parameterCore (LanguageResult.resultType material.code.receipt.resultCore)
            view.body (encode compiled.indexed.ancestry.layout.frame view.callerNative ::
              CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual :: view.environment))
          store := .second (.first (.var rfl))
      obtain ⟨sameClosure, sameStore⟩ := evaluation_deterministic callee expected
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj sameClosure
      rw [sameStore] at argument
      obtain ⟨sameArgument, sameAfter⟩ := evaluation_deterministic argument
        (show Evaluates [view.native, DataPatternValues.packValues nativeArguments] store (.var 1)
          (DataPatternValues.packValues nativeArguments) store from .var rfl)
      rw [sameArgument, sameAfter] at applied
      obtain ⟨innerStore, inner, restored⟩ := outer.2 applied
      rw [atFrame] at inner
      obtain ⟨bodyStore, body, innerEq⟩ := entry.unwrap inner
      refine ⟨bodyStore, body, ?_⟩
      simpa only [innerEq, atFrame, List.set_set] using restored

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalViewedEntry
