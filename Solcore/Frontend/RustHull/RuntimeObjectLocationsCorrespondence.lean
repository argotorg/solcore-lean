import Solcore.Frontend.RustHull.RuntimeObjectInitializationCorrespondence
import Solcore.Frontend.RustHull.RuntimeAllocationLocations

/-! Shared and callback allocations preserve concrete cell separation for public execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

theorem objectRuntime_evaluates_separated {depth : Nat} {environment : Core.Environment}
    {initial : Core.Store} (observes : Core.Value → Core.Store → Prop)
    {slots : List (String × Core.Ty)} {compiled : Core.Expr} {others : List Core.Expr}
    {images : List (Nat × List UInt8)} {codeBytes : Option (List UInt8)}
    {catalog : List AccountRuntime.CodeDefinition} {context : Code}
    {functionsValue initialValues : List Core.Value}
    (captured : CapturedClosures environment (compiled :: others) functionsValue)
    (inputs : CodeValues depth environment ((AccountRuntime.sharedInitializers context).map (·.2.2)) initialValues)
    (continued : ∀ functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation,
      CodeValue (depth + extra.length) (extra ++ environment) functions (bundleValues functionsValue) →
      RuntimeReferences (depth + extra.length) (extra ++ environment) shared cells →
      InitializedCells cells allocated →
      CellLocations cells →
      cells.map (fun cell => (cell.name, cell.type, cell.value)) =
        (((AccountRuntime.sharedInitializers context).zip initialValues).map
          (fun (entry, value) => (entry.1, entry.2.1, value))).reverse →
      StoreRetains initial allocated →
      CodeValue (depth + extra.length) (extra ++ environment) dispatcher
        (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation) →
      CodeValue (depth + extra.length) (extra ++ environment) creator
        (.cellRef (Core.OptionalCell.cellType Creation.callbackType) creatorLocation) →
      (∃ value, allocated.read? creatorLocation = some value) →
      (∀ cell ∈ cells, cell.location < creatorLocation) →
      ∃ result final, Core.Evaluates (extra ++ environment) allocated
        (AccountRuntime.objectFrame slots (others.length + 1) images codeBytes context functions shared dispatcher creator
          (depth + extra.length)) result final ∧ observes result final) :
    ∃ result final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime slots compiled others images codeBytes catalog context depth) result final ∧ observes result final := by
  have packetEvaluated := captured.evaluates initial
  have bundleEvaluated : Core.Evaluates environment initial
      (packet ((compiled :: others).map constant) depth) (bundleValues functionsValue) initial := by
    simpa [packet, constant, Function.comp_def] using packetEvaluated
  let functions : Code := fun here => .var (here - depth - 1)
  have functionsRelated := CodeValue.bound depth environment (bundleValues functionsValue)
  have sharedInputs := inputs.prepend [bundleValues functionsValue]
  obtain ⟨sharedExtra, suffix, shared, cells, references, initialized, separate, description, sharedEvaluated⟩ :=
    allocateSharedSlots_separates sharedInputs
      (references := []) (cells := []) ⟨rfl, .nil⟩ (by intro cell member; cases member) CellLocations.nil
  obtain ⟨dispatcher, creator, callbackExtra, allocated, _, callbacksRetained, dispatcherRelated, creatorRelated, creatorRead, callbacksEvaluated⟩ :=
    allocateCallbacks_initializes (depth := depth + 1 + sharedExtra.length)
      (environment := sharedExtra ++ bundleValues functionsValue :: environment) (initial := initial ++ suffix)
      (fun dispatcher creator => objectHandlers_lambdas slots (others.length + 1) images catalog functions shared dispatcher creator)
  have allRetained : StoreRetains initial allocated := (StoreRetains.append initial suffix).trans callbacksRetained
  have functionsFinal := (functionsRelated.prepend sharedExtra).prepend callbackExtra
  have referencesFinal := references.prepend callbackExtra
  have initializedFinal := initialized.retained callbacksRetained
  have descriptionFinal : cells.map (fun cell => (cell.name, cell.type, cell.value)) =
      (((AccountRuntime.sharedInitializers context).zip initialValues).map
        (fun (entry, value) => (entry.1, entry.2.1, value))).reverse := by
    simpa only [List.map_nil, List.append_nil] using description
  obtain ⟨result, final, completed, observed⟩ := continued functions shared dispatcher creator
    (callbackExtra ++ sharedExtra ++ [bundleValues functionsValue]) allocated cells
    (initial ++ suffix).length ((initial ++ suffix).length + 1)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using functionsFinal)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using referencesFinal)
    initializedFinal separate descriptionFinal allRetained
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dispatcherRelated)
    (by simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using creatorRelated) creatorRead
    (fun cell member => Nat.lt_trans (initialized.location_bound member) (Nat.lt_succ_self _))
  refine ⟨result, final, Core.Evaluates.letE bundleEvaluated ?_, observed⟩
  apply sharedEvaluated
  apply callbacksEvaluated
  simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completed

end Solcore.Frontend.RustHull.Correspondence
