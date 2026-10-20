import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyLeaves
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryContinuation

/-! Ordinary declaration prefixes compose actual marked allocation with the
rest of the lexical body. Restoring bindings keeps new Source and native cells
and every earlier captured generalized descriptor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeclarations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CellAwareLexicalBodyState

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : RecursiveStageMeaning.FaultRep}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

include definitions registered in
theorem absent {context nextContext scope mode id node binder rest expected type body payload}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (mono : binder.scheme.quantified = []) (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projected : checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (TypedLexicalControl.absentRequest invocation.source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (TypedLexicalControl.absentRequest invocation.source scope binder payload))
    (same : annotation.original = allocation.expression)
    (remaining : ∀ next : Entry functions rawRegistry instances program invocation frame globals
        nextContext ((binder.id,payload) :: scope), Nonempty (Result next registry faults mode rest expected type body)) :
    Nonempty (Result entry registry faults mode (id :: rest) expected type (.letE annotation.expression body)) := by
  let after : Dynamic.Heap := ⟨entry.heap.cells ++ [⟨binder.scheme.body,none,none⟩]⟩
  let location : Dynamic.Location := ⟨entry.heap.cells.length⟩
  have allocated : Dynamic.Heap.Allocates entry.heap binder.scheme.body none location after := .append
  obtain ⟨captured,evaluated,environments,heaps,locals,agrees,typed,reference,read,preserved,effect⟩ :=
    CellAwareOrdinaryBodyAllocation.absent GeneralizedLocalDescriptorHeap.ordinary_cells definitions registered
      mono extended ordinary projected allocation annotation same entry.environments entry.heaps entry.locals
      entry.agrees entry.actualTyped entry.reference entry.read allocated
  let next : Entry functions rawRegistry instances program invocation frame globals nextContext ((binder.id,payload) :: scope) := {
    mapping := entry.mapping ++ [entry.store.length + 2]
    world := entry.world ++ [frame.type,allocation.entry.layout.type,OptionalCell.cellType payload]
    administrative := entry.administrative
    actualContext := OptionalCell.referenceType payload :: entry.actualContext
    environment := (binder.id,location) :: entry.environment
    canonical := .cellRef (OptionalCell.cellType payload) (entry.store.length + 2) :: entry.canonical
    actual := .cellRef (OptionalCell.cellType payload) (entry.store.length + 2) :: entry.actual
    heap := after
    store := entry.store ++ [SourceCoreCallableIndexedFrames.encode frame entry.native,
      SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,.inLeft payload .unit]
    embedding := entry.embedding.lift
    location := entry.location
    native := entry.native
    environments := environments
    heaps := heaps
    heapTyped := (Dynamic.HeapWellTyped.iff_of_binderExtends extended).mp (entry.heapTyped.allocate (.none _) allocated)
    locals := locals
    agrees := agrees
    actualTyped := typed
    reference := reference
    read := read
    unmapped := (preserved entry.location entry.unmapped (List.getElem?_eq_some_iff.mp entry.read).1).1
    runtime := entry.runtime.transport (.ofBinderExtends extended)
    covers := (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers entry.covers }
  obtain ⟨tail⟩ := remaining next
  exact ⟨{
    size := _
    finalContext := tail.finalContext
    outcome := tail.outcome
    after := tail.after
    value := tail.value
    store := tail.store
    mapping := tail.mapping
    world := tail.world
    determines := CellAwareLexicalBodyDeterminacy.absent entry.runtime.graph.nodeOccurrencesUnique found form extended allocated tail.determines
    trace := .letUninitialized (lookupStatement?_sound found) form mono extended allocated tail.trace
    evaluated := .letE evaluated tail.evaluated
    represented := tail.represented
    heaps := tail.heaps
    preserved := preserved.trans tail.preserved
    effect := effect.trans tail.effect
    fallthroughTyped := fun environment same =>
      (Dynamic.HeapWellTyped.iff_of_binderExtends extended).mpr (tail.fallthroughTyped environment same) }⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeclarations
