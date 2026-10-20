import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeclarations
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryContinuation

/-! Ordinary declaration prefixes compose actual marked allocation with the
rest of the lexical body. Restoring bindings keeps new Source and native cells
and every earlier captured generalized descriptor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyInitialized
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

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {reasonAt : ExpressionId → Word} {semanticFaults : FunctionCalls.FaultRep}
  (uninitialized : ∀ context fuel scope id lowered,
    CompatibleExpressionReads.LoweredRead fuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (wellFormed : ProgramWellFormed program)

include definitions registered extension uninitialized semantic wellFormed in
theorem completes {context nextContext scope mode id node binder initializer initializerNode rest expected type body lowered}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = []) (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (initializerFound : invocation.source.lookupExpression? initializer = some initializerNode)
    (valueType : initializerNode.type = binder.scheme.body)
    (certificate : CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation)
      (reasonAt := reasonAt) context scope initializer lowered)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (TypedLexicalControl.initializedRequest invocation.source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (TypedLexicalControl.initializedRequest invocation.source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (remaining : ∀ next : Entry functions rawRegistry instances program invocation frame globals
        nextContext ((binder.id,lowered.type) :: scope), Nonempty (Result next registry faults mode rest expected type body)) :
    Nonempty (Result entry registry faults mode (id :: rest) expected type
      (TypedLexicalControl.sequence type lowered.expression annotation.expression body)) := by
  obtain ⟨size,outcome,middle,value,middleStore,trace,evaluated,represented,heaps,preserved,effect,valueTyped,determines⟩ :=
    CellAwareLexicalBodyExpressions.expression functions extension uninitialized semantic wellFormed entry certificate initializerFound
  cases outcome with
  | fault reason =>
    cases represented with
    | fault matched =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .fault reason
        after := middle
        value := _
        store := middleStore
        mapping := entry.mapping
        world := entry.world
        determines := CellAwareLexicalBodyDeterminacy.initializedFault entry.runtime.graph.nodeOccurrencesUnique found form mono extended determines
        trace := .letFault (lookupStatement?_sound found) form mono trace
        evaluated := CellAwareOrdinaryContinuation.failure evaluated
        represented := .fault matched
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | value sourceValue =>
    cases represented with
    | @value _ nativeValue payload =>
      obtain ⟨heapTyped,sourceTyped⟩ := valueTyped sourceValue rfl
      let reached := entry.advance heaps heapTyped preserved effect
      let after : Dynamic.Heap := ⟨middle.cells ++ [⟨binder.scheme.body,some sourceValue,none⟩]⟩
      let location : Dynamic.Location := ⟨middle.cells.length⟩
      have allocated : Dynamic.Heap.Allocates middle binder.scheme.body (some sourceValue) location after := .append
      obtain ⟨captured,allocationEval,environments,nextHeaps,locals,agrees,typed,reference,read,allocationFrame,allocationEffect⟩ :=
        CellAwareOrdinaryBodyAllocation.initialized GeneralizedLocalDescriptorHeap.ordinary_cells definitions registered
          mono extended ordinary allocation annotation same (valueType ▸ payload) reached.environments reached.heaps reached.locals
          reached.agrees reached.actualTyped reached.reference reached.read allocated
      let next : Entry functions rawRegistry instances program invocation frame globals nextContext ((binder.id,lowered.type) :: scope) := {
        mapping := reached.mapping ++ [reached.store.length + 2]
        world := reached.world ++ [frame.type,allocation.entry.layout.type,OptionalCell.cellType lowered.type]
        administrative := reached.administrative
        actualContext := OptionalCell.referenceType lowered.type :: lowered.type :: reached.actualContext
        environment := (binder.id,location) :: reached.environment
        canonical := .cellRef (OptionalCell.cellType lowered.type) (reached.store.length + 2) :: reached.canonical
        actual := .cellRef (OptionalCell.cellType lowered.type) (reached.store.length + 2) :: nativeValue :: reached.actual
        heap := after
        store := reached.store ++ [SourceCoreCallableIndexedFrames.encode frame reached.native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,.inRight .unit nativeValue]
        embedding := (Renaming.comp (Renaming.insertion 0) reached.embedding).lift
        location := reached.location
        native := reached.native
        environments := environments
        heaps := nextHeaps
        heapTyped := (Dynamic.HeapWellTyped.iff_of_binderExtends extended).mp (heapTyped.allocate (.some (valueType ▸ sourceTyped)) allocated)
        locals := locals
        agrees := agrees
        actualTyped := typed
        reference := reference
        read := read
        unmapped := (allocationFrame reached.location reached.unmapped (List.getElem?_eq_some_iff.mp reached.read).1).1
        runtime := reached.runtime.transport (.ofBinderExtends extended)
        covers := (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers reached.covers }
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
        determines := CellAwareLexicalBodyDeterminacy.initialized entry.runtime.graph.nodeOccurrencesUnique found form mono extended determines allocated tail.determines
        trace := .letInitialized (lookupStatement?_sound found) form trace mono extended allocated tail.trace
        evaluated := (CellAwareOrdinaryContinuation.agreement evaluated allocationEval).wrap tail.evaluated
        represented := tail.represented
        heaps := tail.heaps
        preserved := preserved.trans (allocationFrame.trans tail.preserved)
        effect := effect.trans (allocationEffect.trans tail.effect)
        fallthroughTyped := fun environment same =>
          (Dynamic.HeapWellTyped.iff_of_binderExtends extended).mpr (tail.fallthroughTyped environment same) }⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyInitialized
