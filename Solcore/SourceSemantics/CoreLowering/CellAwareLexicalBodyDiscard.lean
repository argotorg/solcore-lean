import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyExpressions
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryContinuation

/-! Ordinary declaration prefixes compose actual marked allocation with the
rest of the lexical body. Restoring bindings keeps new Source and native cells
and every earlier captured generalized descriptor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDiscard
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

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {reasonAt : ExpressionId → Word} {semanticFaults : FunctionCalls.FaultRep}
  (uninitialized : ∀ context fuel scope id lowered,
    CompatibleExpressionReads.LoweredRead fuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)

include extension uninitialized semantic selectedBodies in
theorem completes {context scope mode id node expression expressionNode semicolon rest expected type body lowered}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
    (continuing : semicolon = true ∨ mode = false)
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (certificate : CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation)
      (reasonAt := reasonAt) context scope expression lowered)
    (remaining : ∀ next : Entry functions rawRegistry instances program invocation frame globals context scope,
        Nonempty (Result next registry faults mode rest expected type body)) :
    Nonempty (Result entry registry faults mode (id :: rest) expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)) := by
  obtain ⟨size,outcome,middle,value,middleStore,trace,evaluated,represented,heaps,preserved,effect,valueTyped,determines⟩ :=
    CellAwareLexicalBodyExpressions.expression functions extension uninitialized semantic selectedBodies entry certificate expressionFound
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
        determines := CellAwareLexicalBodyDeterminacy.discardFault entry.runtime.graph.nodeOccurrencesUnique found form continuing determines
        trace := .expressionFault (lookupStatement?_sound found) form trace
        evaluated := by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated
        represented := .fault matched
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | value sourceValue =>
    cases represented with
    | @value _ nativeValue payload =>
      have heapTyped := (valueTyped sourceValue rfl).1
      let reached := entry.advance heaps heapTyped preserved effect
      let next := reached.prefix nativeValue lowered.type ((CompatibleAmbientHeap.payloadModel checked rawRegistry functions).runtime_hasType payload)
      obtain ⟨tail⟩ := remaining next
      have tailEval : Evaluates (nativeValue :: entry.actual) middleStore
          ((body.rename entry.embedding).weakenAt 0) tail.value tail.store := by
        simpa only [next,Entry.prefix,reached,Entry.advance,GenericExpressionMeaning.rename_prefix] using tail.evaluated
      have fullTrace : ∃ fullSize, Staging.Recursive.Size.StatementsIn program registry mode fullSize invocation
          context entry.environment entry.heap (id :: rest) tail.finalContext tail.outcome.embed tail.after := by
        cases semicolon with
        | true => exact ⟨_,.discard (lookupStatement?_sound found) form trace tail.trace⟩
        | false =>
          have modeFalse := continuing.resolve_left (by decide)
          subst mode
          exact ⟨_,.discardValue (lookupStatement?_sound found) form trace tail.trace⟩
      obtain ⟨fullSize,fullTrace⟩ := fullTrace
      exact ⟨{
        size := fullSize
        finalContext := tail.finalContext
        outcome := tail.outcome
        after := tail.after
        value := tail.value
        store := tail.store
        mapping := tail.mapping
        world := tail.world
        determines := CellAwareLexicalBodyDeterminacy.discard entry.runtime.graph.nodeOccurrencesUnique found form continuing determines tail.determines
        trace := fullTrace
        evaluated := by rw [LoopRenaming.discard]; exact LocalSequence.discard_success _ evaluated tailEval
        represented := tail.represented
        heaps := tail.heaps
        preserved := preserved.trans tail.preserved
        effect := effect.trans tail.effect
        fallthroughTyped := tail.fallthroughTyped }⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDiscard
