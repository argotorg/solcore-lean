import Solcore.SourceSemantics.Staging.RecursiveBodyErasure
import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyExpressions
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyTree

/-! Terminal and empty lexical leaves use the actual Source occurrence and
its own expression receipt, retaining semantic faults at the reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyBlock
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

theorem completes {context scope mode id node statements rest expected type innerCode body}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ start : Entry functions rawRegistry instances program invocation frame globals context scope,
      Nonempty (Result start registry faults false statements expected type innerCode))
    (remaining : ∀ next : Entry functions rawRegistry instances program invocation frame globals context scope,
      Nonempty (Result next registry faults mode rest expected type body)) :
    Nonempty (Result entry registry faults mode (id :: rest) expected type (LocalLoop.sequence type innerCode body)) := by
  obtain ⟨⟨size,innerContext,outcome,after,value,store,mapping,world,trace,evaluated,represented,heaps,preserved,effect,heapTyped,determines⟩⟩ := inner entry
  cases outcome with
  | returned sourceValue =>
    cases represented with
    | returned payload =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .returned sourceValue
        after := after
        value := _
        store := store
        mapping := mapping
        world := world
        determines := CellAwareLexicalBodyDeterminacy.blockReturned entry.runtime.graph.nodeOccurrencesUnique found form determines
        trace := .blockReturned (lookupStatement?_sound found) form trace
        evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ evaluated
        represented := .returned payload
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | fault reason =>
    cases represented with
    | fault matched =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .fault reason
        after := after
        value := _
        store := store
        mapping := mapping
        world := world
        determines := CellAwareLexicalBodyDeterminacy.blockFault entry.runtime.graph.nodeOccurrencesUnique found form determines
        trace := .blockFault (lookupStatement?_sound found) form trace
        evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ evaluated
        represented := .fault matched
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | fallthrough innerEnvironment =>
    cases represented with
    | fallthrough _ _ =>
      let reached := entry.advance heaps (heapTyped innerEnvironment rfl) preserved effect
      let next := ((reached.prefix (.inLeft LocalLoop.transferType (.inLeft type .unit))
        (LocalLoop.controlType type) (.inLeft (.inLeft .unit))).prefix (.inLeft type .unit)
        (LocalControl.controlType type) (.inLeft .unit)).prefix .unit .unit .unit
      obtain ⟨tail⟩ := remaining next
      have tailEval : Evaluates
          (.unit :: .inLeft type .unit :: .inLeft LocalLoop.transferType (.inLeft type .unit) :: entry.actual)
          store (((body.rename entry.embedding).weakenAt 0).weakenAt 0 |>.weakenAt 0) tail.value tail.store := by
        simpa only [next,Entry.prefix,reached,Entry.advance,GenericExpressionMeaning.rename_prefix] using tail.evaluated
      exact ⟨{
        size := _
        finalContext := tail.finalContext
        outcome := tail.outcome
        after := tail.after
        value := tail.value
        store := tail.store
        mapping := tail.mapping
        world := tail.world
        determines := CellAwareLexicalBodyDeterminacy.blockFallthrough entry.runtime.graph.nodeOccurrencesUnique found form determines tail.determines
        trace := .blockFallthrough (lookupStatement?_sound found) form trace tail.trace
        evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_fallthrough _ evaluated tailEval
        represented := tail.represented
        heaps := tail.heaps
        preserved := preserved.trans tail.preserved
        effect := effect.trans tail.effect
        fallthroughTyped := tail.fallthroughTyped }⟩

theorem stopped {context scope mode id node statements rest expected type innerCode suffix}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .block statements)
    (stops : GenericLexicalStatements.Stopped invocation.source statements)
    (inner : ∀ start : Entry functions rawRegistry instances program invocation frame globals context scope,
      Nonempty (Result start registry faults false statements expected type innerCode)) :
    Nonempty (Result entry registry faults mode (id :: rest) expected type (LocalLoop.sequence type innerCode suffix)) := by
  obtain ⟨⟨size,innerContext,outcome,after,value,store,mapping,world,trace,evaluated,represented,heaps,preserved,effect,_,determines⟩⟩ := inner entry
  cases outcome with
  | returned sourceValue =>
    cases represented with
    | returned payload =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .returned sourceValue
        after := after
        value := _
        store := store
        mapping := mapping
        world := world
        determines := CellAwareLexicalBodyDeterminacy.blockReturned entry.runtime.graph.nodeOccurrencesUnique found form determines
        trace := .blockReturned (lookupStatement?_sound found) form trace
        evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_returned _ evaluated
        represented := .returned payload
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | fault reason =>
    cases represented with
    | fault matched =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .fault reason
        after := after
        value := _
        store := store
        mapping := mapping
        world := world
        determines := CellAwareLexicalBodyDeterminacy.blockFault entry.runtime.graph.nodeOccurrencesUnique found form determines
        trace := .blockFault (lookupStatement?_sound found) form trace
        evaluated := by rw [LoopRenaming.sequence]; exact LocalLoop.sequence_failure _ evaluated
        represented := .fault matched
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩
  | fallthrough environment =>
    have impossible := stops.terminates entry.runtime.graph.nodeOccurrencesUnique false trace.sound.fallthrough_scoped
    cases impossible

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyBlock
