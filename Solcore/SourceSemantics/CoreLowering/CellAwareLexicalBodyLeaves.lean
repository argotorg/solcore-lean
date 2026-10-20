import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyExpressions
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyTree

/-! Terminal and empty lexical leaves use the actual Source occurrence and
its own expression receipt, retaining semantic faults at the reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyLeaves
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

theorem nil {context scope mode expected type}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (allowed : mode = false ∨ expected = .unit) :
    Nonempty (Result entry registry faults mode [] expected type (LocalLoop.fallthrough type)) := by
  exact ⟨{
    size := _
    finalContext := context
    outcome := .fallthrough entry.environment
    after := entry.heap
    value := LocalLoop.fallthroughValue type
    store := entry.store
    mapping := entry.mapping
    world := entry.world
    trace := .nil
    evaluated := by simpa only [LoopRenaming.fallthrough] using LocalLoop.fallthrough_evaluates type entry.actual entry.store
    represented := .fallthrough entry.environment allowed
    heaps := entry.heaps
    preserved := .refl _ _
    effect := .refl _ _ _ _
    fallthroughTyped := fun _ _ => entry.heapTyped
    determines := CellAwareLexicalBodyDeterminacy.nil }⟩

theorem returnUnit {context scope mode id node}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (rest : List StatementId)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
    Nonempty (Result entry registry faults mode (id :: rest) .unit .unit (LocalLoop.returned .unit)) := by
  exact ⟨{
    size := _
    finalContext := context
    outcome := .returned .unit
    after := entry.heap
    value := LocalLoop.returnedValue .unit
    store := entry.store
    mapping := entry.mapping
    world := entry.world
    determines := CellAwareLexicalBodyDeterminacy.returnUnit entry.runtime.graph.nodeOccurrencesUnique found form
    trace := .returnUnit (lookupStatement?_sound found) form
    evaluated := by simpa only [LoopRenaming.returned, Expr.rename] using LocalLoop.returned_evaluates (Evaluates.unit (environment := entry.actual) (store := entry.store))
    represented := .returned .unit
    heaps := entry.heaps
    preserved := .refl _ _
    effect := .refl _ _ _ _
    fallthroughTyped := by intro _ impossible; cases impossible }⟩

inductive Terminal (source : TypedSource) (expression : ExpressionId) : Bool → List StatementId → Prop where
  | returning {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression)) :
      Terminal source expression mode (id :: rest)
  | tail {id node}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false) :
      Terminal source expression true [id]

theorem Terminal.value {expression mode statements}
    (head : Terminal invocation.source expression mode statements)
    {size context environment before after sourceValue}
    (child : Staging.Recursive.Size.Expression program registry size invocation context environment before expression (.value sourceValue) after) :
    Staging.Recursive.Size.StatementsIn program registry mode (Staging.Recursive.Size.stepSize [size]) invocation
      context environment before statements context (.returned sourceValue) after := by
  cases head with
  | returning rest found form => exact .returnValue (lookupStatement?_sound found) form child
  | tail found form => exact .tail (lookupStatement?_sound found) form child

theorem Terminal.fault {expression mode statements}
    (head : Terminal invocation.source expression mode statements)
    {size context environment before after reason}
    (child : Staging.Recursive.Size.Expression program registry size invocation context environment before expression (.fault reason) after) :
    Staging.Recursive.Size.StatementsIn program registry mode (Staging.Recursive.Size.stepSize [size]) invocation
      context environment before statements context (.fault reason) after := by
  cases head with
  | returning rest found form => exact .returnFault (lookupStatement?_sound found) form child
  | tail found form => exact .expressionFault (lookupStatement?_sound found) form child

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry rawRegistry)
  {reasonAt : ExpressionId → Word} {semanticFaults : FunctionCalls.FaultRep}
  (uninitialized : ∀ context fuel scope id lowered,
    CompatibleExpressionReads.LoweredRead fuel (.initial checked) invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)

include extension uninitialized semantic selectedBodies in
theorem terminal {context scope mode statements expression lowered node expected}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (head : Terminal invocation.source expression mode statements)
    (found : invocation.source.lookupExpression? expression = some node) (valueType : node.type = expected)
    (certificate : CellAwareLexicalBodyExpressions.Certificate (checked := checked) (invocation := invocation)
      (reasonAt := reasonAt) context scope expression lowered) :
    Nonempty (Result entry registry faults mode statements expected lowered.type (LocalLoop.returnValue lowered.type lowered.expression)) := by
  obtain ⟨size,outcome,after,value,finalStore,trace,evaluated,represented,heaps,preserved,effect,_,determines⟩ :=
    CellAwareLexicalBodyExpressions.expression functions extension uninitialized semantic selectedBodies entry certificate found
  have actualHead : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode statements := by
    cases head with
    | returning rest found form => exact .returning rest (lookupStatement?_sound found) form
    | tail found form => exact .tail (lookupStatement?_sound found) form
  cases outcome with
  | value sourceValue =>
    cases represented with
    | @value _ nativeValue payload =>
      exact ⟨{
        size := _
        finalContext := context
        outcome := .returned sourceValue
        after := after
        value := LocalLoop.returnedValue nativeValue
        store := finalStore
        mapping := entry.mapping
        world := entry.world
        determines := CellAwareLexicalBodyDeterminacy.terminal entry.runtime.graph.nodeOccurrencesUnique actualHead determines
        trace := head.value trace
        evaluated := by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated
        represented := .returned (valueType ▸ payload)
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
        store := finalStore
        mapping := entry.mapping
        world := entry.world
        determines := CellAwareLexicalBodyDeterminacy.terminal entry.runtime.graph.nodeOccurrencesUnique actualHead determines
        trace := head.fault trace
        evaluated := by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated
        represented := .fault matched
        heaps := heaps
        preserved := preserved
        effect := effect
        fallthroughTyped := by intro _ impossible; cases impossible }⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyLeaves
