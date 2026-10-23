import Solcore.Frontend.SourceInference.Expression
import Solcore.Frontend.SourceInference.StateProperties
import Solcore.Frontend.SourceInference.NodeShapeProperties

/-!
Graph facts for the actual inference node table.  A completed node may only
refer to identities already in that table.  Coercion attachment changes
payloads but preserves both identities and child edges.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

def NodeIdsPresent (references : List NodeId) (nodes : List Node) : Prop :=
  references ⊆ nodes.map Node.id

def NodesClosed (nodes : List Node) : Prop :=
  ∀ node ∈ nodes, NodeIdsPresent node.references nodes

structure NodeGraphProgress (before after : State) : Prop where
  ids : NodeIdsPresent (before.nodes.map Node.id) after.nodes
  closed : NodesClosed before.nodes → NodesClosed after.nodes
  shapes : NodeShapesPreserved before.nodes after.nodes

namespace NodeIdsPresent

theorem nil (nodes : List Node) : NodeIdsPresent [] nodes := by
  simp [NodeIdsPresent]

theorem append {left right : List NodeId} {nodes : List Node}
    (first : NodeIdsPresent left nodes) (second : NodeIdsPresent right nodes) :
    NodeIdsPresent (left ++ right) nodes := by
  intro id member
  rcases List.mem_append.mp member with member | member
  · exact first member
  · exact second member

theorem cons {head : NodeId} {tail : List NodeId} {nodes : List Node}
    (first : NodeIdsPresent [head] nodes) (rest : NodeIdsPresent tail nodes) :
    NodeIdsPresent (head :: tail) nodes :=
  append first rest

theorem transport {references : List NodeId} {before after : State}
    (present : NodeIdsPresent references before.nodes)
    (progress : NodeGraphProgress before after) :
    NodeIdsPresent references after.nodes :=
  fun _ member => progress.ids (present member)

end NodeIdsPresent

namespace NodesClosed

theorem nil : NodesClosed [] := by
  simp [NodesClosed]

theorem record {nodes : List Node} (closed : NodesClosed nodes) (node : Node)
    (children : NodeIdsPresent node.references nodes) :
    NodesClosed (nodes ++ [node]) := by
  intro current member child reference
  rcases List.mem_append.mp member with old | fresh
  · exact List.mem_map.mpr (by
      rcases List.mem_map.mp (closed current old reference) with ⟨prior, priorMem, eq⟩
      exact ⟨prior, List.mem_append_left _ priorMem, eq⟩)
  · have eq : current = node := List.mem_singleton.mp fresh
    subst current
    rcases List.mem_map.mp (children reference) with ⟨prior, priorMem, eq⟩
    exact List.mem_map.mpr ⟨prior, List.mem_append_left _ priorMem, eq⟩

end NodesClosed

namespace NodeGraphProgress

theorem refl (state : State) : NodeGraphProgress state state :=
  ⟨fun _ member => member, fun closed => closed, .refl _⟩

theorem of_nodes_eq {before after : State} (eq : after.nodes = before.nodes) :
    NodeGraphProgress before after := by
  constructor
  · rw [eq]
    exact fun _ member => member
  · rw [eq]
    exact fun closed => closed
  · exact NodeShapesPreserved.of_eq eq

theorem trans {first middle last : State}
    (left : NodeGraphProgress first middle)
    (right : NodeGraphProgress middle last) :
    NodeGraphProgress first last :=
  ⟨fun _ member => right.ids (left.ids member),
    fun closed => right.closed (left.closed closed),
    left.shapes.trans right.shapes⟩

theorem recordNode (state : State) (node : Node)
    (children : NodeIdsPresent node.references state.nodes) :
    NodeGraphProgress state (state.recordNode node) := by
  constructor
  · intro id member
    simpa only [State.recordNode_nodes, List.map_append, List.map_cons,
      List.map_nil] using
      List.mem_append_left [node.id] member
  · exact fun closed => closed.record node children
  · exact NodeShapesPreserved.recordNode state node

theorem recordNode_present (state : State) (node : Node) :
    NodeIdsPresent [node.id] (state.recordNode node).nodes := by
  intro id member
  have eq := List.mem_singleton.mp member
  subst id
  simp [State.recordNode]

theorem modifyExpressionNode (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode)
    (form : ∀ node, (modify node).form = node.form) :
    NodeGraphProgress state (state.modifyExpressionNode id modify) := by
  have ids : (state.modifyExpressionNode id modify).nodes.map Node.id =
      state.nodes.map Node.id := by
    simp only [State.modifyExpressionNode, List.map_map]
    apply List.map_congr_left
    intro node member
    cases node with
    | statement node => rfl
    | expression node =>
        dsimp
        split
        · rename_i eq
          simp [Node.id, eq]
        · rfl
  constructor
  · rw [NodeIdsPresent, ids]
    exact fun _ member => member
  · intro closed node member child reference
    rw [State.modifyExpressionNode] at member
    rcases List.mem_map.mp member with ⟨prior, priorMem, eq⟩
    have refs : node.references = prior.references := by
      rw [← eq]
      cases prior with
      | statement prior => rfl
      | expression prior =>
          dsimp
          split
          · simp [Node.references, form]
          · rfl
    rw [ids]
    exact closed prior priorMem (by simpa only [refs] using reference)
  · exact NodeShapesPreserved.modifyExpressionNode state id modify form

theorem attachExpressionCoercions (state : State)
    (entries : List Detail.ExpressionCoercions) :
    NodeGraphProgress state (Detail.attachExpressionCoercions state entries) := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact refl state
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      exact (modifyExpressionNode state entry.expression
        (fun node => Detail.appendExpressionCoercions node entry.coercions)
        (fun _ => rfl)).trans (ih _)

end NodeGraphProgress

/-- The richer internal result projects to the established allocation law.
The returned references are real nodes of the resulting table. -/
structure OccurrenceGraphResult (before after : State)
    (references : List NodeId) : Prop where
  bound : before.OccurrenceBoundExtends after
  graph : NodeGraphProgress before after
  returned : NodeIdsPresent references after.nodes

theorem OccurrenceGraphResult.of_bound_nodes {before after : State}
    {references : List NodeId} (bound : before.OccurrenceBoundExtends after)
    (nodes : NodeGraphProgress before after ∧
      NodeIdsPresent references after.nodes) :
    OccurrenceGraphResult before after references :=
  ⟨bound, nodes.1, nodes.2⟩

class ReturnedNodeReferences (alpha : Type) where
  references : alpha → List NodeId

instance : ReturnedNodeReferences (InferredExpression × State) :=
  ⟨fun result => [.expression result.1.id]⟩

instance : ReturnedNodeReferences (List InferredExpression × State) :=
  ⟨fun result => result.1.map (fun expression => .expression expression.id)⟩

instance : ReturnedNodeReferences Detail.StatementResult :=
  ⟨fun result => [.statement result.id]⟩

instance : ReturnedNodeReferences Detail.BlockResult :=
  ⟨fun result => result.statements.map NodeId.statement⟩

instance : ReturnedNodeReferences Detail.InferredForItems :=
  ⟨fun result => result.items.flatMap ForItemForm.references⟩

instance : ReturnedNodeReferences (ForItemForm × State) :=
  ⟨fun result => result.1.references⟩

instance : ReturnedNodeReferences (PlaceResolution × State) :=
  ⟨fun result => result.1.references⟩

instance : ReturnedNodeReferences
    (AssignmentResolution × InferredExpression × State) :=
  ⟨fun result => result.1.references ++ [.expression result.2.1.id]⟩

instance : ReturnedNodeReferences Detail.MatchCasesResult :=
  ⟨fun result => result.cases.flatMap TypedMatchCase.references⟩



end Solcore.Frontend.SourceInference
