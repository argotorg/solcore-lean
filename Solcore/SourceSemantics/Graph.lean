import Solcore.SourceSemantics.WellFormed

/-!
Reachability and acyclicity of resolved source occurrence graphs.

The base closure judgment proves that every retained edge names a node.  This
module additionally excludes unreachable table entries and cyclic occurrence
spines, independently of the executable lookup functions.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend.SourceInference

/-- One direct, category-preserving occurrence edge. -/
def DirectChild (source : TypedSource) (parent child : NodeId) : Prop :=
  ∃ node, ContainsNode source parent node ∧ child ∈ nodeChildIds node

/-- A nonempty path through direct occurrence edges. -/
inductive Descends (source : TypedSource) : NodeId → NodeId → Prop where
  | direct {parent child : NodeId}
      (edge : DirectChild source parent child) :
      Descends source parent child
  | step {parent middle child : NodeId}
      (edge : DirectChild source parent middle)
      (tail : Descends source middle child) :
      Descends source parent child

/-- An occurrence is reachable from one of the declaration roots. -/
inductive Reachable (source : TypedSource) : NodeId → Prop where
  | root {id : NodeId} (member : id ∈ source.roots) : Reachable source id
  | child {parent child : NodeId}
      (parent_reachable : Reachable source parent)
      (edge : DirectChild source parent child) :
      Reachable source child

/-- Every retained table node contributes to the represented declaration. -/
def AllNodesReachable (source : TypedSource) : Prop :=
  ∀ node, node ∈ source.nodes → Reachable source node.id

/-- No occurrence can be its own proper descendant. -/
def OccurrenceGraphAcyclic (source : TypedSource) : Prop :=
  ∀ id, ¬ Descends source id id

/-- Declaration roots are occurrence positions, rather than a bag of entry
points.  Repeating a root would execute the same occurrence more than once. -/
def RootsUnique (source : TypedSource) : Prop :=
  source.roots.Nodup

/-- A parent may not retain the same child occurrence in two operand slots.
Together with `ChildHasUniqueParent`, this gives every non-root occurrence
exactly one incoming edge once reachability is known. -/
def ChildSlotsUnique (source : TypedSource) : Prop :=
  ∀ node, node ∈ source.nodes → (nodeChildIds node).Nodup

/-- One occurrence cannot be shared by two distinct parents. -/
def ChildHasUniqueParent (source : TypedSource) : Prop :=
  ∀ {left right child},
    DirectChild source left child →
    DirectChild source right child →
    left = right

/-- A declaration root has no incoming edge.  Thus roots and proper children
are disjoint occurrence classes. -/
def RootsHaveNoParent (source : TypedSource) : Prop :=
  ∀ {root parent}, root ∈ source.roots →
    ¬ DirectChild source parent root

/-- Full structural closure required by recursive source judgments. -/
structure OccurrenceGraphClosed (source : TypedSource) : Prop where
  wellFormed : OccurrenceGraphWellFormed source
  rootsUnique : RootsUnique source
  childSlotsUnique : ChildSlotsUnique source
  childHasUniqueParent : ChildHasUniqueParent source
  rootsHaveNoParent : RootsHaveNoParent source
  allNodesReachable : AllNodesReachable source
  acyclic : OccurrenceGraphAcyclic source

namespace Descends

theorem trans
    {source : TypedSource} {first middle last : NodeId}
    (left : Descends source first middle)
    (right : Descends source middle last) :
    Descends source first last := by
  induction left with
  | direct edge => exact .step edge right
  | step edge _ induction => exact .step edge (induction right)

end Descends

namespace Reachable

theorem descendant
    {source : TypedSource} {parent child : NodeId}
    (reachable : Reachable source parent)
    (descends : Descends source parent child) :
    Reachable source child := by
  induction descends with
  | direct edge => exact .child reachable edge
  | step edge _ induction => exact induction (.child reachable edge)

end Reachable

namespace OccurrenceGraphClosed

/-- Every reachable non-root occurrence has exactly one parent.  Existence
comes from reachability; uniqueness is the no-sharing invariant above. -/
theorem unique_parent
    {source : TypedSource} (closed : OccurrenceGraphClosed source)
    {child : NodeId} (reachable : Reachable source child)
    (notRoot : child ∉ source.roots) :
    ∃ parent, DirectChild source parent child ∧
      ∀ candidate, DirectChild source candidate child → candidate = parent := by
  induction reachable with
  | root member => exact False.elim (notRoot member)
  | @child parent child _ edge =>
      refine ⟨parent, edge, ?_⟩
      intro candidate candidateEdge
      exact closed.childHasUniqueParent candidateEdge edge

/-- Every retained non-root node has exactly one parent occurrence. -/
theorem retained_unique_parent
    {source : TypedSource} (closed : OccurrenceGraphClosed source)
    {node : Node} (member : node ∈ source.nodes)
    (notRoot : node.id ∉ source.roots) :
    ∃ parent, DirectChild source parent node.id ∧
      ∀ candidate, DirectChild source candidate node.id →
        candidate = parent :=
  closed.unique_parent (closed.allNodesReachable node member) notRoot

end OccurrenceGraphClosed

end Solcore.SourceSemantics
