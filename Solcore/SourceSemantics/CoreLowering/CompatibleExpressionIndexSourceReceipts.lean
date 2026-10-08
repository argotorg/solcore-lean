import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingReservedReceipts

/-! Index receipts retain each actual issuer and the original ordered lookup.
Their source membership is unconditional; canonical source association is a
separate finite receipt. These definitions perform no preparation or evaluation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexSourceReceipts
open Core Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev IndexSite := SourceCoreDataFaultSites.IndexSite

def Selected (indices : List IndexSite) (owner : Key) (id : ExpressionId) : Prop :=
  ∃ site, indices.find? (fun site => decide (site.owner = owner ∧ site.expression = id)) = some site

def Origin (sources : List (Key × TypedSource)) (site : IndexSite) : Prop :=
  ∃ source node base key,
    (site.owner, source) ∈ sources ∧ source.owner = site.owner.declaration ∧
    SourceSemantics.ContainsExpression source site.expression node ∧ node.form = .index base key ∧
    site.diagnostic = ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩

def NodesCovered (owner : Key) (nodes : List Node) (indices : List IndexSite) : Prop :=
  ∀ node, Node.expression node ∈ nodes → ∀ base key, node.form = .index base key →
    Selected indices owner node.id

def SourcesCovered (sources : List (Key × TypedSource)) (indices : List IndexSite) : Prop :=
  ∀ owner source, (owner, source) ∈ sources → NodesCovered owner source.nodes indices

def NodeSelected (owner : Key) (retained : Node) (indices : List IndexSite) : Prop :=
  ∀ node, retained = .expression node → ∀ base key, node.form = .index base key →
    Selected indices owner node.id

structure Inventory (sources visited : List (Key × TypedSource)) (indices : List IndexSite) : Prop where
  origins : ∀ site, site ∈ indices → Origin sources site
  unique : (indices.map (fun site => (site.owner, site.expression))).Nodup
  covered : SourcesCovered visited indices

structure NodeInventory (sources visited : List (Key × TypedSource))
    (owner : Key) (seen : List Node) (indices : List IndexSite) : Prop where
  inventory : Inventory sources visited indices
  covered : NodesCovered owner seen indices

theorem Inventory.empty (sources : List (Key × TypedSource)) : Inventory sources [] [] := by
  refine ⟨?_, by simp, ?_⟩
  · intro site member
    cases member
  · intro owner source member
    cases member

theorem Selected.append {indices : List IndexSite} {owner : Key} {id : ExpressionId}
    (selected : Selected indices owner id) (later : List IndexSite) : Selected (indices ++ later) owner id := by
  obtain ⟨site, found⟩ := selected
  exact ⟨site, by simp only [List.find?_append, found]; rfl⟩

theorem NodesCovered.append_indices {owner : Key} {nodes : List Node} {indices : List IndexSite}
    (covered : NodesCovered owner nodes indices) (later : List IndexSite) :
    NodesCovered owner nodes (indices ++ later) := by
  intro node member base key form
  exact (covered node member base key form).append later

theorem NodesCovered.step {owner : Key} {seen : List Node} {retained : Node} {indices : List IndexSite}
    (covered : NodesCovered owner seen indices) (selected : NodeSelected owner retained indices) :
    NodesCovered owner (seen ++ [retained]) indices := by
  intro node member base key form
  rcases List.mem_append.mp member with old | current
  · exact covered node old base key form
  · exact selected node (List.mem_singleton.mp current).symm base key form

theorem NodeSelected.statement (owner : Key) (node : StatementNode) (indices : List IndexSite) :
    NodeSelected owner (.statement node) indices := by
  intro expression same
  cases same

theorem NodeInventory.start {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    (inventory : Inventory sources visited indices) (owner : Key) :
    NodeInventory sources visited owner [] indices := by
  refine ⟨inventory, ?_⟩
  intro node member
  cases member

theorem NodeInventory.step {sources visited : List (Key × TypedSource)} {owner : Key}
    {seen : List Node} {indices : List IndexSite} {retained : Node}
    (inventory : NodeInventory sources visited owner seen indices)
    (selected : NodeSelected owner retained indices) :
    NodeInventory sources visited owner (seen ++ [retained]) indices :=
  ⟨inventory.inventory, inventory.covered.step selected⟩

theorem NodeInventory.finish {sources visited : List (Key × TypedSource)} {owner : Key}
    {source : TypedSource} {indices : List IndexSite}
    (inventory : NodeInventory sources visited owner source.nodes indices) :
    Inventory sources (visited ++ [(owner, source)]) indices := by
  refine ⟨inventory.inventory.origins, inventory.inventory.unique, ?_⟩
  intro key actual member
  rcases List.mem_append.mp member with old | current
  · exact inventory.inventory.covered key actual old
  · cases List.mem_singleton.mp current
    exact inventory.covered

theorem Inventory.append_index {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    (inventory : Inventory sources visited indices) {owner : Key} {source : TypedSource} {node : ExpressionNode}
    {base key : ExpressionId} (member : (owner, source) ∈ sources) (owns : source.owner = owner.declaration)
    (contains : SourceSemantics.ContainsExpression source node.id node) (form : node.form = .index base key)
    (absent : indices.find? (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = none)
    (reason : Word) :
    Inventory sources visited (indices ++ [⟨owner, node.id, reason,
      ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro site occurs
    rcases List.mem_append.mp occurs with old | current
    · exact inventory.origins site old
    · cases List.mem_singleton.mp current
      exact ⟨source, node, base, key, member, owns, contains, form, rfl⟩
  · rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨inventory.unique, by simp, ?_⟩
    intro pair pairMember other otherMember same
    obtain ⟨site, siteMember, pairEq⟩ := List.mem_map.mp pairMember
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at otherMember
    have pairSame := same.trans otherMember
    have hit : site.owner = owner ∧ site.expression = node.id := by
      exact Prod.mk.inj (pairEq.trans pairSame)
    have avoids := List.find?_eq_none.mp absent site siteMember
    exact avoids (by simp [hit.1, hit.2])
  · intro key actual occurs
    exact (inventory.covered key actual occurs).append_indices _

theorem selected_fresh {indices : List IndexSite} {owner : Key} {node : ExpressionNode} (reason : Word)
    (absent : indices.find? (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = none) :
    Selected (indices ++ [⟨owner, node.id, reason,
      ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩]) owner node.id := by
  refine ⟨⟨owner, node.id, reason,
    ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩, ?_⟩
  rw [List.find?_append, absent]
  simp

theorem NodeInventory.append_index {sources visited : List (Key × TypedSource)} {owner : Key}
    {seen : List Node} {indices : List IndexSite} {source : TypedSource} {node : ExpressionNode}
    {base key : ExpressionId} (inventory : NodeInventory sources visited owner seen indices)
    (member : (owner, source) ∈ sources) (owns : source.owner = owner.declaration)
    (contains : SourceSemantics.ContainsExpression source node.id node) (form : node.form = .index base key)
    (absent : indices.find? (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = none)
    (reason : Word) :
    NodeInventory sources visited owner (seen ++ [.expression node])
      (indices ++ [⟨owner, node.id, reason,
        ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩]) := by
  refine ⟨inventory.inventory.append_index member owns contains form absent reason, ?_⟩
  apply (inventory.covered.append_indices _).step
  intro actual same base key actualForm
  cases same
  exact selected_fresh reason absent

def Receipt {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    (plan : SourceSpecializationWorklist.Plan) (root : Key) (sources : List (Key × TypedSource))
    (program : SourceCoreCompatibleDataPlaceFaultSites.Program context) : Prop :=
  CompatiblePlaceMissingReservedReceipts.ReservedReceipt context plan root program ∧
    Inventory (plan.specializations.map (fun row => (row.key, row.function.typedBody)) ++ sources)
      (plan.specializations.map (fun row => (row.key, row.function.typedBody)) ++ sources)
      program.program.expressions.indices

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexSourceReceipts
