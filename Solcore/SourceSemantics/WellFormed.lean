import Solcore.Frontend.SourceInference.TypedIR

/-!
Declarative occurrence-graph closure for occurrence-addressed typed source.

The predicates in this module describe the source graph independently of the
algorithm that produced it.  In particular, membership is stated with
`List.Mem`; none of these definitions is an alias for a successful frontend
checker run.  The lookup correspondence theorems isolate the one invariant
needed to make the existing first-match lookup functions extensional: node
occurrence identities are unique.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend.SourceInference

/-- Category-preserving identities carried by the source node table. -/
def nodeIds (source : TypedSource) : List NodeId :=
  source.nodes.map Node.id

/-- Category-erased occurrence identities carried by the source node table. -/
def nodeOccurrenceIds (source : TypedSource) : List OccurrenceId :=
  source.nodes.map Node.occurrenceId

/-- Declarative membership of a heterogeneous node at a category-safe ID. -/
def ContainsNode (source : TypedSource) (id : NodeId) (node : Node) : Prop :=
  node ∈ source.nodes ∧ node.id = id

/-- Declarative membership of an expression occurrence. -/
def ContainsExpression (source : TypedSource) (id : ExpressionId)
    (node : ExpressionNode) : Prop :=
  Node.expression node ∈ source.nodes ∧ node.id = id

/-- Declarative membership of a statement occurrence. -/
def ContainsStatement (source : TypedSource) (id : StatementId)
    (node : StatementNode) : Prop :=
  Node.statement node ∈ source.nodes ∧ node.id = id

/-- No two source nodes, even of different categories, share an occurrence. -/
def NodeOccurrencesUnique (source : TypedSource) : Prop :=
  (nodeOccurrenceIds source).Nodup

/-- An occurrence identity belongs to the declaration owning this source. -/
def OccurrenceOwnedBy (owner : Resolved.DeclarationId)
    (id : OccurrenceId) : Prop :=
  id.owner = owner

/-- A category-safe node identity belongs to the given declaration. -/
def NodeIdOwnedBy (owner : Resolved.DeclarationId) (id : NodeId) : Prop :=
  OccurrenceOwnedBy owner id.occurrenceId

/-- Every table node belongs to the declaration represented by the source. -/
def NodesOwned (source : TypedSource) : Prop :=
  ∀ node, node ∈ source.nodes →
    OccurrenceOwnedBy source.owner node.occurrenceId

/-- Every root belongs to the declaration represented by the source. -/
def RootsOwned (source : TypedSource) : Prop :=
  ∀ root, root ∈ source.roots → NodeIdOwnedBy source.owner root

/-- Compatibility name for the canonical place edges stored by typed IR. -/
def placeChildIds (place : PlaceResolution) : List NodeId :=
  place.references

/-- Compatibility name for the canonical assignment-target edges. -/
def assignmentChildIds (assignment : AssignmentResolution) : List NodeId :=
  assignment.references

/-- Compatibility name for the canonical `for`-item edges. -/
def forItemChildIds : ForItemForm → List NodeId
  | item => item.references

/-- Compatibility name for the canonical match-case edges. -/
def matchCaseChildIds (matchCase : TypedMatchCase) : List NodeId :=
  matchCase.references

/-- Compatibility name for the canonical resolved-match edges. -/
def matchChildIds (resolution : MatchResolution) : List NodeId :=
  resolution.references

/-- Compatibility name for the canonical expression-form edges. -/
def expressionChildIds : ExpressionForm → List NodeId
  | form => form.references

/-- Compatibility name for the canonical statement-form edges. -/
def statementChildIds : StatementForm → List NodeId
  | form => form.references

/-- Compatibility name for the canonical heterogeneous-node edges. -/
def nodeChildIds : Node → List NodeId
  | node => node.references

/-- Every category-safe root names a table node of the same category. -/
def RootsExist (source : TypedSource) : Prop :=
  ∀ root, root ∈ source.roots → root ∈ nodeIds source

/-- Every direct occurrence edge names a table node of the same category. -/
def ChildEdgesExist (source : TypedSource) : Prop :=
  ∀ node, node ∈ source.nodes →
    ∀ child, child ∈ nodeChildIds node → child ∈ nodeIds source

/-- The initial occurrence-graph closure layer.  It deliberately does not yet
claim local-identity ownership, reachability, acyclicity, or lexical scope
validity.  Later semantic layers can extend this conjunction without
identifying it with an executable checker result. -/
structure OccurrenceGraphWellFormed (source : TypedSource) : Prop where
  nodeOccurrencesUnique : NodeOccurrencesUnique source
  nodesOwned : NodesOwned source
  rootsOwned : RootsOwned source
  rootsExist : RootsExist source
  childEdgesExist : ChildEdgesExist source

private theorem expressionId_eq_of_occurrence_eq
    {left right : ExpressionId}
    (equal : left.occurrence = right.occurrence) : left = right := by
  cases left
  cases right
  cases equal
  rfl

private theorem statementId_eq_of_occurrence_eq
    {left right : StatementId}
    (equal : left.occurrence = right.occurrence) : left = right := by
  cases left
  cases right
  cases equal
  rfl

private theorem find?_eq_some_of_mem_of_nodup_map
    {α β : Type} [DecidableEq β] (key : α → β)
    {items : List α} {item : α}
    (unique : (items.map key).Nodup) (member : item ∈ items) :
    items.find? (fun candidate => decide (key candidate = key item)) =
      some item := by
  induction items with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases unique with ⟨headAbsent, tailUnique⟩
      simp only [List.mem_cons] at member
      rcases member with headEq | tailMember
      · subst head
        simp
      · have keysDiffer : key head ≠ key item := by
          intro keysEqual
          apply headAbsent
          rw [keysEqual]
          exact List.mem_map.mpr ⟨item, tailMember, rfl⟩
        simp [List.find?, keysDiffer,
          inductionHypothesis tailUnique tailMember]

/-- Successful occurrence lookup implies declarative table membership and the
requested occurrence identity.  This direction needs no uniqueness premise. -/
theorem lookupNode?_sound
    {source : TypedSource} {id : OccurrenceId} {node : Node}
    (found : source.lookupNode? id = some node) :
    node ∈ source.nodes ∧ node.occurrenceId = id := by
  constructor
  · exact List.mem_of_find?_eq_some found
  · have predicateMatches := List.find?_some found
    simpa [TypedSource.lookupNode?] using predicateMatches

/-- With unique occurrences, declarative membership determines occurrence
lookup independently of node-table order. -/
theorem lookupNode?_complete
    {source : TypedSource} {id : OccurrenceId} {node : Node}
    (unique : NodeOccurrencesUnique source)
    (member : node ∈ source.nodes)
    (nodeId : node.occurrenceId = id) :
    source.lookupNode? id = some node := by
  subst id
  exact find?_eq_some_of_mem_of_nodup_map Node.occurrenceId
    (by simpa [NodeOccurrencesUnique, nodeOccurrenceIds] using unique) member

/-- Expression lookup is sound for declarative expression membership. -/
theorem lookupExpression?_sound
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) :
    ContainsExpression source id node := by
  unfold TypedSource.lookupExpression? at found
  generalize lookup : source.lookupNode? id.occurrence = candidate at found
  cases candidate with
  | none => simp at found
  | some candidate =>
      cases candidate with
      | statement statement => simp at found
      | expression expression =>
          simp only [Option.some.injEq] at found
          subst expression
          have sound := lookupNode?_sound lookup
          refine ⟨sound.1, ?_⟩
          apply expressionId_eq_of_occurrence_eq
          simpa [Node.occurrenceId, Node.id, NodeId.occurrenceId] using sound.2

/-- Statement lookup is sound for declarative statement membership. -/
theorem lookupStatement?_sound
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    (found : source.lookupStatement? id = some node) :
    ContainsStatement source id node := by
  unfold TypedSource.lookupStatement? at found
  generalize lookup : source.lookupNode? id.occurrence = candidate at found
  cases candidate with
  | none => simp at found
  | some candidate =>
      cases candidate with
      | expression expression => simp at found
      | statement statement =>
          simp only [Option.some.injEq] at found
          subst statement
          have sound := lookupNode?_sound lookup
          refine ⟨sound.1, ?_⟩
          apply statementId_eq_of_occurrence_eq
          simpa [Node.occurrenceId, Node.id, NodeId.occurrenceId] using sound.2

/-- Under unique occurrences, declarative expression membership is complete
for the executable category-safe lookup. -/
theorem lookupExpression?_complete
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (contains : ContainsExpression source id node) :
    source.lookupExpression? id = some node := by
  rcases contains with ⟨member, nodeId⟩
  have occurrenceId :
      (Node.expression node).occurrenceId = id.occurrence := by
    simp [Node.occurrenceId, Node.id, NodeId.occurrenceId, nodeId]
  have found := lookupNode?_complete unique member occurrenceId
  simp [TypedSource.lookupExpression?, found]

/-- Under unique occurrences, declarative statement membership is complete
for the executable category-safe lookup. -/
theorem lookupStatement?_complete
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) :
    source.lookupStatement? id = some node := by
  rcases contains with ⟨member, nodeId⟩
  have occurrenceId :
      (Node.statement node).occurrenceId = id.occurrence := by
    simp [Node.occurrenceId, Node.id, NodeId.occurrenceId, nodeId]
  have found := lookupNode?_complete unique member occurrenceId
  simp [TypedSource.lookupStatement?, found]

/-- Lookup and declarative expression membership coincide once occurrence
identity uniqueness removes first-match ambiguity. -/
theorem lookupExpression?_eq_some_iff
    {source : TypedSource} (unique : NodeOccurrencesUnique source)
    {id : ExpressionId} {node : ExpressionNode} :
    source.lookupExpression? id = some node ↔
      ContainsExpression source id node :=
  ⟨lookupExpression?_sound, lookupExpression?_complete unique⟩

/-- Lookup and declarative statement membership coincide once occurrence
identity uniqueness removes first-match ambiguity. -/
theorem lookupStatement?_eq_some_iff
    {source : TypedSource} (unique : NodeOccurrencesUnique source)
    {id : StatementId} {node : StatementNode} :
    source.lookupStatement? id = some node ↔
      ContainsStatement source id node :=
  ⟨lookupStatement?_sound, lookupStatement?_complete unique⟩

end Solcore.SourceSemantics
