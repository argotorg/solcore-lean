import Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductSource

/-! Finite post transport uses the actual scalar Source form and layout.
It keeps the same token and final tuple and evaluates no expression. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ScalarExpressionFaultPostContracts
open Core Frontend SourceInference CompatibleExpressionReads
open ExpressionFailurePostContracts

variable {post : ExpressionFaultPost} {listPost : ExpressionsFaultPost}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource}

theorem ordinary_layout {checked : SourceCoreCompatibleCatalog.Checked}
    {id : ExpressionId} {node : ExpressionNode} {type : Ty}
    (metadata : Metadata checked source id node type) :
    Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] := by
  rw [metadata.requirements, metadata.coercions]
  rfl

theorem expression_fault_outcome
    (joins : CompositionJoins post listPost program context evidence source)
    {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id child : ExpressionId} {childType parentType : Ty} {reason : Dynamic.SemanticFault} {token : Word}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {store : Store}
    (link : ExpressionLink program context evidence source environment before id middle child)
    (failed : Dynamic.ExpressionFaults program context evidence source environment middle child reason after)
    (retained : OutcomePost post program context evidence source environment middle child childType
      (.fault reason) after (.inLeft childType (.word token)) mapping world store) :
    OutcomePost post program context evidence source environment before id parentType
      (.fault reason) after (.inLeft parentType (.word token)) mapping world store :=
  ⟨token, rfl, joins.expression link failed (OutcomePost.fault retained)⟩

theorem tuple_outcome (joins : CompositionJoins post listPost program context evidence source)
    {checked : SourceCoreCompatibleCatalog.Checked} {id : ExpressionId} {node : ExpressionNode}
    {nativeType type : Ty} {ids : List ExpressionId} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {sequence : DataExpressionSequence.Outcome}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {store : Store}
    (metadata : Metadata checked source id node nativeType) (form : node.form = .tuple ids)
    (trace : DataExpressionSequence.Trace program context evidence source environment before ids sequence after)
    (packed : CompatibleExpressionProducts.PacksOutcome sequence outcome)
    (retained : ListOutcomePost listPost program context evidence source environment before ids type
      sequence after value mapping world store) :
    OutcomePost post program context evidence source environment before id type
      outcome after value mapping world store := by
  cases packed with
  | values _ => trivial
  | fault reason =>
    cases trace with
    | fault failed =>
      obtain ⟨token, same, retained⟩ := retained
      exact ⟨token, same, joins.expressions
        (.tuple (lookupExpression?_sound metadata.found) form (ordinary_layout metadata)) failed retained⟩

end Solcore.SourceSemantics.CoreLowering.ScalarExpressionFaultPostContracts
