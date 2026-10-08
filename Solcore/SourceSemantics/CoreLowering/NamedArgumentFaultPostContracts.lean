import Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts
import Solcore.SourceSemantics.CoreLowering.SourceExecutionSize

/-! A named argument failure keeps its genuine parent and callee occurrences.
The finite join uses the same failed list and reached semantic tuple. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedArgumentFaultPostContracts
open Core Frontend SourceInference GeneralHeap ExpressionFailurePostContracts

structure ArgumentsJoin (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) : Prop where
  arguments : ∀ {id callee : ExpressionId} {ids : List ExpressionId} {node calleeNode : ExpressionNode}
    {instantiation : DeclarationInstantiation} {name : String}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {token : Word} {mapping : LocationMap} {world : StoreTyping} {store : Store},
    ContainsExpression source id node → node.form = .call callee ids (.declaration instantiation) →
    ContainsExpression source callee calleeNode →
    calleeNode.form = .reference name (.declaration instantiation) →
    Dynamic.ExpressionsFault program context evidence source environment before ids reason after →
    listPost program context evidence source environment before ids reason after token mapping world store →
    expressionPost program context evidence source environment before id reason after token mapping world store

/-- Only the two original Source constructors are used. The sized list proof
is retained directly, without measuring or searching its failure again. -/
theorem source_fault {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {id callee : ExpressionId} {ids : List ExpressionId} {node calleeNode : ExpressionNode}
    {instantiation : DeclarationInstantiation} {name : String}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {size : Nat}
    (parent : ContainsExpression source id node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (calleeContains : ContainsExpression source callee calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (failed : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) :
    SourceExecutionSize.ExpressionFaults program
      (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [size]])
      context evidence source environment before id reason after := by
  exact .form parent (form ▸ .directArguments calleeContains calleeForm failed)

end Solcore.SourceSemantics.CoreLowering.NamedArgumentFaultPostContracts
