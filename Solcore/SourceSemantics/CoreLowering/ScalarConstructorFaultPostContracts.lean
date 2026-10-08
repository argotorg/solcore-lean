import Solcore.SourceSemantics.CoreLowering.ScalarExpressionFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorTree

/-! Constructor fault transport retains the actual header and argument row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ScalarConstructorFaultPostContracts
open Core Frontend SourceInference CompatibleExpressionConstructors ExpressionFailurePostContracts

structure Joins (post : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (values : ValuesContext) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) : Prop where
  arguments : ∀ {id node instantiation ids tag header codes environment before reason after token mapping world store},
    Header values source id node instantiation tag header codes →
    node.form = .constructor instantiation ids →
    SourceSemantics.DataConstructorInstantiation.Valid context instantiation →
    ids.length = instantiation.payloadTypes.length →
    Nodes source ids instantiation.payloadTypes codes →
    Dynamic.ExpressionsFault program context evidence source environment before ids reason after →
    listPost program context evidence source environment before ids reason after token mapping world store →
    post program context evidence source environment before id reason after token mapping world store

theorem trivial_joins (values : ValuesContext) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    Joins TrivialExpressionPost TrivialExpressionsPost values program context evidence source where
  arguments := by intros; trivial

theorem arguments_fault_outcome {post : ExpressionFaultPost} {listPost : ExpressionsFaultPost}
    {values : ValuesContext} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    (joins : Joins post listPost values program context evidence source)
    {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation}
    {ids : List ExpressionId} {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {token : Word} {childType parentType : Ty} {mapping : GeneralHeap.LocationMap}
    {world : StoreTyping} {store : Store}
    (receipt : Header values source id node instantiation tag header codes)
    (form : node.form = .constructor instantiation ids)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    (count : ids.length = instantiation.payloadTypes.length)
    (nodes : Nodes source ids instantiation.payloadTypes codes)
    (failed : Dynamic.ExpressionsFault program context evidence source environment before ids reason after)
    (retained : ListOutcomePost listPost program context evidence source environment before ids childType
      (.error reason) after (.inLeft childType (.word token)) mapping world store) :
    OutcomePost post program context evidence source environment before id parentType
      (.fault reason) after (.inLeft parentType (.word token)) mapping world store :=
  ⟨token, rfl, joins.arguments receipt form valid count nodes failed (ListOutcomePost.fault retained)⟩

end Solcore.SourceSemantics.CoreLowering.ScalarConstructorFaultPostContracts
