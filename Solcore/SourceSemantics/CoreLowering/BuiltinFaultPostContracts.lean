import Solcore.SourceSemantics.CoreLowering.BuiltinCallSource
import Solcore.SourceSemantics.CoreLowering.CompatibleBuiltinMeaning
import Solcore.SourceSemantics.CoreLowering.DataExpressionSequence

/-! Builtin argument fault joins retain the real direct-call metadata,
ordered compiled children and original Source failure. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinFaultPostContracts
open Core Frontend SourceInference GeneralHeap CompatiblePayload ExpressionFailurePostContracts

structure Joins (post : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (values : SourceCoreCompatibleValues.Context) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) : Prop where
  arguments : ∀ {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
    {node : ExpressionNode} {codes : List SourceCoreBasic.LoweredExpr}
    {environment before reason after token mapping world store},
    CompatibleExpressionPrimitives.Metadata values.checked source id node (SourceCoreInteger.builtinResult function) →
    node.form = .call callee ids (.builtinFunction function) →
    node.type = function.returnType →
    DataExpressionSequence.Tree source certificate scope ids function.parameterTypes codes →
    codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function →
    Dynamic.ExpressionsFault program context evidence source environment before ids reason after →
    listPost program context evidence source environment before ids reason after token mapping world store →
    post program context evidence source environment before id reason after token mapping world store

theorem trivial_joins (values : SourceCoreCompatibleValues.Context) (program : Program)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    Joins TrivialExpressionPost TrivialExpressionsPost values program context evidence source where
  arguments := by intros; trivial

theorem arguments_fault_outcome {post : ExpressionFaultPost} {listPost : ExpressionsFaultPost}
    {values : SourceCoreCompatibleValues.Context} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    (joins : Joins post listPost values program context evidence source)
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
    {node : ExpressionNode} {codes : List SourceCoreBasic.LoweredExpr}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {token : Word} {parentType : Ty} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
    (form : node.form = .call callee ids (.builtinFunction function))
    (sourceType : node.type = function.returnType)
    (children : DataExpressionSequence.Tree source certificate scope ids function.parameterTypes codes)
    (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
    (failed : Dynamic.ExpressionsFault program context evidence source environment before ids reason after)
    (retained : listPost program context evidence source environment before ids reason after token mapping world store) :
    OutcomePost post program context evidence source environment before id parentType (.fault reason) after
      (.inLeft parentType (.word token)) mapping world store :=
  ⟨token, rfl, joins.arguments metadata form sourceType children nativeTypes failed retained⟩

end Solcore.SourceSemantics.CoreLowering.BuiltinFaultPostContracts
