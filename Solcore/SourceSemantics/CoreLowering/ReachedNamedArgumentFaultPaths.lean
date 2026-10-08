import Solcore.SourceSemantics.CoreLowering.NamedArgumentFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.ReachedBuiltinExpressionFaultPaths

/-! The named parent adds one genuine direct-argument edge to the original
builtin list path. The primitive leaf, model and native transport stay exact. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedNamedArgumentFaultPaths
open Core Frontend SourceInference GeneralHeap CompatiblePayload ExpressionFailurePostContracts
open ReachedExpressionFaultOrigins (PrimitiveOrigin NativeTransport)
open ReachedExpressionPrimitiveOutcomeProviders (ModelAssociation)

inductive ExpressionPath : {heap : Dynamic.Heap} → {reason : Dynamic.SemanticFault} → {token : Word} →
    PrimitiveOrigin heap reason token → Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
    TypedSource → Dynamic.Environment → Dynamic.Heap → ExpressionId → Prop where
  | arguments {heap : Dynamic.Heap} {reason : Dynamic.SemanticFault} {token : Word}
      {origin : PrimitiveOrigin heap reason token} {program : Program} {context : SourceSemantics.Context}
      {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
      {before : Dynamic.Heap} {id callee : ExpressionId} {ids : List ExpressionId}
      {node calleeNode : ExpressionNode} {instantiation : DeclarationInstantiation} {name : String}
      (parent : ContainsExpression source id node)
      (form : node.form = .call callee ids (.declaration instantiation))
      (calleeContains : ContainsExpression source callee calleeNode)
      (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
      (failed : Dynamic.ExpressionsFault program context evidence source environment before ids reason heap)
      (children : ReachedBuiltinExpressionFaultPaths.ExpressionsPath origin program context evidence source environment before ids) :
      ExpressionPath origin program context evidence source environment before id

def model_expressionPost (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ExpressionFaultPost :=
  fun program context evidence source environment before id reason after token mapping world _store =>
    ∃ origin : PrimitiveOrigin after reason token,
      ExpressionPath origin program context evidence source environment before id ∧
      NativeTransport origin registry mapping world ∧ ModelAssociation checked functions origin

theorem arguments_join (checked : SourceCoreCompatibleCatalog.Checked)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    NamedArgumentFaultPostContracts.ArgumentsJoin (model_expressionPost checked functions registry)
      (ReachedBuiltinExpressionFaultPaths.model_expressionsPost checked functions registry)
      program context evidence source where
  arguments := by
    intro id callee ids node calleeNode instantiation name environment before after reason token mapping world store
      parent form calleeContains calleeForm failed post
    obtain ⟨origin, path, native, associated⟩ := post
    exact ⟨origin, .arguments parent form calleeContains calleeForm failed path, native, associated⟩

end Solcore.SourceSemantics.CoreLowering.ReachedNamedArgumentFaultPaths
