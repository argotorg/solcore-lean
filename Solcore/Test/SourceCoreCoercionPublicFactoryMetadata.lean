import Solcore.Test.SourceCoreCoercionPublicMetadata
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor)

variable {function : CheckedFunction} {signature generic : ProgramFunctionSignature}
  {parameter : TypeSystem.TypeParameterId} {mark coercion : ProgramTraitSignature}
  (shape : FactoryShape function signature generic parameter mark coercion)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem FactoryShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.read.node ∨ node = shape.call.callee.node ∨ node = shape.call.node ∨
      node = shape.expression.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
/-- Only the actual uncoerced argument grammar is admitted by this profile.
The original constrained call remains outside that grammar. -/
theorem FactoryShape.native_metadata {fixture : CompiledFixture}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    NativeMetadataFor fixture.recipe.compiled.indexed named function.typedBody (fun _ => False) := by
  constructor
  · intro id tree node found
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · exact .inl shape.read.requirements
    · exact .inl shape.call.callee.requirements
    · exact False.elim (tree.direct_site found shape.call.form)
    · exact .inl shape.expression.requirements
  · intro id tree node found
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · exact shape.read.coercions
    · exact shape.call.callee.coercions
    · exact False.elim (tree.direct_site found shape.call.form)
    · exact shape.expression.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · rw [shape.read.form] at form; cases form
    · rw [shape.call.calleeForm] at form; cases form
    · rw [shape.call.form] at form; cases form
    · rw [shape.lambda] at form; cases form
  · intro id tree node found callee ids instantiation form
    exact False.elim (tree.direct_site found form)
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem FactoryShape.children : ∀ id ∈ [shape.read.node.id],
    GeneralSyntax function.typedBody id (fun _ => False) := by
  intro id member
  have same := List.mem_singleton.mp member
  subst id
  exact .leaf (.read shape.read.found shape.read.form)

end Tests.SourceCoreCoercionPublic
