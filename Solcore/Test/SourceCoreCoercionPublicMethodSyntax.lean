import Solcore.Test.SourceCoreCoercionPublicFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

variable {function : CheckedFunction} {signature : ProgramFunctionSignature}
  (shape : MethodShape function signature) (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem MethodShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.read.node ∨ node = shape.first.node ∨ node = shape.second.node ∨ node = shape.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [MethodShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem MethodShape.primitive_source :
    CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport.PrimitiveSource function.typedBody := by
  intro id node found
  rcases shape.expressions nodes found with rfl | rfl | rfl | rfl
  · exact .inl ⟨_, _, shape.read.form⟩
  · exact .inr (.inl ⟨_, _, shape.first.form⟩)
  · exact .inr (.inl ⟨_, _, shape.second.form⟩)
  · exact .inr (.inr ⟨_, _, _, shape.conditional⟩)

include nodes in
theorem MethodShape.metadata {fixture : CompiledFixture}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody (fun _ => False) := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with rfl | rfl | rfl | rfl
    · exact .inl shape.read.requirements
    · exact .inr (.inl ⟨_, _, shape.first.form⟩)
    · exact .inr (.inl ⟨_, _, shape.second.form⟩)
    · exact .inl shape.value.requirements
  · intro id _ node found
    rcases shape.expressions nodes found with rfl | rfl | rfl | rfl
    · exact shape.read.coercions
    · exact (SourceCoreElaboration.validateWordIntegerLiteral_sound shape.first.accepted).coercions
    · exact (SourceCoreElaboration.validateWordIntegerLiteral_sound shape.second.accepted).coercions
    · exact shape.value.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases shape.expressions nodes found with rfl | rfl | rfl | rfl
    · rw [shape.read.form] at form; cases form
    · rw [shape.first.form] at form; cases form
    · rw [shape.second.form] at form; cases form
    · rw [shape.conditional] at form; cases form
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem MethodShape.syntax : GeneralSyntax function.typedBody shape.value.node.id (fun _ => False) := by
  refine .conditional shape.value.found shape.conditional (.leaf (.read shape.read.found shape.read.form)) ?_ ?_
  · exact .leaf (.literal shape.first.found (shape.first.form ▸ .integer _ _))
  · exact .leaf (.literal shape.second.found (shape.second.form ▸ .integer _ _))

end Tests.SourceCoreCoercionPublic
