import Solcore.Test.SourceCoreClosureDirectMakeSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreClosureDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private theorem make_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.makeShape.read ∨ node = observed.makeShape.call.callee.node ∨
      node = observed.makeShape.call.value.node ∨ node = observed.makeShape.expression := by
  have present := (lookupExpression?_sound found).1
  rw [observed.makeNodes] at present
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ObservedProgram.make_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (named : CallableIndexedNamedGeneration.Named)
    (assumptions : named.specialized.assumptions = []) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.makeRow.row.function.typedBody := by
  constructor
  · intro id _ node found
    rcases make_expressions observed found with same | same | same | same
    all_goals subst node
    · exact observed.makeShape.readRequirements
    · exact observed.makeShape.call.callee.requirements
    · exact observed.makeShape.call.value.requirements
    · exact observed.makeShape.requirements
  · intro id _ node found
    rcases make_expressions observed found with same | same | same | same
    all_goals subst node
    · exact observed.makeShape.readCoercions
    · exact observed.makeShape.call.callee.coercions
    · exact observed.makeShape.call.value.coercions
    · exact observed.makeShape.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases make_expressions observed found with same | same | same | same
    all_goals subst node
    · rw [observed.makeShape.readForm] at form; cases form
    · rw [observed.makeShape.call.calleeForm] at form; cases form
    · rw [observed.makeShape.call.form] at form; cases form
    · rw [observed.makeShape.lambda] at form; cases form
  · intro _ _ _ _ _ _ _ _
    exact assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ObservedProgram.make_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    GeneralSyntax observed.makeRow.row.function.typedBody observed.makeShape.call.value.node.id := by
  refine .direct observed.makeShape.call.value.found observed.makeShape.call.form ?_ ?_
  · rw [observed.makeShape.call.exact]
    exact ⟨rfl, rfl⟩
  · intro child member
    cases List.mem_singleton.mp member
    exact .leaf (.read observed.makeShape.readFound observed.makeShape.readForm)

end Tests.SourceCoreClosureDirect
