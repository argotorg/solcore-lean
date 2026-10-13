import Solcore.Test.SourceCoreCanonicalScopedSyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

theorem ObservedProgram.make_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.makeShape.initialRead.node ∨ node = observed.makeShape.initial.callee.node ∨ node = observed.makeShape.initial.value.node ∨ node = observed.makeShape.conditionRead.node ∨ node = observed.makeShape.argumentRead.node ∨ node = observed.makeShape.updated.callee.node ∨ node = observed.makeShape.updated.value.node ∨ node = observed.makeShape.stopRead.node ∨ node = observed.makeShape.previousRead.node ∨ node = observed.makeShape.final.callee.node ∨ node = observed.makeShape.final.value.node ∨ node = observed.makeShape.expression := by
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
    rcases observed.make_expressions found with same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.makeShape.initialRead.requirements
    · exact observed.makeShape.initial.callee.requirements
    · exact observed.makeShape.initial.value.requirements
    · exact observed.makeShape.conditionRead.requirements
    · exact observed.makeShape.argumentRead.requirements
    · exact observed.makeShape.updated.callee.requirements
    · exact observed.makeShape.updated.value.requirements
    · exact observed.makeShape.stopRead.requirements
    · exact observed.makeShape.previousRead.requirements
    · exact observed.makeShape.final.callee.requirements
    · exact observed.makeShape.final.value.requirements
    · exact observed.makeShape.requirements
  · intro id _ node found
    rcases observed.make_expressions found with same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.makeShape.initialRead.coercions
    · exact observed.makeShape.initial.callee.coercions
    · exact observed.makeShape.initial.value.coercions
    · exact observed.makeShape.conditionRead.coercions
    · exact observed.makeShape.argumentRead.coercions
    · exact observed.makeShape.updated.callee.coercions
    · exact observed.makeShape.updated.value.coercions
    · exact observed.makeShape.stopRead.coercions
    · exact observed.makeShape.previousRead.coercions
    · exact observed.makeShape.final.callee.coercions
    · exact observed.makeShape.final.value.coercions
    · exact observed.makeShape.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases observed.make_expressions found with same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.makeShape.initialRead.form] at form; cases form
    · rw [observed.makeShape.initial.calleeForm] at form; cases form
    · rw [observed.makeShape.initial.form] at form; cases form
    · rw [observed.makeShape.conditionRead.form] at form; cases form
    · rw [observed.makeShape.argumentRead.form] at form; cases form
    · rw [observed.makeShape.updated.calleeForm] at form; cases form
    · rw [observed.makeShape.updated.form] at form; cases form
    · rw [observed.makeShape.stopRead.form] at form; cases form
    · rw [observed.makeShape.previousRead.form] at form; cases form
    · rw [observed.makeShape.final.calleeForm] at form; cases form
    · rw [observed.makeShape.final.form] at form; cases form
    · rw [observed.makeShape.lambda] at form; cases form
  · intro _ _ _ _ _ _ _ _
    exact assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ObservedProgram.relay_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.relayRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.relayShape.initialRead.node ∨ node = observed.relayShape.initial.callee.node ∨ node = observed.relayShape.initial.value.node ∨ node = observed.relayShape.finalRead.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.relayNodes] at present
  simpa only [RelayShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ObservedProgram.relay_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (named : CallableIndexedNamedGeneration.Named)
    (assumptions : named.specialized.assumptions = []) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.relayRow.row.function.typedBody := by
  constructor
  · intro id _ node found
    rcases observed.relay_expressions found with same | same | same | same
    all_goals subst node
    · exact observed.relayShape.initialRead.requirements
    · exact observed.relayShape.initial.callee.requirements
    · exact observed.relayShape.initial.value.requirements
    · exact observed.relayShape.finalRead.requirements
  · intro id _ node found
    rcases observed.relay_expressions found with same | same | same | same
    all_goals subst node
    · exact observed.relayShape.initialRead.coercions
    · exact observed.relayShape.initial.callee.coercions
    · exact observed.relayShape.initial.value.coercions
    · exact observed.relayShape.finalRead.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases observed.relay_expressions found with same | same | same | same
    all_goals subst node
    · rw [observed.relayShape.initialRead.form] at form; cases form
    · rw [observed.relayShape.initial.calleeForm] at form; cases form
    · rw [observed.relayShape.initial.form] at form; cases form
    · rw [observed.relayShape.finalRead.form] at form; cases form
  · intro _ _ _ _ _ _ _ _
    exact assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem DirectCall.syntax {source : TypedSource} {signature : ProgramFunctionSignature}
    {argument : ExpressionId} {parameter result : TypeSystem.Ty}
    (call : DirectCall source signature argument parameter result)
    (child : GeneralSyntax source argument) : GeneralSyntax source call.value.node.id := by
  refine .direct call.value.found call.form ?_ ?_
  · rw [call.exact]; exact ⟨rfl, rfl⟩
  · intro id member
    cases List.mem_singleton.mp member
    exact child

theorem ObservedProgram.make_children {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∀ id ∈ observed.childIds, GeneralSyntax observed.makeRow.row.function.typedBody id := by
  intro id member
  simp only [childIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact observed.makeShape.initial.syntax (.leaf (.read observed.makeShape.initialRead.found observed.makeShape.initialRead.form))
  · exact .leaf (.read observed.makeShape.conditionRead.found observed.makeShape.conditionRead.form)
  · exact observed.makeShape.updated.syntax (.leaf (.read observed.makeShape.argumentRead.found observed.makeShape.argumentRead.form))
  · exact .leaf (.read observed.makeShape.stopRead.found observed.makeShape.stopRead.form)
  · exact observed.makeShape.final.syntax (.leaf (.read observed.makeShape.previousRead.found observed.makeShape.previousRead.form))

theorem ObservedProgram.relay_initial_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    GeneralSyntax observed.relayRow.row.function.typedBody observed.relayShape.initial.value.node.id :=
  observed.relayShape.initial.syntax (.leaf (.read observed.relayShape.initialRead.found observed.relayShape.initialRead.form))

end Tests.SourceCoreCanonicalScoped
