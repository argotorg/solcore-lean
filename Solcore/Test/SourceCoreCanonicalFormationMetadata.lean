import Solcore.Test.SourceCoreCanonicalFormationFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

theorem ObservedProgram.make_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.makeShape.initialRead.node ∨ node = observed.makeShape.initial.callee.node ∨ node = observed.makeShape.initial.value.node ∨ node = observed.makeShape.read.node ∨ node = observed.makeShape.call.callee.node ∨ node = observed.makeShape.call.value.node ∨ node = observed.makeShape.expression := by
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
    rcases observed.make_expressions found with same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.makeShape.initialRead.requirements
    · exact observed.makeShape.initial.callee.requirements
    · exact observed.makeShape.initial.value.requirements
    · exact observed.makeShape.read.requirements
    · exact observed.makeShape.call.callee.requirements
    · exact observed.makeShape.call.value.requirements
    · exact observed.makeShape.requirements
  · intro id _ node found
    rcases observed.make_expressions found with same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.makeShape.initialRead.coercions
    · exact observed.makeShape.initial.callee.coercions
    · exact observed.makeShape.initial.value.coercions
    · exact observed.makeShape.read.coercions
    · exact observed.makeShape.call.callee.coercions
    · exact observed.makeShape.call.value.coercions
    · exact observed.makeShape.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases observed.make_expressions found with same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.makeShape.initialRead.form] at form; cases form
    · rw [observed.makeShape.initial.calleeForm] at form; cases form
    · rw [observed.makeShape.initial.form] at form; cases form
    · rw [observed.makeShape.read.form] at form; cases form
    · rw [observed.makeShape.call.calleeForm] at form; cases form
    · rw [observed.makeShape.call.form] at form; cases form
    · rw [observed.makeShape.lambda] at form; cases form
  · intro _ _ _ _ _ _ _ _
    exact assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ObservedProgram.relay_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.relayRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.relayShape.read.node ∨ node = observed.relayShape.call.callee.node ∨ node = observed.relayShape.call.value.node := by
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
    rcases observed.relay_expressions found with same | same | same
    all_goals subst node
    · exact observed.relayShape.read.requirements
    · exact observed.relayShape.call.callee.requirements
    · exact observed.relayShape.call.value.requirements
  · intro id _ node found
    rcases observed.relay_expressions found with same | same | same
    all_goals subst node
    · exact observed.relayShape.read.coercions
    · exact observed.relayShape.call.callee.coercions
    · exact observed.relayShape.call.value.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases observed.relay_expressions found with same | same | same
    all_goals subst node
    · rw [observed.relayShape.read.form] at form; cases form
    · rw [observed.relayShape.call.calleeForm] at form; cases form
    · rw [observed.relayShape.call.form] at form; cases form
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

theorem ObservedProgram.make_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    GeneralSyntax observed.makeRow.row.function.typedBody observed.makeShape.call.value.node.id :=
  observed.makeShape.call.syntax (.leaf (.read observed.makeShape.read.found observed.makeShape.read.form))

theorem ObservedProgram.make_initial_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    GeneralSyntax observed.makeRow.row.function.typedBody observed.makeShape.initial.value.node.id :=
  observed.makeShape.initial.syntax (.leaf (.read observed.makeShape.initialRead.found observed.makeShape.initialRead.form))

theorem ObservedProgram.relay_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    GeneralSyntax observed.relayRow.row.function.typedBody observed.relayShape.call.value.node.id :=
  observed.relayShape.call.syntax (.leaf (.read observed.relayShape.read.found observed.relayShape.read.form))

end Tests.SourceCoreCanonicalFormation
