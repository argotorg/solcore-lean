import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.Test.SourceCoreConstructorCallsFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport

/-! The observed constructor body supplies its named support from the actual
recursive expression tree, including an indirect call in the first payload.
No Source execution or payload representation is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem read_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.readRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.readShape.argumentRead.node ∨ node = observed.readShape.factoryRead.node ∨ node = observed.readShape.call.node ∨ node = observed.readShape.priorRead.node ∨ node = observed.readShape.retainedFactoryRead.node ∨ node = observed.readShape.convertRead.node ∨ node = observed.readShape.expression.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.readNodes] at present
  simpa only [ReadShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.read_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rcases read_expressions observed found with same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.readShape.argumentRead.requirements
    · exact observed.readShape.factoryRead.requirements
    · exact observed.readShape.call.requirements
    · exact observed.readShape.priorRead.requirements
    · exact observed.readShape.retainedFactoryRead.requirements
    · exact observed.readShape.convertRead.requirements
    · exact observed.readShape.expression.requirements
  · intro id _ node found
    rw [actual.source] at found
    rcases read_expressions observed found with same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.readShape.argumentRead.coercions
    · exact observed.readShape.factoryRead.coercions
    · exact observed.readShape.call.coercions
    · exact observed.readShape.priorRead.coercions
    · exact observed.readShape.retainedFactoryRead.coercions
    · exact observed.readShape.convertRead.coercions
    · exact observed.readShape.expression.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rcases read_expressions observed found with same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.readShape.argumentRead.form] at form
      cases form
    · rw [observed.readShape.factoryRead.form] at form
      cases form
    · rw [observed.readShape.callForm] at form
      have same := (ExpressionForm.call.inj form).2.2
      cases same
      rw [observed.readShape.applicationEq]
    · rw [observed.readShape.priorRead.form] at form
      cases form
    · rw [observed.readShape.retainedFactoryRead.form] at form
      cases form
    · rw [observed.readShape.convertRead.form] at form
      cases form
    · rw [observed.readShape.expressionForm] at form
      cases form
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.read_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source observed.readShape.expression.node.id := by
  rw [actual.source]
  apply CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax.constructor
    observed.readShape.expression.found observed.readShape.expressionForm
  · rw [observed.readShape.instantiationEq]
    intro parameter type member
    cases member
  · intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact .call observed.readShape.call.found observed.readShape.callForm
        (.leaf (.read observed.readShape.factoryRead.found observed.readShape.factoryRead.form))
        (by intro id member; cases List.mem_singleton.mp member
            exact .leaf (.read observed.readShape.argumentRead.found observed.readShape.argumentRead.form))
    · exact .leaf (.read observed.readShape.priorRead.found observed.readShape.priorRead.form)
    · exact .leaf (.read observed.readShape.retainedFactoryRead.found observed.readShape.retainedFactoryRead.form)
    · exact .leaf (.read observed.readShape.convertRead.found observed.readShape.convertRead.form)

/-- All finite metadata, original typing and selected scope premises of the
compiler producer are derived from this concrete checked/compiled fixture. -/
theorem ActualHeader.read_support_at {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.readShape.expression.node.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (ActualHeader.read_metadata observed actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.read_syntax observed actual) stagePrepared point

/-- The actual terminal lowering supplies its own Point certificate and
preparation packet before the concrete support producer is invoked. -/
theorem ActualHeader.read_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.readShape.expression.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.readShape.expression.node.id
    observed.readShape.statement observed.readShape.roots observed.readShape.statementFound observed.readShape.statementForm
  exact ⟨terminal, expression, ActualHeader.read_support_at observed actual terminal diagnostic expression point receiver stagePrepared⟩

end Tests.SourceCoreConstructorCalls
