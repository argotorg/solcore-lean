import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.Test.SourceCoreRecursiveIndexFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport

/-! The actual echo and choose rows are compiler-produced read bodies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem echo_expression {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.echoRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.echoShape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.echoNodes] at present
  simpa only [IdentityShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.echo_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.echoRow.row)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rw [echo_expression observed found]
    exact observed.echoShape.read.requirements
  · intro id _ node found
    rw [actual.source] at found
    rw [echo_expression observed found]
    exact observed.echoShape.read.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rw [echo_expression observed found, observed.echoShape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.echo_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.echoRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source observed.echoShape.read.node.id := by
  rw [actual.source]
  exact .leaf (.read observed.echoShape.read.found observed.echoShape.read.form)

/-- All finite metadata, original typing and selected scope premises of the
compiler producer are derived from this concrete checked/compiled fixture. -/
theorem ActualHeader.echo_support_at {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.echoRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.echoShape.read.node.id)
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
    terminal diagnostic receiver fixture.source_wellFormed (ActualHeader.echo_metadata observed actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.echo_syntax observed actual) stagePrepared point

/-- The actual terminal lowering supplies its own Point certificate and
preparation packet before the concrete support producer is invoked. -/
theorem ActualHeader.echo_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.echoRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.echoShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.echoShape.read.node.id
    observed.echoShape.statement observed.echoShape.roots observed.echoShape.statementFound observed.echoShape.statementForm
  exact ⟨terminal, expression, ActualHeader.echo_support_at observed actual terminal diagnostic expression point receiver stagePrepared⟩

private theorem choose_expression {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.chooseRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.chooseShape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.chooseNodes] at present
  simpa only [IdentityShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.choose_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseRow.row)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rw [choose_expression observed found]
    exact observed.chooseShape.read.requirements
  · intro id _ node found
    rw [actual.source] at found
    rw [choose_expression observed found]
    exact observed.chooseShape.read.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rw [choose_expression observed found, observed.chooseShape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.choose_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source observed.chooseShape.read.node.id := by
  rw [actual.source]
  exact .leaf (.read observed.chooseShape.read.found observed.chooseShape.read.form)

/-- All finite metadata, original typing and selected scope premises of the
compiler producer are derived from this concrete checked/compiled fixture. -/
theorem ActualHeader.choose_support_at {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.chooseShape.read.node.id)
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
    terminal diagnostic receiver fixture.source_wellFormed (ActualHeader.choose_metadata observed actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.choose_syntax observed actual) stagePrepared point

/-- The actual terminal lowering supplies its own Point certificate and
preparation packet before the concrete support producer is invoked. -/
theorem ActualHeader.choose_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.chooseShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.chooseShape.read.node.id
    observed.chooseShape.statement observed.chooseShape.roots observed.chooseShape.statementFound observed.chooseShape.statementForm
  exact ⟨terminal, expression, ActualHeader.choose_support_at observed actual terminal diagnostic expression point receiver stagePrepared⟩

end Tests.SourceCoreRecursiveIndex
