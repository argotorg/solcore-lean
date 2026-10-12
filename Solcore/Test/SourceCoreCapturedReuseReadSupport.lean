import Solcore.Test.SourceCoreCapturedReuseFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport

/-! The observed read(f) program supplies its entire named body support from
its two actual expression rows. No call readiness, Source execution or payload
representation is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem read_expression {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.readRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.readShape.callee ∨ node = observed.readShape.call := by
  have present := (lookupExpression?_sound found).1
  rw [observed.readNodes] at present
  rcases List.mem_cons.mp present with same | rest
  · exact Or.inl (Node.expression.inj same)
  · rcases List.mem_cons.mp rest with same | rest
    · exact Or.inr (Node.expression.inj same)
    · rcases List.mem_cons.mp rest with impossible | empty
      · cases impossible
      · cases empty

/-- Empty local catalogs and the complete original occurrence table establish
all metadata exclusions in the recursive caller grammar. -/
theorem ActualHeader.read_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rcases read_expression observed found with same | same
    · rw [same]; exact observed.readShape.calleeRequirements
    · rw [same]; exact observed.readShape.callRequirements
  · intro id _ node found
    rw [actual.source] at found
    rcases read_expression observed found with same | same
    · rw [same]; exact observed.readShape.calleeCoercions
    · rw [same]; exact observed.readShape.callCoercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rcases read_expression observed found with same | same
    · rw [same, observed.readShape.calleeForm] at form
      cases form
    · rw [same, observed.readShape.callForm] at form
      cases form
      rw [observed.readShape.application]
  · intro id _ node found name binder form
    simp only [observed.noLocals, List.any_nil]

/-- The exact terminal call has one local-read child and no argument children. -/
theorem ActualHeader.read_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source observed.readShape.call.id := by
  rw [actual.source]
  exact .call observed.readShape.callFound observed.readShape.callForm
    (.leaf (.read observed.readShape.calleeFound observed.readShape.calleeForm))
    (by intro id member; cases member)

/-- All finite metadata, original typing and selected scope premises of the
compiler producer are derived from this concrete checked/compiled fixture. -/
theorem ActualHeader.read_support_at {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.readShape.call.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {completion : SourceCoreCallableIndexedPrograms.Completion fixture.recipe.compiled.indexed}
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
    {completion : SourceCoreCallableIndexedPrograms.Completion fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.readShape.call.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.readShape.call.id
    observed.readShape.statement observed.readShape.roots observed.readShape.statementFound observed.readShape.statementForm
  exact ⟨terminal, expression, ActualHeader.read_support_at observed actual terminal diagnostic expression point receiver stagePrepared⟩

end Tests.SourceCoreCapturedReuse
