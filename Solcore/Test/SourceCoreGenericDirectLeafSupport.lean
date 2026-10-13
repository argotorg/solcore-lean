import Solcore.Test.SourceCoreGenericDirectFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport

/-! Both selected generic bodies are genuine specialized reads. Their metadata
and terminal support come from the actual source graph and compiler receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

section Selected
variable {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    {firstType secondType : TypeSystem.Ty}
    (shape : SelectedShape row.function firstType secondType)
    (nodes : row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row)

include nodes in
private theorem selected_expression {id : ExpressionId} {node : ExpressionNode}
    (found : row.function.typedBody.lookupExpression? id = some node) : node = shape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [SelectedShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes noLocals in
theorem ActualHeader.selected_metadata (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rw [selected_expression shape nodes found]
    exact shape.read.requirements
  · intro id _ node found
    rw [actual.source] at found
    rw [selected_expression shape nodes found]
    exact shape.read.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rw [selected_expression shape nodes found, shape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem ActualHeader.selected_syntax :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source shape.read.node.id := by
  rw [actual.source]
  exact .leaf (.read shape.read.found shape.read.form)

include nodes noLocals in
theorem ActualHeader.selected_support
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = shape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.read.node.id
    shape.statement shape.roots shape.statementFound shape.statementForm
  exact ⟨terminal, expression, CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed
    (ActualHeader.selected_metadata shape nodes noLocals actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.selected_syntax shape actual) stagePrepared point⟩
end Selected

theorem ActualHeader.chooseWord_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseWordRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.chooseWordShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact ActualHeader.selected_support observed.chooseWordShape observed.chooseWordNodes observed.noLocals actual receiver stagePrepared

theorem ActualHeader.chooseBool_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseBoolRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.chooseBoolShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact ActualHeader.selected_support observed.chooseBoolShape observed.chooseBoolNodes observed.noLocals actual receiver stagePrepared

end Tests.SourceCoreGenericDirect
