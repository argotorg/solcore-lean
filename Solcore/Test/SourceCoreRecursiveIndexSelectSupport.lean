import Solcore.Test.SourceCoreRecursiveIndexFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
import Solcore.Test.SourceCoreRecursiveIndexMakeSupport

/-! Finite original Source facts for recursive index and its direct declaration children. The
synthetic callee references carry static catalog metadata; only the original
ordered argument expressions are evaluated recursively. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private theorem select_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.selectRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.selectShape.tableRead.node ∨
      node = observed.selectShape.base.callee.node ∨
      node = observed.selectShape.base.value.node ∨
      node = observed.selectShape.keyRead.node ∨
      node = observed.selectShape.lookup.callee.node ∨
      node = observed.selectShape.lookup.value.node ∨
      node = observed.selectShape.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.selectNodes] at present
  simpa only [SelectShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.select_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.selectRow.row)
    (named : CallableIndexedNamedGeneration.Named) (same : named.specialized = observed.selectRow.row) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rcases select_expressions observed found with same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.selectShape.tableRead.requirements
    · exact observed.selectShape.base.callee.requirements
    · exact observed.selectShape.base.value.requirements
    · exact observed.selectShape.keyRead.requirements
    · exact observed.selectShape.lookup.callee.requirements
    · exact observed.selectShape.lookup.value.requirements
    · exact observed.selectShape.value.requirements
  · intro id _ node found
    rw [actual.source] at found
    rcases select_expressions observed found with same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.selectShape.tableRead.coercions
    · exact observed.selectShape.base.callee.coercions
    · exact observed.selectShape.base.value.coercions
    · exact observed.selectShape.keyRead.coercions
    · exact observed.selectShape.lookup.callee.coercions
    · exact observed.selectShape.lookup.value.coercions
    · exact observed.selectShape.value.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rcases select_expressions observed found with same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.selectShape.tableRead.form] at form; cases form
    · rw [observed.selectShape.base.calleeForm] at form; cases form
    · rw [observed.selectShape.base.form] at form; cases form
    · rw [observed.selectShape.keyRead.form] at form; cases form
    · rw [observed.selectShape.lookup.calleeForm] at form; cases form
    · rw [observed.selectShape.lookup.form] at form; cases form
    · rw [observed.selectShape.form] at form; cases form
  · intro _ _ _ _ _ _ _ _
    rw [same]; exact observed.selectRow.assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.select_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.selectRow.row) :
    GeneralSyntax actual.header.function.source observed.selectShape.value.node.id := by
  rw [actual.source]
  refine .index observed.selectShape.value.found observed.selectShape.form
    observed.selectShape.lookup.value.found ?_ ?_ ?_
  · rw [observed.selectShape.lookup.value.type]
    exact .word
  · refine .direct observed.selectShape.base.value.found observed.selectShape.base.form ?_ ?_
    · rw [observed.selectShape.base.exact]; exact ⟨rfl, rfl⟩
    · intro child member
      cases List.mem_singleton.mp member
      exact .leaf (.read observed.selectShape.tableRead.found observed.selectShape.tableRead.form)
  · refine .direct observed.selectShape.lookup.value.found observed.selectShape.lookup.form ?_ ?_
    · rw [observed.selectShape.lookup.exact]; exact ⟨rfl, rfl⟩
    · intro child member
      cases List.mem_singleton.mp member
      exact .leaf (.read observed.selectShape.keyRead.found observed.selectShape.keyRead.form)

/-- The same authentic finite inventory supplies every reached direct-call
port. No called-body law or current globals value is a static premise. -/
theorem ActualHeader.select_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.selectRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.selectShape.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.selectShape.value.node.id
    observed.selectShape.statement observed.selectShape.roots observed.selectShape.statementFound observed.selectShape.statementForm
  have same : terminal.prepared.named.specialized = observed.selectRow.row :=
    (congrArg (·.specialized) (terminal.aligned.named.symm.trans actual.aligned.named)).trans actual.prepared.same
  exact ⟨terminal, expression, CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (actual.select_metadata observed terminal.prepared.named same)
    (by rw [expression]; exact actual.select_syntax observed) rows complete
    (bootstrap_zero fixture.recipe.compiled) stagePrepared point⟩

end Tests.SourceCoreRecursiveIndex
