import Solcore.Test.SourceCoreBuiltinCallsFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
import Solcore.Test.SourceCoreBuiltinCallsMakeSupport

/-! Finite original Source facts for nested named calls and a real builtin sibling. The
synthetic callee references carry static catalog metadata; only the original
ordered argument expressions are evaluated recursively. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreBuiltinCalls
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private theorem relay_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.relayRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.relayShape.read.node ∨
    node = observed.relayShape.inner.callee.node ∨
    node = observed.relayShape.inner.value.node ∨
    node = observed.relayShape.zero.node ∨
    node = observed.relayShape.converted.callee.node ∨
    node = observed.relayShape.converted.value.node ∨
    node = observed.relayShape.sum.node ∨
    node = observed.relayShape.outer.callee.node ∨
    node = observed.relayShape.outer.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.relayNodes] at present
  simpa only [RelayShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.relay_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayRow.row)
    (named : CallableIndexedNamedGeneration.Named)
    (same : named.specialized = observed.relayRow.row) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rcases relay_expressions observed found with same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact .inl observed.relayShape.read.requirements
    · exact .inl observed.relayShape.inner.callee.requirements
    · exact .inl observed.relayShape.inner.value.requirements
    · exact .inr ⟨_, _, observed.relayShape.zero.form⟩
    · exact .inl observed.relayShape.converted.callee.requirements
    · exact .inl observed.relayShape.converted.value.requirements
    · exact .inl observed.relayShape.sum.requirements
    · exact .inl observed.relayShape.outer.callee.requirements
    · exact .inl observed.relayShape.outer.value.requirements
  · intro id _ node found
    rw [actual.source] at found
    rcases relay_expressions observed found with same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.relayShape.read.coercions
    · exact observed.relayShape.inner.callee.coercions
    · exact observed.relayShape.inner.value.coercions
    · exact (SourceCoreElaboration.validateNativeIntegerLiteral_sound observed.relayShape.zero.accepted).coercions
    · exact observed.relayShape.converted.callee.coercions
    · exact observed.relayShape.converted.value.coercions
    · exact observed.relayShape.sum.coercions
    · exact observed.relayShape.outer.callee.coercions
    · exact observed.relayShape.outer.value.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rcases relay_expressions observed found with same | same | same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.relayShape.read.form] at form
      cases form
    · rw [observed.relayShape.inner.calleeForm] at form
      cases form
    · rw [observed.relayShape.inner.form] at form
      cases form
    · rw [observed.relayShape.zero.form] at form
      cases form
    · rw [observed.relayShape.converted.calleeForm] at form
      cases form
    · rw [observed.relayShape.converted.form] at form
      cases form
    · rw [observed.relayShape.sumForm] at form
      cases form
    · rw [observed.relayShape.outer.calleeForm] at form
      cases form
    · rw [observed.relayShape.outer.form] at form
      cases form
  · intro _ _ _ _ _ _ _ _
    rw [same]
    exact observed.relayRow.assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.relay_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayRow.row) :
    GeneralSyntax actual.header.function.source observed.relayShape.outer.value.node.id := by
  rw [actual.source]
  refine .direct observed.relayShape.outer.value.found observed.relayShape.outer.form ?_ ?_
  · rw [observed.relayShape.outer.exact]
    exact ⟨rfl, rfl⟩
  · intro child member
    cases List.mem_singleton.mp member
    refine .binary observed.relayShape.sum.found observed.relayShape.sumForm ?_ ?_
    · refine .direct observed.relayShape.inner.value.found observed.relayShape.inner.form ?_ ?_
      · rw [observed.relayShape.inner.exact]
        exact ⟨rfl, rfl⟩
      · intro child member
        cases List.mem_singleton.mp member
        exact .leaf (.read observed.relayShape.read.found observed.relayShape.read.form)
    · refine .builtin observed.relayShape.converted.value.found observed.relayShape.converted.form ?_
      intro child member
      cases List.mem_singleton.mp member
      exact .leaf (.literal observed.relayShape.zero.found (observed.relayShape.zero.form ▸ .integer _ _))

/-- The same authentic finite inventory supplies every reached direct-call
port. No called-body law or current globals value is a static premise. -/
theorem ActualHeader.relay_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayRow.row)
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
      terminal.expression = observed.relayShape.outer.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.relayShape.outer.value.node.id
    observed.relayShape.statement observed.relayShape.roots observed.relayShape.statementFound observed.relayShape.statementForm
  have same : terminal.prepared.named.specialized = observed.relayRow.row :=
    (congrArg (·.specialized) (terminal.aligned.named.symm.trans actual.aligned.named)).trans actual.prepared.same
  exact ⟨terminal, expression, CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport.of_actual_native
    terminal diagnostic receiver fixture.source_wellFormed (actual.relay_metadata observed terminal.prepared.named same)
    (by rw [expression]; exact actual.relay_syntax observed) rows complete
    (bootstrap_zero fixture.recipe.compiled) stagePrepared point⟩

end Tests.SourceCoreBuiltinCalls
