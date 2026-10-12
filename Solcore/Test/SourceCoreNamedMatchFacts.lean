import Solcore.Test.SourceCoreNamedMatchFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadLambdaMetadata
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds

/-! Finite observations identify all original reads and exclude anonymous code.
They establish compiler coverage without an execution or body-meaning premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.input_types {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word, .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.shape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.shape.valueScheme, observed.shape.argumentScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.result_type {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

theorem ActualHeader.output {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.result_type] at projected
  exact (Except.ok.inj projected).symm

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

theorem ObservedFactory.read_cases {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node) :
    node = observed.shape.initialRead.node ∨ node = observed.shape.localRead.node ∨ node = observed.shape.finalRead.node := by
  have member := found.1
  rw [observed.nodes] at member
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton, Node.expression.injEq,
    reduceCtorEq, List.not_mem_nil, false_or, or_false] using member

theorem ObservedFactory.metadata {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.row.function.typedBody := by
  apply CallableIndexedOwnedPreparedStagedReadLambdaMetadata.metadata _ named _ observed.noLocals
  intro id node found
  rcases observed.read_cases (lookupExpression?_sound found) with same | same | same
  all_goals subst node
  · exact .inl ⟨_, _, observed.shape.initialRead.form, observed.shape.initialRead.requirements, observed.shape.initialRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.localRead.form, observed.shape.localRead.requirements, observed.shape.localRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.finalRead.form, observed.shape.finalRead.requirements, observed.shape.finalRead.coercions⟩

theorem ObservedFactory.no_lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node)
    {parameters result body} (form : node.form = .lambda parameters result body) : False := by
  rcases observed.read_cases found with same | same | same
  all_goals subst node
  · rw [observed.shape.initialRead.form] at form; cases form
  · rw [observed.shape.localRead.form] at form; cases form
  · rw [observed.shape.finalRead.form] at form; cases form

theorem ObservedFactory.value_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.value.id = .ok observed.shape.value := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.initialRead.form,
    observed.shape.localRead.form, observed.shape.finalRead.form, observed.shape.assignmentForm,
    observed.shape.matchForm, observed.shape.statementForm, observed.shape.arms, observed.shape.patternResolution, SourceCoreDataPlaces.patternBinders, observed.shape.valueOwner,
    observed.shape.valueScheme, TypeSystem.Scheme.mono, observed.shape.argumentValue,
    observed.shape.localValue, observed.shape.valueRequirements]

theorem ObservedFactory.local_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.copyBinder.id = .ok observed.shape.copyBinder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.initialRead.form,
    observed.shape.localRead.form, observed.shape.finalRead.form, observed.shape.assignmentForm,
    observed.shape.matchForm, observed.shape.statementForm, observed.shape.arms, observed.shape.patternResolution, SourceCoreDataPlaces.patternBinders,
    observed.shape.localOwner, observed.shape.localScheme, TypeSystem.Scheme.mono,
    observed.shape.localRequirements,
    Ne.symm observed.shape.localArgument, Ne.symm observed.shape.localValue]

theorem ActualHeader.statements {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.function.body = [observed.shape.matchNode.id, observed.shape.statement.id] := actual.body

end Tests.SourceCoreNamedMatch
