import Solcore.Test.SourceCoreNamedOperatorsFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadLambdaMetadata
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds

/-! Finite observations identify every original read, literal and binary operation.
They establish compiler coverage without an execution or body-meaning premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.input_types {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.shape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.shape.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

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

theorem ObservedFactory.expression_cases {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node) :
    node = observed.shape.conditionRead.node ∨ node = observed.shape.zero.node ∨ node = observed.shape.comparison.node ∨ node = observed.shape.argumentRead.node ∨ node = observed.shape.one.node ∨ node = observed.shape.difference.node ∨ node = observed.shape.finalRead.node := by
  have member := found.1
  rw [observed.nodes] at member
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton, Node.expression.injEq,
    reduceCtorEq, List.not_mem_nil, false_or, or_false] using member

theorem ObservedFactory.no_lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.row.function.typedBody id node)
    {parameters result body} (form : node.form = .lambda parameters result body) : False := by
  rcases observed.expression_cases found with same | same | same | same | same | same | same
  all_goals subst node
  · rw [observed.shape.conditionRead.form] at form; cases form
  · rw [observed.shape.zero.form] at form; cases form
  · rw [observed.shape.comparison.form] at form; cases form
  · rw [observed.shape.argumentRead.form] at form; cases form
  · rw [observed.shape.one.form] at form; cases form
  · rw [observed.shape.difference.form] at form; cases form
  · rw [observed.shape.finalRead.form] at form; cases form

theorem ObservedFactory.binder_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.binder.id = .ok observed.shape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.conditionRead.form, observed.shape.zero.form, observed.shape.comparison.form, observed.shape.argumentRead.form, observed.shape.one.form, observed.shape.difference.form, observed.shape.finalRead.form,
    observed.shape.assignmentForm, observed.shape.loopForm, observed.shape.statementForm,
    observed.shape.binderOwner, observed.shape.binderScheme, TypeSystem.Scheme.mono, observed.shape.binderRequirements]

theorem ActualHeader.statements {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.function.body = [observed.shape.loop.id, observed.shape.statement.id] := actual.body

end Tests.SourceCoreNamedOperators
