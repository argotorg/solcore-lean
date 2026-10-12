import Solcore.Test.SourceCoreOperatorCallsFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport

/-! Finite original node observations supply complete metadata and identify both
real compiler rows. The two indirect calls remain in the supported expression tree. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

theorem ObservedProgram.identity_expressions {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.identityRow.row.function.typedBody id node) :
    node = observed.identityShape.read.node := by
  have member := found.1
  rw [observed.identityNodes] at member
  simpa only [IdentityShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using member

theorem ObservedProgram.identity_no_lambda {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.identityRow.row.function.typedBody id node)
    {parameters result body} (form : node.form = .lambda parameters result body) : False := by
  rcases observed.identity_expressions found with same
  all_goals subst node
  · rw [observed.identityShape.read.form] at form; cases form

theorem ObservedProgram.identity_metadata {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.identityRow.row.function.typedBody := by
  constructor
  · intro id _tree node found
    rcases observed.identity_expressions (lookupExpression?_sound found) with same
    all_goals subst node
    · exact observed.identityShape.read.requirements
  · intro id _tree node found
    rcases observed.identity_expressions (lookupExpression?_sound found) with same
    all_goals subst node
    · exact observed.identityShape.read.coercions
  · intro id _tree
    simp only [observed.noLocals, List.find?_nil]
  · intro id _tree node found callee arguments metadata form
    rcases observed.identity_expressions (lookupExpression?_sound found) with same
    all_goals subst node
    · rw [observed.identityShape.read.form] at form; cases form
  · intro id _tree node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ObservedProgram.select_expressions {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.selectRow.row.function.typedBody id node) :
    node = observed.selectShape.flagRead.node ∨ node = observed.selectShape.negation.node ∨ node = observed.selectShape.leftArgument.node ∨ node = observed.selectShape.leftFunction.node ∨ node = observed.selectShape.leftCall.node ∨ node = observed.selectShape.leftValue.node ∨ node = observed.selectShape.sum.node ∨ node = observed.selectShape.rightArgument.node ∨ node = observed.selectShape.rightFunction.node ∨ node = observed.selectShape.rightCall.node ∨ node = observed.selectShape.rightValue.node ∨ node = observed.selectShape.difference.node ∨ node = observed.selectShape.expression.node := by
  have member := found.1
  rw [observed.selectNodes] at member
  simpa only [SelectShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using member

theorem ObservedProgram.select_no_lambda {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : ContainsExpression observed.selectRow.row.function.typedBody id node)
    {parameters result body} (form : node.form = .lambda parameters result body) : False := by
  rcases observed.select_expressions found with same | same | same | same | same | same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [observed.selectShape.flagRead.form] at form; cases form
  · rw [observed.selectShape.negationForm] at form; cases form
  · rw [observed.selectShape.leftArgument.form] at form; cases form
  · rw [observed.selectShape.leftFunction.form] at form; cases form
  · rw [observed.selectShape.leftCall.form] at form; cases form
  · rw [observed.selectShape.leftValue.form] at form; cases form
  · rw [observed.selectShape.sumForm] at form; cases form
  · rw [observed.selectShape.rightArgument.form] at form; cases form
  · rw [observed.selectShape.rightFunction.form] at form; cases form
  · rw [observed.selectShape.rightCall.form] at form; cases form
  · rw [observed.selectShape.rightValue.form] at form; cases form
  · rw [observed.selectShape.differenceForm] at form; cases form
  · rw [observed.selectShape.expressionForm] at form; cases form

theorem ObservedProgram.select_metadata {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.selectRow.row.function.typedBody := by
  constructor
  · intro id _tree node found
    rcases observed.select_expressions (lookupExpression?_sound found) with same | same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.selectShape.flagRead.requirements
    · exact observed.selectShape.negation.requirements
    · exact observed.selectShape.leftArgument.requirements
    · exact observed.selectShape.leftFunction.requirements
    · exact observed.selectShape.leftCall.requirements
    · exact observed.selectShape.leftValue.requirements
    · exact observed.selectShape.sum.requirements
    · exact observed.selectShape.rightArgument.requirements
    · exact observed.selectShape.rightFunction.requirements
    · exact observed.selectShape.rightCall.requirements
    · exact observed.selectShape.rightValue.requirements
    · exact observed.selectShape.difference.requirements
    · exact observed.selectShape.expression.requirements
  · intro id _tree node found
    rcases observed.select_expressions (lookupExpression?_sound found) with same | same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.selectShape.flagRead.coercions
    · exact observed.selectShape.negation.coercions
    · exact observed.selectShape.leftArgument.coercions
    · exact observed.selectShape.leftFunction.coercions
    · exact observed.selectShape.leftCall.coercions
    · exact observed.selectShape.leftValue.coercions
    · exact observed.selectShape.sum.coercions
    · exact observed.selectShape.rightArgument.coercions
    · exact observed.selectShape.rightFunction.coercions
    · exact observed.selectShape.rightCall.coercions
    · exact observed.selectShape.rightValue.coercions
    · exact observed.selectShape.difference.coercions
    · exact observed.selectShape.expression.coercions
  · intro id _tree
    simp only [observed.noLocals, List.find?_nil]
  · intro id _tree node found callee arguments metadata form
    rcases observed.select_expressions (lookupExpression?_sound found) with same | same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.selectShape.flagRead.form] at form; cases form
    · rw [observed.selectShape.negationForm] at form; cases form
    · rw [observed.selectShape.leftArgument.form] at form; cases form
    · rw [observed.selectShape.leftFunction.form] at form; cases form
    · rw [observed.selectShape.leftCall.form] at form
      have same := (ExpressionForm.call.inj form).2.2
      cases same
      rw [observed.selectShape.leftCall.application]
    · rw [observed.selectShape.leftValue.form] at form; cases form
    · rw [observed.selectShape.sumForm] at form; cases form
    · rw [observed.selectShape.rightArgument.form] at form; cases form
    · rw [observed.selectShape.rightFunction.form] at form; cases form
    · rw [observed.selectShape.rightCall.form] at form
      have same := (ExpressionForm.call.inj form).2.2
      cases same
      rw [observed.selectShape.rightCall.application]
    · rw [observed.selectShape.rightValue.form] at form; cases form
    · rw [observed.selectShape.differenceForm] at form; cases form
    · rw [observed.selectShape.expressionForm] at form; cases form
  · intro id _tree node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (selectHeader : ActualHeader fixture observed.selectRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.identityRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.selectRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 2 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have selectBound := (List.getElem?_eq_some_iff.mp observed.selectRow.slot.selected).1
  rw [observed.globalsLength] at identityBound selectBound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.selectRow.index := by
    have distinct := observed.distinctSlots
    omega
  rcases casesIndex with same | same
  · left
    have actualIndex := (observed.identityRow.prepared_slot identityHeader.prepared).2
    rw [same, ← actualIndex, identityHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) identityHeader.prepared.same
  · right
    have actualIndex := (observed.selectRow.prepared_slot selectHeader.prepared).2
    rw [same, ← actualIndex, selectHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) selectHeader.prepared.same

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

theorem ActualHeader.key {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

def ActualHeader.descriptor {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature} (actual : ActualHeader fixture observed.row)
    (stages : ObservedStages fixture observed) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := actual.key.symm ▸ stages.descriptor

theorem ActualHeader.result_type {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature} (actual : ActualHeader fixture observed.row) :
    actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

theorem ActualHeader.output {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature} (actual : ActualHeader fixture observed.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.result_type] at projected
  exact (Except.ok.inj projected).symm

theorem ActualHeader.identity_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.identityShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.identityShape.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.identity_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.identity_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.select_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.selectRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [functionType, .bool, .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.selectShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.selectShape.callableScheme, observed.selectShape.flagScheme, observed.selectShape.argumentScheme, TypeSystem.Scheme.mono] using inputs.symm


end Tests.SourceCoreOperatorCalls
