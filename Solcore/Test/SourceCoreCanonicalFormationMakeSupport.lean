import Solcore.Test.SourceCoreCanonicalFormationSyntax
import Solcore.Test.SourceCoreCanonicalFormationSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreCanonicalFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
structure ObservedMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  owned : observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    observed.makeRow.row.function.typedBody observed.makeShape.expression.id = .ok (observed.makeShape.expression, reported)
  binderScheme : observed.makeShape.binder.scheme = .mono .word

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) := do
  if accepted : proposition then return ⟨accepted⟩
  else throw (IO.userError label)

def observeMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) : IO (ObservedMake fixture observed) := do
  let ⟨owned⟩ ← confirm (observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner) "reuse lambda owner"
  let ⟨binderScheme⟩ ← confirm (observed.makeShape.binder.scheme = .mono .word) "reuse seed type"
  match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      observed.makeRow.row.function.typedBody observed.makeShape.expression.id with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (node, reported) =>
    let ⟨same⟩ ← confirm (node = observed.makeShape.expression) "reuse exact lambda read"
    return ⟨owned, reported, by simpa only [same] using read, binderScheme⟩

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.identityRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.relayRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 3 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have relayBound := (List.getElem?_eq_some_iff.mp observed.relayRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound relayBound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index ∨ index = observed.relayRow.index := by
    have im := observed.identityMake
    have ir := observed.identityRelay
    have mr := observed.makeRelay
    omega
  rcases casesIndex with same | same | same
  · left
    have actualIndex := (observed.identityRow.prepared_slot identityHeader.prepared).2
    rw [same, ← actualIndex, identityHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) identityHeader.prepared.same
  · right; left
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) makeHeader.prepared.same
  · right; right
    have actualIndex := (observed.relayRow.prepared_slot relayHeader.prepared).2
    rw [same, ← actualIndex, relayHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) relayHeader.prepared.same

theorem ObservedProgram.cached_rows {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    named.specialized = observed.identityRow.row ∨
    named.specialized = observed.makeRow.row ∨
    named.specialized = observed.relayRow.row := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 3 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have relayBound := (List.getElem?_eq_some_iff.mp observed.relayRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound relayBound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index ∨ index = observed.relayRow.index := by
    have im := observed.identityMake
    have ir := observed.identityRelay
    have mr := observed.makeRelay
    omega
  rcases casesIndex with same | same | same
  · left
    have actualIndex := (observed.identityRow.prepared_slot identityHeader.prepared).2
    rw [same, ← actualIndex, identityHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact identityHeader.prepared.same
  · right; left
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact makeHeader.prepared.same
  · right; right
    have actualIndex := (observed.relayRow.prepared_slot relayHeader.prepared).2
    rw [same, ← actualIndex, relayHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact relayHeader.prepared.same

theorem ObservedProgram.cached_assumptions {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    named.specialized.assumptions = [] := by
  rcases observed.cached_rows identityHeader makeHeader relayHeader selected with same | same | same
  · rw [same]; exact observed.identityRow.assumptions
  · rw [same]; exact observed.makeRow.assumptions
  · rw [same]; exact observed.relayRow.assumptions

theorem ObservedProgram.make_lambda_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = .word ∧ body = [observed.makeShape.innerReturn.id] := by
  rcases observed.make_expressions found with same | same | same | same | same | same | same
  all_goals subst node
  · rw [observed.makeShape.initialRead.form] at form; cases form
  · rw [observed.makeShape.initial.calleeForm] at form; cases form
  · rw [observed.makeShape.initial.form] at form; cases form
  · rw [observed.makeShape.read.form] at form; cases form
  · rw [observed.makeShape.call.calleeForm] at form; cases form
  · rw [observed.makeShape.call.form] at form; cases form
  · rw [observed.makeShape.lambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

theorem ActualHeader.make_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.makeShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    extra.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

def ActualHeader.descriptor {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor


theorem ActualHeader.make_body {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.function.body = [observed.makeShape.initialized.id, observed.makeShape.statement.id] := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = _
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.makeShape.roots] at accepted
  exact (Except.ok.inj accepted).symm

def ActualHeader.make_lambda {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (actual : ActualHeader fixture observed.makeRow.row) :
    CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors.ReturnLambda actual.header observed.makeShape.expression.id := {
  node := observed.makeShape.expression, reported := extra.reported, parameters := [], result := .word
  statement := observed.makeShape.innerReturn.id, returnNode := observed.makeShape.innerReturn
  expression := observed.makeShape.call.value.node.id
  found := by rw [actual.source]; exact observed.makeShape.expressionFound
  form := observed.makeShape.lambda
  owner := by rw [actual.source]; exact extra.owned
  requirements := observed.makeShape.requirements, coercions := observed.makeShape.coercions
  ordinary := by simp only [observed.noLocals, List.find?_nil]
  read := by rw [actual.source]; exact extra.read
  returnFound := by rw [actual.source]; exact observed.makeShape.innerReturnFound
  returnForm := observed.makeShape.innerReturnForm, returnType := observed.makeShape.innerReturnType }

theorem ActualHeader.make_syntax {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (actual : ActualHeader fixture observed.makeRow.row) :
    GenericImperativeMatch.Syntax actual.header.function.source
      (CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors.Syntax actual.header) actual.header.context
      (.statements true actual.header.function.body) actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.makeShape.roots, actual.make_result_type] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [actual.source, actual.make_body, actual.make_result_type]
  apply observed.make_body_syntax (actual.source ▸ actual.header.unique) _ _ typed
  · apply CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors.Syntax.general
    rw [actual.source]; exact observed.make_initial_syntax
  · exact .formation (actual.make_lambda extra)

theorem ActualHeader.make_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.make_body]
  exact observed.make_body_shape

def ActualHeader.make_body_packet {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := observed.makeRow.row, prepared := actual.prepared, instantiation := CallableNamedMetadata.instantiation observed.makeRow.row
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .canonicalBranching receipt }

theorem ActualHeader.make_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (actual : ActualHeader fixture observed.makeRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry actual.header
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) body
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨receipt⟩ := actual.make_receipt
  refine ⟨⟨actual.make_body_packet receipt, ?_⟩⟩
  apply CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors.of_actual
    actual.prepared actual.aligned fixture.recipePrepared actual.diagnostic receiver
    fixture.source_wellFormed observed.profile _ rows complete (bootstrap_zero fixture.recipe.compiled)
    observed.makeRow.entryMember receipt stagePrepared (actual.make_syntax extra)
  rw [actual.source]
  exact .of_ordinary (observed.make_metadata actual.prepared.named
    (by rw [actual.prepared.same]; exact observed.makeRow.assumptions))

end Tests.SourceCoreCanonicalFormation
