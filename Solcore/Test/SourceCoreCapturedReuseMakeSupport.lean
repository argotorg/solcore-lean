import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.Test.SourceCoreCapturedReuseFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadSequence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedReturnLambdaFormation

/-! Concrete make support and the complete closure family for the two-function
checked program. The actual compiler observations produce every body premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
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

theorem ActualHeader.make_formation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context
      actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedReturnLambdaFormation.of_terminal terminal
    fixture.recipePrepared diagnostic fixture.source_wellFormed observed.profile (stages.selected actual)
    observed.makeRow.entryMember
    (node := observed.makeShape.expression) (reported := extra.reported)
  · rw [actual.source, expression]; exact observed.makeShape.expressionFound
  · exact observed.makeShape.lambda
  · rw [actual.source, expression]; exact extra.owned
  · exact observed.makeShape.requirements
  · exact observed.makeShape.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact extra.read
  · rw [actual.source]; exact observed.makeShape.innerReturnFound
  · exact observed.makeShape.innerReturnForm
  · exact observed.makeShape.innerReturnType

theorem ActualHeader.make_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) headers)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.make_formation extra stages terminal diagnostic expression
  exact ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual headers
    (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point complete
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (readHeader : ActualHeader fixture observed.readRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.readRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 2 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have readBound := (List.getElem?_eq_some_iff.mp observed.readRow.slot.selected).1
  rw [observed.globalsLength] at makeBound readBound
  have casesIndex : index = observed.makeRow.index ∨ index = observed.readRow.index := by
    have distinct := observed.distinctSlots
    omega
  rcases casesIndex with same | same
  · left
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) makeHeader.prepared.same
  · right
    have actualIndex := (observed.readRow.prepared_slot readHeader.prepared).2
    rw [same, ← actualIndex, readHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) readHeader.prepared.same

theorem ObservedProgram.make_lambda_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = .word ∧ body = [observed.makeShape.innerReturn.id] := by
  have member := (lookupExpression?_sound found).1
  rw [observed.makeNodes] at member
  rcases List.mem_cons.mp member with same | rest
  · have nodeEq := Node.expression.inj same
    rw [nodeEq, observed.makeShape.readForm] at form
    cases form
  · rcases List.mem_cons.mp rest with impossible | rest
    · cases impossible
    · rcases List.mem_cons.mp rest with same | rest
      · have nodeEq := Node.expression.inj same
        rw [nodeEq, observed.makeShape.lambda] at form
        obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
        exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩
      · rcases List.mem_cons.mp rest with impossible | empty
        · cases impossible
        · cases empty

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (readHeader : ActualHeader fixture observed.readRow.row)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.sequence
    have sameSource : function.source = observed.makeRow.row.function.typedBody := by
      rcases observed.cached_source makeHeader readHeader support.caller.selected with original | original
      · exact support.source.trans original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.read_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
    have found := code.sourceFound
    rw [sameSource] at found
    have bodyShape := (observed.make_lambda_shape found code.sourceForm).2.2
    exact CallableIndexedOwnedPreparedStagedSingleReadSequence.sequence stagePrepared code support provenance
      receiver fixture.source_wellFormed
      (by rw [sameSource]; exact observed.makeNodes) observed.makeShape.lambda bodyShape
      (by rw [sameSource]; exact observed.makeShape.innerReturnFound) observed.makeShape.innerReturnForm
      (by rw [sameSource]; exact observed.makeShape.readFound) observed.makeShape.readForm
      observed.makeShape.readRequirements observed.makeShape.readCoercions observed.noLocals
      fixture.makeSignature (by rw [fixture.sameProgram, fixture.signatures]; exact .head _)
      (by rw [sameSource]; exact observed.makeRow.sourceOwner)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)


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

end Tests.SourceCoreCapturedReuse
