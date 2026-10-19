import Solcore.Test.SourceCoreEvidenceClosureFactorySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryEvidenceScopedSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodySupportCompatibility
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

/-- The actual cached slot identifies one of the six prepared Source rows. -/
theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (factoryWordHeader : ActualHeader fixture observed.factoryWordRow.row)
    (factoryBoolHeader : ActualHeader fixture observed.factoryBoolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.wordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.boolRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.factoryWordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.factoryBoolRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.chooseWordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.chooseBoolRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 6 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have casesIndex : index = observed.wordRow.index ∨
      index = observed.boolRow.index ∨
      index = observed.factoryWordRow.index ∨
      index = observed.factoryBoolRow.index ∨
      index = observed.chooseWordRow.index ∨
      index = observed.chooseBoolRow.index := by
    have contained := of_decide_eq_true (List.all_eq_true.mp observed.indexCoverage index (List.mem_range.mpr bound))
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using contained
  rcases casesIndex with same | same | same | same | same | same
  · left
    have actualIndex := (observed.wordRow.prepared_slot wordHeader.prepared).2
    rw [same, ← actualIndex, wordHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) wordHeader.prepared.same
  · right; left
    have actualIndex := (observed.boolRow.prepared_slot boolHeader.prepared).2
    rw [same, ← actualIndex, boolHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) boolHeader.prepared.same
  · right; right; left
    have actualIndex := (observed.factoryWordRow.prepared_slot factoryWordHeader.prepared).2
    rw [same, ← actualIndex, factoryWordHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) factoryWordHeader.prepared.same
  · right; right; right; left
    have actualIndex := (observed.factoryBoolRow.prepared_slot factoryBoolHeader.prepared).2
    rw [same, ← actualIndex, factoryBoolHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) factoryBoolHeader.prepared.same
  · right; right; right; right; left
    have actualIndex := (observed.chooseWordRow.prepared_slot chooseWordHeader.prepared).2
    rw [same, ← actualIndex, chooseWordHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) chooseWordHeader.prepared.same
  · right; right; right; right; right
    have actualIndex := (observed.chooseBoolRow.prepared_slot chooseBoolHeader.prepared).2
    rw [same, ← actualIndex, chooseBoolHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) chooseBoolHeader.prepared.same

private theorem root_no_lambda
    {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType trait)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : ContainsExpression function.typedBody id node)
    (form : node.form = .lambda parameters result body) : False := by
  have member := found.1
  rw [nodes, RootShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same
  all_goals try cases same
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form

private theorem selected_no_lambda {function firstType secondType}
    (shape : SelectedShape function firstType secondType)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : ContainsExpression function.typedBody id node)
    (form : node.form = .lambda parameters result body) : False := by
  have member := found.1
  rw [nodes, SelectedShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · cases same; rw [shape.read.form] at form; cases form
  · cases same

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

private theorem factory_lambda_shape
    {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = firstType ∧ body = [shape.statement.id] := by
  rcases shape.expressions nodes found with same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form
  · rw [shape.lambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩

private theorem factory_packet {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature}
    {generic firstParameter secondParameter firstType secondType trait}
    (shape : FactoryShape row.row.function signature generic firstParameter secondParameter firstType secondType trait)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (ordinary : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
      fixture.recipe.compiled.indexed.base.plan shape.call.instantiation)
    (signatureMember : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows))
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {registry : SourceCoreRawMetadata.Registry}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code fixture.recipe.compiled.indexed function scope administrative)
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
    (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
    (sameSource : function.source = row.row.function.typedBody) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Packet code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Support (headers rows) code support.body.toContext
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have found := code.sourceFound
  rw [sameSource] at found
  have lambda := factory_lambda_shape shape nodes found code.sourceForm
  have bodyShape := lambda.2.2
  have resultShape := lambda.2.1
  have bodyTree : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body := by
    rw [sameSource, bodyShape]; exact shape.body_shape
  obtain ⟨_final, _facts, bodyTyped, _completes⟩ := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters
    support.body.frame support.body.extended
  have tree : GenericImperativeMatch.Syntax function.source
      (fun id => CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax function.source id
        (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported fixture.recipe.compiled.indexed.base.plan))
      support.body.context (.statements true function.body) function.resultType := by
    rw [sameSource, bodyShape, resultShape] at bodyTyped ⊢
    exact shape.body_syntax (sameSource ▸ support.unique) (shape.syntax ordinary) bodyTyped
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor
      fixture.recipe.compiled.indexed support.caller.named function.source
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported fixture.recipe.compiled.indexed.base.plan) := by
    rw [sameSource]; exact shape.metadata nodes support.caller.named observed.noLocals
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  exact CallableIndexedOwnedPreparedStagedOrdinaryEvidenceScopedSupport.of_actual
    stagePrepared code support provenance receiver fixture.source_wellFormed
    (fun instantiation accepted => by simpa only [support.compilation, CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext] using accepted)
    metadata rows complete signatureMember (by rw [sameSource]; exact row.sourceOwner)
    bodyTree tree.prepared _ (.anonymous selected)

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (factoryWordHeader : ActualHeader fixture observed.factoryWordRow.row)
    (factoryBoolHeader : ActualHeader fixture observed.factoryBoolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows))
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {registry : SourceCoreRawMetadata.Registry}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.compiled
    have found := code.sourceFound
    rcases observed.cached_source wordHeader boolHeader factoryWordHeader factoryBoolHeader chooseWordHeader chooseBoolHeader
      support.caller.selected with original | original | original | original | original | original
    · rw [support.source.trans original] at found
      exact False.elim (root_no_lambda observed.wordShape observed.wordNodes (lookupExpression?_sound found) code.sourceForm)
    · rw [support.source.trans original] at found
      exact False.elim (root_no_lambda observed.boolShape observed.boolNodes (lookupExpression?_sound found) code.sourceForm)
    · obtain ⟨packet, supported⟩ := factory_packet observed observed.factoryWordShape observed.factoryWordNodes
        observed.factoryWord_supported (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _))
        rows complete stagePrepared receiver code support provenance (support.source.trans original)
      exact ⟨⟨packet, CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.SupportFor.of_generic _ _ _ supported⟩⟩
    · obtain ⟨packet, supported⟩ := factory_packet observed observed.factoryBoolShape observed.factoryBoolNodes
        observed.factoryBool_supported (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _))
        rows complete stagePrepared receiver code support provenance (support.source.trans original)
      exact ⟨⟨packet, CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.SupportFor.of_generic _ _ _ supported⟩⟩
    · rw [support.source.trans original] at found
      exact False.elim (selected_no_lambda observed.chooseWordShape observed.chooseWordNodes (lookupExpression?_sound found) code.sourceForm)
    · rw [support.source.trans original] at found
      exact False.elim (selected_no_lambda observed.chooseBoolShape observed.chooseBoolNodes (lookupExpression?_sound found) code.sourceForm)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreEvidenceClosure
