import Solcore.Test.SourceCoreEvidenceDirectFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

/-- The actual cached slot identifies one of the six prepared Source rows. -/
theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (relayWordHeader : ActualHeader fixture observed.relayWordRow.row)
    (relayBoolHeader : ActualHeader fixture observed.relayBoolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.wordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.boolRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.relayWordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.relayBoolRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.chooseWordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.chooseBoolRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 6 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have casesIndex : index = observed.wordRow.index ∨
      index = observed.boolRow.index ∨
      index = observed.relayWordRow.index ∨
      index = observed.relayBoolRow.index ∨
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
    have actualIndex := (observed.relayWordRow.prepared_slot relayWordHeader.prepared).2
    rw [same, ← actualIndex, relayWordHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) relayWordHeader.prepared.same
  · right; right; right; left
    have actualIndex := (observed.relayBoolRow.prepared_slot relayBoolHeader.prepared).2
    rw [same, ← actualIndex, relayBoolHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) relayBoolHeader.prepared.same
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

/-- The genuine formation provenance excludes anonymous and method bodies in
this artifact. Named call support is supplied separately for all six rows. -/
def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (relayWordHeader : ActualHeader fixture observed.relayWordRow.row)
    (relayBoolHeader : ActualHeader fixture observed.relayBoolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry faults
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply False.elim
    have found := code.sourceFound
    rcases observed.cached_source wordHeader boolHeader relayWordHeader relayBoolHeader chooseWordHeader chooseBoolHeader
        support.caller.selected with original | original | original | original | original | original
    all_goals rw [support.source.trans original] at found
    · exact False.elim (root_no_lambda observed.wordShape observed.wordNodes
        (lookupExpression?_sound found) code.sourceForm)
    · exact False.elim (root_no_lambda observed.boolShape observed.boolNodes
        (lookupExpression?_sound found) code.sourceForm)
    · exact False.elim (root_no_lambda observed.relayWordShape observed.relayWordNodes
        (lookupExpression?_sound found) code.sourceForm)
    · exact False.elim (root_no_lambda observed.relayBoolShape observed.relayBoolNodes
        (lookupExpression?_sound found) code.sourceForm)
    · exact False.elim (selected_no_lambda observed.chooseWordShape observed.chooseWordNodes
        (lookupExpression?_sound found) code.sourceForm)
    · exact False.elim (selected_no_lambda observed.chooseBoolShape observed.chooseBoolNodes
        (lookupExpression?_sound found) code.sourceForm)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreEvidenceDirect
