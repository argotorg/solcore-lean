import Solcore.Test.SourceCoreMethodScopedClosureSyntax
import Solcore.Test.SourceCoreMethodScopedMethodSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalClosureAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport

/-! Actual cached Source graphs identify the two factory lambda bodies. Their
retained ordinary provenance supplies method-aware roots and the complete
dictionary; genuine selected method bodies contain only a read and return. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport (PacketFor SupportFor)

private def lambdaNode : Node → Bool
  | .expression node => match node.form with | .lambda .. => true | _ => false
  | _ => false

/-- This finite observation checks every actual cache row, including methods. -/
structure ObservedClosureSources (fixture : CompiledFixture) (observed : ObservedProgram fixture) : Prop where
  checked : fixture.recipe.compiled.indexed.base.functions.all (fun named =>
    (CallableIndexedNamedGeneration.source named).nodes.all (fun node =>
      if lambdaNode node then decide (
        CallableIndexedNamedGeneration.source named = observed.makeWordRow.row.function.typedBody ∨
        CallableIndexedNamedGeneration.source named = observed.makeBoolRow.row.function.typedBody)
      else true)) = true

def observeClosureSources (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (PLift (ObservedClosureSources fixture observed)) := do
  if checked : fixture.recipe.compiled.indexed.base.functions.all (fun named =>
    (CallableIndexedNamedGeneration.source named).nodes.all (fun node =>
      if lambdaNode node then decide (
        CallableIndexedNamedGeneration.source named = observed.makeWordRow.row.function.typedBody ∨
        CallableIndexedNamedGeneration.source named = observed.makeBoolRow.row.function.typedBody)
      else true)) = true then
    return ⟨⟨checked⟩⟩
  else throw (IO.userError "actual cached lambda Source attribution")

theorem ObservedClosureSources.selected {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (sources : ObservedClosureSources fixture observed)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named)
    {id node parameters result body}
    (found : ContainsExpression (CallableIndexedNamedGeneration.source named) id node)
    (form : node.form = .lambda parameters result body) :
    CallableIndexedNamedGeneration.source named = observed.makeWordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.makeBoolRow.row.function.typedBody := by
  have row := List.all_eq_true.mp sources.checked named (List.mem_of_getElem? selected)
  have expression := List.all_eq_true.mp row (.expression node) found.1
  simpa only [lambdaNode, form, Bool.true_eq, ↓reduceIte, decide_eq_true_eq] using expression

private theorem factory_lambda_shape {function : CheckedFunction} {type : TypeSystem.Ty}
    (shape : SelectedFactoryShape function type)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = type ∧ body = shape.body := by
  rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.call.form] at form; cases form
  · rw [shape.conditionRead.form] at form; cases form
  · rw [shape.loopSecondRead.form] at form; cases form
  · rw [shape.loopCall.form] at form; cases form
  · rw [shape.stopForm] at form; cases form
  · rw [shape.finalRead.form] at form; cases form
  · rw [shape.finalCall.form] at form; cases form
  · rw [shape.lambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩

private theorem factory_packet {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature} {type : TypeSystem.Ty}
    (shape : SelectedFactoryShape row.row.function type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (signatureMember : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    {registry : SourceCoreRawMetadata.Registry}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code fixture.recipe.compiled.indexed function scope administrative)
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
    (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
    (sameSource : function.source = row.row.function.typedBody) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport.SelectedBody (headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have found := code.sourceFound
  rw [sameSource] at found
  have lambda := factory_lambda_shape shape nodes found code.sourceForm
  have branching : CallableIndexedOwnedPreparedStagedBranchingTree.Shape
      function.source true function.body := by
    rw [sameSource, lambda.2.2]
    exact shape.body_shape
  obtain ⟨finalContext, facts, typed, _complete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters support.body.frame support.body.extended
  have tree : GenericImperativeMatch.Syntax function.source
      (fun id => CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        function.source id (fun _ => False))
      support.body.context (.statements true function.body) function.resultType := by
    rw [sameSource, lambda.2.1, lambda.2.2] at typed ⊢
    exact shape.body_syntax nodes (sameSource ▸ support.body.unique) shape.children typed
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed support.caller.named function.source (fun _ => False) := by
    rw [sameSource]; exact shape.metadata nodes support.caller.named observed.noLocals
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  obtain ⟨loaded, checked⟩ := fixture.loaded
  apply CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedSupport.of_actual
    stagePrepared code support provenance receiver fixture.source_wellFormed
    (fun _ impossible => False.elim impossible) metadata rows
    (fun _ impossible => False.elim impossible) checked _ methods signatureMember
    (by rw [sameSource]; exact row.sourceOwner) branching tree _ (.anonymous selected)
  rw [fixture.sameProgram]
  exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

/-- The callback is derived from actual compiler provenance and original syntax.
Every supplied packet concerns the identical retained Code and dictionary. -/
theorem closure_support {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    {registry : SourceCoreRawMetadata.Registry} {keys}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association (headers rows) keys registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    Nonempty (Σ packet : PacketFor association.original (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SupportFor association.original (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet) := by
  rcases association with ⟨association, _slots⟩
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    have found := code.sourceFound
    rw [support.source] at found
    rcases sources.selected support.caller.selected (lookupExpression?_sound found) code.sourceForm with original | original
    · obtain ⟨packet, supported⟩ := factory_packet observed observed.makeWordShape observed.makeWordNodes
        (by rw [fixture.sameProgram, fixture.signatures]; exact .head _)
        rows stagePrepared receiver methods code support provenance (support.source.trans original)
      exact ⟨⟨.branching packet, supported⟩⟩
    · obtain ⟨packet, supported⟩ := factory_packet observed observed.makeBoolShape observed.makeBoolNodes
        (by rw [fixture.sameProgram, fixture.signatures]; exact .head _)
        rows stagePrepared receiver methods code support provenance (support.source.trans original)
      exact ⟨⟨.branching packet, supported⟩⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    obtain ⟨shape⟩ := bodies.selected support.principal
    have found := code.sourceFound
    rw [support.source, support.principal.source_eq] at found
    obtain ⟨name, binder, read⟩ := shape.only_reads _ _ found
    have form := code.sourceForm
    rw [read] at form
    cases form

end Tests.SourceCoreMethodScoped
