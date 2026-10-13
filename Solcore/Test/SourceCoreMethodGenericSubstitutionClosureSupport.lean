import Solcore.Test.SourceCoreMethodGenericSubstitutionMetadata
import Solcore.Test.SourceCoreMethodGenericSubstitutionMethodSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalClosureAssociation

/-! Actual cached Source graphs identify the two factory lambda bodies. Their
retained ordinary provenance supplies the direct relay call, its complete
dictionary and actual physical slot; selected methods contain a read and return. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreMethodGenericSubstitution
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

private theorem factory_lambda_shape {function : CheckedFunction} {generic : ProgramFunctionSignature}
    {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
    (shape : SelectedFactoryShape function generic parameter type trait)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = type ∧ body = [shape.statement.id] := by
  rcases shape.expressions nodes found with same | same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.flagRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form
  · rw [shape.lambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩

private theorem factory_packet {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {signature generic : ProgramFunctionSignature} {row : ObservedRow fixture signature}
    {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
    (shape : SelectedFactoryShape row.row.function generic parameter type trait)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (signatureMember : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions)
    (supported : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
      fixture.recipe.compiled.indexed.base.plan shape.call.instantiation)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
        shape.call.instantiation = .ok signature.key →
      fixture.recipe.compiled.indexed.base.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    {registry : SourceCoreRawMetadata.Registry}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code fixture.recipe.compiled.indexed function scope administrative)
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
    (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
    (sameSource : function.source = row.row.function.typedBody) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.SelectedBody (headers := headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have found := code.sourceFound
  rw [sameSource] at found
  have lambda := factory_lambda_shape shape nodes found code.sourceForm
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source shape.call.value.node.id function.body := by
    rw [sameSource, lambda.2.2]
    exact .returning [] shape.statementFound shape.statementForm
  have tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
      function.source shape.call.value.node.id (fun inst => inst = shape.call.instantiation) := by
    rw [sameSource]; exact shape.inner_syntax
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed support.caller.named function.source (fun inst => inst = shape.call.instantiation) := by
    rw [sameSource]; exact shape.metadata nodes support.caller.named observed.noLocals
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  obtain ⟨loaded, checked⟩ := fixture.loaded
  apply CallableIndexedOwnedPreparedStagedOrdinaryMethodTerminalSupport.of_actual_generic
    (directSites := fun inst => inst = shape.call.instantiation)
    stagePrepared code support provenance receiver fixture.source_wellFormed
    (by intro inst same; subst inst; rw [support.compilation]; exact supported) metadata rows
    (by
      intro inst same index signature target global
      subst inst
      rw [support.compilation] at target global
      exact covered index signature target global) checked _ methods signatureMember
    (by rw [sameSource]; exact row.sourceOwner) shape.call.value.node.id terminal tree _ (.anonymous selected)
  rw [fixture.sameProgram]
  exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

/-- The callback is derived from actual compiler provenance and original syntax.
Every supplied packet concerns the identical retained Code and dictionary. -/
theorem closure_support {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (given : OrdinaryInventory fixture observed)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    {registry : SourceCoreRawMetadata.Registry} {keys}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association (headers given.rows) keys registry
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
    · have covered : ∀ index signature,
          SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
            observed.makeWordShape.call.instantiation = .ok signature.key →
          fixture.recipe.compiled.indexed.base.globals[index]? = some signature →
          ∃ header ∈ headers given.rows, header.slot = index ∧ header.named.signature = signature := by
        intro index signature target global
        rw [observed.makeWordRelayInstantiation, observed.relayWordRow.target] at target
        have key := Except.ok.inj target
        obtain ⟨signatureEq, indexEq⟩ := observed.relayWordRow.global_slot global key.symm
        exact ⟨given.relayWordHeader.header, given.relayWord_member,
          given.relayWordSlot.trans indexEq.symm, given.relayWordSignature.trans signatureEq.symm⟩
      obtain ⟨⟨packet, supported⟩⟩ := factory_packet observed observed.makeWordShape observed.makeWordNodes
        (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _)))
        observed.makeWord_supported given.rows covered stagePrepared receiver methods code support provenance (support.source.trans original)
      exact ⟨⟨.terminal packet, supported⟩⟩
    · have covered : ∀ index signature,
          SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
            observed.makeBoolShape.call.instantiation = .ok signature.key →
          fixture.recipe.compiled.indexed.base.globals[index]? = some signature →
          ∃ header ∈ headers given.rows, header.slot = index ∧ header.named.signature = signature := by
        intro index signature target global
        rw [observed.makeBoolRelayInstantiation, observed.relayBoolRow.target] at target
        have key := Except.ok.inj target
        obtain ⟨signatureEq, indexEq⟩ := observed.relayBoolRow.global_slot global key.symm
        exact ⟨given.relayBoolHeader.header, given.relayBool_member,
          given.relayBoolSlot.trans indexEq.symm, given.relayBoolSignature.trans signatureEq.symm⟩
      obtain ⟨⟨packet, supported⟩⟩ := factory_packet observed observed.makeBoolShape observed.makeBoolNodes
        (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _)))
        observed.makeBool_supported given.rows covered stagePrepared receiver methods code support provenance (support.source.trans original)
      exact ⟨⟨.terminal packet, supported⟩⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    have found := code.sourceFound
    rw [support.source, support.principal.source_eq] at found
    exact False.elim (bodies.no_lambda support.principal found code.sourceForm)

end Tests.SourceCoreMethodGenericSubstitution
