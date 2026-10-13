import Solcore.Test.SourceCoreCoercionPublicMetadata
import Solcore.Test.SourceCoreCoercionPublicFactoryMetadata
import Solcore.Test.SourceCoreCoercionPublicMethodSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCoercedTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalClosureAssociation

/-! Actual cached Source graphs identify the factory lambda body. Their
retained ordinary provenance supplies the coerced direct call, its complete
dictionary and actual physical slot; the selected method contains a read, literals and a conditional. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreCoercionPublic
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
        CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody)
      else true)) = true

def observeClosureSources (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (PLift (ObservedClosureSources fixture observed)) := do
  if checked : fixture.recipe.compiled.indexed.base.functions.all (fun named =>
    (CallableIndexedNamedGeneration.source named).nodes.all (fun node =>
      if lambdaNode node then decide (
        CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody)
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
    CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody := by
  have row := List.all_eq_true.mp sources.checked named (List.mem_of_getElem? selected)
  have expression := List.all_eq_true.mp row (.expression node) found.1
  simpa only [lambdaNode, form, Bool.true_eq, ↓reduceIte, decide_eq_true_eq] using expression

private theorem factory_lambda_shape {function : CheckedFunction}
    {signature generic : ProgramFunctionSignature} {parameter : TypeSystem.TypeParameterId}
    {mark coercion : ProgramTraitSignature}
    (shape : FactoryShape function signature generic parameter mark coercion)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = .word ∧ body = [shape.innerReturn.id] := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simp only [FactoryShape.nodeList, List.mem_cons,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] at present
  rcases present with same | same | same | same
  all_goals subst node
  · rw [shape.read.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form
  · rw [shape.lambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩

private theorem factory_packet {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (bodies : MethodBodies fixture) (given : OrdinaryInventory fixture observed)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)
    {registry : SourceCoreRawMetadata.Registry}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code fixture.recipe.compiled.indexed function scope administrative)
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
    (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
    (sameSource : function.source = observed.makeRow.row.function.typedBody) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.SelectedBody (headers := headers given.rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have found := code.sourceFound
  rw [sameSource] at found
  have lambda := factory_lambda_shape observed.makeShape observed.makeNodes found code.sourceForm
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source observed.makeShape.call.node.id function.body := by
    rw [sameSource, lambda.2.2]
    exact .returning [] observed.makeShape.innerReturnFound observed.makeShape.innerReturnForm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      fixture.recipe.compiled.indexed support.caller.named function.source (fun _ => False) := by
    rw [sameSource]
    exact observed.makeShape.native_metadata observed.makeNodes support.caller.named observed.noLocals
  have covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey code.compilation.plan
        observed.makeShape.call.instantiation = .ok signature.key →
      code.compilation.globals[index]? = some signature →
      ∃ header ∈ headers given.rows, header.slot = index ∧ header.named.signature = signature := by
    intro index signature target global
    rw [support.compilation] at target global
    change SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      observed.makeShape.call.instantiation = .ok signature.key at target
    change fixture.recipe.compiled.indexed.base.globals[index]? = some signature at global
    rw [observed.makeKeepInstantiation, observed.keepRow.target] at target
    have key := Except.ok.inj target
    obtain ⟨signatureEq, indexEq⟩ := observed.keepRow.global_slot global key.symm
    exact ⟨given.keepHeader.header, given.keep_member,
      given.keepSlot.trans indexEq.symm, given.keepSignature.trans signatureEq.symm⟩
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  apply CallableIndexedOwnedPreparedStagedOrdinaryCoercedTerminalSupport.of_actual
    stagePrepared code support provenance receiver fixture.source_wellFormed metadata given.rows checked _ methods
    (signature := fixture.makeSignature)
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _))
    (by rw [sameSource]; exact observed.makeRow.sourceOwner)
    (fun principal sourceAt diagnostic => bodies.support observed principal sourceAt diagnostic receiver
      (headers := headers given.rows) (RecursiveNamedPreparedStageScopes.registry stagePrepared))
    observed.makeShape.call.node.id terminal
    (by rw [sameSource]; exact observed.makeShape.call.found)
    observed.makeShape.call.form
    (by rw [observed.makeShape.call.coercions]; simp)
    (by rw [observed.makeShape.call.requirements]; simp)
    (by
      intro argument member
      cases List.mem_singleton.mp member
      rw [sameSource]
      exact .leaf (.read observed.makeShape.read.found observed.makeShape.read.form))
    (by simp only [observed.noLocals, List.find?_nil])
    (by rw [support.compilation]; exact observed.keep_supported)
    covered _ (.anonymous selected)
  rw [fixture.sameProgram]
  exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

/-- Actual retained compiler provenance identifies the factory body. The packet
keeps the original direct-call node, complete evidence and output coercion. -/
theorem closure_support {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (given : OrdinaryInventory fixture observed)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)
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
    have original := sources.selected support.caller.selected (lookupExpression?_sound found) code.sourceForm
    obtain ⟨⟨packet, supported⟩⟩ := factory_packet observed bodies given stagePrepared receiver methods
      code support provenance (support.source.trans original)
    exact ⟨⟨.terminal packet, supported⟩⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    have found := code.sourceFound
    rw [support.source, support.principal.source_eq] at found
    exact False.elim (bodies.no_lambda support.principal found code.sourceForm)

end Tests.SourceCoreCoercionPublic
