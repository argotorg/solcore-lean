import Solcore.Test.SourceSemantics.CoreLowering.Method.OriginFixture
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ProgramCompletion
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinaryMethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicPhysicalSessions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectHistories
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalMixedFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CertifiedPublicSessions
import Solcore.SourceSemantics.CoreLowering.PublicSessionOutcomes
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.PublicSessions
import Solcore.SourceSemantics.CoreLowering.PublicSupport

/-!
# Method origin evidence tests

Method origin evidence from the checked cache through public execution, sequences and source outcomes.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceClosureCompilerSupport
/-! Original factory closure nodes are identified without a body scanner.
Accepted inner compiler actions retain the direct call and its ordered reads. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open AcceptedNamedExpressionFlow

variable {fixture : CompiledFixture} {signature generic : ProgramFunctionSignature}
  {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
  {row : ObservedRow fixture signature}
  (shape : SelectedFactoryShape row.row.function generic parameter type trait)

/-- The declaration callee remains in Source. Only the original call and its
actual argument occurrences belong to this reached set. -/
def SelectedFactoryShape.Reached (id : ExpressionId) : Prop :=
  id = shape.call.value.node.id ∨ id = shape.firstRead.node.id ∨
    id = shape.secondRead.node.id ∨ id = shape.flagRead.node.id

theorem SelectedFactoryShape.reached_form {id : ExpressionId} {node : ExpressionNode}
    (reached : shape.Reached id)
    (found : row.row.function.typedBody.lookupExpression? id = some node) :
    (∃ name binder, node.form = .reference name (.local binder)) ∨
      node.form = .call shape.call.callee.node.id
        [shape.firstRead.node.id, shape.secondRead.node.id, shape.flagRead.node.id]
        (.declaration shape.call.instantiation) := by
  rcases reached with same | same | same | same
  · rw [same, shape.call.value.found] at found
    cases Option.some.inj found
    exact .inr shape.call.form
  · rw [same, shape.firstRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, shape.firstRead.form⟩
  · rw [same, shape.secondRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, shape.secondRead.form⟩
  · rw [same, shape.flagRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, shape.flagRead.form⟩

theorem SelectedFactoryShape.reached_forms : ReachedForms row.row.function.typedBody shape.Reached := by
  intro id node reached found
  rcases shape.reached_form reached found with ⟨name, binder, form⟩ | form
  · exact .inl (form ▸ LeafForm.read name binder)
  · exact .inr ⟨_, _, _, form⟩

theorem SelectedFactoryShape.reached_arguments : ReachedArguments row.row.function.typedBody shape.Reached := by
  intro id node reached found callee arguments instantiation form argument member
  rcases shape.reached_form reached found with ⟨name, binder, localForm⟩ | directForm
  · rw [localForm] at form
    cases form
  · have same := (ExpressionForm.call.inj (form.symm.trans directForm)).2.1
    rw [same] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second | flag
    · exact .inr (.inl first)
    · exact .inr (.inr (.inl second))
    · exact .inr (.inr (.inr flag))

theorem SelectedFactoryShape.direct_coverage
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (site : DirectSite directRows shape.call.instantiation) :
    ∀ id node, row.row.function.typedBody.lookupExpression? id = some node →
      ∀ callee arguments instantiation,
      node.form = .call callee arguments (.declaration instantiation) → DirectSite directRows instantiation := by
  intro id node found callee arguments instantiation form
  rcases shape.expressions nodes found with same | same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.flagRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · have same := CallResolution.declaration.inj
      ((ExpressionForm.call.inj (form.symm.trans shape.call.form)).2.2)
    exact same ▸ site

  · rw [shape.lambda] at form; cases form

/-- The original finite node list contains this single lambda. Its body receipt
accounts for that lambda while every remaining node is retained unchanged. -/
theorem SelectedFactoryShape.closure_source
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    {directRows : List SourceSpecialization.SpecializedFunction} {allowCoerced : Bool}
    (certificate : Nonempty (CallableIndexedOwnedPreparedClosureAdmission.OrdinaryBodyCertificate
      fixture.recipe.compiled row.named directRows [shape.statement.id])) :
    CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
      fixture.recipe.compiled row.named directRows allowCoerced := by
  obtain ⟨certificate⟩ := certificate
  constructor
  intro node member
  rw [row.same, nodes] at member
  simp only [SelectedFactoryShape.nodeList, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, shape.firstRead.form]
  · simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, shape.secondRead.form]
  · simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, shape.flagRead.form]
  · simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, shape.call.calleeForm]
  · simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, shape.call.form]
  · trivial
  · simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, shape.lambda]
    exact ⟨.ordinary certificate⟩
  · trivial

/-- The actual lambda compiler body supplies its return expression grammar.
Original metadata and finite source forms retain the same captured variables. -/
theorem ActualHeader.closure_compiler_source
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {directRows : List SourceSpecialization.SpecializedFunction} {allowCoerced : Bool}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed row.named row.row.function.typedBody (DirectSite directRows))
    (site : DirectSite directRows shape.call.instantiation)
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
        fixture.recipe.compiled.indexed.base.plan instantiation) :
    CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
      fixture.recipe.compiled row.named directRows allowCoerced := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named
    actual.prepared row.cached row.same
  have actualMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source (DirectSite directRows) := by
    rw [namedEq, actual.source]
    exact metadata
  have initializers : ∀ id, shape.Reached id → ¬ Nonempty
      (AcceptedContextualDirectReceipt.InitializerAt fixture.recipe.compiled.indexed
        (CallableIndexedNamedGeneration.context fixture.recipe.compiled.indexed actual.prepared.named) id) := by
    intro id _ initializer
    obtain ⟨initializer⟩ := initializer
    have found := initializer.found
    simp only [noLocals, List.find?_nil, Option.filter_none] at found
    cases found
  have issued := AcceptedNamedClosureAdmission.of_returning actual.prepared actual.aligned
    (actual.factory_compiler_roots shape)
    (by rw [actual.source]; exact shape.outerReturnFound) shape.outerReturnForm
    (by rw [actual.source]; exact shape.expression.found) shape.lambda
    shape.expression.requirements shape.expression.coercions
    (by simp only [noLocals, List.find?_nil])
    (by rw [actual.source]; exact shape.statementFound) shape.statementForm fixture.source_wellFormed
    actualMetadata supported (by rw [actual.source]; exact shape.direct_coverage nodes site)
    (by rw [actual.source]; exact shape.reached_forms) initializers
    (by rw [actual.source]; exact shape.reached_arguments)
    (show shape.Reached shape.call.value.node.id from .inl rfl)
  obtain ⟨certificate⟩ := issued
  exact shape.closure_source nodes (AcceptedNamedClosureAdmission.source_of_header
    actual.prepared row.cached row.same certificate)

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceClosureSupport
/-! Actual cached Source graphs identify the two factory lambda bodies. Their
retained ordinary provenance supplies the direct relay call, its complete
dictionary and actual physical slot; selected methods contain a read and return. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreMethodOriginEvidence
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
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
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
  have checked := CallableMethodBodyCoherence.of_loaded checked
  apply CallableIndexedOwnedPreparedStagedOrdinaryMethodTerminalSupport.of_actual_with_catalog
    (directSites := fun inst => inst = shape.call.instantiation)
    stagePrepared code support provenance receiver fixture.source_wellFormed
    (by intro inst same; subst inst; rw [support.compilation]; exact supported) metadata rows
    (by
      intro inst same index signature target global
      subst inst
      rw [support.compilation] at target global
      exact covered index signature target global) checked _ (.origins methods) signatureMember
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
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
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

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceIdentityCompilerSupport
/-! The two existing identity bodies are recovered from their accepted return
and read actions, using the same finite metadata table as the other roots. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open AcceptedNamedExpressionFlow

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
  {type : TypeSystem.Ty} {row : ObservedRow fixture signature}
  (shape : SelectedIdentityShape row.row.function type)

theorem ActualHeader.identity_compiler_admission
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed row.named row.row.function.typedBody (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
        fixture.recipe.compiled.indexed.base.plan instantiation) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header directRows := by
  have bodyEq : actual.header.function.body = [shape.statement.id] := by
    rw [actual.aligned.function]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, shape.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have namedEq : actual.prepared.named = row.named :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named actual.prepared row.cached row.same
  have actualMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source (DirectSite directRows) := by
    rw [namedEq, actual.source]
    exact metadata
  have onlyRead : ∀ id node, actual.header.function.source.lookupExpression? id = some node →
      node = shape.read.node := by
    intro id node found
    rw [actual.source] at found
    exact shape.expression nodes found
  have noDirect : ∀ id node, actual.header.function.source.lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) → False := by
    intro id node found callee arguments instantiation form
    rw [onlyRead id node found, shape.read.form] at form
    cases form
  exact AcceptedNamedBodyExpressionAdmission.of_returning actual.prepared actual.aligned actualMetadata
    supported (fun id node found callee arguments instantiation form =>
      False.elim (noDirect id node found callee arguments instantiation form))
    bodyEq (by rw [actual.source]; exact shape.statementFound) shape.statementForm
    (reached := fun _ => True) (by
      intro id node _ found
      rw [onlyRead id node found]
      exact .inl (shape.read.form ▸ LeafForm.read _ _))
    (fun id _ initializer => by
      obtain ⟨initializer⟩ := initializer
      have found := initializer.found
      simp only [noLocals, List.find?_nil, Option.filter_none] at found
      cases found)
    (by
      intro id node _ found callee arguments instantiation form argument member
      exact False.elim (noDirect id node found callee arguments instantiation form))
    True.intro fixture.source_wellFormed

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceMakeStep
/-! Actual factory calls append their freshly exported closures to the same physical history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.make_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {inventory : OrdinaryInventory fixture observed} {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState inventory receiver session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers inventory.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = request.header.function.resultType ∧ entry.handle = call.handle ∧
      call.handle.sourceType = request.header.function.resultType ∧
      ∃ after : RetainedState inventory receiver call.completion.session (entries ++ [entry]),
        SourceCall inventory request.header invocation state.heap arguments
          (.value entry.source) after.heap := by
  exact RecursiveNamedPublicPhysicalSessionFunctionStep.State.make_typed_handle program fixture.recipePrepared state call request inputs
    (request.started.simple_registry state.registry simple) descriptor invocation

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceMethodCompilerObservation
/-! The original cache supplies finite method observations. Its full parameter
replacement range, evidence-bearing calls, source nodes and local identities
are retained. Genuine final preparation supplies method selection separately. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedScopedMethodAdmission (Excluded RowCase)

/-- This shape signature is obtained from the original implementation's generic
signature and the actual cached replacement list. It supplies only finite shape
observations; method typing is derived from the genuine compiler selector. -/
def methodShapeSignature (fixture : CompiledFixture) (named : SourceCoreGeneralFunctions.Function) :
    ProgramFunctionSignature :=
  let generic := fixture.implementation.functionSignatureOfMethodWithTrait
    fixture.methodShape.trait fixture.methodShape.method
  { generic with
    parameters := generic.parameters.map fun parameter =>
      { parameter with type := named.specialized.parameterSubstitution.apply parameter.type }
    returnTypes := generic.returnTypes.map named.specialized.parameterSubstitution.apply
    scheme := {
      parameters := []
      predicates := named.specialized.assumptions
      body := named.specialized.function.type } }

structure ObservedMethodCompiler (fixture : CompiledFixture)
    (named : SourceCoreGeneralFunctions.Function)
    (rows : List SourceSpecialization.SpecializedFunction) where
  shape : MethodShape named.specialized.function (methodShapeSignature fixture named)
    named.specialized.function.inferredBodyType
  nodes : named.specialized.function.typedBody.nodes = shape.nodeList
  notOrdinary : ∀ signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions,
    named.specialized.function.typedBody.owner ≠ signature.id
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
    named.specialized.parameterSubstitution
  first : DirectSite rows shape.call.instantiation
  loop : DirectSite rows shape.loopCall.instantiation
  last : DirectSite rows shape.finalCall.instantiation

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

private def site (rows : List SourceSpecialization.SpecializedFunction)
    (instantiation : DeclarationInstantiation) : IO (PLift (DirectSite rows instantiation)) :=
  match CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite? rows instantiation with
  | none => throw (IO.userError "original method direct target missing")
  | some receipt => pure receipt

private def observeMethodCompiler (fixture : CompiledFixture)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) :
    IO (ObservedMethodCompiler fixture named rows) := do
  let ⟨shape, _, _, _⟩ ← observeMethod named.specialized.function (methodShapeSignature fixture named)
    named.specialized.function.inferredBodyType fixture.identitySignature fixture.identityParameter
    (.declaration fixture.mark.id)
  let ⟨nodes⟩ ← observed (named.specialized.function.typedBody.nodes = shape.nodeList)
    "original cached method source nodes"
  let ⟨different⟩ ← observed (fixture.recipe.compiled.sourceProgram.signatures.functions.all
      (fun signature => decide (named.specialized.function.typedBody.owner ≠ signature.id)) = true)
    "method owner belongs to an ordinary signature"
  let some ⟨range⟩ := CallableIndexedOwnedPreparedOrdinarySyntaxTable.range?
      fixture.recipe.compiled.sourceProgram.signatures 64 named.specialized.parameterSubstitution
    | throw (IO.userError "original full method replacement range rejected")
  let ⟨first⟩ ← site rows shape.call.instantiation
  let ⟨loop⟩ ← site rows shape.loopCall.instantiation
  let ⟨last⟩ ← site rows shape.finalCall.instantiation
  pure ⟨shape, nodes, (fun signature member =>
    of_decide_eq_true (List.all_eq_true.mp different signature member)), range, first, loop, last⟩

def MethodCompilerRow (fixture : CompiledFixture) (named : SourceCoreGeneralFunctions.Function)
    (rows : List SourceSpecialization.SpecializedFunction) : Prop :=
  Excluded fixture.recipe.compiled named ∨ Nonempty (ObservedMethodCompiler fixture named rows)

private def observeMethodCompilerList (fixture : CompiledFixture)
    (rows : List SourceSpecialization.SpecializedFunction) :
    (items : List SourceCoreGeneralFunctions.Function) →
      IO (PLift (∀ named ∈ items, MethodCompilerRow fixture named rows))
  | [] => pure ⟨by intro named member; cases member⟩
  | named :: rest => do
      let ⟨head⟩ ← (do
        if excluded : (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods.all
            (fun definition => decide (named.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
          pure ⟨Or.inl (fun definition member =>
            of_decide_eq_true (List.all_eq_true.mp excluded definition member))⟩
        else
          let source ← observeMethodCompiler fixture named rows
          pure ⟨Or.inr ⟨source⟩⟩ : IO (PLift (MethodCompilerRow fixture named rows)))
      let ⟨tail⟩ ← observeMethodCompilerList fixture rows rest
      pure ⟨by
        intro actual member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail actual member⟩

structure ObservedMethodCompilers (fixture : CompiledFixture)
    (rows : List SourceSpecialization.SpecializedFunction) : Prop where
  rows : ∀ named ∈ fixture.recipe.compiled.indexed.base.functions, MethodCompilerRow fixture named rows

def observeMethodCompilers (fixture : CompiledFixture)
    (rows : List SourceSpecialization.SpecializedFunction) : IO (PLift (ObservedMethodCompilers fixture rows)) := do
  let ⟨all⟩ ← observeMethodCompilerList fixture rows fixture.recipe.compiled.indexed.base.functions
  pure ⟨⟨all⟩⟩

/-- No operator selector is replayed. Actual final-plan provenance authenticates
this same cache row, and its accepted compilation supplies the method body. -/
theorem ObservedMethodCompilers.complete {fixture : CompiledFixture}
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table fixture.recipe.compiled)
    (sources : ObservedMethodCompilers fixture table.rows)
    (catalog : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (index : Nat) (named : SourceCoreGeneralFunctions.Function)
    (found : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    RowCase fixture.recipe.compiled named table.rows := by
  have actual : Excluded fixture.recipe.compiled named ∨ Nonempty (ObservedMethodCompiler fixture named table.rows) :=
    sources.rows named (List.mem_of_getElem? found)
  rcases actual with excluded | original
  · exact .inl excluded
  · obtain ⟨source⟩ := original
    have retained := RecursiveNamedPreparedFinalPlanOrigins.final_member fixture.recipe.compiled found rfl
    have origin := CallablePreparedFinalCatalogOrigins.of_preparation
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared fixture.recipe.compiled) named.specialized retained
    generalize sameRow : named.specialized = row at origin
    cases origin with
    | ordinary original =>
        obtain ⟨request, signature, generic, member, _genericMember, _resolved, accepted⟩ := original
        have owner : row.function.typedBody.owner = signature.id := by
          rw [(CallableCoercionBodyProvenance.specialization_fields accepted).1]
          change generic.typedBody.owner = signature.id
          have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
          exact identities.2.1.trans identities.1.symm
        exact False.elim (source.notOrdinary signature member ((congrArg (fun value => value.function.typedBody.owner) sameRow).trans owner))
    | @method method selected =>
        obtain ⟨diagnostics, code, cachedCode, ⟨compilation⟩⟩ :=
          CallableIndexedNamedGeneration.compiled_at fixture.recipe.compiled.indexed found
        let cached : CallablePreparedMethodSelection.Cached fixture.recipe.compiled method.specialized :=
          ⟨index, named, diagnostics, code, found, sameRow, cachedCode, compilation⟩
        have formed := catalog.formed.formed selected.implementation selected.implementationMember
          selected.declaration selected.methodMember
        have checked : CallableMethodBodyCoherence.Checked fixture.recipe.compiled.sourceProgram :=
          fixture.sameProgram.symm ▸ CallableMethodBodyCoherence.of_checked fixture.checked
        have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
            (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
            method.specialized.parameterSubstitution := by
          rw [← sameRow]
          exact source.range
        exact .inr (method_compiler_admission cached checked selected formed.parameters range
          fixture.source_wellFormed table source.shape source.nodes noLocals source.first source.loop source.last)

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceOrdinarySupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport (Support)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

variable {fixture : CompiledFixture}
  {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include rows receiver methods in
theorem ActualHeader.direct_support {signature generic : ProgramFunctionSignature}
    {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
    (row : ObservedRow fixture signature)
    (shape : RootShape row.row.function signature generic parameter type trait)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (supported : Supported fixture.recipe.compiled.indexed.base.plan shape.call.instantiation)
    (actual : ActualHeader fixture row.row)
    (covered : ∀ index signature,
      SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
        shape.call.instantiation = .ok signature.key →
      fixture.recipe.compiled.indexed.base.globals[index]? = some signature →
      ∃ header ∈ headers rows, header.slot = index ∧ header.named.signature = signature) :
    ∃ terminal : Terminal actual.header,
      Nonempty (Support (headers := headers rows) (stages := actualRegistry) (semanticFaults := faults)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.call.value.node.id
    shape.statement shape.roots shape.statementFound shape.statementForm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed terminal.prepared.named actual.header.function.source
      (fun inst => inst = shape.call.instantiation) := by
    rw [actual.source]
    exact shape.metadata nodes terminal.prepared.named noLocals
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  refine ⟨terminal, CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport.of_actual_with_catalog
    (directSites := fun inst => inst = shape.call.instantiation)
    terminal diagnostic receiver fixture.source_wellFormed (fun _ same => same ▸ supported) metadata
    (by rw [expression, actual.source]; exact shape.syntax) rows ?_
    checked ?_ (.origins methods)
    (actualStagePrepared fixture) point⟩
  · intro inst same index signature target global
    subst inst
    exact covered index signature target global
  · rw [fixture.sameProgram]
    exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

include rows receiver methods in
theorem ActualHeader.use_support {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
    (row : ObservedRow fixture signature)
    (shape : UseShape row.row.function signature type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row) :
    ∃ terminal : Terminal actual.header,
      Nonempty (Support (headers := headers rows) (stages := actualRegistry) (semanticFaults := faults)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.value.node.id
    shape.body.statement shape.body.roots shape.body.statementFound
    shape.body.statementForm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed terminal.prepared.named actual.header.function.source
      (fun _ => False) := by
    rw [actual.source]
    exact shape.policy_metadata nodes terminal.prepared.named noLocals
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  refine ⟨terminal, CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport.of_actual_with_catalog
    terminal diagnostic receiver fixture.source_wellFormed (fun _ impossible => impossible.elim) metadata
    (by rw [expression, actual.source]; exact shape.syntax) rows
    (fun _ impossible => impossible.elim) checked ?_ (.origins methods)
    (actualStagePrepared fixture) point⟩
  rw [fixture.sameProgram]
  exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

include rows receiver methods in
theorem ActualHeader.identity_support {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
    (row : ObservedRow fixture signature)
    (shape : SelectedIdentityShape row.row.function type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row) :
    ∃ terminal : Terminal actual.header,
      Nonempty (Support (headers := headers rows) (stages := actualRegistry) (semanticFaults := faults)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.read.node.id
    shape.statement shape.roots shape.statementFound shape.statementForm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed terminal.prepared.named actual.header.function.source
      (fun _ => False) := by
    rw [actual.source]
    exact shape.metadata nodes terminal.prepared.named noLocals
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  refine ⟨terminal, CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport.of_actual_with_catalog
    terminal diagnostic receiver fixture.source_wellFormed (fun _ impossible => impossible.elim) metadata
    (by rw [expression, actual.source]; exact shape.syntax) rows
    (fun _ impossible => impossible.elim) checked ?_ (.origins methods)
    (actualStagePrepared fixture) point⟩
  rw [fixture.sameProgram]
  exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceRelaySupport
/-! The actual selected relay Header supplies Source typing and the accepted
scoped compiler action. Three trait sites keep their original requirement IDs
and complete caller dictionary after local initialization and loop assignment. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport (Support)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

/-- The receiver and real cached Header determine all static body children. -/
theorem ActualHeader.scoped_receipt {fixture : CompiledFixture}
    {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
    (row : ObservedRow fixture signature)
    (shape : SelectedRelayShape row.row.function type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (resultType : row.row.function.inferredBodyType = type)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts}
    (entryMember : entry ∈ fixture.recipe.compiled.indexed.entries)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ receipt : Receipt actual.header,
      Support (headers rows) actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) receipt
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have bodyEq : actual.header.function.body = shape.body := by
    rw [actual.aligned.function]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, shape.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have resultEq : actual.header.function.resultType = type := by
    rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
    exact resultType
  have syntaxTree : GenericImperativeMatch.Syntax actual.header.function.source
      (fun id => CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        actual.header.function.source id (fun _ => False))
      actual.header.context (.statements true actual.header.function.body) actual.header.function.resultType := by
    obtain ⟨facts, finalContext, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
    rw [actual.source, shape.roots, resultEq] at typed
    simp only [List.filterMap_cons, List.filterMap_nil] at typed
    rw [actual.source, bodyEq, resultEq]
    exact shape.body_syntax nodes (actual.source ▸ actual.header.unique) shape.children typed
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted
    actual.aligned.accepted (by rw [actual.source, bodyEq]; exact shape.body_shape) actual.aligned.projection
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  refine ⟨receipt, ?_⟩
  apply CallableIndexedOwnedPreparedNamedPhysicalMixedScopedCollectors.of_actual_with_catalog actual.prepared actual.aligned
    fixture.recipePrepared actual.diagnostic receiver fixture.source_wellFormed
    (fun _ impossible => False.elim impossible) _ rows
    (fun _ impossible => False.elim impossible) checked _ (.origins methods) entryMember receipt stagePrepared syntaxTree.prepared
  · rw [actual.source]
    exact shape.metadata nodes actual.prepared.named noLocals
  · rw [fixture.sameProgram]
    exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

theorem ActualHeader.relayWord_receipt {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayWordRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ receipt : Receipt actual.header,
      Support (headers rows) actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) receipt
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) :=
  actual.scoped_receipt observed.relayWordRow observed.relayWordShape observed.relayWordNodes
    observed.relayWordResultType observed.noLocals rows observed.wordRow.entryMember receiver methods stagePrepared

theorem ActualHeader.relayBool_receipt {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayBoolRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ receipt : Receipt actual.header,
      Support (headers rows) actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) receipt
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) :=
  actual.scoped_receipt observed.relayBoolRow observed.relayBoolShape observed.relayBoolNodes
    observed.relayBoolResultType observed.noLocals rows observed.wordRow.entryMember receiver methods stagePrepared

theorem ActualHeader.scoped_support {fixture : CompiledFixture}
    {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
    (row : ObservedRow fixture signature)
    (shape : SelectedRelayShape row.row.function type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (resultType : row.row.function.inferredBodyType = type)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts}
    (entryMember : entry ∈ fixture.recipe.compiled.indexed.entries)
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header body) := by
  obtain ⟨receipt, static⟩ := actual.scoped_receipt row shape nodes resultType noLocals rows entryMember
    receiver methods stagePrepared
  let body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
    row := row.row
    prepared := actual.prepared
    instantiation := CallableNamedCanonicalOrder.retainedInstantiation row.row
    aligned := actual.aligned
    layouts := actual.aligned.layouts
    compilation := .canonicalBranching receipt }
  exact ⟨body, .scoped body receipt rfl static⟩

theorem ActualHeader.relayWord_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayWordRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header body) :=
  actual.scoped_support observed.relayWordRow observed.relayWordShape observed.relayWordNodes
    observed.relayWordResultType observed.noLocals rows observed.wordRow.entryMember receiver methods stagePrepared

theorem ActualHeader.relayBool_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayBoolRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header body) :=
  actual.scoped_support observed.relayBoolRow observed.relayBoolShape observed.relayBoolNodes
    observed.relayBoolResultType observed.noLocals rows observed.wordRow.entryMember receiver methods stagePrepared


end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceRootCompilerSupport
/-! The two original entry roots use the same accepted-body producer. Their
three argument occurrences retain their order and original evidence metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open AcceptedNamedExpressionFlow

variable {fixture : CompiledFixture} {signature generic : ProgramFunctionSignature}
  {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
  {row : ObservedRow fixture signature}
  (shape : RootShape row.row.function signature generic parameter type trait)

/-- The declaration callee remains in Source. Only the original call and its
actual argument occurrences belong to this reached set. -/
def RootShape.Reached (id : ExpressionId) : Prop :=
  id = shape.call.value.node.id ∨ id = shape.firstRead.node.id ∨
    id = shape.secondRead.node.id ∨ id = shape.flagRead.node.id

theorem RootShape.reached_form {id : ExpressionId} {node : ExpressionNode}
    (reached : shape.Reached id)
    (found : row.row.function.typedBody.lookupExpression? id = some node) :
    (∃ name binder, node.form = .reference name (.local binder)) ∨
      node.form = .call shape.call.callee.node.id
        [shape.firstRead.node.id, shape.secondRead.node.id, shape.flagRead.node.id]
        (.declaration shape.call.instantiation) := by
  rcases reached with same | same | same | same
  · rw [same, shape.call.value.found] at found
    cases Option.some.inj found
    exact .inr shape.call.form
  · rw [same, shape.firstRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, shape.firstRead.form⟩
  · rw [same, shape.secondRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, shape.secondRead.form⟩
  · rw [same, shape.flagRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, shape.flagRead.form⟩

theorem RootShape.reached_forms : ReachedForms row.row.function.typedBody shape.Reached := by
  intro id node reached found
  rcases shape.reached_form reached found with ⟨name, binder, form⟩ | form
  · exact .inl (form ▸ LeafForm.read name binder)
  · exact .inr ⟨_, _, _, form⟩

theorem RootShape.reached_arguments : ReachedArguments row.row.function.typedBody shape.Reached := by
  intro id node reached found callee arguments instantiation form argument member
  rcases shape.reached_form reached found with ⟨name, binder, localForm⟩ | directForm
  · rw [localForm] at form
    cases form
  · have same := (ExpressionForm.call.inj (form.symm.trans directForm)).2.1
    rw [same] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second | flag
    · exact .inr (.inl first)
    · exact .inr (.inr (.inl second))
    · exact .inr (.inr (.inr flag))

theorem RootShape.direct_coverage
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (site : DirectSite directRows shape.call.instantiation) :
    ∀ id node, row.row.function.typedBody.lookupExpression? id = some node →
      ∀ callee arguments instantiation,
      node.form = .call callee arguments (.declaration instantiation) → DirectSite directRows instantiation := by
  intro id node found callee arguments instantiation form
  rcases shape.expressions nodes found with same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.flagRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · have same := CallResolution.declaration.inj
      ((ExpressionForm.call.inj (form.symm.trans shape.call.form)).2.2)
    exact same ▸ site

/-- Original source forms and metadata close residuals from this same accepted
Header body. The caller supplies no expression or statement grammar. -/
theorem ActualHeader.root_compiler_admission
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (site : DirectSite directRows shape.call.instantiation)
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
        fixture.recipe.compiled.indexed.base.plan instantiation) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header directRows := by
  have bodyEq : actual.header.function.body = [shape.statement.id] := by
    rw [actual.aligned.function]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, shape.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source (DirectSite directRows) := by
    rw [actual.source]
    exact shape.metadata nodes actual.prepared.named noLocals
  apply AcceptedNamedBodyExpressionAdmission.of_returning actual.prepared actual.aligned metadata
    supported (by rw [actual.source]; exact shape.direct_coverage nodes site)
    bodyEq (by rw [actual.source]; exact shape.statementFound) shape.statementForm
    (by rw [actual.source]; exact shape.reached_forms)
    (fun id _ initializer => ?_)
    (by rw [actual.source]; exact shape.reached_arguments) (show shape.Reached shape.call.value.node.id from .inl rfl) fixture.source_wellFormed
  obtain ⟨initializer⟩ := initializer
  have found := initializer.found
  simp only [noLocals, List.find?_nil, Option.filter_none] at found
  cases found

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ActualHeader.key {fixture : CompiledFixture}
    {row : SourceSpecialization.SpecializedFunction} (actual : ActualHeader fixture row) :
    actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

theorem ObservedRow.keys_ne {fixture : CompiledFixture} {leftSignature rightSignature : ProgramFunctionSignature}
    (left : ObservedRow fixture leftSignature) (right : ObservedRow fixture rightSignature)
    (distinct : left.index ≠ right.index) : left.row.key ≠ right.row.key := by
  intro same
  have globals : left.global.key = right.global.key := left.globalKey.trans (same.trans right.globalKey.symm)
  exact distinct (left.slot.unique right.slot globals).2

private theorem selected_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {root : SourceCoreIndexedSession.Root compiled}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (selected : RootSelection (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers root header) :
    header.named.signature.key = root.key := by
  obtain ⟨_, entry, _, shape, found⟩ := selected
  obtain ⟨named, index, first, namedKey, rootKey, _⟩ := shape
  obtain ⟨namedEq, _⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans first))
  rw [namedEq]
  exact namedKey.trans rootKey.symm

private theorem cast_key {left right : SourceCoreUnifiedCompilation.Compiled}
    (same : left = right) (root : SourceCoreIndexedSession.Root left) :
    (same ▸ root).key = root.key := by
  cases same
  rfl

private theorem started_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {recipe : SourceCoreIndexedSession.Recipe}
    {prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe}
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    (request : Started headers prepared publicCheckpoint session key arguments fuel world store) :
    request.root.key = key := by
  have keyEq := of_decide_eq_true (List.find?_some
    (p := fun root : SourceCoreIndexedSession.Root recipe.compiled => decide (root.key = key))
    request.started.selected)
  exact (cast_key (SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm request.root).symm.trans keyEq

theorem selected_word_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (relayWordHeader : ActualHeader fixture observed.relayWordRow.row)
    (relayBoolHeader : ActualHeader fixture observed.relayBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    (identityWordHeader : ActualHeader fixture observed.identityWordRow.row)
    (identityBoolHeader : ActualHeader fixture observed.identityBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, relayWordHeader.header, relayBoolHeader.header, useWordHeader.header, useBoolHeader.header, identityWordHeader.header, identityBoolHeader.header] root header)
    (key : root.key = observed.wordRow.row.key) : header = wordHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, relayWordHeader.header, relayBoolHeader.header, useWordHeader.header, useBoolHeader.header, identityWordHeader.header, identityBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same | same | same | same | same
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, boolHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.boolRow.index := by
      intro equal
      have impossible : 0 = 1 := (List.getElem_inj
        (i := 0) (j := 1) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.boolRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeWordHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.makeWordRow.index := by
      intro equal
      have impossible : 0 = 2 := (List.getElem_inj
        (i := 0) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.makeWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeBoolHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.makeBoolRow.index := by
      intro equal
      have impossible : 0 = 3 := (List.getElem_inj
        (i := 0) (j := 3) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.makeBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, relayWordHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.relayWordRow.index := by
      intro equal
      have impossible : 0 = 4 := (List.getElem_inj
        (i := 0) (j := 4) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.relayWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, relayBoolHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.relayBoolRow.index := by
      intro equal
      have impossible : 0 = 5 := (List.getElem_inj
        (i := 0) (j := 5) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.relayBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useWordHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.useWordRow.index := by
      intro equal
      have impossible : 0 = 6 := (List.getElem_inj
        (i := 0) (j := 6) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.useWordRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useBoolHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.useBoolRow.index := by
      intro equal
      have impossible : 0 = 7 := (List.getElem_inj
        (i := 0) (j := 7) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.useBoolRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, identityWordHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.identityWordRow.index := by
      intro equal
      have impossible : 0 = 8 := (List.getElem_inj
        (i := 0) (j := 8) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.identityWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, identityBoolHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.identityBoolRow.index := by
      intro equal
      have impossible : 0 = 9 := (List.getElem_inj
        (i := 0) (j := 9) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.identityBoolRow distinct) headerKey.symm)

theorem selected_bool_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (relayWordHeader : ActualHeader fixture observed.relayWordRow.row)
    (relayBoolHeader : ActualHeader fixture observed.relayBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    (identityWordHeader : ActualHeader fixture observed.identityWordRow.row)
    (identityBoolHeader : ActualHeader fixture observed.identityBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, relayWordHeader.header, relayBoolHeader.header, useWordHeader.header, useBoolHeader.header, identityWordHeader.header, identityBoolHeader.header] root header)
    (key : root.key = observed.boolRow.row.key) : header = boolHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, relayWordHeader.header, relayBoolHeader.header, useWordHeader.header, useBoolHeader.header, identityWordHeader.header, identityBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same | same | same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, wordHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.wordRow.index := by
      intro equal
      have impossible : 1 = 0 := (List.getElem_inj
        (i := 1) (j := 0) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.wordRow.toObservedRow distinct) headerKey.symm)
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, makeWordHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.makeWordRow.index := by
      intro equal
      have impossible : 1 = 2 := (List.getElem_inj
        (i := 1) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.makeWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeBoolHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.makeBoolRow.index := by
      intro equal
      have impossible : 1 = 3 := (List.getElem_inj
        (i := 1) (j := 3) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.makeBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, relayWordHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.relayWordRow.index := by
      intro equal
      have impossible : 1 = 4 := (List.getElem_inj
        (i := 1) (j := 4) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.relayWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, relayBoolHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.relayBoolRow.index := by
      intro equal
      have impossible : 1 = 5 := (List.getElem_inj
        (i := 1) (j := 5) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.relayBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useWordHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.useWordRow.index := by
      intro equal
      have impossible : 1 = 6 := (List.getElem_inj
        (i := 1) (j := 6) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.useWordRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useBoolHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.useBoolRow.index := by
      intro equal
      have impossible : 1 = 7 := (List.getElem_inj
        (i := 1) (j := 7) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.useBoolRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, identityWordHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.identityWordRow.index := by
      intro equal
      have impossible : 1 = 8 := (List.getElem_inj
        (i := 1) (j := 8) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.identityWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, identityBoolHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.identityBoolRow.index := by
      intro equal
      have impossible : 1 = 9 := (List.getElem_inj
        (i := 1) (j := 9) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.identityBoolRow distinct) headerKey.symm)

theorem selected_useWord_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (relayWordHeader : ActualHeader fixture observed.relayWordRow.row)
    (relayBoolHeader : ActualHeader fixture observed.relayBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    (identityWordHeader : ActualHeader fixture observed.identityWordRow.row)
    (identityBoolHeader : ActualHeader fixture observed.identityBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, relayWordHeader.header, relayBoolHeader.header, useWordHeader.header, useBoolHeader.header, identityWordHeader.header, identityBoolHeader.header] root header)
    (key : root.key = observed.useWordRow.row.key) : header = useWordHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, relayWordHeader.header, relayBoolHeader.header, useWordHeader.header, useBoolHeader.header, identityWordHeader.header, identityBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same | same | same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, wordHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.wordRow.index := by
      intro equal
      have impossible : 6 = 0 := (List.getElem_inj
        (i := 6) (j := 0) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.wordRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, boolHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.boolRow.index := by
      intro equal
      have impossible : 6 = 1 := (List.getElem_inj
        (i := 6) (j := 1) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.boolRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeWordHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.makeWordRow.index := by
      intro equal
      have impossible : 6 = 2 := (List.getElem_inj
        (i := 6) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.makeWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeBoolHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.makeBoolRow.index := by
      intro equal
      have impossible : 6 = 3 := (List.getElem_inj
        (i := 6) (j := 3) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.makeBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, relayWordHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.relayWordRow.index := by
      intro equal
      have impossible : 6 = 4 := (List.getElem_inj
        (i := 6) (j := 4) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.relayWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, relayBoolHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.relayBoolRow.index := by
      intro equal
      have impossible : 6 = 5 := (List.getElem_inj
        (i := 6) (j := 5) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.relayBoolRow distinct) headerKey.symm)
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, useBoolHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.useBoolRow.index := by
      intro equal
      have impossible : 6 = 7 := (List.getElem_inj
        (i := 6) (j := 7) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.useBoolRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, identityWordHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.identityWordRow.index := by
      intro equal
      have impossible : 6 = 8 := (List.getElem_inj
        (i := 6) (j := 8) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.identityWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, identityBoolHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.identityBoolRow.index := by
      intro equal
      have impossible : 6 = 9 := (List.getElem_inj
        (i := 6) (j := 9) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.identityBoolRow distinct) headerKey.symm)

theorem selected_useBool_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (relayWordHeader : ActualHeader fixture observed.relayWordRow.row)
    (relayBoolHeader : ActualHeader fixture observed.relayBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    (identityWordHeader : ActualHeader fixture observed.identityWordRow.row)
    (identityBoolHeader : ActualHeader fixture observed.identityBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, relayWordHeader.header, relayBoolHeader.header, useWordHeader.header, useBoolHeader.header, identityWordHeader.header, identityBoolHeader.header] root header)
    (key : root.key = observed.useBoolRow.row.key) : header = useBoolHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, relayWordHeader.header, relayBoolHeader.header, useWordHeader.header, useBoolHeader.header, identityWordHeader.header, identityBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same | same | same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, wordHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.wordRow.index := by
      intro equal
      have impossible : 7 = 0 := (List.getElem_inj
        (i := 7) (j := 0) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.wordRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, boolHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.boolRow.index := by
      intro equal
      have impossible : 7 = 1 := (List.getElem_inj
        (i := 7) (j := 1) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.boolRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeWordHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.makeWordRow.index := by
      intro equal
      have impossible : 7 = 2 := (List.getElem_inj
        (i := 7) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.makeWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeBoolHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.makeBoolRow.index := by
      intro equal
      have impossible : 7 = 3 := (List.getElem_inj
        (i := 7) (j := 3) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.makeBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, relayWordHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.relayWordRow.index := by
      intro equal
      have impossible : 7 = 4 := (List.getElem_inj
        (i := 7) (j := 4) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.relayWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, relayBoolHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.relayBoolRow.index := by
      intro equal
      have impossible : 7 = 5 := (List.getElem_inj
        (i := 7) (j := 5) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.relayBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useWordHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.useWordRow.index := by
      intro equal
      have impossible : 7 = 6 := (List.getElem_inj
        (i := 7) (j := 6) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.useWordRow.toObservedRow distinct) headerKey.symm)
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, identityWordHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.identityWordRow.index := by
      intro equal
      have impossible : 7 = 8 := (List.getElem_inj
        (i := 7) (j := 8) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.identityWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, identityBoolHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.identityBoolRow.index := by
      intro equal
      have impossible : 7 = 9 := (List.getElem_inj
        (i := 7) (j := 9) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.identityBoolRow distinct) headerKey.symm)

section StartedSelection
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (relayWordHeader : ActualHeader fixture observed.relayWordRow.row)
    (relayBoolHeader : ActualHeader fixture observed.relayBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    (identityWordHeader : ActualHeader fixture observed.identityWordRow.row)
    (identityBoolHeader : ActualHeader fixture observed.identityBoolRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}

theorem selected_word_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, relayWordHeader.header, relayBoolHeader.header, useWordHeader.header, useBoolHeader.header, identityWordHeader.header, identityBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.wordRow.row.key arguments fuel world store) : request.header = wordHeader.header := by
  subst headers
  exact selected_word_root wordHeader boolHeader makeWordHeader makeBoolHeader relayWordHeader relayBoolHeader useWordHeader useBoolHeader identityWordHeader identityBoolHeader request.selected (started_key request)

theorem selected_bool_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, relayWordHeader.header, relayBoolHeader.header, useWordHeader.header, useBoolHeader.header, identityWordHeader.header, identityBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.boolRow.row.key arguments fuel world store) : request.header = boolHeader.header := by
  subst headers
  exact selected_bool_root wordHeader boolHeader makeWordHeader makeBoolHeader relayWordHeader relayBoolHeader useWordHeader useBoolHeader identityWordHeader identityBoolHeader request.selected (started_key request)

theorem selected_useWord_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, relayWordHeader.header, relayBoolHeader.header, useWordHeader.header, useBoolHeader.header, identityWordHeader.header, identityBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.useWordRow.row.key arguments fuel world store) : request.header = useWordHeader.header := by
  subst headers
  exact selected_useWord_root wordHeader boolHeader makeWordHeader makeBoolHeader relayWordHeader relayBoolHeader useWordHeader useBoolHeader identityWordHeader identityBoolHeader request.selected (started_key request)

theorem selected_useBool_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, relayWordHeader.header, relayBoolHeader.header, useWordHeader.header, useBoolHeader.header, identityWordHeader.header, identityBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.useBoolRow.row.key arguments fuel world store) : request.header = useBoolHeader.header := by
  subst headers
  exact selected_useBool_root wordHeader boolHeader makeWordHeader makeBoolHeader relayWordHeader relayBoolHeader useWordHeader useBoolHeader identityWordHeader identityBoolHeader request.selected (started_key request)
end StartedSelection

theorem ActualHeader.word_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word, .word, .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.wordShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.wordShape.firstScheme, observed.wordShape.secondScheme,
    observed.wordShape.flagScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.word_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.types = [.word, .word, .bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.word_input_types

theorem ActualHeader.word_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.function.resultType = closureType .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.wordResultType

theorem ActualHeader.word_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.output = Core.CallableContract.functionType .unit .word := by
  have projected := actual.aligned.projection
  rw [actual.word_result_type] at projected
  simpa [closureType, SourceCoreCompatibleCatalog.Catalog.project,
    SourceCoreCompatibleCatalog.Catalog.functionType, observed.profile] using (Except.ok.inj projected).symm

theorem ActualHeader.bool_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.bool, .bool, .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.boolShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.boolShape.firstScheme, observed.boolShape.secondScheme,
    observed.boolShape.flagScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.bool_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.types = [.bool, .bool, .bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.bool_input_types

theorem ActualHeader.bool_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.function.resultType = closureType .bool := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.boolResultType

theorem ActualHeader.bool_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.output = Core.CallableContract.functionType .unit .bool := by
  have projected := actual.aligned.projection
  rw [actual.bool_result_type] at projected
  simpa [closureType, SourceCoreCompatibleCatalog.Catalog.project,
    SourceCoreCompatibleCatalog.Catalog.functionType, observed.profile] using (Except.ok.inj projected).symm

theorem ActualHeader.useWord_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useWordRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [closureType .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.useWordShape.body.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.useWordInputScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.useWord_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useWordRow.row) : actual.header.types = [closureType .word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.useWord_input_types

theorem ActualHeader.useWord_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useWordRow.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.useWordResultType

theorem ActualHeader.useWord_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useWordRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.useWord_result_type] at projected
  exact (Except.ok.inj projected).symm

theorem ActualHeader.useBool_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useBoolRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [closureType .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.useBoolShape.body.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.useBoolInputScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.useBool_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useBoolRow.row) : actual.header.types = [closureType .bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.useBool_input_types

theorem ActualHeader.useBool_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useBoolRow.row) : actual.header.function.resultType = .bool := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.useBoolResultType

theorem ActualHeader.useBool_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useBoolRow.row) : actual.header.output = .bool := by
  have projected := actual.aligned.projection
  rw [actual.useBool_result_type] at projected
  exact (Except.ok.inj projected).symm

def ObservedStages.descriptor_at {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature} (stages : ObservedStages fixture observed)
    (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.key]
  exact stages.descriptor

theorem OrdinaryInventory.header_list {fixture observed} (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedFiniteNamedInventories.headers inventory.rows =
      [inventory.wordHeader.header, inventory.boolHeader.header, inventory.makeWordHeader.header, inventory.makeBoolHeader.header, inventory.relayWordHeader.header, inventory.relayBoolHeader.header, inventory.useWordHeader.header, inventory.useBoolHeader.header, inventory.identityWordHeader.header, inventory.identityBoolHeader.header] := by
  simp only [OrdinaryInventory.rows, CallableIndexedOwnedPreparedFiniteNamedInventories.headers,
    inventory.wordAligned, inventory.boolAligned, inventory.makeWordAligned, inventory.makeBoolAligned, inventory.relayWordAligned, inventory.relayBoolAligned, inventory.useWordAligned, inventory.useBoolAligned, inventory.identityWordAligned, inventory.identityBoolAligned]

theorem OrdinaryInventory.indices {fixture observed} (given : OrdinaryInventory fixture observed) :
    [given.wordInput, given.boolInput, given.makeWordInput, given.makeBoolInput, given.relayWordInput, given.relayBoolInput, given.useWordInput, given.useBoolInput, given.identityWordInput, given.identityBoolInput].map (fun input => input.prepared.index) =
      [observed.wordRow.index, observed.boolRow.index, observed.makeWordRow.index, observed.makeBoolRow.index, observed.relayWordRow.index, observed.relayBoolRow.index, observed.useWordRow.index, observed.useBoolRow.index, observed.identityWordRow.index, observed.identityBoolRow.index] := by
  have word : given.wordInput.prepared.index = observed.wordRow.index := by
    have same : given.wordHeader.header.slot = given.wordInput.prepared.index := by
      rw [given.wordAligned]; exact given.wordPacket.aligned.slot
    exact same.symm.trans given.wordSlot
  have bool : given.boolInput.prepared.index = observed.boolRow.index := by
    have same : given.boolHeader.header.slot = given.boolInput.prepared.index := by
      rw [given.boolAligned]; exact given.boolPacket.aligned.slot
    exact same.symm.trans given.boolSlot
  have makeWord : given.makeWordInput.prepared.index = observed.makeWordRow.index := by
    have same : given.makeWordHeader.header.slot = given.makeWordInput.prepared.index := by
      rw [given.makeWordAligned]; exact given.makeWordPacket.aligned.slot
    exact same.symm.trans given.makeWordSlot
  have makeBool : given.makeBoolInput.prepared.index = observed.makeBoolRow.index := by
    have same : given.makeBoolHeader.header.slot = given.makeBoolInput.prepared.index := by
      rw [given.makeBoolAligned]; exact given.makeBoolPacket.aligned.slot
    exact same.symm.trans given.makeBoolSlot
  have relayWord : given.relayWordInput.prepared.index = observed.relayWordRow.index := by
    have same : given.relayWordHeader.header.slot = given.relayWordInput.prepared.index := by
      rw [given.relayWordAligned]; exact given.relayWordPacket.aligned.slot
    exact same.symm.trans given.relayWordSlot
  have relayBool : given.relayBoolInput.prepared.index = observed.relayBoolRow.index := by
    have same : given.relayBoolHeader.header.slot = given.relayBoolInput.prepared.index := by
      rw [given.relayBoolAligned]; exact given.relayBoolPacket.aligned.slot
    exact same.symm.trans given.relayBoolSlot
  have useWord : given.useWordInput.prepared.index = observed.useWordRow.index := by
    have same : given.useWordHeader.header.slot = given.useWordInput.prepared.index := by
      rw [given.useWordAligned]; exact given.useWordPacket.aligned.slot
    exact same.symm.trans given.useWordSlot
  have useBool : given.useBoolInput.prepared.index = observed.useBoolRow.index := by
    have same : given.useBoolHeader.header.slot = given.useBoolInput.prepared.index := by
      rw [given.useBoolAligned]; exact given.useBoolPacket.aligned.slot
    exact same.symm.trans given.useBoolSlot
  have identityWord : given.identityWordInput.prepared.index = observed.identityWordRow.index := by
    have same : given.identityWordHeader.header.slot = given.identityWordInput.prepared.index := by
      rw [given.identityWordAligned]; exact given.identityWordPacket.aligned.slot
    exact same.symm.trans given.identityWordSlot
  have identityBool : given.identityBoolInput.prepared.index = observed.identityBoolRow.index := by
    have same : given.identityBoolHeader.header.slot = given.identityBoolInput.prepared.index := by
      rw [given.identityBoolAligned]; exact given.identityBoolPacket.aligned.slot
    exact same.symm.trans given.identityBoolSlot
  simp only [List.map_cons, List.map_nil, word, bool, makeWord, makeBool, relayWord, relayBool, useWord, useBool, identityWord, identityBool]

theorem OrdinaryInventory.distinct {fixture observed} (given : OrdinaryInventory fixture observed) :
    ([given.wordInput, given.boolInput, given.makeWordInput, given.makeBoolInput, given.relayWordInput, given.relayBoolInput, given.useWordInput, given.useBoolInput, given.identityWordInput, given.identityBoolInput].map (fun input => input.prepared.index)).Nodup := by
  rw [given.indices]
  exact observed.ordinarySlotsDistinct

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceCertifiedHeaders
/-! Original observed rows identify the actual packets in an automatic catalog.
No Header order or separately assembled inventory is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence.Certified
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Eligible)

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}

theorem row_eligible (row : ObservedRow fixture signature) :
    Eligible fixture.recipe.compiled row.named.specialized := by
  rw [row.same]
  refine ⟨row.origin, ?_, row.ordinary, row.inputsOrdinary⟩
  intro parameter replacement member
  have scalar := of_decide_eq_true (List.all_eq_true.mp row.scalarRange (parameter, replacement) member)
  rcases scalar with rfl | rfl
  · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .word⟩
  · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .bool⟩

def selected_row (row : ObservedRow fixture signature) :
    CertifiedPublicSession.EligibleRow fixture.recipe.compiled row.row.key :=
  ⟨row.named, row.index, row.global, row.cached, row.slot, row.globalKey, row_eligible row⟩

/-- The chosen Header is literally the issued packet in this catalog. Full
named equality fixes its original specialized Source and dictionary. -/
theorem header_of_member
    (row : ObservedRow fixture signature)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (member : header ∈ headers rows)
    (named : header.named = row.named) :
    ∃ actual : ActualHeader fixture row.row, actual.header = header := by
  obtain ⟨input, packet, _retained, sameHeader⟩ := rows.mem_headers header member
  subst header
  have sameRow : input.row = row.row :=
    input.prepared.same.symm.trans
      ((congrArg (·.specialized) (packet.aligned.named.symm.trans named)).trans row.same)
  let actual : ActualHeader fixture input.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
    header := packet.header
    aligned := packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  have transported : ∀ (left right : SourceSpecialization.SpecializedFunction)
      (same : left = right) (value : ActualHeader fixture left),
      (same ▸ value : ActualHeader fixture right).header = value.header := by
    intro left right same value
    cases same
    rfl
  exact ⟨sameRow ▸ actual, transported _ _ sameRow actual⟩

end Tests.SourceCoreMethodOriginEvidence.Certified
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceSeed
/-! The initial method-bearing public call connects its actual bootstrap and input
encoding to the Source result and the full returned physical cache. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ObservedPublicRun.as_function_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ObservedFunctionCall first.session observed.wordRow.row.key [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
  ⟨⟨⟨first.checkpoint, first.started⟩, first.completion, first.executed⟩, first.handle, first.returned⟩

theorem ObservedPublicRun.initial_start {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    Nonempty (RecursiveNamedPublicPhysicalSessionInitial.Started inventory.rows fixture.recipePrepared
      inventory.wordHeader.header first.as_function_call.toCall.toStartedCall) := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  obtain ⟨selectedHeader, selected⟩ := RecursiveNamedPublicRootCoverage.selection_of_recipe
    prepared (List.mem_of_find?_eq_some started.selected) inventory.public_coverage
  have selectedEq : selectedHeader = inventory.wordHeader.header := by
    apply selected_word_root inventory.wordHeader inventory.boolHeader inventory.makeWordHeader inventory.makeBoolHeader inventory.relayWordHeader inventory.relayBoolHeader inventory.useWordHeader inventory.useBoolHeader inventory.identityWordHeader inventory.identityBoolHeader
      (root := root) (header := selectedHeader)
    · exact inventory.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.wordRow.row.key)) started.selected)
  subst selectedHeader
  exact ⟨{
    publicCompiled := fixture.facadeCompiled
    artifact := artifact, nativeSession := session, checkpoint := checkpoint, root := root
    world := world, store := store, native := native, encodedValues := encodedValues
    opened := opened, atSession := sessionAt, atCheckpoint := checkpointAt
    started := started, selected := selected, bootstrap := first.bootstrap
    bootstrapFuel := 102400, fresh := first.fresh, authority := first.authority
    ready := .single first.ready }⟩

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (inventory : OrdinaryInventory fixture observed)
    (distinct : ([inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.relayWordInput, inventory.relayBoolInput, inventory.useWordInput, inventory.useBoolInput, inventory.identityWordInput, inventory.identityBoolInput].map (fun input => input.prepared.index)).Nodup)
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = closureType .word ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState inventory receiver first.completion.session [entry],
        SourceCall inventory inventory.wordHeader.header
          (RecursiveStageRegistry.scope stages.sidecar [] inventory.wordHeader.header.function)
          ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value entry.source) state.heap := by
  obtain ⟨start⟩ := first.initial_start inventory
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      inventory.wordHeader.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] inventory.wordHeader.header.types := by
    rw [inventory.wordHeader.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  obtain ⟨entry, type, handle, state, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionInitial.first_function inventory.rows fixture.recipePrepared
      inventory.wordHeader.header inventory.wordHeader.header program distinct first.as_function_call start
      (word_simple seed (Core.Word.ofNatModulo 33) true) inputTypes inputMeanings (stages.descriptor_at inventory.wordHeader)
      (RecursiveStageRegistry.scope stages.sidecar [] inventory.wordHeader.header.function)
  exact ⟨entry, type.trans inventory.wordHeader.word_result_type, handle, state, trace⟩

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceInitialForward
/-! Initial Source success determines sufficient execution and export budgets
at the original public checkpoint. Every sufficient output appends its actual
new closure handle and retains all installed method cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
        ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
          entry.sourceType = closureType .word ∧ entry.source = source ∧
          completion.value = .function entry.handle ∧ entry.handle.sourceType = closureType .word ∧
          ∃ returned : RetainedState inventory receiver completion.session [entry], returned.heap = after

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (inventory : OrdinaryInventory fixture observed)
    (distinct : ([inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.relayWordInput, inventory.relayBoolInput, inventory.useWordInput, inventory.useBoolInput, inventory.identityWordInput, inventory.identityBoolInput].map
      (fun input => input.prepared.index)).Nodup)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow)
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall inventory inventory.wordHeader.header invocation ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value source) after) :
    InitialForwardAt inventory receiver first source after := by
  obtain ⟨start⟩ := first.initial_start inventory
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      inventory.wordHeader.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] inventory.wordHeader.header.types := by
    rw [inventory.wordHeader.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have result : SourceCoreRawMetadata.runtimeType inventory.wordHeader.header.function.resultType =
      .function .unit .word := by
    rw [inventory.wordHeader.word_result_type]
    rfl
  have enough := RecursiveNamedPublicPhysicalSessionInitialForward.first_function
    inventory.rows fixture.recipePrepared inventory.wordHeader.header inventory.wordHeader.header
    program distinct first.as_function_call.toCall.toStartedCall start (word_simple seed (Core.Word.ofNatModulo 33) true)
    inputTypes inputMeanings result trace
  obtain ⟨requiredExecution, requiredOutput, enough⟩ := enough
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, succeeded, ready, entry, entryType, sourceEq, returned, handleType, state, heap⟩ :=
    enough executionFuel outputFuel outcome executionBound outputBound resumed
  exact ⟨completion, succeeded, ready, entry, entryType.trans inventory.wordHeader.word_result_type,
    sourceEq, returned, handleType.trans inventory.wordHeader.word_result_type, state, heap⟩

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceStep
/-! Actual named calls with Word or Bool results continue the same retained session and Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.finished_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {inventory : OrdinaryInventory fixture observed} {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState inventory receiver session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (returned : call.completion.value = scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers inventory.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (registry : request.encodedValues.registry = state.receiving.result.context.registry)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState inventory receiver call.completion.session entries,
      SourceCall inventory request.header invocation state.heap arguments
        (.value scalar.source) after.heap := by
  exact RecursiveNamedPublicPhysicalSessionScalarStep.State.finished_call program fixture.recipePrepared state scalar call returned request inputs registry rawType nativeType descriptor invocation

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceFactoryForward
/-! Independent Source success supplies sufficient native and output fuel at
the original public checkpoint. Every sufficient resume retains the full
physical cache and the same Source heap and prior history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

abbrev FactoryForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key arguments)
    (resultType : TypeSystem.Ty) (source : Dynamic.Value)
    (after : Dynamic.Heap) : Prop :=
  RecursiveNamedPublicPhysicalSessionFunctionForward.FunctionForwardAt (entries := entries)
    inventory.rows inventory.wordHeader.header receiver.completion observed.profile fixture.recipe call.toCall.toStartedCall .unit resultType source after

theorem forward_factory {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {inventory : OrdinaryInventory fixture observed} {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState inventory receiver session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers inventory.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    {resultType : TypeSystem.Ty}
    (rawType : request.header.function.resultType = closureType resultType)
    (ready : session.ExportsReady)
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall inventory request.header invocation state.heap arguments (.value source) after) :
    FactoryForwardAt (entries := entries) inventory receiver call resultType source after := by
  exact RecursiveNamedPublicPhysicalSessionFunctionForward.forward_function program fixture.recipePrepared state call.toCall.toStartedCall request inputs
    (request.started.simple_registry state.registry simple) rawType ready trace

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceForward
/-! Independent Source success supplies sufficient native and output fuel at
the original public checkpoint. Every sufficient resume retains the full
physical cache and the same Source heap and prior history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

abbrev ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key arguments)
    (after : Dynamic.Heap) : Prop :=
  RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt (entries := entries)
    inventory.rows inventory.wordHeader.header receiver.completion observed.profile fixture.recipe scalar call.toStartedCall after

theorem forward_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {inventory : OrdinaryInventory fixture observed} {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState inventory receiver session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers inventory.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (registry : request.encodedValues.registry = state.receiving.result.context.registry)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (ready : session.ExportsReady)
    (program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers inventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) receiver.completion)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall inventory request.header invocation state.heap arguments (.value scalar.source) after) :
    ForwardAt (entries := entries) inventory receiver scalar call after := by
  exact RecursiveNamedPublicPhysicalSessionScalarForward.forward_call program fixture.recipePrepared state scalar call.toStartedCall request inputs registry rawType nativeType ready trace

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceUseCompilerSupport
/-! The original indirect caller retains its actual callee action. Its checked
metadata and original read occurrence close the accepted compiler trace. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open AcceptedNamedExpressionFlow

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
  {type : TypeSystem.Ty} {row : ObservedRow fixture signature}
  (shape : UseShape row.row.function signature type)

def UseShape.Reached (id : ExpressionId) : Prop :=
  id = shape.value.node.id ∨ id = shape.body.read.node.id

theorem UseShape.reached_form {id : ExpressionId} {node : ExpressionNode}
    (reached : shape.Reached id)
    (found : row.row.function.typedBody.lookupExpression? id = some node) :
    (∃ name binder, node.form = .reference name (.local binder)) ∨
      node.form = .call shape.body.read.node.id [] (.indirect shape.metadata) := by
  rcases reached with same | same
  · rw [same, shape.value.found] at found
    cases Option.some.inj found
    exact .inr shape.form
  · rw [same, shape.body.read.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, shape.body.read.form⟩

theorem UseShape.reached_indirect {id : ExpressionId} {node : ExpressionNode}
    (reached : shape.Reached id)
    (found : row.row.function.typedBody.lookupExpression? id = some node)
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (form : node.form = .call callee arguments (.indirect metadata)) :
    callee = shape.body.read.node.id ∧ arguments = [] := by
  rcases shape.reached_form reached found with ⟨name, binder, localForm⟩ | indirectForm
  · rw [localForm] at form
    cases form
  · have same := ExpressionForm.call.inj (form.symm.trans indirectForm)
    exact ⟨same.1, same.2.1⟩

theorem UseShape.no_direct
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    {id : ExpressionId} {node : ExpressionNode}
    (found : row.row.function.typedBody.lookupExpression? id = some node)
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation)) : False := by
  rcases shape.expressions nodes found with same | same
  all_goals subst node
  · rw [shape.body.read.form] at form; cases form
  · rw [shape.form] at form; cases form


theorem UseShape.reached_call_forms : ReachedCallForms row.row.function.typedBody shape.Reached := by
  intro id node reached found
  rcases shape.reached_form reached found with ⟨name, binder, form⟩ | form
  · exact .inl (form ▸ LeafForm.read name binder)
  · exact .inr (.inr ⟨_, _, _, form⟩)

theorem UseShape.reached_call_arguments
    (nodes : row.row.function.typedBody.nodes = shape.nodeList) :
    ReachedCallArguments row.row.function.typedBody shape.Reached := by
  constructor
  · intro id node _reached found callee arguments instantiation form argument member
    exact False.elim (shape.no_direct nodes found form)
  · intro id node reached found callee arguments metadata form
    obtain ⟨calleeEq, argumentsEq⟩ := shape.reached_indirect reached found form
    refine ⟨.inr calleeEq, ?_⟩
    intro argument member
    rw [argumentsEq] at member
    cases member

/-- The actual metadata check is transported to the same Header and projected
at each original indirect node. Accepted compiler children supply the grammar. -/
theorem ActualHeader.use_compiler_admission
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed row.named row.row.function.typedBody (DirectSite directRows))
    (metadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      fixture.recipe.compiled.indexed row.named row.row.function.typedBody (DirectSite directRows) = some ⟨metadata⟩)
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
        fixture.recipe.compiled.indexed.base.plan instantiation) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header directRows := by
  have bodyEq : actual.header.function.body = [shape.body.statement.id] := by
    rw [actual.aligned.function]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, shape.body.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have namedEq : actual.prepared.named = row.named :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named actual.prepared row.cached row.same
  have checked : ∃ receipt : PLift
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
        fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source (DirectSite directRows)),
      CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
        fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source (DirectSite directRows) = some receipt := by
    rw [namedEq, actual.source]
    exact ⟨⟨metadata⟩, metadataAccepted⟩
  obtain ⟨⟨actualMetadata⟩, actualAccepted⟩ := checked
  apply AcceptedNamedBodyExpressionAdmission.of_returning_calls actual.prepared actual.aligned actualMetadata
    supported (by
      intro id node found callee arguments instantiation form
      rw [actual.source] at found
      exact False.elim (shape.no_direct nodes found form))
    bodyEq (by rw [actual.source]; exact shape.body.statementFound) shape.body.statementForm
    (by rw [actual.source]; exact shape.reached_call_forms)
    (fun id _ initializer => ?_)
    (by rw [actual.source]; exact shape.reached_call_arguments nodes)
    (ReachedIndirectMetadata.of_accepted actualAccepted)
    (show shape.Reached shape.value.node.id from .inl rfl) fixture.source_wellFormed
  obtain ⟨initializer⟩ := initializer
  have found := initializer.found
  simp only [noLocals, List.find?_nil, Option.filter_none] at found
  cases found

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceProgramCertificate
/-! The original cache is checked with all ten actual ordinary roots pending.
The two factory closure sources and every method body are also pending.
Accepted compiler actions complete the same shared program certificate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure ObservedProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  pending : AcceptedProgramMethodCompletion.Pending fixture.recipe.compiled
    [observed.wordRow.index, observed.boolRow.index, observed.useWordRow.index, observed.useBoolRow.index, observed.relayWordRow.index, observed.relayBoolRow.index, observed.identityWordRow.index, observed.identityBoolRow.index, observed.makeWordRow.index, observed.makeBoolRow.index] [observed.makeWordRow.index, observed.makeBoolRow.index]
  accepted : AcceptedProgramMethodCompletion.certify fixture.recipe.compiled
    fixture.source_wellFormed [observed.wordRow.index, observed.boolRow.index, observed.useWordRow.index, observed.useBoolRow.index, observed.relayWordRow.index, observed.relayBoolRow.index, observed.identityWordRow.index, observed.identityBoolRow.index, observed.makeWordRow.index, observed.makeBoolRow.index] [observed.makeWordRow.index, observed.makeBoolRow.index] 64 = some pending
  wordSite : CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows observed.wordShape.call.instantiation
  wordAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
    pending.table.rows observed.wordShape.call.instantiation = some ⟨wordSite⟩
  boolSite : CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows observed.boolShape.call.instantiation
  boolAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
    pending.table.rows observed.boolShape.call.instantiation = some ⟨boolSite⟩
  useWordMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.useWordRow.named observed.useWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  useWordMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.useWordRow.named observed.useWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨useWordMetadata⟩
  useBoolMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.useBoolRow.named observed.useBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  useBoolMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.useBoolRow.named observed.useBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨useBoolMetadata⟩
  relayWordMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.relayWordRow.named observed.relayWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  relayWordMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.relayWordRow.named observed.relayWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨relayWordMetadata⟩
  relayBoolMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.relayBoolRow.named observed.relayBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  relayBoolMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.relayBoolRow.named observed.relayBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨relayBoolMetadata⟩
  identityWordMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.identityWordRow.named observed.identityWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  identityWordMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.identityWordRow.named observed.identityWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨identityWordMetadata⟩
  identityBoolMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.identityBoolRow.named observed.identityBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  identityBoolMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.identityBoolRow.named observed.identityBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨identityBoolMetadata⟩
  makeWordSite : CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows observed.makeWordShape.call.instantiation
  makeWordSiteAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
    pending.table.rows observed.makeWordShape.call.instantiation = some ⟨makeWordSite⟩
  makeWordMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.makeWordRow.named observed.makeWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  makeWordMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.makeWordRow.named observed.makeWordRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨makeWordMetadata⟩
  makeBoolSite : CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows observed.makeBoolShape.call.instantiation
  makeBoolSiteAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
    pending.table.rows observed.makeBoolShape.call.instantiation = some ⟨makeBoolSite⟩
  makeBoolMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed observed.makeBoolRow.named observed.makeBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows)
  makeBoolMetadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed observed.makeBoolRow.named observed.makeBoolRow.row.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite pending.table.rows) = some ⟨makeBoolMetadata⟩
  methods : ObservedMethodCompilers fixture pending.table.rows
  rows : ∀ row ∈ pending.table.rows, row ∈ [observed.wordRow.row, observed.boolRow.row, observed.makeWordRow.row, observed.makeBoolRow.row, observed.relayWordRow.row, observed.relayBoolRow.row, observed.useWordRow.row, observed.useBoolRow.row, observed.identityWordRow.row, observed.identityBoolRow.row]

private structure ObservedMetadata (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (rows : List SourceSpecialization.SpecializedFunction) : Type where
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    compiled.indexed named source (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite rows)
  accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata? compiled.indexed named source
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite rows) = some ⟨metadata⟩

private def observeMetadata (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (rows : List SourceSpecialization.SpecializedFunction) : IO (ObservedMetadata compiled named source rows) := do
  match accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata? compiled.indexed named source
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite rows) with
  | none => throw (IO.userError "original expression metadata rejected")
  | some metadata => pure ⟨metadata.down, accepted⟩

private structure ObservedSite (rows : List SourceSpecialization.SpecializedFunction)
    (instantiation : DeclarationInstantiation) : Type where
  site : CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite rows instantiation
  accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite? rows instantiation = some ⟨site⟩

private def observeSite (rows : List SourceSpecialization.SpecializedFunction)
    (instantiation : DeclarationInstantiation) : IO (ObservedSite rows instantiation) := do
  match accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite? rows instantiation with
  | none => throw (IO.userError "original factory closure direct target missing")
  | some site => pure ⟨site.down, accepted⟩

def observeProgramCertificate (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedProgramCertificate fixture observed) := do
  match accepted : AcceptedProgramMethodCompletion.certify fixture.recipe.compiled
      fixture.source_wellFormed [observed.wordRow.index, observed.boolRow.index, observed.useWordRow.index, observed.useBoolRow.index, observed.relayWordRow.index, observed.relayBoolRow.index, observed.identityWordRow.index, observed.identityBoolRow.index, observed.makeWordRow.index, observed.makeBoolRow.index] [observed.makeWordRow.index, observed.makeBoolRow.index] 64 with
  | none => throw (IO.userError "original method-origin complementary certification rejected")
  | some pending =>
      match wordAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
          pending.table.rows observed.wordShape.call.instantiation with
      | none => throw (IO.userError "original word direct target missing")
      | some ⟨wordSite⟩ =>
        match boolAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite?
            pending.table.rows observed.boolShape.call.instantiation with
        | none => throw (IO.userError "original bool direct target missing")
        | some ⟨boolSite⟩ =>
          let useWord ← observeMetadata fixture.recipe.compiled observed.useWordRow.named
            observed.useWordRow.row.function.typedBody pending.table.rows
          let useBool ← observeMetadata fixture.recipe.compiled observed.useBoolRow.named
            observed.useBoolRow.row.function.typedBody pending.table.rows
          let relayWord ← observeMetadata fixture.recipe.compiled observed.relayWordRow.named
            observed.relayWordRow.row.function.typedBody pending.table.rows
          let relayBool ← observeMetadata fixture.recipe.compiled observed.relayBoolRow.named
            observed.relayBoolRow.row.function.typedBody pending.table.rows
          let identityWord ← observeMetadata fixture.recipe.compiled observed.identityWordRow.named
            observed.identityWordRow.row.function.typedBody pending.table.rows
          let identityBool ← observeMetadata fixture.recipe.compiled observed.identityBoolRow.named
            observed.identityBoolRow.row.function.typedBody pending.table.rows
          let makeWordSite ← observeSite pending.table.rows observed.makeWordShape.call.instantiation
          let makeBoolSite ← observeSite pending.table.rows observed.makeBoolShape.call.instantiation
          let makeWord ← observeMetadata fixture.recipe.compiled observed.makeWordRow.named
            observed.makeWordRow.row.function.typedBody pending.table.rows
          let makeBool ← observeMetadata fixture.recipe.compiled observed.makeBoolRow.named
            observed.makeBoolRow.row.function.typedBody pending.table.rows
          let ⟨methods⟩ ← observeMethodCompilers fixture pending.table.rows
          if rows : pending.table.rows.all (fun row =>
              [observed.wordRow.row, observed.boolRow.row, observed.makeWordRow.row, observed.makeBoolRow.row, observed.relayWordRow.row, observed.relayBoolRow.row, observed.useWordRow.row, observed.useBoolRow.row, observed.identityWordRow.row, observed.identityBoolRow.row].any (fun expected => row == expected)) = true then
            pure ⟨pending, accepted, wordSite, wordAccepted, boolSite, boolAccepted,
              useWord.metadata, useWord.accepted,
              useBool.metadata, useBool.accepted,
              relayWord.metadata, relayWord.accepted,
              relayBool.metadata, relayBool.accepted,
              identityWord.metadata, identityWord.accepted,
              identityBool.metadata, identityBool.accepted,
              makeWordSite.site, makeWordSite.accepted, makeWord.metadata, makeWord.accepted,
              makeBoolSite.site, makeBoolSite.accepted, makeBool.metadata, makeBool.accepted, methods, by
              intro row member
              obtain ⟨expected, present, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp rows row member)
              exact (eq_of_beq same).symm ▸ present⟩
          else throw (IO.userError "actual direct table contains an unselected ordinary row")

theorem ObservedProgramCertificate.aligned_pending {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned
      [inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.relayWordInput, inventory.relayBoolInput, inventory.useWordInput, inventory.useBoolInput, inventory.identityWordInput, inventory.identityBoolInput] admission.pending.table.rows := by
  intro row member
  have present := admission.rows row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨inventory.wordInput, by simp, inventory.wordSame⟩
  · exact ⟨inventory.boolInput, by simp, inventory.boolSame⟩
  · exact ⟨inventory.makeWordInput, by simp, inventory.makeWordSame⟩
  · exact ⟨inventory.makeBoolInput, by simp, inventory.makeBoolSame⟩
  · exact ⟨inventory.relayWordInput, by simp, inventory.relayWordSame⟩
  · exact ⟨inventory.relayBoolInput, by simp, inventory.relayBoolSame⟩
  · exact ⟨inventory.useWordInput, by simp, inventory.useWordSame⟩
  · exact ⟨inventory.useBoolInput, by simp, inventory.useBoolSame⟩
  · exact ⟨inventory.identityWordInput, by simp, inventory.identityWordSame⟩
  · exact ⟨inventory.identityBoolInput, by simp, inventory.identityBoolSame⟩

/-- Each selected root is derived from its actual Header, then transported
back to that same cached function. Other pending certificate fields are unused. -/
theorem ObservedProgramCertificate.word_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.wordRow.named observed.wordRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.wordRow.named.specialized.function.typedBody)
      observed.wordRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.wordHeader.prepared inventory.wordHeader.aligned
    observed.wordRow.cached observed.wordRow.same
    (inventory.wordHeader.root_compiler_admission observed.wordShape observed.wordNodes observed.noLocals
      admission.wordSite (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.bool_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.boolRow.named observed.boolRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.boolRow.named.specialized.function.typedBody)
      observed.boolRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.boolHeader.prepared inventory.boolHeader.aligned
    observed.boolRow.cached observed.boolRow.same
    (inventory.boolHeader.root_compiler_admission observed.boolShape observed.boolNodes observed.noLocals
      admission.boolSite (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.useWord_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.useWordRow.named observed.useWordRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.useWordRow.named.specialized.function.typedBody)
      observed.useWordRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.useWordHeader.prepared inventory.useWordHeader.aligned
    observed.useWordRow.cached observed.useWordRow.same
    (inventory.useWordHeader.use_compiler_admission observed.useWordShape observed.useWordNodes observed.noLocals
      admission.useWordMetadata admission.useWordMetadataAccepted (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.useBool_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.useBoolRow.named observed.useBoolRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.useBoolRow.named.specialized.function.typedBody)
      observed.useBoolRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.useBoolHeader.prepared inventory.useBoolHeader.aligned
    observed.useBoolRow.cached observed.useBoolRow.same
    (inventory.useBoolHeader.use_compiler_admission observed.useBoolShape observed.useBoolNodes observed.noLocals
      admission.useBoolMetadata admission.useBoolMetadataAccepted (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.relayWord_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.relayWordRow.named observed.relayWordRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.relayWordRow.named.specialized.function.typedBody)
      observed.relayWordRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.relayWordHeader.prepared inventory.relayWordHeader.aligned
    observed.relayWordRow.cached observed.relayWordRow.same
    (inventory.relayWordHeader.relay_compiler_admission observed.relayWordShape observed.relayWordNodes observed.noLocals
      admission.relayWordMetadata admission.relayWordMetadataAccepted (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.relayBool_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.relayBoolRow.named observed.relayBoolRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.relayBoolRow.named.specialized.function.typedBody)
      observed.relayBoolRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.relayBoolHeader.prepared inventory.relayBoolHeader.aligned
    observed.relayBoolRow.cached observed.relayBoolRow.same
    (inventory.relayBoolHeader.relay_compiler_admission observed.relayBoolShape observed.relayBoolNodes observed.noLocals
      admission.relayBoolMetadata admission.relayBoolMetadataAccepted (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.identityWord_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.identityWordRow.named observed.identityWordRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.identityWordRow.named.specialized.function.typedBody)
      observed.identityWordRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.identityWordHeader.prepared inventory.identityWordHeader.aligned
    observed.identityWordRow.cached observed.identityWordRow.same
    (inventory.identityWordHeader.identity_compiler_admission observed.identityWordShape observed.identityWordNodes observed.noLocals
      admission.identityWordMetadata (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.identityBool_source_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission fixture.recipe.compiled
      observed.identityBoolRow.named observed.identityBoolRow.named.specialized.function.typedBody
      (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements observed.identityBoolRow.named.specialized.function.typedBody)
      observed.identityBoolRow.named.specialized.function.inferredBodyType admission.pending.table.rows := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact AcceptedNamedBodyAdmission.source_of_header inventory.identityBoolHeader.prepared inventory.identityBoolHeader.aligned
    observed.identityBoolRow.cached observed.identityBoolRow.same
    (inventory.identityBoolHeader.identity_compiler_admission observed.identityBoolShape observed.identityBoolNodes observed.noLocals
      admission.identityBoolMetadata (fun _ site => site.supported (admission.aligned_pending inventory)))

theorem ObservedProgramCertificate.makeWord_closure_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate fixture.recipe.compiled
      observed.makeWordRow.named admission.pending.table.rows false := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact inventory.makeWordHeader.closure_compiler_source observed.makeWordShape observed.makeWordNodes
    observed.noLocals admission.makeWordMetadata admission.makeWordSite
    (fun _ site => site.supported (admission.aligned_pending inventory))

theorem ObservedProgramCertificate.makeBool_closure_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate fixture.recipe.compiled
      observed.makeBoolRow.named admission.pending.table.rows false := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact inventory.makeBoolHeader.closure_compiler_source observed.makeBoolShape observed.makeBoolNodes
    observed.noLocals admission.makeBoolMetadata admission.makeBoolSite
    (fun _ site => site.supported (admission.aligned_pending inventory))

/-- Selection uses actual cache indices. The original complete Certificate is
constructed only after every accepted compiler root fills its own position. -/
def ObservedProgramCertificate.certificate {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    CallableIndexedOwnedPreparedProgramAdmission.Certificate fixture.recipe.compiled :=
  admission.pending.complete_receipts (by
    intro position member named selected
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have same : named = observed.wordRow.named :=
        Option.some.inj (selected.symm.trans observed.wordRow.cached)
      subst named
      exact ⟨.scoped admission.word_source_admission⟩
    · have same : named = observed.boolRow.named :=
        Option.some.inj (selected.symm.trans observed.boolRow.cached)
      subst named
      exact ⟨.scoped admission.bool_source_admission⟩
    · have same : named = observed.useWordRow.named :=
        Option.some.inj (selected.symm.trans observed.useWordRow.cached)
      subst named
      exact ⟨.scoped admission.useWord_source_admission⟩
    · have same : named = observed.useBoolRow.named :=
        Option.some.inj (selected.symm.trans observed.useBoolRow.cached)
      subst named
      exact ⟨.scoped admission.useBool_source_admission⟩
    · have same : named = observed.relayWordRow.named :=
        Option.some.inj (selected.symm.trans observed.relayWordRow.cached)
      subst named
      exact ⟨.scoped admission.relayWord_source_admission⟩
    · have same : named = observed.relayBoolRow.named :=
        Option.some.inj (selected.symm.trans observed.relayBoolRow.cached)
      subst named
      exact ⟨.scoped admission.relayBool_source_admission⟩
    · have same : named = observed.identityWordRow.named :=
        Option.some.inj (selected.symm.trans observed.identityWordRow.cached)
      subst named
      exact ⟨.scoped admission.identityWord_source_admission⟩
    · have same : named = observed.identityBoolRow.named :=
        Option.some.inj (selected.symm.trans observed.identityBoolRow.cached)
      subst named
      exact ⟨.scoped admission.identityBool_source_admission⟩
    · have same : named = observed.makeWordRow.named :=
        Option.some.inj (selected.symm.trans observed.makeWordRow.cached)
      subst named
      obtain ⟨certificate⟩ := observed.makeWord_factory_certificate
      exact ⟨.formation certificate⟩
    · have same : named = observed.makeBoolRow.named :=
        Option.some.inj (selected.symm.trans observed.makeBoolRow.cached)
      subst named
      obtain ⟨certificate⟩ := observed.makeBool_factory_certificate
      exact ⟨.formation certificate⟩) (by
    intro position member named selected
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · have same : named = observed.makeWordRow.named :=
        Option.some.inj (selected.symm.trans observed.makeWordRow.cached)
      subst named
      exact admission.makeWord_closure_source
    · have same : named = observed.makeBoolRow.named :=
        Option.some.inj (selected.symm.trans observed.makeBoolRow.cached)
      subst named
      exact admission.makeBool_closure_source)
    (admission.methods.complete admission.pending.table admission.pending.catalog observed.noLocals)

theorem ObservedProgramCertificate.aligned {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (inventory : OrdinaryInventory fixture observed) :
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned
      [inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.relayWordInput, inventory.relayBoolInput, inventory.useWordInput, inventory.useBoolInput, inventory.identityWordInput, inventory.identityBoolInput] admission.certificate.table.rows :=
  admission.aligned_pending inventory

/-- The primary production entry point constructs its own complete eligible
ordinary catalog and closes table alignment without the selected subset. -/
theorem ObservedProgramCertificate.automatic_catalog {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed) :
    ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
      Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
        (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        receiver.completion) := by
  exact admission.certificate.issue fixture.source_wellFormed fixture.recipePrepared receiver.issued
    receiver.registry observed.wordRow.entryMember (by rw [fixture.sameProgram]; exact fixture.checked)

/-- This proof is exercised by the same runtime-produced certificate used by
the seven-call regression; catalog construction is kept inside the proof. -/
theorem ObservedProgramCertificate.automatic_catalog_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
        Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
          (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
          receiver.completion) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, admission.automatic_catalog receiver⟩

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceSupports
/-! The single actual program certificate supplies named, closure and method
support together. The fixture retains only its original public header order. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed)
    extends OrdinaryInventory fixture observed where
  distinct : ([wordInput, boolInput, makeWordInput, makeBoolInput, relayWordInput, relayBoolInput, useWordInput, useBoolInput, identityWordInput, identityBoolInput].map (fun input => input.prepared.index)).Nodup
  program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
    (headers toOrdinaryInventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    completion

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (StaticSupportPackage fixture observed receiver.completion) := by
  obtain ⟨given⟩ := ordinary_inventory fixture observed
  obtain ⟨program⟩ := admission.certificate.issue_for_checked fixture.source_wellFormed
    fixture.recipePrepared receiver.issued receiver.registry observed.wordRow.entryMember
    given.rows (admission.aligned given) (by rw [fixture.sameProgram]; exact fixture.checked)
  exact ⟨{
    toOrdinaryInventory := given
    distinct := given.distinct
    program := program }⟩

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceFamily
/-! Public session proofs consume the static package generated by the actual
whole-program certificate. Body laws remain internal to production support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem StaticSupportPackage.program_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) (support : StaticSupportPackage fixture observed receiver.completion) :
    Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers support.toOrdinaryInventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      receiver.completion) := ⟨support.program⟩

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidencePublicExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  registry : request.encodedValues.registry = before.receiving.result.context.registry
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session entries
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value scalar.source) after.heap

structure FactoryMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (resultType : TypeSystem.Ty) (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session (entries ++ [entry])
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value entry.source) after.heap

theorem RetainedState.word_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Core.Word) (flag : Bool)
    (call : ObservedFunctionCall session observed.wordRow.row.key [.word value, .word next, .bool flag])
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.wordHeader.header call .word [.word value, .word next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_inputs value next flag
  have raw : request.header.function.resultType = closureType .word := by
    rw [selected, support.wordHeader.word_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.wordHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (word_simple value next flag) descriptor support.program invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by simpa only [selected] using trace⟩⟩

theorem RetainedState.bool_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Bool) (flag : Bool)
    (call : ObservedFunctionCall session observed.boolRow.row.key [.bool value, .bool next, .bool flag])
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.boolHeader.header call .bool [.bool value, .bool next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_inputs value next flag
  have raw : request.header.function.resultType = closureType .bool := by
    rw [selected, support.boolHeader.bool_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.boolHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (bool_simple value next flag) descriptor support.program invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by simpa only [selected] using trace⟩⟩

theorem RetainedState.useWord_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useWordRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useWordHeader.header (.word value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useWordHeader.header :=
    selected_useWord_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useWordHeader.useWord_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [selected, support.useWordHeader.useWord_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [selected, support.useWordHeader.useWord_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useWordHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.word value) call returned request inputs registry raw native descriptor
    support.program invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by simpa only [selected] using trace⟩⟩

theorem RetainedState.useBool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .bool)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Bool) (call : ObservedCall session observed.useBoolRow.row.key [.function handle])
    (returned : call.completion.value = .bool value)
    (stages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useBoolHeader.header (.bool value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useBoolHeader.header :=
    selected_useBool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useBoolHeader.useBool_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.bool value : ScalarOutput).sourceType := by
    rw [selected, support.useBoolHeader.useBool_result_type]; rfl
  have native : request.header.output = (.bool value : ScalarOutput).nativeType := by
    rw [selected, support.useBoolHeader.useBool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useBoolHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.bool value) call returned request inputs registry raw native descriptor
    support.program invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by simpa only [selected] using trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  firstEntry : Entry
  firstType : firstEntry.sourceType = closureType .word
  firstHandle : firstEntry.handle = sequence.first.handle
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session [firstEntry]
  firstTrace : SourceCall support.toOrdinaryInventory support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value firstEntry.source) initial.heap
  secondMeaning : FactoryMeaning initial support.boolHeader.header sequence.second .bool [.bool false, .bool true, .bool true]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  firstReadMeaning : CallMeaning secondMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.firstRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdMeaning : FactoryMeaning firstReadMeaning.after support.wordHeader.header sequence.third .word [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  secondReadMeaning : CallMeaning thirdMeaning.after support.useBoolHeader.header (.bool true) sequence.secondRead [secondMeaning.entry.source]
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  repeatedReadMeaning : CallMeaning secondReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdReadMeaning : CallMeaning repeatedReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead [thirdMeaning.entry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)

theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) :
    meaning.firstEntry.handle ≠ meaning.secondMeaning.entry.handle ∧
      meaning.firstEntry.handle ≠ meaning.thirdMeaning.entry.handle ∧
      meaning.secondMeaning.entry.handle ≠ meaning.thirdMeaning.entry.handle := by
  rw [meaning.firstHandle, meaning.secondMeaning.handleEq, meaning.thirdMeaning.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed admission receiver
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    support.program wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_factory_meaning support initial false true true sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.useWord_meaning support second.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.firstRead sequence.firstValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_factory_meaning support firstRead.after
    (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.useBool_meaning support third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.useWord_meaning support secondRead.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.repeatedRead sequence.repeatedValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.useWord_meaning support repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55) sequence.thirdRead sequence.thirdValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages useWordStages useBoolStages admission sequence receiver⟩

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceSequenceForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (ready : session.ExportsReady) :
    ForwardAt (entries := entries) support.toOrdinaryInventory receiver scalar call meaning.after.heap := by
  apply forward_call before scalar call meaning.request meaning.inputs meaning.registry meaning.rawType meaning.nativeType ready
    support.program
  rw [meaning.headerEq]
  exact meaning.trace

theorem FactoryMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFunctionCall session key publicArguments} {resultType : TypeSystem.Ty}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : FactoryMeaning before header call resultType arguments invocation)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (ready : session.ExportsReady) :
    FactoryForwardAt (entries := entries) support.toOrdinaryInventory receiver call resultType meaning.entry.source meaning.after.heap := by
  apply forward_factory before call meaning.request meaning.inputs simple meaning.rawType ready
    support.program
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support.toOrdinaryInventory receiver sequence.first meaning.firstEntry.source meaning.initial.heap
  second : FactoryForwardAt (entries := [meaning.firstEntry]) meaning.support.toOrdinaryInventory receiver sequence.second .bool
    meaning.secondMeaning.entry.source meaning.secondMeaning.after.heap
  firstRead : ForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.firstRead meaning.firstReadMeaning.after.heap
  third : FactoryForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry]) meaning.support.toOrdinaryInventory receiver
    sequence.third .word meaning.thirdMeaning.entry.source meaning.thirdMeaning.after.heap
  secondRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.bool true) sequence.secondRead meaning.secondReadMeaning.after.heap
  repeatedRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead meaning.repeatedReadMeaning.after.heap
  thirdRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead meaning.thirdReadMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver)
    : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨forward_initial meaning.support.toOrdinaryInventory meaning.support.distinct sequence.first
      meaning.support.program
      meaning.firstTrace,
    meaning.secondMeaning.forward (bool_simple false true true) firstReady,
    meaning.firstReadMeaning.forward secondReady,
    meaning.thirdMeaning.forward (word_simple (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false) firstReadReady,
    meaning.secondReadMeaning.forward thirdReady,
    meaning.repeatedReadMeaning.forward secondReadReady,
    meaning.thirdReadMeaning.forward repeatedReady⟩

theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    admission sequence
  exact ⟨receiver, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let admission ← observeProgramCertificate fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _automatic := admission.automatic_catalog_initial
  have _meaning := closed_sequence_forward_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    admission sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,40,67,149,176,258,340,403] do
    throw (IO.userError s!"method scoped stores changed: {reprStr stores}")
  IO.println "METHOD_ORIGIN_EVIDENCE_FORWARD_PASS: seven Source calls; all seven sufficient public fuel bounds; three retained closures; scalar33/true/33/55; generic implementation substitutions, own method Mark dictionaries, and constrained direct calls"

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceCertifiedMeaning
/-! The original public calls retain Source heaps and handles in the catalog
issued from their program certificate. Each call keeps its actual selected Header. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.Certified
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicPhysicalSessionState (SourceCall)
open CertifiedPublicSession (Issued Initial)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure FirstMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) where
  initial : Initial issued first.as_function_call.toCall.toStartedCall
  actual : ActualHeader fixture observed.wordRow.row
  headerEq : initial.header = actual.header
  entry : Entry
  entryType : entry.sourceType = closureType .word
  handleEq : entry.handle = first.handle
  after : issued.State initial.header first.completion.session [entry]
  trace : RecursiveNamedPublicPhysicalSessionState.SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value entry.source) after.heap

structure FunctionMeaning
    (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    (stages : ObservedStages fixture row)
    {arguments : List SourceCorePublicValues.Value} (call : ObservedFunctionCall session row.row.key arguments)
    (resultType : TypeSystem.Ty) (sourceArguments : List Dynamic.Value) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session row.row.key arguments runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture row.row
  headerEq : request.header = actual.header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) arguments sourceArguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : issued.State anchor call.completion.session (entries ++ [entry])
  trace : RecursiveNamedPublicPhysicalSessionState.SourceCall anchor request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
    before.heap sourceArguments (.value entry.source) after.heap

structure ScalarMeaning
    (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    (stages : ObservedStages fixture row)
    {arguments : List SourceCorePublicValues.Value} (call : ObservedCall session row.row.key arguments)
    (scalar : ScalarOutput) (sourceArguments : List Dynamic.Value) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session row.row.key arguments runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture row.row
  headerEq : request.header = actual.header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) arguments sourceArguments
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : issued.State anchor call.completion.session entries
  trace : RecursiveNamedPublicPhysicalSessionState.SourceCall anchor request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
    before.heap sourceArguments (.value scalar.source) after.heap

theorem FirstMeaning.forward {issued : Issued fixture.recipe}
    {stages : ObservedStages fixture observed.wordRow.toObservedRow}
    {first : ObservedPublicRun fixture observed.wordRow.toObservedRow}
    (meaning : FirstMeaning issued stages first) :
    RecursiveNamedPublicPhysicalSessionInitialForward.ForwardAt issued.catalog.rows meaning.initial.header
      meaning.initial.header issued.support first.as_function_call.toCall.toStartedCall meaning.entry.source meaning.after.heap := by
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      meaning.initial.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      meaning.initial.header.types := by
    rw [meaning.headerEq, meaning.actual.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have functionResult : SourceCoreRawMetadata.runtimeType meaning.initial.header.function.resultType =
      .function .unit .word := by
    rw [meaning.headerEq, meaning.actual.word_result_type]
    rfl
  exact meaning.initial.forward_function (word_simple seed (Core.Word.ofNatModulo 33) true)
    inputTypes inputMeanings functionResult meaning.trace

theorem FunctionMeaning.forward {issued : Issued fixture.recipe}
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} {before : issued.State anchor session entries}
    {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature}
    {stages : ObservedStages fixture row}
    {arguments : List SourceCorePublicValues.Value} {call : ObservedFunctionCall session row.row.key arguments}
    {resultType : TypeSystem.Ty} {sourceArguments : List Dynamic.Value}
    (meaning : FunctionMeaning issued before row stages call resultType sourceArguments)
    (ready : session.ExportsReady) :
    RecursiveNamedPublicPhysicalSessionFunctionForward.FunctionForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe
      call.toCall.toStartedCall .unit resultType meaning.entry.source meaning.after.heap :=
  issued.forward_function before call.toCall.toStartedCall meaning.request meaning.inputs meaning.rawType ready meaning.trace

theorem ScalarMeaning.forward {issued : Issued fixture.recipe}
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} {before : issued.State anchor session entries}
    {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature}
    {stages : ObservedStages fixture row}
    {arguments : List SourceCorePublicValues.Value} {call : ObservedCall session row.row.key arguments}
    {scalar : ScalarOutput} {sourceArguments : List Dynamic.Value}
    (meaning : ScalarMeaning issued before row stages call scalar sourceArguments)
    (ready : session.ExportsReady) :
    RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe scalar
      call.toStartedCall meaning.after.heap :=
  issued.forward_scalar before scalar call.toStartedCall meaning.request meaning.inputs
    meaning.rawType meaning.nativeType ready meaning.trace

end Tests.SourceCoreMethodOriginEvidence.Certified
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceCertifiedCalls
/-! Actual public start receipts choose each complete cached row. Reflection
and sufficient-fuel preservation use the single automatic catalog throughout. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.Certified
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicPhysicalSessionState (SourceCall)
open CertifiedPublicSession (Issued Initial)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

theorem first_meaning
    (admission : ObservedProgramCertificate fixture observed)
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ issued : Issued fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨issued, initial, namedEq⟩ := CertifiedPublicSession.from_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued admission.certificate fixture.source_wellFormed first.opened
    first.as_function_call.toCall.toStartedCall first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 102400 first.session from .single first.ready)
    (selected_row observed.wordRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.wordRow.toObservedRow issued.catalog.rows
    initial.start.selected.member namedEq
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      initial.header.types := by
    rw [← actualEq, actual.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  obtain ⟨entry, type, handle, after, trace⟩ := initial.reflect_function
    (call := first.as_function_call) (word_simple seed (Core.Word.ofNatModulo 33) true)
    inputTypes inputMeanings (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  refine ⟨issued, ⟨⟨initial, actual, actualEq.symm, entry, ?_, handle, after, trace⟩⟩⟩
  exact type.trans (by rw [← actualEq]; exact actual.word_result_type)

variable {issued : Issued fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

theorem word_meaning (before : issued.State anchor session entries)
    (value next : Core.Word) (flag : Bool)
    (call : ObservedFunctionCall session observed.wordRow.row.key [.word value, .word next, .bool flag])
    (stages : ObservedStages fixture observed.wordRow.toObservedRow) :
    Nonempty (FunctionMeaning issued before observed.wordRow.toObservedRow stages call .word [.word value, .word next, .bool flag]) := by
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before call.toCall.toStartedCall
    (selected_row observed.wordRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.wordRow.toObservedRow issued.catalog.rows
    request.selected.member namedEq
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
    rw [← actualEq, actual.word_input_types]
    exact word_inputs value next flag
  have raw : request.header.function.resultType = closureType .word := by
    rw [← actualEq]; exact actual.word_result_type
  obtain ⟨entry, type, handle, _handleType, after, trace⟩ := issued.reflect_function before call
    request inputs (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, entry, type.trans raw, handle, after, trace⟩⟩

theorem bool_meaning (before : issued.State anchor session entries)
    (value next : Bool) (flag : Bool)
    (call : ObservedFunctionCall session observed.boolRow.row.key [.bool value, .bool next, .bool flag])
    (stages : ObservedStages fixture observed.boolRow.toObservedRow) :
    Nonempty (FunctionMeaning issued before observed.boolRow.toObservedRow stages call .bool [.bool value, .bool next, .bool flag]) := by
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before call.toCall.toStartedCall
    (selected_row observed.boolRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.boolRow.toObservedRow issued.catalog.rows
    request.selected.member namedEq
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
    rw [← actualEq, actual.bool_input_types]
    exact bool_inputs value next flag
  have raw : request.header.function.resultType = closureType .bool := by
    rw [← actualEq]; exact actual.bool_result_type
  obtain ⟨entry, type, handle, _handleType, after, trace⟩ := issued.reflect_function before call
    request inputs (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, entry, type.trans raw, handle, after, trace⟩⟩

theorem useWord_meaning (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useWordRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useWordRow.toObservedRow) :
    Nonempty (ScalarMeaning issued before observed.useWordRow.toObservedRow stages call (.word value) [entry.source]) := by
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before call.toStartedCall
    (selected_row observed.useWordRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.useWordRow.toObservedRow issued.catalog.rows
    request.selected.member namedEq
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [← actualEq, actual.useWord_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [← actualEq, actual.useWord_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [← actualEq, actual.useWord_output]; rfl
  obtain ⟨after, trace⟩ := issued.reflect_scalar before (.word value) call returned
    request inputs raw native (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, native, after, trace⟩⟩

theorem useBool_meaning (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .bool)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Bool) (call : ObservedCall session observed.useBoolRow.row.key [.function handle])
    (returned : call.completion.value = .bool value)
    (stages : ObservedStages fixture observed.useBoolRow.toObservedRow) :
    Nonempty (ScalarMeaning issued before observed.useBoolRow.toObservedRow stages call (.bool value) [entry.source]) := by
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before call.toStartedCall
    (selected_row observed.useBoolRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.useBoolRow.toObservedRow issued.catalog.rows
    request.selected.member namedEq
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [← actualEq, actual.useBool_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.bool value : ScalarOutput).sourceType := by
    rw [← actualEq, actual.useBool_result_type]; rfl
  have native : request.header.output = (.bool value : ScalarOutput).nativeType := by
    rw [← actualEq, actual.useBool_output]; rfl
  obtain ⟨after, trace⟩ := issued.reflect_scalar before (.bool value) call returned
    request inputs raw native (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, native, after, trace⟩⟩

end Tests.SourceCoreMethodOriginEvidence.Certified
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceCertifiedSequence
/-! The unchanged seven public calls share one automatic catalog and retain
all three closures through subsequent calls and sufficient-fuel resumptions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.Certified
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CertifiedPublicSession (Issued)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure SequenceMeaning (issued : Issued fixture.recipe)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) where
  first : FirstMeaning issued wordStages sequence.first
  second : FunctionMeaning issued first.after observed.boolRow.toObservedRow boolStages sequence.second .bool
    [.bool false, .bool true, .bool true]
  firstRead : ScalarMeaning issued second.after observed.useWordRow.toObservedRow useWordStages sequence.firstRead
    (.word (Core.Word.ofNatModulo 33)) [first.entry.source]
  third : FunctionMeaning issued firstRead.after observed.wordRow.toObservedRow wordStages sequence.third .word
    [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
  secondRead : ScalarMeaning issued third.after observed.useBoolRow.toObservedRow useBoolStages sequence.secondRead
    (.bool true) [second.entry.source]
  repeatedRead : ScalarMeaning issued secondRead.after observed.useWordRow.toObservedRow useWordStages sequence.repeatedRead
    (.word (Core.Word.ofNatModulo 33)) [first.entry.source]
  thirdRead : ScalarMeaning issued repeatedRead.after observed.useWordRow.toObservedRow useWordStages sequence.thirdRead
    (.word (Core.Word.ofNatModulo 55)) [third.entry.source]

variable {issued : Issued fixture.recipe}
  {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
  {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
  {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
  {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
  {sequence : ObservedSequence fixture observed}

theorem SequenceMeaning.handles_distinct
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) :
    meaning.first.entry.handle ≠ meaning.second.entry.handle ∧
      meaning.first.entry.handle ≠ meaning.third.entry.handle ∧
      meaning.second.entry.handle ≠ meaning.third.entry.handle := by
  rw [meaning.first.handleEq, meaning.second.handleEq, meaning.third.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) :
    ∃ issued : Issued fixture.recipe,
      Nonempty (SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning admission wordStages sequence.first
  obtain ⟨second⟩ := bool_meaning first.after false true true sequence.second boolStages
  obtain ⟨firstRead⟩ := useWord_meaning second.after first.entry
    (by simp) first.entryType first.handleEq (Core.Word.ofNatModulo 33)
    sequence.firstRead sequence.firstValue useWordStages
  obtain ⟨third⟩ := word_meaning firstRead.after (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false
    sequence.third wordStages
  obtain ⟨secondRead⟩ := useBool_meaning third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
  obtain ⟨repeatedRead⟩ := useWord_meaning secondRead.after first.entry
    (by simp) first.entryType first.handleEq (Core.Word.ofNatModulo 33)
    sequence.repeatedRead sequence.repeatedValue useWordStages
  obtain ⟨thirdRead⟩ := useWord_meaning repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55)
    sequence.thirdRead sequence.thirdValue useWordStages
  exact ⟨issued, ⟨⟨first, second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩⟩

structure ForwardMeaning
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) : Prop where
  first : RecursiveNamedPublicPhysicalSessionInitialForward.ForwardAt issued.catalog.rows meaning.first.initial.header
    meaning.first.initial.header issued.support sequence.first.as_function_call.toCall.toStartedCall
    meaning.first.entry.source meaning.first.after.heap
  second : RecursiveNamedPublicPhysicalSessionFunctionForward.FunctionForwardAt (entries := [meaning.first.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.second.toCall.toStartedCall .unit .bool meaning.second.entry.source meaning.second.after.heap
  firstRead : RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt (entries := [meaning.first.entry] ++ [meaning.second.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (.word (Core.Word.ofNatModulo 33)) sequence.firstRead.toStartedCall meaning.firstRead.after.heap
  third : RecursiveNamedPublicPhysicalSessionFunctionForward.FunctionForwardAt (entries := [meaning.first.entry] ++ [meaning.second.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.third.toCall.toStartedCall .unit .word meaning.third.entry.source meaning.third.after.heap
  secondRead : RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt
    (entries := ([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.third.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (.bool true) sequence.secondRead.toStartedCall meaning.secondRead.after.heap
  repeatedRead : RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt
    (entries := ([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.third.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead.toStartedCall meaning.repeatedRead.after.heap
  thirdRead : RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt
    (entries := ([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.third.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead.toStartedCall meaning.thirdRead.after.heap

theorem SequenceMeaning.forward
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) :
    ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨meaning.first.forward, meaning.second.forward firstReady, meaning.firstRead.forward secondReady,
    meaning.third.forward firstReadReady, meaning.secondRead.forward thirdReady,
    meaning.repeatedRead.forward secondReadReady, meaning.thirdRead.forward repeatedReady⟩

theorem closed_sequence_forward_meaning
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe)
      (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence),
      ForwardMeaning meaning := by
  obtain ⟨issued, ⟨meaning⟩⟩ := sequence_meaning wordStages boolStages useWordStages useBoolStages admission sequence
  exact ⟨issued, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let admission ← observeProgramCertificate fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _certified := closed_sequence_forward_meaning wordStages boolStages useWordStages useBoolStages admission sequence
  have _original := Tests.SourceCoreMethodOriginEvidence.closed_sequence_forward_meaning fixture observed
    wordStages boolStages useWordStages useBoolStages admission sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,40,67,149,176,258,340,403] do
    throw (IO.userError s!"certified catalog stores changed: {reprStr stores}")
  IO.println "CERTIFIED_CATALOG_FORWARD_PASS: original seven Source calls and sufficient public fuel bounds; one automatic catalog; three distinct retained closures; scalar33/true/33/55; related Source heaps and original public stores"

end Tests.SourceCoreMethodOriginEvidence.Certified
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceFuelForward
/-! The original checker receipt at its actual budget constructs the static
support consumed by all seven Source traces and public forward conclusions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

/-- Every support family is issued from the supplied original checker success. -/
theorem static_supports_at_checkfuel (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program) :
    Nonempty (StaticSupportPackage fixture observed receiver.completion) := by
  obtain ⟨given⟩ := ordinary_inventory fixture observed
  obtain ⟨program⟩ := admission.certificate.issue_for_checked fixture.source_wellFormed
    fixture.recipePrepared receiver.issued receiver.registry observed.wordRow.entryMember
    given.rows (admission.aligned given) (by rw [fixture.sameProgram]; exact checked)
  exact ⟨{
    toOrdinaryInventory := given
    distinct := given.distinct
    program := program }⟩

/-- Automatic catalog construction consumes the same actual checker receipt. -/
theorem ObservedProgramCertificate.automatic_catalog_at_checkfuel
    {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program) :
    ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
      Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
        (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        receiver.completion) := by
  exact admission.certificate.issue fixture.source_wellFormed fixture.recipePrepared receiver.issued
    receiver.registry observed.wordRow.entryMember (by rw [fixture.sameProgram]; exact checked)

theorem sequence_meaning_at_checkfuel {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports_at_checkfuel fixture observed admission receiver checked
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    support.program wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_factory_meaning support initial false true true sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.useWord_meaning support second.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.firstRead sequence.firstValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_factory_meaning support firstRead.after
    (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.useBool_meaning support third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.useWord_meaning support secondRead.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.repeatedRead sequence.repeatedValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.useWord_meaning support repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55) sequence.thirdRead sequence.thirdValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩


/-- The seven-call witness and all seven forward bounds use the supplied budget. -/
theorem closed_sequence_forward_meaning_at_checkfuel
    (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver),
      ForwardMeaning meaning := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨meaning⟩ := sequence_meaning_at_checkfuel wordStages boolStages useWordStages useBoolStages
    admission checked sequence receiver
  exact ⟨receiver, meaning, meaning.forward⟩

/-- The concrete companion retains its method and all seven original conclusions. -/
theorem closed_sequence_forward_meaning_at1000
    (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (original : OriginalCheckAt1000 fixture)
    (sequence : ObservedSequence fixture observed) :
    fixture.program.methods.length = 1 ∧
      ∃ (receiver : ObservedReceiver fixture observed)
        (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver),
        ForwardMeaning meaning :=
  ⟨original.nonemptyMethods,
    closed_sequence_forward_meaning_at_checkfuel fixture observed wordStages boolStages useWordStages
      useBoolStages admission original.accepted sequence⟩

def runForwardAt1000 : IO Unit := do
  let fixture ← compiledFixture
  let ⟨original⟩ ← observeOriginalCheckAt1000 fixture
  let observed ← observeProgram fixture
  let admission ← observeProgramCertificate fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _automatic : ∃ receiver : ObservedReceiver fixture observed,
      ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
        Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
          (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
          receiver.completion) := by
    obtain ⟨receiver⟩ := initial_receiver fixture observed
    exact ⟨receiver, admission.automatic_catalog_at_checkfuel receiver original.accepted⟩
  have _meaning := closed_sequence_forward_meaning_at1000 fixture observed wordStages boolStages
    useWordStages useBoolStages admission original sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,40,67,149,176,258,340,403] do
    throw (IO.userError s!"method scoped stores changed: {reprStr stores}")
  IO.println "METHOD_ORIGIN_EVIDENCE_FUEL_1000_PASS: original checker1000; selected method checker1024; one original method; seven Source calls and all seven public forward bounds; scalar33/true/33/55"

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceSelectedCertifiedMeaning
/-! The original public calls retain Source heaps and handles in the catalog
issued from their program certificate. Each call keeps its actual selected Header. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.SelectedCertified
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreMethodOriginEvidence.Certified (selected_row header_of_member)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicPhysicalSessionState (SourceCall)
open SelectedCompilationCertifiedPublicSession (Issued Initial)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure FirstMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) where
  initial : Initial issued first.as_function_call.toCall.toStartedCall
  actual : ActualHeader fixture observed.wordRow.row
  headerEq : initial.header = actual.header
  entry : Entry
  entryType : entry.sourceType = closureType .word
  handleEq : entry.handle = first.handle
  after : issued.State initial.header first.completion.session [entry]
  trace : RecursiveNamedPublicPhysicalSessionState.SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value entry.source) after.heap

structure FunctionMeaning
    (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    (stages : ObservedStages fixture row)
    {arguments : List SourceCorePublicValues.Value} (call : ObservedFunctionCall session row.row.key arguments)
    (resultType : TypeSystem.Ty) (sourceArguments : List Dynamic.Value) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session row.row.key arguments runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture row.row
  headerEq : request.header = actual.header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) arguments sourceArguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : issued.State anchor call.completion.session (entries ++ [entry])
  trace : RecursiveNamedPublicPhysicalSessionState.SourceCall anchor request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
    before.heap sourceArguments (.value entry.source) after.heap

structure ScalarMeaning
    (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    (stages : ObservedStages fixture row)
    {arguments : List SourceCorePublicValues.Value} (call : ObservedCall session row.row.key arguments)
    (scalar : ScalarOutput) (sourceArguments : List Dynamic.Value) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session row.row.key arguments runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture row.row
  headerEq : request.header = actual.header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) arguments sourceArguments
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : issued.State anchor call.completion.session entries
  trace : RecursiveNamedPublicPhysicalSessionState.SourceCall anchor request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
    before.heap sourceArguments (.value scalar.source) after.heap

theorem FirstMeaning.forward {issued : Issued fixture.recipe}
    {stages : ObservedStages fixture observed.wordRow.toObservedRow}
    {first : ObservedPublicRun fixture observed.wordRow.toObservedRow}
    (meaning : FirstMeaning issued stages first) :
    SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows meaning.initial.header
      meaning.initial.header issued.support first.as_function_call.toCall.toStartedCall meaning.entry.source meaning.after.heap := by
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      meaning.initial.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      meaning.initial.header.types := by
    rw [meaning.headerEq, meaning.actual.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have functionResult : SourceCoreRawMetadata.runtimeType meaning.initial.header.function.resultType =
      .function .unit .word := by
    rw [meaning.headerEq, meaning.actual.word_result_type]
    rfl
  exact meaning.initial.forward_function (word_simple seed (Core.Word.ofNatModulo 33) true)
    inputTypes inputMeanings functionResult meaning.trace

theorem FunctionMeaning.forward {issued : Issued fixture.recipe}
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} {before : issued.State anchor session entries}
    {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature}
    {stages : ObservedStages fixture row}
    {arguments : List SourceCorePublicValues.Value} {call : ObservedFunctionCall session row.row.key arguments}
    {resultType : TypeSystem.Ty} {sourceArguments : List Dynamic.Value}
    (meaning : FunctionMeaning issued before row stages call resultType sourceArguments)
    (ready : session.ExportsReady) :
    SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe
      call.toCall.toStartedCall .unit resultType meaning.entry.source meaning.after.heap :=
  issued.forward_function before call.toCall.toStartedCall meaning.request meaning.inputs meaning.rawType ready meaning.trace

theorem ScalarMeaning.forward {issued : Issued fixture.recipe}
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} {before : issued.State anchor session entries}
    {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature}
    {stages : ObservedStages fixture row}
    {arguments : List SourceCorePublicValues.Value} {call : ObservedCall session row.row.key arguments}
    {scalar : ScalarOutput} {sourceArguments : List Dynamic.Value}
    (meaning : ScalarMeaning issued before row stages call scalar sourceArguments)
    (ready : session.ExportsReady) :
    SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe scalar
      call.toStartedCall meaning.after.heap :=
  issued.forward_scalar before scalar call.toStartedCall meaning.request meaning.inputs
    meaning.rawType meaning.nativeType ready meaning.trace

end Tests.SourceCoreMethodOriginEvidence.SelectedCertified
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceSelectedCertifiedCalls
/-! Actual public start receipts choose each complete cached row. Reflection
and sufficient-fuel preservation use the single automatic catalog throughout. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.SelectedCertified
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreMethodOriginEvidence.Certified (selected_row header_of_member)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicPhysicalSessionState (SourceCall)
open SelectedCompilationCertifiedPublicSession (Issued Initial)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

theorem first_meaning
    (admission : ObservedProgramCertificate fixture observed)
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ issued : Issued fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued admission.certificate.to_prepared (SelectedCompilationBodyTyping.Bodies.of_program fixture.source_wellFormed) first.opened
    first.as_function_call.toCall.toStartedCall first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 102400 first.session from .single first.ready)
    (selected_row observed.wordRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.wordRow.toObservedRow issued.catalog.rows
    initial.start.selected.member namedEq
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      initial.header.types := by
    rw [← actualEq, actual.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  obtain ⟨entry, type, handle, after, trace⟩ := initial.reflect_function
    (call := first.as_function_call) (word_simple seed (Core.Word.ofNatModulo 33) true)
    inputTypes inputMeanings (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  refine ⟨issued, ⟨⟨initial, actual, actualEq.symm, entry, ?_, handle, after, trace⟩⟩⟩
  exact type.trans (by rw [← actualEq]; exact actual.word_result_type)

variable {issued : Issued fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

theorem word_meaning (before : issued.State anchor session entries)
    (value next : Core.Word) (flag : Bool)
    (call : ObservedFunctionCall session observed.wordRow.row.key [.word value, .word next, .bool flag])
    (stages : ObservedStages fixture observed.wordRow.toObservedRow) :
    Nonempty (FunctionMeaning issued before observed.wordRow.toObservedRow stages call .word [.word value, .word next, .bool flag]) := by
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before call.toCall.toStartedCall
    (selected_row observed.wordRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.wordRow.toObservedRow issued.catalog.rows
    request.selected.member namedEq
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
    rw [← actualEq, actual.word_input_types]
    exact word_inputs value next flag
  have raw : request.header.function.resultType = closureType .word := by
    rw [← actualEq]; exact actual.word_result_type
  obtain ⟨entry, type, handle, _handleType, after, trace⟩ := issued.reflect_function before call
    request inputs (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, entry, type.trans raw, handle, after, trace⟩⟩

theorem bool_meaning (before : issued.State anchor session entries)
    (value next : Bool) (flag : Bool)
    (call : ObservedFunctionCall session observed.boolRow.row.key [.bool value, .bool next, .bool flag])
    (stages : ObservedStages fixture observed.boolRow.toObservedRow) :
    Nonempty (FunctionMeaning issued before observed.boolRow.toObservedRow stages call .bool [.bool value, .bool next, .bool flag]) := by
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before call.toCall.toStartedCall
    (selected_row observed.boolRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.boolRow.toObservedRow issued.catalog.rows
    request.selected.member namedEq
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
    rw [← actualEq, actual.bool_input_types]
    exact bool_inputs value next flag
  have raw : request.header.function.resultType = closureType .bool := by
    rw [← actualEq]; exact actual.bool_result_type
  obtain ⟨entry, type, handle, _handleType, after, trace⟩ := issued.reflect_function before call
    request inputs (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, entry, type.trans raw, handle, after, trace⟩⟩

theorem useWord_meaning (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useWordRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useWordRow.toObservedRow) :
    Nonempty (ScalarMeaning issued before observed.useWordRow.toObservedRow stages call (.word value) [entry.source]) := by
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before call.toStartedCall
    (selected_row observed.useWordRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.useWordRow.toObservedRow issued.catalog.rows
    request.selected.member namedEq
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [← actualEq, actual.useWord_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [← actualEq, actual.useWord_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [← actualEq, actual.useWord_output]; rfl
  obtain ⟨after, trace⟩ := issued.reflect_scalar before (.word value) call returned
    request inputs raw native (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, native, after, trace⟩⟩

theorem useBool_meaning (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .bool)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Bool) (call : ObservedCall session observed.useBoolRow.row.key [.function handle])
    (returned : call.completion.value = .bool value)
    (stages : ObservedStages fixture observed.useBoolRow.toObservedRow) :
    Nonempty (ScalarMeaning issued before observed.useBoolRow.toObservedRow stages call (.bool value) [entry.source]) := by
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before call.toStartedCall
    (selected_row observed.useBoolRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.useBoolRow.toObservedRow issued.catalog.rows
    request.selected.member namedEq
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [← actualEq, actual.useBool_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.bool value : ScalarOutput).sourceType := by
    rw [← actualEq, actual.useBool_result_type]; rfl
  have native : request.header.output = (.bool value : ScalarOutput).nativeType := by
    rw [← actualEq, actual.useBool_output]; rfl
  obtain ⟨after, trace⟩ := issued.reflect_scalar before (.bool value) call returned
    request inputs raw native (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, native, after, trace⟩⟩

end Tests.SourceCoreMethodOriginEvidence.SelectedCertified
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceSelectedCertifiedSequence
/-! The unchanged seven public calls share one automatic catalog and retain
all three closures through subsequent calls and sufficient-fuel resumptions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.SelectedCertified
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreMethodOriginEvidence.Certified (selected_row header_of_member)
open SelectedCompilationCertifiedPublicSession (Issued)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure SequenceMeaning (issued : Issued fixture.recipe)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) where
  first : FirstMeaning issued wordStages sequence.first
  second : FunctionMeaning issued first.after observed.boolRow.toObservedRow boolStages sequence.second .bool
    [.bool false, .bool true, .bool true]
  firstRead : ScalarMeaning issued second.after observed.useWordRow.toObservedRow useWordStages sequence.firstRead
    (.word (Core.Word.ofNatModulo 33)) [first.entry.source]
  third : FunctionMeaning issued firstRead.after observed.wordRow.toObservedRow wordStages sequence.third .word
    [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
  secondRead : ScalarMeaning issued third.after observed.useBoolRow.toObservedRow useBoolStages sequence.secondRead
    (.bool true) [second.entry.source]
  repeatedRead : ScalarMeaning issued secondRead.after observed.useWordRow.toObservedRow useWordStages sequence.repeatedRead
    (.word (Core.Word.ofNatModulo 33)) [first.entry.source]
  thirdRead : ScalarMeaning issued repeatedRead.after observed.useWordRow.toObservedRow useWordStages sequence.thirdRead
    (.word (Core.Word.ofNatModulo 55)) [third.entry.source]

variable {issued : Issued fixture.recipe}
  {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
  {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
  {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
  {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
  {sequence : ObservedSequence fixture observed}

theorem SequenceMeaning.handles_distinct
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) :
    meaning.first.entry.handle ≠ meaning.second.entry.handle ∧
      meaning.first.entry.handle ≠ meaning.third.entry.handle ∧
      meaning.second.entry.handle ≠ meaning.third.entry.handle := by
  rw [meaning.first.handleEq, meaning.second.handleEq, meaning.third.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) :
    ∃ issued : Issued fixture.recipe,
      Nonempty (SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning admission wordStages sequence.first
  obtain ⟨second⟩ := bool_meaning first.after false true true sequence.second boolStages
  obtain ⟨firstRead⟩ := useWord_meaning second.after first.entry
    (by simp) first.entryType first.handleEq (Core.Word.ofNatModulo 33)
    sequence.firstRead sequence.firstValue useWordStages
  obtain ⟨third⟩ := word_meaning firstRead.after (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false
    sequence.third wordStages
  obtain ⟨secondRead⟩ := useBool_meaning third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
  obtain ⟨repeatedRead⟩ := useWord_meaning secondRead.after first.entry
    (by simp) first.entryType first.handleEq (Core.Word.ofNatModulo 33)
    sequence.repeatedRead sequence.repeatedValue useWordStages
  obtain ⟨thirdRead⟩ := useWord_meaning repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55)
    sequence.thirdRead sequence.thirdValue useWordStages
  exact ⟨issued, ⟨⟨first, second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩⟩

structure ForwardMeaning
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) : Prop where
  first : SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows meaning.first.initial.header
    meaning.first.initial.header issued.support sequence.first.as_function_call.toCall.toStartedCall
    meaning.first.entry.source meaning.first.after.heap
  second : SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := [meaning.first.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.second.toCall.toStartedCall .unit .bool meaning.second.entry.source meaning.second.after.heap
  firstRead : SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := [meaning.first.entry] ++ [meaning.second.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (.word (Core.Word.ofNatModulo 33)) sequence.firstRead.toStartedCall meaning.firstRead.after.heap
  third : SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := [meaning.first.entry] ++ [meaning.second.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.third.toCall.toStartedCall .unit .word meaning.third.entry.source meaning.third.after.heap
  secondRead : SelectedCompilationPublicSessionScalarForward.ForwardAt
    (entries := ([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.third.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (.bool true) sequence.secondRead.toStartedCall meaning.secondRead.after.heap
  repeatedRead : SelectedCompilationPublicSessionScalarForward.ForwardAt
    (entries := ([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.third.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead.toStartedCall meaning.repeatedRead.after.heap
  thirdRead : SelectedCompilationPublicSessionScalarForward.ForwardAt
    (entries := ([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.third.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead.toStartedCall meaning.thirdRead.after.heap

theorem SequenceMeaning.forward
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) :
    ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨meaning.first.forward, meaning.second.forward firstReady, meaning.firstRead.forward secondReady,
    meaning.third.forward firstReadReady, meaning.secondRead.forward thirdReady,
    meaning.repeatedRead.forward secondReadReady, meaning.thirdRead.forward repeatedReady⟩

theorem closed_sequence_forward_meaning
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe)
      (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence),
      ForwardMeaning meaning := by
  obtain ⟨issued, ⟨meaning⟩⟩ := sequence_meaning wordStages boolStages useWordStages useBoolStages admission sequence
  exact ⟨issued, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let admission ← observeProgramCertificate fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _certified := closed_sequence_forward_meaning wordStages boolStages useWordStages useBoolStages admission sequence
  have _original := Tests.SourceCoreMethodOriginEvidence.closed_sequence_forward_meaning fixture observed
    wordStages boolStages useWordStages useBoolStages admission sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,40,67,149,176,258,340,403] do
    throw (IO.userError s!"certified catalog stores changed: {reprStr stores}")
  IO.println "CERTIFIED_CATALOG_FORWARD_PASS: original seven Source calls and sufficient public fuel bounds; one automatic catalog; three distinct retained closures; scalar33/true/33/55; related Source heaps and original public stores"

end Tests.SourceCoreMethodOriginEvidence.SelectedCertified
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceCompilerProfile
/-! One executable profile of the original complete cache supplies the automatic
public catalog. All seven Source calls use the same physical session, including
retained closures and both genuine original checker budgets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open SelectedCertified
open Tests.SourceCoreMethodOriginEvidence.Certified (selected_row header_of_member)
open SelectedCompilationCertifiedPublicSession (Issued)

structure Observed (fixture : CompiledFixture) where
  value : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled
  accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled
    fixture.source_wellFormed = some value

def observe (fixture : CompiledFixture) : IO (Observed fixture) := do
  match accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled fixture.source_wellFormed with
  | none => throw (IO.userError "original complete compiler profile rejected")
  | some profile => pure ⟨profile, accepted⟩

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

theorem first_meaning
    (profile : Observed fixture)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ issued : Issued fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨profiled, initial, namedEq⟩ := CertifiedPublicSession.from_profile_initial_row
    (by rw [fixture.sameProgram]; exact checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile.value fixture.source_wellFormed first.opened
    first.as_function_call.toCall.toStartedCall first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 102400 first.session from .single first.ready)
    (selected_row observed.wordRow.toObservedRow)
  let issued := profiled.toIssued
  obtain ⟨actual, actualEq⟩ := header_of_member observed.wordRow.toObservedRow issued.catalog.rows
    initial.start.selected.member namedEq
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      initial.header.types := by
    rw [← actualEq, actual.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  obtain ⟨entry, type, handle, after, trace⟩ := initial.reflect_function
    (call := first.as_function_call) (word_simple seed (Core.Word.ofNatModulo 33) true)
    inputTypes inputMeanings (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  refine ⟨issued, ⟨⟨initial, actual, actualEq.symm, entry, ?_, handle, after, trace⟩⟩⟩
  exact type.trans (by rw [← actualEq]; exact actual.word_result_type)

theorem sequence_meaning
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (profile : Observed fixture)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) :
    ∃ issued : Issued fixture.recipe,
      Nonempty (SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning profile checked wordStages sequence.first
  obtain ⟨second⟩ := bool_meaning first.after false true true sequence.second boolStages
  obtain ⟨firstRead⟩ := useWord_meaning second.after first.entry
    (by simp) first.entryType first.handleEq (Core.Word.ofNatModulo 33)
    sequence.firstRead sequence.firstValue useWordStages
  obtain ⟨third⟩ := word_meaning firstRead.after (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false
    sequence.third wordStages
  obtain ⟨secondRead⟩ := useBool_meaning third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
  obtain ⟨repeatedRead⟩ := useWord_meaning secondRead.after first.entry
    (by simp) first.entryType first.handleEq (Core.Word.ofNatModulo 33)
    sequence.repeatedRead sequence.repeatedValue useWordStages
  obtain ⟨thirdRead⟩ := useWord_meaning repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55)
    sequence.thirdRead sequence.thirdValue useWordStages
  exact ⟨issued, ⟨⟨first, second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩⟩

theorem closed_sequence_forward_meaning
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (profile : Observed fixture)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe)
      (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence),
      SelectedCertified.ForwardMeaning meaning := by
  obtain ⟨issued, ⟨meaning⟩⟩ := sequence_meaning wordStages boolStages useWordStages useBoolStages profile checked sequence
  exact ⟨issued, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← observe fixture
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _original := closed_sequence_forward_meaning wordStages boolStages useWordStages useBoolStages
    profile fixture.checked sequence
  let ⟨checked1000⟩ ← observeOriginalCheckAt1000 fixture
  have _companion := closed_sequence_forward_meaning wordStages boolStages useWordStages useBoolStages
    profile checked1000.accepted sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 12 && profile.value.table.rows.length == 10 do
    throw (IO.userError "compiler profile changed original cache12/table10")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,40,67,149,176,258,340,403] do
    throw (IO.userError s!"compiler profile stores changed: {reprStr stores}")
  IO.println "COMPILER_PROFILE_FORWARD_PASS: one actual complete profile; original X7 at checker1024 and1000; all seven Source traces and sufficient public fuel bounds; one automatic catalog; retained closures; scalar33/true/33/55; original stores"

end Tests.SourceCoreMethodOriginEvidence.CompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceSelectedCompilerProfile
/-! One executable profile of the original complete cache supplies the automatic
public catalog. All seven Source calls use the same physical session, including
retained closures and both genuine original checker budgets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.SelectedCompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreMethodOriginEvidence.Certified (selected_row header_of_member)
open SelectedCertified
open SelectedCompilationCertifiedPublicSession (Issued)

structure Observed (fixture : CompiledFixture) where
  value : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled
  accepted : SelectedCompilationCompilerStaticProfile.validateCheckedProfile fixture.recipe.compiled
    (by rw [fixture.sameProgram]; exact fixture.checked) = some value

def observe (fixture : CompiledFixture) : IO (Observed fixture) := do
  match accepted : SelectedCompilationCompilerStaticProfile.validateCheckedProfile fixture.recipe.compiled
      (by rw [fixture.sameProgram]; exact fixture.checked) with
  | none => throw (IO.userError "original complete compiler profile rejected")
  | some profile => pure ⟨profile, accepted⟩

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

theorem first_meaning
    (profile : Observed fixture)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ issued : Issued fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profile_initial_row
    (by rw [fixture.sameProgram]; exact checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile.value first.opened
    first.as_function_call.toCall.toStartedCall first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 102400 first.session from .single first.ready)
    (selected_row observed.wordRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.wordRow.toObservedRow issued.catalog.rows
    initial.start.selected.member namedEq
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      initial.header.types := by
    rw [← actualEq, actual.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  obtain ⟨entry, type, handle, after, trace⟩ := initial.reflect_function
    (call := first.as_function_call) (word_simple seed (Core.Word.ofNatModulo 33) true)
    inputTypes inputMeanings (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  refine ⟨issued, ⟨⟨initial, actual, actualEq.symm, entry, ?_, handle, after, trace⟩⟩⟩
  exact type.trans (by rw [← actualEq]; exact actual.word_result_type)

theorem sequence_meaning
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (profile : Observed fixture)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) :
    ∃ issued : Issued fixture.recipe,
      Nonempty (SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning profile checked wordStages sequence.first
  obtain ⟨second⟩ := bool_meaning first.after false true true sequence.second boolStages
  obtain ⟨firstRead⟩ := useWord_meaning second.after first.entry
    (by simp) first.entryType first.handleEq (Core.Word.ofNatModulo 33)
    sequence.firstRead sequence.firstValue useWordStages
  obtain ⟨third⟩ := word_meaning firstRead.after (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false
    sequence.third wordStages
  obtain ⟨secondRead⟩ := useBool_meaning third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
  obtain ⟨repeatedRead⟩ := useWord_meaning secondRead.after first.entry
    (by simp) first.entryType first.handleEq (Core.Word.ofNatModulo 33)
    sequence.repeatedRead sequence.repeatedValue useWordStages
  obtain ⟨thirdRead⟩ := useWord_meaning repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55)
    sequence.thirdRead sequence.thirdValue useWordStages
  exact ⟨issued, ⟨⟨first, second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩⟩

theorem closed_sequence_forward_meaning
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (profile : Observed fixture)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe)
      (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence),
      SelectedCertified.ForwardMeaning meaning := by
  obtain ⟨issued, ⟨meaning⟩⟩ := sequence_meaning wordStages boolStages useWordStages useBoolStages profile checked sequence
  exact ⟨issued, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← observe fixture
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _original := closed_sequence_forward_meaning wordStages boolStages useWordStages useBoolStages
    profile fixture.checked sequence
  let ⟨checked1000⟩ ← observeOriginalCheckAt1000 fixture
  have _companion := closed_sequence_forward_meaning wordStages boolStages useWordStages useBoolStages
    profile checked1000.accepted sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 12 && profile.value.table.rows.length == 10 do
    throw (IO.userError "compiler profile changed original cache12/table10")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,40,67,149,176,258,340,403] do
    throw (IO.userError s!"compiler profile stores changed: {reprStr stores}")
  IO.println "SELECTED_COMPILER_PROFILE_FORWARD_PASS: one actual complete profile; original X7 at checker1024 and1000; all seven Source traces and sufficient public fuel bounds; one automatic catalog; retained closures; scalar33/true/33/55; original stores"

end Tests.SourceCoreMethodOriginEvidence.SelectedCompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceSelectedSourceOutcomes
/-! The actual seven-call compiler-profile session has independent Dynamic
outcomes at the same retained functions, dictionaries and reached heaps.
Its original sufficient-fuel conclusions remain attached to the same sequence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.SelectedSourceOutcomes
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open SelectedCertified
open SelectedCompilationCertifiedPublicSession (Issued)
open RecursiveNamedPublicPhysicalSessionState (PlainValue)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Issued fixture.recipe}
  {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
  {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
  {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
  {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
  {sequence : ObservedSequence fixture observed}

structure DynamicMeaning
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) : Prop where
  first : PlainValue meaning.first.initial.header meaning.first.initial.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] meaning.first.initial.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] meaning.first.entry.source meaning.first.after.heap
  second : PlainValue meaning.first.initial.header meaning.second.request.header
    (RecursiveStageRegistry.scope boolStages.sidecar [] meaning.second.request.header.function)
    meaning.first.after.heap [.bool false, .bool true, .bool true] meaning.second.entry.source meaning.second.after.heap
  firstRead : PlainValue meaning.first.initial.header meaning.firstRead.request.header
    (RecursiveStageRegistry.scope useWordStages.sidecar [] meaning.firstRead.request.header.function)
    meaning.second.after.heap [meaning.first.entry.source] (.word (Core.Word.ofNatModulo 33)) meaning.firstRead.after.heap
  third : PlainValue meaning.first.initial.header meaning.third.request.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] meaning.third.request.header.function)
    meaning.firstRead.after.heap [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
    meaning.third.entry.source meaning.third.after.heap
  secondRead : PlainValue meaning.first.initial.header meaning.secondRead.request.header
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] meaning.secondRead.request.header.function)
    meaning.third.after.heap [meaning.second.entry.source] (.bool true) meaning.secondRead.after.heap
  repeatedRead : PlainValue meaning.first.initial.header meaning.repeatedRead.request.header
    (RecursiveStageRegistry.scope useWordStages.sidecar [] meaning.repeatedRead.request.header.function)
    meaning.secondRead.after.heap [meaning.first.entry.source] (.word (Core.Word.ofNatModulo 33)) meaning.repeatedRead.after.heap
  thirdRead : PlainValue meaning.first.initial.header meaning.thirdRead.request.header
    (RecursiveStageRegistry.scope useWordStages.sidecar [] meaning.thirdRead.request.header.function)
    meaning.repeatedRead.after.heap [meaning.third.entry.source] (.word (Core.Word.ofNatModulo 55)) meaning.thirdRead.after.heap

theorem dynamic_meaning
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) :
    DynamicMeaning meaning :=
  ⟨meaning.first.trace.value_plain, meaning.second.trace.value_plain, meaning.firstRead.trace.value_plain,
    meaning.third.trace.value_plain, meaning.secondRead.trace.value_plain,
    meaning.repeatedRead.trace.value_plain, meaning.thirdRead.trace.value_plain⟩

/-- Both original checker budgets feed the actual common compiler profile.
The independent applications and the forward bounds use the same session witness. -/
theorem closed_outcomes
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (profile : SelectedCompilerProfile.Observed fixture)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe)
      (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence),
      DynamicMeaning meaning ∧ SelectedCertified.ForwardMeaning meaning ∧
      meaning.first.entry.handle ≠ meaning.second.entry.handle ∧
      meaning.first.entry.handle ≠ meaning.third.entry.handle ∧
      meaning.second.entry.handle ≠ meaning.third.entry.handle := by
  obtain ⟨issued, meaning, forward⟩ := SelectedCompilerProfile.closed_sequence_forward_meaning
    wordStages boolStages useWordStages useBoolStages profile checked sequence
  exact ⟨issued, meaning, dynamic_meaning meaning, forward, meaning.handles_distinct⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← SelectedCompilerProfile.observe fixture
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _original := closed_outcomes wordStages boolStages useWordStages useBoolStages profile fixture.checked sequence
  let ⟨checked1000⟩ ← observeOriginalCheckAt1000 fixture
  have _companion := closed_outcomes wordStages boolStages useWordStages useBoolStages profile checked1000.accepted sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 12 && profile.value.table.rows.length == 10 do
    throw (IO.userError "ordinary source outcomes changed original cache12/table10")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,40,67,149,176,258,340,403] do
    throw (IO.userError s!"ordinary source outcomes changed original stores: {reprStr stores}")
  IO.println "SELECTED_METHOD_SOURCE_OUTCOMES_PASS: actual profile X7 at checker1024 and1000; seven independent Dynamic applications; exact named dictionaries, retained closures and Source heaps; scalar33/true/33/55; original stores and forward bounds"

end Tests.SourceCoreMethodOriginEvidence.SelectedSourceOutcomes
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceSourceOutcomes
/-! The actual seven-call compiler-profile session has independent Dynamic
outcomes at the same retained functions, dictionaries and reached heaps.
Its original sufficient-fuel conclusions remain attached to the same sequence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.SourceOutcomes
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open SelectedCertified
open SelectedCompilationCertifiedPublicSession (Issued)
open SelectedCompilationPublicSessionState (PlainValue)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Issued fixture.recipe}
  {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
  {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
  {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
  {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
  {sequence : ObservedSequence fixture observed}

structure DynamicMeaning
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) : Prop where
  first : PlainValue meaning.first.initial.header meaning.first.initial.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] meaning.first.initial.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] meaning.first.entry.source meaning.first.after.heap
  second : PlainValue meaning.first.initial.header meaning.second.request.header
    (RecursiveStageRegistry.scope boolStages.sidecar [] meaning.second.request.header.function)
    meaning.first.after.heap [.bool false, .bool true, .bool true] meaning.second.entry.source meaning.second.after.heap
  firstRead : PlainValue meaning.first.initial.header meaning.firstRead.request.header
    (RecursiveStageRegistry.scope useWordStages.sidecar [] meaning.firstRead.request.header.function)
    meaning.second.after.heap [meaning.first.entry.source] (.word (Core.Word.ofNatModulo 33)) meaning.firstRead.after.heap
  third : PlainValue meaning.first.initial.header meaning.third.request.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] meaning.third.request.header.function)
    meaning.firstRead.after.heap [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
    meaning.third.entry.source meaning.third.after.heap
  secondRead : PlainValue meaning.first.initial.header meaning.secondRead.request.header
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] meaning.secondRead.request.header.function)
    meaning.third.after.heap [meaning.second.entry.source] (.bool true) meaning.secondRead.after.heap
  repeatedRead : PlainValue meaning.first.initial.header meaning.repeatedRead.request.header
    (RecursiveStageRegistry.scope useWordStages.sidecar [] meaning.repeatedRead.request.header.function)
    meaning.secondRead.after.heap [meaning.first.entry.source] (.word (Core.Word.ofNatModulo 33)) meaning.repeatedRead.after.heap
  thirdRead : PlainValue meaning.first.initial.header meaning.thirdRead.request.header
    (RecursiveStageRegistry.scope useWordStages.sidecar [] meaning.thirdRead.request.header.function)
    meaning.repeatedRead.after.heap [meaning.third.entry.source] (.word (Core.Word.ofNatModulo 55)) meaning.thirdRead.after.heap

theorem dynamic_meaning
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) :
    DynamicMeaning meaning :=
  ⟨meaning.first.trace.value_plain, meaning.second.trace.value_plain, meaning.firstRead.trace.value_plain,
    meaning.third.trace.value_plain, meaning.secondRead.trace.value_plain,
    meaning.repeatedRead.trace.value_plain, meaning.thirdRead.trace.value_plain⟩

/-- Both original checker budgets feed the actual common compiler profile.
The independent applications and the forward bounds use the same session witness. -/
theorem closed_outcomes
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (profile : CompilerProfile.Observed fixture)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe)
      (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence),
      DynamicMeaning meaning ∧ SelectedCertified.ForwardMeaning meaning ∧
      meaning.first.entry.handle ≠ meaning.second.entry.handle ∧
      meaning.first.entry.handle ≠ meaning.third.entry.handle ∧
      meaning.second.entry.handle ≠ meaning.third.entry.handle := by
  obtain ⟨issued, meaning, forward⟩ := CompilerProfile.closed_sequence_forward_meaning
    wordStages boolStages useWordStages useBoolStages profile checked sequence
  exact ⟨issued, meaning, dynamic_meaning meaning, forward, meaning.handles_distinct⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← CompilerProfile.observe fixture
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _original := closed_outcomes wordStages boolStages useWordStages useBoolStages profile fixture.checked sequence
  let ⟨checked1000⟩ ← observeOriginalCheckAt1000 fixture
  have _companion := closed_outcomes wordStages boolStages useWordStages useBoolStages profile checked1000.accepted sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 12 && profile.value.table.rows.length == 10 do
    throw (IO.userError "ordinary source outcomes changed original cache12/table10")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,40,67,149,176,258,340,403] do
    throw (IO.userError s!"ordinary source outcomes changed original stores: {reprStr stores}")
  IO.println "METHOD_SOURCE_OUTCOMES_PASS: actual profile X7 at checker1024 and1000; seven independent Dynamic applications; exact named dictionaries, retained closures and Source heaps; scalar33/true/33/55; original stores and forward bounds"

end Tests.SourceCoreMethodOriginEvidence.SourceOutcomes
end
