import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalCallsReady
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedScopeCoherence

/-! Static indirect-call authority at every genuine selected ordinary closure
scope. Direct and builtin ancestors retain their actual recursive argument
paths; original Source typing and the prepared guard frame determine each port. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryGeneralCallsReady
open Core Frontend SourceInference
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralPolicyFor GeneralSyntax Certificate)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function localScope administrative)
  {readFuel callFuel : Nat} {context : SourceSemantics.Context}
  {callScope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {lowered : SourceCoreBasic.LoweredExpr}
  (profile : GeneralPolicyFor code.policy code.compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    function.source callScope code.reasonAt)
  (syntaxTree : GeneralSyntax function.source id)
  (compiler : CallableIndirectCallCertificates.Receipt code.policy code.lowerBody callFuel
    code.compilation function.source callScope id callee ids metadata code.reasonAt lowered)
  (typed : ExpressionHasType function.source context id compiler.original.type)

include profile syntaxTree typed in
/-- Recover the actual full owner, original Source view and guard frame from
one Code's authentic stage producer. No invocation or sidecar is chosen by
an execution premise, and the emitted compiler receipt stays unchanged. -/
private theorem canonical_scope_port
    (source : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram
      compiled.indexed.base.plan code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
        code.compilation.owner = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar code.active function) ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
        (compiled := compiled)
        (invocation := RecursiveStageRegistry.scope sidecar code.active function) compiler) := by
  obtain ⟨sidecar, issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code source unique
  have readPolicy := profile.read id syntaxTree
  have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent
    compiler readPolicy
  obtain ⟨prepared⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.prepared
    compiler readPolicy code.active code.callables
  obtain ⟨parameter, result, types, calleeTyped, argumentsTyped, bundle, resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler parent unique typed
  obtain ⟨calleeNode, contains, stored⟩ := calleeTyped.stored_type
  have calleeFound := lookupExpression?_complete unique contains
  have sourceEq := source.source issued
  have originalUnique : NodeOccurrencesUnique sidecar.source := by
    have substituted : NodeOccurrencesUnique (sidecar.source.applySubstitution code.active) :=
      sourceEq ▸ unique
    change ((sidecar.source.applySubstitution code.active).nodes.map Node.occurrenceId).Nodup
      at substituted
    change (sidecar.source.nodes.map Node.occurrenceId).Nodup
    simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using substituted
  let port : CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
      (compiled := compiled)
      (invocation := RecursiveStageRegistry.scope sidecar code.active function) compiler := {
    prepared := prepared
    sidecar := sidecar
    caller := by rw [prepared.caller]; exact issued
    view := Or.inr ⟨code.active, sourceEq⟩
    guardFrame := rfl
    originalUnique := originalUnique
    sourceParent := parent
    calleeNode := calleeNode
    calleeFound := calleeFound }
  exact ⟨sidecar, issued, selected, ⟨port⟩⟩


variable (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

/-- The selected frame comes from the actual accepted preparation. The original
compiler certificate supplies the exact indirect-call path, even beneath a
direct declaration or builtin call. -/
theorem calls_ready {named : CallableIndexedNamedGeneration.Named}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {context : SourceSemantics.Context}
    (code : Code compiled.indexed function scope administrative)
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      compiled.indexed named function.source)
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source)
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {signature : ProgramFunctionSignature}
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (sourceOwner : function.source.owner = signature.id)
    {invocation : Staging.Recursive.Scope}
    (selected : ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).Closure function invocation)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr} {rootType : TypeSystem.Ty}
    (typed : ExpressionHasType invocation.source context rootId rootType)
    (root : Certificate code.policy code.lowerBody code.compilation compiled.indexed.fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context code.reasonAt rootScope rootId rootCode) :
    CallsReady (compiled := compiled) (invocation := invocation) root := by
  rcases invocation with ⟨origin, actualSource, owned, invocationContext, evidence, guards⟩
  have sameSource : actualSource = function.source := ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).source selected
  subst actualSource
  obtain ⟨canonical, issued, _canonicalSelected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code sourceReceipt unique
  have guardFrame := RecursiveNamedPreparedScopeCoherence.selected_frame stagePrepared accepted wellFormed signatureMember sourceOwner
    issued sourceReceipt selected
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.calls_syntax path
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.retained_policy_for_native
    retained metadata callScope code.reasonAt
  have parentTyped := CallableIndexedOwnedPreparedStagedRecursiveCallerRawTyping.parent_typed
    compiler unique typed path
  obtain ⟨actualSidecar, actualIssued, _actualSelected, ⟨port⟩⟩ :=
    canonical_scope_port code profile syntaxTree compiler parentTyped sourceReceipt unique
  have same : actualSidecar = canonical := Except.ok.inj (actualIssued.symm.trans issued)
  cases same

  exact ⟨{
    prepared := port.prepared
    sidecar := port.sidecar
    caller := port.caller
    view := port.view
    guardFrame := guardFrame.trans port.guardFrame
    originalUnique := port.originalUnique
    sourceParent := port.sourceParent
    calleeNode := port.calleeNode
    calleeFound := port.calleeFound }⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryGeneralCallsReady
