import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport

/-! The real named compiler callback issues a canonical root at each actual
lexical context. Prepared sidecars, the full inventory and original diagnostics
supply finite authority; runtime global values are supplied only by entry. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalScopedRoots
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax GeneralPolicyFor)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (CanonicalRootAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (metadata : NativeMetadataFor compiled.indexed prepared.named header.function.source)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry actual
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include prepared aligned diagnostic receiver wellFormed metadata complete in
/-- Original Source typing and the actual accepted action determine this root.
All lexical context changes come from the compiler collector's binder fields. -/
theorem of_policy
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word}
    {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      prepared.named prepared.diagnostics prepared.code prepared.compilation rootFuel
      rootSource rootScope rootId rootReasonAt rootLowered)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      fuel (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      invocation.source scope id header.reasonAt = .ok lowered) :
    ∃ root : CanonicalRootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  have sameSource := (stages).source selected
  have unique : NodeOccurrencesUnique invocation.source := sameSource ▸ header.unique
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.recipe_policy_for_native
    root.compilerPolicy metadata scope header.reasonAt
  have childProfile : GeneralPolicyFor root.selected.policy (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) invocation.source scope header.reasonAt := by
    simpa only [sameSource] using profile
  have coercions : ∀ id actualNode, GeneralSyntax invocation.source id →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sameSource] using syntaxTree)
      actualNode (by simpa only [sameSource] using actualFound)
  have compiledChild := accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_general_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique declarations childProfile coercions tree found typed compiledChild
  obtain ⟨sidecar, issued⟩ := CallableIndexedActualNamedSourceReceipts.hook_sidecar compiled header.hook
  have sourceReceipt := (CallableIndexedActualNamedSourceReceipts.header_source compiled header).1
  have canonicalSource : header.function.source = sidecar.source := by
    simpa only [EmptySourceSubstitution.source] using sourceReceipt.source issued
  obtain ⟨request, signature, generic, signatureMember, _genericMember, _requested, specialized⟩ := prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities specialized
  have body := RecursiveNamedSpecializationBodyFacts.body specialized
  have sourceOwner : header.function.source.owner = signature.id := by
    rw [header.agreement.source, aligned.named, prepared.same]
    exact (congrArg TypedSource.owner body).trans (identities.2.1.trans identities.1.symm)
  have guardFrame := RecursiveNamedPreparedScopeCoherence.selected_frame actual
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed
    signatureMember sourceOwner issued sourceReceipt selected
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation) certificate := by
    intro callFuel callScope callId callee ids callMetadata code compiler path
    have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.calls_syntax path
    have callProfile := CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.recipe_policy_for_native
      root.compilerPolicy metadata callScope header.reasonAt
    have readPolicy := callProfile.read callId (by simpa only [sameSource] using syntaxTree)
    have childRead : root.selected.policy.readExpression invocation.source callId =
        SourceCoreCompatibleDataExpressions.readExpression
          (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked invocation.source callId := by
      simpa only [sameSource] using readPolicy
    have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent compiler childRead
    obtain ⟨callPrepared⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.prepared
      compiler childRead [] root.callables
    have parentTyped := CallableIndexedOwnedPreparedStagedRecursiveCallerRawTyping.parent_typed
      compiler unique typed path
    obtain ⟨parameter, result, types, calleeTyped, _⟩ :=
      CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
        compiler parent unique parentTyped
    obtain ⟨calleeNode, contains, _⟩ := calleeTyped.stored_type
    exact ⟨{
      prepared := callPrepared
      sidecar := sidecar
      caller := by rw [callPrepared.caller]; simpa only [aligned.named, CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext] using issued
      view := .inl (sameSource.trans canonicalSource)
      guardFrame := guardFrame
      originalUnique := canonicalSource ▸ header.unique
      sourceParent := parent
      calleeNode := calleeNode
      calleeFound := lookupExpression?_complete unique contains }⟩
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source := by
    rw [sameSource]
    obtain ⟨_, sourceTyped⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
        header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact sourceTyped.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact (original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)).transport fields
  let result := CanonicalRootAt.of_general_compiled
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique declarations childProfile coercions tree found typed compiledChild ready rfl
    (fields.solvedRequirements.trans (header.valid.ledger.trans aligned.solved))
    (fields.runtimeRequirementLedger (RecursiveNamedInitialContextValidity.runtime header.frame header.extended wellFormed))
    wellFormed runtime
    (by rw [(stages).evidence selected]; exact fields.covers (RecursiveNamedInitialContextValidity.covers header.frame header.extended))
    (by rw [root.callables]; rfl)
    (fun _ _ _ receipt location =>
      CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized prepared diagnostic aligned receiver
        (by simpa only [sameSource] using receipt) location)
    rows complete rfl rfl
    (CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.named_ready
      prepared diagnostic aligned sameSource certificate)
  exact ⟨result, rfl⟩


include prepared aligned diagnostic receiver wellFormed metadata complete in
/-- Original Source typing and the actual accepted action determine this root.
All lexical context changes come from the compiler collector's binder fields. -/
theorem of_accepted
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel invocation.source scope id header.reasonAt = .ok lowered) :
    ∃ root : CanonicalRootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  have sameSource := (stages).source selected
  obtain ⟨predecessor, ⟨root⟩⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.policy_receipt
    prepared aligned (by simpa only [sameSource] using accepted)
  exact of_policy prepared aligned diagnostic receiver wellFormed metadata rows complete actual selected
    fields declarations tree found typed root (by simpa only [sameSource] using root.selected.accepted)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalScopedRoots
