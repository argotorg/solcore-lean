import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots

/-! Original named compiler callbacks produce recursive operator roots when
an authentic finite Source table excludes indirect calls. Literal requirements
remain in their original ledger and are validated by the real leaf compiler.
The recursive certificate and semantic operator rules still support calls. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalOperatorRoots
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (NativeMetadataFor)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
/-- All dynamic-facing validity comes from the original Source Header and
actual lexical field transport. No heap, execution or value representation is
an input to this compiler-to-static-root producer. -/
theorem of_accepted
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (metadata : NativeMetadataFor compiled.indexed prepared.named header.function.source)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (sameSource : invocation.source = header.function.source)
    (sameEvidence : invocation.evidence = header.function.evidence)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    (noCalls : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee arguments resolution, node.form ≠ .call callee arguments (.indirect resolution))
    {id : ExpressionId} {node : ExpressionNode}
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel invocation.source scope id header.reasonAt = .ok lowered) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.RootAt compiled context invocation
      scope id lowered (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨predecessor, ⟨root⟩⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.policy_receipt prepared aligned (by simpa only [sameSource] using accepted)
  have unique : NodeOccurrencesUnique invocation.source := sameSource ▸ header.unique
  have profile := CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.recipe_policy_for_native
    root.compilerPolicy metadata scope header.reasonAt
  have childProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor
      root.selected.policy (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) invocation.source scope header.reasonAt := by
    simpa only [sameSource] using profile
  have coercions : ∀ id actualNode,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode tree selected
    exact metadata.coercions id (by simpa only [sameSource] using tree) actualNode
      (by simpa only [sameSource] using selected)
  have compiledChild : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (predecessor + 1) (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      invocation.source scope id header.reasonAt = .ok lowered := by
    simpa only [sameSource] using root.selected.accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
    unique declarations childProfile coercions syntaxTree found typed compiledChild
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation) certificate := by
    intro callFuel callScope callId callee ids callMetadata code compiler _path
    exact False.elim (noCalls callId compiler.original
      (by simpa only [sameSource] using compiler.found) callee ids callMetadata compiler.originalForm)
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source := by
    rw [sameSource]
    obtain ⟨_, sourceTyped⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
        header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact sourceTyped.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact (original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)).transport fields
  exact ⟨CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.RootAt.of_compiled
    unique declarations childProfile coercions syntaxTree found typed compiledChild ready rfl
    (fields.solvedRequirements.trans (header.valid.ledger.trans aligned.solved))
    (fields.runtimeRequirementLedger (RecursiveNamedInitialContextValidity.runtime header.frame header.extended wellFormed))
    wellFormed runtime
    (by rw [sameEvidence]; exact fields.covers (RecursiveNamedInitialContextValidity.covers header.frame header.extended))
    (by rw [root.callables]; rfl)
    (fun _ _ _ receipt location =>
      CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized prepared diagnostic aligned receiver
        (by simpa only [sameSource] using receipt) location)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalOperatorRoots
