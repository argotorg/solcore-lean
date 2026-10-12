import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport

/-! Genuine named expression callbacks produce local-read roots at the actual
lexical context and physical scope. Context fields are retained by binder
extension; diagnostics come from the original compiled issuer and receiver. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
/-- The actual statement callback retains its contextual root policy at any
lexical child, including children after an initialized declaration. -/
theorem policy_receipt {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered) :
    ∃ predecessor, Nonempty (RootPolicyReceipt (compiled := compiled)
      prepared.named prepared.diagnostics prepared.code prepared.compilation predecessor
      header.function.source scope id header.reasonAt lowered) := by
  have callback : header.policy.lowerExpression =
      CallableIndexedOwnedPreparedStagedSelectedNamedCompilerRecipes.contextual prepared := by
    have selected := congrArg (fun policy : SourceCoreLoops.Policy => policy.lowerExpression) aligned.policy
    exact selected.trans rfl
  rw [callback] at accepted
  cases fuel with
  | zero =>
    unfold CallableIndexedOwnedPreparedStagedSelectedNamedCompilerRecipes.contextual at accepted
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases accepted
  | succ predecessor =>
    have record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
        prepared.named.signature.key = .ok prepared.named.specialized := by
      simpa only [aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record compiled header
    exact ⟨predecessor, RootPolicyReceipt.of_accepted prepared.compilation record accepted⟩

private theorem read_no_calls
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (root : Certificate policy body compilation readFuel values source context reasonAt scope id lowered)
    {callFuel : Nat} {callScope : SourceCoreLocalCell.Scope} {callId callee : ExpressionId}
    {ids : List ExpressionId} {metadata : IndirectCallResolution} {code : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body callFuel compilation source
      callScope callId callee ids metadata reasonAt code) (path : Calls compiler root) : False := by
  cases path with
  | here sequence children =>
    have identity := Option.some.inj (compiler.found.symm.trans found)
    have same := compiler.originalForm
    rw [identity, form] at same
    cases same
  | @group current id other inner innerNode code actual otherForm innerFound type child inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @tuple_child current id other tupleIds types codes header sequence children child childCode member inside =>
    have identity := Option.some.inj (header.metadata.found.symm.trans found)
    have same := header.form
    rw [identity, form] at same
    cases same
  | @constructor_child current id other instantiation constructorIds tag headerWord codes header otherForm admissible ranges count nodes sequence children child childCode member inside =>
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst other
    simp [form] at otherForm
  | @call_child current id otherCallee otherIds otherMetadata otherFuel code types outer sequence children child childCode member inside =>
    have identity := Option.some.inj (outer.found.symm.trans found)
    have same := outer.originalForm
    rw [identity, form] at same
    cases same
  | @unary_child scope id node operand childNode operator operandType resultType core childCode actual otherForm childFound inputType outputType profile child inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @binary_left scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode actual otherForm leftFound rightFound leftType rightType outputType profile first second inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @binary_right scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode actual otherForm leftFound rightFound leftType rightType outputType profile first second inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @conditional_condition scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode actual otherForm conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @conditional_then scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode actual otherForm conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @conditional_else scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode actual otherForm conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm


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
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (sameSource : invocation.source = header.function.source)
    (sameEvidence : invocation.evidence = header.function.evidence)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (typed : ExpressionHasType invocation.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel invocation.source scope id header.reasonAt = .ok lowered) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.RootAt compiled context invocation
      scope id lowered (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨predecessor, ⟨root⟩⟩ := policy_receipt prepared aligned (by simpa only [sameSource] using accepted)
  have unique : NodeOccurrencesUnique invocation.source := sameSource ▸ header.unique
  have profile := CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.recipe_policy_for
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
  have syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id :=
    .leaf (.read found form)
  have compiledChild : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (predecessor + 1) (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      invocation.source scope id header.reasonAt = .ok lowered := by
    simpa only [sameSource] using root.selected.accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
    unique declarations childProfile coercions syntaxTree found typed compiledChild
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation) certificate := by
    intro callFuel callScope callId callee ids callMetadata code compiler path
    exact False.elim (read_no_calls found form certificate compiler path)
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots
