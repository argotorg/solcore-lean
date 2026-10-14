import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles

/-! Actual read and Boolean occurrences in selected implementation methods are
issued at each reached lexical context. The static support remains indexed by
general mixed roots, while the initial concrete profile excludes calls from its
original node forms rather than from an execution observation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

/-- A factual property of the full original node table, including unused nodes. -/
def LeafSource (source : TypedSource) : Prop :=
  ∀ id node, source.lookupExpression? id = some node →
    (∃ name binder, node.form = .reference name (.local binder)) ∨
    (∃ name value, node.form = .reference name (.builtinBoolean value))

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (leaves : LeafSource principal.sourceBody.source)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source (fun _ => False))

private theorem policy_receipt {scope : SourceCoreLocalCell.Scope} {fuel : Nat}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    ∃ predecessor, Nonempty (CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      principal.named principal.cached.diagnostics principal.cached.code principal.cached.compilation
      predecessor principal.sourceBody.source scope id
      (principal.cached.diagnostics.reasonAt principal.named.signature.key) lowered) := by
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext principal.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    principal.cached.compilation.parents principal.cached.compilation.own.assignments principal.cached.diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed principal.named)
    compiled.indexed.base.callableContext none none fuel principal.sourceBody.source scope id
    (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered at accepted
  cases fuel with
  | zero => rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted; cases accepted
  | succ predecessor =>
    exact ⟨predecessor, CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
      principal.cached.compilation principal.record accepted⟩

include diagnostic receiver wellFormed leaves metadata in
/-- The actual compiler action and selected scope supply a mixed root with all
readiness obligations derived from original Source forms and full context fields. -/
theorem of_child
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields packet.sourceAt.context context)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    (declarations : CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context)
    (tree : GeneralSyntax principal.sourceBody.source id (fun _ => False))
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (typed : ExpressionHasType principal.sourceBody.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    Certificate headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      context child scope id lowered := by
  have sourceEq : child.source = principal.sourceBody.source := stages.source selected
  obtain ⟨predecessor, ⟨root⟩⟩ := policy_receipt principal accepted
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables (fun _ impossible => False.elim impossible)
    metadata scope (principal.cached.diagnostics.reasonAt principal.named.signature.key)
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    packet.sourceAt.unique declarations profile (fun id node tree found => metadata.coercions id tree node found) tree found typed root.selected.accepted
  let result : RootAt compiled headers stages context child scope id lowered
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := RootAt.ofRoot {
    compilerFuel := predecessor + 1
    accepted := by simpa only [sourceEq] using root.selected.accepted
    certificate := by simpa only [sourceEq] using certificate
    node := node
    found := by simpa only [sourceEq] using found
    rawResult := rfl
    typed := by simpa only [sourceEq] using typed
    sameLedger := fields.solvedRequirements.trans packet.sourceAt.valid.ledger
    runtimeLedger := fields.runtimeRequirementLedger packet.sourceAt.valid.runtime
    unique := sourceEq ▸ packet.sourceAt.unique
    wellFormed := wellFormed
    runtime := by simpa only [sourceEq] using (runtime principal packet wellFormed).transport fields
    covers := by rw [stages.evidence selected]; exact fields.covers packet.sourceAt.valid.covers
    actualFunctionType := by rw [root.callables]; rfl
    uninitialized := by
      intro current id code read _reached location
      exact CallableIndexedOwnedPreparedStagedMethodTerminalSupport.uninitialized principal diagnostic receiver
        packet.sourceAt.unique (by simpa only [sourceEq] using read) location
    callsReady := by
      intro callFuel callScope callId callee ids callMetadata code compiler _path
      rcases leaves callId compiler.original (by simpa only [sourceEq] using compiler.found) with
        ⟨name, binder, form⟩ | ⟨name, value, form⟩ <;>
        have impossible := compiler.originalForm <;> simp [form] at impossible
    directReady := by
      intro callFuel callScope callId callee ids instantiation code compiler _path
      rcases leaves callId compiler.node (by simpa only [sourceEq] using compiler.metadata.found) with
        ⟨name, binder, form⟩ | ⟨name, value, form⟩ <;>
        have impossible := compiler.form <;> simp [form] at impossible
    indexReady := by
      intro indexScope indexId base key actual baseNode keyNode layout comparison first second indexed _keyFound form _sourceType _scalar _path
      rcases leaves indexId actual (by simpa only [sourceEq] using indexed.metadata.found) with
        ⟨name, binder, readForm⟩ | ⟨name, value, readForm⟩ <;> simp [readForm] at form
    methodReady := by
      intro callFuel callScope callId code compiler _path
      rcases leaves callId compiler.node (by simpa only [sourceEq] using compiler.metadata.found) with
        ⟨name, binder, readForm⟩ | ⟨name, value, readForm⟩
      all_goals
        rcases compiler.operator.form with ⟨op, operand, form, _arguments⟩ | ⟨op, left, right, form, _arguments⟩ <;>
          simp [readForm] at form }
  exact ⟨result, rfl⟩

include diagnostic receiver wellFormed leaves metadata in
/-- The original scoped grammar and actual method compiler provide every child. -/
theorem of_actual
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {stages : Staging.Recursive.Registry}
    (syntaxTree : GenericImperativeMatch.Syntax principal.sourceBody.source
      (fun id => GeneralSyntax principal.sourceBody.source id (fun _ => False))
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType) :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  apply CallableIndexedOwnedPreparedStagedMethodScopedCollectors.of_compiler principal packet ready member wellFormed
    (CallableIndexedOwnedPreparedStagedMethodScopedCollectors.operands_of_diagnostic principal diagnostic receiver)
    (CallableIndexedOwnedPreparedStagedMethodScopedCollectors.unary_of_diagnostic principal diagnostic receiver) syntaxTree
  intro child selected context fields scope fuel id node lowered declarations tree found typed accepted _nativeType _native
  exact of_child principal packet diagnostic receiver wellFormed leaves metadata selected fields
    declarations tree found typed accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedRoots
