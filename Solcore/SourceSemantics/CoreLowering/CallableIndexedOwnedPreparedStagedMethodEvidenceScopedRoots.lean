import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerResolvedEvidence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerEvidence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodScopedCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles

/-! Authentic direct evidence calls inside selected implementation methods
retain the real caller dictionary and reached lexical ledger. The accepted
method compiler and shared scoped collector supply every child root. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

/-- The initial method profile contains actual references and declaration calls.
The full original node table excludes indirect, indexed and operator-method sites. -/
def DirectSource (source : TypedSource) : Prop :=
  ∀ id node, source.lookupExpression? id = some node →
    (∃ name resolution, node.form = .reference name resolution) ∨
    (∃ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation))

section Resolved
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sourceForms : DirectSource principal.sourceBody.source)
  {directSites : DeclarationInstantiation → Prop}
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
    compiled.sourceProgram principal.named.specialized principal.dictionary)

local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

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

include diagnostic receiver wellFormed sourceForms supported metadata rows covered resolved in
/-- The actual compiler action and selected scope supply a mixed root with all
readiness obligations derived from original Source forms and full context fields. -/
theorem of_child_with_evidence
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields packet.sourceAt.context context)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    (declarations : CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context)
    (tree : GeneralSyntax principal.sourceBody.source id directSites)
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
    root.compilerPolicy root.selected.callables supported
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
      rcases sourceForms callId compiler.original (by simpa only [sourceEq] using compiler.found) with
        ⟨name, resolution, form⟩ | ⟨actualCallee, arguments, instantiation, form⟩ <;>
        have impossible := compiler.originalForm <;> simp [form] at impossible
    directReady := by
      intro callFuel callScope callId callee ids instantiation code compiler path
      have originalTree : GeneralSyntax child.source id directSites := by simpa only [sourceEq] using tree
      have childMetadata : MetadataFor compiled.indexed principal.named child.source directSites := by
        simpa only [sourceEq] using metadata
      have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path originalTree
      have site := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax.direct_site
        actualTree compiler.metadata.found compiler.form
      obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory_at compiler rows
        (covered instantiation site compiler.index compiler.signature compiler.target compiler.global) rfl
      rcases CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.accepted_direct_action
        root.compilerPolicy childMetadata actualTree compiler.metadata.found compiler.form compiler.accepted with bypass | authentic
      · obtain ⟨requirements, assumptions⟩ :=
          CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct
            compiler.metadata.found compiler.form bypass
        have special := fun callback budget =>
          (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.direct_hook root.compilerPolicy
            childMetadata actualTree compiler.metadata.found compiler.form callback budget callScope
            (principal.cached.diagnostics.reasonAt principal.named.signature.key)).trans
            (CallableCallEvidenceCertificates.direct_bypass compiler.metadata.found compiler.form requirements
              compiler.metadata.coercions assumptions)
        have ordinary := compiler.ordinary special
          (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy root.compilerPolicy childMetadata actualTree)
        exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
          compiler port ordinary requirements context child.evidence⟩⟩
      · obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
          compiler.metadata.found compiler.form authentic
        rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at actual
        let caller := CallableIndexedOwnedPreparedStagedMethodCallerResolvedEvidence.of_selected
          principal packet.sourceAt resolved selected fields
        exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence_of_resolved
          compiler port actual caller.resolved caller.signatures caller.ledger caller.assumptions caller.unique⟩⟩
    indexReady := by
      intro indexScope indexId base key actual baseNode keyNode layout comparison first second indexed _keyFound form _sourceType _scalar _path
      rcases sourceForms indexId actual (by simpa only [sourceEq] using indexed.metadata.found) with
        ⟨name, resolution, nodeForm⟩ | ⟨callee, arguments, instantiation, nodeForm⟩ <;> simp [nodeForm] at form
    methodReady := by
      intro callFuel callScope callId code compiler _path
      rcases sourceForms callId compiler.node (by simpa only [sourceEq] using compiler.metadata.found) with
        ⟨name, resolution, nodeForm⟩ | ⟨callee, arguments, instantiation, nodeForm⟩
      all_goals
        rcases compiler.operator.form with ⟨op, operand, form, _arguments⟩ | ⟨op, left, right, form, _arguments⟩ <;>
          simp [nodeForm] at form }
  exact ⟨result, rfl⟩

include diagnostic receiver wellFormed sourceForms supported metadata rows covered resolved in
/-- The original scoped grammar and actual method compiler provide every child. -/
theorem of_actual_with_evidence
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {stages : Staging.Recursive.Registry}
    (syntaxTree : GenericImperativeMatch.Syntax principal.sourceBody.source
      (fun id => GeneralSyntax principal.sourceBody.source id directSites)
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType) :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  apply CallableIndexedOwnedPreparedStagedMethodScopedCollectors.of_compiler principal packet ready member wellFormed diagnostic
    (CallableIndexedOwnedPreparedStagedMethodScopedCollectors.operands_of_diagnostic principal diagnostic receiver)
    (CallableIndexedOwnedPreparedStagedMethodScopedCollectors.unary_of_diagnostic principal diagnostic receiver) syntaxTree
  intro child selected context fields scope fuel id node lowered declarations tree found typed accepted _nativeType _native
  exact of_child_with_evidence principal packet diagnostic receiver wellFormed sourceForms supported metadata rows covered resolved selected fields
    declarations tree found typed accepted

end Resolved

section Generic
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sourceForms : DirectSource principal.sourceBody.source)
  {directSites : DeclarationInstantiation → Prop}
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (catalog : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)

local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

private def resolved_generic :
    CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
      compiled.sourceProgram principal.named.specialized principal.dictionary := by
  have empty := CallableIndexedOwnedPreparedStagedMethodCallerEvidence.assumptions_empty_generic principal catalog
  have dictionary := RecursiveMethodSelectionIdentity.dictionary_empty principal.selected empty
  have callerEmpty : principal.named.specialized.assumptions = [] := by
    rw [principal.cached.same]
    exact empty
  refine ⟨[], ?_, dictionary⟩
  rw [callerEmpty]
  rfl

include diagnostic receiver wellFormed sourceForms supported metadata rows covered catalog in
theorem of_child_generic
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields packet.sourceAt.context context)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    (declarations : CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context)
    (tree : GeneralSyntax principal.sourceBody.source id directSites)
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (typed : ExpressionHasType principal.sourceBody.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    Certificate headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      context child scope id lowered := by
  exact of_child_with_evidence principal packet diagnostic receiver wellFormed sourceForms supported metadata rows covered
    (resolved_generic principal catalog) selected fields declarations tree found typed accepted

include diagnostic receiver wellFormed sourceForms supported metadata rows covered catalog in
theorem of_actual_generic
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {stages : Staging.Recursive.Registry}
    (syntaxTree : GenericImperativeMatch.Syntax principal.sourceBody.source
      (fun id => GeneralSyntax principal.sourceBody.source id directSites)
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType) :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  exact of_actual_with_evidence principal packet diagnostic receiver wellFormed sourceForms supported metadata rows covered
    (resolved_generic principal catalog) ready member syntaxTree

end Generic


section Legacy
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (packet : Packet principal)
  (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sourceForms : DirectSource principal.sourceBody.source)
  {directSites : DeclarationInstantiation → Prop}
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed principal.named principal.sourceBody.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (catalog : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)

local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

include diagnostic receiver wellFormed sourceForms supported metadata rows covered catalog in
theorem of_child
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields packet.sourceAt.context context)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    (declarations : CompatibleExpressionReads.ScopeDeclarations principal.sourceBody.source scope context)
    (tree : GeneralSyntax principal.sourceBody.source id directSites)
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (typed : ExpressionHasType principal.sourceBody.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (CallablePreparedMethodRuntimeProfileFactory.policy principal.cached.compilation).lowerExpression
      fuel principal.sourceBody.source scope id (principal.cached.diagnostics.reasonAt principal.named.signature.key) = .ok lowered) :
    Certificate headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      context child scope id lowered := by
  exact of_child_generic principal packet diagnostic receiver wellFormed sourceForms supported metadata rows covered
    (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed catalog) selected fields
    declarations tree found typed accepted

include diagnostic receiver wellFormed sourceForms supported metadata rows covered catalog in
theorem of_actual
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {stages : Staging.Recursive.Registry}
    (syntaxTree : GenericImperativeMatch.Syntax principal.sourceBody.source
      (fun id => GeneralSyntax principal.sourceBody.source id directSites)
      packet.sourceAt.context (.statements true principal.cached.compilation.statements) principal.sourceBody.resultType) :
    Support principal packet headers stages
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  exact of_actual_generic principal packet diagnostic receiver wellFormed sourceForms supported metadata rows covered
    (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed catalog) ready member syntaxTree

end Legacy

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots
