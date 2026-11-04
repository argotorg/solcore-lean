import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedCanonicalSupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalDirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LexicalBodyFaults
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DirectCallers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalMixedFamilies

/-!
# Staged bounds: named evidence and scoped roots

Evidence frames of named callers, scoped and lexical roots, and the terminal support of evidence and mixed named bodies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots
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
  | @method_child current id otherFuel code types outer sequence children child childCode member inside =>
    have identity := Option.some.inj (outer.metadata.found.symm.trans found)
    rcases outer.operator.form with ⟨operator, operand, otherForm, _⟩ | ⟨operator, left, right, otherForm, _⟩
    all_goals rw [identity, form] at otherForm; cases otherForm
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
  | @builtin_child current id otherCallee otherIds function otherFuel code outer calleeTyped sourceType nativeTypes sequence children child childCode member inside =>
    have identity := Option.some.inj (outer.metadata.found.symm.trans found)
    have same := outer.form
    rw [identity, form] at same
    cases same
  | @direct_child current id callee directIds instantiation fuel code types outer calleeTyped application sequence children child childCode member inside =>
    have identity := Option.some.inj (outer.metadata.found.symm.trans found)
    have same := outer.form
    rw [identity, form] at same
    cases same
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
  | @index_base scope id other base key baseNode keyNode layout comparison first second header keyFound otherForm sourceType firstTree secondTree inside
  | @index_key scope id other base key baseNode keyNode layout comparison first second header keyFound otherForm sourceType firstTree secondTree inside =>
    have identity := Option.some.inj (header.metadata.found.symm.trans found)
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames
/-! The actual named terminal and selected Source scope retain the caller's
complete ledger and resolved dictionary. No execution trace is required. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames
open Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}

/-- The original caller preparation is reindexed by its genuine cached row. -/
structure CallerAt (terminal : Terminal header) (child : Staging.Recursive.Scope) where
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled terminal.prepared.named.specialized
  signatures : header.context.signatures = compiled.sourceProgram.signatures
  ledger : header.context.solvedRequirements = terminal.prepared.named.specialized.function.solvedRequirements
  assumptions : ∀ goal, goal ∈ terminal.prepared.named.specialized.assumptions → goal ∈ header.context.assumptions
  unique : RequirementIdsUnique header.context
  dictionary : child.evidence = prepared.view.evidence

private theorem reindex_view {left right : SourceSpecialization.SpecializedFunction}
    (same : left = right) (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled left) :
    (same ▸ prepared).view = prepared.view := by
  cases same
  rfl

/-- Parameter installation preserves the original caller's signature catalog,
assumptions and ledger; scope selection preserves its exact dictionary. -/
def of_selected (terminal : Terminal header) {stages : Staging.Recursive.Registry}
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallerAt terminal child := by
  let prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled terminal.prepared.named.specialized :=
    terminal.prepared.same.symm ▸ terminal.prepared
  have view : prepared.view = terminal.prepared.view := reindex_view _ _
  have fields := RecursiveNamedInitialContextValidity.mono_fields header.extended
  refine ⟨prepared, ?_, header.valid.ledger.trans terminal.aligned.solved, ?_, ?_, ?_⟩
  · rw [fields.signatures, terminal.aligned.function]
    rfl
  · intro goal member
    rw [fields.assumptions, terminal.aligned.function]
    exact member
  · exact (RecursiveNamedInitialContextValidity.scoped_ledger header.frame header.extended wellFormed).idsUnique
  · rw [stages.evidence selected, terminal.aligned.function, view]

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceScopedCallerFrames
/-! The actual prepared named row and selected Source scope determine the
complete caller dictionary at every lexical context. Local changes preserve
the nonlocal context fields; no terminal body or execution premise is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceScopedCallerFrames
open Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}

/-- The dictionary keeps the original prepared row; the ledger and signature
facts refer to the actual context reached inside that named body. -/
structure CallerAt (actual : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (context : SourceSemantics.Context) (child : Staging.Recursive.Scope) where
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled actual.named.specialized
  signatures : context.signatures = compiled.sourceProgram.signatures
  ledger : context.solvedRequirements = actual.named.specialized.function.solvedRequirements
  assumptions : ∀ goal, goal ∈ actual.named.specialized.assumptions → goal ∈ context.assumptions
  unique : RequirementIdsUnique context
  dictionary : child.evidence = prepared.view.evidence

private theorem reindex_view {left right : SourceSpecialization.SpecializedFunction}
    (same : left = right) (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled left) :
    (same ▸ prepared).view = prepared.view := by
  cases same
  rfl

/-- Header preparation fixes the complete caller dictionary. Parameter entry
and subsequent lexical context changes preserve its assumptions and ledger. -/
def of_selected
    (actual : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {instantiation : DeclarationInstantiation}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt actual instantiation header)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {context : SourceSemantics.Context}
    (fields : Dynamic.RuntimeContextFields header.context context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallerAt actual context child := by
  let prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled actual.named.specialized :=
    actual.same.symm ▸ actual
  have view : prepared.view = actual.view := reindex_view _ _
  have parameters := RecursiveNamedInitialContextValidity.mono_fields header.extended
  refine ⟨prepared, ?_, fields.solvedRequirements.trans (header.valid.ledger.trans aligned.solved), ?_, ?_, ?_⟩
  · rw [fields.signatures, parameters.signatures, aligned.function]
    rfl
  · intro goal member
    rw [fields.assumptions, parameters.assumptions, aligned.function]
    exact member
  · simpa only [RequirementIdsUnique, fields.solvedRequirements] using
      (RecursiveNamedInitialContextValidity.scoped_ledger header.frame header.extended wellFormed).idsUnique
  · rw [stages.evidence selected, aligned.function, view]

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceScopedCallerFrames
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport
/-! Actual named compiler recipes authenticate the complete caller and callee
 dictionaries before the common static root enters the shared numeric family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (MethodStepPolicyFor GeneralSyntax Certificate)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport (policy_receipt SidecarAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)

section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source directSites)
  (tree : GeneralSyntax header.function.source terminal.expression directSites)
  {stages : Staging.Recursive.Registry}

variable {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (noIndirect : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirectSource header.function.source)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include wellFormed metadata tree rows covered in
/-- Each reached declaration obtains evidence at this exact selected caller
frame, from the same authentic compiler action as the static certificate. -/
theorem direct_ready {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    {child : Staging.Recursive.Scope}
    (sameSource : child.source = header.function.source)
    (selected : stages.Closure header.function child)
    (certificate : Certificate root.selected.policy root.selected.lowerBody
      (context compiled.indexed terminal.prepared.named) compiled.indexed.fuel
      (.initial compiled.compatible.checked) child.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    ∀ {callFuel callScope id callee ids instantiation lowered}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel (context compiled.indexed terminal.prepared.named)
        (.initial compiled.compatible.checked) child.source callScope id callee ids instantiation header.reasonAt lowered),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) header.context child.evidence) := by
  intro callFuel callScope id callee ids instantiation lowered compiler path
  have originalTree : GeneralSyntax child.source terminal.expression directSites := by
    simpa only [sameSource] using tree
  have childMetadata : MetadataFor compiled.indexed terminal.prepared.named child.source directSites := by
    simpa only [sameSource] using metadata
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
        childMetadata actualTree compiler.metadata.found compiler.form callback budget callScope header.reasonAt).trans
        (CallableCallEvidenceCertificates.direct_bypass compiler.metadata.found compiler.form requirements
          compiler.metadata.coercions assumptions)
    have ordinary := compiler.ordinary special
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy root.compilerPolicy childMetadata actualTree)
    exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
      compiler port ordinary requirements header.context child.evidence⟩⟩
  · obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
      compiler.metadata.found compiler.form authentic
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at actual
    let caller := CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames.of_selected terminal selected wellFormed
    exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence
      compiler port actual caller.prepared caller.signatures caller.ledger caller.assumptions caller.unique caller.dictionary⟩⟩

include wellFormed metadata tree checked catalog methods actualStages in
/-- The original policy is opened at the exact reached method leaf. The
retained compiler program is re-established here from that real recipe. -/
theorem method_ready_with_catalog {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    {child : Staging.Recursive.Scope}
    (sameSource : child.source = header.function.source)
    (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (certificate : Certificate root.selected.policy root.selected.lowerBody
      (context compiled.indexed terminal.prepared.named) compiled.indexed.fuel
      (.initial compiled.compatible.checked) child.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    ∀ {callFuel callScope id lowered}
      (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel (context compiled.indexed terminal.prepared.named)
        (.initial compiled.compatible.checked) child.source callScope id header.reasonAt lowered),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
        compiler header.context child.evidence (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  intro callFuel callScope id lowered compiler path
  have originalTree : GeneralSyntax child.source terminal.expression directSites := by simpa only [sameSource] using tree
  have childMetadata : MetadataFor compiled.indexed terminal.prepared.named child.source directSites := by
    simpa only [sameSource] using metadata
  have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.method_calls_syntax_of path originalTree
  have form : (∃ operator operand, compiler.node.form = .unary operator operand) ∨
      (∃ operator left right, compiler.node.form = .binary left operator right) := by
    rcases compiler.operator.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
    · exact .inl ⟨operator, operand, form⟩
    · exact .inr ⟨operator, left, right, form⟩
  have hook := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.operator_hook
    root.compilerPolicy childMetadata actualTree compiler.metadata.found form
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child root.selected.policy root.selected.lowerBody
      callFuel (context compiled.indexed terminal.prepared.named)) (callFuel+1) callScope header.reasonAt
  have accepted := hook.symm.trans compiler.special
  have nonempty : compiler.node.requirements ≠ [] := by
    intro empty
    exact compiler.operator.nonempty ((CallableIndexedOwnedPreparedStagedMethodArgumentRows.requirements compiler).trans empty)
  obtain ⟨actual⟩ := CallablePreparedMethodSelection.of_accepted compiler.metadata.found form
    (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.ordinary_requirements compiler.metadata.coercions)
    nonempty accepted
  rw [← root.selected.callables] at actual
  rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at actual
  obtain ⟨sourceReceipt⟩ := CallablePreparedMethodRuntimeMeaning.OperatorSource.of_accepted actual
  let caller := CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames.of_selected terminal selected wellFormed
  have unique : NodeOccurrencesUnique child.source := sameSource ▸ header.unique
  obtain ⟨rootNode, _found, _type, originalTyped⟩ :=
    CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
  have rootTyped : ExpressionHasType child.source header.context terminal.expression rootNode.type := by
    simpa only [sameSource] using originalTyped
  have parentTyped := CallableIndexedOwnedPreparedStagedMethodPathTyping.parent_typed compiler unique rootTyped path
  have callerMember := (CallableNamedMetadata.specialization_of_exact
    (CallableIndexedActualNamedSourceReceipts.cached_record compiled terminal.prepared.selected terminal.prepared.compilation.hook)).1
  have sourceEq : child.source = terminal.prepared.named.specialized.function.typedBody :=
    sameSource.trans (header.agreement.source.trans (congrArg
      (fun named : SourceCoreGeneralFunctions.Function => named.specialized.function.typedBody) terminal.aligned.named))
  have nodeMember : .expression compiler.node ∈ terminal.prepared.named.specialized.function.typedBody.nodes := by
    have found : terminal.prepared.named.specialized.function.typedBody.lookupExpression? id = some compiler.node :=
      by simpa only [sourceEq] using compiler.metadata.found
    exact (lookupExpression?_sound found).1
  have dictionary : child.evidence = CallableNamedMetadata.environment actual.available := by
    have same := Except.ok.inj (actual.resolved.symm.trans caller.prepared.resolved)
    rw [caller.dictionary, same]
    rfl
  exact CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.of_actual compiler actual compiler.special
    sourceReceipt methods checked wellFormed catalog
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
    callerMember nodeMember rfl rfl caller.signatures caller.ledger caller.assumptions caller.unique dictionary unique parentTyped actualStages
include diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog methods actualStages in
/-- The Source frame and actual selected child derive all runtime-independent
conditions. No native argument or source heap representation is assumed. -/
def at_scope_sites_with_catalog {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child) :
    { support : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry actualStages).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ header.unique
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables supported metadata (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt
  have available : (header.function.source.lookupExpression? terminal.expression).isSome := by
    obtain ⟨node, found, _⟩ := CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child
      terminal.receipt selected wellFormed
    exact Option.isSome_of_eq_some found
  let node := (header.function.source.lookupExpression? terminal.expression).get available
  have found : header.function.source.lookupExpression? terminal.expression = some node :=
    Option.eq_some_of_isSome available
  have properties : node.type = header.function.resultType ∧
      ExpressionHasType header.function.source header.context terminal.expression node.type := by
    obtain ⟨original, originalFound, rawType, typed⟩ :=
      CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
    have same := Option.some.inj (originalFound.symm.trans found)
    exact same ▸ ⟨rawType, typed⟩
  have rawType := properties.1
  have typed := properties.2
  have childFound : child.source.lookupExpression? terminal.expression = some node := by
    simpa only [sourceEq] using found
  have childTyped : ExpressionHasType child.source header.context terminal.expression node.type := by
    simpa only [sourceEq] using typed
  have childProfile : MethodStepPolicyFor root.selected.policy (context compiled.indexed terminal.prepared.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt directSites := by
    simpa only [sourceEq] using profile
  have childDeclarations : CompatibleExpressionReads.ScopeDeclarations child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.context := by
    simpa only [sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using declarations
  have coercions : ∀ id actualNode, GeneralSyntax child.source id directSites →
      child.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sourceEq] using syntaxTree)
      actualNode (by simpa only [sourceEq] using actualFound)
  have childTree : GeneralSyntax child.source terminal.expression directSites := by simpa only [sourceEq] using tree
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (fuel + 1) (context compiled.indexed terminal.prepared.named) child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt = .ok terminal.receipt.child := by
    simpa only [sourceEq] using root.selected.accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique childDeclarations childProfile coercions childTree childFound childTyped accepted
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.context child.source := by
    rw [sourceEq]
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
        header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have noCalls : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirect
      (compiled := compiled) (invocation := child) certificate :=
    CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirect.of_source certificate
      (by simpa only [sourceEq] using noIndirect)
  let support : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt compiled
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages) header.context child
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults :=
    CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt.ofRoot {
      compilerFuel := fuel + 1
      accepted := accepted
      certificate := certificate
      node := node
      found := childFound
      rawResult := rawType
      typed := childTyped
      sameLedger := header.valid.ledger.trans terminal.aligned.solved
      runtimeLedger := RecursiveNamedInitialContextValidity.runtime header.frame header.extended wellFormed
      unique := unique
      wellFormed := wellFormed
      runtime := runtime
      covers := by
        rw [(RecursiveNamedPreparedStageScopes.registry actualStages).evidence selected]
        exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
      actualFunctionType := by rw [root.callables]; rfl
      uninitialized := fun _ _ _ read _ location =>
        CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized terminal.prepared diagnostic
          terminal.aligned receiver (by simpa only [sourceEq] using read) location
      callsReady := by intro callFuel callScope id callee ids metadata lowered compiler path; exact False.elim (noCalls compiler path)
      directReady := direct_ready terminal wellFormed metadata tree rows covered root sourceEq selected certificate
      indexReady := CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.named_ready
        terminal.prepared diagnostic terminal.aligned sourceEq certificate
      methodReady := method_ready_with_catalog terminal wellFormed metadata tree checked catalog methods actualStages root sourceEq selected certificate
      noIndirect := noCalls }
  exact ⟨support, rfl, rfl, rfl⟩

include diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog methods actualStages in
/-- Original named compilation, real caller evidence and the actual method cache
produce the physical body support. Every execution premise comes later. -/
theorem of_actual_with_catalog
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  obtain ⟨fuel, ⟨root⟩⟩ := policy_receipt terminal
  exact ⟨⟨point, fun child selected => at_scope_sites_with_catalog terminal diagnostic receiver wellFormed supported metadata tree
    rows covered noIndirect checked catalog methods actualStages root child selected⟩⟩

end Generic


section GenericWrappers
variable {directSites : DeclarationInstantiation → Prop}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source directSites)
  (tree : GeneralSyntax header.function.source terminal.expression directSites)
  {stages : Staging.Recursive.Registry}

variable {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (noIndirect : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirectSource header.function.source)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include wellFormed metadata tree checked catalog methods actualStages in
theorem method_ready_generic {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    {child : Staging.Recursive.Scope}
    (sameSource : child.source = header.function.source)
    (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (certificate : Certificate root.selected.policy root.selected.lowerBody
      (context compiled.indexed terminal.prepared.named) compiled.indexed.fuel
      (.initial compiled.compatible.checked) child.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    ∀ {callFuel callScope id lowered}
      (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel (context compiled.indexed terminal.prepared.named)
        (.initial compiled.compatible.checked) child.source callScope id header.reasonAt lowered),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
        compiler header.context child.evidence (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  exact method_ready_with_catalog terminal wellFormed metadata tree checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.generic methods) actualStages root sameSource selected certificate

include diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog methods actualStages in
def at_scope_sites_generic {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child) :
    { support : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  exact at_scope_sites_with_catalog terminal diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.generic methods) actualStages root child selected

include diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog methods actualStages in
theorem of_actual_generic
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  exact of_actual_with_catalog terminal diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.generic methods) actualStages point

end GenericWrappers

section EvidenceWrappers
variable {directSites : DeclarationInstantiation → Prop}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source directSites)
  (tree : GeneralSyntax header.function.source terminal.expression directSites)
  {stages : Staging.Recursive.Registry}

variable {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (noIndirect : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirectSource header.function.source)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog compiled)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include wellFormed metadata tree checked catalog methods actualStages in
theorem method_ready_with_evidence {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    {child : Staging.Recursive.Scope}
    (sameSource : child.source = header.function.source)
    (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (certificate : Certificate root.selected.policy root.selected.lowerBody
      (context compiled.indexed terminal.prepared.named) compiled.indexed.fuel
      (.initial compiled.compatible.checked) child.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    ∀ {callFuel callScope id lowered}
      (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel (context compiled.indexed terminal.prepared.named)
        (.initial compiled.compatible.checked) child.source callScope id header.reasonAt lowered),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
        compiler header.context child.evidence (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  exact method_ready_with_catalog terminal wellFormed metadata tree checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.evidence methods) actualStages root sameSource selected certificate

include diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog methods actualStages in
def at_scope_sites_with_evidence {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child) :
    { support : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  exact at_scope_sites_with_catalog terminal diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.evidence methods) actualStages root child selected

include diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog methods actualStages in
theorem of_actual_with_evidence
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  exact of_actual_with_catalog terminal diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.evidence methods) actualStages point

end EvidenceWrappers

section Legacy
variable {directSites : DeclarationInstantiation → Prop}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source directSites)
  (tree : GeneralSyntax header.function.source terminal.expression directSites)
  {stages : Staging.Recursive.Registry}

variable {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  (noIndirect : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.NoIndirectSource header.function.source)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include wellFormed metadata tree checked catalog methods actualStages in
theorem method_ready {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    {child : Staging.Recursive.Scope}
    (sameSource : child.source = header.function.source)
    (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (certificate : Certificate root.selected.policy root.selected.lowerBody
      (context compiled.indexed terminal.prepared.named) compiled.indexed.fuel
      (.initial compiled.compatible.checked) child.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    ∀ {callFuel callScope id lowered}
      (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel (context compiled.indexed terminal.prepared.named)
        (.initial compiled.compatible.checked) child.source callScope id header.reasonAt lowered),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
        compiler header.context child.evidence (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  exact method_ready_generic terminal wellFormed metadata tree checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) actualStages root sameSource selected certificate

include diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog methods actualStages in
def at_scope_sites {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child) :
    { support : CallableIndexedOwnedPreparedStagedMethodRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  exact at_scope_sites_generic terminal diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) actualStages root child selected

include diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog methods actualStages in
theorem of_actual
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  exact of_actual_generic terminal diagnostic receiver wellFormed supported metadata tree rows covered noIndirect checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) actualStages point

end Legacy

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPhysicalMixedScopedRoots
/-! Actual named compiler children share physical mixed roots at every lexical
context. Direct calls, trait methods and indirect calls retain the original
caller ledger, full dictionary and actual selected compiler action. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPhysicalMixedScopedRoots
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax MethodStepPolicyFor)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (RootAt)

section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
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
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed prepared.named header.function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry actual
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog methods in
/-- Original Source typing and the actual accepted action determine this root.
All lexical context changes come from the compiler collector's binder fields. -/
theorem of_policy_sites_with_catalog
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
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
    ∃ root : RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      stages context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  have sameSource := (stages).source selected
  have unique : NodeOccurrencesUnique invocation.source := sameSource ▸ header.unique
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables supported metadata scope header.reasonAt
  have childProfile : MethodStepPolicyFor root.selected.policy (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) invocation.source scope header.reasonAt directSites := by
    simpa only [sameSource] using profile
  have coercions : ∀ id actualNode, GeneralSyntax invocation.source id directSites →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sameSource] using syntaxTree)
      actualNode (by simpa only [sameSource] using actualFound)
  have compiledChild := accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique declarations childProfile coercions tree found typed compiledChild
  obtain ⟨sidecar, issued⟩ := CallableIndexedActualNamedSourceReceipts.hook_sidecar compiled header.hook
  have sourceReceipt := (CallableIndexedActualNamedSourceReceipts.header_source compiled header).1
  have canonicalSource : header.function.source = sidecar.source := by
    simpa only [EmptySourceSubstitution.source] using sourceReceipt.source issued
  obtain ⟨request, signature, generic, signatureMember, _with_catalogMember, _requested, specialized⟩ := prepared.origin
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
    have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.calls_syntax_of path tree
    have readPolicy := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy
      root.compilerPolicy metadata (by simpa only [sameSource] using syntaxTree)
    have childRead : root.selected.policy.readExpression invocation.source callId =
        SourceCoreCompatibleDataExpressions.readExpression
          (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked invocation.source callId := by
      simpa only [sameSource, SourceCoreCompatibleValues.Context.initial] using readPolicy
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
  have directReady : ∀ {callFuel callScope callId callee ids instantiation callCode}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel
        (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
        (.initial compiled.compatible.checked) invocation.source callScope callId callee ids
        instantiation header.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) context invocation.evidence) := by
    intro callFuel callScope callId callee ids instantiation callCode compiler path
    have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path tree
    have site := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax.direct_site
      actualTree compiler.metadata.found compiler.form
    obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory_at compiler rows
      (covered instantiation site compiler.index compiler.signature compiler.target compiler.global) rfl
    have childMetadata : MetadataFor compiled.indexed prepared.named invocation.source directSites := by
      simpa only [sameSource] using metadata
    rcases CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.accepted_direct_action
      root.compilerPolicy childMetadata actualTree compiler.metadata.found compiler.form compiler.accepted with bypass | authentic
    · obtain ⟨requirements, assumptions⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct
          compiler.metadata.found compiler.form bypass
      have special := fun callback budget =>
        (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.direct_hook root.compilerPolicy
          childMetadata actualTree compiler.metadata.found compiler.form callback budget callScope header.reasonAt).trans
          (CallableCallEvidenceCertificates.direct_bypass compiler.metadata.found compiler.form requirements
            compiler.metadata.coercions assumptions)
      have ordinary := compiler.ordinary special
        (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy root.compilerPolicy childMetadata actualTree)
      exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
        compiler port ordinary requirements context invocation.evidence⟩⟩
    · obtain ⟨action⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
        compiler.metadata.found compiler.form authentic
      rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at action
      let caller := CallableIndexedOwnedPreparedStagedNamedEvidenceScopedCallerFrames.of_selected
        prepared aligned selected fields wellFormed
      exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence
        compiler port action caller.prepared caller.signatures caller.ledger caller.assumptions caller.unique caller.dictionary⟩⟩
  have methodReady : ∀ {callFuel callScope callId callCode}
      (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel
        (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
        (.initial compiled.compatible.checked) invocation.source callScope callId header.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.MethodCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
        compiler context invocation.evidence stages) := by
    intro callFuel callScope callId methodCode compiler path
    have originalTree := tree
    have childMetadata : MetadataFor compiled.indexed prepared.named invocation.source directSites := by
      simpa only [sameSource] using metadata
    have actionTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.method_calls_syntax_of path originalTree
    have form : (∃ operator operand, compiler.node.form = .unary operator operand) ∨
        (∃ operator left right, compiler.node.form = .binary left operator right) := by
      rcases compiler.operator.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
      · exact .inl ⟨operator, operand, form⟩
      · exact .inr ⟨operator, left, right, form⟩
    have hook := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.operator_hook
      root.compilerPolicy childMetadata actionTree compiler.metadata.found form
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child root.selected.policy root.selected.lowerBody
        callFuel (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)) (callFuel+1) callScope header.reasonAt
    have accepted := hook.symm.trans compiler.special
    have nonempty : compiler.node.requirements ≠ [] := by
      intro empty
      exact compiler.operator.nonempty ((CallableIndexedOwnedPreparedStagedMethodArgumentRows.requirements compiler).trans empty)
    obtain ⟨action⟩ := CallablePreparedMethodSelection.of_accepted compiler.metadata.found form
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.ordinary_requirements compiler.metadata.coercions)
      nonempty accepted
    rw [← root.selected.callables] at action
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at action
    obtain ⟨sourceReceipt⟩ := CallablePreparedMethodRuntimeMeaning.OperatorSource.of_accepted action
    let caller := CallableIndexedOwnedPreparedStagedNamedEvidenceScopedCallerFrames.of_selected prepared aligned selected fields wellFormed
    have parentTyped := CallableIndexedOwnedPreparedStagedMethodPathTyping.parent_typed compiler unique typed path
    have callerMember := (CallableNamedMetadata.specialization_of_exact
      (CallableIndexedActualNamedSourceReceipts.cached_record compiled prepared.selected prepared.compilation.hook)).1
    have sourceEq : invocation.source = prepared.named.specialized.function.typedBody :=
      sameSource.trans (header.agreement.source.trans (congrArg
        (fun named : SourceCoreGeneralFunctions.Function => named.specialized.function.typedBody) aligned.named))
    have nodeMember : .expression compiler.node ∈ prepared.named.specialized.function.typedBody.nodes := by
      have found : prepared.named.specialized.function.typedBody.lookupExpression? callId = some compiler.node :=
        by simpa only [sourceEq] using compiler.metadata.found
      exact (lookupExpression?_sound found).1
    have dictionary : invocation.evidence = CallableNamedMetadata.environment action.available := by
      have same := Except.ok.inj (action.resolved.symm.trans caller.prepared.resolved)
      rw [caller.dictionary, same]
      rfl
    exact CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.of_actual compiler action compiler.special
      sourceReceipt methods checked wellFormed catalog
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled)
      callerMember nodeMember rfl rfl caller.signatures caller.ledger caller.assumptions caller.unique dictionary unique parentTyped actual
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source := by
    rw [sameSource]
    obtain ⟨_, sourceTyped⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
        header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact sourceTyped.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact (original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)).transport fields
  let result : RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      stages context invocation scope id lowered faults := RootAt.ofRoot {
    compilerFuel := fuel
    accepted := accepted
    certificate := certificate
    node := node
    found := found
    rawResult := rfl
    typed := typed
    sameLedger := fields.solvedRequirements.trans (header.valid.ledger.trans aligned.solved)
    runtimeLedger := fields.runtimeRequirementLedger
      (RecursiveNamedInitialContextValidity.runtime header.frame header.extended wellFormed)
    unique := unique
    wellFormed := wellFormed
    runtime := runtime
    covers := by
      rw [(stages).evidence selected]
      exact fields.covers (RecursiveNamedInitialContextValidity.covers header.frame header.extended)
    actualFunctionType := by rw [root.callables]; rfl
    uninitialized := fun _ _ _ read _ location =>
      CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized prepared diagnostic aligned receiver
        (by simpa only [sameSource] using read) location
    callsReady := ready
    directReady := directReady
    indexReady := CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.named_ready
      prepared diagnostic aligned sameSource certificate
    methodReady := methodReady }
  exact ⟨result, rfl⟩


include prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog methods in
/-- Original Source typing and the actual accepted action determine this root.
All lexical context changes come from the compiler collector's binder fields. -/
theorem of_accepted_sites_with_catalog
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel invocation.source scope id header.reasonAt = .ok lowered) :
    ∃ root : RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      stages context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  have sameSource := (stages).source selected
  obtain ⟨predecessor, ⟨root⟩⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.policy_receipt
    prepared aligned (by simpa only [sameSource] using accepted)
  exact of_policy_sites_with_catalog prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog methods actual selected
    fields declarations tree found typed root (by simpa only [sameSource] using root.selected.accepted)

end Generic



section GenericWrappers
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
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
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed prepared.named header.function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry actual
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog methods in
theorem of_policy_sites_generic
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
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
    ∃ root : RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      stages context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  exact of_policy_sites_with_catalog prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.generic methods) actual selected fields declarations tree found typed root accepted

include prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog methods in
theorem of_accepted_sites_generic
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel invocation.source scope id header.reasonAt = .ok lowered) :
    ∃ root : RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      stages context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  exact of_accepted_sites_with_catalog prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.generic methods) actual selected fields declarations tree found typed accepted

end GenericWrappers

section EvidenceWrappers
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
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
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed prepared.named header.function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog compiled)
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry actual
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog methods in
theorem of_policy_sites_with_evidence
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
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
    ∃ root : RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      stages context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  exact of_policy_sites_with_catalog prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.evidence methods) actual selected fields declarations tree found typed root accepted

include prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog methods in
theorem of_accepted_sites_with_evidence
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel invocation.source scope id header.reasonAt = .ok lowered) :
    ∃ root : RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      stages context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  exact of_accepted_sites_with_catalog prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.evidence methods) actual selected fields declarations tree found typed accepted

end EvidenceWrappers

section Legacy
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
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
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed prepared.named header.function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry actual
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog methods in
theorem of_policy_sites
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
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
    ∃ root : RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      stages context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  exact of_policy_sites_generic prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) actual selected fields declarations tree found typed root accepted

include prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog methods in
theorem of_accepted_sites
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel invocation.source scope id header.reasonAt = .ok lowered) :
    ∃ root : RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      stages context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  exact of_accepted_sites_generic prepared aligned diagnostic receiver wellFormed supported metadata rows covered checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) actual selected fields declarations tree found typed accepted

end Legacy

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPhysicalMixedScopedRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalScopedRoots
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

section Sites
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
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
  (ordinary : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Ordinary compiled.indexed.base.plan instantiation)
  (metadata : NativeMetadataFor compiled.indexed prepared.named header.function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry actual
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include prepared aligned diagnostic receiver wellFormed ordinary metadata complete in
/-- Original Source typing and the actual accepted action determine this root.
All lexical context changes come from the compiler collector's binder fields. -/
theorem of_policy_sites
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
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
      compiled.indexed.fuel (.initial compiled.compatible.checked) invocation.source scope header.reasonAt directSites := by
    simpa only [sameSource] using profile
  have coercions : ∀ id actualNode, GeneralSyntax invocation.source id directSites →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sameSource] using syntaxTree)
      actualNode (by simpa only [sameSource] using actualFound)
  have compiledChild := accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_sites_functions ordinary
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
    have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.calls_syntax_of path tree
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
  let result := CanonicalRootAt.of_sites_compiled ordinary
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


include prepared aligned diagnostic receiver wellFormed ordinary metadata complete in
/-- Original Source typing and the actual accepted action determine this root.
All lexical context changes come from the compiler collector's binder fields. -/
theorem of_accepted_sites
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel invocation.source scope id header.reasonAt = .ok lowered) :
    ∃ root : CanonicalRootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  have sameSource := (stages).source selected
  obtain ⟨predecessor, ⟨root⟩⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.policy_receipt
    prepared aligned (by simpa only [sameSource] using accepted)
  exact of_policy_sites prepared aligned diagnostic receiver wellFormed ordinary metadata rows complete actual selected
    fields declarations tree found typed root (by simpa only [sameSource] using root.selected.accepted)

end Sites

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
  exact of_policy_sites prepared aligned diagnostic receiver wellFormed
    (fun _ supported => supported.ordinary compiled.indexed.base.plan) metadata rows complete actual
    selected fields declarations tree found typed root accepted

include prepared aligned diagnostic receiver wellFormed metadata complete in
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
  exact of_accepted_sites prepared aligned diagnostic receiver wellFormed
    (fun _ supported => supported.ordinary compiled.indexed.base.plan) metadata rows complete actual
    selected fields declarations tree found typed accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalScopedRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceTerminalSupport
/-! Actual named compiler recipes authenticate the complete caller and callee
 dictionaries before the common static root enters the shared numeric family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceTerminalSupport
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (StepPolicyFor GeneralSyntax Certificate)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport (policy_receipt SidecarAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)

private theorem original_unique {original actual : TypedSource}
    (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView original actual)
    (unique : NodeOccurrencesUnique actual) : NodeOccurrencesUnique original := by
  rcases view with same | ⟨active, same⟩
  · exact same ▸ unique
  · rw [same] at unique
    change ((original.applySubstitution active).nodes.map Node.occurrenceId).Nodup at unique
    change (original.nodes.map Node.occurrenceId).Nodup
    simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique

section Sites
variable {directSites : DeclarationInstantiation → Prop}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source directSites)
  (tree : GeneralSyntax header.function.source terminal.expression directSites)
  {stages : Staging.Recursive.Registry}

variable {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include metadata tree in
/-- Every reached indirect call uses the same root policy and real sidecar.
The original parent typing supplies the callee occurrence and raw types. -/
theorem calls_ready_sites {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    {invocation : Staging.Recursive.Scope}
    (sameSource : invocation.source = header.function.source)
    (authority : SidecarAt terminal invocation)
    {type : TypeSystem.Ty}
    (typed : ExpressionHasType invocation.source header.context terminal.expression type)
    (certificate : Certificate root.selected.policy root.selected.lowerBody
      (context compiled.indexed terminal.prepared.named) compiled.indexed.fuel
      (.initial compiled.compatible.checked) invocation.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation) certificate := by
  intro callFuel callScope id callee ids callMetadata lowered compiler path
  have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.calls_syntax_of path
    (by simpa only [sameSource] using tree)
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.read_policy
    root.compilerPolicy metadata (by simpa only [sameSource] using syntaxTree)
  have readPolicy := profile
  have childRead : root.selected.policy.readExpression invocation.source id =
      SourceCoreCompatibleDataExpressions.readExpression
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked invocation.source id := by
    simpa only [sameSource, SourceCoreCompatibleValues.Context.initial] using readPolicy
  have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent compiler childRead
  obtain ⟨prepared⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.prepared
    compiler childRead [] root.callables
  have unique : NodeOccurrencesUnique invocation.source := sameSource ▸ header.unique
  have parentTyped := CallableIndexedOwnedPreparedStagedRecursiveCallerRawTyping.parent_typed
    compiler unique typed path
  obtain ⟨parameter, result, types, calleeTyped, _⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler parent unique parentTyped
  obtain ⟨node, contains, _⟩ := calleeTyped.stored_type
  exact ⟨{
    prepared := prepared
    sidecar := authority.sidecar
    caller := by rw [prepared.caller]; exact authority.issued
    view := by simpa only [sameSource] using authority.view
    guardFrame := authority.guards
    originalUnique := original_unique authority.view header.unique
    sourceParent := parent
    calleeNode := node
    calleeFound := lookupExpression?_complete unique contains }⟩

include wellFormed metadata tree rows complete in
/-- Each reached declaration obtains evidence at this exact selected caller
frame, from the same authentic compiler action as the static certificate. -/
theorem direct_ready {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    {child : Staging.Recursive.Scope}
    (sameSource : child.source = header.function.source)
    (selected : stages.Closure header.function child)
    (certificate : Certificate root.selected.policy root.selected.lowerBody
      (context compiled.indexed terminal.prepared.named) compiled.indexed.fuel
      (.initial compiled.compatible.checked) child.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    ∀ {callFuel callScope id callee ids instantiation lowered}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel (context compiled.indexed terminal.prepared.named)
        (.initial compiled.compatible.checked) child.source callScope id callee ids instantiation header.reasonAt lowered),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) header.context child.evidence) := by
  intro callFuel callScope id callee ids instantiation lowered compiler path
  obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory compiler rows complete rfl rfl
  have originalTree : GeneralSyntax child.source terminal.expression directSites := by
    simpa only [sameSource] using tree
  have childMetadata : MetadataFor compiled.indexed terminal.prepared.named child.source directSites := by
    simpa only [sameSource] using metadata
  have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path originalTree
  rcases CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.accepted_direct_action
    root.compilerPolicy childMetadata actualTree compiler.metadata.found compiler.form compiler.accepted with bypass | authentic
  · obtain ⟨requirements, assumptions⟩ :=
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct
        compiler.metadata.found compiler.form bypass
    have special := fun callback budget =>
      (CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.direct_hook root.compilerPolicy
        childMetadata actualTree compiler.metadata.found compiler.form callback budget callScope header.reasonAt).trans
        (CallableCallEvidenceCertificates.direct_bypass compiler.metadata.found compiler.form requirements
          compiler.metadata.coercions assumptions)
    have ordinary := compiler.ordinary special
      (CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.read_policy root.compilerPolicy childMetadata actualTree)
    exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
      compiler port ordinary requirements header.context child.evidence⟩⟩
  · obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
      compiler.metadata.found compiler.form authentic
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at actual
    let caller := CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames.of_selected terminal selected wellFormed
    exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence
      compiler port actual caller.prepared caller.signatures caller.ledger caller.assumptions caller.unique caller.dictionary⟩⟩

include diagnostic receiver wellFormed supported metadata tree rows complete in
/-- The Source frame and actual selected child derive all runtime-independent
conditions. No native argument or source heap representation is assumed. -/
def at_scope_sites {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : stages.Closure header.function child)
    (authority : SidecarAt terminal child) :
    { support : CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.CanonicalRootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  have sourceEq := stages.source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ header.unique
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables supported metadata (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt
  have available : (header.function.source.lookupExpression? terminal.expression).isSome := by
    obtain ⟨node, found, _⟩ := CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child
      terminal.receipt selected wellFormed
    exact Option.isSome_of_eq_some found
  let node := (header.function.source.lookupExpression? terminal.expression).get available
  have found : header.function.source.lookupExpression? terminal.expression = some node :=
    Option.eq_some_of_isSome available
  have properties : node.type = header.function.resultType ∧
      ExpressionHasType header.function.source header.context terminal.expression node.type := by
    obtain ⟨original, originalFound, rawType, typed⟩ :=
      CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
    have same := Option.some.inj (originalFound.symm.trans found)
    exact same ▸ ⟨rawType, typed⟩
  have rawType := properties.1
  have typed := properties.2
  have childFound : child.source.lookupExpression? terminal.expression = some node := by
    simpa only [sourceEq] using found
  have childTyped : ExpressionHasType child.source header.context terminal.expression node.type := by
    simpa only [sourceEq] using typed
  have childProfile : StepPolicyFor root.selected.policy (context compiled.indexed terminal.prepared.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt directSites := by
    simpa only [sourceEq] using profile
  have childDeclarations : CompatibleExpressionReads.ScopeDeclarations child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.context := by
    simpa only [sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using declarations
  have coercions : ∀ id actualNode, GeneralSyntax child.source id directSites →
      child.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sourceEq] using syntaxTree)
      actualNode (by simpa only [sourceEq] using actualFound)
  have childTree : GeneralSyntax child.source terminal.expression directSites := by simpa only [sourceEq] using tree
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (fuel + 1) (context compiled.indexed terminal.prepared.named) child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt = .ok terminal.receipt.child := by
    simpa only [sourceEq] using root.selected.accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique childDeclarations childProfile coercions childTree childFound childTyped accepted
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := child) certificate :=
    calls_ready_sites terminal metadata tree root sourceEq authority childTyped certificate
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.context child.source := by
    rw [sourceEq]
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
        header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  let support := CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.CanonicalRootAt.of_steps_compiled
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique childDeclarations childProfile coercions childTree childFound childTyped accepted ready rawType
    (header.valid.ledger.trans terminal.aligned.solved)
    (RecursiveNamedInitialContextValidity.runtime header.frame header.extended wellFormed)
    wellFormed runtime
    (by rw [stages.evidence selected]; exact RecursiveNamedInitialContextValidity.covers header.frame header.extended)
    (by rw [root.callables]; rfl)
    (fun _ _ _ receipt location =>
      CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized terminal.prepared diagnostic
        terminal.aligned receiver (by simpa only [sourceEq] using receipt) location) rows
    (direct_ready terminal wellFormed metadata tree rows complete root sourceEq selected certificate)
    (CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.named_ready
      terminal.prepared diagnostic terminal.aligned sourceEq certificate)
  exact ⟨support, rfl, rfl, rfl⟩

include diagnostic receiver wellFormed supported metadata tree rows complete zero in
/-- Genuine root acceptance produces the finite certificate at every actual
selected scope. The returned support feeds the existing public body family. -/
theorem of_terminal
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    (scopes : ∀ child, stages.Closure header.function child → SidecarAt terminal child) :
    Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys := keys) stages faults header terminal) := by
  obtain ⟨fuel, root⟩ := policy_receipt terminal
  obtain ⟨root⟩ := root
  refine ⟨{ point := point, zero := zero, roots := ?_ }⟩
  intro child selected
  exact at_scope_sites terminal diagnostic receiver wellFormed supported metadata tree rows complete root child selected (scopes child selected)

include diagnostic receiver wellFormed supported metadata tree rows complete zero in
/-- The actual named hook supplies its canonical sidecar. Genuine Source
origins and program typing identify every selected guard frame, without
excluding lambdas or other specializations of the same declaration. -/
theorem of_actual
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable)
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys := keys)
      (RecursiveNamedPreparedStageScopes.registry actual) faults header terminal) := by
  obtain ⟨sidecar, issued⟩ := CallableIndexedActualNamedSourceReceipts.hook_sidecar compiled header.hook
  have sourceReceipt := (CallableIndexedActualNamedSourceReceipts.header_source compiled header).1
  have canonicalSource : header.function.source = sidecar.source := by
    simpa only [EmptySourceSubstitution.source] using sourceReceipt.source issued
  obtain ⟨request, signature, generic, signatureMember, _genericMember, _requested, accepted⟩ :=
    terminal.prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have body := RecursiveNamedSpecializationBodyFacts.body accepted
  have sourceOwner : header.function.source.owner = signature.id := by
    rw [header.agreement.source, terminal.aligned.named, terminal.prepared.same]
    exact (congrArg TypedSource.owner body).trans (identities.2.1.trans identities.1.symm)
  apply of_terminal terminal diagnostic receiver wellFormed supported metadata tree rows complete zero point
  intro child selected
  refine { sidecar := sidecar, issued := ?_, view := .inl canonicalSource, guards := ?_ }
  · simpa only [terminal.aligned.named] using issued
  · exact RecursiveNamedPreparedScopeCoherence.selected_frame actual
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed
      signatureMember sourceOwner issued sourceReceipt selected

end Sites

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceTerminalSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceScopedRoots
/-! Evidence-bearing declaration calls receive canonical roots at each actual
lexical context. The prepared caller retains its complete requirement ledger
and dictionary through local allocation and control flow. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceScopedRoots
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax StepPolicyFor)
open CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (CanonicalRootAt)

section Sites
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
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
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed prepared.named header.function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry actual
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include prepared aligned diagnostic receiver wellFormed supported metadata complete in
/-- Original Source typing and the actual accepted action determine this root.
All lexical context changes come from the compiler collector's binder fields. -/
theorem of_policy_sites
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
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
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables supported metadata scope header.reasonAt
  have childProfile : StepPolicyFor root.selected.policy (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) invocation.source scope header.reasonAt directSites := by
    simpa only [sameSource] using profile
  have coercions : ∀ id actualNode, GeneralSyntax invocation.source id directSites →
      invocation.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sameSource] using syntaxTree)
      actualNode (by simpa only [sameSource] using actualFound)
  have compiledChild := accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_steps_functions
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
    have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.calls_syntax_of path tree
    have readPolicy := CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.read_policy
      root.compilerPolicy metadata (by simpa only [sameSource] using syntaxTree)
    have childRead : root.selected.policy.readExpression invocation.source callId =
        SourceCoreCompatibleDataExpressions.readExpression
          (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked invocation.source callId := by
      simpa only [sameSource, SourceCoreCompatibleValues.Context.initial] using readPolicy
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
  have directReady : ∀ {callFuel callScope callId callee ids instantiation callCode}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        root.selected.policy root.selected.lowerBody callFuel
        (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
        (.initial compiled.compatible.checked) invocation.source callScope callId callee ids
        instantiation header.reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler certificate →
      Nonempty (CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) context invocation.evidence) := by
    intro callFuel callScope callId callee ids instantiation callCode compiler path
    obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory compiler rows complete rfl rfl
    have actualTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.direct_calls_syntax_of path tree
    have childMetadata : MetadataFor compiled.indexed prepared.named invocation.source directSites := by
      simpa only [sameSource] using metadata
    rcases CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.accepted_direct_action
      root.compilerPolicy childMetadata actualTree compiler.metadata.found compiler.form compiler.accepted with bypass | authentic
    · obtain ⟨requirements, assumptions⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct
          compiler.metadata.found compiler.form bypass
      have special := fun callback budget =>
        (CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.direct_hook root.compilerPolicy
          childMetadata actualTree compiler.metadata.found compiler.form callback budget callScope header.reasonAt).trans
          (CallableCallEvidenceCertificates.direct_bypass compiler.metadata.found compiler.form requirements
            compiler.metadata.coercions assumptions)
      have ordinary := compiler.ordinary special
        (CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.read_policy root.compilerPolicy childMetadata actualTree)
      exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
        compiler port ordinary requirements context invocation.evidence⟩⟩
    · obtain ⟨action⟩ := CallableCoercionExpressionCertificates.direct_of_accepted
        compiler.metadata.found compiler.form authentic
      rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at action
      let caller := CallableIndexedOwnedPreparedStagedNamedEvidenceScopedCallerFrames.of_selected
        prepared aligned selected fields wellFormed
      exact ⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.authenticated_evidence
        compiler port action caller.prepared caller.signatures caller.ledger caller.assumptions caller.unique caller.dictionary⟩⟩
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source := by
    rw [sameSource]
    obtain ⟨_, sourceTyped⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
        header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact sourceTyped.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact (original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)).transport fields
  let result := CanonicalRootAt.of_steps_compiled
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
    rows directReady
    (CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.named_ready
      prepared diagnostic aligned sameSource certificate)
  exact ⟨result, rfl⟩


include prepared aligned diagnostic receiver wellFormed supported metadata complete in
/-- Original Source typing and the actual accepted action determine this root.
All lexical context changes come from the compiler collector's binder fields. -/
theorem of_accepted_sites
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function invocation)
    (fields : Dynamic.RuntimeContextFields header.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source scope context)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax invocation.source id directSites)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel invocation.source scope id header.reasonAt = .ok lowered) :
    ∃ root : CanonicalRootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      context invocation scope id lowered faults, root.compilation.administrativePrefix = 1 := by
  have sameSource := (stages).source selected
  obtain ⟨predecessor, ⟨root⟩⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.policy_receipt
    prepared aligned (by simpa only [sameSource] using accepted)
  exact of_policy_sites prepared aligned diagnostic receiver wellFormed supported metadata rows complete actual selected
    fields declarations tree found typed root (by simpa only [sameSource] using root.selected.accepted)

end Sites

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceScopedRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
/-! Actual named compiler packets select terminal, lexical or branching static support.
All alternatives supply the same body ports from strict expression children;
no execution law belongs to the static support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedAdmittedStagedExpressionBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

def Support
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (stages : Staging.Recursive.Registry) (body : Body header)
    (semanticFaults : FunctionCalls.FaultRep) : Type :=
  match body.compilation with
  | .terminal expression receipt certificate certifies =>
      CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers keys bodyRegistry header stages
        ⟨body.row, body.prepared, body.instantiation, body.aligned, body.layouts,
          expression, receipt, certificate, certifies⟩ semanticFaults
  | .lexical receipt =>
      CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Support
        headers keys bodyRegistry header stages receipt semanticFaults
  | .canonicalBranching receipt =>
      CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.NamedSupport
        headers keys bodyRegistry header stages receipt semanticFaults
  | .branching receipt =>
      CallableIndexedOwnedPreparedStagedNamedBranchingSupport.Support
        headers keys bodyRegistry header stages receipt semanticFaults

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {stages : Staging.Recursive.Registry} {body : Body header}
  (static : Support headers keys bodyRegistry header stages body semanticFaults)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {receiving : SourceCoreRawMetadata.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {invocation : Staging.Recursive.Scope} (selected : stages.Closure header.function invocation)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled receiving
    (fun reason token => faults (.semantic reason) token))

include static wellFormed selected semantic assignmentInterpretation in
theorem Support.preserves
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    {budget : Nat}
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      PreservesAt poolBridge context model stages child (Point scope expression lowered) faults size)
    (canonicalChildren : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages invocation faults budget := by
  cases body with
  | mk row prepared instantiation aligned layouts compilation =>
    cases compilation with
    | terminal expression receipt certificate certifies =>
      apply CallableIndexedOwnedPreparedStagedTerminalNamedBodyPorts.preserves
        selected wellFormed receipt certifies budget
      cases static with
      | recursive support =>
        apply CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow.pool
        intro size within scope id lowered point
        have same := support.point
        change certificate = _ at same
        rw [same] at point
        intro node
        exact children size within (support.roots invocation selected).val point (node := node)
      | formation support =>
        exact CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.preserves
          (profile := profile) (faults := faults) support selected budget
      | canonical support =>
        exact CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport.preserves
          support selected canonicalChildren
    | lexical receipt =>
      exact CallableIndexedOwnedPreparedStagedNamedLexicalSupport.preserves
        static aligned.globals profile selected layouts children
    | branching receipt =>
      exact CallableIndexedOwnedPreparedStagedNamedBranchingSupport.preserves (semantic := semantic)
        (assignmentInterpretation := assignmentInterpretation)
        static aligned.globals profile selected extension layouts children
    | canonicalBranching receipt =>
      exact CallableIndexedOwnedPreparedStagedCanonicalNamedBranchingSupport.preserves (semantic := semantic)
        (assignmentInterpretation := assignmentInterpretation)
        static aligned.globals profile selected extension layouts children canonicalChildren

include static wellFormed selected semantic assignmentInterpretation in
theorem Support.reflects
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
    {budget : Nat}
    (children : ∀ size, size < budget → ∀ {context child scope expression lowered},
      RootAt compiled context child scope expression lowered semanticFaults →
      ReflectsAt poolBridge context model stages child (Point scope expression lowered) faults size)
    (canonicalChildren : ∀ size, size < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages invocation faults budget := by
  cases body with
  | mk row prepared instantiation aligned layouts compilation =>
    cases compilation with
    | terminal expression receipt certificate certifies =>
      apply CallableIndexedOwnedPreparedStagedTerminalNamedBodyPorts.reflects
        selected wellFormed receipt certifies budget
      cases static with
      | recursive support =>
        apply CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow.pool
        intro size within scope id lowered point
        have same := support.point
        change certificate = _ at same
        rw [same] at point
        intro node
        exact children size within (support.roots invocation selected).val point (node := node)
      | formation support =>
        exact CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.reflects
          (profile := profile) (faults := faults) support selected budget
      | canonical support =>
        exact CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport.reflects
          support selected canonicalChildren
    | lexical receipt =>
      exact CallableIndexedOwnedPreparedStagedNamedLexicalSupport.reflects
        static aligned.globals profile selected layouts children
    | branching receipt =>
      exact CallableIndexedOwnedPreparedStagedNamedBranchingSupport.reflects (semantic := semantic)
        (assignmentInterpretation := assignmentInterpretation)
        static aligned.globals profile selected extension layouts children
    | canonicalBranching receipt =>
      exact CallableIndexedOwnedPreparedStagedCanonicalNamedBranchingSupport.reflects (semantic := semantic)
        (assignmentInterpretation := assignmentInterpretation)
        static aligned.globals profile selected extension layouts children canonicalChildren

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalOperatorRoots
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport
/-! Actual named compiler recipes authenticate the complete caller and callee
 dictionaries before the common static root enters the shared numeric family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (MethodStepPolicyFor GeneralSyntax Certificate)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport (policy_receipt SidecarAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)

private theorem original_unique {original actual : TypedSource}
    (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView original actual)
    (unique : NodeOccurrencesUnique actual) : NodeOccurrencesUnique original := by
  rcases view with same | ⟨active, same⟩
  · exact same ▸ unique
  · rw [same] at unique
    change ((original.applySubstitution active).nodes.map Node.occurrenceId).Nodup at unique
    change (original.nodes.map Node.occurrenceId).Nodup
    simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique

section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source directSites)
  (tree : GeneralSyntax header.function.source terminal.expression directSites)
  {stages : Staging.Recursive.Registry}

variable {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include metadata tree in
/-- Every reached indirect call uses the same root policy and real sidecar.
The original parent typing supplies the callee occurrence and raw types. -/
theorem calls_ready_sites {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    {invocation : Staging.Recursive.Scope}
    (sameSource : invocation.source = header.function.source)
    (authority : SidecarAt terminal invocation)
    {type : TypeSystem.Ty}
    (typed : ExpressionHasType invocation.source header.context terminal.expression type)
    (certificate : Certificate root.selected.policy root.selected.lowerBody
      (context compiled.indexed terminal.prepared.named) compiled.indexed.fuel
      (.initial compiled.compatible.checked) invocation.source header.context header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation) certificate := by
  intro callFuel callScope id callee ids callMetadata lowered compiler path
  have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.calls_syntax_of path
    (by simpa only [sameSource] using tree)
  have readPolicy := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy
    root.compilerPolicy metadata (by simpa only [sameSource] using syntaxTree)
  have childRead : root.selected.policy.readExpression invocation.source id =
      SourceCoreCompatibleDataExpressions.readExpression
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked invocation.source id := by
    simpa only [sameSource, SourceCoreCompatibleValues.Context.initial] using readPolicy
  have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent compiler childRead
  obtain ⟨prepared⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.prepared
    compiler childRead [] root.callables
  have unique : NodeOccurrencesUnique invocation.source := sameSource ▸ header.unique
  have parentTyped := CallableIndexedOwnedPreparedStagedRecursiveCallerRawTyping.parent_typed
    compiler unique typed path
  obtain ⟨parameter, result, types, calleeTyped, _⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler parent unique parentTyped
  obtain ⟨node, contains, _⟩ := calleeTyped.stored_type
  exact ⟨{
    prepared := prepared
    sidecar := authority.sidecar
    caller := by rw [prepared.caller]; exact authority.issued
    view := by simpa only [sameSource] using authority.view
    guardFrame := authority.guards
    originalUnique := original_unique authority.view header.unique
    sourceParent := parent
    calleeNode := node
    calleeFound := lookupExpression?_complete unique contains }⟩


include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
/-- The Source frame and actual selected child derive all runtime-independent
conditions. No native argument or source heap representation is assumed. -/
def at_scope_sites_with_catalog {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (authority : SidecarAt terminal child) :
    { support : CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry actualStages).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ header.unique
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.recipe_policy_for
    root.compilerPolicy root.selected.callables supported metadata (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt
  have available : (header.function.source.lookupExpression? terminal.expression).isSome := by
    obtain ⟨node, found, _⟩ := CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child
      terminal.receipt selected wellFormed
    exact Option.isSome_of_eq_some found
  let node := (header.function.source.lookupExpression? terminal.expression).get available
  have found : header.function.source.lookupExpression? terminal.expression = some node :=
    Option.eq_some_of_isSome available
  have properties : node.type = header.function.resultType ∧
      ExpressionHasType header.function.source header.context terminal.expression node.type := by
    obtain ⟨original, originalFound, rawType, typed⟩ :=
      CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
    have same := Option.some.inj (originalFound.symm.trans found)
    exact same ▸ ⟨rawType, typed⟩
  have rawType := properties.1
  have typed := properties.2
  have childFound : child.source.lookupExpression? terminal.expression = some node := by
    simpa only [sourceEq] using found
  have childTyped : ExpressionHasType child.source header.context terminal.expression node.type := by
    simpa only [sourceEq] using typed
  have childProfile : MethodStepPolicyFor root.selected.policy (context compiled.indexed terminal.prepared.named)
      compiled.indexed.fuel (.initial compiled.compatible.checked) child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.reasonAt directSites := by
    simpa only [sourceEq] using profile
  have childDeclarations : CompatibleExpressionReads.ScopeDeclarations child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.context := by
    simpa only [sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using declarations
  have coercions : ∀ id actualNode, GeneralSyntax child.source id directSites →
      child.source.lookupExpression? id = some actualNode → actualNode.coercions = [] := by
    intro id actualNode syntaxTree actualFound
    exact metadata.coercions id (by simpa only [sourceEq] using syntaxTree)
      actualNode (by simpa only [sourceEq] using actualFound)
  have childTree : GeneralSyntax child.source terminal.expression directSites := by simpa only [sourceEq] using tree
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (fuel + 1) (context compiled.indexed terminal.prepared.named) child.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt = .ok terminal.receipt.child := by
    simpa only [sourceEq] using root.selected.accepted
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_method_steps_functions
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    unique childDeclarations childProfile coercions childTree childFound childTyped accepted
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.context child.source := by
    rw [sourceEq]
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
        header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  let support : CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt compiled
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages) header.context child
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults :=
    CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt.ofRoot {
      compilerFuel := fuel + 1
      accepted := accepted
      certificate := certificate
      node := node
      found := childFound
      rawResult := rawType
      typed := childTyped
      sameLedger := header.valid.ledger.trans terminal.aligned.solved
      runtimeLedger := RecursiveNamedInitialContextValidity.runtime header.frame header.extended wellFormed
      unique := unique
      wellFormed := wellFormed
      runtime := runtime
      covers := by
        rw [(RecursiveNamedPreparedStageScopes.registry actualStages).evidence selected]
        exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
      actualFunctionType := by rw [root.callables]; rfl
      uninitialized := fun _ _ _ read _ location =>
        CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized terminal.prepared diagnostic
          terminal.aligned receiver (by simpa only [sourceEq] using read) location
      callsReady := calls_ready_sites terminal metadata tree root sourceEq authority childTyped certificate
      directReady := CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport.direct_ready terminal wellFormed metadata tree rows covered root sourceEq selected certificate
      indexReady := CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.named_ready
        terminal.prepared diagnostic terminal.aligned sourceEq certificate
      methodReady := CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport.method_ready_with_catalog terminal wellFormed metadata tree checked catalog methods actualStages root sourceEq selected certificate }
  exact ⟨support, rfl, rfl, rfl⟩

include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
/-- Original named compilation, real caller evidence and the actual method cache
produce the physical body support. Every execution premise comes later. -/
theorem of_actual_with_catalog
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  obtain ⟨fuel, ⟨root⟩⟩ := policy_receipt terminal
  obtain ⟨sidecar, issued⟩ := CallableIndexedActualNamedSourceReceipts.hook_sidecar compiled header.hook
  have sourceReceipt := (CallableIndexedActualNamedSourceReceipts.header_source compiled header).1
  have canonicalSource : header.function.source = sidecar.source := by
    simpa only [EmptySourceSubstitution.source] using sourceReceipt.source issued
  obtain ⟨request, signature, generic, signatureMember, _with_catalogMember, _requested, accepted⟩ :=
    terminal.prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have body := RecursiveNamedSpecializationBodyFacts.body accepted
  have sourceOwner : header.function.source.owner = signature.id := by
    rw [header.agreement.source, terminal.aligned.named, terminal.prepared.same]
    exact (congrArg TypedSource.owner body).trans (identities.2.1.trans identities.1.symm)
  refine ⟨⟨point, ?_⟩⟩
  intro child selected
  let authority : SidecarAt terminal child := {
    sidecar := sidecar
    issued := by simpa only [terminal.aligned.named] using issued
    view := .inl canonicalSource
    guards := RecursiveNamedPreparedScopeCoherence.selected_frame actualStages
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) wellFormed
      signatureMember sourceOwner issued sourceReceipt selected }
  exact at_scope_sites_with_catalog terminal diagnostic receiver wellFormed supported metadata tree
    rows covered checked catalog methods actualStages root child selected authority

end Generic


section GenericWrappers
variable {directSites : DeclarationInstantiation → Prop}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source directSites)
  (tree : GeneralSyntax header.function.source terminal.expression directSites)
  {stages : Staging.Recursive.Registry}

variable {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
def at_scope_sites_generic {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (authority : SidecarAt terminal child) :
    { support : CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  exact at_scope_sites_with_catalog terminal diagnostic receiver wellFormed supported metadata tree rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.generic methods) actualStages root child selected authority

include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
theorem of_actual_generic
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  exact of_actual_with_catalog terminal diagnostic receiver wellFormed supported metadata tree rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.generic methods) actualStages point

end GenericWrappers

section EvidenceWrappers
variable {directSites : DeclarationInstantiation → Prop}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source directSites)
  (tree : GeneralSyntax header.function.source terminal.expression directSites)
  {stages : Staging.Recursive.Registry}

variable {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog compiled)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
def at_scope_sites_with_evidence {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (authority : SidecarAt terminal child) :
    { support : CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  exact at_scope_sites_with_catalog terminal diagnostic receiver wellFormed supported metadata tree rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.evidence methods) actualStages root child selected authority

include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
theorem of_actual_with_evidence
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  exact of_actual_with_catalog terminal diagnostic receiver wellFormed supported metadata tree rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.evidence methods) actualStages point

end EvidenceWrappers

section Legacy
variable {directSites : DeclarationInstantiation → Prop}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
  (metadata : MetadataFor compiled.indexed terminal.prepared.named header.function.source directSites)
  (tree : GeneralSyntax header.function.source terminal.expression directSites)
  {stages : Staging.Recursive.Registry}

variable {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation = .ok signature.key →
    compiled.indexed.base.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
def at_scope_sites {fuel : Nat}
    (root : RootPolicyReceipt (compiled := compiled) terminal.prepared.named terminal.prepared.diagnostics
      terminal.prepared.code terminal.prepared.compilation fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression header.reasonAt terminal.receipt.child)
    (child : Staging.Recursive.Scope) (selected : (RecursiveNamedPreparedStageScopes.registry actualStages).Closure header.function child)
    (authority : SidecarAt terminal child) :
    { support : CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport.RootAt compiled (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (RecursiveNamedPreparedStageScopes.registry actualStages)
      header.context child (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child faults //
      support.rawType = header.function.resultType ∧ support.reasonAt = header.reasonAt ∧
      support.compilation.administrativePrefix = 1 } := by
  exact at_scope_sites_generic terminal diagnostic receiver wellFormed supported metadata tree rows covered checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) actualStages root child selected authority

include diagnostic receiver wellFormed supported metadata tree rows covered checked catalog methods actualStages in
theorem of_actual
    (point : terminal.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (stages := RecursiveNamedPreparedStageScopes.registry actualStages) (semanticFaults := faults) header terminal) := by
  exact of_actual_generic terminal diagnostic receiver wellFormed supported metadata tree rows covered checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) actualStages point

end Legacy

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport
end
