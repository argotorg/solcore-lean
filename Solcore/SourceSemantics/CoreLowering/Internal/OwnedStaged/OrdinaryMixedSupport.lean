import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.LambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinaryMethodRoots
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewMatchRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.EligibleSelected
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedLambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicNestedInputs
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinarySequenceCallers

/-!
# Staged bounds: ordinary mixed support

Canonical and mixed scoped support of ordinary rows, and public bounds of returned functions.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalScopedSupport
/-! General expressions at actual ordinary lexical scopes retain the same
Code compiler and genuine canonical-root authorities. Existing branching
collector/flow trees handle local allocation, assignment and finite control. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalScopedSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability CallableLambdaViewEdits
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (CanonicalRoot)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor)
open CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private theorem accepted_child
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative)
    {stages : Staging.Recursive.Registry}
    (choice : CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts.Choice code (stages := stages))
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : choice.packet.policy.lowerExpression fuel code.view current id choice.packet.reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody (min fuel code.fuel)
      code.compilation code.view current id code.reasonAt = .ok lowered := by
  have callback := choice.callback
  have reason := choice.reason
  rw [callback, reason] at accepted
  exact accepted


variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (original : NativeMetadataFor compiled.indexed support.caller.named function.source)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

variable (choice : Choice code
  («stages» := RecursiveNamedPreparedStageScopes.registry stagePrepared))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include provenance receiver wellFormed original rows complete signatureMember sourceOwner in
/-- Every original expression is issued at its real lexical context, including the
RHS and later reads after a genuine assignment or local allocation. -/
def support_general
    (choiceIssued : choice.Issued code support.caller.named)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (GeneralSyntax function.source)
      support.body.context (.statements true function.body) function.resultType) :
    CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.CanonicalBranchingSupport
      headers code support.body.toContext stages choice.packet faults := by
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
    support.body.frame support.body.extended).1
  have sourceSignatures : support.body.context.signatures = compiled.compatible.checked.signatures :=
    (runtime.signatures.trans
      (RecursiveNamedSelectedExpressionFactory.header_program_signatures
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) support.caller).symm).trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := support.caller))
  have ownership : LocalIdentityOwnership function.source := by
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate support.caller wellFormed
    rw [support.source]
    change LocalIdentityOwnership support.caller.named.specialized.function.typedBody
    rw [← support.caller.agreement.source, support.caller.frame.source]
    exact certificate.local_identity_ownership
  refine ⟨support.body.frame, support.body.projection, compiled.indexed.fuel, ?_,
    choice.invalidProjection, choice.missingDefault,
    choiceIssued.assignmentAuthority code support.caller.selected support.source support.body.unique, ?_⟩
  · rw [support.compilation]; rfl
  intro child selected
  have actual := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport.collected
    code support.body.toContext support.body.frame choice provenance.body_view provenance.scope_declarations
    sourceSignatures (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    (CallableIndexedOwnedPublicSignatureCatalog.well_formed compiled wellFormed)
    support.body.valid.ledger support.body.projection
    (fun origin rawProfile => choiceIssued.operands code support.caller.selected support.source receiver origin rawProfile)
    (fun origin rawWord => choiceIssued.unary code support.caller.selected support.source receiver origin rawWord) syntaxTree
    (certificates := fun context scope id lowered => Nonempty (Σ rawType,
      CanonicalRoot compiled code.policy code.lowerBody code.compilation compiled.indexed.fuel
        context child code.reasonAt scope id lowered rawType faults headers))
    (fun context fields current fuel id node lowered declarations tree reached found typed accepted _nativeType _native => by
      exact CallableIndexedOwnedPreparedStagedOrdinaryCanonicalScopedRoots.of_child
        stagePrepared code support provenance receiver wellFormed original rows complete signatureMember sourceOwner
        selected fields declarations tree reached found typed (accepted_child code choice accepted))
  have weakened := CallableLambdaViewMatchRuntimeCertificates.transport_with
    (LocalView.refl function.source) (by intro id member; cases member)
    support.body.unique (fun _ _ _ => True.intro)
    (fun _ _ _ _ _ value => value) actual.tree
    (fun id member => Reaches.root (List.mem_map.mpr ⟨id, member, rfl⟩))
  rw [(stages).source selected]
  refine ⟨weakened, ?_⟩
  intro currentRegistry
  obtain ⟨tree, sites⟩ := PreparedBranchingCatalogTransport.weaken support.body.unique
    (actual.sites currentRegistry)
  exact sites

include provenance receiver wellFormed original rows complete signatureMember sourceOwner in
omit choice in
/-- The real lowerer and typed original syntax produce the same-model packet
and all static support together, without selecting a proof as runtime data. -/
theorem of_actual
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (GeneralSyntax function.source)
      support.body.context (.statements true function.body) function.resultType)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Packet code stages,
      CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Support
        headers code support.body.toContext stages packet faults) := by
  obtain ⟨choice, choiceIssued⟩ := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts.choose_issued
    code support.caller.named provenance.issued_recipe support.compilation shape child selected
  exact ⟨⟨.canonicalBranching choice.packet,
    support_general stagePrepared code support provenance receiver wellFormed original rows complete
      signatureMember sourceOwner choice choiceIssued syntaxTree⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalScopedSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMixedScopedSupport
/-! Ordinary body collectors retain canonical calls and inner formation at
one actual Code, original Source and reached lexical context. The formation
uses the original policy and the full caller packet supplied at invocation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMixedScopedSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability CallableLambdaViewEdits
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (CanonicalRootAt)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor)
open CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors (ReturnLambda)
open CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport (Certificate)

inductive Syntax {compiled : SourceCoreUnifiedCompilation.Compiled}
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) : ExpressionId → Prop where
  | general {id} (tree : GeneralSyntax caller.function.source id) : Syntax caller id
  | formation {id} (shape : ReturnLambda caller id) : Syntax caller id

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (prefixContext : administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (metadata : NativeMetadataFor compiled.indexed support.caller.named function.source)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include provenance prefixContext receiver wellFormed metadata rows complete signatureMember sourceOwner profile in
private theorem child_certificate
    {child : Staging.Recursive.Scope} (selected : (stages).Closure function child)
    {context : SourceSemantics.Context} (fields : Dynamic.RuntimeContextFields support.body.context context)
    {current : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    (tree : Syntax support.caller id)
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation code.view current id code.reasonAt = .ok lowered)
    {nativeType : Ty}
    (native : HasType (SourceCoreLocalCell.coreContext current ++ administrative)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    Certificate headers support.caller bodyRegistry faults context child current id lowered := by
  have original : function.source = support.caller.function.source :=
    support.source.trans support.caller.agreement.source.symm
  cases tree with
  | general syntaxTree =>
    obtain ⟨rawType, root⟩ := CallableIndexedOwnedPreparedStagedOrdinaryCanonicalScopedRoots.of_child
      stagePrepared code support provenance receiver wellFormed metadata rows complete signatureMember sourceOwner
      selected fields declarations (by simpa only [original] using syntaxTree) reached found typed accepted
    exact .canonical (CanonicalRootAt.ofRoot root) (by
      change code.compilation.administrativePrefix = 1
      rw [support.compilation]
      rfl)
  | formation shape =>
    have sameNode : node = shape.node := Option.some.inj
      (found.symm.trans (by simpa only [original] using shape.found))
    obtain ⟨formation⟩ := CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaFormation.of_expression
      code support provenance wellFormed profile selected
      (by simpa only [original] using shape.found) shape.form
      (by simpa only [original] using shape.owner) shape.requirements shape.coercions shape.ordinary
      (by simpa only [original] using shape.read)
      (by simpa only [original] using shape.returnFound) shape.returnForm shape.returnType
      fields declarations (sameNode ▸ typed) reached accepted (prefixContext ▸ native)
    have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context child.source := by
      rw [(stages).source selected]
      exact ((CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
        support.body.frame support.body.extended).1).transport fields
    have covers : child.evidence.Covers context := by
      rw [(stages).evidence selected]
      exact fields.covers support.body.valid.covers
    exact .legacy (.formation formation runtime covers)

include provenance prefixContext receiver wellFormed metadata rows complete signatureMember sourceOwner zero profile in
private def support_mixed
    (choice : Choice code («stages» := stages))
    (choiceIssued : choice.Issued code support.caller.named)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (Syntax support.caller)
      support.body.context (.statements true function.body) function.resultType) :
    CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.NestedBranchingSupport
      headers keys support stages choice.packet := by
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters support.body.frame support.body.extended).1
  have sourceSignatures : support.body.context.signatures = compiled.compatible.checked.signatures :=
    (runtime.signatures.trans
      (RecursiveNamedSelectedExpressionFactory.header_program_signatures
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) support.caller).symm).trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := support.caller))
  have ownership : LocalIdentityOwnership function.source := by
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate support.caller wellFormed
    rw [support.source]
    change LocalIdentityOwnership support.caller.named.specialized.function.typedBody
    rw [← support.caller.agreement.source, support.caller.frame.source]
    exact certificate.local_identity_ownership
  refine ⟨provenance.globals, complete, zero, wellFormed,
    choice.invalidProjection, choice.missingDefault,
    choiceIssued.assignmentAuthority code support.caller.selected support.source support.body.unique, ?_⟩
  intro child selected
  have actual := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport.collected
    code support.body.toContext support.body.frame choice provenance.body_view provenance.scope_declarations
    sourceSignatures (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    (CallableIndexedOwnedPublicSignatureCatalog.well_formed compiled wellFormed)
    support.body.valid.ledger support.body.projection
    (fun origin rawProfile => choiceIssued.operands code support.caller.selected support.source receiver origin rawProfile)
    (fun origin rawWord => choiceIssued.unary code support.caller.selected support.source receiver origin rawWord) syntaxTree
    (certificates := fun context => Certificate headers support.caller bodyRegistry faults context child)
    (fun context fields current fuel id node lowered declarations tree reached found typed accepted _nativeType native => by
      have accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody (min fuel code.fuel)
          code.compilation code.view current id code.reasonAt = .ok lowered := by
        rw [choice.callback, choice.reason] at accepted
        exact accepted
      exact child_certificate stagePrepared code support provenance prefixContext receiver wellFormed metadata
        rows complete signatureMember sourceOwner profile selected fields declarations tree reached found typed accepted native)
  have weakened := CallableLambdaViewMatchRuntimeCertificates.transport_with
    (LocalView.refl function.source) (by intro id member; cases member)
    support.body.unique (fun _ _ _ => True.intro)
    (fun _ _ _ _ _ value => value) actual.tree
    (fun id member => Reaches.root (List.mem_map.mpr ⟨id, member, rfl⟩))
  rw [(stages).source selected]
  refine ⟨weakened, ?_⟩
  intro currentRegistry
  obtain ⟨tree, sites⟩ := PreparedBranchingCatalogTransport.weaken support.body.unique
    (actual.sites currentRegistry)
  exact sites

include provenance prefixContext receiver wellFormed metadata rows complete signatureMember sourceOwner zero profile in
theorem of_actual
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (Syntax support.caller)
      support.body.context (.statements true function.body) function.resultType)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code stages,
      CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.NestedBranchingSupport headers keys support stages packet) := by
  obtain ⟨choice, choiceIssued⟩ := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts.choose_issued
    code support.caller.named provenance.issued_recipe support.compilation shape child selected
  exact ⟨⟨choice.packet, support_mixed stagePrepared code support provenance prefixContext receiver wellFormed metadata
    rows complete signatureMember sourceOwner zero profile choice choiceIssued syntaxTree⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMixedScopedSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReturnedFunctionPublicBounds
/-! An actual successful public call supplies the closure and the reached
owned state for the next public call. Captured environments, locations, heap
contents and stable histories are retained through export and reimport.
The returned handle may pass through real named/builtin issuance before the
next call. Inputs may repeat this handle inside data containers. Both calls
use the same receiving body model and metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReturnedFunctionPublicBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds (OrdinarySequenceFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (inputs : List (Input compiled)) (rows : Inventory inputs)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
      bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association (headers rows) (keys compiled) bodyRegistry semanticFaults
      mapping world function native bindings parameterCore resultCore), OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers rows → Body header)
  (namedSupport : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (keys compiled) bodyRegistry header (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      (namedTerminals header member) semanticFaults)
  {beforePlan : SourceCompilationPlan.Plan} {planFuel planBudget : Nat}
  (acceptedPlan : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
    compiled.sourceProgram beforePlan planFuel planBudget = .ok compiled.indexed.base.plan)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {recipe : SourceCoreIndexedSession.Recipe}
  (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {root : SourceCoreIndexedSession.Root compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {previousCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {previousCompletion : SourceCoreIndexedSession.Completion nativeArtifact}
  {previousFuel outputFuel : Nat} {previousGeneration : SourceCorePublicValues.ExportGeneration}
  {previousValue : Value} {returnedStore : Store}
  (previousSuccess : previousCheckpoint.SucceededResultAt previousFuel outputFuel
    previousGeneration previousValue returnedStore previousCompletion)
  {previousHeader : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (requested : previousCheckpoint.ResultTypeAt previousHeader.function.resultType)
  {handle : SourceCorePublicValues.Handle}
  (previousHandle : previousCompletion.value = .function handle)
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  (continued : previousCompletion.session.IssuanceChain nativeSession)
  {previousMap : LocationMap} {previousWorld : StoreTyping} {previousHeap : Dynamic.Heap}
  {previousStore : Store}
  (previousCaller : State (headers rows) (keys compiled)
    ⟨[], previousMap, previousWorld, previousHeap, previousStore,
      SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
  {previousCapture : CallableIndexedOwnedFunctionValues.NamedCapture (headers rows)
    (owner compiled).key previousHeader previousMap previousWorld}
  {previousPayloads : List Value} {previousOutcome : Staging.Recursive.Outcome}
  {before : Dynamic.Heap} {mapping : LocationMap} {returnedWorld : StoreTyping}
  (previousResult : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
    (registry := completion.result.context.registry) (payloads := previousPayloads)
    (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
    (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
      bodyRegistry semanticFaults profile)
    (owner compiled) previousCaller previousHeader previousCapture previousHeader.function.context
    previousOutcome before previousValue returnedStore mapping returnedWorld
    (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics))
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {options : SourceCoreExecution.RunOptions}
  {publicArguments : List SourceCorePublicValues.Value}
  {arguments : Dynamic.Value → List Dynamic.Value}
  {world : StoreTyping} {store : Store} {payloads : Environment}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe
    ((SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm ▸ root)
    world store payloads encodedValues)
  (inputReceipts : ∀ source, previousOutcome = .value source →
    RecursiveNamedPublicReturnedInputs.Inputs previousHeader.function.resultType (.function handle) source
      header.function.context (header.bindings.map (fun binding => binding.1.scheme.body))
      publicArguments (arguments source))
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  (supports : Dynamic.TypeContextSupports header.context context)

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include wellFormed prepared selected previousSuccess requested previousHandle continued previousResult started inputReceipts metadata in
/-- The actual previous result constructs every dynamic premise for the next
call. No initial caller, heap law, capture representation or source-value
admission is supplied independently of that result. -/
private theorem continued_arguments :
    ∃ source, previousOutcome = .value source ∧
      ∃ caller : State rootHeaders rootKeys
        ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      Relates previousCaller caller ∧
      CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
        rootFunctions mapping world before store ∧
      Dynamic.HeapWellTyped header.function.context before ∧
      CallableIndexedParameterMeaning.Arguments rootModel mapping world header.bindings (arguments source) payloads ∧
      Dynamic.ValuesHaveTypes header.function.context before (arguments source) header.types := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨payload, decoded, _encoded⟩ := previousSuccess.reimports
  obtain ⟨_sourceType, _nativeAt, imported⟩ :=
    previousSuccess.reimports_function_after requested decoded previousHandle continued
  obtain ⟨source, outcomeEq, represented, heaps, worldEq, caller, related, stable, heapTyped, sourceTyped⟩ :=
    RecursiveNamedPublicReturnedValues.returned_value previousResult decoded
  obtain ⟨currentWorld, currentStore⟩ :=
    RecursiveNamedPublicReturnedSessionInputs.StartAt.after_succeeded previousSuccess continued started
  subst returnedWorld
  subst world
  subst store
  have contexts := RecursiveNamedPublicReturnedValues.header_context_supports previousHeader header wellFormed
  obtain ⟨representedArguments, argumentsTyped⟩ :=
    RecursiveNamedPublicReturnedArgumentsReceiving.StartAt.returned_arguments_receiving
      started _ selected imported rfl represented (.refl _)
      (sourceTyped.transportContext contexts.1) (inputReceipts source outcomeEq) metadata wellFormed
  exact ⟨source, outcomeEq, caller, related, stable, heaps,
    heapTyped.transportContext contexts.1, representedArguments, argumentsTyped⟩

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  prepared selected previousSuccess requested previousHandle continued previousResult atCheckpoint started inputReceipts metadata sourceAt supports in
/-- Actual returned-state admission feeds the existing public endpoint. -/
theorem public_run_succeeded_reflects
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ source, previousOutcome = .value source ∧
      ∃ caller : State rootHeaders rootKeys
        ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      Relates previousCaller caller ∧
      ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
        (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        nativeCheckpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
          generation value finalStore actual ∧
        publicCompletion.value = actual.value ∧ publicCompletion.sourceType = actual.sourceType ∧
        publicCompletion.boundaryFuel = actual.boundaryFuel ∧ publicCompletion.session.IndexedAt actual.session ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
          (.global function) (arguments source) outcome after ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  obtain ⟨source, outcomeEq, caller, related, stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    continued_arguments (inputs := inputs) (rows := rows)
      (profile := profile) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (previousSuccess := previousSuccess) (requested := requested) (previousHandle := previousHandle)
      (continued := continued) (previousCaller := previousCaller) (previousResult := previousResult)
      (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  refine ⟨source, outcomeEq, caller, related, ?_⟩
  exact CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.public_run_succeeded_reflects
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := rootOwner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared) (started := started)
      publicStart atCheckpoint publicRun descriptor

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  prepared selected previousSuccess requested previousHandle continued previousResult atCheckpoint started inputReceipts metadata sourceAt supports in
/-- Actual returned-state admission feeds the existing public endpoint. -/
theorem public_run_failed_reflects
    {returned : SourceCoreExecution.Session publicArtifact} {reason : Word}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.failed reason returned)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ source, previousOutcome = .value source ∧
      ∃ caller : State rootHeaders rootKeys
        ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      Relates previousCaller caller ∧
      ∃ (actual : SourceCoreIndexedSession.Session nativeArtifact) (value : Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        nativeCheckpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
        returned.IndexedAt actual ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
          (.global function) (arguments source) outcome after ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  obtain ⟨source, outcomeEq, caller, related, stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    continued_arguments (inputs := inputs) (rows := rows)
      (profile := profile) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (previousSuccess := previousSuccess) (requested := requested) (previousHandle := previousHandle)
      (continued := continued) (previousCaller := previousCaller) (previousResult := previousResult)
      (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  refine ⟨source, outcomeEq, caller, related, ?_⟩
  exact CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.public_run_failed_reflects
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := rootOwner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared) (started := started)
      publicStart atCheckpoint publicRun descriptor

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  prepared selected previousSuccess requested previousHandle continued previousResult atCheckpoint started inputReceipts metadata sourceAt supports in
/-- Actual returned-state admission feeds the existing public endpoint. -/
theorem public_word_preserved
    {source : Dynamic.Value} (previousSource : previousOutcome = .value source)
    (outputWord : header.output = .word) (resultWord : header.function.resultType = .word)
    (outputBudget : Nat) (positive : 0 < outputBudget)
    {size : Nat} {word : Word} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) size invocation context before
      (.global function) (arguments source) (.value (.word word)) after) :
    ∃ caller : State rootHeaders rootKeys
        ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      Relates previousCaller caller ∧
      ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
        (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) (required : Nat),
        (∀ fuel, required ≤ fuel → ∀ outcome, publicCheckpoint.ResumeAt fuel outputBudget outcome →
          ∃ exported, outcome = .succeeded exported ∧ exported.value = .word word) ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture context (.value (.word word)) after
            (.inRight .word (.word word)) finalStore finalMap finalWorld rootFaults := by
  obtain ⟨actualSource, outcomeEq, caller, related, stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    continued_arguments (inputs := inputs) (rows := rows)
      (profile := profile) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (previousSuccess := previousSuccess) (requested := requested) (previousHandle := previousHandle)
      (continued := continued) (previousCaller := previousCaller) (previousResult := previousResult)
      (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  have same : actualSource = source := Staging.Recursive.Outcome.value.inj (outcomeEq.symm.trans previousSource)
  subst actualSource
  refine ⟨caller, related, ?_⟩
  exact CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.public_word_preserved
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := rootOwner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared) (started := started)
      atCheckpoint outputWord resultWord outputBudget positive trace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReturnedFunctionPublicBounds
end
