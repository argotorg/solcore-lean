import Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogTransport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalScopedSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySamePolicyLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors

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
