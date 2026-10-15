import Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogTransport
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionIssuer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewMatchRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport

/-! General expressions at actual ordinary lexical scopes retain the same
Code compiler and genuine canonical-root authorities. Existing branching
collector/flow trees handle local allocation, assignment and finite control. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability CallableLambdaViewEdits
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootStaticSupport (Root)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
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


section Generic
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
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
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (original : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

variable (choice : Choice code
  («stages» := RecursiveNamedPreparedStageScopes.registry stagePrepared))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics


include provenance receiver wellFormed supported original rows covered checked catalog methods signatureMember sourceOwner in
/-- Every original expression is issued at its real lexical context, including the
RHS and later reads after a genuine assignment or local allocation. -/
def support_general_with_catalog
    (choiceIssued : choice.Issued code support.caller.named)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType) :
    CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport.SelectedBody
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
      Root compiled headers stages code.policy code.lowerBody code.compilation compiled.indexed.fuel
        context child code.reasonAt scope id lowered rawType faults))
    (fun context fields current fuel id node lowered declarations tree reached found typed accepted _nativeType _native => by
      exact CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedRoots.of_child_with_catalog
        stagePrepared code support provenance receiver wellFormed supported original rows covered checked catalog methods signatureMember sourceOwner
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

include provenance receiver wellFormed supported original rows covered checked catalog methods signatureMember sourceOwner in
omit choice in
/-- The real lowerer and typed original syntax produce the same-model packet
and all static support together, without selecting a proof as runtime data. -/
theorem of_actual_with_catalog
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code stages,
      CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport.SelectedBody
        headers code support.body.toContext stages packet faults) := by
  obtain ⟨choice, choiceIssued⟩ := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts.choose_issued
    code support.caller.named provenance.issued_recipe support.compilation shape child selected
  exact ⟨⟨choice.packet,
    support_general_with_catalog stagePrepared code support provenance receiver wellFormed supported original rows covered checked catalog methods
      signatureMember sourceOwner choice choiceIssued syntaxTree⟩⟩

end Generic



section GenericWrappers
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
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
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (original : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

variable (choice : Choice code
  («stages» := RecursiveNamedPreparedStageScopes.registry stagePrepared))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics



include provenance receiver wellFormed supported original rows covered checked catalog methods signatureMember sourceOwner in
def support_general_generic
    (choiceIssued : choice.Issued code support.caller.named)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType) :
    CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport.SelectedBody
      headers code support.body.toContext stages choice.packet faults := by
  exact support_general_with_catalog stagePrepared code support provenance receiver wellFormed supported original rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.generic methods) signatureMember sourceOwner choice choiceIssued syntaxTree

include provenance receiver wellFormed supported original rows covered checked catalog methods signatureMember sourceOwner in
omit choice in
theorem of_actual_generic
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code stages,
      CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport.SelectedBody
        headers code support.body.toContext stages packet faults) := by
  exact of_actual_with_catalog stagePrepared code support provenance receiver wellFormed supported original rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.generic methods) signatureMember sourceOwner shape syntaxTree child selected

end GenericWrappers

section EvidenceWrappers
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
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
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (original : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog compiled)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

variable (choice : Choice code
  («stages» := RecursiveNamedPreparedStageScopes.registry stagePrepared))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics



include provenance receiver wellFormed supported original rows covered checked catalog methods signatureMember sourceOwner in
def support_general_with_evidence
    (choiceIssued : choice.Issued code support.caller.named)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType) :
    CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport.SelectedBody
      headers code support.body.toContext stages choice.packet faults := by
  exact support_general_with_catalog stagePrepared code support provenance receiver wellFormed supported original rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.evidence methods) signatureMember sourceOwner choice choiceIssued syntaxTree

include provenance receiver wellFormed supported original rows covered checked catalog methods signatureMember sourceOwner in
omit choice in
theorem of_actual_with_evidence
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code stages,
      CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport.SelectedBody
        headers code support.body.toContext stages packet faults) := by
  exact of_actual_with_catalog stagePrepared code support provenance receiver wellFormed supported original rows covered checked catalog (CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog.evidence methods) signatureMember sourceOwner shape syntaxTree child selected

end EvidenceWrappers

section Legacy
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
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
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (original : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows

variable (choice : Choice code
  («stages» := RecursiveNamedPreparedStageScopes.registry stagePrepared))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics



include provenance receiver wellFormed supported original rows covered checked catalog methods signatureMember sourceOwner in
def support_general
    (choiceIssued : choice.Issued code support.caller.named)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType) :
    CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport.SelectedBody
      headers code support.body.toContext stages choice.packet faults := by
  exact support_general_generic stagePrepared code support provenance receiver wellFormed supported original rows covered checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) signatureMember sourceOwner choice choiceIssued syntaxTree

include provenance receiver wellFormed supported original rows covered checked catalog methods signatureMember sourceOwner in
omit choice in
theorem of_actual
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (fun id => GeneralSyntax function.source id directSites)
      support.body.context (.statements true function.body) function.resultType)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code stages,
      CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport.SelectedBody
        headers code support.body.toContext stages packet faults) := by
  exact of_actual_generic stagePrepared code support provenance receiver wellFormed supported original rows covered checked catalog (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed methods) signatureMember sourceOwner shape syntaxTree child selected

end Legacy

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedSupport
