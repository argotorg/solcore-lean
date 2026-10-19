import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticProducers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalScopedCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceScopedRoots

/-! Actual scoped compiler trees issue evidence-aware expression support.
Local initialization, assignment and control flow retain the full caller
ledger and dictionary through the existing shared body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceScopedCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
/-- The actual prepared Header, complete inventory and native metadata issue
all canonical children without exposing a child execution premise. -/
def of_actual
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {directSites : DeclarationInstantiation → Prop}
    (supported : ∀ instantiation, directSites instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source directSites)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source (fun id => GeneralSyntax header.function.source id directSites)
      header.context (.statements true header.function.body) header.function.resultType) :
    CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.NamedSupport
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry actual) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  apply CallableIndexedOwnedPreparedNamedCanonicalScopedCollectors.of_imperative_compiler prepared aligned ready diagnostic wellFormed complete zero member receipt
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.operands_of_diagnostic prepared aligned diagnostic receiver)
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.unary_of_diagnostic prepared aligned diagnostic receiver)
    (RecursiveNamedPreparedStageScopes.registry actual) syntaxTree
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType native
  have sameSource := (RecursiveNamedPreparedStageScopes.registry actual).source selected
  obtain ⟨root, prefixEq⟩ := CallableIndexedOwnedPreparedStagedNamedEvidenceScopedRoots.of_accepted_sites
    prepared aligned diagnostic receiver wellFormed supported metadata rows complete actual selected fields
    (by simpa only [sameSource] using declarations) (by simpa only [sameSource] using approved)
    (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed)
    (by simpa only [sameSource] using accepted)
  exact .canonical root prefixEq

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceScopedCollectors
