import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPhysicalMixedScopedCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedBodySupport

/-! Finite original-source statement admission supplies scoped named bodies.
Independent Header typing recovers lexical contexts and loop typing through
the shared scanner. The existing physical family consumes the issued support. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedScopedAdmission (Admission)

/-- Actual Header typing and accepted body compilation close the existing
scoped static issuer. Syntax, metadata, direct support and slot callbacks are
all constructed from the certification result and inventory. -/
theorem of_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (table : TableAligned inputs directRows)
    (admission : Admission prepared header directRows)
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      SelectedCompilationPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) := by
  obtain ⟨final, facts, typed, _complete⟩ := certified.statements
  have syntaxTree := admission.body.syntax header.unique typed
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted
    aligned.accepted admission.body.shape aligned.projection
  let support := SelectedCompilationNamedPhysicalMixedScopedCollectors.of_actual_with_catalog
    prepared aligned ready diagnostic receiver bodies certified
    (fun _ site => site.supported table) admission.metadata rows
    (fun _ site _ _ target global => site.covered rows table target global)
    checked catalog methods member receipt actual syntaxTree
  let body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header := {
    row := row, prepared := prepared, instantiation := instantiation, aligned := aligned,
    layouts := aligned.layouts, compilation := .canonicalBranching receipt }
  exact ⟨body, .scoped body receipt rfl support⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedAdmission
