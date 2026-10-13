import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySyntaxTable

/-! One executable entry scans actual cached ordinary rows and original named
syntax. The proof-only issuer connects that finite result to the authentic
catalog and the existing physical body family. Static certification success
remains distinct from public compilation success. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCatalogAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Catalog)

/-- All executable fields come from compiler/source data. The certificate has
no supplied expression, metadata, slot, or body execution callback. -/
structure Certified (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (statements : List StatementId) (expected : TypeSystem.Ty) where
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  sourceAdmission : CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission
    compiled named source statements expected table.rows

/-- The cache scanner conservatively omits rows outside static admission.
The source scanner then requires every actual direct call to match a retained
row, including its full metadata and closed raw replacement range. -/
def certifySource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (statements : List StatementId) (expected : TypeSystem.Ty) (fuel : Nat) :
    Option (Certified compiled named source statements expected) := do
  let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel
  let ⟨sourceAdmission⟩ ← CallableIndexedOwnedPreparedNamedScopedAdmission.admitSource
    compiled named source statements expected table.rows fuel
  pure ⟨table, sourceAdmission⟩

/-- The same certified source is connected to any authentic filtered catalog.
Independent Header typing supplies every lexical context; genuine compiler
and dictionary receipts issue the final physical scoped support. -/
theorem of_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    (catalog : Catalog compiled)
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (certified : Certified compiled prepared.named header.function.source
      header.function.body header.function.resultType)
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (coercions : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers catalog.rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) :=
  CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual prepared aligned catalog.rows
    (certified.table.aligned catalog) certified.sourceAdmission ready diagnostic receiver wellFormed
    checked coercions methods member actual

/-- A source with no declaration calls can be issued for any retained inventory.
The empty data-table alignment is constructed here, so callers supply only the
executable source certificate and the real compiler/Header receipts. -/
theorem of_empty_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (certified : CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission
      compiled prepared.named header.function.source header.function.body header.function.resultType [])
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (coercions : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) :=
  CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual prepared aligned rows
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.TableAligned.empty inputs) certified ready diagnostic receiver wellFormed
    checked coercions methods member actual

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCatalogAdmission
