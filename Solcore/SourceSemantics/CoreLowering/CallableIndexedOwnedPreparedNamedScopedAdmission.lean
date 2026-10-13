import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport

/-! Finite original-source statement admission supplies scoped named bodies.
Independent Header typing recovers lexical contexts and loop typing through
the shared scanner. The existing physical family consumes the issued support. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedFunctionValues (Header)

/-- The named-body API selects top-level mode of the shared original-source scan. -/
abbrev BodyScan (source : TypedSource) (approved : ExpressionId → Prop)
    (expected : TypeSystem.Ty) (statements : List StatementId) : Prop :=
  ScopedSourceBodyAdmission.Scan source approved expected true statements

theorem BodyScan.shape {source : TypedSource} {approved : ExpressionId → Prop}
    {expected : TypeSystem.Ty} {statements : List StatementId}
    (scan : BodyScan source approved expected statements) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape source true statements :=
  ScopedSourceBodyAdmission.Scan.shape scan

theorem BodyScan.syntax {source : TypedSource} {approved : ExpressionId → Prop}
    {expected : TypeSystem.Ty} {statements : List StatementId}
    (scan : BodyScan source approved expected statements) (unique : NodeOccurrencesUnique source)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source {returnType := expected} context statements final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements true statements) expected :=
  ScopedSourceBodyAdmission.Scan.syntax scan unique rfl typed

/-- Fuel bounds both the original statement graph and expression traversal. -/
def scan?
    (inputs : List SourceSpecialization.SpecializedFunction) (source : TypedSource) (expected : TypeSystem.Ty) (fuel : Nat)
    (statements : List StatementId) : Option (PLift
      (BodyScan source (fun id => GeneralSyntax source id (DirectSite inputs)) expected statements)) :=
  ScopedSourceBodyAdmission.scan? source
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.expression? inputs source fuel) expected fuel true statements

structure SourceAdmission (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (statements : List StatementId) (expected : TypeSystem.Ty)
    (directRows : List SourceSpecialization.SpecializedFunction) : Prop where
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    compiled.indexed named source (DirectSite directRows)
  body : BodyScan source (fun id => GeneralSyntax source id (DirectSite directRows)) expected statements

abbrev Admission {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (directRows : List SourceSpecialization.SpecializedFunction) : Prop :=
  SourceAdmission compiled prepared.named header.function.source header.function.body
    header.function.resultType directRows

/-- This checker reads only compiler/source data. Neither Headers nor the
classically assembled inventory appear in the executable arguments. -/
def admitSource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (statements : List StatementId) (expected : TypeSystem.Ty)
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat) :
    Option (PLift (SourceAdmission compiled named source statements expected directRows)) := do
  let ⟨metadata⟩ ← CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    compiled.indexed named source (DirectSite directRows)
  let ⟨body⟩ ← scan? directRows source expected fuel statements
  pure ⟨⟨metadata, body⟩⟩

/-- Successful certification supplies all expression syntax and native hook
metadata from the original finite tables. It does not claim every accepted
program belongs to the supported statement and expression fragment. -/
def admitPrepared {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat) :
    Option (PLift (Admission prepared header directRows)) :=
  admitSource compiled prepared.named header.function.source header.function.body
    header.function.resultType directRows fuel

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
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {loaded : LoadedProgram}
    (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
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
        header body) := by
  obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  have syntaxTree := admission.body.syntax header.unique typed
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted
    aligned.accepted admission.body.shape aligned.projection
  let support := CallableIndexedOwnedPreparedNamedPhysicalMixedScopedCollectors.of_actual_with_catalog
    prepared aligned ready diagnostic receiver wellFormed
    (fun _ site => site.supported table) admission.metadata rows
    (fun _ site _ _ target global => site.covered rows table target global)
    checked catalog methods member receipt actual syntaxTree
  let body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header := {
    row := row, prepared := prepared, instantiation := instantiation, aligned := aligned,
    layouts := aligned.layouts, compilation := .canonicalBranching receipt }
  exact ⟨body, .scoped body receipt rfl support⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission
