import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedFormationCollectors
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedFactoryAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedScopedFactoryAdmission (Certificate at_header)
/-- The terminal compiler receipt and its Point are constructed here. No
caller supplies expression syntax, metadata or a closure execution premise. -/
theorem of_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) (certificate : Certificate compiled named)
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {bodyRegistry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
    {semanticFaults : FunctionCalls.FaultRep}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → semanticFaults reason token) :
    ∃ terminal : Terminal header,
      Nonempty (SelectedCompilationPhysicalNamedFormationSupport.Support
        (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) header terminal) := by
  let source := at_header prepared aligned selected same certificate
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rw [aligned.policy]; rfl) source.terminal aligned.accepted
  let terminal : Terminal header := {
    row := row, prepared := prepared, instantiation := instantiation, aligned := aligned,
    layouts := aligned.layouts, expression := source.expression, receipt := receipt,
    certificate := CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) source.expression receipt.child,
    certifies := by
      intro child generated
      have childEq : child = receipt.child := Except.ok.inj (generated.symm.trans receipt.generated)
      exact ⟨rfl, rfl, childEq⟩ }
  exact ⟨terminal, SelectedCompilationPhysicalNamedFormationCollectors.of_branching terminal
    ready diagnostic receiver included certified catalog profile member source.found source.form source.owner
    source.requirements source.coercions source.ordinary source.read source.scan.shape
    (fun typed => (source.scan.syntax header.unique rfl typed).bareUnary source.bareUnary) rfl⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedFactoryAdmission
