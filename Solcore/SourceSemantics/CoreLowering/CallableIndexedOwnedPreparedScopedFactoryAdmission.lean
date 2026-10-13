import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors

/-! The original returned lambda retains its scoped statement certificate.
The compiler producer derives this certificate from its accepted inner body;
physical formation uses the same original source and captured state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

structure SourceCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (body : List StatementId) where
  expression : ExpressionId
  terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal source expression body
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  reported : Core.Ty
  found : source.lookupExpression? expression = some node
  form : node.form = .lambda parameters result statements
  owner : expression.occurrence.owner = source.owner
  requirements : node.requirements = []
  coercions : node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
      binding.initializer = expression)) = none
  read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
    source expression = .ok (node, reported)
  scan : ScopedSourceBodyAdmission.Scan source (fun _ => True) result true statements

abbrev Certificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) :=
  SourceCertificate compiled named named.specialized.function.typedBody
    (statements named.specialized.function.typedBody)

/-- Actual cached identity transports the source certificate to the exact
Header and its compiled statement roots. -/
def at_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) (certificate : Certificate compiled named) :
    SourceCertificate compiled prepared.named header.function.source header.function.body := by
  obtain ⟨source, body, _result⟩ := header_data prepared aligned
  rw [source, body, cached_named prepared selected same]
  exact certificate

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
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {bodyRegistry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
    {semanticFaults : FunctionCalls.FaultRep} :
    ∃ terminal : Terminal header,
      Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
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
  exact ⟨terminal, CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors.of_branching terminal
    ready diagnostic wellFormed profile member source.found source.form source.owner
    source.requirements source.coercions source.ordinary source.read source.scan.shape
    (fun typed => source.scan.syntax header.unique rfl typed) rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission
