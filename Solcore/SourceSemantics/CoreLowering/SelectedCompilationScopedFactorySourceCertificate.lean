import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission

/-! Selected formation keeps the complete original scoped body. The prepared
physical receipt admits its reached projected unary diagnostics directly. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedFactorySourceCertificate
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
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

/-- The existing narrower certificate embeds with all original fields intact. -/
def of_legacy {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {body : List StatementId}
    (original : CallableIndexedOwnedPreparedScopedFactoryAdmission.SourceCertificate compiled named source body) :
    SourceCertificate compiled named source body := {
  expression := original.expression, terminal := original.terminal, node := original.node,
  parameters := original.parameters, result := original.result, statements := original.statements,
  reported := original.reported, found := original.found, form := original.form, owner := original.owner,
  requirements := original.requirements, coercions := original.coercions, ordinary := original.ordinary,
  read := original.read, scan := original.scan }

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


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedFactorySourceCertificate
