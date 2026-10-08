import Solcore.SourceSemantics.CoreLowering.ReachedExpressionFaultOrigins
import Solcore.SourceSemantics.CoreLowering.CompatibleSessionContextualDiagnosticObservations

/-! A reached local read retains its literal binder and Source occurrence.
Actual issuer selection and table rebuilding supply the same diagnostic token.
Whole-program failure and restored heap associations remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedReadFaultDiagnosticObservations
open Core Frontend SourceInference
open ReachedExpressionFaultOrigins
open CallableIndexedOwnedPublicFaultReceiverTables

/-- The primitive uses the Source and token of the selected actual issuer.
The original prepared function row is kept as a genuine lookup receipt. -/
def IssuerAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked))
    (owner : SourceSpecialization.SpecializationKey) (leaf : ReadLeaf) : Prop :=
  ∃ function own, SourceCompilationPlan.exactSpecialization prepared.plan owner = .ok function ∧
    leaf.source = function.function.typedBody ∧
    leaf.reason = issued.program.reasonAt owner leaf.id ∧
    issued.program.base.find? owner = some own

/-- The Source occurrence follows from this actual read certificate. -/
theorem ReadLeaf.contains (leaf : ReadLeaf) :
    ContainsExpression leaf.source leaf.id leaf.certificate.node :=
  lookupExpression?_sound leaf.certificate.metadata.found

/-- The receiving public table decodes the actual primitive token. Binder and
span come from its certificate, rather than separate association assumptions. -/
theorem ReadLeaf.public_diagnostic (leaf : ReadLeaf)
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {owner : SourceSpecialization.SpecializationKey}
    (issuer : IssuerAt compiled.indexed.base issued owner leaf)
    (unique : NodeOccurrencesUnique leaf.source) :
    completion.result.diagnostics.diagnostic? leaf.reason = some {
      error := .uninitializedLocal leaf.certificate.binder,
      site := .occurrence leaf.id.occurrence, span := some leaf.certificate.node.span } := by
  obtain ⟨function, own, record, sourceEq, reasonEq, ownFound⟩ := issuer
  have canonicalUnique : NodeOccurrencesUnique function.function.typedBody := sourceEq ▸ unique
  have contains : ContainsExpression function.function.typedBody leaf.id leaf.certificate.node :=
    sourceEq ▸ ReadLeaf.contains leaf
  obtain ⟨read, _expression, _binder, _span, token, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic
      compiled receiver present record canonicalUnique contains leaf.certificate.form ownFound
  simpa only [← token, ← reasonEq] using decoded

/-- The actual Session receiving table retains the same canonical read.
Its genuine registry and callable append are supplied by the existing receiver. -/
theorem ReadLeaf.session_diagnostic (leaf : ReadLeaf)
    {artifact : SourceCoreIndexedSession.Artifact}
    (session : SourceCoreIndexedSession.Session artifact)
    {rootKey : SourceSpecialization.SpecializationKey} {table : SourceCoreFaultSites.Table}
    (receiver : session.DiagnosticTableAt rootKey table)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial _)}
    (present : artifact.program.base.diagnostics = some issued)
    {owner : SourceSpecialization.SpecializationKey}
    (issuer : IssuerAt artifact.program.base issued owner leaf)
    (unique : NodeOccurrencesUnique leaf.source) :
    table.diagnostic? leaf.reason = some {
      error := .uninitializedLocal leaf.certificate.binder,
      site := .occurrence leaf.id.occurrence, span := some leaf.certificate.node.span } := by
  obtain ⟨function, own, record, sourceEq, reasonEq, ownFound⟩ := issuer
  have canonicalUnique : NodeOccurrencesUnique function.function.typedBody := sourceEq ▸ unique
  have contains : ContainsExpression function.function.typedBody leaf.id leaf.certificate.node :=
    sourceEq ▸ ReadLeaf.contains leaf
  obtain ⟨registry, _registryAt, actual, read, actualPresent, _expression, _binder, _span,
      token, _member, decoded⟩ :=
    CompatibleSessionContextualDiagnosticObservations.session_read_observation session receiver
      (show CompatibleSessionContextualDiagnosticObservations.ReadInputs artifact.program owner from
        ⟨issued, own, present, ownFound⟩) record canonicalUnique contains leaf.certificate.form
  have same := Option.some.inj (actualPresent.symm.trans present)
  cases same
  simpa only [← token, ← reasonEq] using decoded

end Solcore.SourceSemantics.CoreLowering.ReachedReadFaultDiagnosticObservations
