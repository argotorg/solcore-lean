import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedProgramCertificates

/-! Existing program certificates retain their exact cache, table and source
receipts when used by selected prepared execution. The scoped factory case
forgets only the additional legacy shape restriction. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
open Frontend

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {directRows : List Frontend.SourceSpecialization.SpecializedFunction}

/-- Every original root remains attached to the same cached function and rows. -/
def RootCertificate.to_prepared : RootCertificate compiled named directRows →
    SelectedCompilationPreparedProgramCertificates.RootCertificate compiled named directRows
  | .scoped source => .scoped source
  | .formation source => .formation source
  | .scopedFactory source => .scopedFactory (SelectedCompilationScopedFactorySourceCertificate.of_legacy source.toSourceCertificate)
  | .excluded absent => .excluded absent

/-- The conversion preserves the complete original table and its selection. -/
def Certificate.to_prepared (certificate : Certificate compiled) :
    SelectedCompilationPreparedProgramCertificates.Certificate compiled where
  table := certificate.table
  selection := certificate.selection
  rows := by
    intro named member
    obtain ⟨row⟩ := certificate.rows named member
    exact ⟨⟨row.root.to_prepared, row.closures⟩⟩
  profile := certificate.profile
  diagnostics := certificate.diagnostics

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
