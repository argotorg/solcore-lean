import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission

/-! Selected execution retains prepared closure bodies. Its finite certificate
uses the widened scoped Source inventory, independently of the legacy uniform
body package, while keeping all original rows and actual issuers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedProgramCertificates
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedProgramAdmission (Selection)

inductive RootCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction) where
  | scoped (source : CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission
      compiled named named.specialized.function.typedBody (statements named.specialized.function.typedBody)
      named.specialized.function.inferredBodyType directRows)
  | formation (source : CallableIndexedOwnedPreparedNamedFactoryAdmission.Certificate compiled named)
  | scopedFactory (source : CallableIndexedOwnedPreparedScopedFactoryAdmission.Certificate compiled named)
  | excluded (absent : ∀ signature ∈ compiled.sourceProgram.signatures.functions,
      named.specialized.declaration ≠ signature.id)


structure RowCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) where
  root : RootCertificate compiled named directRows
  closures : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate compiled named directRows allowCoerced


structure Certificate (compiled : SourceCoreUnifiedCompilation.Compiled) where
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  selection : Selection compiled table.rows
  rows : ∀ named ∈ compiled.indexed.base.functions,
    Nonempty (RowCertificate compiled named table.rows selection.allowCoerced)
  profile : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedProgramCertificates
