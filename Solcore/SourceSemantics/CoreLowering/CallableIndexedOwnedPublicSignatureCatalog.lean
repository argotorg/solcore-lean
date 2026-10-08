import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCatalogClosedSources
import Solcore.SourceSemantics.ProgramCheckingSoundness

/-! Public match proofs use the exact Source signature catalog selected by the
successful compiler factory. Native definitions do not establish Source catalog
validity; the original well-formed Source program supplies that judgment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
open Frontend SourceInference

/-- The actual public catalog retains its original Source signature list. -/
theorem signatures (compiled : SourceCoreUnifiedCompilation.Compiled) :
    compiled.compatible.checked.signatures = compiled.sourceProgram.signatures := by
  obtain ⟨types, metadata, accepted⟩ :=
    CallableIndexedOwnedPublicCatalogClosedSources.compiled_catalog compiled
  exact SourceCoreCompatibleCatalog.prepare_signatures accepted

/-- Source program validity applies to that same selected catalog. -/
theorem well_formed (compiled : SourceCoreUnifiedCompilation.Compiled)
    (valid : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    SignatureCatalogWellFormed compiled.compatible.checked.signatures := by
  rw [signatures compiled]
  exact valid.signatures

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
