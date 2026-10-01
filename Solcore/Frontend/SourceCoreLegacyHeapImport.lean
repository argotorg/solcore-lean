import Solcore.Frontend.SourceCoreExecution

/-! Explicit historical-input migration. The common compiler API uses data
cells and sealed snapshots. This adapter only applies the existing deep heap
validator; it introduces no source execution path. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreLegacyHeapImport

def preparePrefix (artifact : SourceCoreExecution.Artifact) (state : SourceTypedRuntime.RuntimeState)
    (validationFuel : Nat := 1024) : Option (SourceCoreExecution.PrefixSnapshot artifact) :=
  SourceCoreExecution.Internal.importPrefix artifact fun native =>
    SourceCoreIndexedSession.Legacy.preparePrefix native state validationFuel

end Solcore.Frontend.SourceCoreLegacyHeapImport
