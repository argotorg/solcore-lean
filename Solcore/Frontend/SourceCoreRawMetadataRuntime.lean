import Solcore.Frontend.SourceCoreRawMetadata
import Solcore.Frontend.SourceRuntimeValues

/-! The metadata registry and the shared source-value carrier use the same
runtime type compatibility relation. This bridge imports the carrier only;
there is no source expression or statement evaluator dependency. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreRawMetadata

theorem runtimeType_sourceValues (type : TypeSystem.Ty) :
    runtimeType type = SourceTypedRuntime.runtimeType type := by
  induction type <;> simp_all [runtimeType]

theorem Inserted.source_runtime_compatible {before : Registry} {expected : TypeSystem.Ty} {metadata : Metadata}
    (inserted : Inserted before expected metadata) :
    SourceTypedRuntime.runtimeType expected = SourceTypedRuntime.runtimeType metadata.type := by
  simpa only [runtimeType_sourceValues] using inserted.runtime_compatible

end Solcore.Frontend.SourceCoreRawMetadata
