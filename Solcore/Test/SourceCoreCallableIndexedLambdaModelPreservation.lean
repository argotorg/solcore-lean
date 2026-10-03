import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimePreservation
import Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody

/-! A stronger function model carries independent source frames. Its value
observations and runtime views follow from the original representation. These
are representation properties; neither executes or assumes a callable body.
The generic preservation endpoints keep this model in results and all cells. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaModelPreservation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Core GeneralHeap CompatiblePayload CompatibleEquality

private def Frame (program : SourceSemantics.Program) (source : Dynamic.Value) : Prop :=
  match source with
  | .closure function => Dynamic.ClosureFrame program function
  | _ => True

private def framed {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (base : FunctionModel checked.catalog ambient) (program : SourceSemantics.Program) :
    FunctionModel checked.catalog ambient where
  Represents := fun registry mapping world type source native nativeType =>
    base.Represents registry mapping world type source native nativeType ∧ Frame program source
  projection := fun related => base.projection related.1
  runtime_hasType := fun related => base.runtime_hasType related.1
  source_function := fun related => base.source_function related.1
  extend := fun related registries maps worlds =>
    ⟨base.extend related.1 registries maps worlds, related.2⟩

theorem observations {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {identity : Dynamic.Value → Word → Prop}
    (observed : FunctionObservations checked.catalog base identity) :
    FunctionObservations checked.catalog (framed base program) identity :=
  fun related => observed related.1

theorem runtime_views {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    (viewed : FunctionRuntimeViews base) : FunctionRuntimeViews (framed base program) :=
  fun related => viewed related.1

/-- Independent closure provenance remains available after allocation, without
reconstructing it from a native closure or a compatibility-erased type. -/
theorem frame_survives_extension {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {registry futureRegistry : SourceCoreRawMetadata.Registry}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {type : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {nativeType : Core.Ty}
    (related : (framed base program).Represents registry mapping world type (.closure function) native nativeType)
    (registries : SourceCoreRawMetadata.Extends registry futureRegistry)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    (framed base program).Represents futureRegistry futureMapping futureWorld type (.closure function) native nativeType ∧
      Dynamic.ClosureFrame program function :=
  ⟨(framed base program).extend related registries maps worlds, related.2⟩

abbrev entry_preserves := @CallableIndexedLambdaRuntimePreservation.entry_preserves_for
abbrev preserves := @CallableIndexedLambdaRuntimePreservation.preserves_for

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedLambdaModelPreservation
