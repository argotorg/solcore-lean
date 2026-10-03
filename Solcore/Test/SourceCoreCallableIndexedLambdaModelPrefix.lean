import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
import Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody

/-! A function relation can carry an independent source closure frame. The real
entry prefix keeps that stronger relation in its complete allocated heap. A
weaker representation supplies no missing frame. Runtime regressions reuse the
actual indexed lambda roots, including captures, faults and checkpoint resume. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaModelPrefix
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Core GeneralHeap CompatiblePayload CallableIndexedLambdaValues
open CallableIndexedHistory CallableIndexedLambdaEntryPrefix

private def SourceFrame (program : SourceSemantics.Program) (source : Dynamic.Value) : Prop :=
  match source with
  | .closure function => Dynamic.ClosureFrame program function
  | _ => True

private def framed {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (base : FunctionModel checked.catalog ambient) (program : SourceSemantics.Program) :
    FunctionModel checked.catalog ambient where
  Represents := fun registry mapping world type source native nativeType =>
    base.Represents registry mapping world type source native nativeType ∧ SourceFrame program source
  projection := fun related => base.projection related.1
  runtime_hasType := fun related => base.runtime_hasType related.1
  source_function := fun related => base.source_function related.1
  extend := fun related registries maps worlds =>
    ⟨base.extend related.1 registries maps worlds, related.2⟩

/-- This static witness travels with a function value; native typing does not
construct it. -/
theorem frame_from_stronger_relation {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {type : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {nativeType : Core.Ty}
    (related : (framed base program).Represents registry mapping world type (.closure function) native nativeType) :
    Dynamic.ClosureFrame program function := related.2

/-- A representation of the same native closure in the older relation cannot
justify the stronger model when its independent source frame is absent. -/
theorem missing_frame_prevents_reverse_inclusion {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {base : FunctionModel checked.catalog ambient} {program : SourceSemantics.Program}
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {type : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {nativeType : Core.Ty}
    (related : base.Represents registry mapping world type (.closure function) native nativeType)
    (missing : ¬ Dynamic.ClosureFrame program function) :
    ¬ base.Includes (framed base program) := by
  intro includes
  exact missing (frame_from_stronger_relation (includes related))

/-- Parameter allocation retains the stronger relation in every cell of the
actual reached heap, including old cells outside the parameter prefix. -/
theorem entry_preserves_full_model {values : SourceCoreCompatibleValues.Context}
    {prepared : Prepared values.checked} {function : Dynamic.Closure}
    {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Core.Environment}
    {captured : Captures prepared mapping world scope function.captured capturedActual}
    {code : Code prepared function scope captured.administrative} {history : History code}
    {inputs : Context code} {program : SourceSemantics.Program}
    {base : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared)}
    {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    {before : Dynamic.Heap} {store : Store} {location : Core.Location}
    {current : NativeFrame} {currentGhost : GhostFrame}
    (entry : EntryFor captured code history inputs (framed base program) registry arguments nativeArguments
      before store location current currentGhost) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry (framed base program)
      entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store := entry.entry.heaps

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedLambdaModelPrefix
