import Solcore.SourceSemantics.CoreLowering.CompatiblePayload
import Solcore.SourceSemantics.Dynamic.RuntimeType

/-! Runtime key guards follow the original source metadata up to staging
normalization. Core type projection is not an authentication rule. Function
leaves supply their own shallow source-type law, independent of capture heaps.
The remaining arbitrary nested data cases follow from the full payload relation.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend SourceInference GeneralHeap

/-- The independent source normalization agrees with the compiler's metadata
view, by structural recursion over every source type form. -/
theorem runtimeType_agrees_metadata (type : TypeSystem.Ty) :
    Dynamic.runtimeType type = SourceCoreRawMetadata.runtimeType type := by
  induction type <;> simp_all [Dynamic.runtimeType, SourceCoreRawMetadata.runtimeType]

def FunctionRuntimeViews {catalog : SourceCoreCompatibleCatalog.Catalog} {ambient : AmbientDefinitions catalog.definitions} (functions : FunctionModel catalog ambient) : Prop :=
  ∀ {registry mapping world parameter result source value type},
    functions.Represents registry mapping world (.function parameter result) source value type →
      Dynamic.ValueRuntimeTypeMatches source (.function parameter result)

/-- Exact metadata receipts and structural children determine runtime
compatibility, including staged mapping keys and proxies nested in products. -/
theorem ValueRep.source_runtimeView {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {value : Value} {type : Ty}
    (functionTypes : FunctionRuntimeViews functions)
    (represented : ValueRep checked registry functions mapping world sourceType source value type) :
    Dynamic.ValueRuntimeTypeMatches source sourceType := by
  induction represented using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit => exact Dynamic.ValueRuntimeType.unit.matches
  | bool value => exact .bool value
  | word value => exact .word value
  | integer value => exact .integer value
  | product _ _ first second =>
    cases first with
    | intro first firstView =>
      cases second with
      | intro second secondView =>
        exact .intro (.product first second) (by simp only [Dynamic.runtimeType, firstView, secondView])
  | function related => exact functionTypes related
  | proxy => exact (Dynamic.ValueRuntimeType.proxy _).matches
  | constructed => exact (Dynamic.ValueRuntimeType.constructed _ _).matches
  | mappingValue => exact (Dynamic.ValueRuntimeType.mapping _ _ _).matches
  | compatible same _ ih =>
    cases ih with
    | intro typed view =>
      exact .intro typed (view.trans (by simpa only [runtimeType_agrees_metadata] using same.symm))
  | nil | cons | empty | entry | absent | present => trivial

end Solcore.SourceSemantics.CoreLowering.CompatiblePayload
