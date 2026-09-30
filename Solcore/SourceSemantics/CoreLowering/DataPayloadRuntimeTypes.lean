import Solcore.SourceSemantics.CoreLowering.DataPayload
import Solcore.SourceSemantics.CoreLowering.ContractedFunctionValues

/-! Source shallow runtime types are a separate authenticity law for abstract
function leaves. Core typing alone cannot provide this information. Concrete
ordinary and descriptor-bearing closures retain their exact source metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference GeneralHeap

/-- The key-type premise used by independent source mapping projections. It
observes retained function metadata, without inspecting captured heap cells. -/
def FunctionRuntimeTypes {catalog : SourceCoreDataCatalog.Catalog}
    (functions : GenericHeap.PayloadModel catalog) : Prop :=
  ∀ {mapping world parameter result source value type},
    functions.Represents mapping world (.function parameter result) source value type →
      Dynamic.ValueRuntimeType source (.function parameter result)

theorem ordinary_function_runtimeTypes (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : FunctionCode.BodyCertificate) (policy : SourceCoreFunctions.Policy) :
    FunctionRuntimeTypes (FunctionValues.model catalog program bodyCertificate policy) := by
  intro mapping world parameter result source value type related
  cases related with
  | closure layout code => exact .closure _

theorem contracted_function_runtimeTypes (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : FunctionCode.BodyCertificate) (table : SourceCoreStageCodebook.Table) :
    FunctionRuntimeTypes (ContractedFunctionValues.model catalog program bodyCertificate table) := by
  intro mapping world parameter result source value type related
  cases related with
  | closure layout code => exact .closure _

private theorem erase_ne_comptime (type inner : TypeSystem.Ty) :
    SourceCoreDataCatalog.erase type ≠ .comptime inner := by
  induction type <;> simp_all [SourceCoreDataCatalog.erase]

/-- Canonical retained data types determine the mathematical source value's
shallow runtime type, including functions nested in products. Nominal and
proxy arguments are retained exactly, not erased by this conclusion. -/
theorem ValueRep.source_runtimeType {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (functionTypes : FunctionRuntimeTypes functions)
    (represented : ValueRep catalog signatures functions mapping world sourceType source value type)
    (canonical : SourceCoreDataCatalog.erase sourceType = sourceType) :
    Dynamic.ValueRuntimeType source sourceType := by
  revert canonical
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) with
  | unit => intro _; exact .unit
  | bool value => intro _; exact .bool value
  | word value => intro _; exact .word value
  | integer value => intro _; exact .integer value
  | product _ _ first second =>
    intro canonical
    obtain ⟨left, right⟩ := TypeSystem.Ty.product.inj canonical
    exact .product (first left) (second right)
  | function related => intro _; exact functionTypes related
  | proxy => intro _; exact .proxy _
  | mapping => intro _; exact .mapping _ _ _
  | constructed nominal result => intro _; rw [← result]; exact .constructed _ _
  | comptime => intro impossible; exact False.elim (erase_ne_comptime _ _ impossible)
  | nil | cons | empty | prepend => trivial

end Solcore.SourceSemantics.CoreLowering.DataPayload
