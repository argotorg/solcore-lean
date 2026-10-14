import Solcore.SourceSemantics.CoreLowering.CompatiblePayload

/-! Original scalar metadata determines both represented values without
any assumptions about the representation of callable values. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRawScalarFields
open Core Frontend SourceInference GeneralHeap CompatiblePayload

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

theorem word_fields {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type)
    (view : SourceCoreRawMetadata.runtimeType sourceType = .word) :
    ∃ word, source = .word word ∧ value = .word word ∧ type = .word := by
  revert view
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | word word => intro _; exact ⟨word, rfl, rfl, rfl⟩
  | compatible same _ ih => intro view; exact ih (same.symm.trans view)
  | @constructed metadata id tag sources values types _ _ _ projected _ _ _ =>
      intro view
      have scalar : checked.catalog.project metadata.resultType = .ok .word := by
        rw [← checked.catalog.project_runtimeType, view]
        rfl
      cases Except.ok.inj (projected.symm.trans scalar)
  | unit | bool | integer | product | function | proxy | mappingValue =>
      intro view
      cases view
  | nil | cons | empty | entry | absent | present => trivial

theorem integer_fields {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type)
    (view : SourceCoreRawMetadata.runtimeType sourceType = .integer) :
    ∃ integer, source = .integer integer ∧ value = .integer integer ∧ type = .integer := by
  revert view
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | integer integer => intro _; exact ⟨integer, rfl, rfl, rfl⟩
  | compatible same _ ih => intro view; exact ih (same.symm.trans view)
  | @constructed metadata id tag sources values types _ _ _ projected _ _ _ =>
      intro view
      have scalar : checked.catalog.project metadata.resultType = .ok .integer := by
        rw [← checked.catalog.project_runtimeType, view]
        rfl
      cases Except.ok.inj (projected.symm.trans scalar)
  | unit | bool | word | product | function | proxy | mappingValue =>
      intro view
      cases view
  | nil | cons | empty | entry | absent | present => trivial

end Solcore.SourceSemantics.CoreLowering.CompatibleRawScalarFields
