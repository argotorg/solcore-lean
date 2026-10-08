import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterMeaning
import Solcore.SourceSemantics.CoreLowering.DataExpressionSequence

/-! Static argument alignment keeps the raw Source and native type rows
independent. The conventional zero and singleton packings require a genuine
equal-length receipt before their packed types determine an ordered row.
Actual represented values and authentic binder arity supply those lengths;
no count is inferred from a type or from a native representation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
open Core Frontend SourceInference GeneralHeap

/-- Source packed products determine their ordered row only at equal lengths. -/
theorem source_rows_of_bundle {left right : List TypeSystem.Ty}
    (lengths : left.length = right.length)
    (packed : TypeSystem.Ty.productMany left = TypeSystem.Ty.productMany right) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
    cases right with
    | nil => simp at lengths
    | cons other rest =>
      have tailLengths : tail.length = rest.length := Nat.succ.inj lengths
      cases tail with
      | nil =>
        cases rest with
        | nil => simpa only [TypeSystem.Ty.productMany, List.cons.injEq, and_true] using packed
        | cons => simp at tailLengths
      | cons next more =>
        cases rest with
        | nil => simp at tailLengths
        | cons nextOther restMore =>
          simp only [TypeSystem.Ty.productMany, TypeSystem.Ty.product.injEq] at packed
          rw [packed.1, ih tailLengths packed.2]

/-- Native packed products retain the same independent physical count. -/
theorem native_rows_of_bundle {left right : List Ty}
    (lengths : left.length = right.length)
    (packed : SourceCoreCompatibleCatalog.packTypes left = SourceCoreCompatibleCatalog.packTypes right) :
    left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
    cases right with
    | nil => simp at lengths
    | cons other rest =>
      have tailLengths : tail.length = rest.length := Nat.succ.inj lengths
      cases tail with
      | nil =>
        cases rest with
        | nil => simpa only [SourceCoreCompatibleCatalog.packTypes, List.cons.injEq, and_true] using packed
        | cons => simp at tailLengths
      | cons next more =>
        cases rest with
        | nil => simp at tailLengths
        | cons nextOther restMore =>
          simp only [SourceCoreCompatibleCatalog.packTypes, Ty.product.injEq] at packed
          rw [packed.1, ih tailLengths packed.2]

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {mapping : LocationMap} {world : StoreTyping}
  {sourceTypes : List TypeSystem.Ty} {types : List Ty}
  {sources : List Dynamic.Value} {values : List Value}

/-- The genuine raw row has one entry for each actually represented Source value. -/
theorem source_length
    (represented : DataExpressionSequence.Values model mapping world sourceTypes types sources values) :
    sourceTypes.length = sources.length := by
  induction represented with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- Exact independent raw and native rows construct the original binder
representation without changing any represented value or its order. -/
theorem arguments_of_rows (bindings : List CallableIndexedParameterCertificates.Binding)
    (represented : DataExpressionSequence.Values model mapping world sourceTypes types sources values)
    (sourceRow : sourceTypes = bindings.map (fun binding => binding.1.scheme.body))
    (nativeRow : types = bindings.map Prod.snd) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values := by
  subst sourceTypes
  subst types
  induction bindings generalizing sources values with
  | nil => cases represented; exact .nil
  | cons binding tail ih =>
    cases represented with
    | cons head rest => exact .cons head (ih rest)

/-- Actual represented values, genuine selected binder arity and the two
independent packed-type receipts close the original binder argument vector. -/
theorem arguments_of_bundles (bindings : List CallableIndexedParameterCertificates.Binding)
    (represented : DataExpressionSequence.Values model mapping world sourceTypes types sources values)
    (arity : sources.length = bindings.length)
    (sourceBundle : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)))
    (nativeBundle : SourceCoreCompatibleCatalog.packTypes types =
      SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values := by
  have rawLength : sourceTypes.length = (bindings.map (fun binding => binding.1.scheme.body)).length := by
    simpa only [List.length_map] using (source_length represented).trans arity
  have nativeLength : types.length = (bindings.map Prod.snd).length := by
    simpa only [List.length_map] using represented.length.1.trans arity
  exact arguments_of_rows bindings represented
    (source_rows_of_bundle rawLength sourceBundle) (native_rows_of_bundle nativeLength nativeBundle)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
