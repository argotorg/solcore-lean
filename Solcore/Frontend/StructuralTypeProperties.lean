import Solcore.Frontend.StructuralType
import Solcore.Frontend.TypeNameProperties

/-! Exact correspondence for the independent structural type fragment.
Named-only interpretation and its whole-result table membership law remain unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem StructuralTypeDenotes.complete {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty}
    (meaning : StructuralTypeDenotes table source type) :
    interpretStructuralType? table source = some type := by
  induction meaning with
  | named found =>
      simpa only [interpretStructuralType?] using TypeNameTable.lookup?_iff.mpr found
  | unit => simp only [interpretStructuralType?]
  | single _ ih => simpa only [interpretStructuralType?] using ih
  | pair _ _ leftIH rightIH =>
      simp only [interpretStructuralType?, leftIH, rightIH, bind, Option.bind_some, pure]

theorem interpretStructuralType?_sound {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty}
    (result : interpretStructuralType? table source = some type) :
    StructuralTypeDenotes table source type := by
  cases source with
  | mk span payload =>
      cases payload <;> try simp only [interpretStructuralType?, reduceCtorEq] at result
      case named name arguments =>
        cases arguments with
        | none =>
            exact .named (TypeNameTable.lookup?_iff.mp
              (by simpa only [interpretStructuralType?] using result))
        | some arguments => simp only [interpretStructuralType?, reduceCtorEq] at result
      case tuple elements =>
        cases elements with
        | nil =>
            simp only [interpretStructuralType?, Option.some.injEq] at result
            cases result
            exact .unit
        | cons left remaining =>
            cases remaining with
            | nil =>
                exact .single (interpretStructuralType?_sound
                  (by simpa only [interpretStructuralType?] using result))
            | cons right tail =>
                cases tail with
                | cons _ _ => simp only [interpretStructuralType?, reduceCtorEq] at result
                | nil =>
                    simp only [interpretStructuralType?, bind, Option.bind_eq_some_iff,
                      pure, Option.some.injEq] at result
                    obtain ⟨leftType, leftResult, rightType, rightResult, rfl⟩ := result
                    exact .pair (interpretStructuralType?_sound leftResult)
                      (interpretStructuralType?_sound rightResult)
termination_by sizeOf source

theorem interpretStructuralType?_iff {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} :
    interpretStructuralType? table source = some type ↔ StructuralTypeDenotes table source type :=
  ⟨interpretStructuralType?_sound, StructuralTypeDenotes.complete⟩

theorem StructuralTypeDenotes.type_unique {table : TypeNameTable}
    {source : Syntax.TypeExpr} {left right : Core.Ty}
    (leftMeaning : StructuralTypeDenotes table source left)
    (rightMeaning : StructuralTypeDenotes table source right) : left = right :=
  Option.some.inj (leftMeaning.complete.symm.trans rightMeaning.complete)

theorem interpretStructuralType?_eq_none_iff {table : TypeNameTable}
    {source : Syntax.TypeExpr} :
    interpretStructuralType? table source = none ↔
      ¬ ∃ type, StructuralTypeDenotes table source type := by
  constructor
  · intro result ⟨type, meaning⟩
    have accepted := meaning.complete
    rw [result] at accepted
    cases accepted
  · intro absent
    cases result : interpretStructuralType? table source with
    | none => rfl
    | some type => exact False.elim (absent ⟨type, interpretStructuralType?_sound result⟩)

/-- Only the outer occurrence range changes; recursive child ranges are untouched. -/
theorem interpretStructuralType?_span (table : TypeNameTable) (source : Syntax.TypeExpr)
    (span : Syntax.SourceSpan) :
    interpretStructuralType? table { source with span } = interpretStructuralType? table source := by
  cases source with
  | mk sourceSpan payload =>
      cases payload <;> try simp only [interpretStructuralType?]
      case named name arguments => cases arguments <;> simp only [interpretStructuralType?]
      case tuple elements =>
        cases elements with
        | nil => simp only [interpretStructuralType?]
        | cons left remaining =>
            cases remaining with
            | nil => simp only [interpretStructuralType?]
            | cons right tail => cases tail <;> simp only [interpretStructuralType?]

theorem TypeNameDenotes.structural {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} (meaning : TypeNameDenotes table source type) :
    StructuralTypeDenotes table source type := by
  cases meaning with
  | named found => exact .named found

theorem interpretStructuralType?_of_typeName {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty}
    (accepted : interpretTypeName? table source = some type) :
    interpretStructuralType? table source = some type :=
  (interpretTypeName?_sound accepted).structural.complete

/-- Full optional-result agreement on the old named/no-arguments shape. -/
theorem interpretStructuralType?_named_eq_typeName (table : TypeNameTable)
    (name : Syntax.QualifiedName) (span : Syntax.SourceSpan) :
    interpretStructuralType? table ⟨span, .named name none⟩ =
      interpretTypeName? table ⟨span, .named name none⟩ := by
  simp only [interpretStructuralType?, interpretTypeName?]

end Solcore.Frontend
