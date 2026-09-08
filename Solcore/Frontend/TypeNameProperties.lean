import Solcore.Frontend.TypeName

/-! Exact first-match type-name interpretation, without lexical or range validity
premises and without assigning built-in meaning to any source spelling. -/

set_option autoImplicit false

namespace Solcore.Frontend

namespace TypeNameTable

theorem lookup?_iff {table : TypeNameTable} {key : List String} {type : Core.Ty} :
    lookup? table key = some type ↔ Lookup table key type := by
  constructor
  · intro result
    induction table with
    | nil => simp [lookup?] at result
    | cons entry rest ih =>
        rcases entry with ⟨candidate, candidateType⟩
        by_cases same : candidate = key
        · subst candidate
          simp only [lookup?, ↓reduceIte, Option.some.injEq] at result
          subst candidateType
          exact .head
        · exact .tail same (ih (by simpa only [lookup?, if_neg same] using result))
  · intro found
    induction found with
    | head => simp [lookup?]
    | tail different _ ih => simpa only [lookup?, if_neg different] using ih

theorem Lookup.type_unique {table : TypeNameTable} {key : List String}
    {left right : Core.Ty} (leftFound : Lookup table key left)
    (rightFound : Lookup table key right) : left = right :=
  Option.some.inj ((lookup?_iff.mpr leftFound).symm.trans (lookup?_iff.mpr rightFound))

theorem Lookup.mem {table : TypeNameTable} {key : List String} {type : Core.Ty}
    (found : Lookup table key type) : (key, type) ∈ table := by
  induction found with
  | head => exact List.mem_cons_self
  | tail _ _ ih => exact List.mem_cons_of_mem _ ih

theorem lookup?_eq_none_iff {table : TypeNameTable} {key : List String} :
    lookup? table key = none ↔ key ∉ table.map Prod.fst := by
  induction table with
  | nil => simp [lookup?]
  | cons entry rest ih =>
      rcases entry with ⟨candidate, candidateType⟩
      by_cases same : candidate = key
      · subst candidate; simp [lookup?]
      · simpa [lookup?, same, Ne.symm same] using ih

end TypeNameTable

theorem TypeNameDenotes.complete {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} (meaning : TypeNameDenotes table source type) :
    interpretTypeName? table source = some type := by
  cases meaning with
  | named found => exact TypeNameTable.lookup?_iff.mpr found

theorem interpretTypeName?_sound {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty}
    (result : interpretTypeName? table source = some type) :
    TypeNameDenotes table source type := by
  cases source with
  | mk span payload =>
      cases payload <;> simp only [interpretTypeName?, reduceCtorEq] at result
      case named name arguments =>
        cases arguments with
        | none => exact .named (TypeNameTable.lookup?_iff.mp result)
        | some arguments => simp only [reduceCtorEq] at result

theorem interpretTypeName?_iff {table : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} :
    interpretTypeName? table source = some type ↔ TypeNameDenotes table source type :=
  ⟨interpretTypeName?_sound, TypeNameDenotes.complete⟩

theorem TypeNameDenotes.type_unique {table : TypeNameTable} {source : Syntax.TypeExpr}
    {left right : Core.Ty} (leftMeaning : TypeNameDenotes table source left)
    (rightMeaning : TypeNameDenotes table source right) : left = right :=
  Option.some.inj (leftMeaning.complete.symm.trans rightMeaning.complete)

/-- Every denoted type is an actual entry in the caller's table. -/
theorem TypeNameDenotes.mem {table : TypeNameTable} {source : Syntax.TypeExpr} {type : Core.Ty}
    (meaning : TypeNameDenotes table source type) : ∃ key, (key, type) ∈ table := by
  cases meaning with
  | named found => exact ⟨_, found.mem⟩

theorem interpretTypeName?_eq_none_iff {table : TypeNameTable} {source : Syntax.TypeExpr} :
    interpretTypeName? table source = none ↔ ¬ ∃ type, TypeNameDenotes table source type := by
  constructor
  · intro result ⟨type, meaning⟩
    have accepted := meaning.complete
    rw [result] at accepted
    cases accepted
  · intro absent
    cases result : interpretTypeName? table source with
    | none => rfl
    | some type => exact False.elim (absent ⟨type, interpretTypeName?_sound result⟩)

/-- Replacing only the outer type range cannot change this adapter's result. -/
theorem interpretTypeName?_span (table : TypeNameTable) (source : Syntax.TypeExpr)
    (span : Syntax.SourceSpan) :
    interpretTypeName? table { source with span } = interpretTypeName? table source := by
  cases source with
  | mk sourceSpan payload =>
      cases payload <;> try rfl
      case named name arguments => cases arguments <;> rfl

/-- Exact component keys suffice, regardless of outer, name, or component ranges. -/
theorem interpretTypeName?_key_eq (table : TypeNameTable)
    {left right : Syntax.QualifiedName}
    (same : qualifiedTypeNameKey left = qualifiedTypeNameKey right)
    (leftSpan rightSpan : Syntax.SourceSpan) :
    interpretTypeName? table ⟨leftSpan, .named left none⟩ =
      interpretTypeName? table ⟨rightSpan, .named right none⟩ := by
  simp only [interpretTypeName?, same]

end Solcore.Frontend
