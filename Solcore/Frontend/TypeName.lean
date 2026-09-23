import Solcore.Core.Syntax
import Solcore.Syntax.Type

/-! Explicit interpretation of canonical named types without type arguments.
Qualified spelling components remain separate, and no spelling is reserved. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Ordered caller meanings for exact qualified spelling-component lists. -/
abbrev TypeNameTable := List (List String × Core.Ty)

namespace TypeNameTable

def lookup? : TypeNameTable → List String → Option Core.Ty
  | [], _ => none
  | (candidate, type) :: table, key =>
      if candidate = key then some type else lookup? table key

/-- The first matching key determines meaning, independently of `lookup?`. -/
inductive Lookup : TypeNameTable → List String → Core.Ty → Prop where
  | head {table : TypeNameTable} {key : List String} {type : Core.Ty} :
      Lookup ((key, type) :: table) key type
  | tail {table : TypeNameTable} {key candidate : List String}
      {type candidateType : Core.Ty}
      (different : candidate ≠ key) (found : Lookup table key type) :
      Lookup ((candidate, candidateType) :: table) key type

end TypeNameTable

/-- Exact component strings in written order; occurrence ranges are ignored. -/
def qualifiedTypeNameKey (name : Syntax.QualifiedName) : List String :=
  name.value.components.toList.map (·.value)

/-- `none` means unmapped or outside this adapter, not general source invalidity. -/
def interpretTypeName? (table : TypeNameTable) (source : Syntax.TypeExpr) : Option Core.Ty :=
  match source with
  | ⟨_, .named name none⟩ => table.lookup? (qualifiedTypeNameKey name)
  | _ => none

/-- Independent canonical meaning for this deliberately restricted type fragment. -/
inductive TypeNameDenotes (table : TypeNameTable) : Syntax.TypeExpr → Core.Ty → Prop where
  | named {span : Syntax.SourceSpan} {name : Syntax.QualifiedName} {type : Core.Ty}
      (found : TypeNameTable.Lookup table (qualifiedTypeNameKey name) type) :
      TypeNameDenotes table ⟨span, .named name none⟩ type

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.TypeNameProperties`
-/

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

/-!
## Consolidated module: `Solcore.Frontend.TypeNameTableExtensionProperties`
-/

/-! Semantic extension retains every existing first-match type meaning.
New keys may gain meanings; only mutual extension preserves lookup absence. -/

set_option autoImplicit false

namespace Solcore.Frontend

namespace TypeNameTable

/-- Preserve original meanings, not merely membership in the list of entries. -/
def Extends (old next : TypeNameTable) : Prop :=
  ∀ {key type}, Lookup old key type → Lookup next key type

theorem Extends.refl (table : TypeNameTable) : Extends table table := by
  intro key type found
  exact found

theorem Extends.trans {old middle next : TypeNameTable}
    (first : Extends old middle) (second : Extends middle next) : Extends old next := by
  intro key type found
  exact second (first found)

/-- Later duplicate entries cannot override the first original match. -/
theorem Extends.append_right (table extras : TypeNameTable) : Extends table (table ++ extras) := by
  intro key type found
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

/-- Freshness is sufficient, not necessary: a same-meaning duplicate can also
be safe, but a prefix that changes an existing meaning is not an extension. -/
theorem Extends.cons_fresh (table : TypeNameTable) (key : List String) (type : Core.Ty)
    (fresh : key ∉ table.map Prod.fst) : Extends table ((key, type) :: table) := by
  intro original originalType found
  apply Lookup.tail ?_ found
  intro same
  apply fresh
  rw [same]
  exact List.mem_map.mpr ⟨(original, originalType), found.mem, rfl⟩

theorem lookup?_eq_of_mutual_extends {left right : TypeNameTable}
    (forward : Extends left right) (backward : Extends right left) (key : List String) :
    lookup? left key = lookup? right key := by
  cases leftResult : lookup? left key with
  | none =>
      cases rightResult : lookup? right key with
      | none => rfl
      | some type =>
          have accepted := lookup?_iff.mpr (backward (lookup?_iff.mp rightResult))
          rw [leftResult] at accepted
          cases accepted
  | some type => exact (lookup?_iff.mpr (forward (lookup?_iff.mp leftResult))).symm

end TypeNameTable

theorem TypeNameDenotes.extend_types {old next : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} (meaning : TypeNameDenotes old source type)
    (extension : TypeNameTable.Extends old next) : TypeNameDenotes next source type := by
  cases meaning with
  | named found => exact .named (extension found)

theorem interpretTypeName?_some_of_extends {old next : TypeNameTable}
    (extension : TypeNameTable.Extends old next) {source : Syntax.TypeExpr} {type : Core.Ty}
    (accepted : interpretTypeName? old source = some type) :
    interpretTypeName? next source = some type :=
  ((interpretTypeName?_sound accepted).extend_types extension).complete

theorem interpretTypeName?_eq_of_mutual_extends {left right : TypeNameTable}
    (forward : TypeNameTable.Extends left right) (backward : TypeNameTable.Extends right left)
    (source : Syntax.TypeExpr) : interpretTypeName? left source = interpretTypeName? right source := by
  rcases source with ⟨span, payload⟩
  cases payload <;> try rfl
  case named name arguments =>
    cases arguments with
    | none => exact TypeNameTable.lookup?_eq_of_mutual_extends forward backward _
    | some _ => rfl

end Solcore.Frontend
