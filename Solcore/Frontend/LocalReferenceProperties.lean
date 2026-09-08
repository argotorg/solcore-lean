import Solcore.Frontend.LocalReference

/-! Exact first-match lookup and the identifier/group bridge. These laws do not
assume lexical validity, source-span validity, or any source scope policy. -/

set_option autoImplicit false

namespace Solcore.Frontend

namespace LocalNameTable

theorem lookup?_iff {table : LocalNameTable} {spelling : String} {id : Resolved.LocalId} :
    lookup? table spelling = some id ↔ Lookup table spelling id := by
  constructor
  · intro result
    induction table with
    | nil => simp [lookup?] at result
    | cons entry rest ih =>
        rcases entry with ⟨candidate, candidateId⟩
        by_cases same : candidate = spelling
        · subst candidate
          simp only [lookup?, ↓reduceIte, Option.some.injEq] at result
          subst candidateId
          exact .head
        · exact .tail same (ih (by simpa only [lookup?, if_neg same] using result))
  · intro found
    induction found with
    | head => simp [lookup?]
    | tail different _ ih => simpa only [lookup?, if_neg different] using ih

theorem Lookup.id_unique {table : LocalNameTable} {spelling : String}
    {left right : Resolved.LocalId} (leftFound : Lookup table spelling left)
    (rightFound : Lookup table spelling right) : left = right :=
  Option.some.inj ((lookup?_iff.mpr leftFound).symm.trans (lookup?_iff.mpr rightFound))

theorem Lookup.mem {table : LocalNameTable} {spelling : String} {id : Resolved.LocalId}
    (found : Lookup table spelling id) : (spelling, id) ∈ table := by
  induction found with
  | head => exact List.mem_cons_self
  | tail _ _ ih => exact List.mem_cons_of_mem _ ih

theorem lookup?_eq_none_iff {table : LocalNameTable} {spelling : String} :
    lookup? table spelling = none ↔ spelling ∉ table.map Prod.fst := by
  induction table with
  | nil => simp [lookup?]
  | cons entry rest ih =>
      rcases entry with ⟨candidate, candidateId⟩
      by_cases same : candidate = spelling
      · subst candidate; simp [lookup?]
      · simpa [lookup?, same, Ne.symm same] using ih

end LocalNameTable

theorem ResolvesLocalReference.complete {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (resolved : ResolvesLocalReference table source id) :
    resolveLocalReference? table source = some (.var id) := by
  induction resolved with
  | identifier found =>
      simp only [resolveLocalReference?, LocalNameTable.lookup?_iff.mpr found, Option.map_some]
  | group _ ih => simpa only [resolveLocalReference?] using ih

/-- Every successful result is a variable with an independent source/table derivation. -/
theorem resolveLocalReference?_sound {table : LocalNameTable}
    {source : Syntax.Expr} {output : Resolved.Expr}
    (result : resolveLocalReference? table source = some output) :
    ∃ id, output = .var id ∧ ResolvesLocalReference table source id := by
  cases source with
  | mk span payload =>
      cases payload <;> simp only [resolveLocalReference?, reduceCtorEq] at result
      case identifier name =>
        cases found : table.lookup? name.value with
        | none => simp only [found, Option.map_none, reduceCtorEq] at result
        | some id =>
            simp only [found, Option.map_some, Option.some.injEq] at result
            exact ⟨id, result.symm, .identifier (LocalNameTable.lookup?_iff.mp found)⟩
      case group inner =>
        obtain ⟨id, outputEq, child⟩ := resolveLocalReference?_sound result
        exact ⟨id, outputEq, .group child⟩
termination_by sizeOf source

theorem resolveLocalReference?_iff {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId} :
    resolveLocalReference? table source = some (.var id) ↔
      ResolvesLocalReference table source id := by
  constructor
  · intro result
    obtain ⟨actual, same, resolved⟩ := resolveLocalReference?_sound result
    cases same
    exact resolved
  · exact ResolvesLocalReference.complete

theorem resolveLocalReference?_eq_some_iff {table : LocalNameTable}
    {source : Syntax.Expr} {output : Resolved.Expr} :
    resolveLocalReference? table source = some output ↔
      ∃ id, ResolvesLocalReference table source id ∧ output = .var id := by
  constructor
  · intro result
    obtain ⟨id, same, resolved⟩ := resolveLocalReference?_sound result
    exact ⟨id, resolved, same⟩
  · rintro ⟨id, resolved, rfl⟩
    exact resolved.complete

theorem ResolvesLocalReference.id_unique {table : LocalNameTable}
    {source : Syntax.Expr} {left right : Resolved.LocalId}
    (leftResolved : ResolvesLocalReference table source left)
    (rightResolved : ResolvesLocalReference table source right) : left = right :=
  Resolved.Expr.var.inj (Option.some.inj (leftResolved.complete.symm.trans rightResolved.complete))

/-- A successful adapter result comes from an actual supplied name/ID entry. -/
theorem ResolvesLocalReference.mem {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (resolved : ResolvesLocalReference table source id) :
    ∃ spelling, (spelling, id) ∈ table := by
  induction resolved with
  | identifier found => exact ⟨_, found.mem⟩
  | group _ ih => exact ih

theorem resolveLocalReference?_eq_none_iff {table : LocalNameTable} {source : Syntax.Expr} :
    resolveLocalReference? table source = none ↔ ¬ ∃ id, ResolvesLocalReference table source id := by
  constructor
  · intro result ⟨id, resolved⟩
    have accepted := resolved.complete
    rw [result] at accepted
    cases accepted
  · intro absent
    cases result : resolveLocalReference? table source with
    | none => rfl
    | some output =>
        obtain ⟨id, _, resolved⟩ := resolveLocalReference?_sound result
        exact False.elim (absent ⟨id, resolved⟩)

/-- Replacing only the expression's outer source range has no semantic effect. -/
theorem resolveLocalReference?_span (table : LocalNameTable) (source : Syntax.Expr)
    (span : Syntax.SourceSpan) :
    resolveLocalReference? table { source with span } = resolveLocalReference? table source := by
  cases source with
  | mk sourceSpan payload => cases payload <;> simp only [resolveLocalReference?]

/-- Both occurrence ranges are ignored; equality of exact spellings is sufficient. -/
theorem resolveLocalReference?_identifier_value_eq (table : LocalNameTable)
    {left right : Syntax.Identifier} (same : left.value = right.value)
    (leftSpan rightSpan : Syntax.SourceSpan) :
    resolveLocalReference? table { span := leftSpan, value := .identifier left } =
      resolveLocalReference? table { span := rightSpan, value := .identifier right } := by
  simp only [resolveLocalReference?, same]

theorem resolveLocalReference?_group (table : LocalNameTable) (span : Syntax.SourceSpan)
    (inner : Syntax.Expr) :
    resolveLocalReference? table { span, value := .group inner } = resolveLocalReference? table inner := by
  simp only [resolveLocalReference?]

end Solcore.Frontend
