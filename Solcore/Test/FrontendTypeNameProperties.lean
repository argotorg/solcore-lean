import Solcore.Frontend.TypeNameProperties

/-! ADR-0167 consumers: an explicit ordered table interprets exact components.
No spelling or source-range validity is required, and unsupported shapes remain
outside this adapter even when their child types have supplied meanings. -/

set_option autoImplicit false

namespace Tests.FrontendTypeName

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "type-name.sol"⟩, 0, 4⟩
private def qualified (nameSpan componentSpan : Syntax.SourceSpan)
    (head : String) (tail : List String) : Syntax.QualifiedName :=
  ⟨nameSpan, ⟨⟨⟨componentSpan, head⟩, tail.map (fun text => ⟨componentSpan, text⟩)⟩⟩⟩
private def named (head : String) (tail : List String := []) : Syntax.TypeExpr :=
  ⟨span, .named (qualified span span head tail) none⟩

private theorem qualified_key (nameSpan componentSpan : Syntax.SourceSpan)
    (head : String) (tail : List String) :
    qualifiedTypeNameKey (qualified nameSpan componentSpan head tail) = head :: tail := by
  simp [qualifiedTypeNameKey, qualified, Syntax.NonemptyList.toList, List.map_map, Function.comp_def]

theorem any_core_type_can_be_assigned_to_any_nonempty_component_sequence
    (head : String) (tail : List String) (type : Core.Ty) (rest : TypeNameTable)
    (outer nameSpan componentSpan : Syntax.SourceSpan) :
    qualifiedTypeNameKey (qualified nameSpan componentSpan head tail) = head :: tail ∧
    TypeNameDenotes (((head :: tail), type) :: rest)
      ⟨outer, .named (qualified nameSpan componentSpan head tail) none⟩ type ∧
    interpretTypeName? (((head :: tail), type) :: rest)
      ⟨outer, .named (qualified nameSpan componentSpan head tail) none⟩ = some type := by
  have meaning : TypeNameDenotes (((head :: tail), type) :: rest)
      ⟨outer, .named (qualified nameSpan componentSpan head tail) none⟩ type := by
    apply TypeNameDenotes.named
    rw [qualified_key]
    exact .head
  exact ⟨qualified_key nameSpan componentSpan head tail, meaning,
    meaning.complete⟩

private def aliases : TypeNameTable := [(["Word"], .bool), (["Alias"], .bool), (["Word"], .word)]
private theorem wordMeaning : TypeNameDenotes aliases (named "Word") .bool := .named .head
private theorem aliasMeaning : TypeNameDenotes aliases (named "Alias") .bool :=
  .named (.tail (by decide) .head)

theorem caller_assignments_allow_aliases_and_first_duplicate_wins :
    TypeNameDenotes aliases (named "Word") .bool ∧
    TypeNameDenotes aliases (named "Alias") .bool ∧
    interpretTypeName? aliases (named "Word") = some .bool ∧
    interpretTypeName? aliases (named "Alias") = some .bool ∧
    (["Word"], Core.Ty.word) ∈ aliases ∧
    ¬ TypeNameDenotes aliases (named "Word") .word := by
  refine ⟨wordMeaning, aliasMeaning, wordMeaning.complete,
    aliasMeaning.complete, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
  intro wrong
  have accepted := wrong.complete
  have first := wordMeaning.complete
  rw [first] at accepted
  cases accepted

theorem unknown_names_have_no_reserved_fallback (name : Syntax.QualifiedName)
    (outer : Syntax.SourceSpan) :
    interpretTypeName? [] ⟨outer, .named name none⟩ = none ∧
    (¬ ∃ type, TypeNameDenotes [] ⟨outer, .named name none⟩ type) ∧
    interpretTypeName? [(["Bool"], .word)] (named "Word") = none ∧
    TypeNameDenotes [(["Bool"], .word)] (named "Bool") .word := by
  refine ⟨rfl, ?_, by decide, .named .head⟩
  rintro ⟨type, meaning⟩
  cases meaning with | named found => cases found

private def unsupported (child : Syntax.TypeExpr) : List Syntax.TypeExprValue :=
  [.named (qualified span span "Word" []) (some ⟨span, ⟨child, []⟩⟩),
   .mapping span span child child, .proxy span child,
   .function span ⟨span, [child]⟩ (some ⟨span, [child]⟩),
   .comptime span span child, .tuple [child], .error]

theorem every_other_shape_is_outside_the_adapter_even_with_a_meaningful_child
    (table : TypeNameTable) (child : Syntax.TypeExpr) (childType : Core.Ty)
    (childMeaning : TypeNameDenotes table child childType)
    (payload : Syntax.TypeExprValue) (present : payload ∈ unsupported child)
    (outer : Syntax.SourceSpan) :
    interpretTypeName? table child = some childType ∧
    interpretTypeName? table ⟨outer, payload⟩ = none ∧
    ¬ ∃ type, TypeNameDenotes table ⟨outer, payload⟩ type := by
  refine ⟨childMeaning.complete, ?_⟩
  simp only [unsupported, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, by rintro ⟨type, meaning⟩; cases meaning⟩

theorem raw_dots_and_empty_components_are_not_normalized :
    qualifiedTypeNameKey (qualified span span "A.B" []) = ["A.B"] ∧
    qualifiedTypeNameKey (qualified span span "A" ["B"]) = ["A", "B"] ∧
    interpretTypeName? [(["A", "B"], .word)] (named "A.B") = none ∧
    interpretTypeName? [(["A.B"], .bool)] (named "A" ["B"]) = none ∧
    interpretTypeName? [(["A", "", "B"], .unit)] (named "A" ["", "B"]) = some .unit ∧
    interpretTypeName? [(["A", "B"], .word)] (named "A" ["", "B"]) = none ∧
    interpretTypeName? [([], .word)] (named "") = none ∧
    TypeNameDenotes [([""], .bool)] (named "") .bool := by
  exact ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, .named .head⟩

private def nonMatchingSpellings : List String :=
  ["word", "WORD", " Word", "Word ", "Ｗord", "Wоrd", "é"]

theorem case_space_and_unicode_payloads_are_matched_exactly
    (spelling : String) (present : spelling ∈ nonMatchingSpellings) :
    interpretTypeName? [(["Word"], .word), (["é"], .bool)] (named spelling) = none ∧
    ¬ ∃ type, TypeNameDenotes [(["Word"], .word), (["é"], .bool)] (named spelling) type := by
  have allRejected : ∀ candidate ∈ nonMatchingSpellings,
      interpretTypeName? [(["Word"], .word), (["é"], .bool)] (named candidate) = none := by decide
  have rejected := allRejected spelling present
  refine ⟨rejected, ?_⟩
  rintro ⟨type, meaning⟩
  have accepted := meaning.complete
  rw [rejected] at accepted
  cases accepted

theorem arbitrary_range_changes_preserve_success_failure_and_independent_meaning
    (table : TypeNameTable) (head : String) (tail : List String) (type : Core.Ty)
    (outer otherOuter nameSpan otherNameSpan componentSpan otherComponentSpan : Syntax.SourceSpan) :
    interpretTypeName? table ⟨outer, .named (qualified nameSpan componentSpan head tail) none⟩ =
      interpretTypeName? table ⟨otherOuter, .named (qualified otherNameSpan otherComponentSpan head tail) none⟩ ∧
    (TypeNameDenotes table ⟨outer, .named (qualified nameSpan componentSpan head tail) none⟩ type ↔
      TypeNameDenotes table ⟨otherOuter, .named (qualified otherNameSpan otherComponentSpan head tail) none⟩ type) := by
  have same : interpretTypeName? table ⟨outer, .named (qualified nameSpan componentSpan head tail) none⟩ =
      interpretTypeName? table ⟨otherOuter, .named (qualified otherNameSpan otherComponentSpan head tail) none⟩ := by
    exact interpretTypeName?_key_eq table (by rw [qualified_key, qualified_key]) outer otherOuter
  exact ⟨same, by rw [← interpretTypeName?_iff, ← interpretTypeName?_iff, same]⟩

private def reversed : Syntax.SourceSpan := ⟨⟨.external "raw", "not-a-validated-path"⟩, 99, 2⟩
theorem invalid_ranges_do_not_prevent_explicit_interpretation (file : Syntax.SourceFile) :
    (¬ reversed.ValidFor file) ∧
    TypeNameDenotes [(["Word"], .bool)]
      ⟨reversed, .named (qualified reversed reversed "Word" []) none⟩ .bool ∧
    interpretTypeName? [(["Word"], .bool)]
      ⟨reversed, .named (qualified reversed reversed "Word" []) none⟩ = some .bool := by
  have meaning : TypeNameDenotes [(["Word"], .bool)]
      ⟨reversed, .named (qualified reversed reversed "Word" []) none⟩ .bool := .named .head
  exact ⟨by simp [Syntax.SourceSpan.ValidFor, reversed], meaning, meaning.complete⟩

theorem successful_results_recover_unique_independent_meaning_and_table_provenance
    (table : TypeNameTable) (source : Syntax.TypeExpr) (type : Core.Ty)
    (accepted : interpretTypeName? table source = some type) :
    TypeNameDenotes table source type ∧
    (∃ key, (key, type) ∈ table) ∧
    (∀ other, TypeNameDenotes table source other → other = type) ∧
    ¬ interpretTypeName? table source = none := by
  have meaning := interpretTypeName?_iff.mp accepted
  refine ⟨meaning, meaning.mem, ?_, ?_⟩
  · intro other otherMeaning
    exact otherMeaning.type_unique meaning
  · intro rejected
    exact (interpretTypeName?_eq_none_iff.mp rejected) ⟨type, meaning⟩

end Tests.FrontendTypeName
