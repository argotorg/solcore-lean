import Solcore.Frontend.StructuralType
import Solcore.Core.Safety

/-! Independent original-syntax meanings, not interpreter-generated expectations.
Structural results need no whole-type table row or runtime inhabitant. -/
set_option autoImplicit false
namespace Tests.FrontendStructuralType
open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "structural-type.sol"⟩, 0, 1⟩
private def qualified (s : Syntax.SourceSpan) (head : String) (tail : List String := []) : Syntax.QualifiedName :=
  ⟨s, ⟨⟨⟨s, head⟩, tail.map (fun text => ⟨s, text⟩)⟩⟩⟩
private def named (s : Syntax.SourceSpan) (head : String) (tail : List String := []) : Syntax.TypeExpr :=
  ⟨s, .named (qualified s head tail) none⟩
private def unit (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s, .tuple []⟩
private def single (s : Syntax.SourceSpan) (child : Syntax.TypeExpr) : Syntax.TypeExpr := ⟨s, .tuple [child]⟩
private def pair (s : Syntax.SourceSpan) (left right : Syntax.TypeExpr) : Syntax.TypeExpr := ⟨s, .tuple [left, right]⟩
private theorem key (s : Syntax.SourceSpan) (head : String) (tail : List String) :
    qualifiedTypeNameKey (qualified s head tail) = head :: tail := by
  simp [qualifiedTypeNameKey, qualified, Syntax.NonemptyList.toList, List.map_map, Function.comp_def]

theorem four_independent_rules_keep_arbitrary_ranges_tables_and_leaf_types
    (outer childSpan : Syntax.SourceSpan) (table : TypeNameTable) (head : String) (tail : List String)
    (type : Core.Ty) (found : TypeNameTable.Lookup table (head :: tail) type) :
    StructuralTypeDenotes table (named childSpan head tail) type ∧
    StructuralTypeDenotes table (unit outer) .unit ∧
    StructuralTypeDenotes table (single outer (named childSpan head tail)) type ∧
    StructuralTypeDenotes table (pair outer (named childSpan head tail) (unit childSpan)) (.product type .unit) ∧
    interpretStructuralType? table (pair outer (named childSpan head tail) (unit childSpan)) = some (.product type .unit) := by
  have leaf : StructuralTypeDenotes table (named childSpan head tail) type := by
    apply StructuralTypeDenotes.named; simpa only [key] using found
  exact ⟨leaf, .unit, .single leaf, .pair leaf .unit, (StructuralTypeDenotes.pair leaf .unit).complete⟩

private def nested (s : Syntax.SourceSpan) (leaf : Syntax.TypeExpr) : Nat → Syntax.TypeExpr
  | 0 => single s (unit s)
  | n + 1 => pair s (single s leaf) (single s (nested s leaf n))
private def nestedType (leaf : Core.Ty) : Nat → Core.Ty
  | 0 => .unit
  | n + 1 => .product leaf (nestedType leaf n)
private theorem nestedMeaning (s : Syntax.SourceSpan) (table : TypeNameTable)
    (leaf : Syntax.TypeExpr) (type : Core.Ty) (meaning : StructuralTypeDenotes table leaf type) (n : Nat) :
    StructuralTypeDenotes table (nested s leaf n) (nestedType type n) := by
  induction n with
  | zero => exact .single .unit
  | succ n ih => exact .pair (.single meaning) (.single ih)

theorem every_depth_has_the_independently_nested_type_and_unique_meaning
    (s : Syntax.SourceSpan) (table : TypeNameTable) (leaf : Syntax.TypeExpr) (type : Core.Ty)
    (meaning : StructuralTypeDenotes table leaf type) (n : Nat) :
    interpretStructuralType? table (nested s leaf n) = some (nestedType type n) ∧
    StructuralTypeDenotes table (nested s leaf n) (nestedType type n) ∧
    (∀ other, StructuralTypeDenotes table (nested s leaf n) other → other = nestedType type n) := by
  have independent := nestedMeaning s table leaf type meaning n
  have accepted := independent.complete
  exact ⟨accepted, interpretStructuralType?_sound accepted,
    fun _ other => other.type_unique independent⟩

private def aliases : TypeNameTable := [(["L"], .word), (["R"], .bool)]
private theorem leftMeaning : StructuralTypeDenotes aliases (named span "L") .word := .named .head
private theorem rightMeaning : StructuralTypeDenotes aliases (named span "R") .bool :=
  .named (.tail (by decide) .head)

theorem equal_product_shape_does_not_justify_swapping_or_reassociating_types :
    interpretStructuralType? aliases (pair span (named span "L") (named span "R")) = some (.product .word .bool) ∧
    interpretStructuralType? aliases (pair span (named span "R") (named span "L")) = some (.product .bool .word) ∧
    (¬ StructuralTypeDenotes aliases (pair span (named span "L") (named span "R")) (.product .bool .word)) ∧
    interpretStructuralType? aliases (pair span (pair span (named span "L") (named span "R")) (unit span)) =
      some (.product (.product .word .bool) .unit) ∧
    interpretStructuralType? aliases (pair span (pair span (named span "L") (named span "R")) (unit span)) ≠
      some (.product .word (.product .bool .unit)) := by
  have binary := StructuralTypeDenotes.pair (span := span) leftMeaning rightMeaning
  have nested := (StructuralTypeDenotes.pair (span := span) binary (StructuralTypeDenotes.unit (span := span))).complete
  refine ⟨binary.complete, (StructuralTypeDenotes.pair rightMeaning leftMeaning).complete, ?_, nested, ?_⟩
  · intro wrong; cases wrong.type_unique binary
  · intro wrong; cases nested.symm.trans wrong

theorem old_named_provenance_survives_but_whole_structural_membership_is_unnecessary
    (table : TypeNameTable) (source : Syntax.TypeExpr) (type : Core.Ty)
    (old : TypeNameDenotes table source type) :
    (∃ key, (key, type) ∈ table) ∧ StructuralTypeDenotes table source type ∧
    interpretStructuralType? table source = some type ∧
    StructuralTypeDenotes [] (pair span (unit span) (unit span)) (.product .unit .unit) ∧
    (¬ ∃ key, (key, Core.Ty.product .unit .unit) ∈ ([] : TypeNameTable)) ∧
    interpretTypeName? [] (pair span (unit span) (unit span)) = none := by
  exact ⟨old.mem, old.structural, interpretStructuralType?_of_typeName old.complete,
    .pair .unit .unit, by simp, rfl⟩

theorem first_duplicate_wins_inside_a_product_without_builtin_spellings :
    interpretStructuralType? [(["Unit"], .bool), (["Unit"], .word)]
      (pair span (named span "Unit") (unit span)) = some (.product .bool .unit) ∧
    (["Unit"], Core.Ty.word) ∈ [(["Unit"], .bool), (["Unit"], .word)] ∧
    ¬ StructuralTypeDenotes [(["Unit"], .bool), (["Unit"], .word)]
      (pair span (named span "Unit") (unit span)) (.product .word .unit) := by
  have meaning : StructuralTypeDenotes [(["Unit"], .bool), (["Unit"], .word)]
      (pair span (named span "Unit") (unit span)) (.product .bool .unit) := .pair (.named .head) .unit
  refine ⟨meaning.complete, by simp, ?_⟩
  intro wrong; cases wrong.type_unique meaning

theorem qualified_components_raw_dots_and_empty_components_remain_distinct :
    interpretStructuralType? [(["A", "B"], .word), (["A.B"], .bool)]
      (pair span (named span "A" ["B"]) (named span "A.B")) = some (.product .word .bool) ∧
    interpretStructuralType? [(["A", "B"], .word)] (named span "A.B") = none ∧
    interpretStructuralType? [(["A", "", "B"], .unit)] (single span (named span "A" ["", "B"])) = some .unit ∧
    interpretStructuralType? [([], .word)] (named span "") = none ∧
    StructuralTypeDenotes [([""], .bool)] (named span "") .bool := by
  have dotted : StructuralTypeDenotes [(["A", "B"], .word), (["A.B"], .bool)]
      (pair span (named span "A" ["B"]) (named span "A.B")) (.product .word .bool) :=
    .pair (.named .head) (.named (.tail (by decide) .head))
  have emptyComponent : StructuralTypeDenotes [(["A", "", "B"], .unit)]
      (single span (named span "A" ["", "B"])) .unit := .single (.named .head)
  refine ⟨dotted.complete, ?_, emptyComponent.complete, ?_, .named .head⟩ <;>
    simp [interpretStructuralType?, named, key, TypeNameTable.lookup?]

private def reversed : Syntax.SourceSpan := ⟨⟨.external "raw", "invalid"⟩, 99, 2⟩
theorem invalid_ranges_and_outer_range_changes_do_not_change_whole_options
    (file : Syntax.SourceFile) (table : TypeNameTable) (source : Syntax.TypeExpr) :
    (¬ reversed.ValidFor file) ∧
    StructuralTypeDenotes table (pair reversed (single reversed (unit reversed)) (unit reversed)) (.product .unit .unit) ∧
    interpretStructuralType? table { source with span := reversed } = interpretStructuralType? table source := by
  exact ⟨by simp [Syntax.SourceSpan.ValidFor, reversed], .pair (.single .unit) .unit,
    interpretStructuralType?_span table source reversed⟩

theorem nominal_structural_types_need_neither_well_formed_data_nor_runtime_inhabitants
    (nominal : Core.DataTypeId) (definitions : Core.DataEnvironment) :
    StructuralTypeDenotes [(["N"], .namedData nominal)]
      (pair span (named span "N") (unit span)) (.product (.namedData nominal) .unit) ∧
    Core.HasType [.namedData nominal] (.pair (.var 0) .unit) (.product (.namedData nominal) .unit) definitions ∧
    (¬ ∃ actual, Core.ValueHasType actual (.namedData nominal)) := by
  refine ⟨.pair (.named .head) .unit, .pair (.var rfl) .unit, ?_⟩
  rintro ⟨actual, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def unsupported (child : Syntax.TypeExpr) : List Syntax.TypeExprValue :=
  [.named (qualified span "Known") (some ⟨span, ⟨child, []⟩⟩), .mapping span span child child,
   .proxy span child, .comptime span span child, .error]
theorem unsupported_constructors_cannot_be_rescued_by_meaningful_children
    (table : TypeNameTable) (child : Syntax.TypeExpr) (type : Core.Ty)
    (meaning : StructuralTypeDenotes table child type) (payload : Syntax.TypeExprValue)
    (present : payload ∈ unsupported child) (outer : Syntax.SourceSpan) :
    interpretStructuralType? table child = some type ∧ interpretStructuralType? table ⟨outer, payload⟩ = none ∧
    ¬ ∃ result, StructuralTypeDenotes table ⟨outer, payload⟩ result := by
  refine ⟨meaning.complete, ?_⟩
  simp only [unsupported, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp only [interpretStructuralType?], by rintro ⟨result, denoted⟩; cases denoted⟩

theorem larger_tuples_remain_named_only_rejections_and_missing_children_stay_strict
    (table : TypeNameTable) (a b c : Syntax.TypeExpr) (rest : List Syntax.TypeExpr) :
    interpretTypeName? table ⟨span, .tuple (a :: b :: c :: rest)⟩ = none ∧
    interpretStructuralType? [] (pair span (unit span) (named span "Missing")) = none ∧
    interpretStructuralType? [] (pair span (named span "Missing") (unit span)) = none ∧
    (¬ ∃ type, StructuralTypeDenotes [] (pair span (unit span) (named span "Missing")) type) ∧
    interpretTypeName? aliases (single span (named span "L")) = none ∧
    interpretStructuralType? aliases (single span (named span "L")) = some .word := by
  have absent : interpretStructuralType? [] (pair span (unit span) (named span "Missing")) = none := by
    simp [interpretStructuralType?, pair, unit, named, TypeNameTable.lookup?]
  refine ⟨rfl, absent, ?_, interpretStructuralType?_eq_none_iff.mp absent, rfl,
    (StructuralTypeDenotes.single leftMeaning).complete⟩ <;>
    simp [interpretStructuralType?, pair, unit, named, TypeNameTable.lookup?]

theorem arbitrary_nested_success_survives_append_and_fresh_prepend
    (table extras : TypeNameTable) (leaf : Syntax.TypeExpr) (type : Core.Ty)
    (meaning : StructuralTypeDenotes table leaf type) (n : Nat) (key : List String) (newType : Core.Ty)
    (fresh : key ∉ table.map Prod.fst) :
    StructuralTypeDenotes (table ++ extras) (nested span leaf n) (nestedType type n) ∧
    interpretStructuralType? ((key, newType) :: table) (nested span leaf n) = some (nestedType type n) := by
  have independent := nestedMeaning span table leaf type meaning n
  exact ⟨independent.extend_types (TypeNameTable.Extends.append_right table extras),
    interpretStructuralType?_some_of_extends (TypeNameTable.Extends.cons_fresh table key newType fresh) independent.complete⟩

private def one : TypeNameTable := [(["T"], .word)]
private def hiddenConflict : TypeNameTable := [(["T"], .word), (["T"], .bool)]
private theorem forward : TypeNameTable.Extends one hiddenConflict := TypeNameTable.Extends.append_right one [(["T"], .bool)]
private theorem backward : TypeNameTable.Extends hiddenConflict one := by
  intro key type found
  cases found with
  | head => exact .head
  | tail different found =>
      cases found with
      | head => exact False.elim (different rfl)
      | tail _ impossible => cases impossible

theorem unequal_tables_with_hidden_conflicts_preserve_every_optional_result (source : Syntax.TypeExpr) :
    one ≠ hiddenConflict ∧ TypeNameTable.Extends one hiddenConflict ∧ TypeNameTable.Extends hiddenConflict one ∧
    interpretStructuralType? one source = interpretStructuralType? hiddenConflict source ∧
    interpretStructuralType? hiddenConflict source = interpretStructuralType? one source ∧
    interpretStructuralType? hiddenConflict (pair span (unit span) (named span "Missing")) = none := by
  exact ⟨by decide, forward, backward,
    interpretStructuralType?_eq_of_mutual_extends forward backward source,
    interpretStructuralType?_congr_lookup hiddenConflict one
      (TypeNameTable.lookup?_eq_of_mutual_extends backward forward) source,
    by simp [interpretStructuralType?, pair, unit, named, key, hiddenConflict, TypeNameTable.lookup?]⟩

theorem one_way_extension_can_repair_an_unknown_child_but_head_override_is_not_extension :
    TypeNameTable.Extends [] [(["Missing"], .word)] ∧
    interpretStructuralType? [] (pair span (unit span) (named span "Missing")) = none ∧
    interpretStructuralType? [(["Missing"], .word)] (pair span (unit span) (named span "Missing")) =
      some (.product .unit .word) ∧
    (¬ TypeNameTable.Extends one ((["T"], .bool) :: one)) ∧
    (["T"], Core.Ty.word) ∈ ((["T"], .bool) :: one) := by
  have repaired : StructuralTypeDenotes [(["Missing"], .word)]
      (pair span (unit span) (named span "Missing")) (.product .unit .word) := .pair .unit (.named .head)
  refine ⟨TypeNameTable.Extends.cons_fresh [] ["Missing"] .word (by simp),
    by simp [interpretStructuralType?, pair, unit, named, TypeNameTable.lookup?],
    repaired.complete, ?_, by simp [one]⟩
  intro extension
  have wrong : TypeNameTable.Lookup ((["T"], .bool) :: one) ["T"] .word := extension .head
  have first : TypeNameTable.Lookup ((["T"], .bool) :: one) ["T"] .bool := .head
  cases wrong.type_unique first

theorem exact_executable_acceptance_is_the_independent_original_syntax_relation
    (table : TypeNameTable) (source : Syntax.TypeExpr) (type : Core.Ty)
    (name : Syntax.QualifiedName) (outer : Syntax.SourceSpan) :
    (interpretStructuralType? table source = some type ↔ StructuralTypeDenotes table source type) ∧
    (interpretStructuralType? table source = none ↔ ¬ ∃ result, StructuralTypeDenotes table source result) ∧
    interpretStructuralType? table ⟨outer, .named name none⟩ = interpretTypeName? table ⟨outer, .named name none⟩ :=
  ⟨interpretStructuralType?_iff, interpretStructuralType?_eq_none_iff,
    interpretStructuralType?_named_eq_typeName table name outer⟩

end Tests.FrontendStructuralType
