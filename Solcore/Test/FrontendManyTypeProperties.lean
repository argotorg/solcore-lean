import Solcore.Frontend.StructuralType
import Solcore.Core.Safety

/-! Original finite type lists have an independent source-order meaning.
The final written type is not followed by an implicit Unit, and explicit
nested products remain distinct. Static meanings do not create runtime values. -/
set_option autoImplicit false
namespace Tests.FrontendManyType
open Solcore Solcore.Frontend

private def folded : List Core.Ty → Core.Ty
  | [] => .unit
  | [type] => type
  | type :: next :: rest => .product type (folded (next :: rest))
private def tuple (span : Syntax.SourceSpan) (elements : List Syntax.TypeExpr) : Syntax.TypeExpr :=
  ⟨span, .tuple elements⟩
private def named (span : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private inductive ChildMeanings (table : TypeNameTable) : List Syntax.TypeExpr → List Core.Ty → Prop where
  | nil : ChildMeanings table [] []
  | cons {child : Syntax.TypeExpr} {type : Core.Ty} {rest : List Syntax.TypeExpr} {types : List Core.Ty}
      (head : StructuralTypeDenotes table child type) (tail : ChildMeanings table rest types) :
      ChildMeanings table (child :: rest) (type :: types)
private theorem listMeaning {table : TypeNameTable} {elements : List Syntax.TypeExpr} {types : List Core.Ty}
    (children : ChildMeanings table elements types) (span : Syntax.SourceSpan) :
    StructuralTypeDenotes table (tuple span elements) (folded types) := by
  induction children with
  | nil => exact .unit
  | @cons first firstType rest restTypes head tail ih =>
      cases tail with
      | nil => exact .single head
      | @cons second secondType remaining remainingTypes secondMeaning others =>
          cases others with
          | nil => exact .pair head secondMeaning
          | cons thirdMeaning final => exact .many head ih

private theorem everyChild {table : TypeNameTable} {source : Syntax.TypeExpr} {type : Core.Ty}
    (meaning : StructuralTypeDenotes table source type) :
    ∀ span elements, source = tuple span elements →
      ∀ child ∈ elements, ∃ childType, StructuralTypeDenotes table child childType := by
  induction meaning with
  | named found => intro span elements same; cases same
  | unit => intro span elements same child member; cases same; cases member
  | single meaning _ =>
      intro span elements same child member
      cases same
      simp only [List.mem_singleton] at member
      subst child
      exact ⟨_, meaning⟩
  | pair left right _ _ =>
      intro span elements same child member
      cases same
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨_, left⟩
      · exact ⟨_, right⟩
  | many head tail _ tailIH =>
      intro span elements same child member
      cases same
      rcases List.mem_cons.mp member with rfl | remaining
      · exact ⟨_, head⟩
      · exact tailIH _ _ rfl child remaining
  | functionDefault _ _ => intro span elements same; cases same
  | functionReturns _ _ _ _ => intro span elements same; cases same

theorem arbitrary_finite_lists_have_independent_right_associated_meaning
    (table : TypeNameTable) (span : Syntax.SourceSpan) (elements : List Syntax.TypeExpr) (types : List Core.Ty)
    (children : ChildMeanings table elements types) :
    StructuralTypeDenotes table (tuple span elements) (folded types) ∧
    interpretStructuralType? table (tuple span elements) = some (folded types) ∧
    elements.length = types.length ∧ (tuple span elements).value = .tuple elements := by
  have lengths : elements.length = types.length := by
    induction children with
    | nil => rfl
    | cons _ _ ih => exact congrArg Nat.succ ih
  exact ⟨listMeaning children span, (listMeaning children span).complete, lengths, rfl⟩

theorem three_original_children_use_many_without_an_extra_terminal_unit
    (table : TypeNameTable) (span : Syntax.SourceSpan) (a b c : Syntax.TypeExpr) (x y z : Core.Ty)
    (first : StructuralTypeDenotes table a x) (second : StructuralTypeDenotes table b y)
    (third : StructuralTypeDenotes table c z) :
    StructuralTypeDenotes table (tuple span [a,b,c]) (.product x (.product y z)) ∧
    interpretStructuralType? table (tuple span [a,b,c]) = some (.product x (.product y z)) ∧
    interpretTypeName? table (tuple span [a,b,c]) = none := by
  have meaning : StructuralTypeDenotes table (tuple span [a,b,c]) (.product x (.product y z)) :=
    .many first (.pair second third)
  exact ⟨meaning, interpretStructuralType?_iff.mpr meaning, rfl⟩

theorem one_missing_original_child_rejects_every_prefix_and_suffix
    (table : TypeNameTable) (span : Syntax.SourceSpan) (before after : List Syntax.TypeExpr) (missing : Syntax.TypeExpr)
    (absent : ¬ ∃ type, StructuralTypeDenotes table missing type) :
    interpretStructuralType? table (tuple span (before ++ missing :: after)) = none ∧
    ¬ ∃ type, StructuralTypeDenotes table (tuple span (before ++ missing :: after)) type := by
  have rejected : ¬ ∃ type, StructuralTypeDenotes table (tuple span (before ++ missing :: after)) type := by
    rintro ⟨type, meaning⟩
    exact absent (everyChild meaning span _ rfl missing (by simp))
  exact ⟨interpretStructuralType?_eq_none_iff.mpr rejected, rejected⟩

private def table : TypeNameTable := [(["A"], .word), (["B"], .bool), (["C"], .unit)]
private theorem three (s : Syntax.SourceSpan) : StructuralTypeDenotes table
    (tuple s [named s "A", named s "B", named s "C"]) (.product .word (.product .bool .unit)) :=
  .many (.named .head) (.pair (.named (.tail (by change ["A"] ≠ ["B"]; decide) .head))
    (.named (.tail (by change ["A"] ≠ ["C"]; decide) (.tail (by change ["B"] ≠ ["C"]; decide) .head))))

theorem explicit_nested_association_is_not_flattened_or_completed_with_unit (span : Syntax.SourceSpan) :
    interpretStructuralType? table (tuple span [named span "A",named span "B",named span "C"]) =
      some (.product .word (.product .bool .unit)) ∧
    interpretStructuralType? table (tuple span [tuple span [named span "A",named span "B"],named span "C"]) =
      some (.product (.product .word .bool) .unit) ∧
    (.product .word (.product .bool .unit) : Core.Ty) ≠ .product (.product .word .bool) .unit ∧
    (.product .word (.product .bool .unit) : Core.Ty) ≠ .product .word (.product .bool (.product .unit .unit)) := by
  have nested : StructuralTypeDenotes table
      (tuple span [tuple span [named span "A",named span "B"],named span "C"]) (.product (.product .word .bool) .unit) :=
    .pair (.pair (.named .head) (.named (.tail (by change ["A"] ≠ ["B"]; decide) .head)))
      (.named (.tail (by change ["A"] ≠ ["C"]; decide) (.tail (by change ["B"] ≠ ["C"]; decide) .head)))
  exact ⟨(three span).complete, nested.complete, by decide, by decide⟩

theorem meaningful_children_do_not_allow_a_wrong_result_for_the_same_flat_source (span : Syntax.SourceSpan) :
    ¬ StructuralTypeDenotes table (tuple span [named span "A",named span "B",named span "C"])
      (.product (.product .word .bool) .unit) := by
  intro wrong
  cases wrong.type_unique (three span)

private def qualified (s : Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s, .named ⟨s, ⟨⟨⟨s,"Pkg"⟩,[⟨s,"A"⟩]⟩⟩⟩ none⟩
private def aliases (x y hidden : Core.Ty) : TypeNameTable :=
  [(["A"],x), (["Pkg","A"],y), (["A"],hidden), (["Pkg.A"],.unit)]
private theorem aliasMeaning (span : Syntax.SourceSpan) (x y hidden : Core.Ty) :
    StructuralTypeDenotes (aliases x y hidden) (tuple span [named span "A",qualified span,named span "A"])
      (.product x (.product y x)) :=
  .many (.named .head) (.pair (.named (.tail (by change ["A"] ≠ ["Pkg","A"]; decide) .head)) (.named .head))

theorem every_original_leaf_uses_the_same_first_match_table_and_qualified_components
    (span : Syntax.SourceSpan) (x y hidden : Core.Ty) :
    interpretStructuralType? (aliases x y hidden) (tuple span [named span "A",qualified span,named span "A"]) =
      some (.product x (.product y x)) ∧
    (aliases x y hidden).lookup? ["A"] = some x ∧
    (aliases x y hidden).lookup? ["Pkg","A"] = some y ∧
    (aliases x y hidden).lookup? ["Pkg.A"] = some .unit :=
  ⟨(aliasMeaning span x y hidden).complete, rfl, rfl, rfl⟩

theorem arbitrary_ranges_and_lookup_equality_preserve_the_full_optional_result
    (left right : TypeNameTable) (same : ∀ key, left.lookup? key = right.lookup? key)
    (original replacement : Syntax.SourceSpan) (a b c : Syntax.TypeExpr) (rest : List Syntax.TypeExpr) :
    interpretStructuralType? left (tuple replacement (a :: b :: c :: rest)) =
      interpretStructuralType? right (tuple original (a :: b :: c :: rest)) ∧
    (tuple replacement (a :: b :: c :: rest)).value = (tuple original (a :: b :: c :: rest)).value := by
  exact ⟨(interpretStructuralType?_span left (tuple original (a :: b :: c :: rest)) replacement).trans
    (interpretStructuralType?_congr_lookup left right same _), rfl⟩

theorem successful_extension_and_mutual_full_options_keep_right_association
    (old next : TypeNameTable) (extension : TypeNameTable.Extends old next) (span : Syntax.SourceSpan)
    (elements : List Syntax.TypeExpr) (types : List Core.Ty)
    (children : ChildMeanings old elements types) :
    StructuralTypeDenotes next (tuple span elements) (folded types) ∧
    interpretStructuralType? next (tuple span elements) = some (folded types) ∧
    (TypeNameTable.Extends next old → ∀ source,
      interpretStructuralType? old source = interpretStructuralType? next source) :=
  ⟨(listMeaning children span).extend_types extension,
    interpretStructuralType?_some_of_extends extension (listMeaning children span).complete,
    fun back source => interpretStructuralType?_eq_of_mutual_extends extension back source⟩

theorem one_way_extension_can_repair_an_original_middle_leaf (span : Syntax.SourceSpan) (type : Core.Ty) :
    TypeNameTable.Extends [] [(["N"],type)] ∧
    interpretStructuralType? [] (tuple span [tuple span [],named span "N",tuple span []]) = none ∧
    interpretStructuralType? [(["N"],type)] (tuple span [tuple span [],named span "N",tuple span []]) =
      some (.product .unit (.product type .unit)) := by
  have absent : ¬ ∃ type, StructuralTypeDenotes [] (named span "N") type := by
    rintro ⟨type, meaning⟩
    cases meaning with | named found => cases found
  have repaired : StructuralTypeDenotes [(["N"],type)]
      (tuple span [tuple span [],named span "N",tuple span []]) (.product .unit (.product type .unit)) :=
    .many .unit (.pair (.named .head) .unit)
  exact ⟨TypeNameTable.Extends.append_right [] _,
    (one_missing_original_child_rejects_every_prefix_and_suffix [] span [tuple span []] [tuple span []] _ absent).1,
    repaired.complete⟩

theorem empty_table_products_need_no_whole_result_membership (span : Syntax.SourceSpan) :
    interpretStructuralType? [] (tuple span [tuple span [],tuple span [],tuple span []]) =
      some (.product .unit (.product .unit .unit)) ∧
    (¬ ∃ key, (key, Core.Ty.product .unit (.product .unit .unit)) ∈ ([] : TypeNameTable)) ∧
    interpretTypeName? [] (tuple span [tuple span [],tuple span [],tuple span []]) = none := by
  have meaning : StructuralTypeDenotes [] (tuple span [tuple span [],tuple span [],tuple span []])
      (.product .unit (.product .unit .unit)) := .many .unit (.pair .unit .unit)
  exact ⟨meaning.complete, by simp, rfl⟩

private theorem repeatedMeaning (nominal : Core.DataTypeId) (span : Syntax.SourceSpan) (n : Nat) :
    ChildMeanings [(["N"], .namedData nominal)]
      (List.replicate n (named span "N")) (List.replicate n (.namedData nominal)) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons (.named .head) ih
private theorem repeatedUninhabited (nominal : Core.DataTypeId) (n : Nat) :
    ¬ ∃ value, Core.ValueHasType value (folded (List.replicate (n + 1) (.namedData nominal))) := by
  induction n with
  | zero =>
      rintro ⟨value, typed⟩
      cases typed with
      | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  | succ n ih => rintro ⟨value, typed⟩; cases typed with | pair _ right => exact ih ⟨_,right⟩

theorem arbitrarily_long_nominal_types_remain_static_without_runtime_inhabitants
    (nominal : Core.DataTypeId) (span : Syntax.SourceSpan) (n : Nat) (definitions : Core.DataEnvironment) :
    StructuralTypeDenotes [(["N"], .namedData nominal)] (tuple span (List.replicate (n + 1) (named span "N")))
      (folded (List.replicate (n + 1) (.namedData nominal))) ∧
    Core.HasType [folded (List.replicate (n + 1) (.namedData nominal))] (.var 0)
      (folded (List.replicate (n + 1) (.namedData nominal))) definitions ∧
    ¬ ∃ value, Core.ValueHasType value (folded (List.replicate (n + 1) (.namedData nominal))) :=
  ⟨listMeaning (repeatedMeaning nominal span (n + 1)) span, .var rfl, repeatedUninhabited nominal n⟩

end Tests.FrontendManyType
