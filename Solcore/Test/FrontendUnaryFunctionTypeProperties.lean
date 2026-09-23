import Solcore.Frontend.StructuralType
import Solcore.Core.Safety

/-! Original unary annotations have independently constructed meanings. Return-list
packing never changes source parameter arity, and meaning does not supply an inhabitant. -/
set_option autoImplicit false
namespace Tests.FrontendUnaryFunctionType
open Solcore Solcore.Frontend
private def span : Syntax.SourceSpan := ⟨⟨.main,"structural-type.sol"⟩,0,1⟩
private def named (s : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr :=
  ⟨s,.named ⟨s,⟨⟨⟨s,name⟩,[]⟩⟩⟩ none⟩
private structure Ranges where
  outer : Syntax.SourceSpan
  keyword : Syntax.SourceSpan
  parameters : Syntax.SourceSpan
  returns : Syntax.SourceSpan
private def original (s : Ranges) (parameter : Syntax.TypeExpr)
    (results : Option (List Syntax.TypeExpr)) : Syntax.TypeExpr :=
  ⟨s.outer,.function s.keyword ⟨s.parameters,[parameter]⟩ (results.map (⟨s.returns,·⟩))⟩
private def product : List Core.Ty → Core.Ty
  | [] => .unit
  | [type] => type
  | first::second::rest => .product first (product (second::rest))
private theorem listMeaning (table : TypeNameTable) (s : Syntax.SourceSpan)
    (entries : List (Syntax.TypeExpr × Core.Ty))
    (means : ∀ entry ∈ entries, StructuralTypeDenotes table entry.1 entry.2) :
    StructuralTypeDenotes table ⟨s,.tuple (entries.map Prod.fst)⟩ (product (entries.map Prod.snd)) := by
  revert means
  induction entries with
  | nil => intro _; exact .unit
  | cons entry rest ih =>
      intro means
      have head := means entry (by simp)
      have tail := ih (fun child member => means child (by simp [member]))
      cases rest with
      | nil => exact .single head
      | cons second remaining =>
          cases remaining with
          | nil => exact .pair head (means second (by simp))
          | cons third remaining => exact .many head tail

theorem absent_empty_and_singleton_returns_keep_the_original_fields
    (s : Ranges) (table : TypeNameTable) (parameter result : Syntax.TypeExpr) (A B : Core.Ty)
    (pa : StructuralTypeDenotes table parameter A) (rb : StructuralTypeDenotes table result B) :
    StructuralTypeDenotes table (original s parameter none) (.function A .unit) ∧
    StructuralTypeDenotes table (original s parameter (some [])) (.function A .unit) ∧
    StructuralTypeDenotes table (original s parameter (some [result])) (.function A B) ∧
    original s parameter none ≠ original s parameter (some []) :=
  ⟨.functionDefault pa,.functionReturns pa .unit,.functionReturns pa (.single rb),by simp [original]⟩

theorem arbitrary_written_return_count_has_one_parameter_and_no_terminal_unit
    (s : Ranges) (table : TypeNameTable) (parameter : Syntax.TypeExpr) (A : Core.Ty)
    (pa : StructuralTypeDenotes table parameter A) (entries : List (Syntax.TypeExpr × Core.Ty))
    (means : ∀ entry ∈ entries, StructuralTypeDenotes table entry.1 entry.2) :
    StructuralTypeDenotes table (original s parameter (some (entries.map Prod.fst)))
      (.function A (product (entries.map Prod.snd))) ∧
    interpretStructuralType? table (original s parameter (some (entries.map Prod.fst))) =
      some (.function A (product (entries.map Prod.snd))) := by
  have independent : StructuralTypeDenotes table (original s parameter (some (entries.map Prod.fst)))
      (.function A (product (entries.map Prod.snd))) := .functionReturns pa (listMeaning table s.returns entries means)
  exact ⟨independent,independent.complete⟩

private def nested (s : Nat → Ranges) (parameter result : Syntax.TypeExpr) : Nat → Syntax.TypeExpr
  | 0 => result
  | n+1 => original (s n) parameter (some [nested s parameter result n])
private def nestedType (A B : Core.Ty) : Nat → Core.Ty
  | 0 => B
  | n+1 => .function A (nestedType A B n)
private theorem nestedMeaning (s : Nat → Ranges) (table : TypeNameTable)
    (parameter result : Syntax.TypeExpr) (A B : Core.Ty)
    (pa : StructuralTypeDenotes table parameter A) (rb : StructuralTypeDenotes table result B) (n : Nat) :
    StructuralTypeDenotes table (nested s parameter result n) (nestedType A B n) := by
  induction n with | zero => exact rb | succ _ ih => exact .functionReturns pa (.single ih)
theorem arbitrary_function_nesting_is_independent_and_unique
    (s : Nat → Ranges) (table : TypeNameTable) (parameter result : Syntax.TypeExpr) (A B : Core.Ty)
    (pa : StructuralTypeDenotes table parameter A) (rb : StructuralTypeDenotes table result B) (n : Nat) :
    StructuralTypeDenotes table (nested s parameter result n) (nestedType A B n) ∧
    interpretStructuralType? table (nested s parameter result n) = some (nestedType A B n) ∧
    ∀ other, StructuralTypeDenotes table (nested s parameter result n) other → other=nestedType A B n := by
  have independent := nestedMeaning s table parameter result A B pa rb n
  exact ⟨independent,independent.complete,fun _ other => other.type_unique independent⟩

theorem explicit_product_parameter_is_not_a_multi_parameter_function
    (s : Ranges) (table : TypeNameTable) (left right : Syntax.TypeExpr) (A B : Core.Ty)
    (la : StructuralTypeDenotes table left A) (rb : StructuralTypeDenotes table right B) :
    StructuralTypeDenotes table (original s ⟨s.parameters,.tuple [left,right]⟩ none)
      (.function (.product A B) .unit) ∧
    StructuralTypeDenotes table (original s ⟨s.parameters,.tuple []⟩ none) (.function .unit .unit) ∧
    interpretStructuralType? table ⟨s.outer,.function s.keyword ⟨s.parameters,[left,right]⟩ none⟩=none ∧
    interpretStructuralType? table ⟨s.outer,.function s.keyword ⟨s.parameters,[]⟩ none⟩=none := by
  refine ⟨.functionDefault (.pair la rb),.functionDefault .unit,?_,?_⟩ <;>
    simp only [interpretStructuralType?]

theorem zero_and_multiple_parameters_cannot_be_rescued_by_any_return_list
    (s : Ranges) (table : TypeNameTable) (left right : Syntax.TypeExpr) (rest : List Syntax.TypeExpr)
    (returns : Option (Syntax.DelimitedList Syntax.TypeExpr)) :
    interpretStructuralType? table ⟨s.outer,.function s.keyword ⟨s.parameters,[]⟩ returns⟩=none ∧
    interpretStructuralType? table ⟨s.outer,.function s.keyword ⟨s.parameters,left::right::rest⟩ returns⟩=none ∧
    (¬ ∃ t, StructuralTypeDenotes table ⟨s.outer,.function s.keyword ⟨s.parameters,[]⟩ returns⟩ t) ∧
    (¬ ∃ t, StructuralTypeDenotes table ⟨s.outer,.function s.keyword ⟨s.parameters,left::right::rest⟩ returns⟩ t) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [interpretStructuralType?]
  · simp only [interpretStructuralType?]
  · rintro ⟨_,h⟩; cases h
  · rintro ⟨_,h⟩; cases h

theorem original_private_unsupported_member_now_has_its_independent_positive
    (table : TypeNameTable) (child : Syntax.TypeExpr) (type : Core.Ty)
    (meaning : StructuralTypeDenotes table child type) (outer : Syntax.SourceSpan) :
    StructuralTypeDenotes table ⟨outer,.function span ⟨span,[child]⟩ (some ⟨span,[child]⟩)⟩ (.function type type) ∧
    interpretStructuralType? table ⟨outer,.function span ⟨span,[child]⟩ (some ⟨span,[child]⟩)⟩=some (.function type type) ∧
    interpretTypeName? table ⟨outer,.function span ⟨span,[child]⟩ (some ⟨span,[child]⟩)⟩=none := by
  have independent : StructuralTypeDenotes table ⟨outer,.function span ⟨span,[child]⟩ (some ⟨span,[child]⟩)⟩
      (.function type type) := .functionReturns meaning (.single meaning)
  exact ⟨independent,independent.complete,rfl⟩

theorem missing_parameter_or_return_children_reject_the_entire_annotation
    (s : Ranges) (table : TypeNameTable) (bad good : Syntax.TypeExpr)
    (missing : ¬ ∃ type, StructuralTypeDenotes table bad type) :
    interpretStructuralType? table (original s bad none)=none ∧
    interpretStructuralType? table (original s bad (some [good]))=none ∧
    interpretStructuralType? table (original s good (some [bad]))=none ∧
    interpretStructuralType? table (original s good (some [good,bad]))=none := by
  have absent := interpretStructuralType?_eq_none_iff.mpr missing
  simp [original,interpretStructuralType?,absent]

theorem nested_success_survives_extensions_without_changing_any_source_range
    (s : Nat → Ranges) (table extras : TypeNameTable) (parameter result : Syntax.TypeExpr) (A B : Core.Ty)
    (pa : StructuralTypeDenotes table parameter A) (rb : StructuralTypeDenotes table result B) (n : Nat)
    (key : List String) (newType : Core.Ty) (fresh : key ∉ table.map Prod.fst) (changed : Syntax.SourceSpan) :
    StructuralTypeDenotes (table++extras) (nested s parameter result n) (nestedType A B n) ∧
    interpretStructuralType? ((key,newType)::table) (nested s parameter result n)=some (nestedType A B n) ∧
    interpretStructuralType? table {nested s parameter result n with span := changed}=some (nestedType A B n) := by
  have independent := nestedMeaning s table parameter result A B pa rb n
  exact ⟨independent.extend_types (TypeNameTable.Extends.append_right table extras),
    interpretStructuralType?_some_of_extends (TypeNameTable.Extends.cons_fresh table key newType fresh) independent.complete,
    (interpretStructuralType?_span table _ changed).trans independent.complete⟩

theorem duplicate_priority_and_lookup_equivalence_apply_inside_function_children
    (s : Ranges) (A B : Core.Ty) (left right : TypeNameTable)
    (same : ∀ key, left.lookup? key=right.lookup? key) (parameter : Syntax.TypeExpr)
    (returns : Option (List Syntax.TypeExpr)) :
    interpretStructuralType? [(["T"],A),(["T"],B)] (original s (named s.parameters "T") (some [named s.returns "T"]))=
      some (.function A A) ∧
    interpretStructuralType? left (original s parameter returns)=interpretStructuralType? right (original s parameter returns) := by
  have leaf (whereAt : Syntax.SourceSpan) : StructuralTypeDenotes [(["T"],A),(["T"],B)] (named whereAt "T") A := .named .head
  exact ⟨(StructuralTypeDenotes.functionReturns (leaf _) (.single (leaf _))).complete,
    interpretStructuralType?_congr_lookup left right same _⟩

theorem nominal_parameter_meaning_needs_no_runtime_inhabitant_or_data_definition
    (s : Ranges) (nominal : Core.DataTypeId) :
    StructuralTypeDenotes [(["N"],.namedData nominal)] (original s (named s.parameters "N") none)
      (.function (.namedData nominal) .unit) ∧
    (¬ ∃ actual, Core.ValueHasType actual (.namedData nominal)) ∧
    interpretTypeName? [(["N"],.namedData nominal)] (original s (named s.parameters "N") none)=none := by
  refine ⟨.functionDefault (.named .head),?_,rfl⟩
  rintro ⟨actual,typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?,Core.DataEnvironment.lookupDataType?] at found
end Tests.FrontendUnaryFunctionType
