import Solcore.Core.LocalFragmentInferenceInsertionProperties
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Resolved.WordLessWithIds

/-! Independent local typing remains exact under retained-prefix insertion.
Context types and data definitions are arbitrary; no runtime inhabitants or
allocation assumptions are used to establish static lookup and inference. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentTypingInsertion

open Solcore Solcore.Core

private def arithmetic (cutoff : Nat) : Expr :=
  .unary .wordNot (.binary .wordSub (.var cutoff) (.var (cutoff + 1)))
private theorem arithmeticLocal (cutoff : Nat) : Expr.LocalFragment (arithmetic cutoff) :=
  .unary (.binary .var .var)
private theorem arithmeticTyped (leading suffix : Context) (definitions : DataEnvironment) :
    HasType (leading ++ .word :: .word :: suffix) (arithmetic leading.length) .word definitions :=
  .unary (.binary (.var (by simp [BinaryOp.leftType])) (.var (by simp [BinaryOp.rightType])))

private def nested : Expr := .letE (.var 1) (.letE (.var 0) (.var 2))
private def nestedShifted : Expr := .letE (.var 2) (.letE (.var 0) (.var 2))
private theorem nestedLocal : Expr.LocalFragment nested := .letE .var (.letE .var .var)
private theorem nestedTyped (retained bound : Ty) (suffix : Context) (definitions : DataEnvironment) :
    HasType (retained :: bound :: suffix) nested retained definitions :=
  .letE (.var rfl) (.letE (.var rfl) (.var rfl))

private def conditional (choice : Bool) : Expr := .ifE (.bool choice) (.var 0) (.var 1)
private theorem conditionalLocal (choice : Bool) : Expr.LocalFragment (conditional choice) := .ifE .bool .var .var
private theorem conditionalTyped (choice : Bool) (type : Ty) (suffix : Context) (definitions : DataEnvironment) :
    HasType (type :: type :: suffix) (conditional choice) type definitions := .ifE .bool (.var rfl) (.var rfl)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"LocalTypingInsertion", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def named : Resolved.Expr := .wordLtWithIds (ident 2) (ident 0) (.var (ident 0)) (.var (ident 1))
private def ordered : Expr := .letE (.var 0) (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1)))
private theorem orderedLowered : Resolved.Lowers [ident 0, ident 1] named ordered := by
  have lowerLeft : Resolved.Lowers [ident 0, ident 1] (.var (ident 0)) (.var 0) := .var .head
  have lowerRight : Resolved.Lowers [ident 0, ident 1] (.var (ident 1)) (.var 1) := .var (.tail (by decide) .head)
  simpa [named, ordered, Expr.wordLt_expansion, Expr.weakenAt] using
    lowerLeft.wordLtWithIds (leftId := ident 2) (rightId := ident 0) lowerRight (by decide) (by decide)
private theorem orderedTyped (definitions : DataEnvironment) : HasType [.word, .word] ordered .bool definitions :=
  .letE (.var rfl) (.letE (.var rfl) (.binary (.var rfl) (.var rfl)))

theorem all_three_constant_forms_retain_types_with_arbitrary_data_definitions
    (leading suffix : Context) (inserted : Ty) (choice : Bool) (word : Word) (definitions : DataEnvironment) :
    HasType (leading ++ inserted :: suffix) .unit .unit definitions ∧
    HasType (leading ++ inserted :: suffix) (.bool choice) .bool definitions ∧
    HasType (leading ++ inserted :: suffix) (.word word) .word definitions := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Expr.weakenAt] using (Expr.LocalFragment.unit.hasType_insert_iff leading suffix inserted).mpr
      (show HasType (leading ++ suffix) .unit .unit definitions from .unit)
  · simpa only [Expr.weakenAt] using (Expr.LocalFragment.bool.hasType_insert_iff leading suffix inserted).mpr
      (show HasType (leading ++ suffix) (.bool choice) .bool definitions from .bool)
  · simpa only [Expr.weakenAt] using (Expr.LocalFragment.word.hasType_insert_iff leading suffix inserted).mpr
      (show HasType (leading ++ suffix) (.word word) .word definitions from .word)

theorem arbitrary_suffix_types_are_shifted_at_the_retained_prefix_length
    (leading suffix : Context) (type inserted : Ty) (definitions : DataEnvironment) :
    HasType (leading ++ type :: suffix) (.var leading.length) type definitions ∧
    HasType (leading ++ inserted :: type :: suffix) (.var (leading.length + 1)) type definitions ∧
    infer? (leading ++ inserted :: type :: suffix) (.var (leading.length + 1)) definitions = some type := by
  have original : HasType (leading ++ type :: suffix) (.var leading.length) type definitions := .var (by simp)
  have fragment : (Expr.var leading.length).LocalFragment := .var
  have shifted := (fragment.hasType_insert_iff leading (type :: suffix) inserted).mpr original
  refine ⟨original, ?_, ?_⟩
  · simpa only [Expr.weakenAt, Nat.le_refl, ↓reduceIte] using shifted
  · simpa only [Expr.weakenAt, Nat.le_refl, ↓reduceIte] using
      (fragment.infer_insert leading (type :: suffix) inserted definitions).trans (infer_complete original)

theorem head_insertion_has_exact_type_preservation_reflection_and_inference
    (context : Context) (type inserted : Ty) (definitions : DataEnvironment) :
    HasType (inserted :: type :: context) (.var 1) type definitions ∧
    HasType (type :: context) (.var 0) type definitions ∧
    (HasType (inserted :: type :: context) (.var 1) type definitions ↔
      HasType (type :: context) (.var 0) type definitions) ∧
    infer? (inserted :: type :: context) (.var 1) definitions = some type := by
  have original : HasType (type :: context) (.var 0) type definitions := .var rfl
  have fragment : (Expr.var 0).LocalFragment := .var
  have shifted := original.weakenAt_zero_localFragment fragment inserted
  refine ⟨?_, shifted.reflect_weakenAt_zero_localFragment fragment, ?_, ?_⟩
  · simpa [Expr.weakenAt] using shifted
  · simpa [Expr.weakenAt] using fragment.hasType_weaken_zero_iff (type :: context) inserted
      (type := type) (definitions := definitions)
  · simpa [Expr.weakenAt] using
      (fragment.infer_weaken_zero (type :: context) inserted definitions).trans (infer_complete original)

theorem retained_types_before_the_cutoff_keep_their_original_position
    (retained inserted : Ty) (suffix : Context) (definitions : DataEnvironment) :
    (Expr.var 0).weakenAt 1 = .var 0 ∧
    HasType (retained :: inserted :: suffix) (.var 0) retained definitions ∧
    infer? (retained :: inserted :: suffix) (.var 0) definitions = some retained := by
  have original : HasType (retained :: suffix) (.var 0) retained definitions := .var rfl
  have shifted := ((Expr.LocalFragment.var (index := 0)).hasType_insert_iff [retained] suffix inserted).mpr original
  have typed : HasType (retained :: inserted :: suffix) (.var 0) retained definitions := by
    simpa [Expr.weakenAt] using shifted
  exact ⟨by simp [Expr.weakenAt], typed, infer_complete typed⟩

theorem opaque_nominal_context_types_need_no_runtime_inhabitant_or_definition
    (dataType : DataTypeId) (inserted : Ty) (suffix : Context) :
    HasType (inserted :: .namedData dataType :: suffix) (.var 1) (.namedData dataType) [] ∧
    infer? (inserted :: .namedData dataType :: suffix) (.var 1) [] = some (.namedData dataType) := by
  have headResult := head_insertion_has_exact_type_preservation_reflection_and_inference suffix (.namedData dataType) inserted []
  exact ⟨headResult.1, headResult.2.2.2⟩

theorem unary_and_binary_word_primitives_retain_typing_and_whole_inference
    (leading suffix : Context) (inserted : Ty) (definitions : DataEnvironment) :
    (arithmetic leading.length).LocalFragment ∧
    HasType (leading ++ inserted :: .word :: .word :: suffix)
      ((arithmetic leading.length).weakenAt leading.length) .word definitions ∧
    infer? (leading ++ inserted :: .word :: .word :: suffix)
      ((arithmetic leading.length).weakenAt leading.length) definitions = some .word :=
  ⟨arithmeticLocal leading.length,
    ((arithmeticLocal leading.length).hasType_insert_iff leading (.word :: .word :: suffix) inserted).mpr
      (arithmeticTyped leading suffix definitions),
    ((arithmeticLocal leading.length).infer_insert leading (.word :: .word :: suffix) inserted definitions).trans
      (infer_complete (arithmeticTyped leading suffix definitions))⟩

theorem nested_lets_keep_bound_types_while_shifting_only_the_original_suffix
    (retained bound inserted : Ty) (suffix : Context) (definitions : DataEnvironment) :
    nested.weakenAt 1 = nestedShifted ∧ nestedShifted.LocalFragment ∧
    HasType (retained :: inserted :: bound :: suffix) nestedShifted retained definitions ∧
    infer? (retained :: inserted :: bound :: suffix) nestedShifted definitions = some retained := by
  have same : nested.weakenAt 1 = nestedShifted := by simp [nested, nestedShifted, Expr.weakenAt]
  have shifted := (nestedLocal.hasType_insert_iff [retained] (bound :: suffix) inserted).mpr
    (nestedTyped retained bound suffix definitions)
  have typing : HasType (retained :: inserted :: bound :: suffix) nestedShifted retained definitions := by
    simpa only [List.length_cons, List.length_nil, same, List.cons_append, List.nil_append] using shifted
  exact ⟨same, same ▸ nestedLocal.weakenAt 1, typing, infer_complete typing⟩

theorem both_conditional_choices_keep_the_common_branch_type
    (choice : Bool) (type inserted : Ty) (suffix : Context) (definitions : DataEnvironment) :
    (conditional choice).LocalFragment ∧
    HasType (type :: type :: suffix) (conditional choice) type definitions ∧
    HasType (inserted :: type :: type :: suffix) ((conditional choice).weakenAt 0) type definitions ∧
    infer? (inserted :: type :: type :: suffix) ((conditional choice).weakenAt 0) definitions = some type :=
  ⟨conditionalLocal choice, conditionalTyped choice type suffix definitions,
    (conditionalTyped choice type suffix definitions).weakenAt_zero_localFragment (conditionalLocal choice) inserted,
    ((conditionalLocal choice).infer_weaken_zero (type :: type :: suffix) inserted definitions).trans
      (infer_complete (conditionalTyped choice type suffix definitions))⟩

theorem resolved_ordered_comparison_supports_core_only_typing_insertion
    (inserted : Ty) (definitions : DataEnvironment) :
    Resolved.Lowers [ident 0, ident 1] named ordered ∧ ordered.LocalFragment ∧
    HasType [inserted, .word, .word] (ordered.weakenAt 0) .bool definitions ∧
    infer? [inserted, .word, .word] (ordered.weakenAt 0) definitions = some .bool :=
  ⟨orderedLowered, orderedLowered.localFragment,
    (orderedTyped definitions).weakenAt_zero_localFragment orderedLowered.localFragment inserted,
    (orderedLowered.localFragment.infer_weaken_zero [.word, .word] inserted definitions).trans
      (infer_complete (orderedTyped definitions))⟩

end Tests.CoreLocalFragmentTypingInsertion
