import Solcore.Frontend.LocalInputsExtensionProperties
import Solcore.Frontend.LocalInputsRenamingProperties
import Solcore.Core.BitwiseLogic

/-! ADR-0164: strict ordered Word operands, exact binary Core, and no mask-based
short circuiting. The source rules remain distinct from whole-expression typing. -/

set_option autoImplicit false

namespace Tests.FrontendLocalWordBitwise

open Solcore Solcore.Frontend

private inductive Kind where | andE | orE | xorE
private def sourceOp : Kind → Syntax.BinaryOp | .andE => .bitAnd | .orE => .bitOr | .xorE => .bitXor
private def coreOp : Kind → Core.BinaryOp | .andE => .wordAnd | .orE => .wordOr | .xorE => .wordXor
private def result (kind : Kind) (left right : Core.Word) : Core.Word :=
  match kind with | .andE => left.bitAnd right | .orE => left.bitOr right | .xorE => left.bitXor right
private theorem applied (kind : Kind) (left right : Core.Word) :
    (coreOp kind).apply (.word left) (.word right) = some (.word (result kind left right)) := by cases kind <;> rfl
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Bitwise", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "bitwise.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def binary (kind : Kind) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .binary left ⟨span, sourceOp kind⟩ right⟩
private def literal (payload : Syntax.CoreLiteralValue) : Syntax.Expr := ⟨span, .literal ⟨span, payload⟩⟩
private def pair (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "r" rightType right rightTyped).bindFresh owner "l" leftType left leftTyped
private def inputs (left right : Core.Word) : LocalInputs := pair .word .word (.word left) (.word right) .word .word
private def source (kind : Kind) : Syntax.Expr := binary kind (ref "l") (ref "r")
private def core (kind : Kind) : Core.Expr := .binary (coreOp kind) (.var 0) (.var 1)
private theorem names_ne : "l" ≠ "r" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide

private theorem resolved (kind : Kind) (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names (source kind)
      (.binary (coreOp kind) (.var ⟨owner, 1⟩) (.var ⟨owner, 0⟩)) := by
  cases kind
  · exact .bitAnd (.identifier .head) (.identifier (.tail names_ne .head))
  · exact .bitOr (.identifier .head) (.identifier (.tail names_ne .head))
  · exact .bitXor (.identifier .head) (.identifier (.tail names_ne .head))
private theorem typed (kind : Kind) (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context (source kind) .word := by
  cases kind
  · exact .bitAnd (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head))
  · exact .bitOr (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head))
  · exact .bitXor (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head))
private theorem checked (kind : Kind) (left right : Core.Word) :
    (inputs left right).check? (source kind) = some (core kind, .word) :=
  elaborateLocalExpression?_complete (resolved kind left right) (.binary (.var .head) (.var (.tail ids_ne .head)))
    ((resolved kind left right).preserves_type (typed kind left right))
private theorem evaluated (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment store
      (source kind) (.word (result kind left right)) store := by
  cases kind
  · exact .bitAnd (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head))
  · exact .bitOr (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head))
  · exact .bitXor (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head))

theorem arbitrary_words_have_exact_independent_and_checked_meanings
    (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    ResolvesLocalExpression (inputs left right).names (source kind)
      (.binary (coreOp kind) (.var ⟨owner, 1⟩) (.var ⟨owner, 0⟩)) ∧
    LocalExpressionHasType (inputs left right).names (inputs left right).context (source kind) .word ∧
    (inputs left right).check? (source kind) = some (core kind, .word) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment store
      (source kind) (.word (result kind left right)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs left right).environment) store
      (core kind) (.word (result kind left right)) store :=
  ⟨resolved kind left right, typed kind left right, checked kind left right, evaluated kind left right store,
    (elaborateLocalExpression?_evaluates_iff (checked kind left right) (inputs left right).sameIds).mp
      (evaluated kind left right store)⟩

theorem successful_bitwise_evaluation_requires_ordered_word_operands
    (kind : Kind) (table : LocalNameTable) (environment : Resolved.Environment)
    (left right : Syntax.Expr) (value : Core.Value) (initialStore finalStore : Core.Store)
    (evaluation : LocalExpressionEvaluates table environment initialStore (binary kind left right) value finalStore) :
    ∃ leftWord rightWord middleStore,
      LocalExpressionEvaluates table environment initialStore left (.word leftWord) middleStore ∧
      LocalExpressionEvaluates table environment middleStore right (.word rightWord) finalStore := by
  cases kind <;> cases evaluation <;> exact ⟨_, _, _, by assumption, by assumption⟩

private theorem typed_operands (kind : Kind) {table : LocalNameTable} {context : Resolved.Context}
    {left right : Syntax.Expr} {type : Core.Ty}
    (typing : LocalExpressionHasType table context (binary kind left right) type) :
    LocalExpressionHasType table context left .word ∧ LocalExpressionHasType table context right .word := by
  cases kind <;> cases typing <;> constructor <;> assumption

theorem named_pairs_have_exact_four_five_fuel_boundary (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 4 (source kind) store = some (.word, .outOfFuel
      ⟨.ret (.word right), [.binaryApply (coreOp kind) (.word left)], store⟩) ∧
    ∀ extra, (inputs left right).run? (extra + 5) (source kind) store =
      some (.word, .done (.word (result kind left right)) store) := by
  constructor
  · rw [LocalInputs.run?, checked]; cases kind <;> rfl
  · intro extra
    rw [LocalInputs.run?, checked]
    change some (Core.Ty.word, Core.runStateful (extra + 5)
      (Core.State.initial (core kind) [.word left, .word right] store)) = _
    apply congrArg (fun value => some (Core.Ty.word, value))
    exact Core.runStateful_complete_with_fuel
      (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight
        (.cons (.var rfl) (.cons (.applyBinary (applied kind left right)) .refl))))) (Nat.le_add_left 5 extra)

private def aa : Core.Word := ⟨170, by decide⟩
private def cc : Core.Word := ⟨204, by decide⟩
private def maskSource (kind : Kind) : Syntax.Expr := binary kind (literal (.hexadecimal "0xAA")) (literal (.hexadecimal "0xCC"))
private theorem aaMeaning : WordLiteralDenotes ⟨span, .hexadecimal "0xAA"⟩ aa := interpretWordLiteral?_sound (by decide)
private theorem ccMeaning : WordLiteralDenotes ⟨span, .hexadecimal "0xCC"⟩ cc := interpretWordLiteral?_sound (by decide)
private theorem checked_masks (kind : Kind) :
    LocalInputs.empty.check? (maskSource kind) = some (.binary (coreOp kind) (.word aa) (.word cc), .word) := by
  cases kind
  · exact elaborateLocalExpression?_complete (.bitAnd (.wordLiteral aaMeaning) (.wordLiteral ccMeaning)) (.binary .word .word) (.binary .word .word)
  · exact elaborateLocalExpression?_complete (.bitOr (.wordLiteral aaMeaning) (.wordLiteral ccMeaning)) (.binary .word .word) (.binary .word .word)
  · exact elaborateLocalExpression?_complete (.bitXor (.wordLiteral aaMeaning) (.wordLiteral ccMeaning)) (.binary .word .word) (.binary .word .word)

theorem literal_masks_have_exact_results_and_fuel (kind : Kind) (store : Core.Store) :
    (result .andE aa cc).val = 136 ∧ (result .orE aa cc).val = 238 ∧ (result .xorE aa cc).val = 102 ∧
    LocalInputs.empty.check? (maskSource kind) = some (.binary (coreOp kind) (.word aa) (.word cc), .word) ∧
    LocalInputs.empty.run? 4 (maskSource kind) store = some (.word, .outOfFuel
      ⟨.ret (.word cc), [.binaryApply (coreOp kind) (.word aa)], store⟩) ∧
    ∀ extra, LocalInputs.empty.run? (extra + 5) (maskSource kind) store = some (.word, .done (.word (result kind aa cc)) store) := by
  refine ⟨by decide, by decide, by decide, checked_masks kind, ?_, ?_⟩
  · rw [LocalInputs.run?, checked_masks]; cases kind <;> rfl
  · intro extra
    rw [LocalInputs.run?, checked_masks]
    change some (Core.Ty.word, Core.runStateful (extra + 5)
      (Core.State.initial (.binary (coreOp kind) (.word aa) (.word cc)) [] store)) = _
    apply congrArg (fun value => some (Core.Ty.word, value))
    exact Core.runStateful_complete_with_fuel
      (.cons .enterBinary (.cons .word (.cons .enterBinaryRight
        (.cons .word (.cons (.applyBinary (applied kind aa cc)) .refl))))) (Nat.le_add_left 5 extra)

theorem zero_maximum_and_self_keep_word_identities (word : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluates (inputs word .zero).names (inputs word .zero).environment store (source .andE) (.word .zero) store ∧
    LocalExpressionEvaluates (inputs .maximum .zero).names (inputs .maximum .zero).environment store (source .orE) (.word .maximum) store ∧
    LocalExpressionEvaluates (inputs word word).names (inputs word word).environment store (source .xorE) (.word .zero) store := by
  exact ⟨by simpa [result] using evaluated .andE word .zero store,
    by simpa [result] using evaluated .orE .maximum .zero store,
    by simpa [result] using evaluated .xorE word word store⟩

private def badPair (onLeft : Bool) (flag : Bool) : LocalInputs :=
  if onLeft then pair .bool .word (.bool flag) (.word cc) .bool .word
  else pair .word .bool (.word aa) (.bool flag) .word .bool

theorem boolean_on_either_side_has_no_checked_or_raw_word_result
    (kind : Kind) (onLeft flag : Bool) (store : Core.Store) :
    (badPair onLeft flag).check? (source kind) = none ∧
    ∀ value finalStore, ¬ LocalExpressionEvaluates (badPair onLeft flag).names (badPair onLeft flag).environment
      store (source kind) value finalStore := by
  have badTyped : LocalExpressionHasType (badPair onLeft flag).names (badPair onLeft flag).context
      (ref (if onLeft then "l" else "r")) .bool := by
    cases onLeft
    · exact .identifier (.tail names_ne .head) (.tail ids_ne .head)
    · exact .identifier .head .head
  constructor
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    obtain ⟨left, right⟩ := typed_operands kind typing
    cases onLeft
    · cases badTyped.type_unique right
    · cases badTyped.type_unique left
  · intro value finalStore evaluation
    obtain ⟨leftWord, rightWord, middleStore, left, right⟩ :=
      successful_bitwise_evaluation_requires_ordered_word_operands kind _ _ _ _ _ _ _ evaluation
    cases onLeft
    · have bad : LocalExpressionEvaluates (badPair false flag).names (badPair false flag).environment
          middleStore (ref "r") (.bool flag) middleStore := .identifier (.tail names_ne .head) (.tail ids_ne .head)
      cases (bad.deterministic right).1
    · have bad : LocalExpressionEvaluates (badPair true flag).names (badPair true flag).environment
          store (ref "l") (.bool flag) store := .identifier .head .head
      cases (bad.deterministic left).1

private def badRights : List Syntax.Expr := [ref "missing", literal (.string "7")]
theorem zero_left_never_skips_missing_or_uninterpretable_right
    (kind : Kind) (right : Syntax.Expr) (present : right ∈ badRights) (store : Core.Store) :
    (inputs .zero .zero).check? (binary kind (ref "l") right) = none ∧
    ∀ value finalStore, ¬ LocalExpressionEvaluates (inputs .zero .zero).names (inputs .zero .zero).environment
      store (binary kind (ref "l") right) value finalStore := by
  have absent : ∀ initial word finalStore, ¬ LocalExpressionEvaluates (inputs .zero .zero).names
      (inputs .zero .zero).environment initial right (.word word) finalStore := by
    intro initial word finalStore evaluation
    simp only [badRights, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · cases evaluation with
      | identifier named _ =>
          have impossible := LocalNameTable.lookup?_iff.mpr named
          have missing : (inputs .zero .zero).names.lookup? "missing" = none := rfl
          rw [missing] at impossible
          cases impossible
    · cases evaluation with
      | wordLiteral meaning =>
          have impossible := interpretWordLiteral?_complete meaning
          simp [interpretWordLiteral?, numericLiteralValue?] at impossible
  constructor
  · simp only [badRights, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    all_goals cases kind <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?,
      binary, sourceOp, ref, literal, inputs, pair, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty,
      LocalNameTable.lookup?, interpretWordLiteral?, numericLiteralValue?]
  · intro value finalStore evaluation
    obtain ⟨_, word, middleStore, _, rightEvaluation⟩ :=
      successful_bitwise_evaluation_requires_ordered_word_operands kind _ _ _ _ _ _ _ evaluation
    exact absent middleStore word finalStore rightEvaluation

private def withFlag (left right : Core.Word) : LocalInputs := (inputs left right).bindFresh owner "c" .bool (.bool true) .bool
private def rawSource : Syntax.Expr := binary .andE ⟨span, .binary (ref "c") ⟨span, .logicalAnd⟩ (ref "l")⟩ (ref "r")
private def rawCore : Core.Expr := .binary .wordAnd (.ifE (.var 0) (.var 1) (.bool false)) (.var 2)
theorem selected_raw_word_inside_an_operand_does_not_imply_whole_typing (left right : Core.Word) (store : Core.Store) :
    (withFlag left right).check? rawSource = none ∧
    LocalExpressionEvaluates (withFlag left right).names (withFlag left right).environment store rawSource (.word (left.bitAnd right)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (withFlag left right).environment) store rawCore (.word (left.bitAnd right)) store := by
  have c_ne_l : "c" ≠ "l" := by decide
  have c_ne_r : "c" ≠ "r" := by decide
  have i21 : (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩ := by decide
  have i20 : (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
  have resolution : ResolvesLocalExpression (withFlag left right).names rawSource
      (.binary .wordAnd (.ifE (.var ⟨owner, 2⟩) (.var ⟨owner, 1⟩) (.bool false)) (.var ⟨owner, 0⟩)) :=
    .bitAnd (.logicalAnd (.identifier .head) (.identifier (.tail c_ne_l .head)))
      (.identifier (.tail c_ne_r (.tail names_ne .head)))
  have evaluation : LocalExpressionEvaluates (withFlag left right).names (withFlag left right).environment store rawSource (.word (left.bitAnd right)) store :=
    .bitAnd (.andTrue (.identifier .head .head) (.identifier (.tail c_ne_l .head) (.tail i21 .head)))
      (.identifier (.tail c_ne_r (.tail names_ne .head)) (.tail i20 (.tail ids_ne .head)))
  refine ⟨?_, evaluation, (resolution.core_evaluates_iff (environment := (withFlag left right).environment)
    (.binary (.ifE (.var .head) (.var (.tail i21 .head)) .bool) (.var (.tail i20 (.tail ids_ne .head))))).mp evaluation⟩
  apply elaborateLocalExpression?_eq_none_iff.mpr
  rintro ⟨type, typing⟩
  cases typing with | bitAnd leftTyped _ => cases leftTyped

theorem unused_inputs_and_id_renaming_preserve_all_three_forms
    (kind : Kind) (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) :
    ((inputs left right).bindFresh owner "extra" .unit .unit .unit).check? (source kind) =
      some (.binary (coreOp kind) (.var 1) (.var 2), .word) ∧
    LocalExpressionEvaluates ((inputs left right).bindFresh owner "extra" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "extra" .unit .unit .unit).environment store
      (source kind) (.word (result kind left right)) store ∧
    ((inputs left right).mapIds mapping injective).check? (source kind) = some (core kind, .word) ∧
    ((inputs left right).mapIds mapping injective).run? fuel (source kind) store = (inputs left right).run? fuel (source kind) store := by
  have avoids : AvoidsLocalName "extra" (source kind) := by
    cases kind
    · exact .bitAnd (.identifier (by decide)) (.identifier (by decide))
    · exact .bitOr (.identifier (by decide)) (.identifier (by decide))
    · exact .bitXor (.identifier (by decide)) (.identifier (by decide))
  refine ⟨?_, (avoids.bindFresh_evaluates_iff (inputs left right) owner .unit .unit .unit).mpr
      (evaluated kind left right store),
    ((inputs left right).check?_mapIds mapping injective _).trans (checked kind left right),
    (inputs left right).run?_mapIds mapping injective fuel (source kind) store⟩
  simpa [core, Core.Expr.weakenAt] using avoids.check_bindFresh_complete
    (inputs left right) owner .unit .unit .unit (checked kind left right)

end Tests.FrontendLocalWordBitwise
