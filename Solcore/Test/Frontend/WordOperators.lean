import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.BitwiseLogic
import Solcore.Core.UnaryPrimitives
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.TerminalReturnBody
import Solcore.Frontend.TerminalReturnTree
import Solcore.Frontend.ReturnBody
import Solcore.Frontend.WordLiteral
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Core.ModularArithmetic
import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Core.UnsignedDivision
import Solcore.Core.DirectWordComparisons
import Solcore.Core.FuelResumptionProperties
import Solcore.Core.Primitive

/-!
# Word operator tests

Parsed Word expressions: addition, arithmetic, division, bitwise forms, equality and ordering, each with
strict operand order, exact transition counts and complete checkpoints.
-/

section
-- leanmerge: from Solcore.Test.FrontendLocalWordBitwiseProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendLocalWordComplementProperties
/-! ADR-0161: fixed Word complement is distinct from Boolean negation.
Strings and untyped short-circuit expressions remain outside checked operands. -/

set_option autoImplicit false

namespace Tests.FrontendLocalWordComplement

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"WordComplement", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "word-complement.sol"⟩, 0, 1⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def complement (operand : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .bitNot⟩ operand⟩
private def negate (operand : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .logicalNot⟩ operand⟩
private def supplied (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "x" type value typed
private def inputs (word : Core.Word) : LocalInputs := supplied .word (.word word) .word
private def source : Syntax.Expr := complement (ref "x")
private def twice : Syntax.Expr := complement source
private def core : Core.Expr := .unary .wordNot (.var 0)
private def twiceCore : Core.Expr := .unary .wordNot core
private theorem checked (word : Core.Word) : (inputs word).check? source = some (core, .word) :=
  elaborateLocalExpression?_complete (.bitNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head))
private theorem checked_twice (word : Core.Word) : (inputs word).check? twice = some (twiceCore, .word) :=
  elaborateLocalExpression?_complete (.bitNot (.bitNot (.identifier .head)))
    (.unary (.unary (.var .head))) (.unary (.unary (.var .head)))
private theorem evaluated (word : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluates (inputs word).names (inputs word).environment store source (.word word.bitNot) store :=
  .bitNot (.identifier .head .head)

theorem arbitrary_words_and_double_complement_have_exact_meanings (word : Core.Word) (store : Core.Store) :
    (inputs word).check? source = some (core, .word) ∧ (inputs word).check? twice = some (twiceCore, .word) ∧
    LocalExpressionEvaluates (inputs word).names (inputs word).environment store source (.word word.bitNot) store ∧
    LocalExpressionEvaluates (inputs word).names (inputs word).environment store twice (.word word) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs word).environment) store core (.word word.bitNot) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs word).environment) store twiceCore (.word word) store := by
  have double : LocalExpressionEvaluates (inputs word).names (inputs word).environment store twice (.word word) store := by
    simpa [twice, complement] using LocalExpressionEvaluates.bitNot (evaluated word store)
  exact ⟨checked word, checked_twice word, evaluated word store, double,
    (elaborateLocalExpression?_evaluates_iff (checked word) (inputs word).sameIds).mp (evaluated word store),
    (elaborateLocalExpression?_evaluates_iff (checked_twice word) (inputs word).sameIds).mp double⟩

private theorem run_enough (word : Core.Word) (extra : Nat) (store : Core.Store) :
    (inputs word).run? (extra + 3) source store = some (.word, .done (.word word.bitNot) store) := by
  rw [LocalInputs.run?, checked]
  change some (Core.Ty.word, Core.runStateful (extra + 3) (Core.State.initial core [.word word] store)) = _
  simp [Core.runStateful, Core.State.initial, Core.advance, core, Core.UnaryOp.apply]

theorem single_and_double_complement_have_exact_fuel (word : Core.Word) (store : Core.Store) :
    (inputs word).run? 2 source store = some (.word, .outOfFuel ⟨.ret (.word word), [.unaryApply .wordNot], store⟩) ∧
    (inputs word).run? 4 twice store = some (.word, .outOfFuel ⟨.ret (.word word.bitNot), [.unaryApply .wordNot], store⟩) ∧
    (∀ extra, (inputs word).run? (extra + 3) source store = some (.word, .done (.word word.bitNot) store)) ∧
    ∀ extra, (inputs word).run? (extra + 5) twice store = some (.word, .done (.word word) store) := by
  refine ⟨?_, ?_, fun extra => run_enough word extra store, ?_⟩
  · rw [LocalInputs.run?, checked]; rfl
  · rw [LocalInputs.run?, checked_twice]; rfl
  · intro extra
    rw [LocalInputs.run?, checked_twice]
    change some (Core.Ty.word, Core.runStateful (extra + 5) (Core.State.initial twiceCore [.word word] store)) = _
    simp [Core.runStateful, Core.State.initial, Core.advance, twiceCore, core, Core.UnaryOp.apply]

theorem zero_one_and_maximum_have_expected_complements (store : Core.Store) :
    (inputs .zero).run? 3 source store = some (.word, .done (.word .maximum) store) ∧
    (inputs (Core.Word.ofNatModulo 1)).run? 3 source store =
      some (.word, .done (.word (Core.Word.ofNatModulo (Core.wordModulus - 2))) store) ∧
    (inputs .maximum).run? 3 source store = some (.word, .done (.word .zero) store) := by
  refine ⟨by simpa using run_enough .zero 0 store, ?_, by simpa using run_enough .maximum 0 store⟩
  have one : (Core.Word.ofNatModulo 1).bitNot = Core.Word.ofNatModulo (Core.wordModulus - 2) := by decide
  simpa only [Nat.zero_add, one] using run_enough (Core.Word.ofNatModulo 1) 0 store

private theorem non_word_rejected (type : Core.Ty) (value : Core.Value)
    (typed : Core.ValueHasType value type) (wrongType : type ≠ .word)
    (wrongValue : ∀ word, value ≠ .word word) (store : Core.Store) :
    (supplied type value typed).check? source = none ∧ ∀ result finalStore,
      ¬ LocalExpressionEvaluates (supplied type value typed).names (supplied type value typed).environment
        store source result finalStore := by
  constructor
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨resultType, typing⟩
    cases typing with
    | bitNot operand =>
        have original : LocalExpressionHasType (supplied type value typed).names
            (supplied type value typed).context (ref "x") type := .identifier .head .head
        exact wrongType (original.type_unique operand)
  · intro result finalStore evaluation
    have original : LocalExpressionEvaluates (supplied type value typed).names
        (supplied type value typed).environment store (ref "x") value store := .identifier .head .head
    cases evaluation with
    | bitNot operand => exact wrongValue _ (original.deterministic operand).1

theorem boolean_and_reference_values_are_not_coerced (flag : Bool) (location : Nat) (store : Core.Store) :
    (supplied .bool (.bool flag) .bool).check? source = none ∧
    (supplied (.cell .word) (.cellRef .word location) .cellRef).check? source = none ∧
    ∀ value finalStore,
      (¬ LocalExpressionEvaluates (supplied .bool (.bool flag) .bool).names
        (supplied .bool (.bool flag) .bool).environment store source value finalStore) ∧
      (¬ LocalExpressionEvaluates (supplied (.cell .word) (.cellRef .word location) .cellRef).names
        (supplied (.cell .word) (.cellRef .word location) .cellRef).environment store source value finalStore) := by
  have boolean := non_word_rejected .bool (.bool flag) .bool (by decide) (by intro word same; cases same) store
  have reference := non_word_rejected (.cell .word) (.cellRef .word location) .cellRef
    (by decide) (by intro word same; cases same) store
  exact ⟨boolean.1, reference.1, fun value finalStore => ⟨boolean.2 value finalStore, reference.2 value finalStore⟩⟩

theorem logical_and_word_negation_do_not_convert_operand_types (word : Core.Word) (flag : Bool) :
    (inputs word).check? (negate source) = none ∧
    (supplied .bool (.bool flag) .bool).check? (complement (negate (ref "x"))) = none := by
  constructor
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    have actual : LocalExpressionHasType (inputs word).names (inputs word).context source .word :=
      .bitNot (.identifier .head .head)
    cases typing with | logicalNot operand => cases actual.type_unique operand
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    have actual : LocalExpressionHasType (supplied .bool (.bool flag) .bool).names
        (supplied .bool (.bool flag) .bool).context (negate (ref "x")) .bool := .logicalNot (.identifier .head .head)
    cases typing with | bitNot operand => cases actual.type_unique operand

private def unsupported : Syntax.Expr := ⟨span, .literal ⟨span, .string "7"⟩⟩
private def badOperands : List Syntax.Expr := [ref "missing", unsupported]

theorem missing_names_and_string_syntax_remain_rejected (word : Core.Word) :
    ∀ operand ∈ badOperands, resolveLocalExpression? (inputs word).names (complement operand) = none ∧
      (inputs word).check? (complement operand) = none := by
  intro operand member
  simp only [badOperands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, complement, ref,
    unsupported, interpretWordLiteral?, numericLiteralValue?, inputs, supplied,
    LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

private def withFlag (word : Core.Word) (flag : Bool) : LocalInputs :=
  (inputs word).bindFresh owner "a" .bool (.bool flag) .bool
private theorem names_ne : "a" ≠ "x" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private def nested : Syntax.Expr := complement
  ⟨span, .group ⟨span, .conditional (ref "a") span source span (ref "x")⟩⟩
private def nestedCore : Core.Expr := .unary .wordNot (.ifE (.var 0) (.unary .wordNot (.var 1)) (.var 1))
private theorem checked_nested (word : Core.Word) (flag : Bool) :
    (withFlag word flag).check? nested = some (nestedCore, .word) :=
  elaborateLocalExpression?_complete (.bitNot (.group (.conditional (.identifier .head)
    (.bitNot (.identifier (.tail names_ne .head))) (.identifier (.tail names_ne .head)))))
    (.unary (.ifE (.var .head) (.unary (.var (.tail ids_ne .head))) (.var (.tail ids_ne .head))))
    (.unary (.ifE (.var .head) (.unary (.var (.tail ids_ne .head))) (.var (.tail ids_ne .head))))

theorem grouped_conditionals_keep_word_complement_meaning (word : Core.Word) (flag : Bool) (store : Core.Store) :
    (withFlag word flag).check? nested = some (nestedCore, .word) ∧
    LocalExpressionEvaluates (withFlag word flag).names (withFlag word flag).environment store nested
      (.word (if flag then word else word.bitNot)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (withFlag word flag).environment) store nestedCore
      (.word (if flag then word else word.bitNot)) store := by
  have coreEvaluation : Core.Evaluates (Resolved.LocalScope.values (withFlag word flag).environment) store nestedCore
      (.word (if flag then word else word.bitNot)) store := by
    cases flag
    · exact .unary (.ifFalse (.var rfl) (.var rfl)) rfl
    · exact .unary (.ifTrue (.var rfl) (.unary (.var rfl) rfl)) (by simp [Core.UnaryOp.apply])
  exact ⟨checked_nested word flag, (elaborateLocalExpression?_evaluates_iff
    (checked_nested word flag) (withFlag word flag).sameIds).mpr coreEvaluation, coreEvaluation⟩

private def rawSource : Syntax.Expr := complement ⟨span, .binary (ref "a") ⟨span, .logicalAnd⟩ (ref "x")⟩
private def rawCore : Core.Expr := .unary .wordNot (.ifE (.var 0) (.var 1) (.bool false))

/-- Raw conjunction forwards its selected Word, but whole-expression checking
still fails. Core correspondence here requires resolution, not typing. -/
theorem raw_selected_word_can_be_complemented_without_being_checked (word : Core.Word) (store : Core.Store) :
    (withFlag word true).check? rawSource = none ∧
    LocalExpressionEvaluates (withFlag word true).names (withFlag word true).environment
      store rawSource (.word word.bitNot) store ∧
    Core.Evaluates (Resolved.LocalScope.values (withFlag word true).environment) store rawCore (.word word.bitNot) store := by
  have raw : LocalExpressionEvaluates (withFlag word true).names (withFlag word true).environment
      store rawSource (.word word.bitNot) store :=
    .bitNot (.andTrue (.identifier .head .head) (.identifier (.tail names_ne .head) (.tail ids_ne .head)))
  have resolution : ResolvesLocalExpression (withFlag word true).names rawSource
      (.unary .wordNot (.ifE (.var ⟨owner, 1⟩) (.var ⟨owner, 0⟩) (.bool false))) :=
    .bitNot (.logicalAnd (.identifier .head) (.identifier (.tail names_ne .head)))
  refine ⟨?_, raw, (resolution.core_evaluates_iff (environment := (withFlag word true).environment)
    (.unary (.ifE (.var .head) (.var (.tail ids_ne .head)) .bool))).mp raw⟩
  apply elaborateLocalExpression?_eq_none_iff.mpr
  rintro ⟨type, typing⟩
  cases typing with | bitNot operand => cases operand

private def shift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex + 5 }
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  cases left
  cases right
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases owners
  cases indices
  rfl
private def extended (word : Core.Word) : LocalInputs := (inputs word).bindFresh owner "extra" .unit .unit .unit
private def renamed (word : Core.Word) : LocalInputs := (inputs word).mapIds shift shift_injective

theorem input_extension_and_id_relabeling_preserve_complement (word : Core.Word) (fuel : Nat) (store : Core.Store) :
    (extended word).check? source = some (.unary .wordNot (.var 1), .word) ∧
    (renamed word).check? source = some (core, .word) ∧
    (renamed word).run? fuel source store = (inputs word).run? fuel source store ∧
    LocalExpressionEvaluates (extended word).names (extended word).environment store source (.word word.bitNot) store := by
  have avoids : AvoidsLocalName "extra" source := .bitNot (.identifier (by decide))
  refine ⟨?_, ((inputs word).check?_mapIds shift shift_injective source).trans (checked word),
    (inputs word).run?_mapIds shift shift_injective fuel source store,
    (avoids.bindFresh_evaluates_iff (inputs word) owner .unit .unit .unit).mpr (evaluated word store)⟩
  simpa [extended, core, Core.Expr.weakenAt] using
    avoids.check_bindFresh_complete (inputs word) owner .unit .unit .unit (checked word)

end Tests.FrontendLocalWordComplement
end

section
-- leanmerge: from Solcore.Test.FrontendLocalWordLiteralProperties
/-! ADR-0163: independent strict Word meanings feed the monomorphic expression
adapter. Checked execution still requires whole-expression type checking. -/

set_option autoImplicit false

namespace Tests.FrontendLocalWordLiteral

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"WordLiteral", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "literal-expressions.sol"⟩, 0, 1⟩
private def literal (payload : Syntax.CoreLiteralValue) : Syntax.CoreLiteral := ⟨span, payload⟩
private def source (payload : Syntax.CoreLiteralValue) : Syntax.Expr := ⟨span, .literal (literal payload)⟩
private def ref : Syntax.Expr := ⟨span, .identifier ⟨span, "c"⟩⟩
private def group (child : Syntax.Expr) : Syntax.Expr := ⟨span, .group child⟩
private def complement (child : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .bitNot⟩ child⟩
private def neg (child : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .logicalNot⟩ child⟩
private def andE (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .logicalAnd⟩ right⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr := ⟨span, .conditional condition span left span right⟩
private def inputs (choice : Bool) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool
private def seven : Core.Word := ⟨7, by decide⟩
private def sevenSource : Syntax.Expr := source (.decimal "7")
private theorem sevenMeaning : WordLiteralDenotes (literal (.decimal "7")) seven :=
  NumericLiteralDenotes.decimal (by decide)
    (.cons (.decimal (digit := 7) (by decide) (by decide)) .nil)

private theorem checked_literal (supplied : LocalInputs) {value : Core.Word} {payload : Syntax.CoreLiteralValue}
    (meaning : WordLiteralDenotes (literal payload) value) :
    supplied.check? (source payload) = some (.word value, .word) :=
  elaborateLocalExpression?_complete (.wordLiteral meaning) .word .word
private theorem checked_seven (supplied : LocalInputs) : supplied.check? sevenSource = some (.word seven, .word) :=
  checked_literal supplied sevenMeaning

theorem independent_literal_meaning_has_exact_resolution_typing_and_evaluation
    (supplied : LocalInputs) (outer : Syntax.SourceSpan) (value : Core.Word)
    (written : Syntax.CoreLiteral) (meaning : WordLiteralDenotes written value) (store : Core.Store) :
    ResolvesLocalExpression supplied.names ⟨outer, .literal written⟩ (.word value) ∧
    LocalExpressionHasType supplied.names supplied.context ⟨outer, .literal written⟩ .word ∧
    LocalExpressionEvaluates supplied.names supplied.environment store ⟨outer, .literal written⟩ (.word value) store ∧
    supplied.check? ⟨outer, .literal written⟩ = some (.word value, .word) ∧
    Core.Evaluates (Resolved.LocalScope.values supplied.environment) store (.word value) (.word value) store :=
  ⟨.wordLiteral meaning, .wordLiteral meaning, .wordLiteral meaning,
    elaborateLocalExpression?_complete (.wordLiteral meaning) .word .word, .word⟩

private def maximumPayload : Syntax.CoreLiteralValue :=
  .decimal "115792089237316195423570985008687907853269984665640564039457584007913129639935"
private def mixedCase : Syntax.CoreLiteralValue := .hexadecimal "0xaBcDeF"
private def mixedValue : Core.Word := ⟨11259375, by decide⟩

theorem zero_seven_maximum_and_mixed_hex_are_exact_word_constants (supplied : LocalInputs) :
    supplied.check? (source (.decimal "0")) = some (.word Core.Word.zero, .word) ∧
    supplied.check? sevenSource = some (.word seven, .word) ∧
    supplied.check? (source maximumPayload) = some (.word Core.Word.maximum, .word) ∧
    supplied.check? (source mixedCase) = some (.word mixedValue, .word) :=
  ⟨checked_literal supplied (interpretWordLiteral?_sound (by decide)), checked_literal supplied sevenMeaning,
    checked_literal supplied (interpretWordLiteral?_sound (by decide)),
    checked_literal supplied (interpretWordLiteral?_sound (by decide))⟩

private def once : Syntax.Expr := complement (group sevenSource)
private def twice : Syntax.Expr := group (complement once)
private def onceCore : Core.Expr := .unary .wordNot (.word seven)
private def twiceCore : Core.Expr := .unary .wordNot onceCore
private theorem checked_once (supplied : LocalInputs) : supplied.check? once = some (onceCore, .word) :=
  elaborateLocalExpression?_complete (.bitNot (.group (.wordLiteral sevenMeaning))) (.unary .word) (.unary .word)
private theorem checked_twice (supplied : LocalInputs) : supplied.check? twice = some (twiceCore, .word) :=
  elaborateLocalExpression?_complete (.group (.bitNot (.bitNot (.group (.wordLiteral sevenMeaning)))))
    (.unary (.unary .word)) (.unary (.unary .word))

theorem grouped_double_complement_preserves_the_independently_denoted_word
    (supplied : LocalInputs) (store : Core.Store) :
    supplied.check? twice = some (twiceCore, .word) ∧
    LocalExpressionHasType supplied.names supplied.context twice .word ∧
    LocalExpressionEvaluates supplied.names supplied.environment store twice (.word seven) store ∧
    Core.Evaluates (Resolved.LocalScope.values supplied.environment) store twiceCore (.word seven) store := by
  have evaluation : LocalExpressionEvaluates supplied.names supplied.environment store twice (.word seven) store := by
    simpa [twice, once, complement, group, sevenSource, source] using
      LocalExpressionEvaluates.group (LocalExpressionEvaluates.bitNot
        (LocalExpressionEvaluates.bitNot (LocalExpressionEvaluates.group
          (LocalExpressionEvaluates.wordLiteral (table := supplied.names)
            (environment := supplied.environment) sevenMeaning))))
  exact ⟨checked_twice supplied, .group (.bitNot (.bitNot (.group (.wordLiteral sevenMeaning)))),
    evaluation, (elaborateLocalExpression?_evaluates_iff (checked_twice supplied) supplied.sameIds).mp evaluation⟩

theorem literal_and_complements_have_exact_one_three_five_transition_boundaries
    (supplied : LocalInputs) (store : Core.Store) :
    supplied.run? 0 sevenSource store = some (.word, .outOfFuel
      (Core.State.initial (.word seven) (Resolved.LocalScope.values supplied.environment) store)) ∧
    supplied.run? 2 once store = some (.word, .outOfFuel ⟨.ret (.word seven), [.unaryApply .wordNot], store⟩) ∧
    supplied.run? 4 twice store = some (.word, .outOfFuel ⟨.ret (.word seven.bitNot), [.unaryApply .wordNot], store⟩) ∧
    ∀ extra, supplied.run? (extra + 1) sevenSource store = some (.word, .done (.word seven) store) ∧
      supplied.run? (extra + 3) once store = some (.word, .done (.word seven.bitNot) store) ∧
      supplied.run? (extra + 5) twice store = some (.word, .done (.word seven) store) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LocalInputs.run?, checked_seven]; rfl
  · rw [LocalInputs.run?, checked_once]; rfl
  · rw [LocalInputs.run?, checked_twice]; rfl
  · intro extra
    constructor
    · rw [LocalInputs.run?, checked_seven]
      change some (Core.Ty.word, Core.runStateful (extra + 1)
        (Core.State.initial (.word seven) (Resolved.LocalScope.values supplied.environment) store)) = _
      apply congrArg (fun result => some (Core.Ty.word, result))
      exact Core.runStateful_complete_with_fuel
        (Core.Steps.cons Core.Transition.word Core.Steps.refl) (Nat.le_add_left 1 extra)
    · constructor
      · rw [LocalInputs.run?, checked_once]
        change some (Core.Ty.word, Core.runStateful (extra + 3)
          (Core.State.initial onceCore (Resolved.LocalScope.values supplied.environment) store)) = _
        apply congrArg (fun result => some (Core.Ty.word, result))
        exact Core.runStateful_complete_with_fuel
          (Core.Steps.cons Core.Transition.enterUnary (.cons .word (.cons (.applyUnary rfl) .refl)))
          (Nat.le_add_left 3 extra)
      · rw [LocalInputs.run?, checked_twice]
        change some (Core.Ty.word, Core.runStateful (extra + 5)
          (Core.State.initial twiceCore (Resolved.LocalScope.values supplied.environment) store)) = _
        apply congrArg (fun result => some (Core.Ty.word, result))
        exact Core.runStateful_complete_with_fuel
          (Core.Steps.cons Core.Transition.enterUnary (.cons .enterUnary (.cons .word
            (.cons (.applyUnary rfl) (.cons (.applyUnary (by simp [Core.UnaryOp.apply])) .refl)))))
          (Nat.le_add_left 5 extra)

theorem word_literals_are_not_boolean_conditions_or_operands (choice : Bool) (store : Core.Store) :
    (inputs choice).check? (neg sevenSource) = none ∧
    (inputs choice).check? (andE sevenSource ref) = none ∧
    (inputs choice).check? (branch sevenSource ref ref) = none ∧
    (inputs choice).check? (branch ref sevenSource ref) = none ∧
    ∀ value finalStore, ¬ LocalExpressionEvaluates (inputs choice).names (inputs choice).environment
      store (neg sevenSource) value finalStore := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typed⟩
    cases typed with | logicalNot child => cases child
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typed⟩
    cases typed with | logicalAnd left _ => cases left
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typed⟩
    cases typed with | conditional condition _ _ => cases condition
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type, typed⟩
    cases typed with
    | conditional _ left right =>
        cases left
        have boolean : LocalExpressionHasType (inputs choice).names (inputs choice).context ref .bool :=
          .identifier .head .head
        cases boolean.type_unique right
  · intro value finalStore evaluated
    cases evaluated with | logicalNot child => cases child

theorem selected_word_right_resolves_and_evaluates_but_is_not_a_checked_conjunction (store : Core.Store) :
    ResolvesLocalExpression (inputs true).names (andE ref sevenSource)
      (.ifE (.var ⟨owner, 0⟩) (.word seven) (.bool false)) ∧
    (inputs true).check? (andE ref sevenSource) = none ∧
    LocalExpressionEvaluates (inputs true).names (inputs true).environment store
      (andE ref sevenSource) (.word seven) store ∧
    Core.Evaluates (Resolved.LocalScope.values (inputs true).environment) store
      (.ifE (.var 0) (.word seven) (.bool false)) (.word seven) store := by
  have resolution : ResolvesLocalExpression (inputs true).names (andE ref sevenSource)
      (.ifE (.var ⟨owner, 0⟩) (.word seven) (.bool false)) :=
    .logicalAnd (.identifier .head) (.wordLiteral sevenMeaning)
  have evaluation : LocalExpressionEvaluates (inputs true).names (inputs true).environment store
      (andE ref sevenSource) (.word seven) store := .andTrue (.identifier .head .head) (.wordLiteral sevenMeaning)
  refine ⟨resolution, ?_, evaluation,
    (resolution.core_evaluates_iff (environment := (inputs true).environment) (.ifE (.var .head) .word .bool)).mp evaluation⟩
  apply elaborateLocalExpression?_eq_none_iff.mpr
  rintro ⟨type, typed⟩
  cases typed with | logicalAnd _ right => cases right

private def overflow : Syntax.CoreLiteralValue :=
  .hexadecimal "0x10000000000000000000000000000000000000000000000000000000000000000"
private def badPayloads : List Syntax.CoreLiteralValue := [.decimal "1_0", overflow, .string "7"]

theorem skipped_bad_literals_are_raw_evaluable_but_never_checked
    (payload : Syntax.CoreLiteralValue) (present : payload ∈ badPayloads) (fuel : Nat) (store : Core.Store) :
    LocalExpressionEvaluates (inputs true).names (inputs true).environment store
      (branch ref sevenSource (source payload)) (.word seven) store ∧
    (inputs true).check? (branch ref sevenSource (source payload)) = none ∧
    (inputs true).run? fuel (branch ref sevenSource (source payload)) store = none ∧
    (¬ ∃ value finalStore, LocalExpressionEvaluates (inputs true).names (inputs true).environment
      store (source payload) value finalStore) := by
  have allRejected : ∀ candidate ∈ badPayloads, interpretWordLiteral? (literal candidate) = none := by decide
  have rejected := allRejected payload present
  have checkRejected : (inputs true).check? (branch ref sevenSource (source payload)) = none := by
    simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, branch, source,
      ref, inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?,
      rejected]
  refine ⟨.ifTrue (.identifier .head .head) (.wordLiteral sevenMeaning), checkRejected,
    (LocalInputs.run?_eq_none_iff fuel store).mpr checkRejected, ?_⟩
  rintro ⟨value, finalStore, evaluation⟩
  cases evaluation with
  | wordLiteral meaning =>
      have impossible := interpretWordLiteral?_complete meaning
      rw [rejected] at impossible
      cases impossible

theorem unused_input_and_identity_mapping_keep_literal_constants
    (supplied : LocalInputs) (name : String) (type : Core.Ty) (value : Core.Value)
    (typed : Core.ValueHasType value type) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) :
    (supplied.bindFresh owner name type value typed).check? sevenSource = some (.word seven, .word) ∧
    LocalExpressionEvaluates (supplied.bindFresh owner name type value typed).names
      (supplied.bindFresh owner name type value typed).environment store sevenSource (.word seven) store ∧
    (supplied.mapIds mapping injective).check? sevenSource = some (.word seven, .word) ∧
    (supplied.mapIds mapping injective).run? fuel sevenSource store = supplied.run? fuel sevenSource store := by
  have avoids : AvoidsLocalName name sevenSource := .literal
  refine ⟨?_, (avoids.bindFresh_evaluates_iff supplied owner type value typed).mpr (.wordLiteral sevenMeaning),
    (supplied.check?_mapIds mapping injective sevenSource).trans (checked_literal supplied sevenMeaning),
    supplied.run?_mapIds mapping injective fuel sevenSource store⟩
  simpa [Core.Expr.weakenAt] using
    avoids.check_bindFresh_complete supplied owner type value typed (checked_literal supplied sevenMeaning)

theorem every_invalid_literal_avoids_names_and_keeps_failed_checking
    (supplied : LocalInputs) (name : String) (type : Core.Ty) (value : Core.Value)
    (typed : Core.ValueHasType value type) (payload : Syntax.CoreLiteralValue)
    (rejected : interpretWordLiteral? (literal payload) = none)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (fuel : Nat) (store : Core.Store) :
    AvoidsLocalName name (source payload) ∧ supplied.check? (source payload) = none ∧
    (supplied.bindFresh owner name type value typed).check? (source payload) = none ∧
    (supplied.mapIds mapping injective).run? fuel (source payload) store = none := by
  have avoids : AvoidsLocalName name (source payload) := .literal
  have failed : supplied.check? (source payload) = none := by
    simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, source, rejected]
  refine ⟨avoids, failed, ?_, ?_⟩
  · simpa only [failed, Option.map_none] using avoids.check_bindFresh_eq supplied owner type value typed
  · rw [LocalInputs.run?_mapIds]
    exact (LocalInputs.run?_eq_none_iff fuel store).mpr failed

end Tests.FrontendLocalWordLiteral
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordAddition
/-! Complete canonical sources preserve addition's exact tree, modular values,
strict checking, parameter positions, and checked machine fuel boundaries. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedAddition", by decide⟩], by decide⟩⟩, 3⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)
private def store : Core.Store := [.word (word 91), .bool true]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def inputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "l" .word (.word (word 7)) .word).bindFresh
    owner "r" .word (.word (word 9)) .word).bindFresh owner "c" .bool (.bool choice) .bool

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) :
    IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-addition.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def expression (content : String) : IO Syntax.Expr := do
  let some source ← parsed? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete diagnostic-free expression")
  return source

private def checkRun (supplied : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (expected : Core.Word) (cost : Nat) : IO Unit := do
  let source ← expression content
  let checked := supplied.check? source
  assertTrue (decide (checked = some (expectedCore, .word))) s!"{content}: wrong exact Core/type"
  let some (actualCore, _) := checked | throw (IO.userError "missing checked Core")
  let initial := Core.State.initial actualCore supplied.environment.values store
  for fuel in [0, cost - 1, cost, cost + 5] do
    assertTrue (decide (supplied.run? fuel source store =
      some (.word, Core.runStateful fuel initial))) s!"{content}: bundled machine mismatch"
  assertTrue (match Core.runStateful (cost - 1) initial with
    | .outOfFuel _ => true | _ => false) s!"{content}: completed below exact cost"
  for fuel in [cost, cost + 5] do
    assertTrue (decide (Core.runStateful fuel initial = .done (.word expected) store))
      s!"{content}: wrong value, store, or completion threshold"

private def checkRejected (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves)
    s!"{content}: wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid expression checked"
  for fuel in [0, 4, 30] do
    assertTrue (supplied.run? fuel source store).isNone s!"{content}: checking was bypassed"
  let declarationText := "function rejected(l: Word, r: Word, c: Bool) returns (Word) { return "
    ++ content ++ "; }"
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module) declarationText
    | throw (IO.userError s!"{content}: wrapped declaration did not parse")
  assertTrue (compileRuntimeFunction? types owner declaration).isNone
    s!"{content}: invalid whole body compiled"

private def checkShapes : IO Unit := do
  let leftAssociated ← expression "1 + 2 + 3"
  assertTrue (match leftAssociated.value with
    | .binary ⟨_, .binary _ ⟨_, .add⟩ _⟩ ⟨_, .add⟩ _ => true
    | _ => false) "addition parser changed left associativity"
  let rightGrouped ← expression "1 + (2 + 3)"
  assertTrue (match rightGrouped.value with
    | .binary _ ⟨_, .add⟩ ⟨_, .group ⟨_, .binary _ ⟨_, .add⟩ _⟩⟩ => true
    | _ => false) "addition parser lost explicit right grouping"
  let mixed ← expression "1 | 2 ^ 3 & 4 + 5"
  assertTrue (match mixed.value with
    | .binary _ ⟨_, .bitOr⟩ ⟨_, .binary _ ⟨_, .bitXor⟩
        ⟨_, .binary _ ⟨_, .bitAnd⟩ ⟨_, .binary _ ⟨_, .add⟩ _⟩⟩⟩ => true
    | _ => false) "addition/bitwise parser precedence changed"

/-- Every tested pair of source positions is retained in open Core, including
nonadjacent and repeated positions. Same-typed values remain individually visible. -/
private def checkParameterPositions : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function sum_{arity}_{left}_{right}({parameters}) returns (Word)"
          ++ " { return " ++ s!"p{left} + p{right};" ++ " }"
        let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
          | throw (IO.userError s!"{content}: expected complete declaration")
        assertTrue (match declaration.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨_, .add⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              l.value == s!"p{left}" && r.value == s!"p{right}"
          | _ => false) s!"{content}: source parameter references changed"
        let some compiled := compileRuntimeFunction? types owner declaration
          | throw (IO.userError s!"{content}: value-free compilation failed")
        let expectedCore := Core.Expr.binary .wordAdd (.var (arity - 1 - left)) (.var (arity - 1 - right))
        assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = .word))
          s!"{content}: compilation changed exact open Core/type"
        assertTrue (decide (compiled.inputs.context.values = List.replicate arity Core.Ty.word))
          s!"{content}: wrong static context"
        assertTrue (decide (compiled.inputs.names = (indices.map fun index =>
          (s!"p{index}", (⟨owner, index⟩ : Resolved.LocalId))).reverse)) s!"{content}: wrong source IDs/names"
        assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some .word))
          s!"{content}: open Core failed typing in its parameter context"
        let arguments : List TypedRuntimeArgument := indices.map fun index =>
          ⟨.word, .word (word (10 * index + 1)), .word⟩
        let some prepared := prepareRuntimeFunction? types owner declaration arguments
          | throw (IO.userError s!"{content}: matching arguments failed preparation")
        assertTrue (decide (prepared.core = compiled.core ∧ prepared.returnType = compiled.returnType ∧
          prepared.inputs.names = compiled.inputs.names ∧ prepared.inputs.context = compiled.inputs.context))
          s!"{content}: runtime preparation changed its compiled projection"
        let values := arguments.reverse.map (·.value)
        assertTrue (decide (prepared.inputs.environment.values = values)) s!"{content}: argument values were reordered"
        let initial := Core.State.initial compiled.core values store
        for fuel in List.range 8 do
          assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel store =
            some (.word, Core.runStateful fuel initial))) s!"{content}: same-fuel full result differs"
          assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel store =
            prepared.inputs.runReturnBody? fuel declaration.value.body store))
            s!"{content}: entry changed actual body execution"
        assertTrue (decide (runRuntimeFunction? types owner declaration arguments 0 store =
          some (.word, .outOfFuel initial))) s!"{content}: wrong exact zero-fuel state"
        let leftValue := word (10 * left + 1)
        let rightValue := word (10 * right + 1)
        let beforeAdd : Core.State := ⟨.ret (.word rightValue), [.binaryApply .wordAdd (.word leftValue)], store⟩
        assertTrue (decide (runRuntimeFunction? types owner declaration arguments 4 store =
          some (.word, .outOfFuel beforeAdd))) s!"{content}: wrong left/right values or fuel-four state"
        assertTrue (decide (runRuntimeFunction? types owner declaration arguments 5 store =
          some (.word, .done (.word (leftValue.add rightValue)) store))) s!"{content}: wrong exact five-fuel result"

def frontendParsedWordAdditionTests : IO Unit := do
  let supplied := inputs true
  checkRun supplied "1 + 2" (.binary .wordAdd (literal 1) (literal 2)) (word 3) 5
  checkRun supplied "/* left */ 0x01 + /* right */ 0002" (.binary .wordAdd (literal 1) (literal 2)) (word 3) 5
  checkRun supplied s!"{Core.Word.maximum.val} + 1"
    (.binary .wordAdd (.word Core.Word.maximum) (literal 1)) Core.Word.zero 5
  checkRun supplied "0 + l" (.binary .wordAdd (literal 0) (.var 2)) (word 7) 5
  checkRun supplied "r + 0" (.binary .wordAdd (.var 1) (literal 0)) (word 9) 5
  checkRun supplied "l - r" (.binary .wordSub (.var 2) (.var 1)) ((word 7).sub (word 9)) 5
  checkRun supplied "l * r" (.binary .wordMul (.var 2) (.var 1)) (word 63) 5
  checkRun supplied "1 + 2 + 3" (.binary .wordAdd (.binary .wordAdd (literal 1) (literal 2)) (literal 3)) (word 6) 9
  checkRun supplied "((1 + 2)) + 3" (.binary .wordAdd (.binary .wordAdd (literal 1) (literal 2)) (literal 3)) (word 6) 9
  checkRun supplied "1 + (2 + 3)" (.binary .wordAdd (literal 1) (.binary .wordAdd (literal 2) (literal 3))) (word 6) 9
  checkRun supplied "1 | 2 ^ 3 & 4 + 5" (.binary .wordOr (literal 1)
    (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3) (.binary .wordAdd (literal 4) (literal 5))))) (word 3) 17
  checkRun supplied "1 + 2 & 4 + 5" (.binary .wordAnd
    (.binary .wordAdd (literal 1) (literal 2)) (.binary .wordAdd (literal 4) (literal 5))) (word 1) 13
  checkRun supplied "1 + (2 & 4) + 5" (.binary .wordAdd
    (.binary .wordAdd (literal 1) (.binary .wordAnd (literal 2) (literal 4))) (literal 5)) (word 6) 13
  checkRun supplied "~(l + r)" (.unary .wordNot (.binary .wordAdd (.var 2) (.var 1))) (word 16).bitNot 7
  for choice in [false, true] do
    let selected := inputs choice
    checkRun selected "c ? l + r : 0"
      (.ifE (.var 0) (.binary .wordAdd (.var 2) (.var 1)) (literal 0))
      (word (if choice then 16 else 0)) (if choice then 8 else 4)
    checkRun selected "c ? 0 : l + r"
      (.ifE (.var 0) (literal 0) (.binary .wordAdd (.var 2) (.var 1)))
      (word (if choice then 0 else 16)) (if choice then 4 else 8)
    for content in ["c + l", "l + c", "c ? l : 0 + c", "c ? c + 0 : r"] do
      checkRejected selected content true
    for content in ["0 + missing", "missing + 0", s!"0 + {Core.wordModulus}",
        s!"{Core.wordModulus} + 0", "c ? l : 0 + missing", "c ? missing + 0 : r",
        s!"c ? l : 0 + {Core.wordModulus}", s!"c ? {Core.wordModulus} + 0 : r",
        "0 + \"1\"", "l(c)", "r(c)"] do
      checkRejected selected content false
  checkShapes
  checkParameterPositions
  for content in ["+1", "-1", "1 +", "1 + 2 3", "1 + 2 trailing", "l += r"] do
    assertTrue (← parsed? Syntax.Parser.expression content).isNone
      s!"{content}: malformed, unsupported prefix, or unconsumed source accepted"
  assertTrue (← parsed? (Syntax.Parser.functionDecl .module)
    "function trailing() returns (Word) { return 1 + 2; } trailing").isNone
    "function parser helper accepted only a valid prefix"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordArithmetic
/-! Fully parsed subtraction and multiplication retain ordered syntax/Core,
modular results, strict checking, and exact pending-frame fuel boundaries. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owner_variant : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedArithmetic", by decide⟩], by decide⟩⟩, 5⟩
private def store_variant : Core.Store := [.word (word 91), .bool false]
private def inputs_variant (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner_variant "l" .word (.word (word 7)) .word).bindFresh
    owner_variant "r" .word (.word (word 9)) .word).bindFresh owner_variant "c" .bool (.bool choice) .bool

private def parsed_variant? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) :
    IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-arithmetic.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def expression_variant (content : String) : IO Syntax.Expr := do
  let some source ← parsed_variant? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete diagnostic-free expression")
  return source

private def checkRun_variant (supplied : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (expected : Core.Word) (cost : Nat) : IO Unit := do
  let source ← expression_variant content
  let checked := supplied.check? source
  assertTrue (decide (checked = some (expectedCore, .word))) s!"{content}: wrong exact Core/type"
  let some (actualCore, _) := checked | throw (IO.userError "missing checked Core")
  let initial := Core.State.initial actualCore supplied.environment.values store_variant
  for fuel in [0, cost - 1, cost, cost + 5] do
    assertTrue (decide (supplied.run? fuel source store_variant =
      some (.word, Core.runStateful fuel initial))) s!"{content}: bundled machine mismatch"
  assertTrue (match Core.runStateful (cost - 1) initial with
    | .outOfFuel _ => true | _ => false) s!"{content}: completed below exact cost"
  for fuel in [cost, cost + 5] do
    assertTrue (decide (Core.runStateful fuel initial = .done (.word expected) store_variant))
      s!"{content}: wrong value, store, or completion threshold"

private def checkRejected_variant (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression_variant content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves)
    s!"{content}: wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid expression checked"
  for fuel in [0, 4, 30] do
    assertTrue (supplied.run? fuel source store_variant).isNone s!"{content}: checking was bypassed"
  let declarationText := "function rejected(l: Word, r: Word, c: Bool) returns (Word) { return "
    ++ content ++ "; }"
  let some declaration ← parsed_variant? (Syntax.Parser.functionDecl .module) declarationText
    | throw (IO.userError s!"{content}: wrapped declaration did not parse")
  assertTrue (compileRuntimeFunction? types owner_variant declaration).isNone
    s!"{content}: invalid whole body compiled"

private def checkShapes_variant : IO Unit := do
  let leftAssociated ← expression_variant "8 - 3 - 2"
  assertTrue (match leftAssociated.value with
    | .binary ⟨_, .binary _ ⟨_, .subtract⟩ _⟩ ⟨_, .subtract⟩ _ => true
    | _ => false) "subtraction parser changed left associativity"
  let rightGrouped ← expression_variant "8 - (3 - 2)"
  assertTrue (match rightGrouped.value with
    | .binary _ ⟨_, .subtract⟩ ⟨_, .group ⟨_, .binary _ ⟨_, .subtract⟩ _⟩⟩ => true
    | _ => false) "subtraction parser lost right grouping"
  let multiplyAssociated ← expression_variant "2 * 3 * 4"
  assertTrue (match multiplyAssociated.value with
    | .binary ⟨_, .binary _ ⟨_, .multiply⟩ _⟩ ⟨_, .multiply⟩ _ => true
    | _ => false) "multiplication parser changed left associativity"
  let mixed ← expression_variant "8 - 2 * 3 | 1"
  assertTrue (match mixed.value with
    | .binary ⟨_, .binary _ ⟨_, .subtract⟩ ⟨_, .binary _ ⟨_, .multiply⟩ _⟩⟩ ⟨_, .bitOr⟩ _ => true
    | _ => false) "arithmetic/bitwise parser precedence changed"

/-- Check each tested source pair, not just endpoint parameters. The pending
frame distinguishes left and right even when multiplication results commute. -/
private def checkParameterPositions_variant (symbol : String) (sourceOperator : Syntax.BinaryOp)
    (operator : Core.BinaryOp) (operation : Core.Word → Core.Word → Core.Word) : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function arithmetic_{arity}_{left}_{right}({parameters}) returns (Word)"
          ++ " { return " ++ s!"p{left} {symbol} p{right};" ++ " }"
        let some declaration ← parsed_variant? (Syntax.Parser.functionDecl .module) content
          | throw (IO.userError s!"{content}: expected complete declaration")
        assertTrue (match declaration.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨_, op⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              op == sourceOperator && l.value == s!"p{left}" && r.value == s!"p{right}"
          | _ => false) s!"{content}: source operator or parameter references changed"
        let some compiled := compileRuntimeFunction? types owner_variant declaration
          | throw (IO.userError s!"{content}: value-free compilation failed")
        let expectedCore := Core.Expr.binary operator (.var (arity - 1 - left)) (.var (arity - 1 - right))
        assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = .word))
          s!"{content}: compilation changed exact open Core/type"
        assertTrue (decide (compiled.inputs.context.values = List.replicate arity Core.Ty.word))
          s!"{content}: wrong static context"
        assertTrue (decide (compiled.inputs.names = (indices.map fun index =>
          (s!"p{index}", (⟨owner_variant, index⟩ : Resolved.LocalId))).reverse)) s!"{content}: wrong source IDs/names"
        assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some .word))
          s!"{content}: open Core failed typing in its parameter context"
        let arguments : List TypedRuntimeArgument := indices.map fun index =>
          ⟨.word, .word (word (10 * index + 1)), .word⟩
        let some prepared := prepareRuntimeFunction? types owner_variant declaration arguments
          | throw (IO.userError s!"{content}: matching arguments failed preparation")
        assertTrue (decide (prepared.core = compiled.core ∧ prepared.returnType = compiled.returnType ∧
          prepared.inputs.names = compiled.inputs.names ∧ prepared.inputs.context = compiled.inputs.context))
          s!"{content}: runtime preparation changed its compiled projection"
        let values := arguments.reverse.map (·.value)
        assertTrue (decide (prepared.inputs.environment.values = values)) s!"{content}: argument values were reordered"
        let initial := Core.State.initial compiled.core values store_variant
        for fuel in List.range 8 do
          assertTrue (decide (runRuntimeFunction? types owner_variant declaration arguments fuel store_variant =
            some (.word, Core.runStateful fuel initial))) s!"{content}: same-fuel full result differs"
          assertTrue (decide (runRuntimeFunction? types owner_variant declaration arguments fuel store_variant =
            prepared.inputs.runReturnBody? fuel declaration.value.body store_variant))
            s!"{content}: entry changed actual body execution"
        assertTrue (decide (runRuntimeFunction? types owner_variant declaration arguments 0 store_variant =
          some (.word, .outOfFuel initial))) s!"{content}: wrong exact zero-fuel state"
        let leftValue := word (10 * left + 1)
        let rightValue := word (10 * right + 1)
        let pending : Core.State := ⟨.ret (.word rightValue), [.binaryApply operator (.word leftValue)], store_variant⟩
        assertTrue (decide (runRuntimeFunction? types owner_variant declaration arguments 4 store_variant =
          some (.word, .outOfFuel pending))) s!"{content}: wrong left/right values or fuel-four state"
        assertTrue (decide (runRuntimeFunction? types owner_variant declaration arguments 5 store_variant =
          some (.word, .done (.word (operation leftValue rightValue)) store_variant))) s!"{content}: wrong exact five-fuel result"

private def operations : List (String × Syntax.BinaryOp × Core.BinaryOp × (Core.Word → Core.Word → Core.Word)) :=
  [("-", .subtract, .wordSub, Core.Word.sub), ("*", .multiply, .wordMul, Core.Word.mul)]

def frontendParsedWordArithmeticTests : IO Unit := do
  let supplied := inputs_variant true
  checkRun_variant supplied "0 - 1" (.binary .wordSub (literal 0) (literal 1)) Core.Word.maximum 5
  checkRun_variant supplied s!"{Core.Word.maximum.val} * 2"
    (.binary .wordMul (.word Core.Word.maximum) (literal 2)) (word (Core.wordModulus - 2)) 5
  checkRun_variant supplied "l - r" (.binary .wordSub (.var 2) (.var 1)) (word (Core.wordModulus - 2)) 5
  checkRun_variant supplied "r - l" (.binary .wordSub (.var 1) (.var 2)) (word 2) 5
  checkRun_variant supplied "/* left */ 0x09 - /* right */ 0007" (.binary .wordSub (literal 9) (literal 7)) (word 2) 5
  checkRun_variant supplied "8 - 3 - 2" (.binary .wordSub (.binary .wordSub (literal 8) (literal 3)) (literal 2)) (word 3) 9
  checkRun_variant supplied "8 - (3 - 2)" (.binary .wordSub (literal 8) (.binary .wordSub (literal 3) (literal 2))) (word 7) 9
  checkRun_variant supplied "2 * 3 * 4" (.binary .wordMul (.binary .wordMul (literal 2) (literal 3)) (literal 4)) (word 24) 9
  checkRun_variant supplied "1 + 2 * 3" (.binary .wordAdd (literal 1) (.binary .wordMul (literal 2) (literal 3))) (word 7) 9
  checkRun_variant supplied "8 - 3 * 2" (.binary .wordSub (literal 8) (.binary .wordMul (literal 3) (literal 2))) (word 2) 9
  checkRun_variant supplied "(8 - 3) * 2" (.binary .wordMul (.binary .wordSub (literal 8) (literal 3)) (literal 2)) (word 10) 9
  checkRun_variant supplied "8 - 2 * 3 | 1" (.binary .wordOr
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3))) (literal 1)) (word 3) 13
  checkRun_variant supplied "1 ^ 8 - 2 * 3" (.binary .wordXor (literal 1)
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3)))) (word 3) 13
  for (symbol, sourceOperator, operator, operation) in operations do
    checkRun_variant supplied s!"l {symbol} r" (.binary operator (.var 2) (.var 1)) (operation (word 7) (word 9)) 5
    for identity in [0, 1] do
      checkRun_variant supplied s!"{identity} {symbol} l" (.binary operator (literal identity) (.var 2))
        (operation (word identity) (word 7)) 5
      checkRun_variant supplied s!"l {symbol} {identity}" (.binary operator (.var 2) (literal identity))
        (operation (word 7) (word identity)) 5
    for choice in [false, true] do
      let selected := inputs_variant choice
      checkRun_variant selected s!"c ? l {symbol} r : 0"
        (.ifE (.var 0) (.binary operator (.var 2) (.var 1)) (literal 0))
        (if choice then operation (word 7) (word 9) else Core.Word.zero) (if choice then 8 else 4)
      checkRun_variant selected s!"c ? 0 : l {symbol} r"
        (.ifE (.var 0) (literal 0) (.binary operator (.var 2) (.var 1)))
        (if choice then Core.Word.zero else operation (word 7) (word 9)) (if choice then 4 else 8)
      for content in [s!"c {symbol} l", s!"l {symbol} c", s!"c ? l : 0 {symbol} c", s!"c ? c {symbol} 0 : r"] do
        checkRejected_variant selected content true
      for content in [s!"0 {symbol} missing", s!"missing {symbol} 0", s!"1 {symbol} missing", s!"missing {symbol} 1",
          s!"0 {symbol} {Core.wordModulus}", s!"{Core.wordModulus} {symbol} 0",
          s!"0 {symbol} \"1\"", s!"\"1\" {symbol} 0",
          s!"c ? l : 0 {symbol} missing", s!"c ? missing {symbol} 0 : r",
          s!"c ? l : 0 {symbol} {Core.wordModulus}", s!"c ? {Core.wordModulus} {symbol} 0 : r"] do
        checkRejected_variant selected content false
    checkParameterPositions_variant symbol sourceOperator operator operation
  let equality ← expression_variant "l == r"
  let equalityCore := Core.Expr.binary .wordEq (.var 2) (.var 1)
  assertTrue (decide (supplied.check? equality = some (equalityCore, .bool)))
    "Word equality must check as the actual Bool-valued Core primitive"
  let equalityInitial := Core.State.initial equalityCore supplied.environment.values store_variant
  for fuel in [0, 4, 5, 10] do
    assertTrue (decide (supplied.run? fuel equality store_variant =
      some (.bool, Core.runStateful fuel equalityInitial))) "equality changed the checked Core execution"
  assertTrue (match Core.runStateful 4 equalityInitial with | .outOfFuel _ => true | _ => false)
    "equality completed below its five-transition cost"
  assertTrue (decide (supplied.run? 5 equality store_variant = some (.bool, .done (.bool false) store_variant)))
    "equality lost its Bool result or exact five-transition cost"
  for content in ["l(c)", "r(c)"] do
    checkRejected_variant supplied content false
  checkShapes_variant
  for content in ["-1", "+1", "8 -", "2 *", "8 - 3 2", "2 * 3 trailing", "l -= r", "l *= r"] do
    assertTrue (← parsed_variant? Syntax.Parser.expression content).isNone
      s!"{content}: malformed, unsupported prefix, or unconsumed source accepted"
  assertTrue (← parsed_variant? (Syntax.Parser.functionDecl .module)
    "function trailing() returns (Word) { return 8 - 3 * 2; } trailing").isNone
    "function parser helper accepted only a valid prefix"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordBitwise
/-! Actual parsed-source execution for strict binary Word operators. Full AST
checking is mandatory, and expected Core shapes retain precedence and order. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owner_variant2 : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedBitwise", by decide⟩], by decide⟩⟩, 0⟩
private def literalCore (value : Nat) : Core.Expr := .word (word value)
private def inputs_variant2 (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner_variant2 "a" .word (.word (word 170)) .word).bindFresh
    owner_variant2 "b" .word (.word (word 204)) .word).bindFresh owner_variant2 "c" .bool (.bool choice) .bool

private def relabel (id : Resolved.LocalId) : Resolved.LocalId :=
  { id with binderIndex := id.binderIndex + 23 }
private theorem relabel_injective : Function.Injective relabel := by
  intro left right same
  cases left with
  | mk leftOwner leftIndex =>
      cases right with
      | mk rightOwner rightIndex =>
          have owners := congrArg Resolved.LocalId.owner same
          have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
          cases owners; cases indices; rfl

private def parsedExpression (content : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-bitwise.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  assertTrue lexed.diagnostics.isEmpty s!"{content}: unexpected lexical diagnostic"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      assertTrue next.atEnd s!"{content}: unconsumed source tokens"
      assertTrue next.diagnostics.isEmpty s!"{content}: unexpected parse diagnostic"
      pure source
  | .reject failure _ => throw (IO.userError s!"{content}: rejected expression {reprStr failure}")
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def checkRun_variant2 (supplied : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (expected : Core.Word) (required : Nat) : IO Unit := do
  let source ← parsedExpression content
  let checked := supplied.check? source
  assertTrue (decide (checked = some (expectedCore, .word))) s!"{content}: wrong checked Core or type"
  let some (actualCore, _) := checked
    | throw (IO.userError s!"{content}: expression did not check")
  let initial := Core.State.initial actualCore (Resolved.LocalScope.values supplied.environment) store
  for fuel in [required, required + 6] do
    assertTrue (decide (Core.runStateful fuel initial = .done (.word expected) store))
      s!"{content}: wrong checked value or final store"
  assertTrue (match Core.runStateful (required - 1) initial with
    | .outOfFuel _ => true | _ => false) s!"{content}: wrong exact fuel boundary"
  assertTrue (decide (supplied.run? required source store = some (.word, .done (.word expected) store)))
    s!"{content}: bundled execution diverged from checked Core"

private def checkRejected_variant2 (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← parsedExpression content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves)
    s!"{content}: wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: expression unexpectedly checked"
  for fuel in [0, 30] do
    assertTrue (supplied.run? fuel source store).isNone s!"{content}: failed checking reached execution"

private def operations_variant : List (String × Core.BinaryOp × (Core.Word → Core.Word → Core.Word) × Nat) :=
  [("&", .wordAnd, Core.Word.bitAnd, 136), ("|", .wordOr, Core.Word.bitOr, 238),
    ("^", .wordXor, Core.Word.bitXor, 102)]

/-- Input insertion preserves completed observations and exhaustion presence,
not the suspended states themselves. All other result fields remain exact. -/
private def sameObservation (left right : Option (Core.Ty × Core.StatefulRunResult)) : Bool :=
  match left, right with
  | some (leftType, .outOfFuel _), some (rightType, .outOfFuel _) => decide (leftType = rightType)
  | _, _ => decide (left = right)

private def checkInputInvariance : IO Unit := do
  for choice in [false, true] do
    let supplied := inputs_variant2 choice
    let extended := supplied.bindFresh owner_variant2 "extra" .unit .unit .unit
    let renamed := extended.mapIds relabel relabel_injective
    for content in ["7", "a & b", "a | b", "a ^ b", "~a & (b | 0x0F)",
        "c ? a & b : a ^ b", "c && !c", "c || !c", "c ? 7 : missing",
        "0 & missing", "c | b", "0 ^ \"7\""] do
      let source ← parsedExpression content
      assertTrue (decide (extended.check? source =
        (supplied.check? source).map (fun result => (result.1.weakenAt 0, result.2))))
        s!"{content}: unused input changed Core beyond positional weakening"
      assertTrue (decide (extended.run? 30 source store = supplied.run? 30 source store))
        s!"{content}: unused input changed a completed result or failed checking"
      assertTrue (decide (renamed.check? source = extended.check? source))
        s!"{content}: ID relabeling changed checked Core or type"
      for fuel in [0, 1, 3, 4, 5, 6, 7, 8, 13] do
        assertTrue (sameObservation (extended.run? fuel source store) (supplied.run? fuel source store))
          s!"{content}: unused input changed a same-fuel completion or exhaustion observation"
        assertTrue (decide (renamed.run? fuel source store = extended.run? fuel source store))
          s!"{content}: ID relabeling changed the result or exact suspended state"
    let constant ← parsedExpression "7"
    assertTrue (decide (extended.run? 0 constant store ≠ supplied.run? 0 constant store))
      "input insertion should retain distinct initial environments when exhausted"
    assertTrue (sameObservation (extended.run? 0 constant store) (supplied.run? 0 constant store))
      "distinct suspended states must still have equal exhaustion observations"

def frontendParsedWordBitwiseTests : IO Unit := do
  let supplied := inputs_variant2 true
  for (symbol, operator, operation, maskResult) in operations_variant do
    checkRun_variant2 supplied s!"0xAA {symbol} 0xCC"
      (.binary operator (literalCore 170) (literalCore 204)) (word maskResult) 5
    checkRun_variant2 supplied s!"a {symbol} b" (.binary operator (.var 2) (.var 1)) (word maskResult) 5
    checkRun_variant2 supplied s!"a {symbol} 0" (.binary operator (.var 2) (literalCore 0))
      (operation (word 170) Core.Word.zero) 5
    checkRun_variant2 supplied s!"a {symbol} a" (.binary operator (.var 2) (.var 2))
      (operation (word 170) (word 170)) 5
    checkRun_variant2 supplied s!"1 {symbol} 2 {symbol} 4"
      (.binary operator (.binary operator (literalCore 1) (literalCore 2)) (literalCore 4))
      (operation (operation (word 1) (word 2)) (word 4)) 9
    checkRejected_variant2 supplied s!"c {symbol} a" true
    checkRejected_variant2 supplied s!"a {symbol} c" true
    checkRejected_variant2 supplied s!"0 {symbol} missing" false
    checkRejected_variant2 supplied s!"0 {symbol} \"7\"" false
    checkRejected_variant2 supplied s!"0 {symbol} {Core.wordModulus}" false
    checkRejected_variant2 supplied s!"(c && a) {symbol} b" true
  checkRun_variant2 supplied "1 | 2 ^ 3 & 4"
    (.binary .wordOr (literalCore 1)
      (.binary .wordXor (literalCore 2) (.binary .wordAnd (literalCore 3) (literalCore 4)))) (word 3) 13
  checkRun_variant2 supplied "1 | 2 & 4"
    (.binary .wordOr (literalCore 1) (.binary .wordAnd (literalCore 2) (literalCore 4))) (word 1) 9
  checkRun_variant2 supplied "(1 | 2) & 4"
    (.binary .wordAnd (.binary .wordOr (literalCore 1) (literalCore 2)) (literalCore 4)) (word 0) 9
  checkRun_variant2 supplied " /* mask */ ~0xAA & /* right */ 0xCC"
    (.binary .wordAnd (.unary .wordNot (literalCore 170)) (literalCore 204)) (word 68) 7
  checkRun_variant2 supplied "~(0xAA & 0xCC)"
    (.unary .wordNot (.binary .wordAnd (literalCore 170) (literalCore 204))) (word 136).bitNot 7
  for choice in [false, true] do
    checkRun_variant2 (inputs_variant2 choice) "c ? 0xAA & 0xCC : 0xAA | 0xCC"
      (.ifE (.var 0) (.binary .wordAnd (literalCore 170) (literalCore 204))
        (.binary .wordOr (literalCore 170) (literalCore 204))) (word (if choice then 136 else 238)) 8
  checkRejected_variant2 supplied "(a & b) ? 1 : 0" true
  checkRejected_variant2 supplied "c && (a & b)" true
  checkRun_variant2 supplied "a + b" (.binary .wordAdd (.var 2) (.var 1)) (word 374) 5
  checkRun_variant2 supplied "a - b" (.binary .wordSub (.var 2) (.var 1)) ((word 170).sub (word 204)) 5
  checkRun_variant2 supplied "a * b" (.binary .wordMul (.var 2) (.var 1)) (word 34680) 5
  checkRejected_variant2 supplied "a(b)" false
  let rejectsTrailing ← try
    let _ ← parsedExpression "a & b 7"
    pure false
  catch error => pure (error.toString == "a & b 7: unconsumed source tokens")
  assertTrue rejectsTrailing "bitwise source helper accepted only a valid prefix"
  checkInputInvariance

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordDivision
/-! Canonical unsigned quotient and remainder preserve original operand order.
Zero divisors produce zero only after both children execute; literal boundaries,
actual typed arguments, whole checking, and genuine checkpoints stay explicit. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owner_variant3 : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedDivision", by decide⟩], by decide⟩⟩, 31⟩
private def otherOwner : Resolved.DeclarationId := { owner_variant3 with declarationIndex := 63 }
private def shift (id : Resolved.LocalId) : Resolved.LocalId := { id with binderIndex := id.binderIndex + 43 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases left; cases right; simp_all [shift]
private def wordArg (value : Nat) : TypedRuntimeArgument := ⟨.word, .word (word value), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def types_variant : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def stores : List Core.Store :=
  [[.word (word 91), .bool true], [.cellRef .word 40, .unit, .word Core.Word.maximum]]
private def result (remainder : Bool) (left right : Nat) : Core.Word :=
  word (if right == 0 then 0 else if remainder then left % right else left / right)
private def parsed_variant2? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-division.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")
private def leafValue? (expression : Core.Expr) (environment : Core.Environment) : Option Core.Value :=
  match expression with | .word value => some (.word value) | .var index => environment[index]? | _ => none

private def checkMachine (run : Nat → Option (Core.Ty × Core.StatefulRunResult)) (core : Core.Expr)
    (environment : Core.Environment) (store : Core.Store) (type : Core.Ty) (value : Core.Value)
    (cost bound : Nat) : IO Unit := do
  assertTrue (decide (0 < cost ∧ cost ≤ bound)) "selected cost exceeded its source bound"
  for fuel in List.range (bound + 3) do
    assertTrue (decide (run fuel = some (type, Core.runStateful fuel (Core.State.initial core environment store))))
      "actual compiled Core or full same-fuel result changed"
    assertTrue (match run fuel with
      | some (actualType, .done actualValue finalStore) =>
          decide (cost ≤ fuel ∧ actualType = type ∧ actualValue = value ∧ finalStore = store)
      | some (actualType, .outOfFuel checkpoint) => decide (fuel < cost ∧ actualType = type ∧ checkpoint.store = store)
      | _ => false) "wrong exact threshold, value, return type, or own store"
  for spent in List.range cost do
    let some (_, .outOfFuel checkpoint) := run spent | throw (IO.userError "genuine checkpoint disappeared")
    for remaining in List.range (cost - spent + 3) do
      let resumed := Core.runStateful remaining checkpoint
      assertTrue (decide (run (spent + remaining) = some (type, resumed))) "same-state resumption changed"
      assertTrue (match resumed with
        | .done actualValue finalStore => decide (cost - spent ≤ remaining ∧ actualValue = value ∧ finalStore = store)
        | .outOfFuel residual => decide (remaining < cost - spent ∧ residual.store = store)
        | _ => false) "wrong exact residual cost or resumed store"
  match core with
  | .binary operator left right =>
      if let (some leftValue, some rightValue) := (leafValue? left environment, leafValue? right environment) then
        let two : Core.State := ⟨.ret leftValue, [.binaryRight operator right environment], store⟩
        let four : Core.State := ⟨.ret rightValue, [.binaryApply operator leftValue], store⟩
        assertTrue (decide (run 2 = some (type, .outOfFuel two) ∧ run 4 = some (type, .outOfFuel four) ∧
          Core.runStateful 2 two = .outOfFuel four ∧ Core.runStateful 1 four = .done value store ∧
          Core.runStateful 0 four = .outOfFuel four ∧
          Core.runStateful 0 { four with continuation := [] } = .done rightValue store))
          "left/right order, both-child evaluation, multichunk resumption, or pending application changed"
  | _ => pure ()

private def checkExpression (content : String) (core : Core.Expr) (value : Core.Word) (cost : Nat) : IO Unit := do
  let some source ← parsed_variant2? Syntax.Parser.expression content | throw (IO.userError "expression did not fully parse")
  assertTrue (decide (LocalInputs.empty.check? source = some (core, .word))) "literal expression's exact Core/type changed"
  assertTrue (localExpressionFuelBound source == cost) "strict expression source bound changed"
  for store in stores do
    checkMachine (fun fuel => LocalInputs.empty.run? fuel source store) core [] store .word (.word value) cost cost

private def checkEntry (content : String) (core : Core.Expr) (type : Core.Ty) (parameterTypes : List Core.Ty)
    (bound : Nat) (cases : List (List TypedRuntimeArgument × Core.Value × Nat)) : IO Unit := do
  let some source ← parsed_variant2? (Syntax.Parser.functionDecl .module) content | throw (IO.userError "entry did not fully parse")
  match accepted : compileRuntimeFunction? types_variant owner_variant3 source with
  | none => throw (IO.userError s!"{content}: value-free compilation failed")
  | some compiled =>
      let provenance := compileRuntimeFunction?_sound accepted
      let names ← source.value.signature.parameters.elements.mapM fun parameter => do
        let .typed none name _ := parameter.value | throw (IO.userError "unsupported parameter compiled")
        pure name.value
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
        compiled.inputs.context.values = parameterTypes.reverse ∧ Core.infer? parameterTypes.reverse core = some type ∧
        compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner_variant3, index⟩ : Resolved.LocalId)))).reverse))
        "exact open Core, original source identities, or declared type changed"
      assertTrue (terminalReturnTreeFuelBound source.value.body == bound &&
        typedLetReturnTreeFuelBound source.value.body == bound) "old body or integrated entry bound changed"
      for (arguments, value, cost) in cases do
        if matching : arguments.map (·.type) = compiled.inputs.context.values.reverse then
          let some prepared := prepareRuntimeFunction? types_variant owner_variant3 source arguments
            | throw (IO.userError "actual matching arguments did not prepare")
          let mapped := prepared.inputs.mapIds shift shiftInjective
          assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧
            prepared.inputs.names = compiled.inputs.names ∧ prepared.inputs.context.values = parameterTypes.reverse ∧
            prepared.inputs.environment.values = arguments.reverse.map (·.value) ∧
            prepared.inputs.checkTerminalReturnBody? source.value.body = some (core, type) ∧
            mapped.checkTerminalReturnBody? source.value.body = some (core, type)))
            "preparation or injective relabeling changed actual arguments/Core/body"
          for store in stores do
            have _ := provenance.run_done_of_fuelBound arguments matching store
              (typedLetReturnTreeFuelBound source.value.body) (Nat.le_refl _)
            let run := fun fuel => runRuntimeFunction? types_variant owner_variant3 source arguments fuel store
            checkMachine run core (arguments.reverse.map (·.value)) store type value cost bound
            for fuel in List.range (bound + 3) do
              have _ := provenance.run_eq arguments matching fuel store
              assertTrue (decide (run fuel = runRuntimeFunction? types_variant otherOwner source arguments fuel store ∧
                run fuel = mapped.runTerminalReturnBody? fuel source.value.body store)) "owner/ID relabeling changed full states"
              for replacement in stores do
                if replacement != store then
                  assertTrue (decide (run fuel ≠ runRuntimeFunction? types_variant owner_variant3 source arguments fuel replacement))
                    "store replay erased distinct stores from full results"
        else throw (IO.userError "positive fixture supplied mismatching argument types")
      for arguments in [[], [boolArg true], [wordArg 7, boolArg false], [wordArg 7, wordArg 9, boolArg true]] do
        if arguments.map (·.type) != parameterTypes then
          assertTrue (prepareRuntimeFunction? types_variant owner_variant3 source arguments).isNone "actual argument guard was bypassed"

private def reject (content : String) (arguments : List TypedRuntimeArgument) : IO Unit := do
  let some source ← parsed_variant2? (Syntax.Parser.functionDecl .module) content | throw (IO.userError s!"{content}: negative did not parse")
  assertTrue ((compileRuntimeFunction? types_variant owner_variant3 source).isNone &&
    (prepareRuntimeFunction? types_variant owner_variant3 source arguments).isNone) s!"{content}: invalid whole entry checked"
  for store in stores do
    for fuel in [0, typedLetReturnTreeFuelBound source.value.body, 50] do
      assertTrue (runRuntimeFunction? types_variant owner_variant3 source arguments fuel store).isNone "rejection exposed an actual checkpoint"

private def positions (symbol : String) (sourceOperator : Syntax.BinaryOp) (operator : Core.BinaryOp)
    (remainder : Bool) : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function ordered({parameters}) returns (Word)" ++ "{return " ++ s!"p{left} {symbol} p{right};" ++ "}"
        let some source ← parsed_variant2? (Syntax.Parser.functionDecl .module) content | throw (IO.userError "positions did not parse")
        assertTrue (match source.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨span, op⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              op == sourceOperator && l.value == s!"p{left}" && r.value == s!"p{right}" &&
                decide (l.span.endByte ≤ span.startByte ∧ span.endByte ≤ r.span.startByte)
          | _ => false) "canonical ordered source operator/positions changed"
        let cases := [false, true].map fun zeroFirst =>
          let argumentValue := fun index => if zeroFirst && index == 0 then 0 else 10 * index + 7
          (indices.map (fun index => wordArg (argumentValue index)),
            Core.Value.word (result remainder (argumentValue left) (argumentValue right)), 5)
        checkEntry content (.binary operator (.var (arity - 1 - left)) (.var (arity - 1 - right)))
          .word (List.replicate arity .word) 5 cases

def frontendParsedWordDivisionTests : IO Unit := do
  let boundaries := [0, 1, 3, 7, 2 ^ 255, Core.Word.maximum.val]
  for (symbol, sourceOperator, operator, remainder) in
      [("/", Syntax.BinaryOp.divide, Core.BinaryOp.wordDiv, false), ("%", .modulo, .wordMod, true)] do
    let cases := boundaries.flatMap fun left => boundaries.map fun right =>
      ([wordArg left, wordArg right], Core.Value.word (result remainder left right), 5)
    checkEntry ("function divide(l: Word,r: Word) returns (Word){return l " ++ symbol ++ " r;}")
      (.binary operator (.var 1) (.var 0)) .word [.word, .word] 5 cases
    for (left, right) in [(7, 3), (3, 7), (7, 0), (0, 7), (0, 0), (Core.Word.maximum.val, 2 ^ 255)] do
      checkExpression s!" /* numerator */ (({left})) {symbol} /* divisor */ ({right})"
        (.binary operator (literal left) (literal right)) (result remainder left right) 5
    positions symbol sourceOperator operator remainder
    let branchCases := [false, true].flatMap fun choice => boundaries.map fun right =>
      ([boolArg choice, wordArg 7, wordArg right], Core.Value.word
        (if choice then result remainder 7 right else word 7), if choice then 8 else 4)
    for body in ["{return c ? l " ++ symbol ++ " r : l;}", "{if(c){return l " ++ symbol ++ " r;}else{return l;}}"] do
      checkEntry ("function selected(c: Bool,l: Word,r: Word) returns (Word)" ++ body)
        (.ifE (.var 2) (.binary operator (.var 1) (.var 0)) (.var 1)) .word [.bool, .word, .word] 8 branchCases
    let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
    let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
    let closure : TypedRuntimeArgument :=
      ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
    for (name, argument) in [("Bool", boolArg false), ("Unit", unit), ("Cell", cell), ("Fn", closure)] do
      for operand in ["x " ++ symbol ++ " y", "y " ++ symbol ++ " x"] do
        reject (s!"function wrong(x: {name},y: Word) returns (Word)" ++ "{return " ++ operand ++ ";}")
          [argument, wordArg 7]
    for choice in [false, true] do
      let arguments := [boolArg choice, wordArg 7, wordArg 3]
      for invalid in ["missing " ++ symbol ++ " r", "l " ++ symbol ++ " missing", "l(c) " ++ symbol ++ " r",
          "l " ++ symbol ++ " r(c)", s!"{Core.wordModulus} {symbol} r", s!"l {symbol} {Core.wordModulus}",
          "c " ++ symbol ++ " r", "l " ++ symbol ++ " c"] do
        for body in ["{return c ? l : " ++ invalid ++ ";}", "{if(c){return " ++ invalid ++ ";}else{return l;}}"] do
          reject ("function skipped(c: Bool,l: Word,r: Word) returns (Word)" ++ body) arguments
    reject ("function wrong(l: Word,r: Word) returns (Bool){return l " ++ symbol ++ " r;}") [wordArg 7, wordArg 3]
    reject ("function wrong(l: Word,r: Word){return l " ++ symbol ++ " r;}") [wordArg 7, wordArg 3]
    reject ("function wrong(l: Word,r: Word) returns (Unknown){return l " ++ symbol ++ " r;}") [wordArg 7, wordArg 3]
  checkExpression "20 / 3 * 2 % 7" (.binary .wordMod
    (.binary .wordMul (.binary .wordDiv (literal 20) (literal 3)) (literal 2)) (literal 7)) (word 5) 13
  checkExpression "20 / (3 * 2) % 7" (.binary .wordMod
    (.binary .wordDiv (literal 20) (.binary .wordMul (literal 3) (literal 2))) (literal 7)) (word 3) 13
  checkExpression "20 - 7 % 3 + 8 / 2" (.binary .wordAdd
    (.binary .wordSub (literal 20) (.binary .wordMod (literal 7) (literal 3)))
    (.binary .wordDiv (literal 8) (literal 2))) (word 23) 17
  checkExpression "0 / (7 % 0)" (.binary .wordDiv (literal 0) (.binary .wordMod (literal 7) (literal 0))) (word 0) 9
  let shortCases := [false, true].flatMap fun choice => boundaries.map fun right =>
    ([boolArg choice, wordArg 7, wordArg right], Core.Value.bool (choice && (result false 7 right == word 0)),
      if choice then 12 else 4)
  checkEntry "function short(c: Bool,l: Word,r: Word) returns (Bool){return c && l / r == 0;}"
    (.ifE (.var 2) (.binary .wordEq (.binary .wordDiv (.var 1) (.var 0)) (literal 0)) (.bool false))
    .bool [.bool, .word, .word] 12 shortCases
  let guardCases := boundaries.flatMap fun left => boundaries.map fun right =>
    let choice := decide (result false left right > word right)
    ([wordArg left, wordArg right], Core.Value.word (if choice then result true left right else word left),
      if choice then 16 else 12)
  checkEntry "function guard(l: Word,r: Word) returns (Word){if(l / r > r){return l % r;}else{return l;}}"
    (.ifE (.binary .wordGt (.binary .wordDiv (.var 1) (.var 0)) (.var 0))
      (.binary .wordMod (.var 1) (.var 0)) (.var 1)) .word [.word, .word] 16 guardCases
  for content in ["7 /", "7 %", "7 / 3 trailing", "7 % 3 2", "-7 / 3", "7 / -3", "l /= r", "l %= r"] do
    assertTrue (← parsed_variant2? Syntax.Parser.expression content).isNone "malformed, signed-prefix, or unconsumed expression accepted"
  assertTrue (← parsed_variant2? (Syntax.Parser.functionDecl .module)
    "function f() returns (Word){return 7 % 0;} trailing").isNone "function parser accepted only a valid prefix"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordEquality
/-! Complete source parsing connects monomorphic Word equality to Bool results,
ordered pending frames, conservative budgets, and genuine one-step resumption. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owner_variant4 : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedEquality", by decide⟩], by decide⟩⟩, 22⟩
private def types_variant2 : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def inputs_variant3 (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner_variant4 "l" .word (.word (word 7)) .word).bindFresh
    owner_variant4 "r" .word (.word (word 9)) .word).bindFresh owner_variant4 "c" .bool (.bool choice) .bool

private def parsed_variant3? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) :
    IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-equality.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def expression_variant2 (content : String) : IO Syntax.Expr := do
  let some source ← parsed_variant3? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete diagnostic-free expression")
  return source

private def checkRun_variant3 (supplied : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (expectedType : Core.Ty) (expected : Core.Value) (cost : Nat) : IO Unit := do
  let source ← expression_variant2 content
  let checked := supplied.check? source
  assertTrue (decide (checked = some (expectedCore, expectedType))) s!"{content}: wrong exact Core/type"
  assertTrue (decide (cost ≤ localExpressionFuelBound source)) s!"{content}: source budget was insufficient"
  let some (actualCore, _) := checked | throw (IO.userError "missing checked Core")
  let initial := Core.State.initial actualCore supplied.environment.values store_variant
  for fuel in List.range (cost + 3) do
    let observed := supplied.run? fuel source store_variant
    assertTrue (decide (observed = some (expectedType, Core.runStateful fuel initial)))
      s!"{content}: full checked machine result changed"
    assertTrue (match observed with
      | some (type, .done value finalStore) =>
          decide (cost ≤ fuel ∧ type = expectedType ∧ value = expected ∧ finalStore = store_variant)
      | some (type, .outOfFuel suspended) => decide (fuel < cost ∧ type = expectedType ∧ suspended.store = store_variant)
      | _ => false) s!"{content}: wrong value, store, or exact cost"

private def checkLeaf (content : String) (left right : Core.Expr)
    (leftWord rightWord : Core.Word) : IO Unit := do
  let supplied := inputs_variant3 true
  let expected := Core.Value.bool (leftWord == rightWord)
  checkRun_variant3 supplied content (.binary .wordEq left right) .bool expected 5
  let source ← expression_variant2 content
  assertTrue (localExpressionFuelBound source == 5) s!"{content}: leaf equality budget changed"
  let some (.bool, .outOfFuel checkpoint) := supplied.run? 4 source store_variant
    | throw (IO.userError "leaf equality did not yield its genuine four-fuel checkpoint")
  let pending : Core.State := ⟨.ret (.word rightWord), [.binaryApply .wordEq (.word leftWord)], store_variant⟩
  assertTrue (decide (checkpoint = pending ∧ Core.runStateful 0 checkpoint = .outOfFuel pending ∧
    Core.runStateful 1 checkpoint = .done expected store_variant)) "ordered frame or one-step residual path changed"

private def checkRejected_variant3 (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression_variant2 content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves)
    s!"{content}: wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid equality checked"
  for fuel in [0, 4, 30] do
    assertTrue (supplied.run? fuel source store_variant).isNone s!"{content}: whole checking was bypassed"
  let text := "function rejected(l: Word, r: Word, c: Bool) returns (Bool) { return " ++ content ++ "; }"
  let some declaration ← parsed_variant3? (Syntax.Parser.functionDecl .module) text
    | throw (IO.userError s!"{content}: wrapped declaration did not parse")
  assertTrue (compileRuntimeFunction? types_variant2 owner_variant4 declaration).isNone s!"{content}: invalid whole body compiled"
  for choice in [false, true] do
    let arguments : List TypedRuntimeArgument :=
      [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩, ⟨.bool, .bool choice, .bool⟩]
    assertTrue (prepareRuntimeFunction? types_variant2 owner_variant4 declaration arguments).isNone
      "a skipped invalid branch bypassed preparation"
    for fuel in [0, 5, 30] do
      assertTrue (runRuntimeFunction? types_variant2 owner_variant4 declaration arguments fuel store_variant).isNone
        "a rejected whole entry produced an execution result"

/-- All 4 + 9 + 16 ordered pairs preserve source IDs, reverse environment
positions, and distinct pending states even though terminal equality commutes. -/
private def checkParameterPositions_variant2 : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function equality_{arity}_{left}_{right}({parameters}) returns (Bool)"
          ++ " { return " ++ s!"p{left} == p{right};" ++ " }"
        let some declaration ← parsed_variant3? (Syntax.Parser.functionDecl .module) content
          | throw (IO.userError s!"{content}: expected complete declaration")
        assertTrue (match declaration.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨_, .equal⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              l.value == s!"p{left}" && r.value == s!"p{right}"
          | _ => false) s!"{content}: source operator or ordered references changed"
        assertTrue (returnBodyFuelBound declaration.value.body == 5) "parsed equality body budget changed"
        let some compiled := compileRuntimeFunction? types_variant2 owner_variant4 declaration
          | throw (IO.userError s!"{content}: value-free compilation failed")
        let expectedCore := Core.Expr.binary .wordEq (.var (arity - 1 - left)) (.var (arity - 1 - right))
        assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = .bool ∧
          compiled.inputs.context.values = List.replicate arity Core.Ty.word)) "wrong open Core/type/context"
        assertTrue (decide (compiled.inputs.names = (indices.map fun index =>
          (s!"p{index}", (⟨owner_variant4, index⟩ : Resolved.LocalId))).reverse)) "wrong ordered source IDs/names"
        let arguments : List TypedRuntimeArgument := indices.map fun index =>
          ⟨.word, .word (word (10 * index + 1)), .word⟩
        let some prepared := prepareRuntimeFunction? types_variant2 owner_variant4 declaration arguments
          | throw (IO.userError "matching actual arguments failed preparation")
        let values := arguments.reverse.map (·.value)
        assertTrue (decide (prepared.inputs.environment.values = values ∧ prepared.core = compiled.core ∧
          prepared.returnType = .bool ∧ prepared.inputs.context = compiled.inputs.context))
          "preparation changed actual ordered values or the compiled projection"
        let initial := Core.State.initial compiled.core values store_variant
        for fuel in List.range 8 do
          assertTrue (decide (runRuntimeFunction? types_variant2 owner_variant4 declaration arguments fuel store_variant =
            some (.bool, Core.runStateful fuel initial))) "same-fuel full compiled result differs"
        let pending : Core.State := ⟨.ret (.word (word (10 * right + 1))),
          [.binaryApply .wordEq (.word (word (10 * left + 1)))], store_variant⟩
        let some (.bool, .outOfFuel checkpoint) := runRuntimeFunction? types_variant2 owner_variant4 declaration arguments 4 store_variant
          | throw (IO.userError "equality entry lost its genuine fuel-four checkpoint")
        assertTrue (decide (checkpoint = pending ∧ Core.runStateful 0 checkpoint = .outOfFuel pending ∧
          Core.runStateful 1 checkpoint = .done (.bool (left == right)) store_variant))
          "source order, retained left value, or residual one-step result changed"
        if left != right then
          let swapped : Core.State := ⟨.ret (.word (word (10 * left + 1))),
            [.binaryApply .wordEq (.word (word (10 * right + 1)))], store_variant⟩
          assertTrue (decide (pending ≠ swapped ∧ Core.runStateful 1 pending = Core.runStateful 1 swapped))
            "commutativity incorrectly identified ordered intermediate states"

private def checkReturnContract : IO Unit := do
  let some declaration ← parsed_variant3? (Syntax.Parser.functionDecl .module)
    "function wrong(l: Word, r: Word) returns (Word) { return l == r; }"
    | throw (IO.userError "wrong return contract did not parse")
  let arguments : List TypedRuntimeArgument := [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
  let some bound := bindRuntimeParameters? types_variant2 owner_variant4 declaration.value.signature.parameters.elements arguments
    | throw (IO.userError "wrong return contract parameters did not bind")
  assertTrue (decide (bound.checkReturnBody? declaration.value.body =
    some (.binary .wordEq (.var 1) (.var 0), .bool))) "body-only checker lost Bool equality"
  assertTrue (compileRuntimeFunction? types_variant2 owner_variant4 declaration).isNone "Bool equality compiled with Word return"
  assertTrue (prepareRuntimeFunction? types_variant2 owner_variant4 declaration arguments).isNone "Bool equality prepared with Word return"
  for fuel in [0, 5, 30] do
    assertTrue (runRuntimeFunction? types_variant2 owner_variant4 declaration arguments fuel store_variant).isNone "return contract bypassed"

private def checkArithmeticEntry : IO Unit := do
  let some declaration ← parsed_variant3? (Syntax.Parser.functionDecl .module)
    "function guard(l: Word, r: Word) returns (Word) { return l * r == r ? l - r : l; }"
    | throw (IO.userError "arithmetic equality entry did not parse")
  let some compiled := compileRuntimeFunction? types_variant2 owner_variant4 declaration
    | throw (IO.userError "arithmetic equality entry did not compile")
  assertTrue (decide (compiled.core = .ifE
    (.binary .wordEq (.binary .wordMul (.var 1) (.var 0)) (.var 0))
    (.binary .wordSub (.var 1) (.var 0)) (.var 1) ∧ compiled.returnType = .word))
    "arithmetic equality guard changed exact compiled Core or type"
  assertTrue (returnBodyFuelBound declaration.value.body == 16) "arithmetic guard lost its source bound"
  for left in [0, 1, 7, Core.Word.maximum.val] do
    for right in [0, 1, 9] do
      let arguments : List TypedRuntimeArgument :=
        [⟨.word, .word (word left), .word⟩, ⟨.word, .word (word right), .word⟩]
      let selected := (word left).mul (word right) == word right
      let expected := Core.Value.word (if selected then (word left).sub (word right) else word left)
      let cost := if selected then 16 else 12
      let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) store_variant
      for fuel in List.range 19 do
        let observed := runRuntimeFunction? types_variant2 owner_variant4 declaration arguments fuel store_variant
        assertTrue (decide (observed = some (.word, Core.runStateful fuel initial)))
          "arithmetic entry diverged from its actual compiled machine"
        assertTrue (match observed with
          | some (.word, .done value finalStore) => decide (cost ≤ fuel ∧ value = expected ∧ finalStore = store_variant)
          | some (.word, .outOfFuel suspended) => decide (fuel < cost ∧ suspended.store = store_variant)
          | _ => false) "arithmetic equality changed the exact 12/16 path cost or result"

def frontendParsedWordEqualityTests : IO Unit := do
  let supplied := inputs_variant3 true
  checkLeaf "l == r" (.var 2) (.var 1) (word 7) (word 9)
  checkLeaf "r == l" (.var 1) (.var 2) (word 9) (word 7)
  checkLeaf "l == l" (.var 2) (.var 2) (word 7) (word 7)
  for left in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
    for right in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
      checkLeaf s!"{left} == {right}" (literal left) (literal right) (word left) (word right)
  checkLeaf "/* left */ 0x09 == /* right */ 0009" (literal 9) (literal 9) (word 9) (word 9)
  checkLeaf "((r)) == (l)" (.var 1) (.var 2) (word 9) (word 7)
  checkRun_variant3 supplied "8 - 2 * 3 | 1 == 3" (.binary .wordEq (.binary .wordOr
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3))) (literal 1)) (literal 3))
    .bool (.bool true) 17
  checkRun_variant3 supplied "1 | 2 ^ 3 & 4 + 5 * 2 == 3" (.binary .wordEq (.binary .wordOr (literal 1)
    (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3)
      (.binary .wordAdd (literal 4) (.binary .wordMul (literal 5) (literal 2)))))) (literal 3))
    .bool (.bool false) 25
  checkRun_variant3 supplied "l * r == r ? l - r : l" (.ifE
    (.binary .wordEq (.binary .wordMul (.var 2) (.var 1)) (.var 1))
    (.binary .wordSub (.var 2) (.var 1)) (.var 2)) .word (.word (word 7)) 12
  checkRun_variant3 supplied "l * r == 63 ? l - r : l" (.ifE
    (.binary .wordEq (.binary .wordMul (.var 2) (.var 1)) (literal 63))
    (.binary .wordSub (.var 2) (.var 1)) (.var 2)) .word (.word ((word 7).sub (word 9))) 16
  let unequal := Core.Expr.binary .wordEq (.var 2) (.var 1)
  let equal := Core.Expr.binary .wordEq (.var 2) (.var 2)
  checkRun_variant3 supplied "l == r && l == l" (.ifE unequal equal (.bool false)) .bool (.bool false) 8
  checkRun_variant3 supplied "l == l && l == r" (.ifE equal unequal (.bool false)) .bool (.bool false) 12
  checkRun_variant3 supplied "l == l || l == r" (.ifE equal (.bool true) unequal) .bool (.bool true) 8
  checkRun_variant3 supplied "l == r || l == l" (.ifE unequal (.bool true) equal) .bool (.bool true) 12
  for choice in [false, true] do
    let selected := inputs_variant3 choice
    checkRun_variant3 selected "l == r || l == l && c" (.ifE unequal (.bool true)
      (.ifE equal (.var 0) (.bool false))) .bool (.bool choice) 15
    checkRun_variant3 selected "c ? l == r : l == l" (.ifE (.var 0) unequal equal) .bool (.bool (!choice)) 8
    for content in ["c == l", "l == c", "c == c", "(l == r) == l", "l == (r == l)",
        "l > r == c", "c == l > r", "c ? l == r : c == c", "l == l || c == c", "l == r && c == c"] do
      checkRejected_variant3 selected content true
    for content in ["missing == 0", "0 == missing", s!"{Core.wordModulus} == 0", s!"0 == {Core.wordModulus}",
        "l == l || missing == 0", "l == r && 0 == missing", s!"l == l || 0 == {Core.wordModulus}",
        "c ? l == r : missing == 0", s!"c ? {Core.wordModulus} == 0 : r == l"] do
      checkRejected_variant3 selected content false
  for name in ["Bool", "Unit", "Cell", "Fn", "Opaque"] do
    let content := s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x == y; }"
    let some declaration ← parsed_variant3? (Syntax.Parser.functionDecl .module) content
      | throw (IO.userError "same non-Word operand declaration did not parse")
    assertTrue (compileRuntimeFunction? types_variant2 owner_variant4 declaration).isNone
      "same non-Word operand types accidentally enabled polymorphic equality"
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let closure : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  for (name, argument) in [("Unit", unit), ("Cell", cell), ("Fn", closure)] do
    let some declaration ← parsed_variant3? (Syntax.Parser.functionDecl .module)
      (s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x == y; }")
      | throw (IO.userError "actual non-Word fixture did not parse")
    assertTrue (prepareRuntimeFunction? types_variant2 owner_variant4 declaration [argument, argument]).isNone
      "two equal actual non-Word values enabled polymorphic equality"
    for fuel in [0, 5, 30] do
      assertTrue (runRuntimeFunction? types_variant2 owner_variant4 declaration [argument, argument] fuel store_variant).isNone
        "rejected actual non-Word equality entered execution"
  checkRun_variant3 supplied "l != r" (.unary .boolNot (.binary .wordEq (.var 2) (.var 1))) .bool (.bool true) 7
  checkRun_variant3 supplied "l <= r" (.unary .boolNot (.binary .wordGt (.var 2) (.var 1))) .bool (.bool true) 7
  for content in ["l(c)", "r(c)"] do
    checkRejected_variant3 supplied content false
  checkParameterPositions_variant2
  checkReturnContract
  checkArithmeticEntry
  for content in ["l == r == l", "l ==", "-1 == 0", "+1 == 0", "l == r trailing", "l == r 0"] do
    assertTrue (← parsed_variant3? Syntax.Parser.expression content).isNone
      s!"{content}: non-associative, prefix, incomplete, or unconsumed source accepted"
  assertTrue (← parsed_variant3? (Syntax.Parser.functionDecl .module)
    "function trailing(l: Word) returns (Bool) { return l == 0; } trailing").isNone
    "function parser helper accepted only a valid prefix"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordGreater
/-! Complete source parsing connects unsigned Word comparison to exact Bool
typing, ordered parameter positions, and checked machine states and costs. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owner_variant5 : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedGreater", by decide⟩], by decide⟩⟩, 6⟩
private def inputs_variant4 (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner_variant5 "l" .word (.word (word 7)) .word).bindFresh
    owner_variant5 "r" .word (.word (word 9)) .word).bindFresh owner_variant5 "c" .bool (.bool choice) .bool

private def parsed_variant4? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) :
    IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-greater.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def expression_variant3 (content : String) : IO Syntax.Expr := do
  let some source ← parsed_variant4? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete diagnostic-free expression")
  return source

private def checkRun_variant4 (supplied : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (expectedType : Core.Ty) (expected : Core.Value) (cost : Nat) : IO Unit := do
  let source ← expression_variant3 content
  let checked := supplied.check? source
  assertTrue (decide (checked = some (expectedCore, expectedType))) s!"{content}: wrong exact Core/type"
  let some (actualCore, _) := checked | throw (IO.userError "missing checked Core")
  let initial := Core.State.initial actualCore supplied.environment.values store_variant
  for fuel in [0, cost - 1, cost, cost + 5] do
    assertTrue (decide (supplied.run? fuel source store_variant =
      some (expectedType, Core.runStateful fuel initial))) s!"{content}: bundled machine mismatch"
  assertTrue (match Core.runStateful (cost - 1) initial with
    | .outOfFuel _ => true | _ => false) s!"{content}: completed below exact cost"
  for fuel in [cost, cost + 5] do
    assertTrue (decide (Core.runStateful fuel initial = .done expected store_variant))
      s!"{content}: wrong value, store, or completion threshold"

private def checkLeaf_variant (content : String) (left right : Core.Expr)
    (leftWord rightWord : Core.Word) (expected : Bool) : IO Unit := do
  let supplied := inputs_variant4 true
  checkRun_variant4 supplied content (.binary .wordGt left right) .bool (.bool expected) 5
  let source ← expression_variant3 content
  assertTrue (decide (supplied.run? 4 source store_variant = some (.bool, .outOfFuel
    ⟨.ret (.word rightWord), [.binaryApply .wordGt (.word leftWord)], store_variant⟩)))
    s!"{content}: wrong ordered Word values in fuel-four frame"

private def checkRejected_variant4 (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression_variant3 content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves)
    s!"{content}: wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid expression checked"
  for fuel in [0, 4, 30] do
    assertTrue (supplied.run? fuel source store_variant).isNone s!"{content}: checking was bypassed"
  let text := "function rejected(l: Word, r: Word, c: Bool) returns (Bool) { return " ++ content ++ "; }"
  let some declaration ← parsed_variant4? (Syntax.Parser.functionDecl .module) text
    | throw (IO.userError s!"{content}: wrapped declaration did not parse")
  assertTrue (compileRuntimeFunction? types owner_variant5 declaration).isNone
    s!"{content}: invalid whole body compiled"

/-- All 4 + 9 + 16 ordered source pairs retain exact identity, index, value,
and the pending left-valued frame, including repeated and distant references. -/
private def checkParameterPositions_variant3 : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function greater_{arity}_{left}_{right}({parameters}) returns (Bool)"
          ++ " { return " ++ s!"p{left} > p{right};" ++ " }"
        let some declaration ← parsed_variant4? (Syntax.Parser.functionDecl .module) content
          | throw (IO.userError s!"{content}: expected complete declaration")
        assertTrue (match declaration.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨_, .greater⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              l.value == s!"p{left}" && r.value == s!"p{right}"
          | _ => false) s!"{content}: source operator or parameter references changed"
        let some compiled := compileRuntimeFunction? types owner_variant5 declaration
          | throw (IO.userError s!"{content}: value-free compilation failed")
        let expectedCore := Core.Expr.binary .wordGt (.var (arity - 1 - left)) (.var (arity - 1 - right))
        assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = .bool))
          s!"{content}: compilation changed exact open Core/type"
        assertTrue (decide (compiled.inputs.context.values = List.replicate arity Core.Ty.word))
          s!"{content}: wrong static context"
        assertTrue (decide (compiled.inputs.names = (indices.map fun index =>
          (s!"p{index}", (⟨owner_variant5, index⟩ : Resolved.LocalId))).reverse)) s!"{content}: wrong source IDs/names"
        assertTrue (decide (compiled.inputs.context.ids =
          (indices.map fun index => (⟨owner_variant5, index⟩ : Resolved.LocalId)).reverse))
          s!"{content}: wrong context identity order"
        assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some .bool))
          s!"{content}: open Core failed typing in its parameter context"
        let arguments : List TypedRuntimeArgument := indices.map fun index =>
          ⟨.word, .word (word (10 * index + 1)), .word⟩
        let some prepared := prepareRuntimeFunction? types owner_variant5 declaration arguments
          | throw (IO.userError s!"{content}: matching arguments failed preparation")
        assertTrue (decide (prepared.core = compiled.core ∧ prepared.returnType = compiled.returnType ∧
          prepared.inputs.names = compiled.inputs.names ∧ prepared.inputs.context = compiled.inputs.context))
          s!"{content}: runtime preparation changed its compiled projection"
        let values := arguments.reverse.map (·.value)
        assertTrue (decide (prepared.inputs.environment.values = values)) s!"{content}: argument values were reordered"
        let initial := Core.State.initial compiled.core values store_variant
        for fuel in List.range 8 do
          assertTrue (decide (runRuntimeFunction? types owner_variant5 declaration arguments fuel store_variant =
            some (.bool, Core.runStateful fuel initial))) s!"{content}: same-fuel full result differs"
          assertTrue (decide (runRuntimeFunction? types owner_variant5 declaration arguments fuel store_variant =
            prepared.inputs.runReturnBody? fuel declaration.value.body store_variant))
            s!"{content}: entry changed actual body execution"
        assertTrue (decide (runRuntimeFunction? types owner_variant5 declaration arguments 0 store_variant =
          some (.bool, .outOfFuel initial))) s!"{content}: wrong exact zero-fuel state"
        let leftValue := word (10 * left + 1)
        let rightValue := word (10 * right + 1)
        let pending : Core.State := ⟨.ret (.word rightValue), [.binaryApply .wordGt (.word leftValue)], store_variant⟩
        assertTrue (decide (runRuntimeFunction? types owner_variant5 declaration arguments 4 store_variant =
          some (.bool, .outOfFuel pending))) s!"{content}: wrong left/right values or fuel-four state"
        assertTrue (decide (runRuntimeFunction? types owner_variant5 declaration arguments 5 store_variant =
          some (.bool, .done (.bool (decide (left > right))) store_variant))) s!"{content}: wrong exact five-fuel result"

private def checkReturnContract_variant : IO Unit := do
  let content := "function wrong(l: Word, r: Word) returns (Word) { return r > l; }"
  let some declaration ← parsed_variant4? (Syntax.Parser.functionDecl .module) content
    | throw (IO.userError "wrong return contract did not parse")
  let arguments : List TypedRuntimeArgument := [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
  let some bound := bindRuntimeParameters? types owner_variant5 declaration.value.signature.parameters.elements arguments
    | throw (IO.userError "wrong return contract parameters did not bind")
  assertTrue (decide (bound.checkReturnBody? declaration.value.body =
    some (.binary .wordGt (.var 0) (.var 1), .bool))) "body-only checker lost Bool comparison"
  assertTrue (compileRuntimeFunction? types owner_variant5 declaration).isNone "comparison compiled with declared Word result"
  assertTrue (prepareRuntimeFunction? types owner_variant5 declaration arguments).isNone "comparison prepared with Word return"
  for fuel in [0, 5, 30] do
    assertTrue (runRuntimeFunction? types owner_variant5 declaration arguments fuel store_variant).isNone "return contract bypassed"

def frontendParsedWordGreaterTests : IO Unit := do
  let supplied := inputs_variant4 true
  checkLeaf_variant "l > r" (.var 2) (.var 1) (word 7) (word 9) false
  checkLeaf_variant "r > l" (.var 1) (.var 2) (word 9) (word 7) true
  checkLeaf_variant "l > l" (.var 2) (.var 2) (word 7) (word 7) false
  checkLeaf_variant s!"{2 ^ 255} > 0" (literal (2 ^ 255)) (literal 0) (word (2 ^ 255)) .zero true
  checkLeaf_variant s!"{Core.Word.maximum.val} > 0" (.word .maximum) (literal 0) .maximum .zero true
  checkLeaf_variant s!"0 > {Core.Word.maximum.val}" (literal 0) (.word .maximum) .zero .maximum false
  checkLeaf_variant s!"{Core.Word.maximum.val} > {Core.Word.maximum.val}" (.word .maximum) (.word .maximum) .maximum .maximum false
  checkLeaf_variant "/* left */ 0x09 > /* right */ 0007" (literal 9) (literal 7) (word 9) (word 7) true
  checkRun_variant4 supplied "((r)) > (l)" (.binary .wordGt (.var 1) (.var 2)) .bool (.bool true) 5
  checkRun_variant4 supplied "8 - 2 * 3 | 1 > 2" (.binary .wordGt (.binary .wordOr
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3))) (literal 1)) (literal 2))
    .bool (.bool true) 17
  checkRun_variant4 supplied "1 | 2 ^ 3 & 4 + 5 * 2 > 2" (.binary .wordGt (.binary .wordOr (literal 1)
    (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3)
      (.binary .wordAdd (literal 4) (.binary .wordMul (literal 5) (literal 2)))))) (literal 2))
    .bool (.bool false) 25
  checkRun_variant4 supplied "r - l > 0 ? l * r : 1" (.ifE
    (.binary .wordGt (.binary .wordSub (.var 1) (.var 2)) (literal 0))
    (.binary .wordMul (.var 2) (.var 1)) (literal 1)) .word (.word (word 63)) 16
  checkRun_variant4 supplied "r - l > 2 ? l * r : 1" (.ifE
    (.binary .wordGt (.binary .wordSub (.var 1) (.var 2)) (literal 2))
    (.binary .wordMul (.var 2) (.var 1)) (literal 1)) .word (.word (word 1)) 12
  let forward := Core.Expr.binary .wordGt (.var 2) (.var 1)
  let reversed := Core.Expr.binary .wordGt (.var 1) (.var 2)
  checkRun_variant4 supplied "l > r && r > l" (.ifE forward reversed (.bool false)) .bool (.bool false) 8
  checkRun_variant4 supplied "r > l && l > r" (.ifE reversed forward (.bool false)) .bool (.bool false) 12
  checkRun_variant4 supplied "r > l || l > r" (.ifE reversed (.bool true) forward) .bool (.bool true) 8
  checkRun_variant4 supplied "l > r || r > l" (.ifE forward (.bool true) reversed) .bool (.bool true) 12
  for choice in [false, true] do
    let selected := inputs_variant4 choice
    checkRun_variant4 selected "l > r || r > l && c" (.ifE forward (.bool true) (.ifE reversed (.var 0) (.bool false)))
      .bool (.bool choice) 15
    checkRun_variant4 selected "c ? l > r : r > l" (.ifE (.var 0) forward reversed) .bool (.bool (!choice)) 8
    for content in ["c > l", "l > c", "(l > r) > l", "l > (r > l)",
        "c ? r > l : c > l", "c ? l > c : r > l", "l > r && c > l", "r > l || l > c"] do
      checkRejected_variant4 selected content true
    for content in ["missing > 0", "0 > missing", s!"{Core.wordModulus} > 0", s!"0 > {Core.wordModulus}",
        "l > r && missing > 0", "r > l || 0 > missing", s!"r > l || 0 > {Core.wordModulus}",
        "c ? r > l : missing > 0", s!"c ? {Core.wordModulus} > 0 : r > l"] do
      checkRejected_variant4 selected content false
  checkRun_variant4 supplied "l == r" (.binary .wordEq (.var 2) (.var 1)) .bool (.bool false) 5
  checkRun_variant4 supplied "l != r" (.unary .boolNot (.binary .wordEq (.var 2) (.var 1))) .bool (.bool true) 7
  checkRun_variant4 supplied "l <= r" (.unary .boolNot (.binary .wordGt (.var 2) (.var 1))) .bool (.bool true) 7
  for content in ["l(c)", "r(c)"] do
    checkRejected_variant4 supplied content false
  checkParameterPositions_variant3
  checkReturnContract_variant
  for content in ["l > r > l", "-1 > 0", "+1 > 0", "l >", "l > r trailing", "l > r 0"] do
    assertTrue (← parsed_variant4? Syntax.Parser.expression content).isNone
      s!"{content}: non-associative, prefix, incomplete, or unconsumed source accepted"
  assertTrue (← parsed_variant4? (Syntax.Parser.functionDecl .module)
    "function trailing(l: Word) returns (Bool) { return l > 0; } trailing").isNone
    "function parser helper accepted only a valid prefix"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordGreaterEqual
/-! Fully parsed unsigned greater-than-or-equal negates two ordered Core lets.
Both operands retain their original identities. Checkpoints, environments, and
pending frames survive resumption; compilation carries its own provenance. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owner_variant6 : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedGreaterEqual", by decide⟩], by decide⟩⟩, 26⟩
private def ge (left right : Core.Expr) : Core.Expr :=
  .unary .boolNot (.letE left (.letE (right.weakenAt 0) (.binary .wordGt (.var 0) (.var 1))))
private def inputs_variant5 (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner_variant6 "l" .word (.word (word 7)) .word).bindFresh
    owner_variant6 "r" .word (.word (word 9)) .word).bindFresh owner_variant6 "c" .bool (.bool choice) .bool

private def parsed_variant5? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-greaterEqual.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")
private def expression_variant4 (content : String) : IO Syntax.Expr := do
  let some source ← parsed_variant5? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected complete diagnostic-free expression")
  return source
private def compile (declaration : Syntax.FunctionDecl) :
    IO { compiled // RuntimeFunctionCompiles types_variant2 owner_variant6 declaration compiled } :=
  match accepted : compileRuntimeFunction? types_variant2 owner_variant6 declaration with
  | some compiled => pure ⟨compiled, compileRuntimeFunction?_sound accepted⟩
  | none => throw (IO.userError "parsed declaration did not compile")

private def checkMachine_variant (run : Nat → Option (Core.Ty × Core.StatefulRunResult))
    (initial : Core.State) (type : Core.Ty) (expected : Core.Value) (cost : Nat) : IO Unit := do
  for fuel in List.range (cost + 3) do
    let observed := run fuel
    assertTrue (decide (observed = some (type, Core.runStateful fuel initial))) "full actual Core result changed"
    assertTrue (match observed with
      | some (actualType, .done value finalStore) =>
          decide (cost ≤ fuel ∧ actualType = type ∧ value = expected ∧ finalStore = store_variant)
      | some (actualType, .outOfFuel suspended) =>
          decide (fuel < cost ∧ actualType = type ∧ suspended.store = store_variant)
      | _ => false) "wrong exact cost, value, type, or store"
  for spent in List.range cost do
    let some (_, .outOfFuel checkpoint) := run spent | throw (IO.userError "genuine checkpoint missing")
    for remaining in List.range (cost - spent + 3) do
      assertTrue (decide (run (spent + remaining) = some (type, Core.runStateful remaining checkpoint)))
        "resumption changed full result or discarded a pending frame"

private def checkPending (run : Nat → Option (Core.Ty × Core.StatefulRunResult))
    (right : Core.Expr) (environment : Core.Environment) (leftWord rightWord : Core.Word) : IO Unit := do
  let body := Core.Expr.binary .wordGt (.var 0) (.var 1)
  let negation := Core.Frame.unaryApply .boolNot
  let three : Core.State := ⟨.ret (.word leftWord),
    [.letBody (.letE (right.weakenAt 0) body) environment, negation], store_variant⟩
  let six : Core.State := ⟨.ret (.word rightWord),
    [.letBody body (.word leftWord :: environment), negation], store_variant⟩
  let eleven : Core.State := ⟨.ret (.word leftWord), [.binaryApply .wordGt (.word rightWord), negation], store_variant⟩
  let twelve : Core.State := ⟨.ret (.bool (decide (leftWord < rightWord))), [negation], store_variant⟩
  let some (.bool, .outOfFuel actualThree) := run 3 | throw (IO.userError "first let checkpoint missing")
  let some (.bool, .outOfFuel actualSix) := run 6 | throw (IO.userError "second let checkpoint missing")
  let some (.bool, .outOfFuel actualEleven) := run 11 | throw (IO.userError "ordered comparison frame missing")
  let some (.bool, .outOfFuel actualTwelve) := run 12 | throw (IO.userError "negation frame missing")
  assertTrue (decide (actualThree = three ∧ actualSix = six ∧ actualEleven = eleven ∧ actualTwelve = twelve))
    "two-let order/environments or retained negation changed"
  assertTrue (decide (Core.runStateful 3 actualThree = .outOfFuel actualSix ∧
    Core.runStateful 5 actualSix = .outOfFuel actualEleven ∧ Core.runStateful 1 actualEleven = .outOfFuel actualTwelve ∧
    Core.runStateful 1 actualTwelve = .done (.bool (!(decide (leftWord < rightWord)))) store_variant ∧
    Core.runStateful 0 actualTwelve = .outOfFuel actualTwelve ∧
    Core.runStateful 0 { actualTwelve with continuation := [] } = .done (.bool (decide (leftWord < rightWord))) store_variant))
    "genuine multichunk resumption or dropped-negation counterexample changed"

private def checkRun_variant5 (supplied : LocalInputs) (content : String) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let source ← expression_variant4 content
  assertTrue (decide (supplied.check? source = some (core, type))) s!"{content}: wrong exact Core/type"
  assertTrue (decide (cost ≤ localExpressionFuelBound source)) "source-only bound insufficient"
  for fuel in [localExpressionFuelBound source, localExpressionFuelBound source + 2] do
    assertTrue (decide (supplied.run? fuel source store_variant = some (type, .done value store_variant))) "conservative bound did not finish"
  checkMachine_variant (fun fuel => supplied.run? fuel source store_variant)
    (Core.State.initial core supplied.environment.values store_variant) type value cost
private def checkLeaf_variant2 (content : String) (left right : Core.Expr) (l r : Core.Word) : IO Unit := do
  let supplied := inputs_variant5 true
  checkRun_variant5 supplied content (ge left right) .bool (.bool (!(decide (l < r)))) 13
  let source ← expression_variant4 content
  assertTrue (localExpressionFuelBound source == 13) "two leaves no longer have source bound thirteen"
  checkPending (fun fuel => supplied.run? fuel source store_variant) right supplied.environment.values l r

private def checkRejected_variant5 (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression_variant4 content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves) s!"{content}: resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid greater-than-or-equal checked"
  let some declaration ← parsed_variant5? (Syntax.Parser.functionDecl .module)
    ("function rejected(l: Word, r: Word, c: Bool) returns (Bool) { return " ++ content ++ "; }")
    | throw (IO.userError "wrapped rejection declaration did not parse")
  assertTrue (compileRuntimeFunction? types_variant2 owner_variant6 declaration).isNone "invalid whole body compiled"
  for choice in [false, true] do
    let arguments : List TypedRuntimeArgument :=
      [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩, ⟨.bool, .bool choice, .bool⟩]
    assertTrue (prepareRuntimeFunction? types_variant2 owner_variant6 declaration arguments).isNone "invalid body prepared"
    for fuel in [0, 3, 6, 11, 12, 13, 50] do
      assertTrue ((supplied.run? fuel source store_variant).isNone &&
        (runRuntimeFunction? types_variant2 owner_variant6 declaration arguments fuel store_variant).isNone) "whole rejection bypassed"

private def checkParameterPositions_variant4 : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let some declaration ← parsed_variant5? (Syntax.Parser.functionDecl .module)
          (s!"function greaterEqual_{arity}_{left}_{right}({parameters}) returns (Bool)" ++
            " { return " ++ s!"p{left} >= p{right};" ++ " }")
          | throw (IO.userError "ordered parameter declaration did not parse")
        let ⟨compiled, provenance⟩ ← compile declaration
        let core := ge (.var (arity - 1 - left)) (.var (arity - 1 - right))
        assertTrue (decide (compiled.core = core ∧ compiled.returnType = .bool ∧
          compiled.inputs.context.values = List.replicate arity Core.Ty.word ∧
          compiled.inputs.names = (indices.map fun index => (s!"p{index}", (⟨owner_variant6, index⟩ : Resolved.LocalId))).reverse))
          "open compilation changed original positions or allocated hidden source identities"
        assertTrue (returnBodyFuelBound declaration.value.body == 13) "entry source bound changed"
        match declaration.value.body.value with
        | [⟨_, .returnStmt (some source)⟩] =>
            assertTrue (match source.value with
              | .binary ⟨_, .identifier l⟩ ⟨_, .greaterEqual⟩ ⟨_, .identifier r⟩ => l.value == s!"p{left}" && r.value == s!"p{right}"
              | _ => false) "canonical operator or ordered source references changed"
            assertTrue (decide (resolveLocalExpression? compiled.inputs.names source =
              some (.unary .boolNot (.wordLt (.var ⟨owner_variant6, left⟩) (.var ⟨owner_variant6, right⟩))))) "identity-free resolved shape changed"
        | _ => throw (IO.userError "own compiled body not a single return")
        let boundaries := [0, 1, 2 ^ 255, Core.Word.maximum.val]
        let vectors := if arity == 2 && left == 0 && right == 1 then
          boundaries.flatMap (fun l => boundaries.map (fun r => [l, r])) else [indices.map (fun i => 10 * i + 1)]
        for vector in vectors do
          let arguments : List TypedRuntimeArgument := vector.map (fun value => ⟨.word, .word (word value), .word⟩)
          let some prepared := prepareRuntimeFunction? types_variant2 owner_variant6 declaration arguments
            | throw (IO.userError "actual matching arguments did not prepare")
          let values := arguments.reverse.map (·.value)
          assertTrue (decide (prepared.inputs.environment.values = values ∧ prepared.core = compiled.core ∧
            prepared.inputs.context = compiled.inputs.context ∧ prepared.returnType = compiled.returnType))
            "actual runtime values or compiled projection changed"
          if matching : arguments.map (·.type) = compiled.inputs.context.values.reverse then
            have _ := provenance.run_eq arguments matching 13 store_variant
            let run := fun fuel => runRuntimeFunction? types_variant2 owner_variant6 declaration arguments fuel store_variant
            let l := word (vector[left]!)
            let r := word (vector[right]!)
            checkMachine_variant run (Core.State.initial compiled.core values store_variant) .bool (.bool (!(decide (l < r)))) 13
            checkPending run (.var (arity - 1 - right)) values l r
          else throw (IO.userError "actual argument guard disagreed with own compilation")

private def checkArithmeticEntry_variant : IO Unit := do
  let some declaration ← parsed_variant5? (Syntax.Parser.functionDecl .module)
    "function guard(l: Word, r: Word) returns (Word) { return l * r >= r ? l - r : l; }"
    | throw (IO.userError "arithmetic entry did not parse")
  let ⟨compiled, _⟩ ← compile declaration
  assertTrue (decide (compiled.core = .ifE (ge (.binary .wordMul (.var 1) (.var 0)) (.var 0))
    (.binary .wordSub (.var 1) (.var 0)) (.var 1) ∧ compiled.returnType = .word)) "arithmetic compiled shape changed"
  assertTrue (returnBodyFuelBound declaration.value.body == 24) "arithmetic source bound changed"
  for left in [0, 1, 7, Core.Word.maximum.val] do
    for right in [0, 1, 9] do
      let arguments : List TypedRuntimeArgument := [⟨.word, .word (word left), .word⟩, ⟨.word, .word (word right), .word⟩]
      let selected := !(decide ((word left).mul (word right) < word right))
      let expected := Core.Value.word (if selected then (word left).sub (word right) else word left)
      checkMachine_variant (fun fuel => runRuntimeFunction? types_variant2 owner_variant6 declaration arguments fuel store_variant)
        (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store_variant) .word expected (if selected then 24 else 20)

private def checkReturnContract_variant2 : IO Unit := do
  let some declaration ← parsed_variant5? (Syntax.Parser.functionDecl .module)
    "function wrong(l: Word, r: Word) returns (Word) { return l >= r; }"
    | throw (IO.userError "wrong return declaration did not parse")
  let arguments : List TypedRuntimeArgument := [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
  let some bound := bindRuntimeParameters? types_variant2 owner_variant6 declaration.value.signature.parameters.elements arguments
    | throw (IO.userError "actual parameters did not bind")
  assertTrue (decide (bound.checkReturnBody? declaration.value.body = some (ge (.var 1) (.var 0), .bool))) "body lost Bool type"
  assertTrue ((compileRuntimeFunction? types_variant2 owner_variant6 declaration).isNone &&
    (prepareRuntimeFunction? types_variant2 owner_variant6 declaration arguments).isNone) "Bool body accepted under Word return contract"
  for fuel in [0, 12, 13, 50] do
    assertTrue (runRuntimeFunction? types_variant2 owner_variant6 declaration arguments fuel store_variant).isNone "return contract bypassed"

def frontendParsedWordGreaterEqualTests : IO Unit := do
  let supplied := inputs_variant5 true
  checkLeaf_variant2 "l >= r" (.var 2) (.var 1) (word 7) (word 9)
  checkLeaf_variant2 "r >= l" (.var 1) (.var 2) (word 9) (word 7)
  checkLeaf_variant2 "l >= l" (.var 2) (.var 2) (word 7) (word 7)
  for left in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
    for right in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
      checkLeaf_variant2 s!"{left} >= {right}" (literal left) (literal right) (word left) (word right)
  checkLeaf_variant2 "/* left */ 0x09 >= /* right */ 0009" (literal 9) (literal 9) (word 9) (word 9)
  checkLeaf_variant2 "((r)) >= (l)" (.var 1) (.var 2) (word 9) (word 7)
  checkRun_variant5 supplied "~0 >= 1" (ge (.unary .wordNot (literal 0)) (literal 1)) .bool (.bool true) 15
  let precedence ← expression_variant4 "l >= r == c"
  assertTrue (match precedence.value with
    | .binary ⟨_, .binary _ ⟨_, .greaterEqual⟩ _⟩ ⟨_, .equal⟩ _ => true | _ => false) "relational/equality precedence changed"
  let reversePrecedence ← expression_variant4 "c != l >= r"
  assertTrue (match reversePrecedence.value with
    | .binary _ ⟨_, .notEqual⟩ ⟨_, .binary _ ⟨_, .greaterEqual⟩ _⟩ => true | _ => false) "right relational precedence changed"
  checkRun_variant5 supplied "8 - 2 * 3 | 1 >= 3" (ge (.binary .wordOr
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3))) (literal 1)) (literal 3)) .bool (.bool true) 25
  checkRun_variant5 supplied "1 | 2 ^ 3 & 4 + 5 * 2 >= 3" (ge (.binary .wordOr (literal 1)
    (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3)
      (.binary .wordAdd (literal 4) (.binary .wordMul (literal 5) (literal 2)))))) (literal 3)) .bool (.bool false) 33
  let forward := ge (.var 2) (.var 1)
  let reversed := ge (.var 1) (.var 2)
  checkRun_variant5 supplied "!(l >= r)" (.unary .boolNot forward) .bool (.bool true) 15
  checkRun_variant5 supplied "r >= l && l >= r" (.ifE reversed forward (.bool false)) .bool (.bool false) 28
  checkRun_variant5 supplied "l >= r && r >= l" (.ifE forward reversed (.bool false)) .bool (.bool false) 16
  checkRun_variant5 supplied "l >= r || r >= l" (.ifE forward (.bool true) reversed) .bool (.bool true) 28
  checkRun_variant5 supplied "r >= l || l >= r" (.ifE reversed (.bool true) forward) .bool (.bool true) 16
  for choice in [false, true] do
    let selected := inputs_variant5 choice
    checkRun_variant5 selected "l >= r || r >= l && c" (.ifE forward (.bool true)
      (.ifE reversed (.var 0) (.bool false))) .bool (.bool choice) 31
    checkRun_variant5 selected "c ? l >= r : r >= l" (.ifE (.var 0) forward reversed) .bool (.bool (!choice)) 16
    checkRun_variant5 selected "(c ? l : r) >= (c ? r : l)" (ge (.ifE (.var 0) (.var 2) (.var 1))
      (.ifE (.var 0) (.var 1) (.var 2))) .bool (.bool (!choice)) 19
    for content in ["c >= l", "l >= c", "c >= c", "(l >= r) >= l", "l >= (r >= l)", "l >= r == c", "c != l >= r",
        "c ? l >= r : c >= c", "r >= l || c >= c", "l >= r && c >= c"] do
      checkRejected_variant5 selected content true
    for content in ["missing >= 0", "0 >= missing", s!"{Core.wordModulus} >= 0", s!"0 >= {Core.wordModulus}",
        "r >= l || missing >= 0", "l >= r && 0 >= missing", s!"r >= l || 0 >= {Core.wordModulus}", "c ? l >= r : missing >= 0"] do
      checkRejected_variant5 selected content false
  for name in ["Bool", "Unit", "Cell", "Fn", "Opaque"] do
    let some declaration ← parsed_variant5? (Syntax.Parser.functionDecl .module)
      (s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x >= y; }")
      | throw (IO.userError "non-Word declaration did not parse")
    assertTrue (compileRuntimeFunction? types_variant2 owner_variant6 declaration).isNone "matching non-Word operands enabled greater-than-or-equal"
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let closure : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  for (name, argument) in [("Unit", unit), ("Cell", cell), ("Fn", closure)] do
    for returned in ["x >= y", "y >= x"] do
      let some declaration ← parsed_variant5? (Syntax.Parser.functionDecl .module)
        (s!"function wrong(x: {name}, y: Word) returns (Bool)" ++ " { return " ++ returned ++ "; }")
        | throw (IO.userError "actual mixed operand declaration did not parse")
      let arguments := [argument, (⟨.word, .word (word 7), .word⟩ : TypedRuntimeArgument)]
      assertTrue (prepareRuntimeFunction? types_variant2 owner_variant6 declaration arguments).isNone "actual non-Word operand prepared"
      for fuel in [0, 12, 13, 50] do
        assertTrue (runRuntimeFunction? types_variant2 owner_variant6 declaration arguments fuel store_variant).isNone "actual non-Word operand ran"
  for content in ["l(c)", "r(c)"] do checkRejected_variant5 supplied content false
  checkParameterPositions_variant4
  checkReturnContract_variant2
  checkArithmeticEntry_variant
  for content in ["l >= r >= l", "l >= r > l", "l <= r >= l", "l >= r <= l", "l >=", "-1 >= 0", "+1 >= 0",
      "l >= r trailing", "l >= r 0"] do
    assertTrue (← parsed_variant5? Syntax.Parser.expression content).isNone "non-associative or incomplete source accepted"
  assertTrue (← parsed_variant5? (Syntax.Parser.functionDecl .module)
    "function trailing(l: Word) returns (Bool) { return l >= 0; } trailing").isNone "only a function prefix was accepted"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordInequality
/-! Parsed Word inequality retains ordered equality beneath an observable
negation frame. Five and six transitions are genuine, distinct checkpoints. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owner_variant7 : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedInequality", by decide⟩], by decide⟩⟩, 23⟩
private def ne (left right : Core.Expr) : Core.Expr := .unary .boolNot (.binary .wordEq left right)
private def inputs_variant6 (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner_variant7 "l" .word (.word (word 7)) .word).bindFresh
    owner_variant7 "r" .word (.word (word 9)) .word).bindFresh owner_variant7 "c" .bool (.bool choice) .bool

private def parsed_variant6? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) :
    IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-inequality.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def expression_variant5 (content : String) : IO Syntax.Expr := do
  let some source ← parsed_variant6? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete diagnostic-free expression")
  return source

private def checkRun_variant6 (supplied : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (expectedType : Core.Ty) (expected : Core.Value) (cost : Nat) : IO Unit := do
  let source ← expression_variant5 content
  assertTrue (decide (supplied.check? source = some (expectedCore, expectedType))) "wrong exact nested Core/type"
  assertTrue (decide (cost ≤ localExpressionFuelBound source)) "source budget was insufficient"
  let initial := Core.State.initial expectedCore supplied.environment.values store_variant
  for fuel in List.range (cost + 3) do
    let observed := supplied.run? fuel source store_variant
    assertTrue (decide (observed = some (expectedType, Core.runStateful fuel initial)))
      s!"{content}: full checked machine result changed"
    assertTrue (match observed with
      | some (type, .done value finalStore) =>
          decide (cost ≤ fuel ∧ type = expectedType ∧ value = expected ∧ finalStore = store_variant)
      | some (type, .outOfFuel suspended) => decide (fuel < cost ∧ type = expectedType ∧ suspended.store = store_variant)
      | _ => false) s!"{content}: wrong value, store, or exact cost"

private def checkPending_variant (run : Nat → Option (Core.Ty × Core.StatefulRunResult))
    (left right : Core.Word) : IO Unit := do
  let five : Core.State := ⟨.ret (.word right),
    [.binaryApply .wordEq (.word left), .unaryApply .boolNot], store_variant⟩
  let six : Core.State := ⟨.ret (.bool (left == right)), [.unaryApply .boolNot], store_variant⟩
  let expected := Core.Value.bool (!(left == right))
  let some (.bool, .outOfFuel actualFive) := run 5
    | throw (IO.userError "inequality lost the genuine five-fuel checkpoint")
  let some (.bool, .outOfFuel actualSix) := run 6
    | throw (IO.userError "inequality lost the genuine six-fuel checkpoint")
  assertTrue (decide (actualFive = five ∧ actualSix = six ∧ five ≠ six))
    "ordered equality and negation checkpoints changed"
  assertTrue (decide (Core.runStateful 0 actualFive = .outOfFuel five ∧
    Core.runStateful 1 actualFive = .outOfFuel six ∧ Core.runStateful 0 actualSix = .outOfFuel six ∧
    Core.runStateful 2 actualFive = .done expected store_variant ∧ Core.runStateful 1 actualSix = .done expected store_variant ∧
    run 7 = some (.bool, .done expected store_variant))) "remaining two/one transitions changed"
  for remaining in List.range 5 do
    assertTrue (decide (run (5 + remaining) = some (.bool, Core.runStateful remaining actualFive) ∧
      run (6 + remaining) = some (.bool, Core.runStateful remaining actualSix)))
      "genuine checkpoint resumption changed the full result"

private def checkLeaf_variant3 (content : String) (left right : Core.Expr)
    (leftWord rightWord : Core.Word) : IO Unit := do
  let supplied := inputs_variant6 true
  checkRun_variant6 supplied content (ne left right) .bool (.bool (!(leftWord == rightWord))) 7
  let source ← expression_variant5 content
  assertTrue (localExpressionFuelBound source == 7) "leaf inequality source budget changed"
  checkPending_variant (fun fuel => supplied.run? fuel source store_variant) leftWord rightWord

private def checkRejected_variant6 (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression_variant5 content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves) "wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid inequality checked"
  for fuel in [0, 5, 6, 7, 30] do
    assertTrue (supplied.run? fuel source store_variant).isNone "whole checking was bypassed"
  let text := "function rejected(l: Word, r: Word, c: Bool) returns (Bool) { return " ++ content ++ "; }"
  let some declaration ← parsed_variant6? (Syntax.Parser.functionDecl .module) text
    | throw (IO.userError "wrapped rejection declaration did not parse")
  assertTrue (compileRuntimeFunction? types_variant2 owner_variant7 declaration).isNone "invalid whole body compiled"
  for choice in [false, true] do
    let arguments : List TypedRuntimeArgument :=
      [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩, ⟨.bool, .bool choice, .bool⟩]
    assertTrue (prepareRuntimeFunction? types_variant2 owner_variant7 declaration arguments).isNone "invalid whole entry prepared"
    for fuel in [0, 7, 30] do
      assertTrue (runRuntimeFunction? types_variant2 owner_variant7 declaration arguments fuel store_variant).isNone
        "a skipped invalid branch bypassed whole entry rejection"

private def checkParameterPositions_variant5 : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function inequality_{arity}_{left}_{right}({parameters}) returns (Bool)"
          ++ " { return " ++ s!"p{left} != p{right};" ++ " }"
        let some declaration ← parsed_variant6? (Syntax.Parser.functionDecl .module) content
          | throw (IO.userError "ordered parameter declaration did not parse")
        assertTrue (match declaration.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨_, .notEqual⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              l.value == s!"p{left}" && r.value == s!"p{right}"
          | _ => false) "canonical inequality or ordered references changed"
        assertTrue (returnBodyFuelBound declaration.value.body == 7) "parsed inequality body budget changed"
        let some compiled := compileRuntimeFunction? types_variant2 owner_variant7 declaration
          | throw (IO.userError "ordered parameter declaration did not compile")
        assertTrue (decide (compiled.core = ne (.var (arity - 1 - left)) (.var (arity - 1 - right)) ∧
          compiled.returnType = .bool ∧ compiled.inputs.context.values = List.replicate arity Core.Ty.word))
          "wrong exact nested Core, Bool result, or parameter context"
        assertTrue (decide (compiled.inputs.names = (indices.map fun index =>
          (s!"p{index}", (⟨owner_variant7, index⟩ : Resolved.LocalId))).reverse)) "wrong ordered source IDs/names"
        let arguments : List TypedRuntimeArgument := indices.map fun index =>
          ⟨.word, .word (word (10 * index + 1)), .word⟩
        let some prepared := prepareRuntimeFunction? types_variant2 owner_variant7 declaration arguments
          | throw (IO.userError "matching actual arguments failed preparation")
        let values := arguments.reverse.map (·.value)
        assertTrue (decide (prepared.inputs.environment.values = values ∧ prepared.core = compiled.core ∧
          prepared.returnType = .bool ∧ prepared.inputs.context = compiled.inputs.context))
          "preparation changed ordered actual values or the compiled projection"
        let initial := Core.State.initial compiled.core values store_variant
        let run := fun fuel => runRuntimeFunction? types_variant2 owner_variant7 declaration arguments fuel store_variant
        for fuel in List.range 11 do
          assertTrue (decide (run fuel = some (.bool, Core.runStateful fuel initial)))
            "same-fuel full compiled result differs"
        checkPending_variant run (word (10 * left + 1)) (word (10 * right + 1))

private def checkArithmeticEntry_variant2 : IO Unit := do
  let some declaration ← parsed_variant6? (Syntax.Parser.functionDecl .module)
    "function guard(l: Word, r: Word) returns (Word) { return l * r != r ? l - r : l; }"
    | throw (IO.userError "arithmetic inequality entry did not parse")
  let some compiled := compileRuntimeFunction? types_variant2 owner_variant7 declaration
    | throw (IO.userError "arithmetic inequality entry did not compile")
  assertTrue (decide (compiled.core = .ifE (ne (.binary .wordMul (.var 1) (.var 0)) (.var 0))
    (.binary .wordSub (.var 1) (.var 0)) (.var 1) ∧ compiled.returnType = .word))
    "arithmetic inequality changed exact compiled Core or type"
  assertTrue (returnBodyFuelBound declaration.value.body == 18) "arithmetic guard source bound changed"
  for left in [0, 1, 7, Core.Word.maximum.val] do
    for right in [0, 1, 9] do
      let arguments : List TypedRuntimeArgument :=
        [⟨.word, .word (word left), .word⟩, ⟨.word, .word (word right), .word⟩]
      let selected := !((word left).mul (word right) == word right)
      let expected := Core.Value.word (if selected then (word left).sub (word right) else word left)
      let cost := if selected then 18 else 14
      let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) store_variant
      for fuel in List.range 21 do
        let observed := runRuntimeFunction? types_variant2 owner_variant7 declaration arguments fuel store_variant
        assertTrue (decide (observed = some (.word, Core.runStateful fuel initial))) "compiled guard execution changed"
        assertTrue (match observed with
          | some (.word, .done value finalStore) => decide (cost ≤ fuel ∧ value = expected ∧ finalStore = store_variant)
          | some (.word, .outOfFuel suspended) => decide (fuel < cost ∧ suspended.store = store_variant)
          | _ => false) "arithmetic inequality changed the exact 14/18 path cost or result"

private def checkReturnContract_variant3 : IO Unit := do
  let some declaration ← parsed_variant6? (Syntax.Parser.functionDecl .module)
    "function wrong(l: Word, r: Word) returns (Word) { return l != r; }"
    | throw (IO.userError "wrong return contract did not parse")
  let arguments : List TypedRuntimeArgument := [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
  let some bound := bindRuntimeParameters? types_variant2 owner_variant7 declaration.value.signature.parameters.elements arguments
    | throw (IO.userError "wrong return contract parameters did not bind")
  assertTrue (decide (bound.checkReturnBody? declaration.value.body = some (ne (.var 1) (.var 0), .bool)))
    "body-only checker lost Bool inequality"
  assertTrue (compileRuntimeFunction? types_variant2 owner_variant7 declaration).isNone "Bool inequality compiled with Word return"
  assertTrue (prepareRuntimeFunction? types_variant2 owner_variant7 declaration arguments).isNone "Bool inequality prepared with Word return"
  for fuel in [0, 7, 30] do
    assertTrue (runRuntimeFunction? types_variant2 owner_variant7 declaration arguments fuel store_variant).isNone "return contract bypassed"

def frontendParsedWordInequalityTests : IO Unit := do
  let supplied := inputs_variant6 true
  checkLeaf_variant3 "l != r" (.var 2) (.var 1) (word 7) (word 9)
  checkLeaf_variant3 "r != l" (.var 1) (.var 2) (word 9) (word 7)
  checkLeaf_variant3 "l != l" (.var 2) (.var 2) (word 7) (word 7)
  for left in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
    for right in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
      checkLeaf_variant3 s!"{left} != {right}" (literal left) (literal right) (word left) (word right)
  checkLeaf_variant3 "/* left */ 0x09 != /* right */ 0009" (literal 9) (literal 9) (word 9) (word 9)
  checkLeaf_variant3 "((r)) != (l)" (.var 1) (.var 2) (word 9) (word 7)
  checkRun_variant6 supplied "8 - 2 * 3 | 1 != 3" (ne (.binary .wordOr
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3))) (literal 1)) (literal 3))
    .bool (.bool false) 19
  checkRun_variant6 supplied "1 | 2 ^ 3 & 4 + 5 * 2 != 3" (ne (.binary .wordOr (literal 1)
    (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3)
      (.binary .wordAdd (literal 4) (.binary .wordMul (literal 5) (literal 2)))))) (literal 3))
    .bool (.bool true) 27
  let differs := ne (.var 2) (.var 1)
  let same := ne (.var 2) (.var 2)
  checkRun_variant6 supplied "l != l && l != r" (.ifE same differs (.bool false)) .bool (.bool false) 10
  checkRun_variant6 supplied "l != r && l != l" (.ifE differs same (.bool false)) .bool (.bool false) 16
  checkRun_variant6 supplied "l != r || l != l" (.ifE differs (.bool true) same) .bool (.bool true) 10
  checkRun_variant6 supplied "l != l || l != r" (.ifE same (.bool true) differs) .bool (.bool true) 16
  for choice in [false, true] do
    let selected := inputs_variant6 choice
    checkRun_variant6 selected "l != l || l != r && c" (.ifE same (.bool true)
      (.ifE differs (.var 0) (.bool false))) .bool (.bool choice) 19
    checkRun_variant6 selected "c ? l != r : l != l" (.ifE (.var 0) differs same) .bool (.bool choice) 10
    for content in ["c != l", "l != c", "c != c", "(l != r) != l", "l != (r != l)",
        "l > r != c", "c != l > r", "c ? l != r : c != c", "l != r || c != c", "l != l && c != c"] do
      checkRejected_variant6 selected content true
    for content in ["missing != 0", "0 != missing", s!"{Core.wordModulus} != 0", s!"0 != {Core.wordModulus}",
        "l != r || missing != 0", "l != l && 0 != missing", s!"l != r || 0 != {Core.wordModulus}",
        "c ? l != r : missing != 0", s!"c ? {Core.wordModulus} != 0 : r != l"] do
      checkRejected_variant6 selected content false
  for name in ["Bool", "Unit", "Cell", "Fn", "Opaque"] do
    let content := s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x != y; }"
    let some declaration ← parsed_variant6? (Syntax.Parser.functionDecl .module) content
      | throw (IO.userError "same non-Word operand declaration did not parse")
    assertTrue (compileRuntimeFunction? types_variant2 owner_variant7 declaration).isNone "matching non-Word types enabled inequality"
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let closure : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  for (name, argument) in [("Unit", unit), ("Cell", cell), ("Fn", closure)] do
    let some declaration ← parsed_variant6? (Syntax.Parser.functionDecl .module)
      (s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x != y; }")
      | throw (IO.userError "actual non-Word fixture did not parse")
    assertTrue (prepareRuntimeFunction? types_variant2 owner_variant7 declaration [argument, argument]).isNone
      "two actual non-Word values enabled inequality"
    for fuel in [0, 7, 30] do
      assertTrue (runRuntimeFunction? types_variant2 owner_variant7 declaration [argument, argument] fuel store_variant).isNone
        "rejected actual non-Word inequality entered execution"
  checkRun_variant6 supplied "l <= r" (.unary .boolNot (.binary .wordGt (.var 2) (.var 1))) .bool (.bool true) 7
  for content in ["l(c)", "r(c)"] do
    checkRejected_variant6 supplied content false
  checkParameterPositions_variant5
  checkReturnContract_variant3
  checkArithmeticEntry_variant2
  for content in ["l != r != l", "l != r == l", "l == r != l", "l !=", "-1 != 0", "+1 != 0",
      "l != r trailing", "l != r 0"] do
    assertTrue (← parsed_variant6? Syntax.Parser.expression content).isNone "non-associative or incomplete source accepted"
  assertTrue (← parsed_variant6? (Syntax.Parser.functionDecl .module)
    "function trailing(l: Word) returns (Bool) { return l != 0; } trailing").isNone
    "function parser helper accepted only a valid prefix"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordLess
/-! Fully parsed unsigned less-than retains both original operands in two Core
lets. Actual checkpoints, their environments, and their pending frames survive
resumption unchanged; type-only compilation carries its own provenance. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owner_variant8 : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedLess", by decide⟩], by decide⟩⟩, 25⟩
private def lt (left right : Core.Expr) : Core.Expr :=
  .letE left (.letE (right.weakenAt 0) (.binary .wordGt (.var 0) (.var 1)))
private def inputs_variant7 (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner_variant8 "l" .word (.word (word 7)) .word).bindFresh
    owner_variant8 "r" .word (.word (word 9)) .word).bindFresh owner_variant8 "c" .bool (.bool choice) .bool

private def parsed_variant7? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-less.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")
private def expression_variant6 (content : String) : IO Syntax.Expr := do
  let some source ← parsed_variant7? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected complete diagnostic-free expression")
  return source
private def compile_variant (declaration : Syntax.FunctionDecl) :
    IO { compiled // RuntimeFunctionCompiles types_variant2 owner_variant8 declaration compiled } :=
  match accepted : compileRuntimeFunction? types_variant2 owner_variant8 declaration with
  | some compiled => pure ⟨compiled, compileRuntimeFunction?_sound accepted⟩
  | none => throw (IO.userError "parsed declaration did not compile")

private def checkPending_variant2 (run : Nat → Option (Core.Ty × Core.StatefulRunResult))
    (right : Core.Expr) (environment : Core.Environment) (leftWord rightWord : Core.Word) : IO Unit := do
  let body := Core.Expr.binary .wordGt (.var 0) (.var 1)
  let two : Core.State := ⟨.ret (.word leftWord), [.letBody (.letE (right.weakenAt 0) body) environment], store_variant⟩
  let five : Core.State := ⟨.ret (.word rightWord), [.letBody body (.word leftWord :: environment)], store_variant⟩
  let ten : Core.State := ⟨.ret (.word leftWord), [.binaryApply .wordGt (.word rightWord)], store_variant⟩
  let some (.bool, .outOfFuel actualTwo) := run 2 | throw (IO.userError "first let checkpoint missing")
  let some (.bool, .outOfFuel actualFive) := run 5 | throw (IO.userError "second let checkpoint missing")
  let some (.bool, .outOfFuel actualTen) := run 10 | throw (IO.userError "ordered comparison frame missing")
  assertTrue (decide (actualTwo = two ∧ actualFive = five ∧ actualTen = ten)) "two-let order/environments changed"
  assertTrue (decide (Core.runStateful 3 actualTwo = .outOfFuel actualFive ∧
    Core.runStateful 5 actualFive = .outOfFuel actualTen ∧
    Core.runStateful 1 actualTen = .done (.bool (decide (leftWord < rightWord))) store_variant ∧
    Core.runStateful 0 actualTen = .outOfFuel actualTen ∧
    Core.runStateful 0 { actualTen with continuation := [] } = .done (.word leftWord) store_variant))
    "genuine multichunk resumption or dropped-frame counterexample changed"

private def checkRun_variant7 (supplied : LocalInputs) (content : String) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let source ← expression_variant6 content
  assertTrue (decide (supplied.check? source = some (core, type))) s!"{content}: wrong exact Core/type"
  assertTrue (decide (cost ≤ localExpressionFuelBound source)) "source-only bound insufficient"
  for fuel in [localExpressionFuelBound source, localExpressionFuelBound source + 2] do
    assertTrue (decide (supplied.run? fuel source store_variant = some (type, .done value store_variant))) "conservative bound did not finish"
  checkMachine_variant (fun fuel => supplied.run? fuel source store_variant)
    (Core.State.initial core supplied.environment.values store_variant) type value cost
private def checkLeaf_variant4 (content : String) (left right : Core.Expr) (l r : Core.Word) : IO Unit := do
  let supplied := inputs_variant7 true
  checkRun_variant7 supplied content (lt left right) .bool (.bool (decide (l < r))) 11
  let source ← expression_variant6 content
  assertTrue (localExpressionFuelBound source == 11) "two leaves no longer have source bound eleven"
  checkPending_variant2 (fun fuel => supplied.run? fuel source store_variant) right supplied.environment.values l r

private def checkRejected_variant7 (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression_variant6 content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves) s!"{content}: resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid less-than checked"
  let some declaration ← parsed_variant7? (Syntax.Parser.functionDecl .module)
    ("function rejected(l: Word, r: Word, c: Bool) returns (Bool) { return " ++ content ++ "; }")
    | throw (IO.userError "wrapped rejection declaration did not parse")
  assertTrue (compileRuntimeFunction? types_variant2 owner_variant8 declaration).isNone "invalid whole body compiled"
  for choice in [false, true] do
    let arguments : List TypedRuntimeArgument :=
      [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩, ⟨.bool, .bool choice, .bool⟩]
    assertTrue (prepareRuntimeFunction? types_variant2 owner_variant8 declaration arguments).isNone "invalid body prepared"
    for fuel in [0, 2, 5, 10, 11, 50] do
      assertTrue ((supplied.run? fuel source store_variant).isNone &&
        (runRuntimeFunction? types_variant2 owner_variant8 declaration arguments fuel store_variant).isNone) "whole rejection bypassed"

private def checkParameterPositions_variant6 : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let some declaration ← parsed_variant7? (Syntax.Parser.functionDecl .module)
          (s!"function less_{arity}_{left}_{right}({parameters}) returns (Bool)" ++
            " { return " ++ s!"p{left} < p{right};" ++ " }")
          | throw (IO.userError "ordered parameter declaration did not parse")
        let ⟨compiled, provenance⟩ ← compile_variant declaration
        let core := lt (.var (arity - 1 - left)) (.var (arity - 1 - right))
        assertTrue (decide (compiled.core = core ∧ compiled.returnType = .bool ∧
          compiled.inputs.context.values = List.replicate arity Core.Ty.word ∧
          compiled.inputs.names = (indices.map fun index => (s!"p{index}", (⟨owner_variant8, index⟩ : Resolved.LocalId))).reverse))
          "open compilation changed original positions or allocated hidden source identities"
        assertTrue (returnBodyFuelBound declaration.value.body == 11) "entry source bound changed"
        match declaration.value.body.value with
        | [⟨_, .returnStmt (some source)⟩] =>
            assertTrue (match source.value with
              | .binary ⟨_, .identifier l⟩ ⟨_, .less⟩ ⟨_, .identifier r⟩ => l.value == s!"p{left}" && r.value == s!"p{right}"
              | _ => false) "canonical operator or ordered source references changed"
            assertTrue (decide (resolveLocalExpression? compiled.inputs.names source =
              some (.wordLt (.var ⟨owner_variant8, left⟩) (.var ⟨owner_variant8, right⟩)))) "identity-free resolved shape changed"
        | _ => throw (IO.userError "own compiled body not a single return")
        let boundaries := [0, 1, 2 ^ 255, Core.Word.maximum.val]
        let vectors := if arity == 2 && left == 0 && right == 1 then
          boundaries.flatMap (fun l => boundaries.map (fun r => [l, r])) else [indices.map (fun i => 10 * i + 1)]
        for vector in vectors do
          let arguments : List TypedRuntimeArgument := vector.map (fun value => ⟨.word, .word (word value), .word⟩)
          let some prepared := prepareRuntimeFunction? types_variant2 owner_variant8 declaration arguments
            | throw (IO.userError "actual matching arguments did not prepare")
          let values := arguments.reverse.map (·.value)
          assertTrue (decide (prepared.inputs.environment.values = values ∧ prepared.core = compiled.core ∧
            prepared.inputs.context = compiled.inputs.context ∧ prepared.returnType = compiled.returnType))
            "actual runtime values or compiled projection changed"
          if matching : arguments.map (·.type) = compiled.inputs.context.values.reverse then
            have _ := provenance.run_eq arguments matching 11 store_variant
            let run := fun fuel => runRuntimeFunction? types_variant2 owner_variant8 declaration arguments fuel store_variant
            let l := word (vector[left]!)
            let r := word (vector[right]!)
            checkMachine_variant run (Core.State.initial compiled.core values store_variant) .bool (.bool (decide (l < r))) 11
            checkPending_variant2 run (.var (arity - 1 - right)) values l r
          else throw (IO.userError "actual argument guard disagreed with own compilation")

private def checkArithmeticEntry_variant3 : IO Unit := do
  let some declaration ← parsed_variant7? (Syntax.Parser.functionDecl .module)
    "function guard(l: Word, r: Word) returns (Word) { return l * r < r ? l - r : l; }"
    | throw (IO.userError "arithmetic entry did not parse")
  let ⟨compiled, _⟩ ← compile_variant declaration
  assertTrue (decide (compiled.core = .ifE (lt (.binary .wordMul (.var 1) (.var 0)) (.var 0))
    (.binary .wordSub (.var 1) (.var 0)) (.var 1) ∧ compiled.returnType = .word)) "arithmetic compiled shape changed"
  assertTrue (returnBodyFuelBound declaration.value.body == 22) "arithmetic source bound changed"
  for left in [0, 1, 7, Core.Word.maximum.val] do
    for right in [0, 1, 9] do
      let arguments : List TypedRuntimeArgument := [⟨.word, .word (word left), .word⟩, ⟨.word, .word (word right), .word⟩]
      let selected := decide ((word left).mul (word right) < word right)
      let expected := Core.Value.word (if selected then (word left).sub (word right) else word left)
      checkMachine_variant (fun fuel => runRuntimeFunction? types_variant2 owner_variant8 declaration arguments fuel store_variant)
        (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store_variant) .word expected (if selected then 22 else 18)

private def checkReturnContract_variant4 : IO Unit := do
  let some declaration ← parsed_variant7? (Syntax.Parser.functionDecl .module)
    "function wrong(l: Word, r: Word) returns (Word) { return l < r; }"
    | throw (IO.userError "wrong return declaration did not parse")
  let arguments : List TypedRuntimeArgument := [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
  let some bound := bindRuntimeParameters? types_variant2 owner_variant8 declaration.value.signature.parameters.elements arguments
    | throw (IO.userError "actual parameters did not bind")
  assertTrue (decide (bound.checkReturnBody? declaration.value.body = some (lt (.var 1) (.var 0), .bool))) "body lost Bool type"
  assertTrue ((compileRuntimeFunction? types_variant2 owner_variant8 declaration).isNone &&
    (prepareRuntimeFunction? types_variant2 owner_variant8 declaration arguments).isNone) "Bool body accepted under Word return contract"
  for fuel in [0, 11, 50] do
    assertTrue (runRuntimeFunction? types_variant2 owner_variant8 declaration arguments fuel store_variant).isNone "return contract bypassed"

def frontendParsedWordLessTests : IO Unit := do
  let supplied := inputs_variant7 true
  checkLeaf_variant4 "l < r" (.var 2) (.var 1) (word 7) (word 9)
  checkLeaf_variant4 "r < l" (.var 1) (.var 2) (word 9) (word 7)
  checkLeaf_variant4 "l < l" (.var 2) (.var 2) (word 7) (word 7)
  for left in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
    for right in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
      checkLeaf_variant4 s!"{left} < {right}" (literal left) (literal right) (word left) (word right)
  checkLeaf_variant4 "/* left */ 0x09 < /* right */ 0009" (literal 9) (literal 9) (word 9) (word 9)
  checkLeaf_variant4 "((r)) < (l)" (.var 1) (.var 2) (word 9) (word 7)
  checkRun_variant7 supplied "~0 < 1" (lt (.unary .wordNot (literal 0)) (literal 1)) .bool (.bool false) 13
  let precedence ← expression_variant6 "l < r == c"
  assertTrue (match precedence.value with
    | .binary ⟨_, .binary _ ⟨_, .less⟩ _⟩ ⟨_, .equal⟩ _ => true | _ => false) "relational/equality precedence changed"
  let reversePrecedence ← expression_variant6 "c != l < r"
  assertTrue (match reversePrecedence.value with
    | .binary _ ⟨_, .notEqual⟩ ⟨_, .binary _ ⟨_, .less⟩ _⟩ => true | _ => false) "right relational precedence changed"
  checkRun_variant7 supplied "8 - 2 * 3 | 1 < 3" (lt (.binary .wordOr
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3))) (literal 1)) (literal 3)) .bool (.bool false) 23
  checkRun_variant7 supplied "1 | 2 ^ 3 & 4 + 5 * 2 < 3" (lt (.binary .wordOr (literal 1)
    (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3)
      (.binary .wordAdd (literal 4) (.binary .wordMul (literal 5) (literal 2)))))) (literal 3)) .bool (.bool true) 31
  let forward := lt (.var 2) (.var 1)
  let reversed := lt (.var 1) (.var 2)
  checkRun_variant7 supplied "!(l < r)" (.unary .boolNot forward) .bool (.bool false) 13
  checkRun_variant7 supplied "r < l && l < r" (.ifE reversed forward (.bool false)) .bool (.bool false) 14
  checkRun_variant7 supplied "l < r && r < l" (.ifE forward reversed (.bool false)) .bool (.bool false) 24
  checkRun_variant7 supplied "l < r || r < l" (.ifE forward (.bool true) reversed) .bool (.bool true) 14
  checkRun_variant7 supplied "r < l || l < r" (.ifE reversed (.bool true) forward) .bool (.bool true) 24
  for choice in [false, true] do
    let selected := inputs_variant7 choice
    checkRun_variant7 selected "r < l || l < r && c" (.ifE reversed (.bool true)
      (.ifE forward (.var 0) (.bool false))) .bool (.bool choice) 27
    checkRun_variant7 selected "c ? l < r : r < l" (.ifE (.var 0) forward reversed) .bool (.bool choice) 14
    checkRun_variant7 selected "(c ? l : r) < (c ? r : l)" (lt (.ifE (.var 0) (.var 2) (.var 1))
      (.ifE (.var 0) (.var 1) (.var 2))) .bool (.bool choice) 17
    for content in ["c < l", "l < c", "c < c", "(l < r) < l", "l < (r < l)", "l < r == c", "c != l < r",
        "c ? l < r : c < c", "l < r || c < c", "r < l && c < c"] do
      checkRejected_variant7 selected content true
    for content in ["missing < 0", "0 < missing", s!"{Core.wordModulus} < 0", s!"0 < {Core.wordModulus}",
        "l < r || missing < 0", "r < l && 0 < missing", s!"l < r || 0 < {Core.wordModulus}", "c ? l < r : missing < 0"] do
      checkRejected_variant7 selected content false
  for name in ["Bool", "Unit", "Cell", "Fn", "Opaque"] do
    let some declaration ← parsed_variant7? (Syntax.Parser.functionDecl .module)
      (s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x < y; }")
      | throw (IO.userError "non-Word declaration did not parse")
    assertTrue (compileRuntimeFunction? types_variant2 owner_variant8 declaration).isNone "matching non-Word operands enabled less-than"
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let closure : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  for (name, argument) in [("Unit", unit), ("Cell", cell), ("Fn", closure)] do
    for returned in ["x < y", "y < x"] do
      let some declaration ← parsed_variant7? (Syntax.Parser.functionDecl .module)
        (s!"function wrong(x: {name}, y: Word) returns (Bool)" ++ " { return " ++ returned ++ "; }")
        | throw (IO.userError "actual mixed operand declaration did not parse")
      let arguments := [argument, (⟨.word, .word (word 7), .word⟩ : TypedRuntimeArgument)]
      assertTrue (prepareRuntimeFunction? types_variant2 owner_variant8 declaration arguments).isNone "actual non-Word operand prepared"
      for fuel in [0, 11, 50] do
        assertTrue (runRuntimeFunction? types_variant2 owner_variant8 declaration arguments fuel store_variant).isNone "actual non-Word operand ran"
  for content in ["l(c)", "r(c)"] do checkRejected_variant7 supplied content false
  checkParameterPositions_variant6
  checkReturnContract_variant4
  checkArithmeticEntry_variant3
  for content in ["l < r < l", "l < r > l", "l <= r < l", "l < r <= l", "l <", "-1 < 0", "+1 < 0",
      "l < r trailing", "l < r 0"] do
    assertTrue (← parsed_variant7? Syntax.Parser.expression content).isNone "non-associative or incomplete source accepted"
  assertTrue (← parsed_variant7? (Syntax.Parser.functionDecl .module)
    "function trailing(l: Word) returns (Bool) { return l < 0; } trailing").isNone "only a function prefix was accepted"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordLessEqual
/-! Parsed unsigned Word less-than-or-equal retains ordered greater-than beneath
a negation frame. Five and six transitions are genuine, distinct checkpoints. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def owner_variant9 : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedLessEqual", by decide⟩], by decide⟩⟩, 24⟩
private def le (left right : Core.Expr) : Core.Expr := .unary .boolNot (.binary .wordGt left right)
private def inputs_variant8 (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner_variant9 "l" .word (.word (word 7)) .word).bindFresh
    owner_variant9 "r" .word (.word (word 9)) .word).bindFresh owner_variant9 "c" .bool (.bool choice) .bool

private def parsed_variant8? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) :
    IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-lessEqual.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def expression_variant7 (content : String) : IO Syntax.Expr := do
  let some source ← parsed_variant8? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete diagnostic-free expression")
  return source

private def checkRun_variant8 (supplied : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (expectedType : Core.Ty) (expected : Core.Value) (cost : Nat) : IO Unit := do
  let source ← expression_variant7 content
  assertTrue (decide (supplied.check? source = some (expectedCore, expectedType))) "wrong exact nested Core/type"
  assertTrue (decide (cost ≤ localExpressionFuelBound source)) "source budget was insufficient"
  let initial := Core.State.initial expectedCore supplied.environment.values store_variant
  for fuel in List.range (cost + 3) do
    let observed := supplied.run? fuel source store_variant
    assertTrue (decide (observed = some (expectedType, Core.runStateful fuel initial)))
      s!"{content}: full checked machine result changed"
    assertTrue (match observed with
      | some (type, .done value finalStore) =>
          decide (cost ≤ fuel ∧ type = expectedType ∧ value = expected ∧ finalStore = store_variant)
      | some (type, .outOfFuel suspended) => decide (fuel < cost ∧ type = expectedType ∧ suspended.store = store_variant)
      | _ => false) s!"{content}: wrong value, store, or exact cost"

private def checkPending_variant3 (run : Nat → Option (Core.Ty × Core.StatefulRunResult))
    (left right : Core.Word) : IO Unit := do
  let five : Core.State := ⟨.ret (.word right),
    [.binaryApply .wordGt (.word left), .unaryApply .boolNot], store_variant⟩
  let six : Core.State := ⟨.ret (.bool (decide (left > right))), [.unaryApply .boolNot], store_variant⟩
  let expected := Core.Value.bool (!(decide (left > right)))
  let some (.bool, .outOfFuel actualFive) := run 5
    | throw (IO.userError "lessEqual lost the genuine five-fuel checkpoint")
  let some (.bool, .outOfFuel actualSix) := run 6
    | throw (IO.userError "lessEqual lost the genuine six-fuel checkpoint")
  assertTrue (decide (actualFive = five ∧ actualSix = six ∧ five ≠ six))
    "ordered greater-than and negation checkpoints changed"
  assertTrue (decide (Core.runStateful 0 actualFive = .outOfFuel five ∧
    Core.runStateful 1 actualFive = .outOfFuel six ∧ Core.runStateful 0 actualSix = .outOfFuel six ∧
    Core.runStateful 2 actualFive = .done expected store_variant ∧ Core.runStateful 1 actualSix = .done expected store_variant ∧
    run 7 = some (.bool, .done expected store_variant))) "remaining two/one transitions changed"
  for remaining in List.range 5 do
    assertTrue (decide (run (5 + remaining) = some (.bool, Core.runStateful remaining actualFive) ∧
      run (6 + remaining) = some (.bool, Core.runStateful remaining actualSix)))
      "genuine checkpoint resumption changed the full result"

private def checkLeaf_variant5 (content : String) (left right : Core.Expr)
    (leftWord rightWord : Core.Word) : IO Unit := do
  let supplied := inputs_variant8 true
  checkRun_variant8 supplied content (le left right) .bool (.bool (!(decide (leftWord > rightWord)))) 7
  let source ← expression_variant7 content
  assertTrue (localExpressionFuelBound source == 7) "leaf lessEqual source budget changed"
  checkPending_variant3 (fun fuel => supplied.run? fuel source store_variant) leftWord rightWord

private def checkRejected_variant8 (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression_variant7 content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves) "wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid lessEqual checked"
  for fuel in [0, 5, 6, 7, 30] do
    assertTrue (supplied.run? fuel source store_variant).isNone "whole checking was bypassed"
  let text := "function rejected(l: Word, r: Word, c: Bool) returns (Bool) { return " ++ content ++ "; }"
  let some declaration ← parsed_variant8? (Syntax.Parser.functionDecl .module) text
    | throw (IO.userError "wrapped rejection declaration did not parse")
  assertTrue (compileRuntimeFunction? types_variant2 owner_variant9 declaration).isNone "invalid whole body compiled"
  for choice in [false, true] do
    let arguments : List TypedRuntimeArgument :=
      [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩, ⟨.bool, .bool choice, .bool⟩]
    assertTrue (prepareRuntimeFunction? types_variant2 owner_variant9 declaration arguments).isNone "invalid whole entry prepared"
    for fuel in [0, 7, 30] do
      assertTrue (runRuntimeFunction? types_variant2 owner_variant9 declaration arguments fuel store_variant).isNone
        "a skipped invalid branch bypassed whole entry rejection"

private def checkParameterPositions_variant7 : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function lessEqual_{arity}_{left}_{right}({parameters}) returns (Bool)"
          ++ " { return " ++ s!"p{left} <= p{right};" ++ " }"
        let some declaration ← parsed_variant8? (Syntax.Parser.functionDecl .module) content
          | throw (IO.userError "ordered parameter declaration did not parse")
        assertTrue (match declaration.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨_, .lessEqual⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              l.value == s!"p{left}" && r.value == s!"p{right}"
          | _ => false) "canonical lessEqual or ordered references changed"
        assertTrue (returnBodyFuelBound declaration.value.body == 7) "parsed lessEqual body budget changed"
        let some compiled := compileRuntimeFunction? types_variant2 owner_variant9 declaration
          | throw (IO.userError "ordered parameter declaration did not compile")
        assertTrue (decide (compiled.core = le (.var (arity - 1 - left)) (.var (arity - 1 - right)) ∧
          compiled.returnType = .bool ∧ compiled.inputs.context.values = List.replicate arity Core.Ty.word))
          "wrong exact nested Core, Bool result, or parameter context"
        assertTrue (decide (compiled.inputs.names = (indices.map fun index =>
          (s!"p{index}", (⟨owner_variant9, index⟩ : Resolved.LocalId))).reverse)) "wrong ordered source IDs/names"
        let arguments : List TypedRuntimeArgument := indices.map fun index =>
          ⟨.word, .word (word (10 * index + 1)), .word⟩
        let some prepared := prepareRuntimeFunction? types_variant2 owner_variant9 declaration arguments
          | throw (IO.userError "matching actual arguments failed preparation")
        let values := arguments.reverse.map (·.value)
        assertTrue (decide (prepared.inputs.environment.values = values ∧ prepared.core = compiled.core ∧
          prepared.returnType = .bool ∧ prepared.inputs.context = compiled.inputs.context))
          "preparation changed ordered actual values or the compiled projection"
        let initial := Core.State.initial compiled.core values store_variant
        let run := fun fuel => runRuntimeFunction? types_variant2 owner_variant9 declaration arguments fuel store_variant
        for fuel in List.range 11 do
          assertTrue (decide (run fuel = some (.bool, Core.runStateful fuel initial)))
            "same-fuel full compiled result differs"
        checkPending_variant3 run (word (10 * left + 1)) (word (10 * right + 1))

private def checkArithmeticEntry_variant4 : IO Unit := do
  let some declaration ← parsed_variant8? (Syntax.Parser.functionDecl .module)
    "function guard(l: Word, r: Word) returns (Word) { return l * r <= r ? l - r : l; }"
    | throw (IO.userError "arithmetic lessEqual entry did not parse")
  let some compiled := compileRuntimeFunction? types_variant2 owner_variant9 declaration
    | throw (IO.userError "arithmetic lessEqual entry did not compile")
  assertTrue (decide (compiled.core = .ifE (le (.binary .wordMul (.var 1) (.var 0)) (.var 0))
    (.binary .wordSub (.var 1) (.var 0)) (.var 1) ∧ compiled.returnType = .word))
    "arithmetic lessEqual changed exact compiled Core or type"
  assertTrue (returnBodyFuelBound declaration.value.body == 18) "arithmetic guard source bound changed"
  for left in [0, 1, 7, Core.Word.maximum.val] do
    for right in [0, 1, 9] do
      let arguments : List TypedRuntimeArgument :=
        [⟨.word, .word (word left), .word⟩, ⟨.word, .word (word right), .word⟩]
      let selected := !(decide ((word left).mul (word right) > word right))
      let expected := Core.Value.word (if selected then (word left).sub (word right) else word left)
      let cost := if selected then 18 else 14
      let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) store_variant
      for fuel in List.range 21 do
        let observed := runRuntimeFunction? types_variant2 owner_variant9 declaration arguments fuel store_variant
        assertTrue (decide (observed = some (.word, Core.runStateful fuel initial))) "compiled guard execution changed"
        assertTrue (match observed with
          | some (.word, .done value finalStore) => decide (cost ≤ fuel ∧ value = expected ∧ finalStore = store_variant)
          | some (.word, .outOfFuel suspended) => decide (fuel < cost ∧ suspended.store = store_variant)
          | _ => false) "arithmetic lessEqual changed the exact 14/18 path cost or result"

private def checkReturnContract_variant5 : IO Unit := do
  let some declaration ← parsed_variant8? (Syntax.Parser.functionDecl .module)
    "function wrong(l: Word, r: Word) returns (Word) { return l <= r; }"
    | throw (IO.userError "wrong return contract did not parse")
  let arguments : List TypedRuntimeArgument := [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
  let some bound := bindRuntimeParameters? types_variant2 owner_variant9 declaration.value.signature.parameters.elements arguments
    | throw (IO.userError "wrong return contract parameters did not bind")
  assertTrue (decide (bound.checkReturnBody? declaration.value.body = some (le (.var 1) (.var 0), .bool)))
    "body-only checker lost Bool lessEqual"
  assertTrue (compileRuntimeFunction? types_variant2 owner_variant9 declaration).isNone "Bool lessEqual compiled with Word return"
  assertTrue (prepareRuntimeFunction? types_variant2 owner_variant9 declaration arguments).isNone "Bool lessEqual prepared with Word return"
  for fuel in [0, 7, 30] do
    assertTrue (runRuntimeFunction? types_variant2 owner_variant9 declaration arguments fuel store_variant).isNone "return contract bypassed"

def frontendParsedWordLessEqualTests : IO Unit := do
  let supplied := inputs_variant8 true
  checkLeaf_variant5 "l <= r" (.var 2) (.var 1) (word 7) (word 9)
  checkLeaf_variant5 "r <= l" (.var 1) (.var 2) (word 9) (word 7)
  checkLeaf_variant5 "l <= l" (.var 2) (.var 2) (word 7) (word 7)
  for left in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
    for right in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
      checkLeaf_variant5 s!"{left} <= {right}" (literal left) (literal right) (word left) (word right)
  checkLeaf_variant5 "/* left */ 0x09 <= /* right */ 0009" (literal 9) (literal 9) (word 9) (word 9)
  checkLeaf_variant5 "((r)) <= (l)" (.var 1) (.var 2) (word 9) (word 7)
  let relationalLeft ← expression_variant7 "l <= r == c"
  assertTrue (match relationalLeft.value with
    | .binary ⟨_, .binary _ ⟨_, .lessEqual⟩ _⟩ ⟨_, .equal⟩ _ => true
    | _ => false) "relational precedence no longer exceeds equality on the left"
  let relationalRight ← expression_variant7 "c != l <= r"
  assertTrue (match relationalRight.value with
    | .binary _ ⟨_, .notEqual⟩ ⟨_, .binary _ ⟨_, .lessEqual⟩ _⟩ => true
    | _ => false) "relational precedence no longer exceeds inequality on the right"
  checkRun_variant8 supplied "8 - 2 * 3 | 1 <= 3" (le (.binary .wordOr
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3))) (literal 1)) (literal 3))
    .bool (.bool true) 19
  checkRun_variant8 supplied "1 | 2 ^ 3 & 4 + 5 * 2 <= 3" (le (.binary .wordOr (literal 1)
    (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3)
      (.binary .wordAdd (literal 4) (.binary .wordMul (literal 5) (literal 2)))))) (literal 3))
    .bool (.bool true) 27
  let forward := le (.var 2) (.var 1)
  let reversed := le (.var 1) (.var 2)
  checkRun_variant8 supplied "r <= l && l <= r" (.ifE reversed forward (.bool false)) .bool (.bool false) 10
  checkRun_variant8 supplied "l <= r && r <= l" (.ifE forward reversed (.bool false)) .bool (.bool false) 16
  checkRun_variant8 supplied "l <= r || r <= l" (.ifE forward (.bool true) reversed) .bool (.bool true) 10
  checkRun_variant8 supplied "r <= l || l <= r" (.ifE reversed (.bool true) forward) .bool (.bool true) 16
  for choice in [false, true] do
    let selected := inputs_variant8 choice
    checkRun_variant8 selected "r <= l || l <= r && c" (.ifE reversed (.bool true)
      (.ifE forward (.var 0) (.bool false))) .bool (.bool choice) 19
    checkRun_variant8 selected "c ? l <= r : r <= l" (.ifE (.var 0) forward reversed) .bool (.bool choice) 10
    for content in ["c <= l", "l <= c", "c <= c", "(l <= r) <= l", "l <= (r <= l)",
        "l <= r == c", "c == l <= r", "c != l <= r", "l <= r == l", "l == r <= l",
        "c ? l <= r : c <= c", "l <= r || c <= c", "r <= l && c <= c"] do
      checkRejected_variant8 selected content true
    for content in ["missing <= 0", "0 <= missing", s!"{Core.wordModulus} <= 0", s!"0 <= {Core.wordModulus}",
        "l <= r || missing <= 0", "r <= l && 0 <= missing", s!"l <= r || 0 <= {Core.wordModulus}",
        "c ? l <= r : missing <= 0", s!"c ? {Core.wordModulus} <= 0 : r <= l"] do
      checkRejected_variant8 selected content false
  for name in ["Bool", "Unit", "Cell", "Fn", "Opaque"] do
    let content := s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x <= y; }"
    let some declaration ← parsed_variant8? (Syntax.Parser.functionDecl .module) content
      | throw (IO.userError "same non-Word operand declaration did not parse")
    assertTrue (compileRuntimeFunction? types_variant2 owner_variant9 declaration).isNone "matching non-Word types enabled lessEqual"
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let closure : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  for (name, argument) in [("Unit", unit), ("Cell", cell), ("Fn", closure)] do
    let some declaration ← parsed_variant8? (Syntax.Parser.functionDecl .module)
      (s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x <= y; }")
      | throw (IO.userError "actual non-Word fixture did not parse")
    assertTrue (prepareRuntimeFunction? types_variant2 owner_variant9 declaration [argument, argument]).isNone
      "two actual non-Word values enabled lessEqual"
    for fuel in [0, 7, 30] do
      assertTrue (runRuntimeFunction? types_variant2 owner_variant9 declaration [argument, argument] fuel store_variant).isNone
        "rejected actual non-Word lessEqual entered execution"
  for content in ["l(c)", "r(c)"] do
    checkRejected_variant8 supplied content false
  checkParameterPositions_variant7
  checkReturnContract_variant5
  checkArithmeticEntry_variant4
  for content in ["l <= r <= l", "l <= r > l", "l > r <= l", "l <=", "-1 <= 0", "+1 <= 0",
      "l <= r trailing", "l <= r 0"] do
    assertTrue (← parsed_variant8? Syntax.Parser.expression content).isNone "non-associative or incomplete source accepted"
  assertTrue (← parsed_variant8? (Syntax.Parser.functionDecl .module)
    "function trailing(l: Word) returns (Bool) { return l <= 0; } trailing").isNone
    "function parser helper accepted only a valid prefix"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordLiterals
/-! Full-source literal regressions for numeric interpretation and checked execution.
Parser acceptance, natural-number meaning, and strict Word range are distinct.
The monomorphic local-expression adapter admits exactly the strict Word values. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def parsedLiteral? (content : String) : IO (Option Syntax.CoreLiteral) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-word-literal.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      match source.value with
      | .literal literal => return some literal
      | _ => return none
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def checkNumeric (content : String) (expectedPayload : Syntax.CoreLiteralValue)
    (expected : Nat) : IO Unit := do
  let some literal ← parsedLiteral? content
    | throw (IO.userError s!"{content}: expected one complete literal expression")
  assertTrue (decide (literal.value = expectedPayload)) s!"{content}: changed numeric spelling"
  assertTrue (decide (numericLiteralValue? literal.value = some expected))
    s!"{content}: wrong natural-number meaning"
  let actual := interpretWordLiteral? literal
  assertTrue (decide (actual = Core.Word.ofNat? expected))
    s!"{content}: wrong strict Word range or value"
  let source : Syntax.Expr := ⟨literal.span, .literal literal⟩
  let checked := LocalInputs.empty.check? source
  let store : Core.Store := [.word Core.Word.zero, .bool false]
  match actual with
  | some word =>
      assertTrue (decide (word.val = expected)) s!"{content}: Word value was reduced"
      assertTrue (decide (checked = some (.word word, .word)))
        s!"{content}: wrong literal Core or source type"
      let some (actualCore, _) := checked
        | throw (IO.userError s!"{content}: literal did not check")
      assertTrue (decide (LocalInputs.empty.run? 0 source store =
        some (.word, .outOfFuel (Core.State.initial actualCore [] store))))
        s!"{content}: literal completed without its one transition"
      for fuel in [1, 6] do
        assertTrue (decide (LocalInputs.empty.run? fuel source store =
          some (.word, .done (.word word) store)))
          s!"{content}: checked literal changed value or store"
  | none =>
      assertTrue (decide (Core.wordModulus ≤ expected)) s!"{content}: in-range value was rejected"
      assertTrue checked.isNone s!"{content}: overflowing literal checked"
      for fuel in [0, 7] do
        assertTrue (LocalInputs.empty.run? fuel source store).isNone
          s!"{content}: overflowing literal reached execution"
  let shifted : Syntax.CoreLiteral :=
    { literal with span := ⟨⟨.main, "unrelated.sol"⟩, 900, 2⟩ }
  assertTrue (decide (interpretWordLiteral? shifted = actual))
    s!"{content}: literal interpretation depended on source ranges"
  assertTrue (decide (LocalInputs.empty.check? ⟨shifted.span, .literal shifted⟩ = checked))
    s!"{content}: literal checking depended on either source range"

def frontendParsedWordLiteralTests : IO Unit := do
  checkNumeric "0" (.decimal "0") 0
  checkNumeric "1" (.decimal "1") 1
  checkNumeric "0007" (.decimal "0007") 7
  checkNumeric " /* leading */ 0007 /* trailing */ " (.decimal "0007") 7
  checkNumeric "0x0" (.hexadecimal "0x0") 0
  checkNumeric "0x1" (.hexadecimal "0x1") 1
  checkNumeric "0xaBcD" (.hexadecimal "0xaBcD") 43981
  checkNumeric "0xAbCd" (.hexadecimal "0xAbCd") 43981
  checkNumeric "43981" (.decimal "43981") 43981
  let decimalMaximum := toString (Core.wordModulus - 1)
  let decimalOverflow := toString Core.wordModulus
  checkNumeric decimalMaximum (.decimal decimalMaximum) (Core.wordModulus - 1)
  checkNumeric decimalOverflow (.decimal decimalOverflow) Core.wordModulus
  let hexMaximum := "0x" ++ String.ofList (List.replicate 64 'F')
  let hexOverflow := "0x1" ++ String.ofList (List.replicate 64 '0')
  checkNumeric hexMaximum (.hexadecimal hexMaximum) (Core.wordModulus - 1)
  checkNumeric hexOverflow (.hexadecimal hexOverflow) Core.wordModulus
  let zeroes := String.ofList (List.replicate 100 '0')
  checkNumeric (zeroes ++ "7") (.decimal (zeroes ++ "7")) 7
  checkNumeric ("0x" ++ zeroes ++ "aF") (.hexadecimal ("0x" ++ zeroes ++ "aF")) 175
  for content in ["0x", "0Xff", "1_000", "123abc", "0x1g", "٤", "４", "1.0", "-1", "+1", "7 8"] do
    let parsed ← parsedLiteral? content
    assertTrue parsed.isNone s!"{content}: accepted an incomplete or malformed numeric expression"
  let some quoted ← parsedLiteral? "\"7\""
    | throw (IO.userError "quoted source should parse as a string literal")
  assertTrue (decide (numericLiteralValue? quoted.value = none ∧ interpretWordLiteral? quoted = none))
    "a quoted string received numeric meaning"
  assertTrue (LocalInputs.empty.check? ⟨quoted.span, .literal quoted⟩).isNone
    "a quoted string became a checked numeric expression"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendWordAdditionProperties
/-! Independent strict Word addition retains actual Core, operand order,
modular results, and exact costs through local and function-entry adapters. -/

set_option autoImplicit false

namespace Tests.FrontendWordAddition

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Addition", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "addition.sol"⟩, 17, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def add (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .add⟩ right⟩
private def source := add (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := .binary .wordAdd (.var 1) (.var 0)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.binary .wordAdd (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) :=
  .add (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .word :=
  .add (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (left right : Core.Word) :
    (inputs left right).check? source = some (core, .word) :=
  elaborateLocalExpression?_complete (resolved left right)
    (.binary (.var (.tail ids_ne .head)) (.var .head))
    ((resolved left right).preserves_type (typed left right))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.word (left.add right)) store 5 :=
  .add (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_have_independent_typing_evaluation_and_exact_core_steps
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .word ∧
    (inputs left right).check? source = some (core, .word) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store source (.word (left.add right)) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.word (left.add right)) store 5 ∧
    Core.Steps 5 (Core.State.initial core [.word right, .word left] store)
      (Core.State.final (.word (left.add right)) store) :=
  ⟨typed left right, checked left right, (costed left right store).erase, costed left right store,
    (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds⟩

theorem exact_completion_and_the_ordered_four_step_suspended_state
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 4 source store = some (.word, .outOfFuel
      ⟨.ret (.word right), [.binaryApply .wordAdd (.word left)], store⟩) ∧
    ∀ fuel, ((inputs left right).run? fuel source store =
      some (.word, .done (.word (left.add right)) store) ↔ 5 ≤ fuel) := by
  constructor
  · rw [LocalInputs.run?, checked]; rfl
  · intro fuel
    simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using
      (costed left right store).checked_runStateful_done_iff (fuel := fuel)
        (checked left right) (inputs left right).sameIds

theorem maximum_plus_one_wraps_but_does_not_fold_away_the_binary_core (store : Core.Store) :
    (inputs .maximum (Core.Word.ofNatModulo 1)).check? source = some (core, .word) ∧
    (inputs .maximum (Core.Word.ofNatModulo 1)).run? 5 source store =
      some (.word, .done (.word .zero) store) := by
  refine ⟨checked _ _, ?_⟩
  simpa only [Core.Word.add_maximum_one] using
    (exact_completion_and_the_ordered_four_step_suspended_state .maximum
      (Core.Word.ofNatModulo 1) store).2 5 |>.mpr (by decide)

theorem successful_addition_requires_both_ordered_word_children
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (add left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .word (leftWord.add rightWord) ∧ cost = leftCost + rightCost + 3 := by
  cases evaluation with
  | add leftEvaluation rightEvaluation => exact ⟨_, _, _, _, _, leftEvaluation, rightEvaluation, rfl, rfl⟩

theorem zero_does_not_bypass_an_unresolved_operand (store : Core.Store) :
    (inputs .zero .zero).check? (add (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (add (ref "missing") (ref "r")) = none ∧
    ∀ value finalStore, ¬ LocalExpressionEvaluates (inputs .zero .zero).names
      (inputs .zero .zero).environment store (add (ref "l") (ref "missing")) value finalStore := by
  have rightMissing : (inputs .zero .zero).check? (add (ref "l") (ref "missing")) = none := by
    simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, add, ref,
      inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  have leftMissing : (inputs .zero .zero).check? (add (ref "missing") (ref "r")) = none := by
    simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, add, ref,
      inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  refine ⟨rightMissing, leftMissing, ?_⟩
  intro value finalStore evaluation
  cases evaluation with
  | add _ rightEvaluation =>
      cases rightEvaluation with
      | identifier named _ =>
          have found := LocalNameTable.lookup?_iff.mpr named
          have absent : (inputs .zero .zero).names.lookup? "missing" = none := rfl
          rw [absent] at found
          cases found

theorem unused_inputs_and_injective_ids_preserve_addition_cost_and_observations
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) :
    ((inputs left right).mapIds mapping injective).run? fuel source store =
      (inputs left right).run? fuel source store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store source (.word (left.add right)) store 5 ∧
    (((inputs left right).bindFresh owner "unused" .unit .unit .unit).run? fuel source store =
      some (.word, .done (.word (left.add right)) store) ↔
      (inputs left right).run? fuel source store = some (.word, .done (.word (left.add right)) store)) := by
  have avoids : AvoidsLocalName "unused" source := .add (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel source store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed left right store),
    avoids.bindFresh_run_done_at_fuel_iff (inputs left right) owner .unit .unit .unit⟩

private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Word"⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ annotation⟩
private def types : TypeNameTable := [(["Word"], .word)]
private def declaration : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "sum"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some source)⟩]⟩⟩⟩
private def compiled : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word, core, .word⟩
private theorem compilation : RuntimeFunctionCompiles types owner declaration compiled :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil),
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.add (.identifier (.tail names_ne .head)) (.identifier .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))⟩
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (left right : Core.Word) :
    RuntimeFunctionPrepares types owner declaration (arguments left right) ⟨inputs left right, core, .word⟩ :=
  ⟨compilation.header,
    .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil), compilation.body⟩

theorem independent_value_free_function_compilation_reaches_exact_runtime_cost
    (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionCompiles types owner declaration compiled ∧
    compileRuntimeFunction? types owner declaration = some compiled ∧
    RuntimeFunctionEvaluatesWithCost types owner declaration (arguments left right)
      store .word (.word (left.add right)) store 5 ∧
    ∀ fuel, (runRuntimeFunction? types owner declaration (arguments left right) fuel store =
      some (.word, .done (.word (left.add right)) store) ↔ 5 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration (arguments left right)
      store .word (.word (left.add right)) store 5 :=
    .intro (preparation left right) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (costed left right store))
  exact ⟨compilation, compilation.complete, evaluation, fun _ => evaluation.run_done_iff⟩

end Tests.FrontendWordAddition
end

section
-- leanmerge: from Solcore.Test.FrontendWordArithmeticProperties
/-! Independent subtraction and multiplication preserve ordered Word operands,
modular results, exact Core frames, and the whole compiled entry contract. -/

set_option autoImplicit false

namespace Tests.FrontendWordArithmetic

open Solcore Solcore.Frontend

private inductive Kind where | subtractE | multiplyE
private def sourceOp : Kind → Syntax.BinaryOp | .subtractE => .subtract | .multiplyE => .multiply
private def coreOp : Kind → Core.BinaryOp | .subtractE => .wordSub | .multiplyE => .wordMul
private def result (kind : Kind) (left right : Core.Word) : Core.Word :=
  match kind with | .subtractE => left.sub right | .multiplyE => left.mul right
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Arithmetic", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "arithmetic.sol"⟩, 17, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def binary (kind : Kind) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .binary left ⟨span, sourceOp kind⟩ right⟩
private def source (kind : Kind) := binary kind (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core (kind : Kind) : Core.Expr := .binary (coreOp kind) (.var 1) (.var 0)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (kind : Kind) (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names (source kind)
      (.binary (coreOp kind) (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) := by
  cases kind
  · exact .subtract (.identifier (.tail names_ne .head)) (.identifier .head)
  · exact .multiply (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (kind : Kind) (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context (source kind) .word := by
  cases kind
  · exact .subtract (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
  · exact .multiply (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (kind : Kind) (left right : Core.Word) :
    (inputs left right).check? (source kind) = some (core kind, .word) :=
  elaborateLocalExpression?_complete (resolved kind left right)
    (.binary (.var (.tail ids_ne .head)) (.var .head))
    ((resolved kind left right).preserves_type (typed kind left right))
private theorem costed (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (source kind) (.word (result kind left right)) store 5 := by
  cases kind
  · exact .subtract (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
      (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
  · exact .multiply (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
      (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_have_independent_typing_evaluation_and_exact_core_steps
    (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    ResolvesLocalExpression (inputs left right).names (source kind)
      (.binary (coreOp kind) (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) ∧
    LocalExpressionHasType (inputs left right).names (inputs left right).context (source kind) .word ∧
    (inputs left right).check? (source kind) = some (core kind, .word) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store (source kind) (.word (result kind left right)) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (source kind) (.word (result kind left right)) store 5 ∧
    Core.Steps 5 (Core.State.initial (core kind) [.word right, .word left] store)
      (Core.State.final (.word (result kind left right)) store) :=
  ⟨resolved kind left right, typed kind left right, checked kind left right,
    (costed kind left right store).erase, costed kind left right store,
    (costed kind left right store).checked_toSteps (checked kind left right) (inputs left right).sameIds⟩

theorem exact_completion_and_ordered_four_step_state
    (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 4 (source kind) store = some (.word, .outOfFuel
      ⟨.ret (.word right), [.binaryApply (coreOp kind) (.word left)], store⟩) ∧
    ∀ fuel, ((inputs left right).run? fuel (source kind) store =
      some (.word, .done (.word (result kind left right)) store) ↔ 5 ≤ fuel) := by
  constructor
  · rw [LocalInputs.run?, checked]; cases kind <;> rfl
  · intro fuel
    simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using
      (costed kind left right store).checked_runStateful_done_iff (fuel := fuel)
        (checked kind left right) (inputs left right).sameIds

theorem subtraction_underflow_is_not_commutative (store : Core.Store) :
    (inputs .zero (Core.Word.ofNatModulo 1)).check? (source .subtractE) =
      some (core .subtractE, .word) ∧
    (inputs .zero (Core.Word.ofNatModulo 1)).run? 5 (source .subtractE) store =
      some (.word, .done (.word .maximum) store) ∧
    (inputs (Core.Word.ofNatModulo 1) .zero).run? 5 (source .subtractE) store =
      some (.word, .done (.word (Core.Word.ofNatModulo 1)) store) ∧
    (Core.Word.maximum : Core.Word) ≠ Core.Word.ofNatModulo 1 := by
  refine ⟨checked .subtractE _ _, ?_, ?_, by decide⟩
  · simpa only [result, Core.Word.zero_sub_one] using
      (exact_completion_and_ordered_four_step_state .subtractE .zero
        (Core.Word.ofNatModulo 1) store).2 5 |>.mpr (by decide)
  · simpa only [result, Core.Word.sub_zero] using
      (exact_completion_and_ordered_four_step_state .subtractE
        (Core.Word.ofNatModulo 1) .zero store).2 5 |>.mpr (by decide)

theorem maximum_times_two_wraps_without_folding (store : Core.Store) :
    (inputs .maximum (Core.Word.ofNatModulo 2)).check? (source .multiplyE) =
      some (core .multiplyE, .word) ∧
    (inputs .maximum (Core.Word.ofNatModulo 2)).run? 5 (source .multiplyE) store =
      some (.word, .done (.word (Core.Word.ofNatModulo (Core.wordModulus - 2))) store) := by
  refine ⟨checked .multiplyE _ _, ?_⟩
  simpa only [result, Core.Word.maximum_mul_two] using
    (exact_completion_and_ordered_four_step_state .multiplyE .maximum
      (Core.Word.ofNatModulo 2) store).2 5 |>.mpr (by decide)

theorem successful_arithmetic_requires_ordered_word_costs (kind : Kind)
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (binary kind left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .word (result kind leftWord rightWord) ∧ cost = leftCost + rightCost + 3 := by
  cases kind <;> cases evaluation <;> exact ⟨_, _, _, _, _, by assumption, by assumption, rfl, rfl⟩

private theorem missing_not_evaluates {initialStore finalStore : Core.Store} {value : Core.Value} :
    ¬ LocalExpressionEvaluates (inputs .zero .zero).names (inputs .zero .zero).environment
      initialStore (ref "missing") value finalStore := by
  intro evaluation
  cases evaluation with
  | identifier named _ =>
      have found := LocalNameTable.lookup?_iff.mpr named
      have absent : (inputs .zero .zero).names.lookup? "missing" = none := rfl
      rw [absent] at found
      cases found

theorem zero_multiplication_does_not_bypass_missing_operands (store : Core.Store) :
    (inputs .zero .zero).check? (binary .multiplyE (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (binary .multiplyE (ref "missing") (ref "r")) = none ∧
    ∀ value finalStore,
      (¬ LocalExpressionEvaluates (inputs .zero .zero).names (inputs .zero .zero).environment
        store (binary .multiplyE (ref "l") (ref "missing")) value finalStore) ∧
      (¬ LocalExpressionEvaluates (inputs .zero .zero).names (inputs .zero .zero).environment
        store (binary .multiplyE (ref "missing") (ref "r")) value finalStore) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, binary, sourceOp, ref,
      inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  · simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, binary, sourceOp, ref,
      inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  · intro value finalStore
    constructor
    · intro evaluation
      cases evaluation with | multiply _ right => exact missing_not_evaluates right
    · intro evaluation
      cases evaluation with | multiply left _ => exact missing_not_evaluates left

theorem unused_inputs_and_injective_ids_preserve_arithmetic
    (kind : Kind) (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) :
    ((inputs left right).mapIds mapping injective).run? fuel (source kind) store =
      (inputs left right).run? fuel (source kind) store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store (source kind) (.word (result kind left right)) store 5 ∧
    (((inputs left right).bindFresh owner "unused" .unit .unit .unit).run? fuel (source kind) store =
      some (.word, .done (.word (result kind left right)) store) ↔
      (inputs left right).run? fuel (source kind) store =
        some (.word, .done (.word (result kind left right)) store)) := by
  have avoids : AvoidsLocalName "unused" (source kind) := by
    cases kind
    · exact .subtract (.identifier (by decide)) (.identifier (by decide))
    · exact .multiply (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel (source kind) store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed kind left right store),
    avoids.bindFresh_run_done_at_fuel_iff (inputs left right) owner .unit .unit .unit⟩

private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Word"⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ annotation⟩
private def types : TypeNameTable := [(["Word"], .word)]
private def declaration (kind : Kind) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "arithmetic"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some (source kind))⟩]⟩⟩⟩
private def compiled (kind : Kind) : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word, core kind, .word⟩
private theorem compilation (kind : Kind) : RuntimeFunctionCompiles types owner (declaration kind) (compiled kind) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil), ?_⟩
  cases kind
  · exact TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.subtract (.identifier (.tail names_ne .head)) (.identifier .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
  · exact TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.multiply (.identifier (.tail names_ne .head)) (.identifier .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (kind : Kind) (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration kind) (arguments left right)
      ⟨inputs left right, core kind, .word⟩ :=
  ⟨(compilation kind).header,
    .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil), (compilation kind).body⟩

theorem independent_compilation_preparation_and_exact_entry_cost
    (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionCompiles types owner (declaration kind) (compiled kind) ∧
    compileRuntimeFunction? types owner (declaration kind) = some (compiled kind) ∧
    RuntimeFunctionPrepares types owner (declaration kind) (arguments left right)
      ⟨inputs left right, core kind, .word⟩ ∧
    RuntimeFunctionEvaluatesWithCost types owner (declaration kind) (arguments left right)
      store .word (.word (result kind left right)) store 5 ∧
    ∀ fuel, (runRuntimeFunction? types owner (declaration kind) (arguments left right) fuel store =
      some (.word, .done (.word (result kind left right)) store) ↔ 5 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner (declaration kind) (arguments left right)
      store .word (.word (result kind left right)) store 5 :=
    .intro (preparation kind left right) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (costed kind left right store))
  exact ⟨compilation kind, (compilation kind).complete, preparation kind left right,
    evaluation, fun _ => evaluation.run_done_iff⟩

end Tests.FrontendWordArithmetic
end

section
-- leanmerge: from Solcore.Test.FrontendWordDivisionProperties
/-! Ordered unsigned division and remainder use actual inputs, including zero
divisors. Independent source evidence reaches the complete terminal entry. -/

set_option autoImplicit false

namespace Tests.FrontendWordDivision

open Solcore Solcore.Frontend

private inductive Kind where | quotient | remainder
private def sourceOp : Kind → Syntax.BinaryOp | .quotient => .divide | .remainder => .modulo
private def coreOp : Kind → Core.BinaryOp | .quotient => .wordDiv | .remainder => .wordMod
private def result (kind : Kind) (left right : Core.Word) : Core.Word :=
  match kind with | .quotient => left.udiv right | .remainder => left.umod right
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Division", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "division.sol"⟩, 23, 4⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def binary (kind : Kind) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .binary left ⟨span, sourceOp kind⟩ right⟩
private def source (kind : Kind) := binary kind (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core (kind : Kind) : Core.Expr := .binary (coreOp kind) (.var 1) (.var 0)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (kind : Kind) (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names (source kind)
      (.binary (coreOp kind) (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) := by
  cases kind
  · exact .divide (.identifier (.tail names_ne .head)) (.identifier .head)
  · exact .modulo (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (kind : Kind) (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context (source kind) .word := by
  cases kind
  · exact .divide (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
  · exact .modulo (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (kind : Kind) (left right : Core.Word) :
    (inputs left right).check? (source kind) = some (core kind, .word) :=
  elaborateLocalExpression?_complete (resolved kind left right)
    (.binary (.var (.tail ids_ne .head)) (.var .head))
    ((resolved kind left right).preserves_type (typed kind left right))
private theorem costed (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (source kind) (.word (result kind left right)) store 5 := by
  cases kind
  · exact .divide (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
      (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
  · exact .modulo (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
      (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_have_independent_typing_raw_cost_and_outer_continuation_paths
    (kind : Kind) (left right : Core.Word) (store : Core.Store) (continuation : List Core.Frame) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context (source kind) .word ∧
    (inputs left right).check? (source kind) = some (core kind, .word) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store (source kind) (.word (result kind left right)) store ∧
    Core.Steps 5 ⟨.eval (core kind) [.word right, .word left], continuation, store⟩
      ⟨.ret (.word (result kind left right)), continuation, store⟩ := by
  refine ⟨typed kind left right, checked kind left right, ?_,
    (costed kind left right store).toStepsWithContinuation (resolved kind left right)
      (.binary (.var (.tail ids_ne .head)) (.var .head)) continuation⟩
  cases kind
  · exact .divide (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
  · exact .modulo (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem exact_five_step_threshold_includes_every_zero_case
    (kind : Kind) (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    ((inputs left right).run? fuel (source kind) store =
      some (.word, .done (.word (result kind left right)) store) ↔ 5 ≤ fuel) ∧
    ((∃ suspended, Core.runStateful fuel (Core.State.initial (core kind) [.word right, .word left] store) =
      .outOfFuel suspended) ↔ fuel < 5) := by
  refine ⟨?_, (costed kind left right store).checked_runStateful_outOfFuel_iff (checked kind left right)
    (inputs left right).sameIds⟩
  simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure, Option.some.injEq,
    Prod.mk.injEq, true_and] using (costed kind left right store).checked_runStateful_done_iff
      (fuel := fuel) (checked kind left right) (inputs left right).sameIds

private def pending (kind : Kind) (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word right), [.binaryApply (coreOp kind) (.word left)], store⟩
theorem original_left_then_right_checkpoints_resume_the_genuine_remaining_step
    (kind : Kind) (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    Core.runStateful 2 (Core.State.initial (core kind) [.word right, .word left] store) =
      .outOfFuel ⟨.ret (.word left), [.binaryRight (coreOp kind) (.var 0) [.word right, .word left]], store⟩ ∧
    (inputs left right).run? 4 (source kind) store = some (.word, .outOfFuel (pending kind left right store)) ∧
    Core.Steps 1 (pending kind left right store) (Core.State.final (.word (result kind left right)) store) ∧
    (inputs left right).run? (4 + additional) (source kind) store =
      some (.word, Core.runStateful additional (pending kind left right store)) := by
  have exhausted : Core.runStateful 4 (Core.State.initial (core kind) [.word right, .word left] store) =
      .outOfFuel (pending kind left right store) := by cases kind <;> rfl
  have publicExhausted := LocalInputs.run?_eq_some_iff.mpr ⟨core kind, checked kind left right, exhausted⟩
  exact ⟨by cases kind <;> rfl, publicExhausted,
    ((costed kind left right store).checked_residual_of_outOfFuel
      (checked kind left right) (inputs left right).sameIds exhausted).2,
    LocalInputs.run?_resume publicExhausted additional⟩

theorem zero_divisors_and_dividends_are_total_without_reducing_the_fuel
    (kind : Kind) (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    result kind left .zero = .zero ∧ result kind .zero right = .zero ∧
    ((inputs left .zero).run? fuel (source kind) store = some (.word, .done (.word .zero) store) ↔ 5 ≤ fuel) := by
  have zeroRight : result kind left .zero = .zero := by
    cases kind; exact Core.Word.udiv_zero left; exact Core.Word.umod_zero left
  refine ⟨zeroRight, ?_, ?_⟩
  · cases kind <;> simp only [result, Core.Word.udiv, Core.Word.umod] <;> split
    all_goals apply Fin.ext
    all_goals first | exact Nat.zero_div _ | exact Nat.zero_mod _ | rfl
  · simpa only [zeroRight] using (exact_five_step_threshold_includes_every_zero_case kind left .zero store fuel).1

theorem nonzero_operands_agree_with_the_existing_unsigned_core_interface
    (left right : Core.Word) (nonzero : right ≠ .zero) :
    result .quotient left right = left / right ∧ result .remainder left right = left % right :=
  ⟨Core.Word.udiv_nonzero left right nonzero, Core.Word.umod_nonzero left right nonzero⟩

theorem ordered_nonzero_high_bit_and_maximum_values_distinguish_quotient_from_remainder :
    result .quotient (Core.Word.ofNatModulo 7) (Core.Word.ofNatModulo 3) = Core.Word.ofNatModulo 2 ∧
    result .remainder (Core.Word.ofNatModulo 7) (Core.Word.ofNatModulo 3) = Core.Word.ofNatModulo 1 ∧
    result .quotient (Core.Word.ofNatModulo 3) (Core.Word.ofNatModulo 7) = .zero ∧
    result .remainder (Core.Word.ofNatModulo 3) (Core.Word.ofNatModulo 7) = Core.Word.ofNatModulo 3 ∧
    result .remainder (Core.Word.ofNatModulo 7) .zero ≠ Core.Word.ofNatModulo 7 % Core.Word.zero ∧
    result .quotient .maximum (Core.Word.ofNatModulo (2 ^ 255)) = Core.Word.ofNatModulo 1 ∧
    result .remainder .maximum (Core.Word.ofNatModulo (2 ^ 255)) = Core.Word.ofNatModulo (2 ^ 255 - 1) := by decide

theorem successful_cost_requires_both_original_ordered_word_children (kind : Kind)
    {table : LocalNameTable} {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {left right : Syntax.Expr} {value : Core.Value} {cost : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment initialStore (binary kind left right) value finalStore cost) :
    ∃ l r middle lc rc, LocalExpressionEvaluatesWithCost table environment initialStore left (.word l) middle lc ∧
      LocalExpressionEvaluatesWithCost table environment middle right (.word r) finalStore rc ∧
      value = .word (result kind l r) ∧ cost = lc + rc + 3 := by
  cases kind <;> cases evaluation <;> exact ⟨_, _, _, _, _, by assumption, by assumption, rfl, rfl⟩

private def typedInputs (l r : Core.Ty) (left right : Core.Value)
    (lt : Core.ValueHasType left l) (rt : Core.ValueHasType right r) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" l left lt).bindFresh owner "r" r right rt
theorem either_non_word_type_rejects_without_conversions (kind : Kind)
    (l r : Core.Ty) (left right : Core.Value) (lt : Core.ValueHasType left l) (rt : Core.ValueHasType right r)
    (wrong : l ≠ .word ∨ r ≠ .word) (fuel : Nat) (store : Core.Store) :
    (typedInputs l r left right lt rt).run? fuel (source kind) store = none := by
  apply (LocalInputs.run?_eq_none_iff fuel store).mpr
  cases accepted : (typedInputs l r left right lt rt).check? (source kind) with
  | none => rfl
  | some output =>
    rcases output with ⟨outputCore, outputType⟩
    have whole := LocalInputs.check?_iff_hasType.mp ⟨outputCore, accepted⟩
    have first : LocalExpressionHasType (typedInputs l r left right lt rt).names
        (typedInputs l r left right lt rt).context (ref "l") l := .identifier (.tail names_ne .head) (.tail ids_ne .head)
    have second : LocalExpressionHasType (typedInputs l r left right lt rt).names
        (typedInputs l r left right lt rt).context (ref "r") r := .identifier .head .head
    cases kind
    · cases whole with
      | divide a b => exact False.elim (wrong.elim
          (fun bad => bad (first.type_unique a)) (fun bad => bad (second.type_unique b)))
    · cases whole with
      | modulo a b => exact False.elim (wrong.elim
          (fun bad => bad (first.type_unique a)) (fun bad => bad (second.type_unique b)))

theorem zero_operands_do_not_resolve_a_missing_other_operand (kind : Kind) :
    (inputs .zero .zero).check? (binary kind (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (binary kind (ref "missing") (ref "r")) = none := by
  cases kind <;> constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?,
    binary, sourceOp, ref, inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
private def skipped (kind : Kind) : Syntax.Expr := ⟨span,
  .conditional ⟨span, .binary (ref "l") ⟨span, .equal⟩ (ref "l")⟩ span (ref "l") span
    (binary kind (ref "l") (ref "missing"))⟩
theorem raw_selected_path_does_not_license_an_invalid_written_divisor (kind : Kind) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs .zero .zero).names (inputs .zero .zero).environment
      store (skipped kind) (.word .zero) store 8 ∧ (inputs .zero .zero).check? (skipped kind) = none := by
  have leaf : LocalExpressionEvaluatesWithCost (inputs .zero .zero).names (inputs .zero .zero).environment
      store (ref "l") (.word .zero) store 1 := .identifier (.tail names_ne .head) (.tail ids_ne .head)
  refine ⟨.ifTrue (.equal leaf leaf) leaf, ?_⟩
  cases kind <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, skipped,
    binary, sourceOp, ref, inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

theorem spans_injective_ids_and_fresh_unused_inputs_preserve_the_arithmetic
    (kind : Kind) (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) (s o : Syntax.SourceSpan) :
    ((inputs left right).mapIds mapping injective).run? fuel (source kind) store =
      (inputs left right).run? fuel (source kind) store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store (source kind) (.word (result kind left right)) store 5 ∧
    resolveLocalExpression? (inputs left right).names (source kind) =
      resolveLocalExpression? (inputs left right).names ⟨s, .binary (ref "l") ⟨o, sourceOp kind⟩ (ref "r")⟩ := by
  have avoids : AvoidsLocalName "unused" (source kind) := by
    cases kind
    · exact .divide (.identifier (by decide)) (.identifier (by decide))
    · exact .modulo (.identifier (by decide)) (.identifier (by decide))
  refine ⟨(inputs left right).run?_mapIds mapping injective fuel (source kind) store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed kind left right store), ?_⟩
  cases kind
  · exact resolveLocalExpression?_divide_spans _ _ _ _ _ _ _
  · exact resolveLocalExpression?_modulo_spans _ _ _ _ _ _ _

theorem arbitrary_identity_maps_store_replay_and_value_erasure_keep_the_contract
    (kind : Kind) (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (first replacement : Core.Store) :
    ResolvesLocalExpression (LocalNameTable.mapIds mapping (inputs left right).names) (source kind)
      (.binary (coreOp kind) (.var (mapping ⟨owner, 0⟩)) (.var (mapping ⟨owner, 1⟩))) ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      replacement (source kind) (.word (result kind left right)) replacement 5 ∧
    5 ≤ localExpressionFuelBound (source kind) ∧ localExpressionFuelBound (source kind) = 5 ∧
    (inputs left right).toTypeInputs.context = (inputs left right).context := by
  exact ⟨(resolved kind left right).mapIds mapping, (costed kind left right first).change_store replacement,
    (costed kind left right first).cost_le_fuelBound,
    by cases kind <;> simp [localExpressionFuelBound, source, binary, sourceOp, ref], (inputs left right).toTypeInputs_context⟩

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (annotation "Word")⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def returned (value : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some value)⟩]⟩
private def entryBody (kind : Kind) : Syntax.Block := ⟨span, [⟨span,
  .ifThen ⟨span, .binary (ref "l") ⟨span, .equal⟩ (ref "r")⟩
    (returned (source kind)) (some (returned (ref "l")))⟩]⟩
private def declaration (kind : Kind) (name : String := "Word") : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "division"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation name]⟩⟩, none⟩, entryBody kind⟩⟩
private def compiled (kind : Kind) : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word,
    .ifE (.binary .wordEq (.var 1) (.var 0)) (core kind) (.var 1), .word⟩
private theorem compilation (kind : Kind) : RuntimeFunctionCompiles types owner (declaration kind) (compiled kind) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil), TypedLetReturnBodyElaborates.returnTree <| .terminal <| .conditional
    (.equal (.identifier (.tail names_ne .head)) (.identifier .head))
    (.binary (.var (.tail ids_ne .head)) (.var .head)) (.binary (.var (.tail ids_ne .head)) (.var .head))
    (.single (.expression (resolved kind .zero .zero) (.binary (.var (.tail ids_ne .head)) (.var .head))
      ((resolved kind .zero .zero).preserves_type (typed kind .zero .zero))))
    (.single (.expression (.identifier (.tail names_ne .head)) (.var (.tail ids_ne .head)) (.var (.tail ids_ne .head))))⟩
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (kind : Kind) (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration kind) (arguments left right) ⟨inputs left right, (compiled kind).core, .word⟩ :=
  ⟨(compilation kind).header, .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil), (compilation kind).body⟩

theorem terminal_compilation_uses_actual_arguments_and_selected_exact_cost
    (kind : Kind) (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    RuntimeFunctionCompiles types owner (declaration kind) (compiled kind) ∧
    RuntimeFunctionPrepares types owner (declaration kind) (arguments left right) ⟨inputs left right, (compiled kind).core, .word⟩ ∧
    RuntimeFunctionEvaluatesWithCost types owner (declaration kind) (arguments left right) store .word
      (.word (if left == right then result kind left right else left)) store (if left == right then 12 else 8) ∧
    runRuntimeFunction? types owner (declaration kind) (arguments left right) fuel store = some (.word,
      Core.runStateful fuel (Core.State.initial (compiled kind).core [.word right, .word left] store)) := by
  refine ⟨compilation kind, preparation kind left right, ?_, (compilation kind).run_eq _ rfl fuel store⟩
  apply RuntimeFunctionEvaluatesWithCost.intro (preparation kind left right)
  apply TypedLetReturnBodyEvaluatesWithCost.returnTree
  apply TypedLetReturnBodyEvaluatesWithCost.terminal
  have l : LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (ref "l") (.word left) store 1 := .identifier (.tail names_ne .head) (.tail ids_ne .head)
  have r : LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (ref "r") (.word right) store 1 := .identifier .head .head
  have comparison := LocalExpressionEvaluatesWithCost.equal (span := span) (operatorSpan := span) l r
  cases choice : (left == right)
  · exact .ifFalse (by simpa only [choice] using comparison) (.single (.expression l))
  · exact .ifTrue (by simpa only [choice] using comparison) (.single (.expression (costed kind left right store)))

theorem terminal_selected_threshold_bound_and_actual_compiled_path
    (kind : Kind) (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    (runRuntimeFunction? types owner (declaration kind) (arguments left right) fuel store =
      some (.word, .done (.word (if left == right then result kind left right else left)) store) ↔
      (if left == right then 12 else 8) ≤ fuel) ∧
    Core.Steps (if left == right then 12 else 8)
      (Core.State.initial (compiled kind).core ((arguments left right).reverse.map (·.value)) store)
      (Core.State.final (.word (if left == right then result kind left right else left)) store) ∧
    (if left == right then 12 else 8) ≤ typedLetReturnTreeFuelBound (declaration kind).value.body := by
  have evaluation := (terminal_compilation_uses_actual_arguments_and_selected_exact_cost kind left right store fuel).2.2.1
  exact ⟨evaluation.run_done_iff, evaluation.compiled_toSteps (compilation kind), evaluation.cost_le_fuelBound⟩

theorem a_boolean_declared_return_cannot_replace_the_word_result (kind : Kind) :
    compileRuntimeFunction? types owner (declaration kind "Bool") = none := by
  apply compileRuntimeFunction?_eq_none_iff.mpr
  rintro ⟨candidate, accepted⟩
  have sameInputs := accepted.parameters.result_unique (compilation kind).parameters
  have body := accepted.body
  rw [sameInputs] at body
  have sameType := ((compilation kind).body.result_unique body).2
  have header : RuntimeFunctionHeader types (declaration kind "Bool").value.signature .bool :=
    ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩
  cases sameType.trans (accepted.header.type_unique header)

end Tests.FrontendWordDivision
end

section
-- leanmerge: from Solcore.Test.FrontendWordEqualityProperties
/-! Independent Word-only equality returns Bool while preserving strict operand
order, exact transition counts, and the complete checked entry contract. -/

set_option autoImplicit false

namespace Tests.FrontendWordEquality

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Equality", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "equality.sol"⟩, 19, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def equal (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .equal⟩ right⟩
private def source := equal (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := .binary .wordEq (.var 1) (.var 0)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.binary .wordEq (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) :=
  .equal (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool :=
  .equal (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (left right : Core.Word) :
    (inputs left right).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete (resolved left right)
    (.binary (.var (.tail ids_ne .head)) (.var .head))
    ((resolved left right).preserves_type (typed left right))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (left == right)) store 5 :=
  .equal (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_produce_independent_bool_typing_evaluation_and_exact_steps
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool ∧
    (inputs left right).check? source = some (core, .bool) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store source (.bool (left == right)) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (left == right)) store 5 ∧
    Core.Steps 5 (Core.State.initial core [.word right, .word left] store)
      (Core.State.final (.bool (left == right)) store) :=
  ⟨typed left right, checked left right,
    .equal (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head),
    costed left right store, (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds⟩

theorem exact_fuel_four_checkpoint_preserves_left_and_right_operand_order
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 4 source store = some (.bool, .outOfFuel
      ⟨.ret (.word right), [.binaryApply .wordEq (.word left)], store⟩) ∧
    ∀ fuel, ((inputs left right).run? fuel source store =
      some (.bool, .done (.bool (left == right)) store) ↔ 5 ≤ fuel) := by
  constructor
  · rw [LocalInputs.run?, checked]; rfl
  · intro fuel
    simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using
      (costed left right store).checked_runStateful_done_iff (fuel := fuel)
        (checked left right) (inputs left right).sameIds

theorem equality_and_inequality_still_need_five_steps_and_return_no_word_flag
    (left right : Core.Word) (different : left ≠ right) (fuel : Nat) (store : Core.Store) :
    ((inputs left left).run? fuel source store = some (.bool, .done (.bool true) store) ↔ 5 ≤ fuel) ∧
    ((inputs left right).run? fuel source store = some (.bool, .done (.bool false) store) ↔ 5 ≤ fuel) ∧
    ∀ word, Core.Value.bool (left == right) ≠ .word word := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using (exact_fuel_four_checkpoint_preserves_left_and_right_operand_order left left store).2 fuel
  · have unequal : (left == right) = false := beq_eq_false_iff_ne.mpr different
    simpa only [unequal] using (exact_fuel_four_checkpoint_preserves_left_and_right_operand_order left right store).2 fuel
  · intro word same; cases same

theorem zero_high_bit_and_maximum_keep_exact_word_equality (store : Core.Store) :
    (inputs .zero .zero).run? 5 source store = some (.bool, .done (.bool true) store) ∧
    (inputs .maximum .maximum).run? 5 source store = some (.bool, .done (.bool true) store) ∧
    (inputs (Core.Word.ofNatModulo (2 ^ 255)) .zero).run? 5 source store =
      some (.bool, .done (.bool false) store) ∧
    (inputs .zero .maximum).run? 5 source store = some (.bool, .done (.bool false) store) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (exact_fuel_four_checkpoint_preserves_left_and_right_operand_order .zero .zero store).2 5 |>.mpr (by decide)
  · simpa using (exact_fuel_four_checkpoint_preserves_left_and_right_operand_order .maximum .maximum store).2 5 |>.mpr (by decide)
  · have unequal : (Core.Word.ofNatModulo (2 ^ 255) == Core.Word.zero) = false := by decide
    exact ((exact_fuel_four_checkpoint_preserves_left_and_right_operand_order
      (Core.Word.ofNatModulo (2 ^ 255)) .zero store).2 5 |>.mpr (by decide)).trans
        (congrArg (fun result => some (Core.Ty.bool, Core.StatefulRunResult.done (.bool result) store)) unequal)
  · have unequal : (Core.Word.zero == Core.Word.maximum) = false := by decide
    exact ((exact_fuel_four_checkpoint_preserves_left_and_right_operand_order .zero .maximum store).2 5 |>.mpr (by decide)).trans
      (congrArg (fun result => some (Core.Ty.bool, Core.StatefulRunResult.done (.bool result) store)) unequal)

theorem independent_equality_requires_both_ordered_word_operands
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (equal left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .bool (leftWord == rightWord) ∧ cost = leftCost + rightCost + 3 := by
  cases evaluation with
  | equal leftEvaluation rightEvaluation => exact ⟨_, _, _, _, _, leftEvaluation, rightEvaluation, rfl, rfl⟩

theorem missing_either_operand_is_not_bypassed_by_equal_known_values :
    (inputs .zero .zero).check? (equal (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (equal (ref "missing") (ref "r")) = none := by
  constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, equal, ref,
    inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

private def typedInputs (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" leftType left leftTyped).bindFresh owner "r" rightType right rightTyped

theorem non_word_on_either_side_is_rejected_without_polymorphic_equality
    (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType)
    (wrong : leftType ≠ .word ∨ rightType ≠ .word) (fuel : Nat) (store : Core.Store) :
    (typedInputs leftType rightType left right leftTyped rightTyped).check? source = none ∧
    (typedInputs leftType rightType left right leftTyped rightTyped).run? fuel source store = none := by
  have rejected : (typedInputs leftType rightType left right leftTyped rightTyped).check? source = none := by
    cases accepted : (typedInputs leftType rightType left right leftTyped rightTyped).check? source with
    | none => rfl
    | some result =>
      rcases result with ⟨compiledCore, resultType⟩
      have whole := LocalInputs.check?_iff_hasType.mp ⟨compiledCore, accepted⟩
      cases whole with
      | equal first second =>
        have firstTyped : LocalExpressionHasType
            (typedInputs leftType rightType left right leftTyped rightTyped).names
            (typedInputs leftType rightType left right leftTyped rightTyped).context (ref "l") leftType :=
          .identifier (.tail names_ne .head) (.tail ids_ne .head)
        have secondTyped : LocalExpressionHasType
            (typedInputs leftType rightType left right leftTyped rightTyped).names
            (typedInputs leftType rightType left right leftTyped rightTyped).context (ref "r") rightType :=
          .identifier .head .head
        exact False.elim (wrong.elim (fun mismatch => mismatch (firstTyped.type_unique first))
          (fun mismatch => mismatch (secondTyped.type_unique second)))
  exact ⟨rejected, (LocalInputs.run?_eq_none_iff fuel store).mpr rejected⟩

theorem symmetric_final_equality_does_not_permit_swapping_pending_operands
    (left right : Core.Word) (different : left ≠ right) (store : Core.Store) :
    Core.runStateful 5 (Core.State.initial core [.word right, .word left] store) =
      Core.runStateful 5 (Core.State.initial (.binary .wordEq (.var 0) (.var 1)) [.word right, .word left] store) ∧
    Core.runStateful 4 (Core.State.initial core [.word right, .word left] store) ≠
      Core.runStateful 4 (Core.State.initial (.binary .wordEq (.var 0) (.var 1)) [.word right, .word left] store) := by
  constructor
  · change Core.StatefulRunResult.done (.bool (left == right)) store = .done (.bool (right == left)) store
    rw [beq_eq_false_iff_ne.mpr different, beq_eq_false_iff_ne.mpr (Ne.symm different)]
  · intro same
    have controls := congrArg Core.State.control (Core.StatefulRunResult.outOfFuel.inj same)
    exact different (Core.Value.word.inj (Core.Control.ret.inj controls)).symm

theorem equality_preserves_unrelated_inputs_and_ignores_only_spans_and_injective_ids
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store)
    (otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    ((inputs left right).mapIds mapping injective).run? fuel source store =
      (inputs left right).run? fuel source store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store source (.bool (left == right)) store 5 ∧
    resolveLocalExpression? (inputs left right).names source = resolveLocalExpression? (inputs left right).names
      ⟨otherSpan, .binary (ref "l") ⟨otherOperatorSpan, .equal⟩ (ref "r")⟩ := by
  have avoids : AvoidsLocalName "unused" source := .equal (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel source store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed left right store),
    resolveLocalExpression?_equal_spans _ _ _ _ _ _ _⟩

theorem replay_structural_budget_and_checkpoint_residual_keep_boolean_equality
    (left right : Core.Word) (first replacement : Core.Store) (additional : Nat) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      replacement source (.bool (left == right)) replacement 5 ∧
    5 ≤ localExpressionFuelBound source ∧ localExpressionFuelBound source = 5 ∧
    Core.Steps 1 ⟨.ret (.word right), [.binaryApply .wordEq (.word left)], replacement⟩
      (Core.State.final (.bool (left == right)) replacement) ∧
    (inputs left right).run? (4 + additional) source replacement = some (.bool,
      Core.runStateful additional ⟨.ret (.word right), [.binaryApply .wordEq (.word left)], replacement⟩) := by
  have replayed := (costed left right first).change_store replacement
  have exhausted := (exact_fuel_four_checkpoint_preserves_left_and_right_operand_order left right replacement).1
  have coreExhausted : Core.runStateful 4 (Core.State.initial core [.word right, .word left] replacement) =
      .outOfFuel ⟨.ret (.word right), [.binaryApply .wordEq (.word left)], replacement⟩ := rfl
  refine ⟨replayed, replayed.cost_le_fuelBound, ?_,
    (replayed.checked_residual_of_outOfFuel (checked left right) (inputs left right).sameIds coreExhausted).2,
    LocalInputs.run?_resume exhausted additional⟩
  simp [source, equal, ref, localExpressionFuelBound]

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation "Word")⟩
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def declaration (returnName : String) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "equal"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation returnName]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some source)⟩]⟩⟩⟩
private def compiled : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word, core, .bool⟩
private theorem wordAnnotation : TypeNameDenotes types (annotation "Word") .word :=
  .named (.tail (by decide) .head)
private theorem compilation : RuntimeFunctionCompiles types owner (declaration "Bool") compiled :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons wordAnnotation.structural (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons wordAnnotation.structural (by change "r" ∉ ["l"]; simp) .nil),
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.equal (.identifier (.tail names_ne .head)) (.identifier .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))⟩
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ :=
  ⟨compilation.header,
    .cons wordAnnotation.structural (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons wordAnnotation.structural (by change "r" ∉ ["l"]; simp) .nil), compilation.body⟩

theorem independent_compilation_preparation_and_exact_bool_entry_cost
    (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionCompiles types owner (declaration "Bool") compiled ∧
    compileRuntimeFunction? types owner (declaration "Bool") = some compiled ∧
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ ∧
    RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (left == right)) store 5 ∧
    ∀ fuel, (runRuntimeFunction? types owner (declaration "Bool") (arguments left right) fuel store =
      some (.bool, .done (.bool (left == right)) store) ↔ 5 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (left == right)) store 5 :=
    .intro (preparation left right) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (costed left right store))
  exact ⟨compilation, compilation.complete, preparation left right, evaluation, fun _ => evaluation.run_done_iff⟩

theorem declared_word_return_rejects_a_bool_equality_result :
    compileRuntimeFunction? types owner (declaration "Word") = none := by
  apply compileRuntimeFunction?_eq_none_iff.mpr
  intro ⟨candidate, accepted⟩
  have sameInputs : candidate.inputs = compiled.inputs := accepted.parameters.result_unique compilation.parameters
  have expectedHeader : RuntimeFunctionHeader types (declaration "Word").value.signature .word :=
    ⟨rfl, rfl, rfl, rfl, .single wordAnnotation.structural⟩
  have sameReturn : candidate.returnType = .word := accepted.header.type_unique expectedHeader
  have candidateBody := accepted.body
  rw [sameInputs] at candidateBody
  have bodyReturn : candidate.returnType = .bool := (candidateBody.result_unique compilation.body).2
  cases sameReturn.symm.trans bodyReturn

end Tests.FrontendWordEquality
end

section
-- leanmerge: from Solcore.Test.FrontendWordGreaterEqualProperties
/-! Independent unsigned Word ordering returns Bool while preserving strict operand
order, exact transition counts, and the complete checked entry contract. -/

set_option autoImplicit false

namespace Tests.FrontendWordGreaterEqual

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"GreaterEqual", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "greaterEqual.sol"⟩, 19, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def greaterEqual (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .greaterEqual⟩ right⟩
private def source := greaterEqual (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := .unary .boolNot ((Core.Expr.var 1).wordLt (.var 0))
private theorem coreShape :
    core = .unary .boolNot (.letE (.var 1) (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1)))) := by
  simp [core, Core.Expr.wordLt_expansion, Core.Expr.weakenAt]
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.unary .boolNot (.wordLt (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩))) :=
  .greaterEqual (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool :=
  .greaterEqual (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (left right : Core.Word) :
    (inputs left right).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete (resolved left right)
    (.unary (.wordLt (.var (.tail ids_ne .head)) (.var .head)))
    ((resolved left right).preserves_type (typed left right))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (!(decide (left < right)))) store 13 :=
  .greaterEqual (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_produce_independent_bool_typing_evaluation_and_exact_steps
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool ∧
    (inputs left right).check? source = some (core, .bool) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store source (.bool (!(decide (left < right)))) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (!(decide (left < right)))) store 13 ∧
    Core.Steps 13 (Core.State.initial core [.word right, .word left] store)
      (Core.State.final (.bool (!(decide (left < right)))) store) :=
  ⟨typed left right, checked left right,
    .greaterEqual (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head),
    costed left right store, (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds⟩

private def firstBinding (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.letBody (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1)))
    [.word right, .word left], .unaryApply .boolNot], store⟩
private def secondBinding (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word right), [.letBody (.binary .wordGt (.var 0) (.var 1))
    [.word left, .word right, .word left], .unaryApply .boolNot], store⟩
private def pending (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.binaryApply .wordGt (.word right), .unaryApply .boolNot], store⟩
private def pendingNot (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool (decide (left < right))), [.unaryApply .boolNot], store⟩

theorem exact_resolved_and_core_shapes_negate_the_ordered_identity_free_comparison
    (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.unary .boolNot (.wordLt (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩))) ∧
    core = .unary .boolNot (.letE (.var 1) (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1)))) :=
  ⟨resolved left right, coreShape⟩

theorem genuine_checkpoints_retain_ordered_bindings_comparison_and_final_negation
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 3 source store = some (.bool, .outOfFuel (firstBinding left right store)) ∧
    (inputs left right).run? 6 source store = some (.bool, .outOfFuel (secondBinding left right store)) ∧
    (inputs left right).run? 11 source store = some (.bool, .outOfFuel (pending left right store)) ∧
    (inputs left right).run? 12 source store = some (.bool, .outOfFuel (pendingNot left right store)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [LocalInputs.run?, checked, coreShape] <;> rfl

theorem all_fuel_thresholds_count_thirteen_steps_for_every_actual_word_pair
    (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    ((inputs left right).run? fuel source store =
      some (.bool, .done (.bool (!(decide (left < right)))) store) ↔ 13 ≤ fuel) ∧
    ((∃ checkpoint, (inputs left right).run? fuel source store =
      some (.bool, .outOfFuel checkpoint)) ↔ fuel < 13) := by
  have path := (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds
  constructor
  · simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using path.runStateful_done_iff (fuel := fuel)
  · simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using path.runStateful_outOfFuel_iff (fuel := fuel)

theorem equal_strict_and_reverse_orders_never_return_word_flags
    (left right : Core.Word) (strict : left < right) (fuel : Nat) (store : Core.Store) :
    ((inputs left left).run? fuel source store = some (.bool, .done (.bool true) store) ↔ 13 ≤ fuel) ∧
    ((inputs left right).run? fuel source store = some (.bool, .done (.bool false) store) ↔ 13 ≤ fuel) ∧
    ((inputs right left).run? fuel source store = some (.bool, .done (.bool true) store) ↔ 13 ≤ fuel) ∧
    ∀ word, Core.Value.bool (!(decide (left < right))) ≠ .word word := by
  have reversed : ¬right < left := Nat.not_lt.mpr (Nat.le_of_lt strict)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (all_fuel_thresholds_count_thirteen_steps_for_every_actual_word_pair left left store fuel).1
  · simpa [strict] using (all_fuel_thresholds_count_thirteen_steps_for_every_actual_word_pair left right store fuel).1
  · simpa [reversed] using (all_fuel_thresholds_count_thirteen_steps_for_every_actual_word_pair right left store fuel).1
  · intro word same; cases same

theorem zero_high_bit_and_maximum_distinguish_unsigned_order (store : Core.Store) :
    (inputs .zero (Core.Word.ofNatModulo (2 ^ 255))).run? 13 source store = some (.bool, .done (.bool false) store) ∧
    (inputs (Core.Word.ofNatModulo (2 ^ 255)) .zero).run? 13 source store = some (.bool, .done (.bool true) store) ∧
    (inputs (Core.Word.ofNatModulo (2 ^ 255)) .maximum).run? 13 source store = some (.bool, .done (.bool false) store) ∧
    (inputs .maximum (Core.Word.ofNatModulo (2 ^ 255))).run? 13 source store = some (.bool, .done (.bool true) store) ∧
    (inputs .maximum .maximum).run? 13 source store = some (.bool, .done (.bool true) store) := by
  have first := equal_strict_and_reverse_orders_never_return_word_flags
    .zero (Core.Word.ofNatModulo (2 ^ 255)) (by decide) 13 store
  have second := equal_strict_and_reverse_orders_never_return_word_flags
    (Core.Word.ofNatModulo (2 ^ 255)) .maximum (by decide) 13 store
  exact ⟨first.2.1.mpr (by decide), first.2.2.1.mpr (by decide),
    second.2.1.mpr (by decide), second.2.2.1.mpr (by decide),
    by simpa using (all_fuel_thresholds_count_thirteen_steps_for_every_actual_word_pair .maximum .maximum store 13).1.mpr (by decide)⟩

theorem genuine_checkpoints_have_exact_residuals_and_final_negation_resumption
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    Core.Steps 10 (firstBinding left right store) (Core.State.final (.bool (!(decide (left < right)))) store) ∧
    Core.Steps 7 (secondBinding left right store) (Core.State.final (.bool (!(decide (left < right)))) store) ∧
    Core.Steps 2 (pending left right store) (Core.State.final (.bool (!(decide (left < right)))) store) ∧
    Core.Steps 1 (pendingNot left right store) (Core.State.final (.bool (!(decide (left < right)))) store) ∧
    Core.runStateful 1 (pending left right store) = .outOfFuel (pendingNot left right store) ∧
    (inputs left right).run? (6 + additional) source store =
      some (.bool, Core.runStateful additional (secondBinding left right store)) ∧
    (inputs left right).run? (12 + additional) source store =
      some (.bool, Core.runStateful additional (pendingNot left right store)) := by
  have first : Core.runStateful 3 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (firstBinding left right store) := by rw [coreShape]; rfl
  have second : Core.runStateful 6 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (secondBinding left right store) := by rw [coreShape]; rfl
  have compared : Core.runStateful 11 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (pending left right store) := by rw [coreShape]; rfl
  have last : Core.runStateful 12 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (pendingNot left right store) := by rw [coreShape]; rfl
  have path := (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds
  have residual := (costed left right store).checked_residual_of_outOfFuel
    (checked left right) (inputs left right).sameIds last
  have checkpoints := genuine_checkpoints_retain_ordered_bindings_comparison_and_final_negation left right store
  exact ⟨(path.residual_of_outOfFuel first).2, (path.residual_of_outOfFuel second).2,
    (path.residual_of_outOfFuel compared).2, residual.2, rfl,
    LocalInputs.run?_resume checkpoints.2.1 additional, LocalInputs.run?_resume checkpoints.2.2.2 additional⟩

theorem independent_greater_equal_requires_both_ordered_word_operands
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (greaterEqual left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .bool (!(decide (leftWord < rightWord))) ∧ cost = leftCost + rightCost + 11 := by
  cases evaluation with
  | greaterEqual leftEvaluation rightEvaluation => exact ⟨_, _, _, _, _, leftEvaluation, rightEvaluation, rfl, rfl⟩

theorem missing_either_operand_is_not_bypassed_by_equal_known_values :
    (inputs .zero .zero).check? (greaterEqual (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (greaterEqual (ref "missing") (ref "r")) = none := by
  constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, greaterEqual, ref,
    inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

private def typedInputs (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" leftType left leftTyped).bindFresh owner "r" rightType right rightTyped

theorem non_word_on_either_side_is_rejected_without_polymorphic_greater_equal
    (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType)
    (wrong : leftType ≠ .word ∨ rightType ≠ .word) (fuel : Nat) (store : Core.Store) :
    (typedInputs leftType rightType left right leftTyped rightTyped).check? source = none ∧
    (typedInputs leftType rightType left right leftTyped rightTyped).run? fuel source store = none := by
  have rejected : (typedInputs leftType rightType left right leftTyped rightTyped).check? source = none := by
    cases accepted : (typedInputs leftType rightType left right leftTyped rightTyped).check? source with
    | none => rfl
    | some result =>
      rcases result with ⟨compiledCore, resultType⟩
      have whole := LocalInputs.check?_iff_hasType.mp ⟨compiledCore, accepted⟩
      cases whole with
      | greaterEqual first second =>
        have firstTyped : LocalExpressionHasType
            (typedInputs leftType rightType left right leftTyped rightTyped).names
            (typedInputs leftType rightType left right leftTyped rightTyped).context (ref "l") leftType :=
          .identifier (.tail names_ne .head) (.tail ids_ne .head)
        have secondTyped : LocalExpressionHasType
            (typedInputs leftType rightType left right leftTyped rightTyped).names
            (typedInputs leftType rightType left right leftTyped rightTyped).context (ref "r") rightType :=
          .identifier .head .head
        exact False.elim (wrong.elim (fun mismatch => mismatch (firstTyped.type_unique first))
          (fun mismatch => mismatch (secondTyped.type_unique second)))
  exact ⟨rejected, (LocalInputs.run?_eq_none_iff fuel store).mpr rejected⟩

theorem greater_equal_preserves_unrelated_inputs_and_ignores_only_spans_and_injective_ids
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store)
    (otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    ((inputs left right).mapIds mapping injective).run? fuel source store =
      (inputs left right).run? fuel source store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store source (.bool (!(decide (left < right)))) store 13 ∧
    resolveLocalExpression? (inputs left right).names source = resolveLocalExpression? (inputs left right).names
      ⟨otherSpan, .binary (ref "l") ⟨otherOperatorSpan, .greaterEqual⟩ (ref "r")⟩ := by
  have avoids : AvoidsLocalName "unused" source := .greaterEqual (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel source store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed left right store),
    resolveLocalExpression?_greaterEqual_spans _ _ _ _ _ _ _⟩

theorem arbitrary_identity_maps_preserve_structural_resolution_without_fresh_names
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId) :
    ResolvesLocalExpression (LocalNameTable.mapIds mapping (inputs left right).names) source
      (.unary .boolNot (.wordLt (.var (mapping ⟨owner, 0⟩)) (.var (mapping ⟨owner, 1⟩)))) := by
  simpa only [Resolved.Expr.renameIds] using (resolved left right).mapIds mapping

theorem replay_structural_budget_and_type_erasure_preserve_the_source_contract
    (left right : Core.Word) (first replacement : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      replacement source (.bool (!(decide (left < right)))) replacement 13 ∧
    13 ≤ localExpressionFuelBound source ∧ localExpressionFuelBound source = 13 ∧
    (inputs left right).toTypeInputs.names = (inputs left right).names ∧
    (inputs left right).toTypeInputs.context = (inputs left right).context := by
  have replayed := (costed left right first).change_store replacement
  exact ⟨replayed, replayed.cost_le_fuelBound, by simp [source, greaterEqual, ref, localExpressionFuelBound],
    (inputs left right).toTypeInputs_names, (inputs left right).toTypeInputs_context⟩

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation "Word")⟩
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def declaration (returnName : String) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "greaterEqual"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation returnName]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some source)⟩]⟩⟩⟩
private def compiled : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word, core, .bool⟩
private theorem wordAnnotation : TypeNameDenotes types (annotation "Word") .word :=
  .named (.tail (by decide) .head)
private theorem compilation : RuntimeFunctionCompiles types owner (declaration "Bool") compiled :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons wordAnnotation.structural (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons wordAnnotation.structural (by change "r" ∉ ["l"]; simp) .nil),
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.greaterEqual (.identifier (.tail names_ne .head)) (.identifier .head))
      (.unary (.wordLt (.var (.tail ids_ne .head)) (.var .head)))
      (.unary (.wordLt (.var (.tail ids_ne .head)) (.var .head)))⟩
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ :=
  ⟨compilation.header,
    .cons wordAnnotation.structural (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons wordAnnotation.structural (by change "r" ∉ ["l"]; simp) .nil), compilation.body⟩

theorem independent_compilation_preparation_and_exact_bool_entry_cost
    (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionCompiles types owner (declaration "Bool") compiled ∧
    compileRuntimeFunction? types owner (declaration "Bool") = some compiled ∧
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ ∧
    RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (!(decide (left < right)))) store 13 ∧
    ∀ fuel, (runRuntimeFunction? types owner (declaration "Bool") (arguments left right) fuel store =
      some (.bool, .done (.bool (!(decide (left < right)))) store) ↔ 13 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (!(decide (left < right)))) store 13 :=
    .intro (preparation left right) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (costed left right store))
  exact ⟨compilation, compilation.complete, preparation left right, evaluation, fun _ => evaluation.run_done_iff⟩

theorem declared_word_return_rejects_a_bool_greater_equal_result :
    compileRuntimeFunction? types owner (declaration "Word") = none := by
  apply compileRuntimeFunction?_eq_none_iff.mpr
  intro ⟨candidate, accepted⟩
  have sameInputs : candidate.inputs = compiled.inputs := accepted.parameters.result_unique compilation.parameters
  have expectedHeader : RuntimeFunctionHeader types (declaration "Word").value.signature .word :=
    ⟨rfl, rfl, rfl, rfl, .single wordAnnotation.structural⟩
  have sameReturn : candidate.returnType = .word := accepted.header.type_unique expectedHeader
  have candidateBody := accepted.body
  rw [sameInputs] at candidateBody
  have bodyReturn : candidate.returnType = .bool := (candidateBody.result_unique compilation.body).2
  cases sameReturn.symm.trans bodyReturn

end Tests.FrontendWordGreaterEqual
end

section
-- leanmerge: from Solcore.Test.FrontendWordGreaterProperties
/-! Independent unsigned comparison changes the result type, not operand order,
strict checking, exact machine frames, or the whole entry contract. -/

set_option autoImplicit false

namespace Tests.FrontendWordGreater

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Greater", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "greater.sol"⟩, 17, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def greater (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .greater⟩ right⟩
private def source := greater (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := .binary .wordGt (.var 1) (.var 0)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.binary .wordGt (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) :=
  .greater (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool :=
  .greater (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (left right : Core.Word) :
    (inputs left right).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete (resolved left right)
    (.binary (.var (.tail ids_ne .head)) (.var .head))
    ((resolved left right).preserves_type (typed left right))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (decide (left > right))) store 5 :=
  .greater (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_produce_independently_typed_booleans_and_exact_steps
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool ∧
    (inputs left right).check? source = some (core, .bool) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store source (.bool (decide (left > right))) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (decide (left > right))) store 5 ∧
    Core.Steps 5 (Core.State.initial core [.word right, .word left] store)
      (Core.State.final (.bool (decide (left > right))) store) :=
  ⟨typed left right, checked left right, (costed left right store).erase, costed left right store,
    (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds⟩

theorem exact_completion_and_ordered_four_step_state
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 4 source store = some (.bool, .outOfFuel
      ⟨.ret (.word right), [.binaryApply .wordGt (.word left)], store⟩) ∧
    ∀ fuel, ((inputs left right).run? fuel source store =
      some (.bool, .done (.bool (decide (left > right))) store) ↔ 5 ≤ fuel) := by
  constructor
  · rw [LocalInputs.run?, checked]; rfl
  · intro fuel
    simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using
      (costed left right store).checked_runStateful_done_iff (fuel := fuel)
        (checked left right) (inputs left right).sameIds

theorem equal_words_still_take_five_steps (value : Core.Word) (fuel : Nat) (store : Core.Store) :
    ((inputs value value).run? fuel source store = some (.bool, .done (.bool false) store) ↔ 5 ≤ fuel) := by
  simpa using (exact_completion_and_ordered_four_step_state value value store).2 fuel

theorem unsigned_high_bit_and_maximum_are_greater_than_zero (store : Core.Store) :
    (inputs (Core.Word.ofNatModulo (2 ^ 255)) .zero).run? 5 source store =
      some (.bool, .done (.bool true) store) ∧
    (inputs .maximum .zero).run? 5 source store = some (.bool, .done (.bool true) store) ∧
    (inputs .zero .maximum).run? 5 source store = some (.bool, .done (.bool false) store) := by
  have high : decide (Core.Word.ofNatModulo (2 ^ 255) > Core.Word.zero) = true := by decide
  have maximum : decide (Core.Word.maximum > Core.Word.zero) = true := by decide
  have reversed : decide (Core.Word.zero > Core.Word.maximum) = false := by decide
  refine ⟨?_, ?_, ?_⟩
  · exact ((exact_completion_and_ordered_four_step_state
      (Core.Word.ofNatModulo (2 ^ 255)) .zero store).2 5 |>.mpr (by decide)).trans
      (congrArg (fun value => some (Core.Ty.bool, Core.StatefulRunResult.done (.bool value) store)) high)
  · simpa only [maximum] using
      (exact_completion_and_ordered_four_step_state .maximum .zero store).2 5 |>.mpr (by decide)
  · simpa only [reversed] using
      (exact_completion_and_ordered_four_step_state .zero .maximum store).2 5 |>.mpr (by decide)

theorem successful_comparison_requires_ordered_words_and_boolean_result
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (greater left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .bool (decide (leftWord > rightWord)) ∧ cost = leftCost + rightCost + 3 := by
  cases evaluation with
  | greater leftEvaluation rightEvaluation => exact ⟨_, _, _, _, _, leftEvaluation, rightEvaluation, rfl, rfl⟩

theorem zero_does_not_bypass_missing_operands :
    (inputs .zero .zero).check? (greater (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (greater (ref "missing") (ref "r")) = none := by
  constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, greater, ref,
    inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

theorem unused_inputs_and_injective_ids_preserve_comparison
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) :
    ((inputs left right).mapIds mapping injective).run? fuel source store =
      (inputs left right).run? fuel source store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store source (.bool (decide (left > right))) store 5 ∧
    (((inputs left right).bindFresh owner "unused" .unit .unit .unit).run? fuel source store =
      some (.bool, .done (.bool (decide (left > right))) store) ↔
      (inputs left right).run? fuel source store = some (.bool, .done (.bool (decide (left > right))) store)) := by
  have avoids : AvoidsLocalName "unused" source := .greater (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel source store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed left right store),
    avoids.bindFresh_run_done_at_fuel_iff (inputs left right) owner .unit .unit .unit⟩

private def guarded : Syntax.Expr :=
  ⟨span, .conditional (greater ⟨span, .binary (ref "l") ⟨span, .multiply⟩ (ref "r")⟩ (ref "r")) span
    ⟨span, .binary (ref "l") ⟨span, .subtract⟩ (ref "r")⟩ span (ref "l")⟩
private def guardedCore : Core.Expr := .ifE
  (.binary .wordGt (.binary .wordMul (.var 1) (.var 0)) (.var 0))
  (.binary .wordSub (.var 1) (.var 0)) (.var 1)

theorem arithmetic_comparison_selects_a_branch_with_exact_cost
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context guarded .word ∧
    (inputs left right).check? guarded = some (guardedCore, .word) ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store guarded (.word (if left.mul right > right then left.sub right else left)) store
      (if left.mul right > right then 16 else 12) ∧
    ∀ fuel, ((inputs left right).run? fuel guarded store =
      some (.word, .done (.word (if left.mul right > right then left.sub right else left)) store) ↔
      (if left.mul right > right then 16 else 12) ≤ fuel) := by
  have leftTyped : LocalExpressionHasType (inputs left right).names (inputs left right).context (ref "l") .word :=
    .identifier (.tail names_ne .head) (.tail ids_ne .head)
  have rightTyped : LocalExpressionHasType (inputs left right).names (inputs left right).context (ref "r") .word :=
    .identifier .head .head
  have typing : LocalExpressionHasType (inputs left right).names (inputs left right).context guarded .word :=
    .conditional (.greater (.multiply leftTyped rightTyped) rightTyped) (.subtract leftTyped rightTyped) leftTyped
  have resolution : ResolvesLocalExpression (inputs left right).names guarded
      (.ifE (.binary .wordGt (.binary .wordMul (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) (.var ⟨owner, 1⟩))
        (.binary .wordSub (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) (.var ⟨owner, 0⟩)) :=
    .conditional (.greater (.multiply (.identifier (.tail names_ne .head)) (.identifier .head)) (.identifier .head))
      (.subtract (.identifier (.tail names_ne .head)) (.identifier .head)) (.identifier (.tail names_ne .head))
  have accepted : (inputs left right).check? guarded = some (guardedCore, .word) :=
    elaborateLocalExpression?_complete resolution
      (.ifE (.binary (.binary (.var (.tail ids_ne .head)) (.var .head)) (.var .head))
        (.binary (.var (.tail ids_ne .head)) (.var .head)) (.var (.tail ids_ne .head)))
      (resolution.preserves_type typing)
  have leftCost : LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (ref "l") (.word left) store 1 := .identifier (.tail names_ne .head) (.tail ids_ne .head)
  have rightCost : LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (ref "r") (.word right) store 1 := .identifier .head .head
  have guardCost : LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (greater ⟨span, .binary (ref "l") ⟨span, .multiply⟩ (ref "r")⟩ (ref "r"))
      (.bool (decide (left.mul right > right))) store 9 :=
    .greater (leftCost := 5) (rightCost := 1) (.multiply leftCost rightCost) rightCost
  have evaluation : LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store guarded (.word (if left.mul right > right then left.sub right else left)) store
      (if left.mul right > right then 16 else 12) := by
    by_cases selected : left.mul right > right
    · simp only [if_pos selected]
      exact .ifTrue (by simpa [selected] using guardCost) (.subtract leftCost rightCost)
    · simp only [if_neg selected]
      exact .ifFalse (by simpa [selected] using guardCost) leftCost
  refine ⟨typing, accepted, evaluation, ?_⟩
  intro fuel
  simpa only [LocalInputs.run?, accepted, bind, Option.bind_some, pure,
    Option.some.injEq, Prod.mk.injEq, true_and] using
    evaluation.checked_runStateful_done_iff (fuel := fuel) accepted (inputs left right).sameIds

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation "Word")⟩
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def declaration (returnName : String) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "greater"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation returnName]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some source)⟩]⟩⟩⟩
private def compiled : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word, core, .bool⟩
private theorem wordAnnotation : TypeNameDenotes types (annotation "Word") .word :=
  .named (.tail (by decide) .head)
private theorem compilation : RuntimeFunctionCompiles types owner (declaration "Bool") compiled :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons wordAnnotation.structural (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons wordAnnotation.structural (by change "r" ∉ ["l"]; simp) .nil),
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.greater (.identifier (.tail names_ne .head)) (.identifier .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))⟩
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ :=
  ⟨compilation.header,
    .cons wordAnnotation.structural (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons wordAnnotation.structural (by change "r" ∉ ["l"]; simp) .nil), compilation.body⟩

theorem independent_compilation_preparation_and_exact_boolean_entry_cost
    (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionCompiles types owner (declaration "Bool") compiled ∧
    compileRuntimeFunction? types owner (declaration "Bool") = some compiled ∧
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ ∧
    RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (decide (left > right))) store 5 ∧
    ∀ fuel, (runRuntimeFunction? types owner (declaration "Bool") (arguments left right) fuel store =
      some (.bool, .done (.bool (decide (left > right))) store) ↔ 5 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (decide (left > right))) store 5 :=
    .intro (preparation left right) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (costed left right store))
  exact ⟨compilation, compilation.complete, preparation left right, evaluation, fun _ => evaluation.run_done_iff⟩

theorem word_return_annotation_rejects_a_boolean_comparison :
    compileRuntimeFunction? types owner (declaration "Word") = none := by
  apply compileRuntimeFunction?_eq_none_iff.mpr
  intro ⟨candidate, accepted⟩
  have sameInputs : candidate.inputs = compiled.inputs :=
    accepted.parameters.result_unique compilation.parameters
  have expectedHeader : RuntimeFunctionHeader types (declaration "Word").value.signature .word :=
    ⟨rfl, rfl, rfl, rfl, .single wordAnnotation.structural⟩
  have sameReturn : candidate.returnType = .word := accepted.header.type_unique expectedHeader
  have candidateBody := accepted.body
  rw [sameInputs] at candidateBody
  have bodyReturn : candidate.returnType = .bool := (candidateBody.result_unique compilation.body).2
  cases sameReturn.symm.trans bodyReturn

end Tests.FrontendWordGreater
end

section
-- leanmerge: from Solcore.Test.FrontendWordInequalityProperties
/-! Independent Word-only inequality returns Bool while preserving strict operand
order, exact transition counts, and the complete checked entry contract. -/

set_option autoImplicit false

namespace Tests.FrontendWordInequality

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Inequality", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "inequality.sol"⟩, 19, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def notEqual (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .notEqual⟩ right⟩
private def source := notEqual (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := .unary .boolNot (.binary .wordEq (.var 1) (.var 0))
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.unary .boolNot (.binary .wordEq (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩))) :=
  .notEqual (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool :=
  .notEqual (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (left right : Core.Word) :
    (inputs left right).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete (resolved left right)
    (.unary (.binary (.var (.tail ids_ne .head)) (.var .head)))
    ((resolved left right).preserves_type (typed left right))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (!(left == right))) store 7 :=
  .notEqual (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_produce_independent_bool_typing_evaluation_and_exact_steps
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool ∧
    (inputs left right).check? source = some (core, .bool) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store source (.bool (!(left == right))) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (!(left == right))) store 7 ∧
    Core.Steps 7 (Core.State.initial core [.word right, .word left] store)
      (Core.State.final (.bool (!(left == right))) store) :=
  ⟨typed left right, checked left right,
    .notEqual (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head),
    costed left right store, (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds⟩

theorem exact_fuel_five_checkpoint_preserves_left_and_right_operand_order
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 5 source store = some (.bool, .outOfFuel
      ⟨.ret (.word right), [.binaryApply .wordEq (.word left), .unaryApply .boolNot], store⟩) ∧
    ∀ fuel, ((inputs left right).run? fuel source store =
      some (.bool, .done (.bool (!(left == right))) store) ↔ 7 ≤ fuel) := by
  constructor
  · rw [LocalInputs.run?, checked]; rfl
  · intro fuel
    simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using
      (costed left right store).checked_runStateful_done_iff (fuel := fuel)
        (checked left right) (inputs left right).sameIds

theorem equal_and_distinct_words_still_need_seven_steps_and_return_no_word_flag
    (left right : Core.Word) (different : left ≠ right) (fuel : Nat) (store : Core.Store) :
    ((inputs left left).run? fuel source store = some (.bool, .done (.bool false) store) ↔ 7 ≤ fuel) ∧
    ((inputs left right).run? fuel source store = some (.bool, .done (.bool true) store) ↔ 7 ≤ fuel) ∧
    ∀ word, Core.Value.bool (!(left == right)) ≠ .word word := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using (exact_fuel_five_checkpoint_preserves_left_and_right_operand_order left left store).2 fuel
  · have unequal : (left == right) = false := beq_eq_false_iff_ne.mpr different
    simpa only [unequal, Bool.not_false] using (exact_fuel_five_checkpoint_preserves_left_and_right_operand_order left right store).2 fuel
  · intro word same; cases same

theorem sixth_step_retains_boolean_negation_and_its_one_step_residual
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    (inputs left right).run? 6 source store = some (.bool, .outOfFuel
      ⟨.ret (.bool (left == right)), [.unaryApply .boolNot], store⟩) ∧
    Core.runStateful 1 ⟨.ret (.word right), [.binaryApply .wordEq (.word left), .unaryApply .boolNot], store⟩ =
      .outOfFuel ⟨.ret (.bool (left == right)), [.unaryApply .boolNot], store⟩ ∧
    Core.Steps 1 ⟨.ret (.bool (left == right)), [.unaryApply .boolNot], store⟩
      (Core.State.final (.bool (!(left == right))) store) ∧
    (Core.runStateful additional ⟨.ret (.bool (left == right)), [.unaryApply .boolNot], store⟩ =
      .done (.bool (!(left == right))) store ↔ 1 ≤ additional) ∧
    (inputs left right).run? (6 + additional) source store = some (.bool,
      Core.runStateful additional ⟨.ret (.bool (left == right)), [.unaryApply .boolNot], store⟩) := by
  have exhausted : (inputs left right).run? 6 source store = some (.bool, .outOfFuel
      ⟨.ret (.bool (left == right)), [.unaryApply .boolNot], store⟩) := by
    rw [LocalInputs.run?, checked]; rfl
  have coreExhausted : Core.runStateful 6 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel ⟨.ret (.bool (left == right)), [.unaryApply .boolNot], store⟩ := rfl
  have residual := ((costed left right store).checked_residual_of_outOfFuel
    (checked left right) (inputs left right).sameIds coreExhausted).2
  exact ⟨exhausted, rfl, residual, residual.runStateful_done_iff, LocalInputs.run?_resume exhausted additional⟩

theorem independent_inequality_requires_both_ordered_word_operands
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (notEqual left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .bool (!(leftWord == rightWord)) ∧ cost = leftCost + rightCost + 5 := by
  cases evaluation with
  | notEqual leftEvaluation rightEvaluation => exact ⟨_, _, _, _, _, leftEvaluation, rightEvaluation, rfl, rfl⟩

theorem missing_either_operand_is_not_bypassed_by_equal_known_values :
    (inputs .zero .zero).check? (notEqual (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (notEqual (ref "missing") (ref "r")) = none := by
  constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, notEqual, ref,
    inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

private def typedInputs (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" leftType left leftTyped).bindFresh owner "r" rightType right rightTyped

theorem non_word_on_either_side_is_rejected_without_polymorphic_inequality
    (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType)
    (wrong : leftType ≠ .word ∨ rightType ≠ .word) (fuel : Nat) (store : Core.Store) :
    (typedInputs leftType rightType left right leftTyped rightTyped).check? source = none ∧
    (typedInputs leftType rightType left right leftTyped rightTyped).run? fuel source store = none := by
  have rejected : (typedInputs leftType rightType left right leftTyped rightTyped).check? source = none := by
    cases accepted : (typedInputs leftType rightType left right leftTyped rightTyped).check? source with
    | none => rfl
    | some result =>
      rcases result with ⟨compiledCore, resultType⟩
      have whole := LocalInputs.check?_iff_hasType.mp ⟨compiledCore, accepted⟩
      cases whole with
      | notEqual first second =>
        have firstTyped : LocalExpressionHasType
            (typedInputs leftType rightType left right leftTyped rightTyped).names
            (typedInputs leftType rightType left right leftTyped rightTyped).context (ref "l") leftType :=
          .identifier (.tail names_ne .head) (.tail ids_ne .head)
        have secondTyped : LocalExpressionHasType
            (typedInputs leftType rightType left right leftTyped rightTyped).names
            (typedInputs leftType rightType left right leftTyped rightTyped).context (ref "r") rightType :=
          .identifier .head .head
        exact False.elim (wrong.elim (fun mismatch => mismatch (firstTyped.type_unique first))
          (fun mismatch => mismatch (secondTyped.type_unique second)))
  exact ⟨rejected, (LocalInputs.run?_eq_none_iff fuel store).mpr rejected⟩

theorem symmetric_final_inequality_does_not_permit_swapping_pending_operands
    (left right : Core.Word) (different : left ≠ right) (store : Core.Store) :
    Core.runStateful 7 (Core.State.initial core [.word right, .word left] store) =
      Core.runStateful 7 (Core.State.initial (.unary .boolNot (.binary .wordEq (.var 0) (.var 1))) [.word right, .word left] store) ∧
    Core.runStateful 5 (Core.State.initial core [.word right, .word left] store) ≠
      Core.runStateful 5 (Core.State.initial (.unary .boolNot (.binary .wordEq (.var 0) (.var 1))) [.word right, .word left] store) := by
  constructor
  · change Core.StatefulRunResult.done (.bool (!(left == right))) store = .done (.bool (!(right == left))) store
    rw [beq_eq_false_iff_ne.mpr different, beq_eq_false_iff_ne.mpr (Ne.symm different)]
  · intro same
    have controls := congrArg Core.State.control (Core.StatefulRunResult.outOfFuel.inj same)
    exact different (Core.Value.word.inj (Core.Control.ret.inj controls)).symm

theorem inequality_preserves_unrelated_inputs_and_ignores_only_spans_and_injective_ids
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store)
    (otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    ((inputs left right).mapIds mapping injective).run? fuel source store =
      (inputs left right).run? fuel source store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store source (.bool (!(left == right))) store 7 ∧
    resolveLocalExpression? (inputs left right).names source = resolveLocalExpression? (inputs left right).names
      ⟨otherSpan, .binary (ref "l") ⟨otherOperatorSpan, .notEqual⟩ (ref "r")⟩ := by
  have avoids : AvoidsLocalName "unused" source := .notEqual (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel source store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed left right store),
    resolveLocalExpression?_notEqual_spans _ _ _ _ _ _ _⟩

theorem replay_structural_budget_and_checkpoint_residual_keep_boolean_inequality
    (left right : Core.Word) (first replacement : Core.Store) (additional : Nat) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      replacement source (.bool (!(left == right))) replacement 7 ∧
    7 ≤ localExpressionFuelBound source ∧ localExpressionFuelBound source = 7 ∧
    Core.Steps 2 ⟨.ret (.word right), [.binaryApply .wordEq (.word left), .unaryApply .boolNot], replacement⟩
      (Core.State.final (.bool (!(left == right))) replacement) ∧
    (inputs left right).run? (5 + additional) source replacement = some (.bool,
      Core.runStateful additional ⟨.ret (.word right), [.binaryApply .wordEq (.word left), .unaryApply .boolNot], replacement⟩) := by
  have replayed := (costed left right first).change_store replacement
  have exhausted := (exact_fuel_five_checkpoint_preserves_left_and_right_operand_order left right replacement).1
  have coreExhausted : Core.runStateful 5 (Core.State.initial core [.word right, .word left] replacement) =
      .outOfFuel ⟨.ret (.word right), [.binaryApply .wordEq (.word left), .unaryApply .boolNot], replacement⟩ := rfl
  refine ⟨replayed, replayed.cost_le_fuelBound, ?_,
    (replayed.checked_residual_of_outOfFuel (checked left right) (inputs left right).sameIds coreExhausted).2,
    LocalInputs.run?_resume exhausted additional⟩
  simp [source, notEqual, ref, localExpressionFuelBound]

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation "Word")⟩
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def declaration (returnName : String) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "notEqual"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation returnName]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some source)⟩]⟩⟩⟩
private def compiled : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word, core, .bool⟩
private theorem wordAnnotation : TypeNameDenotes types (annotation "Word") .word :=
  .named (.tail (by decide) .head)
private theorem compilation : RuntimeFunctionCompiles types owner (declaration "Bool") compiled :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons wordAnnotation.structural (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons wordAnnotation.structural (by change "r" ∉ ["l"]; simp) .nil),
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.notEqual (.identifier (.tail names_ne .head)) (.identifier .head))
      (.unary (.binary (.var (.tail ids_ne .head)) (.var .head)))
      (.unary (.binary (.var (.tail ids_ne .head)) (.var .head)))⟩
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ :=
  ⟨compilation.header,
    .cons wordAnnotation.structural (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons wordAnnotation.structural (by change "r" ∉ ["l"]; simp) .nil), compilation.body⟩

theorem independent_compilation_preparation_and_exact_bool_entry_cost
    (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionCompiles types owner (declaration "Bool") compiled ∧
    compileRuntimeFunction? types owner (declaration "Bool") = some compiled ∧
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ ∧
    RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (!(left == right))) store 7 ∧
    ∀ fuel, (runRuntimeFunction? types owner (declaration "Bool") (arguments left right) fuel store =
      some (.bool, .done (.bool (!(left == right))) store) ↔ 7 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (!(left == right))) store 7 :=
    .intro (preparation left right) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (costed left right store))
  exact ⟨compilation, compilation.complete, preparation left right, evaluation, fun _ => evaluation.run_done_iff⟩

theorem declared_word_return_rejects_a_bool_inequality_result :
    compileRuntimeFunction? types owner (declaration "Word") = none := by
  apply compileRuntimeFunction?_eq_none_iff.mpr
  intro ⟨candidate, accepted⟩
  have sameInputs : candidate.inputs = compiled.inputs := accepted.parameters.result_unique compilation.parameters
  have expectedHeader : RuntimeFunctionHeader types (declaration "Word").value.signature .word :=
    ⟨rfl, rfl, rfl, rfl, .single wordAnnotation.structural⟩
  have sameReturn : candidate.returnType = .word := accepted.header.type_unique expectedHeader
  have candidateBody := accepted.body
  rw [sameInputs] at candidateBody
  have bodyReturn : candidate.returnType = .bool := (candidateBody.result_unique compilation.body).2
  cases sameReturn.symm.trans bodyReturn

end Tests.FrontendWordInequality
end

section
-- leanmerge: from Solcore.Test.FrontendWordLessCostProperties
/-! Independent exact paths for the existing ordered less-than Core expansion.
Generated lets, the weakened right reference, and every continuation are retained. -/

set_option autoImplicit false

namespace Tests.FrontendWordLessCost

open Solcore Solcore.Frontend

private def core : Core.Expr := (Core.Expr.var 1).wordLt (.var 0)
private def environment (left right : Core.Word) (tail : Core.Environment) : Core.Environment :=
  .word right :: .word left :: tail
private def result (left right : Core.Word) : Core.Value := .bool (decide (left < right))
private def firstBinding (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.letBody (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1)))
    (environment left right tail)], store⟩
private def secondBinding (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) : Core.State :=
  ⟨.ret (.word right), [.letBody (.binary .wordGt (.var 0) (.var 1))
    (.word left :: environment left right tail)], store⟩
private def pending (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.binaryApply .wordGt (.word right)], store⟩
private theorem coreShape :
    core = .letE (.var 1) (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1))) := by
  simp [core, Core.Expr.wordLt_expansion, Core.Expr.weakenAt]

theorem let_binding_counts_enter_and_bind_for_any_actual_value
    (value : Core.Value) (tail : Core.Environment) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 4 ⟨.eval (.letE (.var 0) (.var 0)) (value :: tail), continuation, store⟩
      ⟨.ret value, continuation, store⟩ :=
  CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)

theorem exact_nested_core_keeps_left_first_and_weakens_right :
    core = .letE (.var 1) (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1))) ∧
    Core.HasType [.word, .word] core .bool :=
  ⟨coreShape, Core.HasType.wordLt (.var rfl) (.var rfl)⟩

theorem ordered_variables_take_eleven_steps_under_any_continuation
    (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 11 ⟨.eval core (environment left right tail), continuation, store⟩
      ⟨.ret (result left right), continuation, store⟩ := by
  apply CostStepComposition.wordLt (leftCost := 1) (rightCost := 1)
  · intro frames
    exact .cons (.var rfl) .refl
  · intro frames
    simp only [Core.Expr.weakenAt, Nat.le_refl, ↓reduceIte]
    exact .cons (.var rfl) .refl

theorem all_fuel_thresholds_are_exact_and_preserve_the_actual_store
    (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) (fuel : Nat) :
    (Core.runStateful fuel (Core.State.initial core (environment left right tail) store) =
      .done (result left right) store ↔ 11 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (Core.State.initial core (environment left right tail) store) =
      .outOfFuel checkpoint) ↔ fuel < 11) := by
  have path := ordered_variables_take_eleven_steps_under_any_continuation left right tail store []
  exact ⟨path.runStateful_done_iff, path.runStateful_outOfFuel_iff⟩

theorem actual_let_and_binary_checkpoints_retain_both_ordered_words
    (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) :
    Core.runStateful 2 (Core.State.initial core (environment left right tail) store) =
      .outOfFuel (firstBinding left right tail store) ∧
    Core.runStateful 5 (Core.State.initial core (environment left right tail) store) =
      .outOfFuel (secondBinding left right tail store) ∧
    Core.runStateful 10 (Core.State.initial core (environment left right tail) store) =
      .outOfFuel (pending left right store) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [coreShape] <;> rfl

theorem genuine_let_checkpoints_retain_exact_nine_and_six_step_suffixes
    (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) (additional : Nat) :
    Core.Steps 9 (firstBinding left right tail store) (Core.State.final (result left right) store) ∧
    Core.Steps 6 (secondBinding left right tail store) (Core.State.final (result left right) store) ∧
    Core.Steps 1 (pending left right store) (Core.State.final (result left right) store) ∧
    Core.runStateful additional (firstBinding left right tail store) =
      Core.runStateful (2 + additional) (Core.State.initial core (environment left right tail) store) ∧
    Core.runStateful additional (secondBinding left right tail store) =
      Core.runStateful (5 + additional) (Core.State.initial core (environment left right tail) store) ∧
    (Core.runStateful additional (secondBinding left right tail store) =
      .done (result left right) store ↔ 6 ≤ additional) ∧
    ((∃ checkpoint, Core.runStateful additional (firstBinding left right tail store) =
      .outOfFuel checkpoint) ↔ additional < 9) := by
  have path := ordered_variables_take_eleven_steps_under_any_continuation left right tail store []
  obtain ⟨first, second, last⟩ := actual_let_and_binary_checkpoints_retain_both_ordered_words left right tail store
  exact ⟨(path.residual_of_outOfFuel first).2, (path.residual_of_outOfFuel second).2,
    (path.residual_of_outOfFuel last).2, Core.runStateful_resume first additional,
    Core.runStateful_resume second additional, path.resumed_done_iff second, path.resumed_outOfFuel_iff first⟩

theorem multichunk_resumption_uses_the_retained_let_environments
    (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) (additional : Nat) :
    Core.runStateful 3 (firstBinding left right tail store) = .outOfFuel (secondBinding left right tail store) ∧
    Core.runStateful 5 (secondBinding left right tail store) = .outOfFuel (pending left right store) ∧
    Core.runStateful additional (pending left right store) =
      Core.runStateful (10 + additional) (Core.State.initial core (environment left right tail) store) := by
  have first := (actual_let_and_binary_checkpoints_retain_both_ordered_words left right tail store).1
  have second : Core.runStateful 3 (firstBinding left right tail store) =
      .outOfFuel (secondBinding left right tail store) := rfl
  have third : Core.runStateful 5 (secondBinding left right tail store) =
      .outOfFuel (pending left right store) := rfl
  refine ⟨second, third, ?_⟩
  simpa only [← Nat.add_assoc] using (Core.runStateful_resume third additional).trans
    ((Core.runStateful_resume second (5 + additional)).trans (Core.runStateful_resume first (3 + (5 + additional))))

theorem nonempty_continuation_is_retained_then_consumed_separately
    (left right : Core.Word) (tail : Core.Environment) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 11 ⟨.eval core (environment left right tail), .unaryApply .boolNot :: continuation, store⟩
      ⟨.ret (result left right), .unaryApply .boolNot :: continuation, store⟩ ∧
    Core.Steps 12 ⟨.eval core (environment left right tail), .unaryApply .boolNot :: continuation, store⟩
      ⟨.ret (.bool (!(decide (left < right)))), continuation, store⟩ := by
  have path := ordered_variables_take_eleven_steps_under_any_continuation left right tail store
    (.unaryApply .boolNot :: continuation)
  exact ⟨path, path.trans (.cons (.applyUnary rfl) .refl)⟩

theorem equal_values_do_not_remove_generated_binding_steps
    (value : Core.Word) (tail : Core.Environment) (store : Core.Store) (fuel : Nat) :
    (Core.runStateful fuel (Core.State.initial core (environment value value tail) store) =
      .done (.bool false) store ↔ 11 ≤ fuel) ∧
    Core.runStateful 10 (Core.State.initial core (environment value value tail) store) =
      .outOfFuel (pending value value store) := by
  have threshold := (all_fuel_thresholds_are_exact_and_preserve_the_actual_store value value tail store fuel).1
  have exhausted := (actual_let_and_binary_checkpoints_retain_both_ordered_words value value tail store).2.2
  exact ⟨by simpa [result] using threshold, exhausted⟩

theorem reversing_strictly_ordered_actual_words_changes_the_boolean
    (left right : Core.Word) (ordered : left < right) (tail : Core.Environment) (store : Core.Store) :
    Core.runStateful 11 (Core.State.initial core (environment left right tail) store) = .done (.bool true) store ∧
    Core.runStateful 11 (Core.State.initial core (environment right left tail) store) = .done (.bool false) store := by
  have reversed : ¬right < left := by
    intro opposite
    exact Nat.lt_irrefl left.val (Nat.lt_trans ordered opposite)
  have first := (all_fuel_thresholds_are_exact_and_preserve_the_actual_store left right tail store 11).1.mpr (by decide)
  have second := (all_fuel_thresholds_are_exact_and_preserve_the_actual_store right left tail store 11).1.mpr (by decide)
  exact ⟨by simpa [result, ordered] using first, by simpa [result, reversed] using second⟩

end Tests.FrontendWordLessCost
end

section
-- leanmerge: from Solcore.Test.FrontendWordLessEqualProperties
/-! Independent unsigned Word ordering returns Bool while preserving strict operand
order, exact transition counts, and the complete checked entry contract. -/

set_option autoImplicit false

namespace Tests.FrontendWordLessEqual

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LessEqual", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "less_equal.sol"⟩, 19, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def lessEqual (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .lessEqual⟩ right⟩
private def source := lessEqual (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := .unary .boolNot (.binary .wordGt (.var 1) (.var 0))
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.unary .boolNot (.binary .wordGt (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩))) :=
  .lessEqual (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool :=
  .lessEqual (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (left right : Core.Word) :
    (inputs left right).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete (resolved left right)
    (.unary (.binary (.var (.tail ids_ne .head)) (.var .head)))
    ((resolved left right).preserves_type (typed left right))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (!(decide (left > right)))) store 7 :=
  .lessEqual (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_produce_independent_bool_typing_evaluation_and_exact_steps
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool ∧
    (inputs left right).check? source = some (core, .bool) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store source (.bool (!(decide (left > right)))) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (!(decide (left > right)))) store 7 ∧
    Core.Steps 7 (Core.State.initial core [.word right, .word left] store)
      (Core.State.final (.bool (!(decide (left > right)))) store) :=
  ⟨typed left right, checked left right,
    .lessEqual (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head),
    costed left right store, (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds⟩

theorem exact_fuel_five_checkpoint_preserves_left_and_right_operand_order
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 5 source store = some (.bool, .outOfFuel
      ⟨.ret (.word right), [.binaryApply .wordGt (.word left), .unaryApply .boolNot], store⟩) ∧
    ∀ fuel, ((inputs left right).run? fuel source store =
      some (.bool, .done (.bool (!(decide (left > right)))) store) ↔ 7 ≤ fuel) := by
  constructor
  · rw [LocalInputs.run?, checked]; rfl
  · intro fuel
    simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using
      (costed left right store).checked_runStateful_done_iff (fuel := fuel)
        (checked left right) (inputs left right).sameIds

theorem boolean_result_is_true_exactly_for_unsigned_less_equal (left right : Core.Word) :
    !(decide (left > right)) = true ↔ left ≤ right := by
  by_cases bounded : left ≤ right
  · have notGreater : ¬left > right := Nat.not_lt.mpr bounded
    simp [bounded, notGreater]
  · have greater : left > right := Nat.lt_of_not_ge bounded
    simp [bounded, greater]

theorem equal_strict_and_reverse_orders_keep_seven_steps_and_never_return_word_flags
    (left right : Core.Word) (strict : left < right) (fuel : Nat) (store : Core.Store) :
    ((inputs left left).run? fuel source store = some (.bool, .done (.bool true) store) ↔ 7 ≤ fuel) ∧
    ((inputs left right).run? fuel source store = some (.bool, .done (.bool true) store) ↔ 7 ≤ fuel) ∧
    ((inputs right left).run? fuel source store = some (.bool, .done (.bool false) store) ↔ 7 ≤ fuel) ∧
    ∀ word, Core.Value.bool (!(decide (left > right))) ≠ .word word := by
  have notGreater : ¬left > right := Nat.not_lt.mpr (Nat.le_of_lt strict)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (exact_fuel_five_checkpoint_preserves_left_and_right_operand_order left left store).2 fuel
  · simpa [notGreater] using (exact_fuel_five_checkpoint_preserves_left_and_right_operand_order left right store).2 fuel
  · simpa [strict] using (exact_fuel_five_checkpoint_preserves_left_and_right_operand_order right left store).2 fuel
  · intro word same; cases same

theorem zero_high_bit_and_maximum_distinguish_unsigned_order_and_operand_direction (store : Core.Store) :
    (inputs .zero .zero).run? 7 source store = some (.bool, .done (.bool true) store) ∧
    (inputs .maximum .maximum).run? 7 source store = some (.bool, .done (.bool true) store) ∧
    (inputs .zero (Core.Word.ofNatModulo (2 ^ 255))).run? 7 source store = some (.bool, .done (.bool true) store) ∧
    (inputs (Core.Word.ofNatModulo (2 ^ 255)) .zero).run? 7 source store = some (.bool, .done (.bool false) store) ∧
    (inputs (Core.Word.ofNatModulo (2 ^ 255)) .maximum).run? 7 source store = some (.bool, .done (.bool true) store) ∧
    (inputs .maximum (Core.Word.ofNatModulo (2 ^ 255))).run? 7 source store = some (.bool, .done (.bool false) store) := by
  have first := equal_strict_and_reverse_orders_keep_seven_steps_and_never_return_word_flags
    .zero (Core.Word.ofNatModulo (2 ^ 255)) (by decide) 7 store
  have second := equal_strict_and_reverse_orders_keep_seven_steps_and_never_return_word_flags
    (Core.Word.ofNatModulo (2 ^ 255)) .maximum (by decide) 7 store
  refine ⟨first.1.mpr (by decide), ?_, first.2.1.mpr (by decide), first.2.2.1.mpr (by decide),
    second.2.1.mpr (by decide), second.2.2.1.mpr (by decide)⟩
  simpa using (exact_fuel_five_checkpoint_preserves_left_and_right_operand_order .maximum .maximum store).2 7 |>.mpr (by decide)

theorem sixth_step_retains_boolean_negation_and_its_one_step_residual
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    (inputs left right).run? 6 source store = some (.bool, .outOfFuel
      ⟨.ret (.bool (decide (left > right))), [.unaryApply .boolNot], store⟩) ∧
    Core.runStateful 1 ⟨.ret (.word right), [.binaryApply .wordGt (.word left), .unaryApply .boolNot], store⟩ =
      .outOfFuel ⟨.ret (.bool (decide (left > right))), [.unaryApply .boolNot], store⟩ ∧
    Core.Steps 1 ⟨.ret (.bool (decide (left > right))), [.unaryApply .boolNot], store⟩
      (Core.State.final (.bool (!(decide (left > right)))) store) ∧
    (Core.runStateful additional ⟨.ret (.bool (decide (left > right))), [.unaryApply .boolNot], store⟩ =
      .done (.bool (!(decide (left > right)))) store ↔ 1 ≤ additional) ∧
    (inputs left right).run? (6 + additional) source store = some (.bool,
      Core.runStateful additional ⟨.ret (.bool (decide (left > right))), [.unaryApply .boolNot], store⟩) := by
  have exhausted : (inputs left right).run? 6 source store = some (.bool, .outOfFuel
      ⟨.ret (.bool (decide (left > right))), [.unaryApply .boolNot], store⟩) := by
    rw [LocalInputs.run?, checked]; rfl
  have coreExhausted : Core.runStateful 6 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel ⟨.ret (.bool (decide (left > right))), [.unaryApply .boolNot], store⟩ := rfl
  have residual := ((costed left right store).checked_residual_of_outOfFuel
    (checked left right) (inputs left right).sameIds coreExhausted).2
  exact ⟨exhausted, rfl, residual, residual.runStateful_done_iff, LocalInputs.run?_resume exhausted additional⟩

theorem independent_less_equal_requires_both_ordered_word_operands
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (lessEqual left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .bool (!(decide (leftWord > rightWord))) ∧ cost = leftCost + rightCost + 5 := by
  cases evaluation with
  | lessEqual leftEvaluation rightEvaluation => exact ⟨_, _, _, _, _, leftEvaluation, rightEvaluation, rfl, rfl⟩

theorem missing_either_operand_is_not_bypassed_by_equal_known_values :
    (inputs .zero .zero).check? (lessEqual (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (lessEqual (ref "missing") (ref "r")) = none := by
  constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, lessEqual, ref,
    inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

private def typedInputs (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" leftType left leftTyped).bindFresh owner "r" rightType right rightTyped

theorem non_word_on_either_side_is_rejected_without_polymorphic_less_equal
    (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType)
    (wrong : leftType ≠ .word ∨ rightType ≠ .word) (fuel : Nat) (store : Core.Store) :
    (typedInputs leftType rightType left right leftTyped rightTyped).check? source = none ∧
    (typedInputs leftType rightType left right leftTyped rightTyped).run? fuel source store = none := by
  have rejected : (typedInputs leftType rightType left right leftTyped rightTyped).check? source = none := by
    cases accepted : (typedInputs leftType rightType left right leftTyped rightTyped).check? source with
    | none => rfl
    | some result =>
      rcases result with ⟨compiledCore, resultType⟩
      have whole := LocalInputs.check?_iff_hasType.mp ⟨compiledCore, accepted⟩
      cases whole with
      | lessEqual first second =>
        have firstTyped : LocalExpressionHasType
            (typedInputs leftType rightType left right leftTyped rightTyped).names
            (typedInputs leftType rightType left right leftTyped rightTyped).context (ref "l") leftType :=
          .identifier (.tail names_ne .head) (.tail ids_ne .head)
        have secondTyped : LocalExpressionHasType
            (typedInputs leftType rightType left right leftTyped rightTyped).names
            (typedInputs leftType rightType left right leftTyped rightTyped).context (ref "r") rightType :=
          .identifier .head .head
        exact False.elim (wrong.elim (fun mismatch => mismatch (firstTyped.type_unique first))
          (fun mismatch => mismatch (secondTyped.type_unique second)))
  exact ⟨rejected, (LocalInputs.run?_eq_none_iff fuel store).mpr rejected⟩

theorem less_equal_preserves_unrelated_inputs_and_ignores_only_spans_and_injective_ids
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store)
    (otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    ((inputs left right).mapIds mapping injective).run? fuel source store =
      (inputs left right).run? fuel source store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store source (.bool (!(decide (left > right)))) store 7 ∧
    resolveLocalExpression? (inputs left right).names source = resolveLocalExpression? (inputs left right).names
      ⟨otherSpan, .binary (ref "l") ⟨otherOperatorSpan, .lessEqual⟩ (ref "r")⟩ := by
  have avoids : AvoidsLocalName "unused" source := .lessEqual (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel source store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed left right store),
    resolveLocalExpression?_lessEqual_spans _ _ _ _ _ _ _⟩

theorem replay_structural_budget_and_checkpoint_residual_keep_boolean_less_equal
    (left right : Core.Word) (first replacement : Core.Store) (additional : Nat) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      replacement source (.bool (!(decide (left > right)))) replacement 7 ∧
    7 ≤ localExpressionFuelBound source ∧ localExpressionFuelBound source = 7 ∧
    Core.Steps 2 ⟨.ret (.word right), [.binaryApply .wordGt (.word left), .unaryApply .boolNot], replacement⟩
      (Core.State.final (.bool (!(decide (left > right)))) replacement) ∧
    (inputs left right).run? (5 + additional) source replacement = some (.bool,
      Core.runStateful additional ⟨.ret (.word right), [.binaryApply .wordGt (.word left), .unaryApply .boolNot], replacement⟩) := by
  have replayed := (costed left right first).change_store replacement
  have exhausted := (exact_fuel_five_checkpoint_preserves_left_and_right_operand_order left right replacement).1
  have coreExhausted : Core.runStateful 5 (Core.State.initial core [.word right, .word left] replacement) =
      .outOfFuel ⟨.ret (.word right), [.binaryApply .wordGt (.word left), .unaryApply .boolNot], replacement⟩ := rfl
  refine ⟨replayed, replayed.cost_le_fuelBound, ?_,
    (replayed.checked_residual_of_outOfFuel (checked left right) (inputs left right).sameIds coreExhausted).2,
    LocalInputs.run?_resume exhausted additional⟩
  simp [source, lessEqual, ref, localExpressionFuelBound]

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation "Word")⟩
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def declaration (returnName : String) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "lessEqual"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation returnName]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some source)⟩]⟩⟩⟩
private def compiled : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word, core, .bool⟩
private theorem wordAnnotation : TypeNameDenotes types (annotation "Word") .word :=
  .named (.tail (by decide) .head)
private theorem compilation : RuntimeFunctionCompiles types owner (declaration "Bool") compiled :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons wordAnnotation.structural (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons wordAnnotation.structural (by change "r" ∉ ["l"]; simp) .nil),
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.lessEqual (.identifier (.tail names_ne .head)) (.identifier .head))
      (.unary (.binary (.var (.tail ids_ne .head)) (.var .head)))
      (.unary (.binary (.var (.tail ids_ne .head)) (.var .head)))⟩
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ :=
  ⟨compilation.header,
    .cons wordAnnotation.structural (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons wordAnnotation.structural (by change "r" ∉ ["l"]; simp) .nil), compilation.body⟩

theorem independent_compilation_preparation_and_exact_bool_entry_cost
    (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionCompiles types owner (declaration "Bool") compiled ∧
    compileRuntimeFunction? types owner (declaration "Bool") = some compiled ∧
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ ∧
    RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (!(decide (left > right)))) store 7 ∧
    ∀ fuel, (runRuntimeFunction? types owner (declaration "Bool") (arguments left right) fuel store =
      some (.bool, .done (.bool (!(decide (left > right)))) store) ↔ 7 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (!(decide (left > right)))) store 7 :=
    .intro (preparation left right) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (costed left right store))
  exact ⟨compilation, compilation.complete, preparation left right, evaluation, fun _ => evaluation.run_done_iff⟩

theorem declared_word_return_rejects_a_bool_less_equal_result :
    compileRuntimeFunction? types owner (declaration "Word") = none := by
  apply compileRuntimeFunction?_eq_none_iff.mpr
  intro ⟨candidate, accepted⟩
  have sameInputs : candidate.inputs = compiled.inputs := accepted.parameters.result_unique compilation.parameters
  have expectedHeader : RuntimeFunctionHeader types (declaration "Word").value.signature .word :=
    ⟨rfl, rfl, rfl, rfl, .single wordAnnotation.structural⟩
  have sameReturn : candidate.returnType = .word := accepted.header.type_unique expectedHeader
  have candidateBody := accepted.body
  rw [sameInputs] at candidateBody
  have bodyReturn : candidate.returnType = .bool := (candidateBody.result_unique compilation.body).2
  cases sameReturn.symm.trans bodyReturn

end Tests.FrontendWordLessEqual
end

section
-- leanmerge: from Solcore.Test.FrontendWordLessProperties
/-! Independent unsigned Word ordering returns Bool while preserving strict operand
order, exact transition counts, and the complete checked entry contract. -/

set_option autoImplicit false

namespace Tests.FrontendWordLess

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Less", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "less.sol"⟩, 19, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def less (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .less⟩ right⟩
private def source := less (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := (Core.Expr.var 1).wordLt (.var 0)
private theorem coreShape :
    core = .letE (.var 1) (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1))) := by
  simp [core, Core.Expr.wordLt_expansion, Core.Expr.weakenAt]
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.wordLt (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) :=
  .less (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool :=
  .less (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (left right : Core.Word) :
    (inputs left right).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete (resolved left right)
    (.wordLt (.var (.tail ids_ne .head)) (.var .head))
    ((resolved left right).preserves_type (typed left right))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (decide (left < right))) store 11 :=
  .less (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_produce_independent_bool_typing_evaluation_and_exact_steps
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool ∧
    (inputs left right).check? source = some (core, .bool) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store source (.bool (decide (left < right))) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (decide (left < right))) store 11 ∧
    Core.Steps 11 (Core.State.initial core [.word right, .word left] store)
      (Core.State.final (.bool (decide (left < right))) store) :=
  ⟨typed left right, checked left right,
    .less (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head),
    costed left right store, (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds⟩

private def firstBinding (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.letBody (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1)))
    [.word right, .word left]], store⟩
private def secondBinding (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word right), [.letBody (.binary .wordGt (.var 0) (.var 1))
    [.word left, .word right, .word left]], store⟩
private def pending (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.binaryApply .wordGt (.word right)], store⟩

theorem exact_resolved_and_core_shapes_keep_original_children_and_ordered_generated_bindings
    (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.wordLt (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) ∧
    core = .letE (.var 1) (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1))) :=
  ⟨resolved left right, coreShape⟩

theorem genuine_checkpoints_retain_left_then_right_before_the_reversed_primitive
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 2 source store = some (.bool, .outOfFuel (firstBinding left right store)) ∧
    (inputs left right).run? 5 source store = some (.bool, .outOfFuel (secondBinding left right store)) ∧
    (inputs left right).run? 10 source store = some (.bool, .outOfFuel (pending left right store)) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [LocalInputs.run?, checked, coreShape] <;> rfl

theorem all_fuel_thresholds_count_eleven_steps_for_every_actual_word_pair
    (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    ((inputs left right).run? fuel source store =
      some (.bool, .done (.bool (decide (left < right))) store) ↔ 11 ≤ fuel) ∧
    ((∃ checkpoint, (inputs left right).run? fuel source store =
      some (.bool, .outOfFuel checkpoint)) ↔ fuel < 11) := by
  have path := (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds
  constructor
  · simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using path.runStateful_done_iff (fuel := fuel)
  · simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using path.runStateful_outOfFuel_iff (fuel := fuel)

theorem equal_strict_and_reverse_orders_never_return_word_flags
    (left right : Core.Word) (strict : left < right) (fuel : Nat) (store : Core.Store) :
    ((inputs left left).run? fuel source store = some (.bool, .done (.bool false) store) ↔ 11 ≤ fuel) ∧
    ((inputs left right).run? fuel source store = some (.bool, .done (.bool true) store) ↔ 11 ≤ fuel) ∧
    ((inputs right left).run? fuel source store = some (.bool, .done (.bool false) store) ↔ 11 ≤ fuel) ∧
    ∀ word, Core.Value.bool (decide (left < right)) ≠ .word word := by
  have reversed : ¬right < left := Nat.not_lt.mpr (Nat.le_of_lt strict)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (all_fuel_thresholds_count_eleven_steps_for_every_actual_word_pair left left store fuel).1
  · simpa [strict] using (all_fuel_thresholds_count_eleven_steps_for_every_actual_word_pair left right store fuel).1
  · simpa [reversed] using (all_fuel_thresholds_count_eleven_steps_for_every_actual_word_pair right left store fuel).1
  · intro word same; cases same

theorem zero_high_bit_and_maximum_distinguish_unsigned_order (store : Core.Store) :
    (inputs .zero (Core.Word.ofNatModulo (2 ^ 255))).run? 11 source store = some (.bool, .done (.bool true) store) ∧
    (inputs (Core.Word.ofNatModulo (2 ^ 255)) .zero).run? 11 source store = some (.bool, .done (.bool false) store) ∧
    (inputs (Core.Word.ofNatModulo (2 ^ 255)) .maximum).run? 11 source store = some (.bool, .done (.bool true) store) ∧
    (inputs .maximum (Core.Word.ofNatModulo (2 ^ 255))).run? 11 source store = some (.bool, .done (.bool false) store) ∧
    (inputs .maximum .maximum).run? 11 source store = some (.bool, .done (.bool false) store) := by
  have first := equal_strict_and_reverse_orders_never_return_word_flags
    .zero (Core.Word.ofNatModulo (2 ^ 255)) (by decide) 11 store
  have second := equal_strict_and_reverse_orders_never_return_word_flags
    (Core.Word.ofNatModulo (2 ^ 255)) .maximum (by decide) 11 store
  exact ⟨first.2.1.mpr (by decide), first.2.2.1.mpr (by decide),
    second.2.1.mpr (by decide), second.2.2.1.mpr (by decide),
    by simpa using (all_fuel_thresholds_count_eleven_steps_for_every_actual_word_pair .maximum .maximum store 11).1.mpr (by decide)⟩

theorem genuine_checkpoints_have_exact_residuals_and_same_state_resumption
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    Core.Steps 9 (firstBinding left right store) (Core.State.final (.bool (decide (left < right))) store) ∧
    Core.Steps 6 (secondBinding left right store) (Core.State.final (.bool (decide (left < right))) store) ∧
    Core.Steps 1 (pending left right store) (Core.State.final (.bool (decide (left < right))) store) ∧
    Core.runStateful 3 (firstBinding left right store) = .outOfFuel (secondBinding left right store) ∧
    (inputs left right).run? (5 + additional) source store =
      some (.bool, Core.runStateful additional (secondBinding left right store)) ∧
    (inputs left right).run? (10 + additional) source store =
      some (.bool, Core.runStateful additional (pending left right store)) := by
  have first : Core.runStateful 2 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (firstBinding left right store) := by rw [coreShape]; rfl
  have second : Core.runStateful 5 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (secondBinding left right store) := by rw [coreShape]; rfl
  have last : Core.runStateful 10 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (pending left right store) := by rw [coreShape]; rfl
  have firstResidual := (costed left right store).checked_residual_of_outOfFuel
    (checked left right) (inputs left right).sameIds first
  have secondResidual := (costed left right store).checked_residual_of_outOfFuel
    (checked left right) (inputs left right).sameIds second
  have lastResidual := (costed left right store).checked_residual_of_outOfFuel
    (checked left right) (inputs left right).sameIds last
  have checkpoints := genuine_checkpoints_retain_left_then_right_before_the_reversed_primitive left right store
  exact ⟨firstResidual.2, secondResidual.2, lastResidual.2, rfl,
    LocalInputs.run?_resume checkpoints.2.1 additional, LocalInputs.run?_resume checkpoints.2.2 additional⟩

theorem independent_less_requires_both_ordered_word_operands
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (less left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .bool (decide (leftWord < rightWord)) ∧ cost = leftCost + rightCost + 9 := by
  cases evaluation with
  | less leftEvaluation rightEvaluation => exact ⟨_, _, _, _, _, leftEvaluation, rightEvaluation, rfl, rfl⟩

theorem missing_either_operand_is_not_bypassed_by_equal_known_values :
    (inputs .zero .zero).check? (less (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (less (ref "missing") (ref "r")) = none := by
  constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, less, ref,
    inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

private def typedInputs (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" leftType left leftTyped).bindFresh owner "r" rightType right rightTyped

theorem non_word_on_either_side_is_rejected_without_polymorphic_less
    (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType)
    (wrong : leftType ≠ .word ∨ rightType ≠ .word) (fuel : Nat) (store : Core.Store) :
    (typedInputs leftType rightType left right leftTyped rightTyped).check? source = none ∧
    (typedInputs leftType rightType left right leftTyped rightTyped).run? fuel source store = none := by
  have rejected : (typedInputs leftType rightType left right leftTyped rightTyped).check? source = none := by
    cases accepted : (typedInputs leftType rightType left right leftTyped rightTyped).check? source with
    | none => rfl
    | some result =>
      rcases result with ⟨compiledCore, resultType⟩
      have whole := LocalInputs.check?_iff_hasType.mp ⟨compiledCore, accepted⟩
      cases whole with
      | less first second =>
        have firstTyped : LocalExpressionHasType
            (typedInputs leftType rightType left right leftTyped rightTyped).names
            (typedInputs leftType rightType left right leftTyped rightTyped).context (ref "l") leftType :=
          .identifier (.tail names_ne .head) (.tail ids_ne .head)
        have secondTyped : LocalExpressionHasType
            (typedInputs leftType rightType left right leftTyped rightTyped).names
            (typedInputs leftType rightType left right leftTyped rightTyped).context (ref "r") rightType :=
          .identifier .head .head
        exact False.elim (wrong.elim (fun mismatch => mismatch (firstTyped.type_unique first))
          (fun mismatch => mismatch (secondTyped.type_unique second)))
  exact ⟨rejected, (LocalInputs.run?_eq_none_iff fuel store).mpr rejected⟩

theorem less_preserves_unrelated_inputs_and_ignores_only_spans_and_injective_ids
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store)
    (otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    ((inputs left right).mapIds mapping injective).run? fuel source store =
      (inputs left right).run? fuel source store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store source (.bool (decide (left < right))) store 11 ∧
    resolveLocalExpression? (inputs left right).names source = resolveLocalExpression? (inputs left right).names
      ⟨otherSpan, .binary (ref "l") ⟨otherOperatorSpan, .less⟩ (ref "r")⟩ := by
  have avoids : AvoidsLocalName "unused" source := .less (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel source store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed left right store),
    resolveLocalExpression?_less_spans _ _ _ _ _ _ _⟩

theorem arbitrary_identity_maps_preserve_structural_resolution_without_fresh_names
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId) :
    ResolvesLocalExpression (LocalNameTable.mapIds mapping (inputs left right).names) source
      (.wordLt (.var (mapping ⟨owner, 0⟩)) (.var (mapping ⟨owner, 1⟩))) := by
  simpa only [Resolved.Expr.renameIds] using (resolved left right).mapIds mapping

theorem replay_structural_budget_and_type_erasure_preserve_the_source_contract
    (left right : Core.Word) (first replacement : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      replacement source (.bool (decide (left < right))) replacement 11 ∧
    11 ≤ localExpressionFuelBound source ∧ localExpressionFuelBound source = 11 ∧
    (inputs left right).toTypeInputs.names = (inputs left right).names ∧
    (inputs left right).toTypeInputs.context = (inputs left right).context := by
  have replayed := (costed left right first).change_store replacement
  exact ⟨replayed, replayed.cost_le_fuelBound, by simp [source, less, ref, localExpressionFuelBound],
    (inputs left right).toTypeInputs_names, (inputs left right).toTypeInputs_context⟩

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation "Word")⟩
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def declaration (returnName : String) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "less"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation returnName]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some source)⟩]⟩⟩⟩
private def compiled : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word, core, .bool⟩
private theorem wordAnnotation : TypeNameDenotes types (annotation "Word") .word :=
  .named (.tail (by decide) .head)
private theorem compilation : RuntimeFunctionCompiles types owner (declaration "Bool") compiled :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons wordAnnotation.structural (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons wordAnnotation.structural (by change "r" ∉ ["l"]; simp) .nil),
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.less (.identifier (.tail names_ne .head)) (.identifier .head))
      (.wordLt (.var (.tail ids_ne .head)) (.var .head))
      (.wordLt (.var (.tail ids_ne .head)) (.var .head))⟩
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ :=
  ⟨compilation.header,
    .cons wordAnnotation.structural (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons wordAnnotation.structural (by change "r" ∉ ["l"]; simp) .nil), compilation.body⟩

theorem independent_compilation_preparation_and_exact_bool_entry_cost
    (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionCompiles types owner (declaration "Bool") compiled ∧
    compileRuntimeFunction? types owner (declaration "Bool") = some compiled ∧
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ ∧
    RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (decide (left < right))) store 11 ∧
    ∀ fuel, (runRuntimeFunction? types owner (declaration "Bool") (arguments left right) fuel store =
      some (.bool, .done (.bool (decide (left < right))) store) ↔ 11 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (decide (left < right))) store 11 :=
    .intro (preparation left right) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (costed left right store))
  exact ⟨compilation, compilation.complete, preparation left right, evaluation, fun _ => evaluation.run_done_iff⟩

theorem declared_word_return_rejects_a_bool_less_result :
    compileRuntimeFunction? types owner (declaration "Word") = none := by
  apply compileRuntimeFunction?_eq_none_iff.mpr
  intro ⟨candidate, accepted⟩
  have sameInputs : candidate.inputs = compiled.inputs := accepted.parameters.result_unique compilation.parameters
  have expectedHeader : RuntimeFunctionHeader types (declaration "Word").value.signature .word :=
    ⟨rfl, rfl, rfl, rfl, .single wordAnnotation.structural⟩
  have sameReturn : candidate.returnType = .word := accepted.header.type_unique expectedHeader
  have candidateBody := accepted.body
  rw [sameInputs] at candidateBody
  have bodyReturn : candidate.returnType = .bool := (candidateBody.result_unique compilation.body).2
  cases sameReturn.symm.trans bodyReturn

end Tests.FrontendWordLess
end

section
-- leanmerge: from Solcore.Test.FrontendWordLiteralProperties
/-! ADR-0162 consumers: complete ASCII spellings have independent natural
meanings and strict Word bounds do not wrap. These tests do not require an
expression adapter; its integration is tested in FrontendLocalWordLiteralProperties. -/

set_option autoImplicit false

namespace Tests.FrontendWordLiteral

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "word-literals.sol"⟩, 0, 1⟩
private def literal (payload : Syntax.CoreLiteralValue) : Syntax.CoreLiteral := ⟨span, payload⟩
private def fortyTwo : Core.Word := ⟨42, by decide⟩
private def one : Core.Word := ⟨1, by decide⟩

private theorem decimalMeaning : NumericLiteralDenotes (.decimal "42") 42 :=
  .decimal (by decide)
    (.cons (.decimal (digit := 4) (by decide) (by decide))
      (.cons (.decimal (digit := 2) (by decide) (by decide)) .nil))
private theorem lowerHexMeaning : NumericLiteralDenotes (.hexadecimal "0x2a") 42 :=
  .hexadecimal rfl (by decide)
    (.cons (.decimal (digit := 2) (by decide) (by decide))
      (.cons (.hexLower (digit := 10) (by decide) (by decide) (by decide)) .nil))
private theorem upperHexMeaning : NumericLiteralDenotes (.hexadecimal "0x2A") 42 :=
  .hexadecimal rfl (by decide)
    (.cons (.decimal (digit := 2) (by decide) (by decide))
      (.cons (.hexUpper (digit := 10) (by decide) (by decide) (by decide)) .nil))

theorem decimal_and_both_hex_cases_have_the_same_independent_value :
    NumericLiteralDenotes (.decimal "42") 42 ∧
    NumericLiteralDenotes (.hexadecimal "0x2a") 42 ∧
    NumericLiteralDenotes (.hexadecimal "0x2A") 42 ∧
    interpretWordLiteral? (literal (.decimal "42")) = some fortyTwo ∧
    interpretWordLiteral? (literal (.hexadecimal "0x2a")) = some fortyTwo ∧
    interpretWordLiteral? (literal (.hexadecimal "0x2A")) = some fortyTwo ∧
    fortyTwo.val = 42 :=
  ⟨decimalMeaning, lowerHexMeaning, upperHexMeaning,
    interpretWordLiteral?_complete decimalMeaning,
    interpretWordLiteral?_complete lowerHexMeaning,
    interpretWordLiteral?_complete upperHexMeaning, rfl⟩

private def paddedDecimal (count : Nat) : Syntax.CoreLiteralValue :=
  .decimal (String.ofList (List.replicate count '0' ++ ['1']))
private def paddedHex (count : Nat) : Syntax.CoreLiteralValue :=
  .hexadecimal (String.ofList ('0' :: 'x' :: (List.replicate count '0' ++ ['1'])))
private theorem oneDigits (radix : NumericRadix) : NumericDigitsDenote radix ['1'] 0 1 := by
  simpa only [Nat.mul_zero, Nat.zero_add] using
    (NumericDigitsDenote.cons (initial := 0)
      (NumericDigitDenotes.decimal (radix := radix) (digit := 1) (by decide) (by decide)) .nil)
private theorem paddedDecimalMeaning (count : Nat) : NumericLiteralDenotes (paddedDecimal count) 1 := by
  apply NumericLiteralDenotes.decimal
  · simp
  · simpa using (oneDigits .decimal).leading_zeros count
private theorem paddedHexMeaning (count : Nat) : NumericLiteralDenotes (paddedHex count) 1 := by
  apply NumericLiteralDenotes.hexadecimal (characters := List.replicate count '0' ++ ['1'])
  · simp
  · simp
  · exact (oneDigits .hexadecimal).leading_zeros count

theorem arbitrarily_many_leading_zeroes_preserve_exact_value (count : Nat) :
    NumericLiteralDenotes (paddedDecimal count) 1 ∧
    NumericLiteralDenotes (paddedHex count) 1 ∧
    numericLiteralValue? (paddedDecimal count) = some 1 ∧
    numericLiteralValue? (paddedHex count) = some 1 ∧
    interpretWordLiteral? (literal (paddedDecimal count)) = some one ∧
    interpretWordLiteral? (literal (paddedHex count)) = some one :=
  ⟨paddedDecimalMeaning count, paddedHexMeaning count,
    numericLiteralValue?_complete (paddedDecimalMeaning count),
    numericLiteralValue?_complete (paddedHexMeaning count),
    interpretWordLiteral?_complete (paddedDecimalMeaning count),
    interpretWordLiteral?_complete (paddedHexMeaning count)⟩

private def decimalMaximum : Syntax.CoreLiteralValue :=
  .decimal "115792089237316195423570985008687907853269984665640564039457584007913129639935"
private def hexMaximum : Syntax.CoreLiteralValue :=
  .hexadecimal "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
private def decimalOverflow : Syntax.CoreLiteralValue :=
  .decimal "115792089237316195423570985008687907853269984665640564039457584007913129639936"
private def hexOverflow : Syntax.CoreLiteralValue :=
  .hexadecimal "0x10000000000000000000000000000000000000000000000000000000000000000"

theorem zero_one_and_maximum_are_accepted_without_reduction :
    interpretWordLiteral? (literal (.decimal "0")) = some Core.Word.zero ∧
    interpretWordLiteral? (literal (.hexadecimal "0x0")) = some Core.Word.zero ∧
    interpretWordLiteral? (literal (.decimal "1")) = some one ∧
    interpretWordLiteral? (literal (.hexadecimal "0x1")) = some one ∧
    interpretWordLiteral? (literal decimalMaximum) = some Core.Word.maximum ∧
    interpretWordLiteral? (literal hexMaximum) = some Core.Word.maximum ∧
    WordLiteralDenotes (literal decimalMaximum) Core.Word.maximum ∧
    WordLiteralDenotes (literal hexMaximum) Core.Word.maximum := by
  have decimal : interpretWordLiteral? (literal decimalMaximum) = some Core.Word.maximum := by decide
  have hexadecimal : interpretWordLiteral? (literal hexMaximum) = some Core.Word.maximum := by decide
  exact ⟨by decide, by decide, by decide, by decide, decimal, hexadecimal,
    interpretWordLiteral?_sound decimal, interpretWordLiteral?_sound hexadecimal⟩

theorem modulus_has_a_natural_meaning_but_no_word_meaning :
    numericLiteralValue? decimalOverflow = some Core.wordModulus ∧
    numericLiteralValue? hexOverflow = some Core.wordModulus ∧
    NumericLiteralDenotes decimalOverflow Core.wordModulus ∧
    NumericLiteralDenotes hexOverflow Core.wordModulus ∧
    interpretWordLiteral? (literal decimalOverflow) = none ∧
    interpretWordLiteral? (literal hexOverflow) = none ∧
    interpretWordLiteralModulo? (literal decimalOverflow) = some Core.Word.zero ∧
    interpretWordLiteralModulo? (literal hexOverflow) = some Core.Word.zero ∧
    (¬ ∃ word, WordLiteralDenotes (literal decimalOverflow) word) ∧
    (¬ ∃ word, WordLiteralDenotes (literal hexOverflow) word) := by
  have decimal : numericLiteralValue? decimalOverflow = some Core.wordModulus := by decide
  have hexadecimal : numericLiteralValue? hexOverflow = some Core.wordModulus := by decide
  have decimalMeaning := numericLiteralValue?_sound decimal
  have hexMeaning := numericLiteralValue?_sound hexadecimal
  have decimalRejected : interpretWordLiteral? (literal decimalOverflow) = none :=
    interpretWordLiteral?_eq_none_of_out_of_range decimalMeaning (Nat.le_refl _)
  have hexRejected : interpretWordLiteral? (literal hexOverflow) = none :=
    interpretWordLiteral?_eq_none_of_out_of_range hexMeaning (Nat.le_refl _)
  have modulusWraps :
      Core.Word.ofNatModulo Core.wordModulus = Core.Word.zero := by
    apply Fin.ext
    simp [Core.Word.ofNatModulo, Core.Word.zero]
  have decimalModulo :
      interpretWordLiteralModulo? (literal decimalOverflow) =
        some Core.Word.zero := by
    apply interpretWordLiteralModulo?_complete
    exact ⟨Core.wordModulus, decimalMeaning, modulusWraps⟩
  have hexModulo :
      interpretWordLiteralModulo? (literal hexOverflow) =
        some Core.Word.zero := by
    apply interpretWordLiteralModulo?_complete
    exact ⟨Core.wordModulus, hexMeaning, modulusWraps⟩
  refine ⟨decimal, hexadecimal, decimalMeaning, hexMeaning, decimalRejected,
    hexRejected, decimalModulo, hexModulo, ?_, ?_⟩
  · rintro ⟨word, meaning⟩
    have impossible := interpretWordLiteral?_complete meaning
    rw [decimalRejected] at impossible
    cases impossible
  · rintro ⟨word, meaning⟩
    have impossible := interpretWordLiteral?_complete meaning
    rw [hexRejected] at impossible
    cases impossible

private def malformed : List Syntax.CoreLiteralValue :=
  [.decimal "", .decimal "+", .decimal "-1", .decimal "+1", .decimal " 1", .decimal "1 ",
   .decimal "1_000", .decimal "１", .decimal "١", .decimal "1.0", .decimal "12x", .decimal "0x1",
   .hexadecimal "", .hexadecimal "0x", .hexadecimal "0X", .hexadecimal "0X1", .hexadecimal "0x+1",
   .hexadecimal "0x 1", .hexadecimal "0x1_0", .hexadecimal "0xＦ", .hexadecimal "0x1g",
   .hexadecimal "12", .hexadecimal "0x1.0", .string "123", .string "0x1"]

theorem malformed_payloads_have_no_numeric_or_word_meaning
    (payload : Syntax.CoreLiteralValue) (present : payload ∈ malformed) (location : Syntax.SourceSpan) :
    numericLiteralValue? payload = none ∧
    (¬ ∃ value, NumericLiteralDenotes payload value) ∧
    interpretWordLiteral? ⟨location, payload⟩ = none ∧
    interpretWordLiteralModulo? ⟨location, payload⟩ = none ∧
    ¬ ∃ word, WordLiteralDenotes ⟨location, payload⟩ word := by
  have allRejected : ∀ candidate ∈ malformed, numericLiteralValue? candidate = none := by decide
  have rejected := allRejected payload present
  have wordRejected : interpretWordLiteral? ⟨location, payload⟩ = none := by
    simp [interpretWordLiteral?, rejected]
  have moduloRejected :
      interpretWordLiteralModulo? ⟨location, payload⟩ = none := by
    simp [interpretWordLiteralModulo?, rejected]
  refine ⟨rejected, numericLiteralValue?_eq_none_iff.mp rejected, wordRejected,
    moduloRejected, ?_⟩
  rintro ⟨word, meaning⟩
  have impossible := interpretWordLiteral?_complete meaning
  rw [wordRejected] at impossible
  cases impossible

theorem span_changes_do_not_change_interpretation_or_independent_meaning
    (payload : Syntax.CoreLiteralValue) (location otherLocation : Syntax.SourceSpan) (word : Core.Word) :
    interpretWordLiteral? ⟨location, payload⟩ = interpretWordLiteral? ⟨otherLocation, payload⟩ ∧
    (WordLiteralDenotes ⟨location, payload⟩ word ↔ WordLiteralDenotes ⟨otherLocation, payload⟩ word) ∧
    interpretWordLiteralModulo? ⟨location, payload⟩ =
      interpretWordLiteralModulo? ⟨otherLocation, payload⟩ ∧
    (ModuloWordLiteralDenotes ⟨location, payload⟩ word ↔
      ModuloWordLiteralDenotes ⟨otherLocation, payload⟩ word) :=
  ⟨interpretWordLiteral?_span payload location otherLocation,
    wordLiteralDenotes_span payload location otherLocation word,
    interpretWordLiteralModulo?_span payload location otherLocation,
    moduloWordLiteralDenotes_span payload location otherLocation word⟩

end Tests.FrontendWordLiteral
end
