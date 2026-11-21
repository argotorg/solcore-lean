import Solcore.Frontend.SourceCore.Compatible
import Solcore.SourceSemantics.Dynamic.Fault
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Equality
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.AssignmentProfiles

/-!
# Foundations: compound assignments at fixed-width targets

The modifier that both place compilers emit for `+= -= *= /= %=`, their unchecked forms and
`&= |= ^=` at the twelve fixed-width integer types, beside the source rules on the same operands,
and the profile that admits them beside `AssignmentProfile`. The data and compatible place pipelines
use them. `<<=` and `>>=` there have the same facts, for an amount of any word, and so does in-place
`~` there, with its own profile beside `AssignmentProfile`'s.

Main declarations:
- `FixedCompoundAssignment` and `WideAssignmentProfile`, the profile with these targets, and
  `decidableFixedCompoundAssignment`, its check;
- `leaf`, the word Core's modifier computes, and `modified_evaluates` and
  `compatible_modified_evaluates`, its evaluation in each place compiler;
- `applies_leaf`, an applied source operation gives that word;
- `Agreement` and `guard_agrees`: the modifier's check after the setter writes exactly when the
  source applies the operation, and otherwise fails with the source's panic;
- `canonical_of_applies`, an applied result is canonical for the type;
- `shift_leaf_evaluates`, `shift_applies_leaf`, `shift_canonical_of_applies` and
  `shift_guard_agrees`, the same facts for the shifts, which ask nothing of the amount;
- `WideBitNotProfile`, in-place `~`'s profile with these targets, and `bitNotLeaf`,
  `bitNot_modified_evaluates`, `bitNot_applies_leaf`, `bitNot_applies` and `bitNot_canonical`, its
  leaf and the source's rule on it.
-/

section
/-! Word arithmetic. Core's operations are taken modulo `2^256`, the source's on the integers a
type reads its words as (`Dynamic.fixedValue`), so the two agree modulo `2^256`; the wrap of a
leaf keeps its low `N` bits, as `Dynamic.fixedWrap` does. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.FixedCompoundModifier
open Core Frontend

theorem ofIntModulo_val (value : Int) :
    ((Word.ofIntModulo value).val : Int) = value % (wordModulus : Int) := by
  cases value with
  | ofNat n =>
    simp only [Word.ofIntModulo, Word.ofNatModulo, Int.ofNat_eq_natCast, wordModulus, Nat.reducePow]
    omega
  | negSucc n =>
    simp only [Word.ofIntModulo, Word.ofNatModulo, Int.negSucc_eq, wordModulus, Nat.reducePow]
    omega

theorem fixedValue_emod (type : TypeSystem.FixedInteger) (word : Word) :
    Dynamic.fixedValue type word % (wordModulus : Int) = (word.val : Int) := by
  have bound := word.isLt
  simp only [wordModulus, Nat.reducePow] at bound ⊢
  unfold Dynamic.fixedValue Dynamic.wordSigned
  simp only [Nat.reducePow, Int.reducePow]
  split <;> (try split) <;> omega

theorem ofIntModulo_congr {left right : Int}
    (same : left % (wordModulus : Int) = right % (wordModulus : Int)) :
    Word.ofIntModulo left = Word.ofIntModulo right := by
  apply Fin.ext
  have values : ((Word.ofIntModulo left).val : Int) = ((Word.ofIntModulo right).val : Int) := by
    rw [ofIntModulo_val, ofIntModulo_val, same]
  exact_mod_cast values

theorem ofIntModulo_fixedValue (type : TypeSystem.FixedInteger) (word : Word) :
    Word.ofIntModulo (Dynamic.fixedValue type word) = word := by
  apply Fin.ext
  have value := ofIntModulo_val (Dynamic.fixedValue type word)
  rw [fixedValue_emod] at value
  exact_mod_cast value

theorem add_fixed (type : TypeSystem.FixedInteger) (left right : Word) :
    left.add right = Word.ofIntModulo (Dynamic.fixedValue type left + Dynamic.fixedValue type right) := by
  apply Fin.ext
  have value := ofIntModulo_val (Dynamic.fixedValue type left + Dynamic.fixedValue type right)
  rw [Int.add_emod, fixedValue_emod, fixedValue_emod] at value
  have sum : ((left.add right).val : Int) = ((left.val : Int) + right.val) % (wordModulus : Int) := by
    simp only [Word.add, Fin.val_add]
    push_cast
    rfl
  exact_mod_cast sum.trans value.symm

theorem sub_fixed (type : TypeSystem.FixedInteger) (left right : Word) :
    left.sub right = Word.ofIntModulo (Dynamic.fixedValue type left - Dynamic.fixedValue type right) := by
  apply Fin.ext
  have value := ofIntModulo_val (Dynamic.fixedValue type left - Dynamic.fixedValue type right)
  rw [Int.sub_emod, fixedValue_emod, fixedValue_emod] at value
  have leftBound := left.isLt
  have rightBound := right.isLt
  have difference : (left.sub right).val = (wordModulus - right.val + left.val) % wordModulus := by
    simp only [Word.sub, Fin.sub_def]
  simp only [wordModulus, Nat.reducePow] at value leftBound rightBound difference
  omega

theorem mul_fixed (type : TypeSystem.FixedInteger) (left right : Word) :
    left.mul right = Word.ofIntModulo (Dynamic.fixedValue type left * Dynamic.fixedValue type right) := by
  apply Fin.ext
  have value := ofIntModulo_val (Dynamic.fixedValue type left * Dynamic.fixedValue type right)
  rw [Int.mul_emod, fixedValue_emod, fixedValue_emod] at value
  have product : ((left.mul right).val : Int) = ((left.val : Int) * right.val) % (wordModulus : Int) := by
    simp only [Word.mul, Fin.val_mul]
    push_cast
    rfl
  exact_mod_cast product.trans value.symm

private theorem nonzero_val {word : Word} (nonzero : word ≠ Word.zero) : word.val ≠ 0 :=
  fun same => nonzero (Fin.ext same)

private theorem ofIntModulo_natCast (value : Nat) : Word.ofIntModulo (value : Int) = Word.ofNatModulo value :=
  rfl

private theorem ofNatModulo_val {value : Nat} (small : value < wordModulus) : (Word.ofNatModulo value).val = value :=
  Nat.mod_eq_of_lt small

theorem udiv_unsigned {left right : Word} (nonzero : right ≠ Word.zero) :
    left.udiv right = Word.ofIntModulo ((left.val : Int).tdiv right.val) := by
  rw [← Int.ofNat_tdiv, ofIntModulo_natCast]
  apply Fin.ext
  have small : left.val / right.val < wordModulus := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) left.isLt
  rw [ofNatModulo_val small]
  simp only [Word.udiv, nonzero_val nonzero, if_false]
  rfl

theorem umod_unsigned {left right : Word} (nonzero : right ≠ Word.zero) :
    left.umod right = Word.ofIntModulo ((left.val : Int).tmod right.val) := by
  rw [← Int.ofNat_tmod, ofIntModulo_natCast]
  apply Fin.ext
  have small : left.val % right.val < wordModulus := Nat.lt_of_le_of_lt (Nat.mod_le _ _) left.isLt
  rw [ofNatModulo_val small]
  simp only [Word.umod, nonzero_val nonzero, if_false, Fin.val_mod]

private theorem signedMagnitude_le (word : Word) : word.signedMagnitude ≤ wordModulus := by
  have bound := word.isLt
  unfold Word.signedMagnitude
  split <;> omega

private theorem wordSigned_eq (word : Word) :
    Dynamic.wordSigned word =
      if word.signedNegative then -(word.signedMagnitude : Int) else (word.signedMagnitude : Int) := by
  have bound := word.isLt
  unfold Dynamic.wordSigned Word.signedMagnitude Word.signedNegative
  by_cases small : word.val < 2 ^ 255
  · have notNegative : decide (2 ^ 255 ≤ word.val) = false := by simp only [decide_eq_false_iff_not]; omega
    simp only [small, notNegative, if_true, Bool.false_eq_true, if_false]
  · have negative : decide (2 ^ 255 ≤ word.val) = true := by simp only [decide_eq_true_eq]; omega
    simp only [small, negative, if_true, if_false]
    simp only [wordModulus, Nat.reducePow] at bound ⊢
    omega

private theorem ofSignedMagnitude_eq (negative : Bool) {magnitude : Nat} (bound : magnitude ≤ wordModulus) :
    Word.ofSignedMagnitude negative magnitude =
      Word.ofIntModulo (if negative then -(magnitude : Int) else (magnitude : Int)) := by
  cases negative
  · rfl
  · apply Fin.ext
    have value := ofIntModulo_val (-(magnitude : Int))
    simp only [Word.ofSignedMagnitude, if_true, Word.ofNatModulo]
    simp only [wordModulus, Nat.reducePow] at value bound ⊢
    omega

private theorem tdiv_signs (a b : Nat) (signA signB : Bool) :
    Int.tdiv (if signA then -(a : Int) else (a : Int)) (if signB then -(b : Int) else (b : Int)) =
      if (signA != signB) then -((a / b : Nat) : Int) else ((a / b : Nat) : Int) := by
  cases signA <;> cases signB <;> simp [Int.neg_tdiv, Int.tdiv_neg]

private theorem tmod_signs (a b : Nat) (signA signB : Bool) :
    Int.tmod (if signA then -(a : Int) else (a : Int)) (if signB then -(b : Int) else (b : Int)) =
      if signA then -((a % b : Nat) : Int) else ((a % b : Nat) : Int) := by
  cases signA <;> cases signB <;> simp [Int.neg_tmod, Int.tmod_neg, ← Int.ofNat_tmod]

theorem sdiv_signed {left right : Word} (nonzero : right ≠ Word.zero) :
    left.sdiv right = Word.ofIntModulo ((Dynamic.wordSigned left).tdiv (Dynamic.wordSigned right)) := by
  rw [wordSigned_eq left, wordSigned_eq right, tdiv_signs]
  unfold Word.sdiv
  rw [if_neg (nonzero_val nonzero)]
  exact ofSignedMagnitude_eq _ (Nat.le_trans (Nat.div_le_self _ _) (signedMagnitude_le left))

theorem smod_signed {left right : Word} (nonzero : right ≠ Word.zero) :
    left.smod right = Word.ofIntModulo ((Dynamic.wordSigned left).tmod (Dynamic.wordSigned right)) := by
  rw [wordSigned_eq left, wordSigned_eq right, tmod_signs]
  unfold Word.smod
  rw [if_neg (nonzero_val nonzero)]
  exact ofSignedMagnitude_eq _ (Nat.le_trans (Nat.mod_le _ _) (signedMagnitude_le left))

/-- Word's division at a fixed-width type, by a nonzero divisor, is the word of the quotient
rounded toward zero. -/
theorem divide_fixed (type : TypeSystem.FixedInteger) {left right : Word} (nonzero : right ≠ Word.zero) :
    (if type.signed then left.sdiv right else left.udiv right) =
      Word.ofIntModulo ((Dynamic.fixedValue type left).tdiv (Dynamic.fixedValue type right)) := by
  unfold Dynamic.fixedValue
  cases type.signed
  · exact udiv_unsigned nonzero
  · exact sdiv_signed nonzero

/-- And its remainder is the word of the remainder with the dividend's sign. -/
theorem modulo_fixed (type : TypeSystem.FixedInteger) {left right : Word} (nonzero : right ≠ Word.zero) :
    (if type.signed then left.smod right else left.umod right) =
      Word.ofIntModulo ((Dynamic.fixedValue type left).tmod (Dynamic.fixedValue type right)) := by
  unfold Dynamic.fixedValue
  cases type.signed
  · exact umod_unsigned nonzero
  · exact smod_signed nonzero

/-- The word `SourceCoreDataPlaces.wrapLeaf` gives at a fixed-width type: the low `N` bits of a
word, sign-extended on a signed type. -/
def wrapWord (type : TypeSystem.FixedInteger) (word : Word) : Word :=
  if type.signed then (Word.ofNatModulo (type.width.bits / 8 - 1)).signExtend word
  else word.bitAnd (Word.ofNatModulo (2 ^ type.width.bits - 1))

private theorem bitAnd_mask (word : Word) {bits : Nat} (small : bits ≤ 256) :
    (word.bitAnd (Word.ofNatModulo (2 ^ bits - 1))).val = word.val % 2 ^ bits := by
  have below : 2 ^ bits ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) small
  have positive := Nat.two_pow_pos bits
  have mask : (Word.ofNatModulo (2 ^ bits - 1)).val = 2 ^ bits - 1 :=
    ofNatModulo_val (by unfold wordModulus; omega)
  simp only [Word.bitAnd, Fin.and_val, mask, Nat.and_two_pow_sub_one_eq_mod]

private theorem signExtend_val (word : Word) {index : Nat} (small : index < 32) :
    ((Word.ofNatModulo index).signExtend word).val =
      if word.val % 2 ^ (8 * (index + 1)) < 2 ^ (8 * (index + 1) - 1) then word.val % 2 ^ (8 * (index + 1))
      else wordModulus - 2 ^ (8 * (index + 1)) + word.val % 2 ^ (8 * (index + 1)) := by
  have indexValue : (Word.ofNatModulo index).val = index := ofNatModulo_val (by unfold wordModulus; omega)
  have below : 2 ^ (8 * (index + 1)) ≤ wordModulus := Nat.pow_le_pow_right (by decide) (by omega)
  have low := Nat.mod_lt word.val (Nat.two_pow_pos (8 * (index + 1)))
  unfold Word.signExtend
  simp only [indexValue, small, if_true]
  generalize 2 ^ (8 * (index + 1)) = width at below low ⊢
  split
  · exact ofNatModulo_val (by omega)
  · exact ofNatModulo_val (by omega)

theorem wrapWord_fixed (type : TypeSystem.FixedInteger) (word : Word) :
    wrapWord type word = Word.ofIntModulo (Dynamic.fixedWrap type (Dynamic.fixedValue type word)) := by
  apply Fin.ext
  apply Int.natCast_inj.mp
  rw [ofIntModulo_val]
  have bound := word.isLt
  obtain ⟨signed, width⟩ := type
  cases signed
  · have mask := bitAnd_mask word (TypeSystem.IntegerWidth.bits_le width)
    simp only [wrapWord, Bool.false_eq_true, if_false] at mask ⊢
    rw [mask]
    unfold Dynamic.fixedWrap Dynamic.fixedValue
    simp only [Bool.false_eq_true, if_false]
    generalize word.val = n at bound ⊢
    cases width <;> simp only [TypeSystem.IntegerWidth.bits, wordModulus, Nat.reducePow] at bound ⊢ <;> omega
  · have small : width.bits / 8 - 1 < 32 := by cases width <;> decide
    simp only [wrapWord, if_true]
    rw [signExtend_val word small]
    unfold Dynamic.fixedWrap Dynamic.fixedValue Dynamic.wordSigned
    simp only [if_true]
    generalize word.val = n at bound ⊢
    by_cases low : n % 2 ^ (8 * (width.bits / 8 - 1 + 1)) < 2 ^ (8 * (width.bits / 8 - 1 + 1) - 1) <;>
      by_cases positive : n < 2 ^ 255 <;>
      simp only [low, positive, if_true, if_false] <;>
      cases width <;>
      simp only [TypeSystem.IntegerWidth.bits, wordModulus, Nat.reducePow, Nat.reduceDiv, Nat.reduceSub,
        Nat.reduceAdd, Nat.reduceMul, Int.reducePow] at bound low positive ⊢ <;>
      omega

theorem fixedWrap_congr (type : TypeSystem.FixedInteger) {left right : Int}
    (same : left % (wordModulus : Int) = right % (wordModulus : Int)) :
    Dynamic.fixedWrap type left = Dynamic.fixedWrap type right := by
  obtain ⟨signed, width⟩ := type
  simp only [wordModulus, Nat.reducePow] at same
  cases signed <;> cases width <;>
    simp only [Dynamic.fixedWrap, TypeSystem.IntegerWidth.bits, Bool.false_eq_true, if_false, if_true,
      Nat.reducePow, Nat.reduceSub] <;>
    omega

/-- The wrap of a word given modulo `2^256` is the type's wrap of the integer. -/
theorem wrap_ofIntModulo (type : TypeSystem.FixedInteger) (value : Int) :
    wrapWord type (Word.ofIntModulo value) = Word.ofIntModulo (Dynamic.fixedWrap type value) := by
  rw [wrapWord_fixed]
  congr 1
  apply fixedWrap_congr
  rw [fixedValue_emod, ofIntModulo_val]

/-- The canonical words of a type, as a proposition. -/
theorem canonical_true_iff (type : TypeSystem.FixedInteger) (value : Nat) :
    type.canonical value = true ↔
      (if type.signed then value < 2 ^ (type.width.bits - 1) ∨ 2 ^ 256 - 2 ^ (type.width.bits - 1) ≤ value
       else value < 2 ^ type.width.bits) := by
  unfold TypeSystem.FixedInteger.canonical
  split <;> simp

/-- A word of an integer in the type's range is canonical for the type. -/
theorem canonical_ofIntModulo {type : TypeSystem.FixedInteger} {value : Int}
    (inRange : Dynamic.FixedInRange type value) : type.canonical (Word.ofIntModulo value).val = true := by
  have word := ofIntModulo_val value
  rw [canonical_true_iff]
  generalize (Word.ofIntModulo value).val = n at word ⊢
  obtain ⟨signed, width⟩ := type
  cases signed <;> cases width <;>
    simp only [Dynamic.FixedInRange, TypeSystem.FixedInteger.min, TypeSystem.FixedInteger.max,
      TypeSystem.IntegerWidth.bits, Bool.false_eq_true, if_false, if_true, wordModulus, Nat.reducePow,
      Nat.reduceSub] at inRange word ⊢ <;>
    omega

private theorem canonical_signed_iff (width : TypeSystem.IntegerWidth) {value : Nat} (bound : value < wordModulus) :
    TypeSystem.FixedInteger.canonical ⟨true, width⟩ value = true ↔
      (value / 2 ^ (width.bits - 1) = 0 ∨ value / 2 ^ (width.bits - 1) = 2 ^ (257 - width.bits) - 1) := by
  rw [canonical_true_iff]
  simp only [if_true]
  simp only [wordModulus, Nat.reducePow] at bound
  cases width <;> simp only [TypeSystem.IntegerWidth.bits, Nat.reducePow, Nat.reduceSub] <;> omega

private theorem top_and {a b top : Nat} (first : a = 0 ∨ a = top) (second : b = 0 ∨ b = top) :
    a &&& b = 0 ∨ a &&& b = top := by
  rcases first with rfl | rfl <;> rcases second with rfl | rfl <;> simp [Nat.and_self]

private theorem top_or {a b top : Nat} (first : a = 0 ∨ a = top) (second : b = 0 ∨ b = top) :
    a ||| b = 0 ∨ a ||| b = top := by
  rcases first with rfl | rfl <;> rcases second with rfl | rfl <;> simp [Nat.or_self]

private theorem top_xor {a b top : Nat} (first : a = 0 ∨ a = top) (second : b = 0 ∨ b = top) :
    a ^^^ b = 0 ∨ a ^^^ b = top := by
  rcases first with rfl | rfl <;> rcases second with rfl | rfl <;> simp [Nat.xor_self]

private theorem or_val (left right : Word) : (left.bitOr right).val = left.val ||| right.val := by
  have bound : left.val ||| right.val < wordModulus := by
    unfold wordModulus
    exact Nat.or_lt_two_pow left.isLt right.isLt
  simp only [Word.bitOr, Fin.or_val, Nat.mod_eq_of_lt bound]

private theorem xor_val (left right : Word) : (left.bitXor right).val = left.val ^^^ right.val := by
  have bound : left.val ^^^ right.val < wordModulus := by
    unfold wordModulus
    exact Nat.xor_lt_two_pow left.isLt right.isLt
  simp only [Word.bitXor, Fin.xor_val, Nat.mod_eq_of_lt bound]

/-- Word's `&`, `|` and `^` keep the canonical words of a fixed-width type. -/
theorem canonical_bitwise {type : TypeSystem.FixedInteger} {left right : Word}
    (leftCanonical : type.canonical left.val = true) (rightCanonical : type.canonical right.val = true) :
    type.canonical (left.bitAnd right).val = true ∧ type.canonical (left.bitOr right).val = true ∧
      type.canonical (left.bitXor right).val = true := by
  have andVal : (left.bitAnd right).val = left.val &&& right.val := Fin.and_val _ _
  obtain ⟨signed, width⟩ := type
  cases signed
  · simp only [canonical_true_iff, Bool.false_eq_true, if_false] at leftCanonical rightCanonical ⊢
    rw [andVal, or_val, xor_val]
    exact ⟨Nat.and_lt_two_pow _ rightCanonical, Nat.or_lt_two_pow leftCanonical rightCanonical,
      Nat.xor_lt_two_pow leftCanonical rightCanonical⟩
  · rw [canonical_signed_iff width left.isLt] at leftCanonical
    rw [canonical_signed_iff width right.isLt] at rightCanonical
    rw [canonical_signed_iff width (left.bitAnd right).isLt, canonical_signed_iff width (left.bitOr right).isLt,
      canonical_signed_iff width (left.bitXor right).isLt, andVal, or_val, xor_val]
    simp only [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_and_distrib, Nat.shiftRight_or_distrib,
      Nat.shiftRight_xor_distrib] at leftCanonical rightCanonical ⊢
    exact ⟨top_and leftCanonical rightCanonical, top_or leftCanonical rightCanonical,
      top_xor leftCanonical rightCanonical⟩

/-- The range test of checked `+ - *` reads the source's exact result. -/
theorem checkedInRange_arithmetic {type : TypeSystem.FixedInteger} {binary : Syntax.BinaryOp}
    (kind : FixedCheckedArithmetic binary) (left right : Word) :
    SourceCorePrimitive.checkedInRange type binary left right = true ↔
      Dynamic.FixedInRange type
        (Dynamic.checkedResult binary (Dynamic.fixedValue type left) (Dynamic.fixedValue type right)) := by
  have value : ∀ word, SourceCorePrimitive.fixedIntegerValue type.signed word = Dynamic.fixedValue type word := by
    intro word
    unfold SourceCorePrimitive.fixedIntegerValue Dynamic.fixedValue Dynamic.wordSigned
    rfl
  cases kind <;>
    simp only [SourceCorePrimitive.checkedInRange, value, SourceCorePrimitive.checkedIntegerValue,
      Dynamic.checkedResult, Dynamic.FixedInRange, decide_eq_true_eq]

/-- And that of checked `/ %`, by a nonzero divisor, reads the quotient or the remainder. -/
theorem checkedInRange_division {type : TypeSystem.FixedInteger} {binary : Syntax.BinaryOp}
    (kind : FixedCheckedDivision binary) (left : Word) {right : Word} (nonzero : right ≠ Word.zero) :
    SourceCorePrimitive.checkedInRange type binary left right = true ↔
      Dynamic.FixedInRange type
        (Dynamic.divisionResult binary (Dynamic.fixedValue type left) (Dynamic.fixedValue type right)) := by
  have value : ∀ word, SourceCorePrimitive.fixedIntegerValue type.signed word = Dynamic.fixedValue type word := by
    intro word
    unfold SourceCorePrimitive.fixedIntegerValue Dynamic.fixedValue Dynamic.wordSigned
    rfl
  have divisor : SourceCorePrimitive.fixedIntegerValue type.signed right ≠ 0 :=
    SourceCorePrimitive.fixedIntegerValue_ne_zero nonzero
  rw [value] at divisor
  cases kind <;>
    simp only [SourceCorePrimitive.checkedInRange, value, SourceCorePrimitive.checkedIntegerValue,
      SourceCorePrimitive.divisionIntegerValue, Dynamic.divisionResult, Dynamic.FixedInRange, decide_eq_true_eq,
      divisor, if_false]

end Solcore.SourceSemantics.CoreLowering.FixedCompoundModifier
end

section
/-! The profile with fixed-width compound targets, beside `AssignmentProfile`. Its fourth disjunct
is at the target's own type, not its metadata view: the view erases `comptime`, and at a type whose
view is fixed-width but which is not one of the twelve, the compiler and the source take Word's
operations, whose results need not be canonical for the view. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering
open Frontend

/-- A compound assignment at one of the twelve fixed-width integer types whose binary operator is a
builtin there (`FixedCompoundAssignmentOperator`): `+= -= *= /= %=`, their unchecked forms and
`&= |= ^=`; or a shift (`ShiftCompoundAssignmentOperator`), `<<=` or `>>=`, whose amount has its own
type. -/
abbrev FixedCompoundAssignment (operator : Syntax.ValueAssignOp) (target : TypeSystem.Ty) : Prop :=
  (∃ type, target = .fixed type) ∧
    (FixedCompoundAssignmentOperator operator ∨ ShiftCompoundAssignmentOperator operator)

/-- `AssignmentProfile` on a target's metadata view, or `FixedCompoundAssignment` at its own type. -/
abbrev WideAssignmentProfile (operator : Syntax.ValueAssignOp) (target : TypeSystem.Ty) : Prop :=
  AssignmentProfile operator (SourceCoreRawMetadata.runtimeType target) ∨ FixedCompoundAssignment operator target

/-- `TypeSystem.Ty.fixedInteger?` finds exactly the twelve types. -/
theorem fixedInteger?_eq_some {target : TypeSystem.Ty} {type : TypeSystem.FixedInteger} :
    target.fixedInteger? = some type ↔ target = .fixed type := by
  constructor
  · intro found
    unfold TypeSystem.Ty.fixedInteger? at found
    split at found
    · cases found
      rfl
    · cases found
  · rintro rfl
    rfl

/-- Whether a type is one of the twelve, so the recognizers can check `FixedCompoundAssignment`. -/
instance decidableFixedTarget (target : TypeSystem.Ty) : Decidable (∃ type, target = .fixed type) :=
  match found : target.fixedInteger? with
  | some type => isTrue ⟨type, fixedInteger?_eq_some.mp found⟩
  | none => isFalse fun ⟨_, same⟩ => by
    have absent := (fixedInteger?_eq_some.mpr same).symm.trans found
    cases absent

instance decidableFixedCompoundOperator (operator : Syntax.ValueAssignOp) :
    Decidable (FixedCompoundAssignmentOperator operator) := by
  cases operator
  all_goals first
    | exact isTrue (by constructor)
    | exact isFalse (by intro kind; cases kind)

instance decidableShiftCompoundOperator (operator : Syntax.ValueAssignOp) :
    Decidable (ShiftCompoundAssignmentOperator operator) := by
  cases operator
  all_goals first
    | exact isTrue (by constructor)
    | exact isFalse (by intro kind; cases kind)

instance decidableFixedCompoundAssignment (operator : Syntax.ValueAssignOp) (target : TypeSystem.Ty) :
    Decidable (FixedCompoundAssignment operator target) :=
  inferInstanceAs (Decidable ((∃ type, target = .fixed type) ∧
    (FixedCompoundAssignmentOperator operator ∨ ShiftCompoundAssignmentOperator operator)))

end Solcore.SourceSemantics.CoreLowering
end

section
/-! The leaf. Both place compilers choose the modifier with `assignmentModifier` and the wrap with
`SourceCoreDataPlaces.placeWrap`. At a fixed-width target the modifier applies Word's operation to
the snapshot's word and the right-hand side's, and the unchecked forms and `<<=` wrap the result. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.FixedCompoundModifier
open Core Frontend DataEquality

/-- The word Core's modifier computes for a compound assignment at a fixed-width target. -/
def leaf (type : TypeSystem.FixedInteger) : Syntax.ValueAssignOp → Word → Word → Word
  | .add, left, right => left.add right
  | .subtract, left, right => left.sub right
  | .multiply, left, right => left.mul right
  | .divide, left, right => if type.signed then left.sdiv right else left.udiv right
  | .modulo, left, right => if type.signed then left.smod right else left.umod right
  | .bitAnd, left, right => left.bitAnd right
  | .bitOr, left, right => left.bitOr right
  | .bitXor, left, right => left.bitXor right
  | .uncheckedAdd, left, right => wrapWord type (left.add right)
  | .uncheckedSubtract, left, right => wrapWord type (left.sub right)
  | .uncheckedMultiply, left, right => wrapWord type (left.mul right)
  | .uncheckedDivide, left, right => wrapWord type (if type.signed then left.sdiv right else left.udiv right)
  | .uncheckedModulo, left, right => wrapWord type (if type.signed then left.smod right else left.umod right)
  | .shiftLeft, left, right => wrapWord type (left.shiftLeft right)
  | .shiftRight, left, right => if type.signed then left.shiftArithmeticRight right else left.shiftRight right
  | _, _, right => right

/-- The two compilers' modifiers are the same. -/
theorem compatible_assignmentModifier (target : TypeSystem.Ty) (integer : Bool) (operator : Syntax.ValueAssignOp) :
    SourceCoreCompatibleDataPlaces.assignmentModifier target integer operator =
      SourceCoreDataPlaces.assignmentModifier target integer operator := by
  unfold SourceCoreCompatibleDataPlaces.assignmentModifier SourceCoreDataPlaces.assignmentModifier
  cases SourceCoreDataPlaces.checkedCompound target operator with
  | some pair => rfl
  | none => cases operator <;> rfl

/-- At a fixed-width target a shift's modifier, wrapped as the compiler wraps it, computes the
leaf. -/
theorem shift_leaf_evaluates {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    (shift : ShiftCompoundAssignmentOperator operator) {environment : Environment} {store : Store}
    {shifted : Expr} {left right : Word}
    (rightEvaluated : Evaluates (.word left :: environment) store shifted (.word right) store) :
    ∃ modifier, SourceCoreDataPlaces.assignmentModifier (.fixed type) false operator = some modifier ∧
      Evaluates (.word left :: environment) store
        (SourceCoreDataPlaces.wrapLeaf (SourceCoreDataPlaces.placeWrap (.fixed type) operator false)
          (.binary modifier.operation (.var 0) shifted)) (.word (leaf type operator left right)) store := by
  obtain ⟨signed, width⟩ := type
  cases signed <;> cases shift <;>
    first
      | exact ⟨_, rfl, .binary (.var rfl) rightEvaluated rfl⟩
      | exact ⟨_, rfl, .binary (.binary (.var rfl) rightEvaluated rfl) .word rfl⟩
      | exact ⟨_, rfl, .binary .word (.binary (.var rfl) rightEvaluated rfl) rfl⟩

/-- The data-place compiler's shift modifier at a fixed-width target gives the leaf. -/
theorem shift_modified_evaluates {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    (shift : ShiftCompoundAssignmentOperator operator) {environment : Environment} {snapshot rhs : Expr}
    {left right : Word} (snapshotSelected : Selects environment snapshot (.inRight .unit (.word left)))
    (rightSelected : Selects environment rhs (.word right)) (store : Store) (invalid : Word) :
    Evaluates environment store
      (SourceCoreDataPlaces.modified .word (SourceCoreDataPlaces.assignmentModifier (.fixed type) false operator)
        false snapshot rhs invalid (SourceCoreDataPlaces.placeWrap (.fixed type) operator false))
      (.inRight .word (.word (leaf type operator left right))) store := by
  obtain ⟨modifier, chosen, evaluated⟩ :=
    shift_leaf_evaluates (type := type) shift ((rightSelected.weaken (.word left)).evaluates store)
  rw [chosen]
  exact .caseRight (snapshotSelected.evaluates store) (.inRight evaluated)

/-- So does the compatible compiler's. -/
theorem shift_compatible_modified_evaluates {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    (shift : ShiftCompoundAssignmentOperator operator) {environment : Environment} {snapshot rhs : Expr}
    {left right : Word} (snapshotSelected : Selects environment snapshot (.inRight .unit (.word left)))
    (rightSelected : Selects environment rhs (.word right)) (store : Store) (invalid : Word) :
    Evaluates environment store
      (SourceCoreCompatibleDataPlaces.modified .word
        (SourceCoreCompatibleDataPlaces.assignmentModifier (.fixed type) false operator)
        false snapshot rhs invalid (SourceCoreDataPlaces.placeWrap (.fixed type) operator false))
      (.inRight .word (.word (leaf type operator left right))) store := by
  obtain ⟨modifier, chosen, evaluated⟩ :=
    shift_leaf_evaluates (type := type) shift ((rightSelected.weaken (.word left)).evaluates store)
  rw [compatible_assignmentModifier, chosen]
  exact .caseRight (snapshotSelected.evaluates store) (.inRight evaluated)

/-- At a fixed-width target the modifier's operation, wrapped as the compiler wraps it, computes the
leaf. -/
theorem leaf_evaluates {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    (kind : FixedCompoundAssignmentOperator operator ∨ ShiftCompoundAssignmentOperator operator) {environment : Environment} {store : Store}
    {shifted : Expr} {left right : Word}
    (rightEvaluated : Evaluates (.word left :: environment) store shifted (.word right) store) :
    ∃ modifier, SourceCoreDataPlaces.assignmentModifier (.fixed type) false operator = some modifier ∧
      Evaluates (.word left :: environment) store
        (SourceCoreDataPlaces.wrapLeaf (SourceCoreDataPlaces.placeWrap (.fixed type) operator false)
          (.binary modifier.operation (.var 0) shifted)) (.word (leaf type operator left right)) store := by
  rcases kind with kind | shift
  rotate_left
  · exact shift_leaf_evaluates shift rightEvaluated
  obtain ⟨signed, width⟩ := type
  cases signed <;> cases kind <;>
    first
      | exact ⟨_, rfl, .binary (.var rfl) rightEvaluated rfl⟩
      | exact ⟨_, rfl, .binary (.binary (.var rfl) rightEvaluated rfl) .word rfl⟩
      | exact ⟨_, rfl, .binary .word (.binary (.var rfl) rightEvaluated rfl) rfl⟩

/-- The data-place compiler's modifier at a fixed-width target gives the leaf. -/
theorem modified_evaluates {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    (kind : FixedCompoundAssignmentOperator operator ∨ ShiftCompoundAssignmentOperator operator) {environment : Environment} {snapshot rhs : Expr}
    {left right : Word} (snapshotSelected : Selects environment snapshot (.inRight .unit (.word left)))
    (rightSelected : Selects environment rhs (.word right)) (store : Store) (invalid : Word) :
    Evaluates environment store
      (SourceCoreDataPlaces.modified .word (SourceCoreDataPlaces.assignmentModifier (.fixed type) false operator)
        false snapshot rhs invalid (SourceCoreDataPlaces.placeWrap (.fixed type) operator false))
      (.inRight .word (.word (leaf type operator left right))) store := by
  obtain ⟨modifier, chosen, evaluated⟩ :=
    leaf_evaluates (type := type) kind ((rightSelected.weaken (.word left)).evaluates store)
  rw [chosen]
  exact .caseRight (snapshotSelected.evaluates store) (.inRight evaluated)

/-- So does the compatible compiler's. -/
theorem compatible_modified_evaluates {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    (kind : FixedCompoundAssignmentOperator operator ∨ ShiftCompoundAssignmentOperator operator) {environment : Environment} {snapshot rhs : Expr}
    {left right : Word} (snapshotSelected : Selects environment snapshot (.inRight .unit (.word left)))
    (rightSelected : Selects environment rhs (.word right)) (store : Store) (invalid : Word) :
    Evaluates environment store
      (SourceCoreCompatibleDataPlaces.modified .word
        (SourceCoreCompatibleDataPlaces.assignmentModifier (.fixed type) false operator)
        false snapshot rhs invalid (SourceCoreDataPlaces.placeWrap (.fixed type) operator false))
      (.inRight .word (.word (leaf type operator left right))) store := by
  obtain ⟨modifier, chosen, evaluated⟩ :=
    leaf_evaluates (type := type) kind ((rightSelected.weaken (.word left)).evaluates store)
  rw [compatible_assignmentModifier, chosen]
  exact .caseRight (snapshotSelected.evaluates store) (.inRight evaluated)

end Solcore.SourceSemantics.CoreLowering.FixedCompoundModifier
end

section
/-! The source rules on the same operands. An applied operation gives the leaf. The source panics
on checked `+= -= *=` outside the type's range, on checked `/= %=` by zero or outside the range,
and on unchecked `/= %=` by zero. The modifier's check, which `guard` makes after the setter, fails
with the same panic, and otherwise writes. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.FixedCompoundModifier
open Core Frontend

private theorem fixed_inj {type other : TypeSystem.FixedInteger}
    (same : TypeSystem.Ty.fixed type = TypeSystem.Ty.fixed other) : other = type := by
  unfold TypeSystem.Ty.fixed at same
  injection same with same
  injection same with same
  injection same with same
  exact same.symm

private abbrev value (type : TypeSystem.FixedInteger) (word : Word) : Int := Dynamic.fixedValue type word

private theorem leaf_add (type : TypeSystem.FixedInteger) (left right : Word) :
    leaf type .add left right =
      Word.ofIntModulo (Dynamic.checkedResult .add (value type left) (value type right)) :=
  add_fixed type left right

private theorem leaf_subtract (type : TypeSystem.FixedInteger) (left right : Word) :
    leaf type .subtract left right =
      Word.ofIntModulo (Dynamic.checkedResult .subtract (value type left) (value type right)) :=
  sub_fixed type left right

private theorem leaf_multiply (type : TypeSystem.FixedInteger) (left right : Word) :
    leaf type .multiply left right =
      Word.ofIntModulo (Dynamic.checkedResult .multiply (value type left) (value type right)) :=
  mul_fixed type left right

private theorem leaf_divide (type : TypeSystem.FixedInteger) {left right : Word} (nonzero : right ≠ Word.zero) :
    leaf type .divide left right =
      Word.ofIntModulo (Dynamic.divisionResult .divide (value type left) (value type right)) :=
  divide_fixed type nonzero

private theorem leaf_modulo (type : TypeSystem.FixedInteger) {left right : Word} (nonzero : right ≠ Word.zero) :
    leaf type .modulo left right =
      Word.ofIntModulo (Dynamic.divisionResult .modulo (value type left) (value type right)) :=
  modulo_fixed type nonzero

private theorem leaf_uncheckedAdd (type : TypeSystem.FixedInteger) (left right : Word) :
    leaf type .uncheckedAdd left right = Word.ofIntModulo (Dynamic.fixedWrap type
      (Dynamic.uncheckedResult .uncheckedAdd (value type left) (value type right))) := by
  show wrapWord type (left.add right) = _
  rw [add_fixed type, wrap_ofIntModulo]
  rfl

private theorem leaf_uncheckedSubtract (type : TypeSystem.FixedInteger) (left right : Word) :
    leaf type .uncheckedSubtract left right = Word.ofIntModulo (Dynamic.fixedWrap type
      (Dynamic.uncheckedResult .uncheckedSubtract (value type left) (value type right))) := by
  show wrapWord type (left.sub right) = _
  rw [sub_fixed type, wrap_ofIntModulo]
  rfl

private theorem leaf_uncheckedMultiply (type : TypeSystem.FixedInteger) (left right : Word) :
    leaf type .uncheckedMultiply left right = Word.ofIntModulo (Dynamic.fixedWrap type
      (Dynamic.uncheckedResult .uncheckedMultiply (value type left) (value type right))) := by
  show wrapWord type (left.mul right) = _
  rw [mul_fixed type, wrap_ofIntModulo]
  rfl

private theorem leaf_uncheckedDivide (type : TypeSystem.FixedInteger) {left right : Word}
    (nonzero : right ≠ Word.zero) :
    leaf type .uncheckedDivide left right = Word.ofIntModulo (Dynamic.fixedWrap type
      (Dynamic.uncheckedDivisionResult .uncheckedDivide (value type left) (value type right))) := by
  show wrapWord type (if type.signed then left.sdiv right else left.udiv right) = _
  rw [divide_fixed type nonzero, wrap_ofIntModulo]
  rfl

private theorem leaf_uncheckedModulo (type : TypeSystem.FixedInteger) {left right : Word}
    (nonzero : right ≠ Word.zero) :
    leaf type .uncheckedModulo left right = Word.ofIntModulo (Dynamic.fixedWrap type
      (Dynamic.uncheckedDivisionResult .uncheckedModulo (value type left) (value type right))) := by
  show wrapWord type (if type.signed then left.smod right else left.umod right) = _
  rw [modulo_fixed type nonzero, wrap_ofIntModulo]
  rfl

private theorem leaf_shiftLeft (type : TypeSystem.FixedInteger) (left right : Word) :
    leaf type .shiftLeft left right =
      Word.ofIntModulo (Dynamic.fixedWrap type (Dynamic.fixedValue type (left.shiftLeft right))) :=
  wrapWord_fixed type _

/-- An applied shift at a fixed-width target gives the leaf. -/
theorem shift_applies_leaf {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    (shift : ShiftCompoundAssignmentOperator operator) {left right : Word} {result : Dynamic.Value}
    (applied : Dynamic.CompoundAssignmentApplies (.fixed type) operator (some (.word left)) (.word right) result) :
    result = .word (leaf type operator left right) := by
  cases shift
  · cases applied
    case primitive plain _ => exact (plain type rfl .shiftLeft).elim
    case shiftLeft same applies =>
      cases fixed_inj same
      cases applies <;> first
        | cases ‹FixedCheckedArithmetic _› | cases ‹FixedCheckedDivision _› | cases ‹FixedUncheckedArithmetic _›
        | cases ‹FixedUncheckedDivision _›
        | exact congrArg Dynamic.Value.word (leaf_shiftLeft type left right).symm
  · cases applied
    case primitive plain _ => exact (plain type rfl .shiftRight).elim
    case shiftRight same applies =>
      cases fixed_inj same
      cases applies <;> first
        | cases ‹FixedCheckedArithmetic _› | cases ‹FixedCheckedDivision _› | cases ‹FixedUncheckedArithmetic _›
        | cases ‹FixedUncheckedDivision _›
        | rfl

/-- An applied operation at a fixed-width target gives the leaf. -/
theorem applies_leaf {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    (kind : FixedCompoundAssignmentOperator operator ∨ ShiftCompoundAssignmentOperator operator) {left right : Word} {result : Dynamic.Value}
    (applied : Dynamic.CompoundAssignmentApplies (.fixed type) operator (some (.word left)) (.word right) result) :
    result = .word (leaf type operator left right) := by
  rcases kind with kind | shift
  rotate_left
  · exact shift_applies_leaf shift applied
  cases applied
  case primitive plain applies =>
    cases kind <;> try exact (plain type rfl (by constructor)).elim
    all_goals
      cases applies
      rename_i applies
      cases applies
      rfl
  case add same applies =>
    cases fixed_inj same
    cases applies <;> first
      | cases ‹FixedCheckedDivision _› | cases ‹FixedUncheckedArithmetic _› | cases ‹FixedUncheckedDivision _›
      | exact congrArg Dynamic.Value.word (leaf_add type left right).symm
  case subtract same applies =>
    cases fixed_inj same
    cases applies <;> first
      | cases ‹FixedCheckedDivision _› | cases ‹FixedUncheckedArithmetic _› | cases ‹FixedUncheckedDivision _›
      | exact congrArg Dynamic.Value.word (leaf_subtract type left right).symm
  case multiply same applies =>
    cases fixed_inj same
    cases applies <;> first
      | cases ‹FixedCheckedDivision _› | cases ‹FixedUncheckedArithmetic _› | cases ‹FixedUncheckedDivision _›
      | exact congrArg Dynamic.Value.word (leaf_multiply type left right).symm
  case divide same applies =>
    cases fixed_inj same
    cases applies <;> first
      | cases ‹FixedCheckedArithmetic _› | cases ‹FixedUncheckedArithmetic _› | cases ‹FixedUncheckedDivision _›
      | exact congrArg Dynamic.Value.word (leaf_divide type ‹right ≠ Word.zero›).symm
  case modulo same applies =>
    cases fixed_inj same
    cases applies <;> first
      | cases ‹FixedCheckedArithmetic _› | cases ‹FixedUncheckedArithmetic _› | cases ‹FixedUncheckedDivision _›
      | exact congrArg Dynamic.Value.word (leaf_modulo type ‹right ≠ Word.zero›).symm
  case uncheckedAdd same applies =>
    cases fixed_inj same
    cases applies <;> first
      | cases ‹FixedCheckedArithmetic _› | cases ‹FixedCheckedDivision _› | cases ‹FixedUncheckedDivision _›
      | exact congrArg Dynamic.Value.word (leaf_uncheckedAdd type left right).symm
  case uncheckedSubtract same applies =>
    cases fixed_inj same
    cases applies <;> first
      | cases ‹FixedCheckedArithmetic _› | cases ‹FixedCheckedDivision _› | cases ‹FixedUncheckedDivision _›
      | exact congrArg Dynamic.Value.word (leaf_uncheckedSubtract type left right).symm
  case uncheckedMultiply same applies =>
    cases fixed_inj same
    cases applies <;> first
      | cases ‹FixedCheckedArithmetic _› | cases ‹FixedCheckedDivision _› | cases ‹FixedUncheckedDivision _›
      | exact congrArg Dynamic.Value.word (leaf_uncheckedMultiply type left right).symm
  case uncheckedDivide same applies =>
    cases fixed_inj same
    cases applies <;> first
      | cases ‹FixedCheckedArithmetic _› | cases ‹FixedCheckedDivision _› | cases ‹FixedUncheckedArithmetic _›
      | exact congrArg Dynamic.Value.word (leaf_uncheckedDivide type ‹right ≠ Word.zero›).symm
  case uncheckedModulo same applies =>
    cases fixed_inj same
    cases applies <;> first
      | cases ‹FixedCheckedArithmetic _› | cases ‹FixedCheckedDivision _› | cases ‹FixedUncheckedArithmetic _›
      | exact congrArg Dynamic.Value.word (leaf_uncheckedModulo type ‹right ≠ Word.zero›).symm
  case shiftLeft => cases kind
  case shiftRight => cases kind

/-- An applied shift keeps the target's word canonical for the type, whatever the amount. -/
theorem shift_canonical_of_applies {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    (shift : ShiftCompoundAssignmentOperator operator) {left right : Word} {result : Dynamic.Value}
    (leftCanonical : type.canonical left.val = true)
    (applied : Dynamic.CompoundAssignmentApplies (.fixed type) operator (some (.word left)) (.word right) result) :
    ∃ word, result = .word word ∧ type.canonical word.val = true := by
  refine ⟨_, shift_applies_leaf shift applied, ?_⟩
  cases shift
  · rw [leaf_shiftLeft]
    exact canonical_ofIntModulo (Dynamic.fixedWrap_inRange type _)
  · exact Dynamic.fixed_canonical_shiftRight leftCanonical right

/-- An applied operation keeps the words canonical for the type. -/
theorem canonical_of_applies {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    (kind : FixedCompoundAssignmentOperator operator ∨ ShiftCompoundAssignmentOperator operator) {left right : Word} {result : Dynamic.Value}
    (leftCanonical : type.canonical left.val = true) (rightCanonical : type.canonical right.val = true)
    (applied : Dynamic.CompoundAssignmentApplies (.fixed type) operator (some (.word left)) (.word right) result) :
    ∃ word, result = .word word ∧ type.canonical word.val = true := by
  rcases kind with kind | shift
  rotate_left
  · exact shift_canonical_of_applies shift leftCanonical applied
  have bitwise := canonical_bitwise leftCanonical rightCanonical
  have wrapped : ∀ value, type.canonical (Word.ofIntModulo (Dynamic.fixedWrap type value)).val = true :=
    fun value => canonical_ofIntModulo (Dynamic.fixedWrap_inRange type value)
  cases applied
  case primitive plain applies =>
    cases kind <;> try exact (plain type rfl (by constructor)).elim
    all_goals
      cases applies
      rename_i applies
      cases applies
    · exact ⟨_, rfl, bitwise.1⟩
    · exact ⟨_, rfl, bitwise.2.2⟩
    · exact ⟨_, rfl, bitwise.2.1⟩
  case shiftLeft => cases kind
  case shiftRight => cases kind
  all_goals
    rename_i same applies
    cases fixed_inj same
    cases applies <;> first
      | exact ⟨_, rfl, wrapped _⟩
      | exact ⟨_, rfl, canonical_ofIntModulo ‹Dynamic.FixedInRange _ _›⟩
      | cases ‹FixedCheckedArithmetic _›
      | cases ‹FixedCheckedDivision _›
      | cases ‹FixedUncheckedArithmetic _›
      | cases ‹FixedUncheckedDivision _›

/-- A panic of the type's own operation excludes an applied one. -/
private theorem not_applies {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    {binary : Syntax.BinaryOp} {left right : Word} {code : UInt8}
    (corresponds : Dynamic.AssignmentOperatorBinary operator binary) (checked : FixedCheckedCompound operator)
    (panics : Dynamic.FixedBinaryPanics type binary (.word left) (.word right) code) (result : Dynamic.Value) :
    ¬ Dynamic.CompoundAssignmentApplies (.fixed type) operator (some (.word left)) (.word right) result := by
  intro applied
  cases applied
  case primitive plain _ => exact plain type rfl checked
  all_goals
    rename_i same applies
    cases fixed_inj same
    cases corresponds
    exact panics.excludes_application applies

/-- Unchecked `/= %=` by zero apply nothing. -/
private theorem not_applies_zero {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    {binary : Syntax.BinaryOp} (corresponds : Dynamic.AssignmentOperatorBinary operator binary)
    (kind : FixedUncheckedDivision binary) (left : Word) (result : Dynamic.Value) :
    ¬ Dynamic.CompoundAssignmentApplies (.fixed type) operator (some (.word left)) (.word Word.zero) result := by
  intro applied
  cases kind <;> cases corresponds <;> cases applied
  all_goals first
    | (rename_i plain _; exact plain type rfl (by constructor))
    | (rename_i same applies
       cases fixed_inj same
       cases applies <;> first
        | exact ‹Word.zero ≠ Word.zero› rfl
        | cases ‹FixedCheckedArithmetic _›
        | cases ‹FixedCheckedDivision _›
        | cases ‹FixedUncheckedArithmetic _›)

/-- Word operands of a shift are never invalid. -/
theorem shift_words_valid {operator : Syntax.ValueAssignOp} (shift : ShiftCompoundAssignmentOperator operator)
    (left right : Word) : ¬ Dynamic.AssignmentOperandsInvalid operator (some (.word left)) (.word right) := by
  intro invalid
  cases invalid with
  | compound corresponds invalid =>
    cases invalid with
    | numeric _ pair => exact pair trivial
    | word _ pair => exact pair trivial
    | logical operatorClass => cases shift <;> cases corresponds <;> cases operatorClass

/-- Word operands of these operators are never invalid. -/
theorem words_valid {operator : Syntax.ValueAssignOp} (kind : FixedCompoundAssignmentOperator operator ∨ ShiftCompoundAssignmentOperator operator)
    (left right : Word) : ¬ Dynamic.AssignmentOperandsInvalid operator (some (.word left)) (.word right) := by
  intro invalid
  cases invalid with
  | compound corresponds invalid =>
    cases invalid with
    | numeric _ pair => exact pair trivial
    | word _ pair => exact pair trivial
    | logical operatorClass => cases kind <;> cases corresponds <;> cases operatorClass

variable {environment : Environment} {store : Store} {outputType leftType : Ty} {write : Expr}
  {updated changed : Value}

/-- A nonzero right-hand side passes a zero test. -/
theorem guard_divisor_nonzero {operation : BinaryOp} {right : Word} (nonzero : right ≠ Word.zero)
    (result : Value) (after : Store) :
    Evaluates (updated :: changed :: .word right :: environment) store
        (SourceCoreDataPlaces.guard outputType (some ⟨operation, .divisor⟩) write) result after ↔
      Evaluates (updated :: changed :: .word right :: environment) store write result after := by
  constructor
  · intro evaluated
    rcases SourceCoreDataPlaces.guard_inv evaluated with ⟨_, written⟩ | ⟨_, _, zero, _, _⟩ | ⟨_, _, _, ranged, _⟩
    · exact written
    · cases zero
      exact (nonzero rfl).elim
    · cases ranged
  · exact SourceCoreDataPlaces.guard_passes (.nonzero nonzero)

/-- A zero right-hand side fails it with `Panic(0x12)`. -/
theorem guard_divisor_zero {operation : BinaryOp} (result : Value) (after : Store) :
    Evaluates (updated :: changed :: .word Word.zero :: environment) store
        (SourceCoreDataPlaces.guard outputType (some ⟨operation, .divisor⟩) write) result after ↔
      (result = .inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero)) ∧
        after = store) := by
  constructor
  · intro evaluated
    rcases SourceCoreDataPlaces.guard_inv evaluated with ⟨passes, _⟩ | ⟨_, _, _, resultEq, storeEq⟩ |
        ⟨_, _, _, ranged, _⟩
    · cases passes with
      | total total => cases total _ rfl
      | nonzero nonzero => exact (nonzero rfl).elim
    · exact ⟨resultEq, storeEq⟩
    · cases ranged
  · rintro ⟨rfl, rfl⟩
    exact SourceCoreDataPlaces.guard_panic

private theorem guard_range_pass {operation : BinaryOp} {type : TypeSystem.FixedInteger}
    {binary : Syntax.BinaryOp} {left right : Word}
    (divisor : SourceCoreDataPlaces.DivisorPasses binary (.word right))
    (inRange : SourceCorePrimitive.checkedInRange type binary left right = true) (result : Value) (after : Store) :
    Evaluates (updated :: changed :: .word right :: .inRight leftType (.word left) :: environment) store
        (SourceCoreDataPlaces.guard outputType (some ⟨operation, .range type binary⟩) write) result after ↔
      Evaluates (updated :: changed :: .word right :: .inRight leftType (.word left) :: environment) store
        write result after := by
  constructor
  · intro evaluated
    rcases SourceCoreDataPlaces.guard_range_inv evaluated with ⟨_, _, written⟩ |
        ⟨⟨_, _, _, head, same, outside⟩, _⟩ | ⟨division, zero, _⟩
    · exact written
    · simp only [List.head?_cons, Option.some.injEq] at head
      cases head
      cases same
      rw [inRange] at outside
      cases outside
    · obtain ⟨word, same, nonzero⟩ := divisor division
      cases zero
      cases same
      exact (nonzero rfl).elim
  · exact SourceCoreDataPlaces.guard_inRange divisor inRange

private theorem guard_range_overflow {operation : BinaryOp} {type : TypeSystem.FixedInteger}
    {binary : Syntax.BinaryOp} {left right : Word}
    (divisor : SourceCoreDataPlaces.DivisorPasses binary (.word right))
    (outside : SourceCorePrimitive.checkedInRange type binary left right = false) (result : Value) (after : Store) :
    Evaluates (updated :: changed :: .word right :: .inRight leftType (.word left) :: environment) store
        (SourceCoreDataPlaces.guard outputType (some ⟨operation, .range type binary⟩) write) result after ↔
      (result = .inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.arithmetic)) ∧
        after = store) := by
  constructor
  · intro evaluated
    rcases SourceCoreDataPlaces.guard_range_inv evaluated with ⟨_, passes, _⟩ | ⟨_, _, resultEq, storeEq⟩ |
        ⟨division, zero, _⟩
    · rcases passes with ⟨_, _, impossible⟩ | ⟨_, _, _, head, same, inRange⟩
      · cases impossible
      · cases head
        cases same
        rw [outside] at inRange
        cases inRange
    · exact ⟨resultEq, storeEq⟩
    · obtain ⟨word, same, nonzero⟩ := divisor division
      cases zero
      cases same
      exact (nonzero rfl).elim
  · rintro ⟨rfl, rfl⟩
    exact SourceCoreDataPlaces.guard_overflow divisor outside

private theorem guard_range_zero {operation : BinaryOp} {type : TypeSystem.FixedInteger}
    {binary : Syntax.BinaryOp} (division : SourceCorePrimitive.checkedDivision binary = true)
    (result : Value) (after : Store) :
    Evaluates (updated :: changed :: .word Word.zero :: environment) store
        (SourceCoreDataPlaces.guard outputType (some ⟨operation, .range type binary⟩) write) result after ↔
      (result = .inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero)) ∧
        after = store) := by
  constructor
  · intro evaluated
    rcases SourceCoreDataPlaces.guard_range_inv evaluated with ⟨divisor, _, _⟩ | ⟨_, divisor, _, _⟩ |
        ⟨_, _, resultEq, storeEq⟩
    · obtain ⟨word, same, nonzero⟩ := divisor division
      cases same
      exact (nonzero rfl).elim
    · obtain ⟨word, same, nonzero⟩ := divisor division
      cases same
      exact (nonzero rfl).elim
    · exact ⟨resultEq, storeEq⟩
  · rintro ⟨rfl, rfl⟩
    exact SourceCoreDataPlaces.guard_rangeZero division

private theorem no_division {binary : Syntax.BinaryOp} (kind : FixedCheckedArithmetic binary) (right : Word) :
    SourceCoreDataPlaces.DivisorPasses binary (.word right) := by
  intro division
  cases kind <;> simp [SourceCorePrimitive.checkedDivision] at division

/-- The check of `modifier` passes on the right-hand side `right` and the snapshot `snapshot`: a total
or nonzero check (`SourceCoreDataPlaces.Passes`), or a range check whose zero test and range test
pass. -/
def CheckPasses (modifier : Option SourceCoreDataPlaces.Modifier) (snapshot right : Value) : Prop :=
  SourceCoreDataPlaces.Passes modifier right ∨
    ∃ operation type binary, modifier = some ⟨operation, .range type binary⟩ ∧
      SourceCoreDataPlaces.DivisorPasses binary right ∧ SourceCoreDataPlaces.RangePasses type binary [snapshot] right

/-- How a modifier's check, after the setter, agrees with the source on a compound assignment: under
any binders over the right-hand side `rightCore` and the snapshot `snapshotCore`, the check of
`modifier` writes when the source applies the operation, with `result`, and otherwise fails with the
source's panic, writing nothing. -/
inductive Agreement (target : TypeSystem.Ty) (operator : Syntax.ValueAssignOp) (snapshot : Option Dynamic.Value)
    (right result : Dynamic.Value) (modifier : Option SourceCoreDataPlaces.Modifier) (snapshotCore rightCore : Value) :
    Prop where
  /-- The source applies the operation, and the check passes and writes. -/
  | applied (applies : Dynamic.CompoundAssignmentApplies target operator snapshot right result)
      (passing : CheckPasses modifier snapshotCore rightCore)
      (writes : ∀ {binders : Environment} {store after : Store} {outputType : Ty} {write : Expr}
          {value updated changed : Value},
        Evaluates (updated :: changed :: rightCore :: snapshotCore :: binders) store
            (SourceCoreDataPlaces.guard outputType modifier write) value after ↔
          Evaluates (updated :: changed :: rightCore :: snapshotCore :: binders) store write value after)
  /-- The source panics and applies nothing, and the check fails with the panic. -/
  | panicked (code : UInt8) (panics : Dynamic.AssignmentOperandsPanic target operator snapshot right code)
      (excluded : ∀ other, ¬ Dynamic.CompoundAssignmentApplies target operator snapshot right other)
      (fails : ∀ {binders : Environment} {store after : Store} {outputType : Ty} {write : Expr}
          {value updated changed : Value},
        Evaluates (updated :: changed :: rightCore :: snapshotCore :: binders) store
            (SourceCoreDataPlaces.guard outputType modifier write) value after ↔
          (value = .inLeft outputType (.word (SourceCorePanics.reason code)) ∧ after = store))

private theorem agrees_checked {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    {binary : Syntax.BinaryOp} {left right : Word} (corresponds : Dynamic.AssignmentOperatorBinary operator binary)
    (arithmetic : FixedCheckedArithmetic binary) (checked : FixedCheckedCompound operator)
    (applies : ∀ {result : Dynamic.Value}, Dynamic.FixedBinaryApplies type binary (.word left) (.word right) result →
      Dynamic.CompoundAssignmentApplies (.fixed type) operator (some (.word left)) (.word right) result)
    (leafEq : leaf type operator left right =
      Word.ofIntModulo (Dynamic.checkedResult binary (value type left) (value type right)))
    {operation : BinaryOp} :
    Agreement (.fixed type) operator (some (.word left)) (.word right) (.word (leaf type operator left right))
      (some ⟨operation, .range type binary⟩) (.inRight leftType (.word left)) (.word right) := by
  by_cases inRange : Dynamic.FixedInRange type (Dynamic.checkedResult binary (value type left) (value type right))
  · refine .applied ?_ (.inr ⟨operation, type, binary, rfl, no_division arithmetic right,
      .inr ⟨leftType, left, right, rfl, rfl, (checkedInRange_arithmetic arithmetic left right).mpr inRange⟩⟩)
      (guard_range_pass (no_division arithmetic right) ((checkedInRange_arithmetic arithmetic left right).mpr inRange) _ _)
    rw [leafEq]
    exact applies (.checked arithmetic left right inRange)
  · have panics := Dynamic.FixedBinaryPanics.overflow arithmetic left right inRange
    exact .panicked 0x11 (.compound corresponds (.fixed rfl panics)) (not_applies corresponds checked panics)
      (guard_range_overflow (no_division arithmetic right)
        (Bool.eq_false_iff.mpr fun same => inRange ((checkedInRange_arithmetic arithmetic left right).mp same)) _ _)

private theorem agrees_division {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    {binary : Syntax.BinaryOp} {left right : Word} (corresponds : Dynamic.AssignmentOperatorBinary operator binary)
    (division : FixedCheckedDivision binary) (checked : FixedCheckedCompound operator)
    (applies : ∀ {result : Dynamic.Value}, Dynamic.FixedBinaryApplies type binary (.word left) (.word right) result →
      Dynamic.CompoundAssignmentApplies (.fixed type) operator (some (.word left)) (.word right) result)
    (leafEq : right ≠ Word.zero → leaf type operator left right =
      Word.ofIntModulo (Dynamic.divisionResult binary (value type left) (value type right)))
    {operation : BinaryOp} :
    Agreement (.fixed type) operator (some (.word left)) (.word right) (.word (leaf type operator left right))
      (some ⟨operation, .range type binary⟩) (.inRight leftType (.word left)) (.word right) := by
  have divides : SourceCorePrimitive.checkedDivision binary = true := by cases division <;> rfl
  by_cases zero : right = Word.zero
  · subst zero
    have panics := Dynamic.FixedBinaryPanics.divisionByZero (type := type) division left
    exact .panicked 0x12 (.compound corresponds (.fixed rfl panics)) (not_applies corresponds checked panics)
      (guard_range_zero divides _ _)
  · have divisor : SourceCoreDataPlaces.DivisorPasses binary (.word right) := fun _ => ⟨right, rfl, zero⟩
    by_cases inRange : Dynamic.FixedInRange type (Dynamic.divisionResult binary (value type left) (value type right))
    · refine .applied ?_ (.inr ⟨operation, type, binary, rfl, divisor,
        .inr ⟨leftType, left, right, rfl, rfl, (checkedInRange_division division left zero).mpr inRange⟩⟩)
        (guard_range_pass divisor ((checkedInRange_division division left zero).mpr inRange) _ _)
      rw [leafEq zero]
      exact applies (.division division left right zero inRange)
    · have panics := Dynamic.FixedBinaryPanics.divisionOverflow division left right zero inRange
      exact .panicked 0x11 (.compound corresponds (.fixed rfl panics)) (not_applies corresponds checked panics)
        (guard_range_overflow divisor
          (Bool.eq_false_iff.mpr fun same => inRange ((checkedInRange_division division left zero).mp same)) _ _)

private theorem agrees_total {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp} {left right : Word}
    (applies : Dynamic.CompoundAssignmentApplies (.fixed type) operator (some (.word left)) (.word right)
      (.word (leaf type operator left right)))
    {operation : BinaryOp} :
    Agreement (.fixed type) operator (some (.word left)) (.word right) (.word (leaf type operator left right))
      (some ⟨operation, .total⟩) (.inRight leftType (.word left)) (.word right) :=
  .applied applies (.inl (.total fun _ same => by cases same; rfl)) Iff.rfl

private theorem agrees_unchecked_division {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    {binary : Syntax.BinaryOp} {left right : Word} (corresponds : Dynamic.AssignmentOperatorBinary operator binary)
    (kind : FixedUncheckedDivision binary)
    (applies : right ≠ Word.zero → Dynamic.CompoundAssignmentApplies (.fixed type) operator (some (.word left))
      (.word right) (.word (leaf type operator left right)))
    (panics : Dynamic.BinaryPrimitivePanics binary (.word left) (.word Word.zero) 0x12) {operation : BinaryOp} :
    Agreement (.fixed type) operator (some (.word left)) (.word right) (.word (leaf type operator left right))
      (some ⟨operation, .divisor⟩) (.inRight leftType (.word left)) (.word right) := by
  by_cases zero : right = Word.zero
  · subst zero
    exact .panicked 0x12 (.compound corresponds (.primitive panics)) (not_applies_zero corresponds kind left)
      (guard_divisor_zero _ _)
  · exact .applied (applies zero) (.inl (.nonzero zero)) (guard_divisor_nonzero zero _ _)

/-- A shift's modifier checks nothing after the setter, and the source applies the shift, with the
leaf. -/
theorem shift_guard_agrees {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    (shift : ShiftCompoundAssignmentOperator operator) (left right : Word) {leftType : Ty} :
    Agreement (.fixed type) operator (some (.word left)) (.word right) (.word (leaf type operator left right))
      (SourceCoreDataPlaces.assignmentModifier (.fixed type) false operator) (.inRight leftType (.word left))
      (.word right) := by
  cases shift
  · exact agrees_total (by
      rw [leaf_shiftLeft]
      exact .shiftLeft rfl (.shiftLeft left right))
  · exact agrees_total (.shiftRight rfl (.shiftRight left right))

/-- The check of the modifier after the setter, under the check's binders (the updated root, the
modified leaf, the right-hand side and the snapshot), agrees with the source: it writes exactly when
the source applies the operation, with the leaf, and otherwise fails with the source's panic. -/
theorem guard_agrees {type : TypeSystem.FixedInteger} {operator : Syntax.ValueAssignOp}
    (kind : FixedCompoundAssignmentOperator operator ∨ ShiftCompoundAssignmentOperator operator) (left right : Word) :
    Agreement (.fixed type) operator (some (.word left)) (.word right) (.word (leaf type operator left right))
      (SourceCoreDataPlaces.assignmentModifier (.fixed type) false operator) (.inRight leftType (.word left))
      (.word right) := by
  rcases kind with kind | shift
  rotate_left
  · exact shift_guard_agrees shift left right
  cases kind
  · exact agrees_checked .add .add .add (fun applied => .add rfl applied) (leaf_add type left right)
  · exact agrees_checked .subtract .subtract .subtract (fun applied => .subtract rfl applied)
      (leaf_subtract type left right)
  · exact agrees_checked .multiply .multiply .multiply (fun applied => .multiply rfl applied)
      (leaf_multiply type left right)
  · exact agrees_division .divide .divide .divide (fun applied => .divide rfl applied) (leaf_divide type)
  · exact agrees_division .modulo .modulo .modulo (fun applied => .modulo rfl applied) (leaf_modulo type)
  · exact agrees_total (.primitive (fun _ _ checked => by cases checked) (.bitAnd (.wordBitAnd left right)))
  · exact agrees_total (.primitive (fun _ _ checked => by cases checked) (.bitXor (.wordBitXor left right)))
  · exact agrees_total (.primitive (fun _ _ checked => by cases checked) (.bitOr (.wordBitOr left right)))
  · exact agrees_total (by
      rw [leaf_uncheckedAdd]
      exact .uncheckedAdd rfl (.unchecked .uncheckedAdd left right))
  · exact agrees_total (by
      rw [leaf_uncheckedSubtract]
      exact .uncheckedSubtract rfl (.unchecked .uncheckedSubtract left right))
  · exact agrees_total (by
      rw [leaf_uncheckedMultiply]
      exact .uncheckedMultiply rfl (.unchecked .uncheckedMultiply left right))
  · exact agrees_unchecked_division .uncheckedDivide .uncheckedDivide (fun zero => by
      rw [leaf_uncheckedDivide type zero]
      exact .uncheckedDivide rfl (.uncheckedDivision .uncheckedDivide left right zero))
      (.wordUncheckedDivide left)
  · exact agrees_unchecked_division .uncheckedModulo .uncheckedModulo (fun zero => by
      rw [leaf_uncheckedModulo type zero]
      exact .uncheckedModulo rfl (.uncheckedDivision .uncheckedModulo left right zero))
      (.wordUncheckedModulo left)

end Solcore.SourceSemantics.CoreLowering.FixedCompoundModifier
end

section
/-! In-place `~` at a fixed-width target. Both place compilers apply Word's `~` to the snapshot's
word, and at `uint8` … `uint128` keep its low `N` bits (`SourceCoreDataPlaces.bitNotWrap`), as the
source's `~` there does (`FixedUnaryApplies`). At the other fixed-width types the source's `~` is
Word's, which keeps a canonical word canonical. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering
open Frontend

/-- In-place `~`'s profile: a target whose metadata view is `word` or `integer`, or one of the twelve
fixed-width integer types at its own type, whose `~` the compiler wraps at `uint8` … `uint128`. -/
abbrev WideBitNotProfile (target : TypeSystem.Ty) : Prop :=
  (SourceCoreRawMetadata.runtimeType target = .word ∨ SourceCoreRawMetadata.runtimeType target = .integer) ∨
    ∃ type, target = .fixed type

/-- The accepted-body recognizers' targets for in-place `~`, `Word` and the twelve fixed-width types,
are of its profile. -/
theorem WideBitNotProfile.of_word_or_fixed {target : TypeSystem.Ty}
    (profile : target = .word ∨ ∃ type, target = .fixed type) : WideBitNotProfile target :=
  profile.imp_left fun word => .inl (by rw [word]; rfl)

end Solcore.SourceSemantics.CoreLowering

namespace Solcore.SourceSemantics.CoreLowering.FixedCompoundModifier
open Core Frontend DataEquality

/-- The word in-place `~` writes at a fixed-width target: Word's `~`, keeping only the low `N` bits
at `uint8` … `uint128`. -/
def bitNotLeaf (type : TypeSystem.FixedInteger) (word : Word) : Word :=
  if type.signed = false ∧ type.width ≠ .w256 then word.bitNot.bitAnd (Word.ofNatModulo (2 ^ type.width.bits - 1))
  else word.bitNot

private theorem bitNotWrap_narrow {width : TypeSystem.IntegerWidth} (narrow : width ≠ .w256) :
    SourceCoreDataPlaces.bitNotWrap (.fixed ⟨false, width⟩) = some ⟨false, width⟩ := by
  unfold SourceCoreDataPlaces.bitNotWrap TypeSystem.Ty.fixed
  simp [narrow]

private theorem bitNotWrap_wide {type : TypeSystem.FixedInteger}
    (wide : ¬ (type.signed = false ∧ type.width ≠ .w256)) :
    SourceCoreDataPlaces.bitNotWrap (.fixed type) = none := by
  unfold SourceCoreDataPlaces.bitNotWrap TypeSystem.Ty.fixed
  simp [wide]

/-- The data-place compiler's in-place `~` at a fixed-width target gives the leaf. -/
theorem bitNot_modified_evaluates {type : TypeSystem.FixedInteger} {environment : Environment}
    {snapshot rhs : Expr} {word : Word} (snapshotSelected : Selects environment snapshot (.inRight .unit (.word word)))
    (operator : Option SourceCoreDataPlaces.Modifier) (store : Store) (invalid : Word) :
    Evaluates environment store
      (SourceCoreDataPlaces.modified .word operator true snapshot rhs invalid
        (SourceCoreDataPlaces.bitNotWrap (.fixed type)))
      (.inRight .word (.word (bitNotLeaf type word))) store := by
  by_cases narrow : type.signed = false ∧ type.width ≠ .w256
  · obtain ⟨signed, width⟩ := type
    obtain ⟨unsigned, narrowWidth⟩ := narrow
    cases unsigned
    rw [bitNotWrap_narrow narrowWidth, bitNotLeaf, if_pos ⟨rfl, narrowWidth⟩]
    exact .caseRight (snapshotSelected.evaluates store) (.inRight (.binary (.unary (.var rfl) rfl) .word rfl))
  · rw [bitNotWrap_wide narrow, bitNotLeaf, if_neg narrow]
    exact .caseRight (snapshotSelected.evaluates store) (.inRight (.unary (.var rfl) rfl))

/-- So does the compatible compiler's. -/
theorem bitNot_compatible_modified_evaluates {type : TypeSystem.FixedInteger} {environment : Environment}
    {snapshot rhs : Expr} {word : Word} (snapshotSelected : Selects environment snapshot (.inRight .unit (.word word)))
    (operator : Option SourceCoreDataPlaces.Modifier) (store : Store) (invalid : Word) :
    Evaluates environment store
      (SourceCoreCompatibleDataPlaces.modified .word operator true snapshot rhs invalid
        (SourceCoreDataPlaces.bitNotWrap (.fixed type)))
      (.inRight .word (.word (bitNotLeaf type word))) store := by
  by_cases narrow : type.signed = false ∧ type.width ≠ .w256
  · obtain ⟨signed, width⟩ := type
    obtain ⟨unsigned, narrowWidth⟩ := narrow
    cases unsigned
    rw [bitNotWrap_narrow narrowWidth, bitNotLeaf, if_pos ⟨rfl, narrowWidth⟩]
    exact .caseRight (snapshotSelected.evaluates store) (.inRight (.binary (.unary (.var rfl) rfl) .word rfl))
  · rw [bitNotWrap_wide narrow, bitNotLeaf, if_neg narrow]
    exact .caseRight (snapshotSelected.evaluates store) (.inRight (.unary (.var rfl) rfl))

/-- The source's in-place `~` at a fixed-width target gives the leaf. -/
theorem bitNot_applies_leaf {type : TypeSystem.FixedInteger} {word : Word} {result : Dynamic.Value}
    (applied : Dynamic.BitNotAssignmentApplies (.fixed type) (some (.word word)) result) :
    result = .word (bitNotLeaf type word) := by
  cases applied with
  | primitive plain applies =>
    cases applies
    have wide : ¬ (type.signed = false ∧ type.width ≠ .w256) :=
      fun narrow => plain type rfl (.bitNot narrow.1 narrow.2)
    rw [bitNotLeaf, if_neg wide]
  | narrow same applies =>
    cases fixed_inj same
    cases applies with
    | narrowBitNot unsigned narrow =>
      rw [bitNotLeaf, if_pos ⟨unsigned, narrow⟩]
      rfl

/-- The source's in-place `~` at a fixed-width target applies, with the leaf. -/
theorem bitNot_applies (type : TypeSystem.FixedInteger) (word : Word) :
    Dynamic.BitNotAssignmentApplies (.fixed type) (some (.word word)) (.word (bitNotLeaf type word)) := by
  by_cases narrow : type.signed = false ∧ type.width ≠ .w256
  · rw [bitNotLeaf, if_pos narrow]
    exact .narrow rfl (.narrowBitNot narrow.1 narrow.2 word)
  · rw [bitNotLeaf, if_neg narrow]
    refine .primitive (fun other same kind => ?_) (.word word)
    cases fixed_inj same
    cases kind with
    | bitNot unsigned narrowWidth => exact narrow ⟨unsigned, narrowWidth⟩

/-- In-place `~` keeps the target's word canonical for the type. -/
theorem bitNot_canonical {type : TypeSystem.FixedInteger} {word : Word}
    (canonical : type.canonical word.val = true) : type.canonical (bitNotLeaf type word).val = true := by
  by_cases narrow : type.signed = false ∧ type.width ≠ .w256
  · rw [bitNotLeaf, if_pos narrow]
    exact Dynamic.fixed_canonical_narrowBitNot narrow.1 narrow.2 word
  · rw [bitNotLeaf, if_neg narrow]
    refine Dynamic.fixed_canonical_bitNot ?_ canonical
    cases signed : type.signed
    · by_cases full : type.width = .w256
      · exact .full full
      · exact absurd ⟨signed, full⟩ narrow
    · exact .signed signed

/-- A word is never an invalid operand of `~`. -/
theorem bitNot_word_valid (word : Word) : ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot (.word word) :=
  fun invalid => invalid.excludes_application ⟨_, .wordBitNot word⟩

end Solcore.SourceSemantics.CoreLowering.FixedCompoundModifier
end
