import Solcore.Core.Primitive
import Solcore.Synthesis.Source.ScalarMeaning.Semantics

/-! The Core Word operations reached only through raw `std.opcodes` aliases
agree with the independent EVM operations of the source semantics. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

theorem evm_div (left right : Solcore.Core.Word) :
    Evm.div left.val right.val = (left.udiv right).val := by
  unfold Evm.div Solcore.Core.Word.udiv
  split <;> simp_all [Solcore.Core.Word.zero]

theorem evm_mod (left right : Solcore.Core.Word) :
    Evm.mod left.val right.val = (left.umod right).val := by
  unfold Evm.mod Solcore.Core.Word.umod
  split <;> simp_all [Solcore.Core.Word.zero]

theorem evm_shl (shift value : Solcore.Core.Word) :
    Evm.shl shift.val value.val = (value.shiftLeft shift).val := by
  unfold Evm.shl Solcore.Core.Word.shiftLeft
  split
  · simp [Nat.shiftLeft_eq, Evm.modulus, Solcore.Core.wordModulus]
  · simp [Solcore.Core.Word.zero]

theorem evm_shr (shift value : Solcore.Core.Word) :
    Evm.shr shift.val value.val = (value.shiftRight shift).val := by
  unfold Evm.shr Solcore.Core.Word.shiftRight
  split
  · simp [Nat.shiftRight_eq_div_pow]
  · simp [Solcore.Core.Word.zero]

theorem evm_clz (value : Solcore.Core.Word) :
    Evm.clz value.val = value.clz.val := by
  unfold Evm.clz Solcore.Core.Word.clz
  split
  · simp only [Solcore.Core.Word.ofNatModulo, Solcore.Core.wordModulus]
  · simp only [Solcore.Core.Word.ofNatModulo, Solcore.Core.wordModulus]
    exact (Nat.mod_eq_of_lt (by omega)).symm

theorem evm_byte (index value : Solcore.Core.Word) :
    Evm.byte index.val value.val = (index.byteAt value).val := by
  unfold Evm.byte Solcore.Core.Word.byteAt
  split
  · simp only [Solcore.Core.Word.ofNatModulo, Solcore.Core.wordModulus]
    rw [Nat.pow_mul]
    exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))).symm
  · simp [Solcore.Core.Word.zero]

theorem evm_addmod (left right divisor : Solcore.Core.Word) :
    Evm.addmod left.val right.val divisor.val = (left.addMod right divisor).val := by
  unfold Evm.addmod Solcore.Core.Word.addMod
  split
  · simp [Solcore.Core.Word.zero]
  · have bound := divisor.isLt
    simp only [Solcore.Core.Word.ofNatModulo]
    exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by omega)) bound)).symm

theorem evm_mulmod (left right divisor : Solcore.Core.Word) :
    Evm.mulmod left.val right.val divisor.val = (left.mulMod right divisor).val := by
  unfold Evm.mulmod Solcore.Core.Word.mulMod
  split
  · simp [Solcore.Core.Word.zero]
  · have bound := divisor.isLt
    simp only [Solcore.Core.Word.ofNatModulo]
    exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by omega)) bound)).symm

/-! ### Signed and exponent operations: EVM side -/

namespace Evm

theorem toSigned_of_lt (word : Nat) (small : word < 2 ^ 255) :
    toSigned word = (word : Int) := by
  rw [toSigned, if_pos small]

theorem toSigned_of_ge (word : Nat) (large : ¬ word < 2 ^ 255)
    (bound : word < 2 ^ 256) :
    toSigned word = Int.negSucc (2 ^ 256 - 1 - word) := by
  rw [toSigned, if_neg large, Int.negSucc_eq, modulus]
  omega

theorem ofSigned_cast (value : Nat) (bound : value < 2 ^ 256) :
    ofSigned (value : Int) = value := by
  rw [ofSigned, modulus]
  omega

theorem ofSigned_neg_cast (value : Nat) (bound : value < 2 ^ 256) :
    ofSigned (-(value : Int)) = (2 ^ 256 - value) % 2 ^ 256 := by
  rw [ofSigned, modulus]
  omega

theorem ofSigned_negSucc (value : Nat) (bound : value < 2 ^ 256) :
    ofSigned (Int.negSucc value) = 2 ^ 256 - 1 - value := by
  rw [ofSigned, modulus, Int.negSucc_eq]
  omega

theorem tdiv_cast_cast (a b : Nat) :
    Int.tdiv (a : Int) (b : Int) = ((a / b : Nat) : Int) := rfl

theorem tdiv_cast_negSucc (a b : Nat) :
    Int.tdiv (a : Int) (Int.negSucc b) = -((a / (b + 1) : Nat) : Int) := rfl

theorem tdiv_negSucc_cast (a b : Nat) :
    Int.tdiv (Int.negSucc a) (b : Int) = -(((a + 1) / b : Nat) : Int) := rfl

theorem tdiv_negSucc_negSucc (a b : Nat) :
    Int.tdiv (Int.negSucc a) (Int.negSucc b) = (((a + 1) / (b + 1) : Nat) : Int) := rfl

theorem tmod_cast_cast (a b : Nat) :
    Int.tmod (a : Int) (b : Int) = ((a % b : Nat) : Int) := rfl

theorem tmod_cast_negSucc (a b : Nat) :
    Int.tmod (a : Int) (Int.negSucc b) = ((a % (b + 1) : Nat) : Int) := rfl

theorem tmod_negSucc_cast (a b : Nat) :
    Int.tmod (Int.negSucc a) (b : Int) = -(((a + 1) % b : Nat) : Int) := rfl

theorem tmod_negSucc_negSucc (a b : Nat) :
    Int.tmod (Int.negSucc a) (Int.negSucc b) = -(((a + 1) % (b + 1) : Nat) : Int) := rfl

theorem cast_ediv_cast (a b : Nat) : (a : Int) / (b : Int) = ((a / b : Nat) : Int) := rfl

theorem negSucc_ediv_cast (a b : Nat) (positive : 0 < b) :
    Int.negSucc a / (b : Int) = Int.negSucc (a / b) := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  rfl

theorem bne_false_false : (false != false) = false := rfl

theorem bne_false_true : (false != true) = true := rfl

theorem bne_true_false : (true != false) = true := rfl

theorem bne_true_true : (true != true) = false := rfl

theorem bnot_ite_beq_zero (condition : Prop) [Decidable condition] :
    (!((if condition then 1 else 0 : Nat) == 0)) = decide condition := by
  by_cases h : condition
  · rw [if_pos h, decide_eq_true h]
    rfl
  · rw [if_neg h, decide_eq_false h]
    rfl

end Evm

/-! ### Signed and exponent operations: Core side

Facts about the Core Word operations, kept outside the Core namespace. -/

namespace CoreWord

open Solcore.Core Solcore.Core.Word

theorem ofNatModulo_val (value : Nat) : (ofNatModulo value).val = value % 2 ^ 256 := rfl

theorem zero_val : zero.val = 0 := rfl

theorem maximum_val : maximum.val = 2 ^ 256 - 1 := rfl

theorem signedNegative_of_lt (value : Word) (small : value.val < 2 ^ 255) :
    value.signedNegative = false := by
  rw [signedNegative, decide_eq_false (Nat.not_le_of_lt small)]

theorem signedNegative_of_ge (value : Word) (large : ¬ value.val < 2 ^ 255) :
    value.signedNegative = true := by
  rw [signedNegative, decide_eq_true (Nat.le_of_not_lt large)]

theorem signedMagnitude_of_lt (value : Word) (small : value.val < 2 ^ 255) :
    value.signedMagnitude = value.val := by
  rw [signedMagnitude, signedNegative_of_lt value small, if_neg Bool.false_ne_true]

theorem signedMagnitude_of_ge (value : Word) (large : ¬ value.val < 2 ^ 255) :
    value.signedMagnitude = 2 ^ 256 - value.val := by
  rw [signedMagnitude, signedNegative_of_ge value large, if_pos rfl]
  rfl

theorem ofSignedMagnitude_false_val (magnitude : Nat) :
    (ofSignedMagnitude false magnitude).val = magnitude % 2 ^ 256 := rfl

theorem ofSignedMagnitude_true_val (magnitude : Nat) :
    (ofSignedMagnitude true magnitude).val = (2 ^ 256 - magnitude) % 2 ^ 256 := rfl

theorem shiftArithmeticRight_neg_val (value shift : Word) (small : shift.val < 256)
    (negative : ¬ value.val < 2 ^ 255) :
    (value.shiftArithmeticRight shift).val =
      (2 ^ 256 - 1 - (2 ^ 256 - 1 - value.val) / 2 ^ shift.val) % 2 ^ 256 := by
  rw [shiftArithmeticRight, if_pos small, if_neg negative]
  rfl

theorem signExtend_small_clear_val (index value : Word) (small : index.val < 32)
    (clear : value.val % 2 ^ (8 * (index.val + 1)) < 2 ^ (8 * (index.val + 1) - 1)) :
    (index.signExtend value).val = value.val % 2 ^ (8 * (index.val + 1)) % 2 ^ 256 := by
  rw [signExtend, if_pos small]
  dsimp only
  rw [if_pos clear]
  rfl

theorem signExtend_small_set_val (index value : Word) (small : index.val < 32)
    (set : ¬ value.val % 2 ^ (8 * (index.val + 1)) < 2 ^ (8 * (index.val + 1) - 1)) :
    (index.signExtend value).val =
      (2 ^ 256 - 2 ^ (8 * (index.val + 1)) + value.val % 2 ^ (8 * (index.val + 1))) %
        2 ^ 256 := by
  rw [signExtend, if_pos small]
  dsimp only
  rw [if_neg set]
  rfl

theorem signExtend_large (index value : Word) (large : ¬ index.val < 32) :
    index.signExtend value = value := by
  rw [signExtend, if_neg large]

theorem modularPowLoop_val (base accumulator exponent : Nat) :
    modularPowLoop base accumulator exponent = accumulator * base ^ exponent % 2 ^ 256 := by
  induction exponent using Nat.strongRecOn generalizing base accumulator with
  | ind exponent ih =>
    rw [modularPowLoop]
    have modulusEq : wordModulus = 2 ^ 256 := rfl
    by_cases zero : exponent = 0
    · rw [dif_pos zero, zero, Nat.pow_zero, Nat.mul_one, modulusEq]
    · rw [dif_neg zero]
      dsimp only
      rw [ih (exponent / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)),
        modulusEq]
      by_cases odd : exponent % 2 = 1
      · rw [if_pos odd, Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod,
          Nat.mul_pow]
        generalize split : exponent / 2 = half
        rw [(by omega : exponent = Nat.succ (half + half)), Nat.pow_succ base (half + half),
          Nat.pow_add base half half]
        ac_rfl
      · rw [if_neg odd, Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod,
          Nat.mul_pow]
        generalize split : exponent / 2 = half
        rw [(by omega : exponent = half + half), Nat.pow_add base half half]

end CoreWord

/-! ### Signed and exponent operations: agreement -/

open Solcore.Core in
theorem evm_sdiv (left right : Word) : Evm.sdiv left.val right.val = (left.sdiv right).val := by
  have leftBound : left.val < 2 ^ 256 := left.isLt
  have rightBound : right.val < 2 ^ 256 := right.isLt
  by_cases zero : right.val = 0
  · rw [Evm.sdiv, if_pos zero, Word.sdiv, if_pos zero, CoreWord.zero_val]
  · rw [Evm.sdiv, if_neg zero, Word.sdiv, if_neg zero]
    by_cases leftSmall : left.val < 2 ^ 255 <;> by_cases rightSmall : right.val < 2 ^ 255
    · rw [Evm.toSigned_of_lt _ leftSmall, Evm.toSigned_of_lt _ rightSmall, Evm.tdiv_cast_cast,
        Evm.ofSigned_cast _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leftBound),
        CoreWord.signedNegative_of_lt _ leftSmall, CoreWord.signedNegative_of_lt _ rightSmall,
        CoreWord.signedMagnitude_of_lt _ leftSmall, CoreWord.signedMagnitude_of_lt _ rightSmall,
        Evm.bne_false_false, CoreWord.ofSignedMagnitude_false_val,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leftBound)]
    · rw [Evm.toSigned_of_lt _ leftSmall, Evm.toSigned_of_ge _ rightSmall rightBound,
        Evm.tdiv_cast_negSucc,
        (by omega : 2 ^ 256 - 1 - right.val + 1 = 2 ^ 256 - right.val),
        Evm.ofSigned_neg_cast _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leftBound),
        CoreWord.signedNegative_of_lt _ leftSmall, CoreWord.signedNegative_of_ge _ rightSmall,
        CoreWord.signedMagnitude_of_lt _ leftSmall, CoreWord.signedMagnitude_of_ge _ rightSmall,
        Evm.bne_false_true, CoreWord.ofSignedMagnitude_true_val]
    · rw [Evm.toSigned_of_ge _ leftSmall leftBound, Evm.toSigned_of_lt _ rightSmall,
        Evm.tdiv_negSucc_cast,
        (by omega : 2 ^ 256 - 1 - left.val + 1 = 2 ^ 256 - left.val),
        Evm.ofSigned_neg_cast ((2 ^ 256 - left.val) / right.val)
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)),
        CoreWord.signedNegative_of_ge _ leftSmall, CoreWord.signedNegative_of_lt _ rightSmall,
        CoreWord.signedMagnitude_of_ge _ leftSmall, CoreWord.signedMagnitude_of_lt _ rightSmall,
        Evm.bne_true_false, CoreWord.ofSignedMagnitude_true_val]
    · rw [Evm.toSigned_of_ge _ leftSmall leftBound, Evm.toSigned_of_ge _ rightSmall rightBound,
        Evm.tdiv_negSucc_negSucc,
        (by omega : 2 ^ 256 - 1 - left.val + 1 = 2 ^ 256 - left.val),
        (by omega : 2 ^ 256 - 1 - right.val + 1 = 2 ^ 256 - right.val),
        Evm.ofSigned_cast ((2 ^ 256 - left.val) / (2 ^ 256 - right.val))
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)),
        CoreWord.signedNegative_of_ge _ leftSmall, CoreWord.signedNegative_of_ge _ rightSmall,
        CoreWord.signedMagnitude_of_ge _ leftSmall, CoreWord.signedMagnitude_of_ge _ rightSmall,
        Evm.bne_true_true, CoreWord.ofSignedMagnitude_false_val,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
          (by omega : 2 ^ 256 - left.val < 2 ^ 256))]

open Solcore.Core in
theorem evm_smod (left right : Word) : Evm.smod left.val right.val = (left.smod right).val := by
  have leftBound : left.val < 2 ^ 256 := left.isLt
  have rightBound : right.val < 2 ^ 256 := right.isLt
  by_cases zero : right.val = 0
  · rw [Evm.smod, if_pos zero, Word.smod, if_pos zero, CoreWord.zero_val]
  · rw [Evm.smod, if_neg zero, Word.smod, if_neg zero]
    by_cases leftSmall : left.val < 2 ^ 255 <;> by_cases rightSmall : right.val < 2 ^ 255
    · rw [Evm.toSigned_of_lt _ leftSmall, Evm.toSigned_of_lt _ rightSmall, Evm.tmod_cast_cast,
        Evm.ofSigned_cast _ (Nat.lt_of_le_of_lt (Nat.mod_le _ _) leftBound),
        CoreWord.signedNegative_of_lt _ leftSmall, CoreWord.signedMagnitude_of_lt _ leftSmall,
        CoreWord.signedMagnitude_of_lt _ rightSmall, CoreWord.ofSignedMagnitude_false_val,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) leftBound)]
    · rw [Evm.toSigned_of_lt _ leftSmall, Evm.toSigned_of_ge _ rightSmall rightBound,
        Evm.tmod_cast_negSucc,
        (by omega : 2 ^ 256 - 1 - right.val + 1 = 2 ^ 256 - right.val),
        Evm.ofSigned_cast _ (Nat.lt_of_le_of_lt (Nat.mod_le _ _) leftBound),
        CoreWord.signedNegative_of_lt _ leftSmall, CoreWord.signedMagnitude_of_lt _ leftSmall,
        CoreWord.signedMagnitude_of_ge _ rightSmall, CoreWord.ofSignedMagnitude_false_val,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) leftBound)]
    · rw [Evm.toSigned_of_ge _ leftSmall leftBound, Evm.toSigned_of_lt _ rightSmall,
        Evm.tmod_negSucc_cast,
        (by omega : 2 ^ 256 - 1 - left.val + 1 = 2 ^ 256 - left.val),
        Evm.ofSigned_neg_cast ((2 ^ 256 - left.val) % right.val)
          (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)),
        CoreWord.signedNegative_of_ge _ leftSmall, CoreWord.signedMagnitude_of_ge _ leftSmall,
        CoreWord.signedMagnitude_of_lt _ rightSmall, CoreWord.ofSignedMagnitude_true_val]
    · rw [Evm.toSigned_of_ge _ leftSmall leftBound, Evm.toSigned_of_ge _ rightSmall rightBound,
        Evm.tmod_negSucc_negSucc,
        (by omega : 2 ^ 256 - 1 - left.val + 1 = 2 ^ 256 - left.val),
        (by omega : 2 ^ 256 - 1 - right.val + 1 = 2 ^ 256 - right.val),
        Evm.ofSigned_neg_cast ((2 ^ 256 - left.val) % (2 ^ 256 - right.val))
          (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)),
        CoreWord.signedNegative_of_ge _ leftSmall, CoreWord.signedMagnitude_of_ge _ leftSmall,
        CoreWord.signedMagnitude_of_ge _ rightSmall, CoreWord.ofSignedMagnitude_true_val]

open Solcore.Core in
theorem evm_sgt (left right : Word) :
    (!(Evm.sgt left.val right.val == 0)) = left.signedGt right := by
  have leftBound : left.val < 2 ^ 256 := left.isLt
  have rightBound : right.val < 2 ^ 256 := right.isLt
  rw [Evm.sgt, Evm.bnot_ite_beq_zero, Word.signedGt]
  by_cases leftSmall : left.val < 2 ^ 255 <;> by_cases rightSmall : right.val < 2 ^ 255
  · rw [Evm.toSigned_of_lt _ leftSmall, Evm.toSigned_of_lt _ rightSmall, if_pos leftSmall,
      if_pos rightSmall, decide_eq_decide]
    exact Int.ofNat_lt
  · rw [Evm.toSigned_of_lt _ leftSmall, Evm.toSigned_of_ge _ rightSmall rightBound,
      if_pos leftSmall, if_neg rightSmall, decide_eq_true_eq, Int.negSucc_eq]
    omega
  · rw [Evm.toSigned_of_ge _ leftSmall leftBound, Evm.toSigned_of_lt _ rightSmall,
      if_neg leftSmall, if_pos rightSmall, decide_eq_false_iff_not, Int.negSucc_eq]
    omega
  · rw [Evm.toSigned_of_ge _ leftSmall leftBound, Evm.toSigned_of_ge _ rightSmall rightBound,
      if_neg leftSmall, if_neg rightSmall, decide_eq_decide, Int.negSucc_eq, Int.negSucc_eq,
      gt_iff_lt, Fin.lt_def]
    constructor <;> intro h <;> omega

open Solcore.Core in
theorem evm_sar (value shift : Word) :
    Evm.sar shift.val value.val = (value.shiftArithmeticRight shift).val := by
  have valueBound : value.val < 2 ^ 256 := value.isLt
  by_cases small : shift.val < 256
  · by_cases nonnegative : value.val < 2 ^ 255
    · rw [Evm.sar, if_pos small, Evm.toSigned_of_lt _ nonnegative, Evm.cast_ediv_cast,
        Evm.ofSigned_cast _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) valueBound),
        Word.shiftArithmeticRight, if_pos small, if_pos nonnegative, CoreWord.ofNatModulo_val,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) valueBound)]
    · rw [Evm.sar, if_pos small, Evm.toSigned_of_ge _ nonnegative valueBound,
        Evm.negSucc_ediv_cast _ _ (Nat.two_pow_pos _),
        Evm.ofSigned_negSucc ((2 ^ 256 - 1 - value.val) / 2 ^ shift.val)
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)),
        CoreWord.shiftArithmeticRight_neg_val value shift small nonnegative,
        Nat.mod_eq_of_lt
          (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by omega : 2 ^ 256 - 1 < 2 ^ 256))]
  · by_cases nonnegative : value.val < 2 ^ 255
    · rw [Evm.sar, if_neg small, Evm.toSigned_of_lt _ nonnegative,
        if_neg (by omega : ¬ ((value.val : Nat) : Int) < 0),
        Word.shiftArithmeticRight, if_neg small, if_pos nonnegative, CoreWord.zero_val]
    · rw [Evm.sar, if_neg small, Evm.toSigned_of_ge _ nonnegative valueBound,
        if_pos (Int.negSucc_lt_zero _),
        Word.shiftArithmeticRight, if_neg small, if_neg nonnegative, CoreWord.maximum_val,
        Evm.modulus]

open Solcore.Core in
theorem evm_signextend (index value : Word) :
    Evm.signextend index.val value.val = (index.signExtend value).val := by
  have valueBound : value.val < 2 ^ 256 := value.isLt
  by_cases small : index.val < 31
  · have small32 : index.val < 32 := by omega
    have widthLe : 2 ^ (8 * (index.val + 1)) ≤ 2 ^ 248 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have lowLt : value.val % 2 ^ (8 * (index.val + 1)) < 2 ^ (8 * (index.val + 1)) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [Evm.signextend, if_pos small]
    dsimp only
    by_cases clear : value.val % 2 ^ (8 * (index.val + 1)) < 2 ^ (8 * (index.val + 1) - 1)
    · rw [if_pos clear, CoreWord.signExtend_small_clear_val index value small32 clear,
        Nat.mod_eq_of_lt (by omega : value.val % 2 ^ (8 * (index.val + 1)) < 2 ^ 256)]
    · rw [if_neg clear, CoreWord.signExtend_small_set_val index value small32 clear, Evm.modulus]
      omega
  · by_cases small32 : index.val < 32
    · have index31 : index.val = 31 := by omega
      rw [Evm.signextend, if_neg small, Word.signExtend, if_pos small32]
      dsimp only
      rw [index31, (rfl : 8 * (31 + 1) = 256), (rfl : 256 - 1 = 255),
        Nat.mod_eq_of_lt valueBound]
      by_cases nonnegative : value.val < 2 ^ 255
      · rw [if_pos nonnegative, CoreWord.ofNatModulo_val, Nat.mod_eq_of_lt valueBound]
      · rw [if_neg nonnegative, CoreWord.ofNatModulo_val]
        have modulusEq : wordModulus = 2 ^ 256 := rfl
        omega
    · rw [Evm.signextend, if_neg small, CoreWord.signExtend_large index value small32]

theorem powMod_spec (base exponent : Nat) :
    Evm.powMod base exponent = base ^ exponent % Evm.modulus := by
  induction exponent using Nat.strongRecOn with
  | ind exponent ih =>
    rw [Evm.powMod]
    by_cases zero : exponent = 0
    · rw [dif_pos zero, zero, Nat.pow_zero]
    · rw [dif_neg zero]
      dsimp only
      rw [ih (exponent / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide))]
      by_cases even : exponent % 2 = 0
      · rw [if_pos even, ← Nat.mul_mod, ← Nat.pow_add,
          (by omega : exponent / 2 + exponent / 2 = exponent)]
      · rw [if_neg even,
          ← Nat.mul_mod (base ^ (exponent / 2)) (base ^ (exponent / 2)) Evm.modulus,
          ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_succ,
          (by omega : (exponent / 2 + exponent / 2).succ = exponent)]

open Solcore.Core in
theorem evm_exp (base exponent : Word) :
    Evm.exp base.val exponent.val = (base.pow exponent).val := by
  rw [Evm.exp, powMod_spec, Word.pow, CoreWord.ofNatModulo_val, CoreWord.modularPowLoop_val,
    Nat.one_mul, Nat.mod_mod]
  rfl

end Solcore.Synthesis.Source.ScalarMeaning
