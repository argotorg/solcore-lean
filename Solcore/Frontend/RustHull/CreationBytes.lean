import Solcore.Frontend.RustHull.CreationAddressSemantics
import Solcore.Core.ByteSelection

/-! Byte reads of the source memory after byte and word writes, and the
independence of Keccak absorption from bytes outside the absorbed range. The
proofs compare individual bits of the packed big-endian words. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationBytes
open Core


theorem modulus : wordModulus = 2 ^ 256 := rfl

theorem val_small {n : Nat} (small : n < 2 ^ 256) : (Word.ofNatModulo n).val = n := Nat.mod_eq_of_lt small

theorem val_bitAnd (a b : Word) : (a.bitAnd b).val = a.val &&& b.val :=
  Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ b.isLt)

theorem val_bitOr (a b : Word) : (a.bitOr b).val = a.val ||| b.val :=
  Nat.mod_eq_of_lt (Nat.or_lt_two_pow a.isLt b.isLt)

theorem val_bitNot (a : Word) : a.bitNot.val = 2 ^ 256 - (a.val + 1) := by
  show (Word.maximum - a).val = _
  rw [Fin.sub_val_of_le (Fin.le_def.mpr (by show a.val ≤ wordModulus - 1; have := a.isLt; omega))]
  show wordModulus - 1 - a.val = _
  have := a.isLt
  change a.val < 2 ^ 256 at this
  change 2 ^ 256 - 1 - a.val = _
  omega

theorem val_shiftLeft (a s : Word) (small : s.val < 256) : (a.shiftLeft s).val = (a.val <<< s.val) % 2 ^ 256 := by
  simp only [Word.shiftLeft, small, ↓reduceIte]; rfl

theorem val_shiftRight (a s : Word) (small : s.val < 256) : (a.shiftRight s).val = a.val >>> s.val := by
  simp only [Word.shiftRight, small, ↓reduceIte]
  show (a.val >>> s.val) % wordModulus = _
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.isLt)

theorem val_byteAt (i a : Word) (small : i.val < 32) :
    (Word.byteAt i a).val = a.val / 2 ^ (8 * (31 - i.val)) % 2 ^ 8 := by
  simp only [Word.byteAt, small, ↓reduceIte]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem testBit_word (a : Word) {i : Nat} (large : 256 ≤ i) : a.val.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) large))

/-- Byte `lane` of a word equals byte `lane'` of another when their bits agree there. -/
theorem byte_eq {x y : Nat} {s s' : Nat} (agree : ∀ t, t < 8 → x.testBit (s + t) = y.testBit (s' + t)) :
    x / 2 ^ s % 2 ^ 8 = y / 2 ^ s' % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases small : t < 8
  · simp only [small, decide_true, Bool.true_and]
    rw [Nat.add_comm t s, Nat.add_comm t s']
    exact agree t small
  · simp [small]


theorem lookup_insert_same (key value : Word) (entries : MemorySemantics.Entries) :
    MemorySemantics.lookup key (MemorySemantics.insert key value entries) = value := by
  induction entries with
  | nil => simp [MemorySemantics.insert, MemorySemantics.lookup]
  | cons entry rest ih =>
    rcases entry with ⟨stored, old⟩
    simp only [MemorySemantics.insert]
    split <;> simp_all [MemorySemantics.lookup]

theorem lookup_insert_other {key other : Word} (different : other ≠ key) (value : Word)
    (entries : MemorySemantics.Entries) :
    MemorySemantics.lookup other (MemorySemantics.insert key value entries) = MemorySemantics.lookup other entries := by
  induction entries with
  | nil => simp [MemorySemantics.insert, MemorySemantics.lookup, different]
  | cons entry rest ih =>
    rcases entry with ⟨stored, old⟩
    simp only [MemorySemantics.insert]
    by_cases same : key = stored
    · subst same
      simp [MemorySemantics.lookup, different]
    · simp only [beq_iff_eq, same, ↓reduceIte, MemorySemantics.lookup, ih]

theorem val_index (offset : Word) : (MemorySemantics.index offset).val = offset.val / 32 := by
  simp only [MemorySemantics.index, Word.udiv]
  rw [if_neg (by decide)]
  rfl

theorem val_position (offset : Word) : (MemorySemantics.position offset).val = offset.val % 32 := by
  simp only [MemorySemantics.position, Word.umod]
  rw [if_neg (by decide)]
  rfl

theorem testBit_lane (x s t : Nat) : (x / 2 ^ s % 2 ^ 8).testBit t = (decide (t < 8) && x.testBit (s + t)) := by
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm t s]

theorem testBit_255 (t : Nat) : (255 : Nat).testBit t = decide (t < 8) := by
  simpa using Nat.testBit_two_pow_sub_one 8 t

theorem val_distance (offset : Word) :
    (((Word.ofNatModulo 31).sub (MemorySemantics.position offset)).mul (Word.ofNatModulo 8)).val =
      8 * (31 - offset.val % 32) := by
  have thirtyOne : (Word.ofNatModulo 31).val = 31 := Nat.mod_eq_of_lt (by decide)
  have eight : (Word.ofNatModulo 8).val = 8 := Nat.mod_eq_of_lt (by decide)
  have below : offset.val % 32 < 32 := Nat.mod_lt _ (by decide)
  have small : (MemorySemantics.position offset) ≤ Word.ofNatModulo 31 := by
    rw [Fin.le_def, val_position, thirtyOne]; omega
  show ((Word.ofNatModulo 31 - MemorySemantics.position offset).val * (Word.ofNatModulo 8).val) % wordModulus = _
  rw [Fin.sub_val_of_le small, val_position, thirtyOne, eight]
  rw [Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
  omega

theorem readByte_writeByte_same (entries : MemorySemantics.Entries) (offset value : Word) :
    MemoryCopySemantics.readByte (MemorySemantics.writeByte entries offset value) offset =
      value.bitAnd (Word.ofNatModulo 255) := by
  have positionSmall : (MemorySemantics.position offset).val < 32 := by
    rw [val_position]; exact Nat.mod_lt _ (by decide)
  have distance := val_distance offset
  unfold MemoryCopySemantics.readByte MemorySemantics.writeByte
  simp only [lookup_insert_same]
  apply Fin.ext
  rw [val_byteAt _ _ positionSmall, val_bitAnd, val_position, val_bitOr, val_bitAnd, val_bitNot,
    val_shiftLeft _ _ (by rw [distance]; omega), val_shiftLeft _ _ (by rw [distance]; omega), val_bitAnd, distance,
    val_small (show 255 < 2 ^ 256 by decide)]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_lane]
  by_cases small : t < 8
  · have lane : 8 * (31 - offset.val % 32) + t < 256 := by omega
    simp only [small, decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_and,
      Nat.testBit_two_pow_sub_succ (Nat.mod_lt _ (by decide) : _ < 2 ^ 256), Nat.testBit_mod_two_pow,
      Nat.testBit_shiftLeft, lane, ge_iff_le, Nat.le_add_right, Nat.add_sub_cancel_left]
    simp only [testBit_255, small, decide_true, Bool.and_true, Bool.not_true, Bool.and_false, Bool.false_or]
  · simp [small, Nat.testBit_and, testBit_255]


theorem index_ne_of {offset other : Word} (different : (MemorySemantics.index other).val ≠ (MemorySemantics.index offset).val) :
    MemorySemantics.index other ≠ MemorySemantics.index offset := fun same => different (congrArg Fin.val same)

theorem readByte_writeByte_other (entries : MemorySemantics.Entries) {offset other : Word} (value : Word)
    (different : other ≠ offset) :
    MemoryCopySemantics.readByte (MemorySemantics.writeByte entries offset value) other =
      MemoryCopySemantics.readByte entries other := by
  have distance := val_distance offset
  have otherSmall : (MemorySemantics.position other).val < 32 := by
    rw [val_position]; exact Nat.mod_lt _ (by decide)
  unfold MemoryCopySemantics.readByte MemorySemantics.writeByte
  by_cases sameIndex : other.val / 32 = offset.val / 32
  · have keys : MemorySemantics.index other = MemorySemantics.index offset := Fin.ext (by rw [val_index, val_index, sameIndex])
    rw [keys, lookup_insert_same]
    have lanes : other.val % 32 ≠ offset.val % 32 := by
      intro same
      apply different
      apply Fin.ext
      have := Nat.div_add_mod other.val 32
      have := Nat.div_add_mod offset.val 32
      omega
    apply Fin.ext
    rw [val_byteAt _ _ otherSmall, val_byteAt _ _ otherSmall, val_position, val_bitOr, val_bitAnd, val_bitNot,
      val_shiftLeft _ _ (by rw [distance]; omega), val_shiftLeft _ _ (by rw [distance]; omega), val_bitAnd, distance,
      val_small (show 255 < 2 ^ 256 by decide)]
    apply Nat.eq_of_testBit_eq
    intro t
    rw [testBit_lane, testBit_lane]
    by_cases small : t < 8
    · have bound : 8 * (31 - other.val % 32) + t < 256 := by omega
      have otherLane := Nat.mod_lt other.val (show 32 > 0 by decide)
      have offsetLane := Nat.mod_lt offset.val (show 32 > 0 by decide)
      simp only [small, decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_and,
        Nat.testBit_two_pow_sub_succ (Nat.mod_lt _ (by decide) : _ < 2 ^ 256), Nat.testBit_mod_two_pow,
        Nat.testBit_shiftLeft, bound, testBit_255]
      by_cases above : 8 * (31 - offset.val % 32) ≤ 8 * (31 - other.val % 32) + t
      · have far : ¬(8 * (31 - other.val % 32) + t - 8 * (31 - offset.val % 32) < 8) := by omega
        simp [above, far]
      · simp [above]
    · simp [small]
  · rw [lookup_insert_other (index_ne_of (by rw [val_index, val_index]; exact sameIndex))]


theorem testBit_ones (k : Nat) : (2 ^ 256 - 1).testBit k = decide (k < 256) := Nat.testBit_two_pow_sub_one 256 k

/-- Lane `lane` of `(first & ~mask) | (value >> 8r)` with `mask = ones >> 8r`. -/
theorem lane_high (first value : Word) {r lane : Nat} (rSmall : r < 32) (laneSmall : lane < 32) :
    (first.val &&& (2 ^ 256 - ((2 ^ 256 - 1) >>> (8 * r) + 1)) ||| value.val >>> (8 * r)) / 2 ^ (8 * (31 - lane)) % 2 ^ 8 =
      if r ≤ lane then value.val / 2 ^ (8 * (31 - (lane - r))) % 2 ^ 8
      else first.val / 2 ^ (8 * (31 - lane)) % 2 ^ 8 := by
  have maskSmall : (2 ^ 256 - 1) >>> (8 * r) < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by decide)
  split
  · apply byte_eq
    intro t small
    have bound : 8 * (31 - lane) + t < 256 := by omega
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_two_pow_sub_succ maskSmall, Nat.testBit_shiftRight,
      testBit_ones, bound]
    have inside : 8 * r + (8 * (31 - lane) + t) < 256 := by omega
    simp only [inside, decide_true, Bool.not_true, Bool.and_false, Bool.false_or]
    congr 1
    omega
  · apply byte_eq
    intro t small
    have bound : 8 * (31 - lane) + t < 256 := by omega
    have outside : ¬(8 * r + (8 * (31 - lane) + t) < 256) := by omega
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_two_pow_sub_succ maskSmall, Nat.testBit_shiftRight,
      testBit_ones, bound, outside, decide_true, decide_false, Bool.not_false, Bool.and_true]
    rw [testBit_word value (by omega), Bool.or_false]

/-- Lane `lane` of `(second & mask) | (value << (256 - 8r))`. -/
theorem lane_low (second value : Word) {r lane : Nat} (rPositive : 0 < r) (rSmall : r < 32) (laneSmall : lane < 32) :
    (second.val &&& (2 ^ 256 - 1) >>> (8 * r) ||| (value.val <<< (256 - 8 * r)) % 2 ^ 256) / 2 ^ (8 * (31 - lane)) % 2 ^ 8 =
      if lane < r then value.val / 2 ^ (8 * (31 - (32 + lane - r))) % 2 ^ 8
      else second.val / 2 ^ (8 * (31 - lane)) % 2 ^ 8 := by
  split
  · apply byte_eq
    intro t small
    have bound : 8 * (31 - lane) + t < 256 := by omega
    have outside : ¬(8 * r + (8 * (31 - lane) + t) < 256) := by omega
    have above : 256 - 8 * r ≤ 8 * (31 - lane) + t := by omega
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, outside, decide_false,
      Bool.and_false, Bool.false_or, Nat.testBit_mod_two_pow, bound, decide_true, Bool.true_and,
      Nat.testBit_shiftLeft, ge_iff_le, above]
    congr 1
    omega
  · apply byte_eq
    intro t small
    have bound : 8 * (31 - lane) + t < 256 := by omega
    have inside : 8 * r + (8 * (31 - lane) + t) < 256 := by omega
    have below : ¬(256 - 8 * r ≤ 8 * (31 - lane) + t) := by omega
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, inside, decide_true,
      Bool.and_true, Nat.testBit_mod_two_pow, bound, Bool.true_and, Nat.testBit_shiftLeft, ge_iff_le, below,
      decide_false, Bool.false_and, Bool.or_false]


theorem val_shift (offset : Word) : (MemorySemantics.shift offset).val = 8 * (offset.val % 32) := by
  have eight : (Word.ofNatModulo 8).val = 8 := Nat.mod_eq_of_lt (by decide)
  show ((MemorySemantics.position offset).val * (Word.ofNatModulo 8).val) % wordModulus = _
  rw [val_position, eight, Nat.mod_eq_of_lt (by have := Nat.mod_lt offset.val (show 32 > 0 by decide); change _ < 2 ^ 256; omega)]
  omega

theorem val_next (offset : Word) :
    ((MemorySemantics.index offset).add (Word.ofNatModulo 1)).val = offset.val / 32 + 1 := by
  show ((MemorySemantics.index offset).val + (Word.ofNatModulo 1).val) % wordModulus = _
  rw [val_index, show (Word.ofNatModulo 1).val = 1 from rfl]
  apply Nat.mod_eq_of_lt
  have := offset.isLt
  change offset.val < 2 ^ 256 at this
  change _ < 2 ^ 256
  omega

theorem readByte_writeWord (entries : MemorySemantics.Entries) (offset value other : Word) :
    MemoryCopySemantics.readByte (MemorySemantics.writeWord entries offset value) other =
      if offset.val ≤ other.val ∧ other.val < offset.val + 32 then
        Word.byteAt (Word.ofNatModulo (other.val - offset.val)) value
      else MemoryCopySemantics.readByte entries other := by
  have otherSmall : (MemorySemantics.position other).val < 32 := by
    rw [val_position]; exact Nat.mod_lt _ (by decide)
  have otherSplit := Nat.div_add_mod other.val 32
  have offsetSplit := Nat.div_add_mod offset.val 32
  have otherLane := Nat.mod_lt other.val (show 32 > 0 by decide)
  have offsetLane := Nat.mod_lt offset.val (show 32 > 0 by decide)
  have byteOf {position : Nat} (small : position < 32) (word : Word) :
      (Word.byteAt (Word.ofNatModulo position) word).val = word.val / 2 ^ (8 * (31 - position)) % 2 ^ 8 := by
    rw [val_byteAt _ _ (by rw [val_small (by omega)]; exact small), val_small (by omega)]
  unfold MemoryCopySemantics.readByte MemorySemantics.writeWord
  by_cases aligned : offset.val % 32 = 0
  · have test : (MemorySemantics.position offset == Word.zero) = true :=
      beq_iff_eq.mpr (Fin.ext (by rw [val_position]; exact aligned))
    simp only [test, ↓reduceIte]
    by_cases sameIndex : other.val / 32 = offset.val / 32
    · have keys : MemorySemantics.index other = MemorySemantics.index offset :=
        Fin.ext (by rw [val_index, val_index, sameIndex])
      rw [keys, lookup_insert_same, if_pos (by omega)]
      apply Fin.ext
      rw [val_byteAt _ _ otherSmall, byteOf (by omega), val_position]
      congr 3
      omega
    · rw [lookup_insert_other (index_ne_of (by rw [val_index, val_index]; exact sameIndex)), if_neg (by omega)]
  · have test : (MemorySemantics.position offset == Word.zero) = false :=
      beq_eq_false_iff_ne.mpr (fun same => aligned (by rw [← val_position, same]; rfl))
    simp only [test, Bool.false_eq_true, ↓reduceIte]
    have distance := val_shift offset
    have distanceSmall : (MemorySemantics.shift offset).val < 256 := by omega
    have complement : ((Word.ofNatModulo 256).sub (MemorySemantics.shift offset)).val = 256 - 8 * (offset.val % 32) := by
      have below : MemorySemantics.shift offset ≤ Word.ofNatModulo 256 := by
        rw [Fin.le_def, distance, show (Word.ofNatModulo 256).val = 256 from rfl]; omega
      show (Word.ofNatModulo 256 - MemorySemantics.shift offset).val = _
      rw [Fin.sub_val_of_le below, distance]; rfl
    have ones : (Word.ofNatModulo (wordModulus - 1)).val = 2 ^ 256 - 1 := Nat.mod_eq_of_lt (by decide)
    have maskValue : ((Word.ofNatModulo (wordModulus - 1)).shiftRight (MemorySemantics.shift offset)).val =
        (2 ^ 256 - 1) >>> (8 * (offset.val % 32)) := by
      rw [val_shiftRight _ _ distanceSmall, ones, distance]
    have nextIndex : (MemorySemantics.index offset).add (Word.ofNatModulo 1) ≠ MemorySemantics.index offset := by
      intro same
      have := congrArg Fin.val same
      rw [val_next, val_index] at this
      omega
    by_cases sameIndex : other.val / 32 = offset.val / 32
    · have keys : MemorySemantics.index other = MemorySemantics.index offset :=
        Fin.ext (by rw [val_index, val_index, sameIndex])
      rw [keys, lookup_insert_other (Ne.symm nextIndex), lookup_insert_same]
      apply Fin.ext
      rw [val_byteAt _ _ otherSmall, val_position, val_bitOr, val_bitAnd, val_bitNot, maskValue,
        val_shiftRight _ _ distanceSmall, distance, lane_high _ _ offsetLane otherLane]
      by_cases inside : offset.val % 32 ≤ other.val % 32
      · rw [if_pos inside, if_pos (by omega), byteOf (by omega)]
        congr 3
        omega
      · rw [if_neg inside, if_neg (by omega), val_byteAt _ _ otherSmall, val_position]
    · by_cases nextSame : other.val / 32 = offset.val / 32 + 1
      · have keys : MemorySemantics.index other = (MemorySemantics.index offset).add (Word.ofNatModulo 1) :=
          Fin.ext (by rw [val_index, val_next, nextSame])
        rw [keys, lookup_insert_same, lookup_insert_other nextIndex]
        apply Fin.ext
        rw [val_byteAt _ _ otherSmall, val_position, val_bitOr, val_bitAnd, maskValue,
          val_shiftLeft _ _ (by rw [complement]; omega), complement,
          lane_low _ _ (by omega) offsetLane otherLane]
        by_cases inside : other.val % 32 < offset.val % 32
        · rw [if_pos inside, if_pos (by omega), byteOf (by omega)]
          congr 3
          omega
        · rw [if_neg inside, if_neg (by omega), val_byteAt _ _ otherSmall, val_position, ← keys]
      · have notNext : MemorySemantics.index other ≠ (MemorySemantics.index offset).add (Word.ofNatModulo 1) := by
          intro same
          have := congrArg Fin.val same
          rw [val_index, val_next] at this
          exact nextSame this
        rw [lookup_insert_other notNext,
          lookup_insert_other (index_ne_of (by rw [val_index, val_index]; exact sameIndex)), if_neg (by omega)]


theorem readByte_writeByte (entries : MemorySemantics.Entries) (offset value other : Word) :
    MemoryCopySemantics.readByte (MemorySemantics.writeByte entries offset value) other =
      if other = offset then value.bitAnd (Word.ofNatModulo 255) else MemoryCopySemantics.readByte entries other := by
  split
  · rename_i same
    subst same
    exact readByte_writeByte_same entries other value
  · rename_i different
    exact readByte_writeByte_other entries value different

theorem readByte_empty (other : Word) : MemoryCopySemantics.readByte [] other = Word.zero := by
  simp [MemoryCopySemantics.readByte, MemorySemantics.lookup]

theorem byte_bitAnd {byte : Nat} (small : byte < 256) :
    (Word.ofNatModulo byte).bitAnd (Word.ofNatModulo 255) = Word.ofNatModulo byte := by
  apply Fin.ext
  rw [val_bitAnd, val_small (by omega), val_small (by decide)]
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt small

/-- Bytes written one at a time are read back in order; other addresses keep
their previous bytes. -/
theorem readByte_storeBytes (other : Word) :
    ∀ (bytes : CreationAddressSemantics.Bytes) (words : MemorySemantics.Entries) (index : Nat),
      index + bytes.length ≤ 2 ^ 256 →
      MemoryCopySemantics.readByte (CreationAddressSemantics.storeBytes words index bytes) other =
        if index ≤ other.val ∧ other.val < index + bytes.length then
          (Word.ofNatModulo (bytes.getD (other.val - index) 0)).bitAnd (Word.ofNatModulo 255)
        else MemoryCopySemantics.readByte words other := by
  intro bytes
  induction bytes with
  | nil =>
      intro words index _
      rw [if_neg (by simp)]
      rfl
  | cons byte rest ih =>
      intro words index fits
      simp only [CreationAddressSemantics.storeBytes, List.length_cons] at fits ⊢
      rw [ih _ (index + 1) (by omega), readByte_writeByte]
      by_cases here : other.val = index
      · have same : other = Word.ofNatModulo index := Fin.ext (by rw [val_small (by omega)]; exact here)
        rw [if_neg (by omega), if_pos same, if_pos (by omega), here, Nat.sub_self]
        rfl
      · have different : other ≠ Word.ofNatModulo index := fun same => here (by rw [same, val_small (by omega)])
        rw [if_neg different]
        by_cases later : index + 1 ≤ other.val ∧ other.val < index + 1 + rest.length
        · rw [if_pos later, if_pos (by omega)]
          congr 2
          rw [show other.val - index = (other.val - (index + 1)) + 1 by omega]
          rfl
        · rw [if_neg later, if_neg (by omega)]

theorem readByte_stored {bytes : CreationAddressSemantics.Bytes} (small : ∀ byte ∈ bytes, byte < 256)
    (fits : bytes.length ≤ 2 ^ 256) {index : Nat} (inside : index < bytes.length) :
    MemoryCopySemantics.readByte (CreationAddressSemantics.stored bytes) (Word.ofNatModulo index) =
      Word.ofNatModulo (bytes.getD index 0) := by
  unfold CreationAddressSemantics.stored
  rw [readByte_storeBytes _ bytes [] 0 (by omega), val_small (by omega), if_pos (by omega), Nat.sub_zero]
  apply byte_bitAnd
  have same : bytes.getD index 0 = bytes[index] := (List.getElem_eq_getD 0).symm
  rw [same]
  exact small _ (List.getElem_mem inside)

/-- Byte `lane` of a word shifted left by whole bytes. -/
theorem lane_shiftLeft (value : Word) {shift lane : Nat} (small : lane + shift < 32) :
    (value.val <<< (8 * shift)) % 2 ^ 256 / 2 ^ (8 * (31 - lane)) % 2 ^ 8 =
      value.val / 2 ^ (8 * (31 - (lane + shift))) % 2 ^ 8 := by
  apply byte_eq
  intro t inside
  have bound : 8 * (31 - lane) + t < 256 := by omega
  have above : 8 * shift ≤ 8 * (31 - lane) + t := by omega
  simp only [Nat.testBit_mod_two_pow, bound, decide_true, Bool.true_and, Nat.testBit_shiftLeft, ge_iff_le, above]
  congr 1
  omega

/-- The low 20 bytes of a word survive the 160-bit address mask. -/
theorem lane_mask (value : Word) {lane : Nat} (low : 12 ≤ lane) (small : lane < 32) :
    (value.val &&& (2 ^ 160 - 1)) / 2 ^ (8 * (31 - lane)) % 2 ^ 8 = value.val / 2 ^ (8 * (31 - lane)) % 2 ^ 8 := by
  apply byte_eq
  intro t inside
  have bound : 8 * (31 - lane) + t < 160 := by omega
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, bound, decide_true, Bool.and_true]

/-! Keccak absorption reads only the bytes inside its range. -/


theorem paddedByte_congr {first second : MemorySemantics.Entries} {offset remaining : Word} {index : Nat}
    (small : index < 136)
    (agree : index < remaining.val →
      MemoryCopySemantics.readByte first (offset.add (Word.ofNatModulo index)) =
        MemoryCopySemantics.readByte second (offset.add (Word.ofNatModulo index))) :
    KeccakSemantics.paddedByte first offset remaining index = KeccakSemantics.paddedByte second offset remaining index := by
  unfold KeccakSemantics.paddedByte
  by_cases inside : remaining > Word.ofNatModulo index
  · have bound : index < remaining.val := by
      have := Fin.lt_def.mp inside
      rwa [val_small (by omega)] at this
    simp only [inside, ↓reduceIte, agree bound]
  · simp only [inside, ↓reduceIte]

theorem readLane_congr {first second : MemorySemantics.Entries} {offset remaining : Word}
    (agree : ∀ index, index < 136 → index < remaining.val →
      MemoryCopySemantics.readByte first (offset.add (Word.ofNatModulo index)) =
        MemoryCopySemantics.readByte second (offset.add (Word.ofNatModulo index))) :
    ∀ count index accumulator, index + count ≤ 136 →
      KeccakSemantics.readLane count index first offset remaining accumulator =
        KeccakSemantics.readLane count index second offset remaining accumulator := by
  intro count
  induction count with
  | zero => intro index accumulator _; rfl
  | succ count ih =>
      intro index accumulator bounded
      simp only [KeccakSemantics.readLane]
      rw [paddedByte_congr (by omega) (agree index (by omega))]
      exact ih (index + 1) _ (by omega)

theorem absorbBlock_congr {first second : MemorySemantics.Entries} {offset remaining : Word}
    (state : KeccakSemantics.State)
    (agree : ∀ index, index < 136 → index < remaining.val →
      MemoryCopySemantics.readByte first (offset.add (Word.ofNatModulo index)) =
        MemoryCopySemantics.readByte second (offset.add (Word.ofNatModulo index))) :
    KeccakSemantics.absorbBlock first offset remaining state = KeccakSemantics.absorbBlock second offset remaining state := by
  unfold KeccakSemantics.absorbBlock
  apply List.map_congr_left
  intro index member
  split
  · rename_i small
    rw [readLane_congr agree 8 (8 * index) Word.zero (by omega)]
  · rfl

theorem add_add (offset : Word) (step index : Nat) (small : step + index < 2 ^ 256) :
    (offset.add (Word.ofNatModulo step)).add (Word.ofNatModulo index) = offset.add (Word.ofNatModulo (step + index)) := by
  apply Fin.ext
  show ((offset.val + step % wordModulus) % wordModulus + index % wordModulus) % wordModulus =
    (offset.val + (step + index) % wordModulus) % wordModulus
  change ((offset.val + step % 2 ^ 256) % 2 ^ 256 + index % 2 ^ 256) % 2 ^ 256 =
    (offset.val + (step + index) % 2 ^ 256) % 2 ^ 256
  rw [Nat.mod_eq_of_lt (show step < 2 ^ 256 by omega), Nat.mod_eq_of_lt (show index < 2 ^ 256 by omega),
    Nat.mod_eq_of_lt small, Nat.mod_add_mod, Nat.add_assoc]

theorem Absorb.congr {first second : MemorySemantics.Entries} {offset remaining : Word}
    {state : KeccakSemantics.State} {result : Word}
    (absorbed : KeccakSemantics.Absorb first offset remaining state result)
    (agree : ∀ index, index < remaining.val →
      MemoryCopySemantics.readByte first (offset.add (Word.ofNatModulo index)) =
        MemoryCopySemantics.readByte second (offset.add (Word.ofNatModulo index))) :
    KeccakSemantics.Absorb second offset remaining state result := by
  induction absorbed with
  | last offset remaining state short =>
      rw [absorbBlock_congr state (fun index _ inside => agree index inside)]
      exact .last offset remaining state short
  | more full rest ih =>
      rename_i offset remaining state result
      have large : 136 ≤ remaining.val := by
        have := Nat.not_lt.mp (fun lt => full (Fin.lt_def.mpr (by rw [val_small (by decide)]; exact lt)))
        exact this
      have remainingSub : (remaining.sub (Word.ofNatModulo 136)).val = remaining.val - 136 := by
        show (remaining - Word.ofNatModulo 136).val = _
        rw [Fin.sub_val_of_le (Fin.le_def.mpr (by rw [val_small (by decide)]; exact large)), val_small (by decide)]
      have same := absorbBlock_congr state (fun index _ inside => agree index inside)
      refine .more full ?_
      rw [← same]
      refine ih ?_
      intro index inside
      rw [remainingSub] at inside
      have remainingSmall := remaining.isLt
      change remaining.val < 2 ^ 256 at remainingSmall
      rw [add_add _ _ _ (by omega)]
      exact agree (136 + index) (by omega)

theorem Absorb.deterministic {words : MemorySemantics.Entries} {offset remaining : Word}
    {state : KeccakSemantics.State} {first second : Word}
    (left : KeccakSemantics.Absorb words offset remaining state first)
    (right : KeccakSemantics.Absorb words offset remaining state second) : first = second := by
  induction left generalizing second with
  | last offset remaining state short =>
      cases right with
      | last => rfl
      | more full => exact absurd short full
  | more full rest ih =>
      cases right with
      | last _ _ _ short => exact absurd short full
      | more _ rest' => exact ih rest'

theorem Keccak.deterministic {bytes : CreationAddressSemantics.Bytes} {first second : Word}
    (left : CreationAddressSemantics.Keccak bytes first) (right : CreationAddressSemantics.Keccak bytes second) :
    first = second :=
  Absorb.deterministic left right

end Solcore.Frontend.RustHull.CreationBytes
