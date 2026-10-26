import Solcore.Frontend.RustHull.CreationBytes

/-! The CREATE and CREATE2 preimages as the actual address builders store them.
`createScratch` and `create2Scratch` replay, on source memory, the byte and
word writes of `Creation.createAddress` and `Creation.create2Address`. Their
bytes equal the independent RLP and CREATE2 preimages over the hashed range, so
their Keccak absorption is the specified Keccak-256 of those preimages. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationPreimage
open Core CreationAddressSemantics CreationBytes

theorem getD_append_left {first second : List Nat} {index : Nat} (inside : index < first.length) :
    (first ++ second).getD index 0 = first.getD index 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left inside]

theorem getD_append_right {first second : List Nat} {index : Nat} (beyond : first.length ≤ index) :
    (first ++ second).getD index 0 = second.getD (index - first.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right beyond]

theorem bigEndian_zero : bigEndian 0 = [] := by
  rw [bigEndian]; simp

theorem bigEndian_pos {value : Nat} (positive : 0 < value) :
    bigEndian value = bigEndian (value / 256) ++ [value % 256] := by
  rw [bigEndian, if_neg (by omega)]

theorem bigEndian_upper (value : Nat) : value < 256 ^ (bigEndian value).length := by
  by_cases zero : value = 0
  · subst zero; rw [bigEndian_zero]; decide
  · rw [bigEndian_pos (by omega), List.length_append, List.length_singleton, Nat.pow_succ]
    have := bigEndian_upper (value / 256)
    exact (Nat.div_lt_iff_lt_mul (by decide)).mp this
termination_by value
decreasing_by omega

theorem bigEndian_lower (value : Nat) (positive : 0 < value) :
    256 ^ ((bigEndian value).length - 1) ≤ value := by
  rw [bigEndian_pos positive, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  by_cases small : value < 256
  · rw [Nat.div_eq_of_lt small, bigEndian_zero]
    simp only [List.length_nil, Nat.pow_zero]
    omega
  · have lower := bigEndian_lower (value / 256) (by omega)
    have positiveLength : 0 < (bigEndian (value / 256)).length := by
      rw [bigEndian_pos (by omega)]; simp
    generalize (bigEndian (value / 256)).length = count at lower positiveLength ⊢
    obtain ⟨previous, rfl⟩ : ∃ previous, count = previous + 1 := ⟨count - 1, by omega⟩
    rw [Nat.add_sub_cancel] at lower
    rw [Nat.pow_succ]
    exact Nat.le_trans (Nat.mul_le_mul_right 256 lower) (Nat.div_mul_le_self value 256)
termination_by value
decreasing_by omega

theorem bigEndian_length {value : Nat} (positive : 0 < value) :
    (bigEndian value).length = Nat.log2 value / 8 + 1 := by
  have upper := bigEndian_upper value
  have lower := bigEndian_lower value positive
  have nonzero : value ≠ 0 := by omega
  have pow (count : Nat) : (256 : Nat) ^ count = 2 ^ (8 * count) := by
    rw [Nat.pow_mul]
  rw [pow] at upper lower
  have high := (Nat.log2_lt nonzero).mpr upper
  have low := (Nat.le_log2 nonzero).mpr lower
  have positiveLength : 0 < (bigEndian value).length := by
    rw [bigEndian_pos positive]; simp
  omega

theorem bigEndian_getD (value : Nat) :
    ∀ index, index < (bigEndian value).length →
      (bigEndian value).getD index 0 = value / 256 ^ ((bigEndian value).length - 1 - index) % 256 := by
  intro index inside
  by_cases zero : value = 0
  · subst zero; rw [bigEndian_zero] at inside; simp at inside
  · have unfolded := bigEndian_pos (value := value) (by omega)
    rw [unfolded] at inside ⊢
    rw [List.length_append, List.length_singleton] at inside ⊢
    by_cases last : index = (bigEndian (value / 256)).length
    · subst last
      rw [getD_append_right (Nat.le_refl _), Nat.sub_self]
      simp
    · rw [getD_append_left (by omega), bigEndian_getD (value / 256) index (by omega),
        Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3
      omega
termination_by value
decreasing_by omega

theorem bigEndian_bytes (value : Nat) : ∀ byte ∈ bigEndian value, byte < 256 := by
  intro byte member
  by_cases zero : value = 0
  · subst zero; rw [bigEndian_zero] at member; simp at member
  · rw [bigEndian_pos (by omega)] at member
    rcases List.mem_append.mp member with rest | here
    · exact bigEndian_bytes (value / 256) byte rest
    · simp at here; omega
termination_by value
decreasing_by omega


theorem pow256 (count : Nat) : (256 : Nat) ^ count = 2 ^ (8 * count) := by
  rw [Nat.pow_mul]

theorem wordBytes_length (value : Word) : (wordBytes value).length = 32 := by
  simp [wordBytes]

theorem wordBytes_getD (value : Word) {index : Nat} (inside : index < 32) :
    (wordBytes value).getD index 0 = value.val / 256 ^ (31 - index) % 256 := by
  simp [wordBytes, List.getD_eq_getElem?_getD, inside]

theorem addressBytes_length (value : Word) : (addressBytes value).length = 20 := by
  simp [addressBytes, wordBytes_length]

theorem addressBytes_getD (value : Word) {index : Nat} (inside : index < 20) :
    (addressBytes value).getD index 0 = value.val / 256 ^ (19 - index) % 256 := by
  have shifted : (addressBytes value).getD index 0 = (wordBytes value).getD (12 + index) 0 := by
    simp [addressBytes, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [shifted, wordBytes_getD _ (by omega)]
  congr 3
  omega

theorem encodeBytes_address (value : Word) : encodeBytes (addressBytes value) = 148 :: addressBytes value := by
  unfold encodeBytes
  rw [addressBytes_length]
  simp

def nonceBytes (nonce : Word) : Bytes := encodeBytes (bigEndian nonce.val)

theorem bigEndian_short {value : Nat} (positive : 0 < value) (small : value < 256) : bigEndian value = [value] := by
  rw [bigEndian_pos positive, Nat.div_eq_of_lt small, bigEndian_zero, Nat.mod_eq_of_lt small]
  rfl

theorem nonceBytes_zero {nonce : Word} (zero : nonce.val = 0) : nonceBytes nonce = [128] := by
  simp [nonceBytes, zero, bigEndian_zero, encodeBytes]

theorem nonceBytes_small {nonce : Word} (positive : 0 < nonce.val) (small : nonce.val < 128) :
    nonceBytes nonce = [nonce.val] := by
  simp [nonceBytes, bigEndian_short positive (by omega), encodeBytes, small]

theorem bigEndian_word_length (nonce : Word) (positive : 0 < nonce.val) :
    (bigEndian nonce.val).length ≤ 32 := by
  rw [bigEndian_length positive]
  have := (Nat.log2_lt (n := nonce.val) (k := 256) (by omega)).mpr nonce.isLt
  omega

theorem nonceBytes_large {nonce : Word} (large : 128 ≤ nonce.val) :
    nonceBytes nonce = (128 + (bigEndian nonce.val).length) :: bigEndian nonce.val := by
  have bounded := bigEndian_word_length nonce (by omega)
  unfold nonceBytes encodeBytes
  rw [if_neg, if_pos (by omega)]
  intro ⟨single, head⟩
  have upper := bigEndian_upper nonce.val
  rw [single] at upper
  rw [bigEndian_short (by omega) (by simpa using upper)] at head
  simp at head
  omega


theorem nonceBytes_length_le (nonce : Word) : (nonceBytes nonce).length ≤ 33 := by
  by_cases zero : nonce.val = 0
  · rw [nonceBytes_zero zero]; simp
  · by_cases small : nonce.val < 128
    · rw [nonceBytes_small (by omega) small]; simp
    · rw [nonceBytes_large (by omega)]
      have := bigEndian_word_length nonce (by omega)
      simp only [List.length_cons]
      omega

theorem createPreimage_eq (creator nonce : Word) :
    createPreimage creator nonce =
      (213 + (nonceBytes nonce).length) :: 148 :: (addressBytes creator ++ nonceBytes nonce) := by
  have bounded := nonceBytes_length_le nonce
  show encodeList [encodeBytes (addressBytes creator), nonceBytes nonce] = _
  rw [encodeBytes_address]
  unfold encodeList
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.length_cons,
    List.length_append, addressBytes_length]
  rw [if_pos (by omega)]
  congr 1
  omega

theorem createPreimage_length (creator nonce : Word) :
    (createPreimage creator nonce).length = 22 + (nonceBytes nonce).length := by
  rw [createPreimage_eq]
  simp only [List.length_cons, List.length_append, addressBytes_length]
  omega

theorem createPreimage_getD (creator nonce : Word) (index : Nat) :
    (createPreimage creator nonce).getD index 0 =
      if index = 0 then 213 + (nonceBytes nonce).length
      else if index = 1 then 148
      else if index < 22 then (addressBytes creator).getD (index - 2) 0
      else (nonceBytes nonce).getD (index - 22) 0 := by
  rw [createPreimage_eq]
  rcases index with _ | _ | index
  · simp
  · simp
  · rw [if_neg (by omega), if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
    rw [← List.getD_eq_getElem?_getD]
    by_cases small : index + 2 < 22
    · rw [if_pos small, getD_append_left (by rw [addressBytes_length]; omega)]
      rfl
    · rw [if_neg small, getD_append_right (by rw [addressBytes_length]; omega), addressBytes_length]
      congr 1

theorem createPreimage_bytes (creator nonce : Word) : ∀ byte ∈ createPreimage creator nonce, byte < 256 := by
  have bounded := nonceBytes_length_le nonce
  intro byte member
  rw [createPreimage_eq] at member
  simp only [List.mem_cons, List.mem_append] at member
  rcases member with rfl | rfl | address | nonceByte
  · omega
  · omega
  · simp only [addressBytes, wordBytes] at address
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop address)
    exact Nat.mod_lt _ (by decide)
  · by_cases zero : nonce.val = 0
    · rw [nonceBytes_zero zero] at nonceByte; simp at nonceByte; omega
    · by_cases small : nonce.val < 128
      · rw [nonceBytes_small (by omega) small] at nonceByte; simp at nonceByte; omega
      · rw [nonceBytes_large (by omega)] at nonceByte
        simp only [List.mem_cons] at nonceByte
        rcases nonceByte with rfl | rest
        · have := bigEndian_word_length nonce (by omega); omega
        · exact bigEndian_bytes _ _ rest

def addressMask : Word := Word.ofNatModulo (2 ^ 160 - 1)

def byteCount (nonce : Word) : Word := (Word.ofNatModulo 32).sub (nonce.clz.udiv (Word.ofNatModulo 8))

def encodedLength (nonce : Word) : Word :=
  if nonce > Word.ofNatModulo 127 then (byteCount nonce).add (Word.ofNatModulo 1) else Word.ofNatModulo 1

def createLength (nonce : Word) : Word := (Word.ofNatModulo 22).add (encodedLength nonce)

def createPrefix (creator nonce : Word) : MemorySemantics.Entries :=
  MemorySemantics.writeWord
    (MemorySemantics.writeByte
      (MemorySemantics.writeByte [] (Word.ofNatModulo 0) ((Word.ofNatModulo 213).add (encodedLength nonce)))
      (Word.ofNatModulo 1) (Word.ofNatModulo 148))
    (Word.ofNatModulo 2) ((creator.bitAnd addressMask).shiftLeft (Word.ofNatModulo 96))

def createScratch (creator nonce : Word) : MemorySemantics.Entries :=
  if nonce == Word.ofNatModulo 0 then
    MemorySemantics.writeByte (createPrefix creator nonce) (Word.ofNatModulo 22) (Word.ofNatModulo 128)
  else if nonce > Word.ofNatModulo 127 then
    MemorySemantics.writeWord
      (MemorySemantics.writeByte (createPrefix creator nonce) (Word.ofNatModulo 22)
        ((Word.ofNatModulo 128).add (byteCount nonce)))
      (Word.ofNatModulo 23) (nonce.shiftLeft (((Word.ofNatModulo 32).sub (byteCount nonce)).mul (Word.ofNatModulo 8)))
  else MemorySemantics.writeByte (createPrefix creator nonce) (Word.ofNatModulo 22) nonce

theorem byteCount_val {nonce : Word} (positive : 0 < nonce.val) :
    (byteCount nonce).val = (bigEndian nonce.val).length := by
  have logSmall := (Nat.log2_lt (n := nonce.val) (k := 256) (by omega)).mpr nonce.isLt
  have clzValue : nonce.clz.val = 255 - Nat.log2 nonce.val := by
    simp only [Word.clz, show nonce.val ≠ 0 by omega, ↓reduceIte]
    exact val_small (by omega)
  have divided : (nonce.clz.udiv (Word.ofNatModulo 8)).val = (255 - Nat.log2 nonce.val) / 8 := by
    simp only [Word.udiv, show (Word.ofNatModulo 8).val ≠ 0 from by decide, ↓reduceIte]
    show nonce.clz.val / (Word.ofNatModulo 8).val = _
    rw [clzValue, val_small (by decide)]
  rw [bigEndian_length positive]
  show ((Word.ofNatModulo 32) - nonce.clz.udiv (Word.ofNatModulo 8)).val = _
  rw [Fin.sub_val_of_le (Fin.le_def.mpr (by rw [divided, val_small (by decide)]; omega)), divided, val_small (by decide)]
  omega

theorem encodedLength_val (nonce : Word) : (encodedLength nonce).val = (nonceBytes nonce).length := by
  unfold encodedLength
  by_cases large : nonce > Word.ofNatModulo 127
  · have bound : 128 ≤ nonce.val := by
      have := Fin.lt_def.mp large; rw [val_small (by decide)] at this; omega
    rw [if_pos large, nonceBytes_large bound]
    have := bigEndian_word_length nonce (by omega)
    show ((byteCount nonce).val + (Word.ofNatModulo 1).val) % wordModulus = _
    rw [byteCount_val (by omega), val_small (by decide), Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    simp
  · have bound : nonce.val < 128 := by
      have := Fin.not_lt.mp large; rw [Fin.le_def, val_small (by decide)] at this; omega
    rw [if_neg large]
    by_cases zero : nonce.val = 0
    · rw [nonceBytes_zero zero]; rfl
    · rw [nonceBytes_small (by omega) bound]; rfl

theorem createLength_val (creator nonce : Word) :
    (createLength nonce).val = (createPreimage creator nonce).length := by
  have := nonceBytes_length_le nonce
  show ((Word.ofNatModulo 22).val + (encodedLength nonce).val) % wordModulus = _
  rw [encodedLength_val, val_small (by decide), Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega), createPreimage_length]

theorem readByte_writeByte_at (entries : MemorySemantics.Entries) {position index : Nat} (value : Word)
    (positionSmall : position < 2 ^ 256) (indexSmall : index < 2 ^ 256) :
    MemoryCopySemantics.readByte (MemorySemantics.writeByte entries (Word.ofNatModulo position) value)
        (Word.ofNatModulo index) =
      if index = position then value.bitAnd (Word.ofNatModulo 255)
      else MemoryCopySemantics.readByte entries (Word.ofNatModulo index) := by
  rw [readByte_writeByte]
  by_cases same : index = position
  · rw [if_pos (by rw [same]), if_pos same]
  · rw [if_neg (fun equal => same (by
      have := congrArg Fin.val equal; rwa [val_small indexSmall, val_small positionSmall] at this)), if_neg same]

theorem readByte_writeWord_at (entries : MemorySemantics.Entries) {position index : Nat} (value : Word)
    (positionSmall : position < 2 ^ 256) (indexSmall : index < 2 ^ 256) :
    MemoryCopySemantics.readByte (MemorySemantics.writeWord entries (Word.ofNatModulo position) value)
        (Word.ofNatModulo index) =
      if position ≤ index ∧ index < position + 32 then Word.byteAt (Word.ofNatModulo (index - position)) value
      else MemoryCopySemantics.readByte entries (Word.ofNatModulo index) := by
  rw [readByte_writeWord, val_small positionSmall, val_small indexSmall]

theorem address_lane (creator : Word) {lane : Nat} (inside : lane < 20) :
    Word.byteAt (Word.ofNatModulo lane) ((creator.bitAnd addressMask).shiftLeft (Word.ofNatModulo 96)) =
      Word.ofNatModulo ((addressBytes creator).getD lane 0) := by
  rw [addressBytes_getD _ inside]
  apply Fin.ext
  rw [val_byteAt _ _ (by rw [val_small (by omega)]; omega), val_small (by omega),
    val_shiftLeft _ _ (by rw [val_small (by decide)]; decide), val_small (show 96 < 2 ^ 256 by decide),
    val_small (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)),
    show (96 : Nat) = 8 * 12 from rfl, lane_shiftLeft _ (by omega), val_bitAnd,
    show addressMask.val = 2 ^ 160 - 1 from val_small (by decide), lane_mask _ (by omega) (by omega), pow256]
  congr 3
  omega

theorem createPrefix_byte (creator nonce : Word) {index : Nat} (inside : index < 22) :
    MemoryCopySemantics.readByte (createPrefix creator nonce) (Word.ofNatModulo index) =
      Word.ofNatModulo ((createPreimage creator nonce).getD index 0) := by
  unfold createPrefix
  rw [readByte_writeWord_at _ _ (by decide) (by omega), createPreimage_getD]
  by_cases address : 2 ≤ index
  · rw [if_pos ⟨address, by omega⟩, if_neg (by omega), if_neg (by omega), if_pos inside]
    exact address_lane creator (by omega)
  · rw [if_neg (by omega), readByte_writeByte_at _ _ (by decide) (by omega)]
    by_cases one : index = 1
    · rw [if_pos one, if_neg (by omega), if_pos one]
      exact byte_bitAnd (by decide)
    · have bounded := nonceBytes_length_le nonce
      rw [if_neg one, readByte_writeByte_at _ _ (by decide) (by omega), if_pos (by omega), if_pos (by omega)]
      have header : (Word.ofNatModulo 213).add (encodedLength nonce) = Word.ofNatModulo (213 + (nonceBytes nonce).length) := by
        apply Fin.ext
        show ((Word.ofNatModulo 213).val + (encodedLength nonce).val) % wordModulus = _
        rw [encodedLength_val, val_small (by decide), val_small (by omega)]
        exact Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)
      rw [header]
      exact byte_bitAnd (by omega)


theorem nonce_lane {nonce : Word} (large : 128 ≤ nonce.val) {lane : Nat} (inside : lane < (bigEndian nonce.val).length) :
    Word.byteAt (Word.ofNatModulo lane)
        (nonce.shiftLeft (((Word.ofNatModulo 32).sub (byteCount nonce)).mul (Word.ofNatModulo 8))) =
      Word.ofNatModulo ((bigEndian nonce.val).getD lane 0) := by
  have bounded := bigEndian_word_length nonce (by omega)
  have count := byteCount_val (nonce := nonce) (by omega)
  have remaining : ((Word.ofNatModulo 32).sub (byteCount nonce)).val = 32 - (bigEndian nonce.val).length := by
    show (Word.ofNatModulo 32 - byteCount nonce).val = _
    rw [Fin.sub_val_of_le (Fin.le_def.mpr (by rw [count, val_small (by decide)]; omega)), count, val_small (by decide)]
  have shift : (((Word.ofNatModulo 32).sub (byteCount nonce)).mul (Word.ofNatModulo 8)).val =
      8 * (32 - (bigEndian nonce.val).length) := by
    show (((Word.ofNatModulo 32).sub (byteCount nonce)).val * (Word.ofNatModulo 8).val) % wordModulus = _
    rw [remaining, val_small (by decide), Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    omega
  have positiveLength : 0 < (bigEndian nonce.val).length := by omega
  rw [bigEndian_getD _ _ inside]
  apply Fin.ext
  rw [val_byteAt _ _ (by rw [val_small (by omega)]; omega), val_small (by omega),
    val_shiftLeft _ _ (by rw [shift]; omega), shift, lane_shiftLeft _ (by omega),
    val_small (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)), pow256]
  congr 3
  omega

theorem createScratch_byte (creator nonce : Word) {index : Nat}
    (inside : index < (createPreimage creator nonce).length) :
    MemoryCopySemantics.readByte (createScratch creator nonce) (Word.ofNatModulo index) =
      Word.ofNatModulo ((createPreimage creator nonce).getD index 0) := by
  have total := createPreimage_length creator nonce
  have bounded := nonceBytes_length_le nonce
  unfold createScratch
  by_cases zero : nonce.val = 0
  · have test : (nonce == Word.ofNatModulo 0) = true := beq_iff_eq.mpr (Fin.ext (by rw [zero]; rfl))
    rw [if_pos test, readByte_writeByte_at _ _ (by decide) (by omega)]
    by_cases last : index = 22
    · rw [if_pos last, createPreimage_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega), last,
        nonceBytes_zero zero]
      exact byte_bitAnd (by decide)
    · rw [if_neg last]
      rw [nonceBytes_zero zero] at total
      exact createPrefix_byte creator nonce (by simp at total; omega)
  · have test : (nonce == Word.ofNatModulo 0) = false :=
      beq_eq_false_iff_ne.mpr (fun same => zero (by rw [same]; rfl))
    rw [if_neg (by rw [test]; decide)]
    by_cases large : nonce > Word.ofNatModulo 127
    · have bound : 128 ≤ nonce.val := by
        have := Fin.lt_def.mp large; rw [val_small (by decide)] at this; omega
      have lengthBound := bigEndian_word_length nonce (by omega)
      rw [if_pos large, nonceBytes_large bound] at *
      simp only [List.length_cons] at total
      rw [readByte_writeWord_at _ _ (by decide) (by omega)]
      by_cases tail : 23 ≤ index
      · rw [if_pos ⟨tail, by omega⟩, nonce_lane bound (by omega), createPreimage_getD, if_neg (by omega),
          if_neg (by omega), if_neg (by omega), nonceBytes_large bound,
          show index - 22 = (index - 23) + 1 by omega]
        rfl
      · rw [if_neg (by omega), readByte_writeByte_at _ _ (by decide) (by omega)]
        by_cases last : index = 22
        · rw [if_pos last, createPreimage_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega), last,
            nonceBytes_large bound]
          have header : (Word.ofNatModulo 128).add (byteCount nonce) =
              Word.ofNatModulo (128 + (bigEndian nonce.val).length) := by
            apply Fin.ext
            show ((Word.ofNatModulo 128).val + (byteCount nonce).val) % wordModulus = _
            rw [byteCount_val (by omega), val_small (by decide), val_small (by omega)]
            exact Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)
          rw [header]
          exact byte_bitAnd (by omega)
        · rw [if_neg last]
          exact createPrefix_byte creator nonce (by omega)
    · have bound : nonce.val < 128 := by
        have := Fin.not_lt.mp large; rw [Fin.le_def, val_small (by decide)] at this; omega
      rw [if_neg large, readByte_writeByte_at _ _ (by decide) (by omega)]
      rw [nonceBytes_small (by omega) bound] at total
      simp only [List.length_cons, List.length_nil] at total
      by_cases last : index = 22
      · rw [if_pos last, createPreimage_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega), last,
          nonceBytes_small (by omega) bound]
        apply Fin.ext
        rw [val_bitAnd, val_small (show 255 < 2 ^ 256 by decide)]
        show nonce.val &&& 255 = (Word.ofNatModulo ([nonce.val].getD 0 0)).val
        rw [show [nonce.val].getD 0 0 = nonce.val from rfl, val_small (by omega)]
        rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_eq_of_lt (by omega)
      · rw [if_neg last]
        exact createPrefix_byte creator nonce (by omega)

theorem zero_add (index : Nat) (small : index < 2 ^ 256) :
    Word.zero.add (Word.ofNatModulo index) = Word.ofNatModulo index := by
  apply Fin.ext
  show (0 + (Word.ofNatModulo index).val) % wordModulus = _
  rw [Nat.zero_add, val_small small]
  exact Nat.mod_eq_of_lt small

/-- A memory holding a byte string from address zero absorbs as the string. -/
theorem keccak_of_bytes {bytes : Bytes} {words : MemorySemantics.Entries} {length : Word}
    (small : ∀ byte ∈ bytes, byte < 256) (fits : bytes.length < 2 ^ 256)
    (sameLength : length.val = bytes.length)
    (agree : ∀ index, index < bytes.length →
      MemoryCopySemantics.readByte words (Word.ofNatModulo index) = Word.ofNatModulo (bytes.getD index 0))
    {digest : Word} :
    Keccak bytes digest ↔ KeccakSemantics.Absorb words Word.zero length (List.replicate 25 Word.zero) digest := by
  have lengthWord : length = Word.ofNatModulo bytes.length := Fin.ext (by rw [sameLength, val_small fits])
  have reads : ∀ index, index < length.val →
      MemoryCopySemantics.readByte (stored bytes) (Word.zero.add (Word.ofNatModulo index)) =
        MemoryCopySemantics.readByte words (Word.zero.add (Word.ofNatModulo index)) := by
    intro index inside
    rw [sameLength] at inside
    rw [zero_add _ (by omega), readByte_stored small (by omega) inside, agree index inside]
  unfold Keccak
  rw [← lengthWord]
  exact ⟨fun hashed => Absorb.congr hashed reads,
    fun absorbed => Absorb.congr absorbed (fun index inside => (reads index inside).symm)⟩

/-- Keccak-256 of a string shorter than the 136-byte rate absorbs one padded
block. -/
def shortDigest (bytes : Bytes) : Word :=
  KeccakSemantics.digest (KeccakSemantics.permute (KeccakSemantics.absorbBlock (stored bytes) Word.zero
    (Word.ofNatModulo bytes.length) (List.replicate 25 Word.zero)))

theorem shortDigest_keccak {bytes : Bytes} (short : bytes.length < 136) : Keccak bytes (shortDigest bytes) :=
  .last _ _ _ (by
    change (Word.ofNatModulo bytes.length).val < (Word.ofNatModulo 136).val
    rw [val_small (by omega), val_small (by decide)]
    exact short)

theorem createScratch_keccak (creator nonce : Word) {digest : Word} :
    Keccak (createPreimage creator nonce) digest ↔
      KeccakSemantics.Absorb (createScratch creator nonce) Word.zero (createLength nonce)
        (List.replicate 25 Word.zero) digest := by
  have total := createPreimage_length creator nonce
  have bounded := nonceBytes_length_le nonce
  exact keccak_of_bytes (createPreimage_bytes creator nonce) (by omega) (createLength_val creator nonce)
    (fun index inside => createScratch_byte creator nonce inside)

def create2Scratch (creator salt initHash : Word) : MemorySemantics.Entries :=
  MemorySemantics.writeWord
    (MemorySemantics.writeWord
      (MemorySemantics.writeWord (MemorySemantics.writeByte [] (Word.ofNatModulo 0) (Word.ofNatModulo 255))
        (Word.ofNatModulo 1) ((creator.bitAnd addressMask).shiftLeft (Word.ofNatModulo 96)))
      (Word.ofNatModulo 21) salt)
    (Word.ofNatModulo 53) initHash

theorem create2Preimage_length (creator salt initHash : Word) :
    (create2Preimage creator salt initHash).length = 85 := by
  simp [create2Preimage, addressBytes_length, wordBytes_length]

theorem create2Preimage_getD (creator salt initHash : Word) (index : Nat) :
    (create2Preimage creator salt initHash).getD index 0 =
      if index = 0 then 255
      else if index < 21 then (addressBytes creator).getD (index - 1) 0
      else if index < 53 then (wordBytes salt).getD (index - 21) 0
      else (wordBytes initHash).getD (index - 53) 0 := by
  rcases index with _ | index
  · rfl
  · rw [if_neg (by omega)]
    simp only [create2Preimage, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
    rw [← List.getD_eq_getElem?_getD, List.append_assoc]
    by_cases address : index + 1 < 21
    · rw [if_pos address, getD_append_left (by rw [addressBytes_length]; omega)]
      rfl
    · rw [if_neg address, getD_append_right (by rw [addressBytes_length]; omega), addressBytes_length]
      by_cases saltByte : index + 1 < 53
      · rw [if_pos saltByte, getD_append_left (by rw [wordBytes_length]; omega)]
        congr 1
      · rw [if_neg saltByte, getD_append_right (by rw [wordBytes_length]; omega), wordBytes_length]
        congr 1

theorem create2Preimage_bytes (creator salt initHash : Word) :
    ∀ byte ∈ create2Preimage creator salt initHash, byte < 256 := by
  intro byte member
  simp only [create2Preimage, List.mem_cons, List.mem_append, addressBytes, wordBytes] at member
  rcases member with rfl | (address | saltByte) | hashByte
  · omega
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop address)
    exact Nat.mod_lt _ (by decide)
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp saltByte
    exact Nat.mod_lt _ (by decide)
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hashByte
    exact Nat.mod_lt _ (by decide)

theorem word_lane (value : Word) {lane : Nat} (inside : lane < 32) :
    Word.byteAt (Word.ofNatModulo lane) value = Word.ofNatModulo ((wordBytes value).getD lane 0) := by
  rw [wordBytes_getD _ inside]
  apply Fin.ext
  rw [val_byteAt _ _ (by rw [val_small (by omega)]; omega), val_small (by omega),
    val_small (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)), pow256]

theorem create2Scratch_byte (creator salt initHash : Word) {index : Nat} (inside : index < 85) :
    MemoryCopySemantics.readByte (create2Scratch creator salt initHash) (Word.ofNatModulo index) =
      Word.ofNatModulo ((create2Preimage creator salt initHash).getD index 0) := by
  unfold create2Scratch
  rw [readByte_writeWord_at _ _ (by decide) (by omega), create2Preimage_getD]
  by_cases hashByte : 53 ≤ index
  · rw [if_pos ⟨hashByte, by omega⟩, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact word_lane initHash (by omega)
  · rw [if_neg (by omega), readByte_writeWord_at _ _ (by decide) (by omega)]
    by_cases saltByte : 21 ≤ index
    · rw [if_pos ⟨saltByte, by omega⟩, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      exact word_lane salt (by omega)
    · rw [if_neg (by omega), readByte_writeWord_at _ _ (by decide) (by omega)]
      by_cases address : 1 ≤ index
      · rw [if_pos ⟨address, by omega⟩, if_neg (by omega), if_pos (by omega)]
        exact address_lane creator (by omega)
      · rw [if_neg (by omega), readByte_writeByte_at _ _ (by decide) (by omega), if_pos (by omega), if_pos (by omega)]
        exact byte_bitAnd (by decide)

theorem create2Scratch_keccak (creator salt initHash : Word) {digest : Word} :
    Keccak (create2Preimage creator salt initHash) digest ↔
      KeccakSemantics.Absorb (create2Scratch creator salt initHash) Word.zero (Word.ofNatModulo 85)
        (List.replicate 25 Word.zero) digest :=
  keccak_of_bytes (create2Preimage_bytes creator salt initHash) (by rw [create2Preimage_length]; decide)
    (by rw [create2Preimage_length]; rfl)
    (fun index inside => create2Scratch_byte creator salt initHash (by rwa [create2Preimage_length] at inside))

end Solcore.Frontend.RustHull.CreationPreimage
