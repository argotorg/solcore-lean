import Std

set_option autoImplicit false

namespace Solcore.Util.FixedRadix

/-- Exactly `width` big-endian digits in the given base. -/
abbrev Digits (base width : Nat) := Vector (Fin base) width

/-- Values representable by exactly `width` digits in the given base. -/
abbrev Value (base width : Nat) := Fin (base ^ width)

private def encodeList (base : Nat) (basePositive : 0 < base) :
    (width : Nat) → Value base width → List (Fin base)
  | 0, _ => []
  | width + 1, value =>
      let place := base ^ width
      let high : Fin base :=
        ⟨value.val / place, by
          apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos basePositive)).2
          simpa [Nat.pow_succ'] using value.isLt⟩
      let low : Value base width :=
        ⟨value.val % place, Nat.mod_lt _ (Nat.pow_pos basePositive)⟩
      high :: encodeList base basePositive width low

@[simp] private theorem encodeList_length
    (base : Nat) (basePositive : 0 < base) (width : Nat)
    (value : Value base width) :
    (encodeList base basePositive width value).length = width := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp [encodeList, ih]

private theorem digit_of_mod_pow
    (base value width exponent : Nat) (exponentLt : exponent < width) :
    ((value % base ^ width) / base ^ exponent) % base =
      (value / base ^ exponent) % base := by
  have divides : base ^ exponent * base ∣ base ^ width := by
    rw [← Nat.pow_succ]
    exact Nat.pow_dvd_pow base (Nat.succ_le_of_lt exponentLt)
  calc
    ((value % base ^ width) / base ^ exponent) % base =
        (value % base ^ width) % (base ^ exponent * base) /
          base ^ exponent :=
      (Nat.mod_mul_right_div_self _ _ _).symm
    _ = value % (base ^ exponent * base) / base ^ exponent := by
      rw [Nat.mod_mod_of_dvd value divides]
    _ = (value / base ^ exponent) % base :=
      Nat.mod_mul_right_div_self _ _ _

private theorem encodeList_getElem
    (base : Nat) (basePositive : 0 < base) (width : Nat)
    (value : Value base width) (index : Nat) (indexLt : index < width) :
    ((encodeList base basePositive width value)[index]'(by simpa using indexLt)).val =
      (value.val / base ^ (width - 1 - index)) % base := by
  induction width generalizing index with
  | zero => omega
  | succ width ih =>
      cases index with
      | zero =>
          have highBound : value.val / base ^ width < base := by
            apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos basePositive)).2
            simpa [Nat.pow_succ'] using value.isLt
          simp [encodeList, Nat.mod_eq_of_lt highBound]
      | succ index =>
          have indexLt' : index < width := by omega
          have exponentLt : width - 1 - index < width := by omega
          simp only [encodeList, List.getElem_cons_succ]
          rw [ih _ index indexLt']
          rw [digit_of_mod_pow base value.val width (width - 1 - index) exponentLt]
          congr 3 <;> omega

private def decodeList (base : Nat) : List (Fin base) → Nat
  | [] => 0
  | digit :: rest =>
      digit.val * base ^ rest.length + decodeList base rest

private theorem decodeList_lt
    (base : Nat) (digits : List (Fin base)) :
    decodeList base digits < base ^ digits.length := by
  induction digits with
  | nil => simp [decodeList]
  | cons digit rest ih =>
      have step :
          digit.val * base ^ rest.length + decodeList base rest <
            (digit.val + 1) * base ^ rest.length := by
        simpa [Nat.add_mul] using
          Nat.add_lt_add_left ih (digit.val * base ^ rest.length)
      have digitBound : digit.val + 1 ≤ base :=
        Nat.succ_le_iff.mpr digit.isLt
      calc
        decodeList base (digit :: rest) =
            digit.val * base ^ rest.length + decodeList base rest := rfl
        _ < (digit.val + 1) * base ^ rest.length := step
        _ ≤ base * base ^ rest.length :=
          Nat.mul_le_mul_right (base ^ rest.length) digitBound
        _ = base ^ (digit :: rest).length := by
          simp [Nat.pow_succ']

private theorem decodeList_encodeList
    (base : Nat) (basePositive : 0 < base) (width : Nat)
    (value : Value base width) :
    decodeList base (encodeList base basePositive width value) = value.val := by
  induction width with
  | zero =>
      have valueZero : value.val = 0 := by
        have valueBound := value.isLt
        simp only [Nat.pow_zero] at valueBound
        omega
      simp [encodeList, decodeList, valueZero]
  | succ width ih =>
      simp [encodeList, decodeList, ih, Nat.div_add_mod']

private theorem encodeList_decodeList
    (base : Nat) (basePositive : 0 < base)
    (digits : List (Fin base)) :
    encodeList base basePositive digits.length
        ⟨decodeList base digits, decodeList_lt base digits⟩ = digits := by
  induction digits with
  | nil => rfl
  | cons digit rest ih =>
      let place := base ^ rest.length
      have placePositive : 0 < place := Nat.pow_pos basePositive
      have restBound : decodeList base rest < place :=
        decodeList_lt base rest
      have highValue :
          (digit.val * place + decodeList base rest) / place = digit.val := by
        rw [Nat.mul_comm digit.val place, Nat.mul_add_div placePositive]
        simp [Nat.div_eq_of_lt restBound]
      have lowValue :
          (digit.val * place + decodeList base rest) % place = decodeList base rest := by
        rw [Nat.mul_comm digit.val place, Nat.mul_add_mod_self_left]
        exact Nat.mod_eq_of_lt restBound
      have highBound :
          (digit.val * place + decodeList base rest) / place < base := by
        rw [highValue]
        exact digit.isLt
      have lowBound :
          (digit.val * place + decodeList base rest) % place <
            base ^ rest.length := by
        rw [lowValue]
        exact restBound
      simp only [List.length_cons, encodeList, decodeList]
      change
        (⟨(digit.val * place + decodeList base rest) / place, highBound⟩ : Fin base) ::
            encodeList base basePositive rest.length
              ⟨(digit.val * place + decodeList base rest) % place, lowBound⟩ =
          digit :: rest
      have highFin :
          (⟨(digit.val * place + decodeList base rest) / place, highBound⟩ : Fin base) =
            digit :=
        Fin.eq_of_val_eq highValue
      have lowFin :
          (⟨(digit.val * place + decodeList base rest) % place, lowBound⟩ :
              Value base rest.length) =
            ⟨decodeList base rest, decodeList_lt base rest⟩ :=
        Fin.eq_of_val_eq lowValue
      rw [highFin, lowFin, ih]

private theorem encodeList_decodeList_of_length
    (base : Nat) (basePositive : 0 < base) (width : Nat)
    (digits : List (Fin base)) (lengthEq : digits.length = width) :
    encodeList base basePositive width
        ⟨decodeList base digits, by
          simpa [← lengthEq] using decodeList_lt base digits⟩ = digits := by
  subst width
  exact encodeList_decodeList base basePositive digits

/-- Decode fixed-width, big-endian digits as a natural number. -/
def decodeNat {base width : Nat} (digits : Digits base width) : Nat :=
  decodeList base digits.toList

/-- A decoded value always fits in the range determined by its width. -/
theorem decodeNat_lt {base width : Nat} (digits : Digits base width) :
    decodeNat digits < base ^ width := by
  simpa [decodeNat] using decodeList_lt base digits.toList

/-- Encode a natural number modulo the range determined by the width. -/
def encodeNat (base width value : Nat) (basePositive : 0 < base) :
    Digits base width :=
  let bounded : Value base width :=
    ⟨value % base ^ width, Nat.mod_lt _ (Nat.pow_pos basePositive)⟩
  ⟨(encodeList base basePositive width bounded).toArray, by simp⟩

/-- Encoding always has exactly the requested number of digits. -/
@[simp] theorem encodeNat_length
    (base width value : Nat) (basePositive : 0 < base) :
    (encodeNat base width value basePositive).toList.length = width := by
  simp

/-- Decoding an encoded natural returns its residue in the represented range. -/
@[simp] theorem decodeNat_encodeNat
    (base width value : Nat) (basePositive : 0 < base) :
    decodeNat (encodeNat base width value basePositive) = value % base ^ width := by
  simp [decodeNat, encodeNat, decodeList_encodeList]

/-- In-range naturals survive encoding and decoding unchanged. -/
theorem decodeNat_encodeNat_of_lt
    (base width value : Nat) (basePositive : 0 < base)
    (valueBound : value < base ^ width) :
    decodeNat (encodeNat base width value basePositive) = value := by
  simp [Nat.mod_eq_of_lt valueBound]

/-- Encoding a decoded digit vector reproduces that vector. -/
@[simp] theorem encodeNat_decodeNat
    {base width : Nat} (basePositive : 0 < base)
    (digits : Digits base width) :
    encodeNat base width (decodeNat digits) basePositive = digits := by
  apply Vector.toList_inj.mp
  have decodedBound :
      decodeList base digits.toList < base ^ width := by
    simpa using decodeList_lt base digits.toList
  have decodedMod :
      decodeList base digits.toList % base ^ width = decodeList base digits.toList :=
    Nat.mod_eq_of_lt decodedBound
  have listRoundtrip := encodeList_decodeList_of_length
    base basePositive width digits.toList Vector.length_toList
  simp [encodeNat, decodeNat]
  simpa [decodedMod] using
    listRoundtrip

/-- Encode an intrinsically range-checked value. -/
def encode (base width : Nat) (basePositive : 0 < base)
    (value : Value base width) : Digits base width :=
  encodeNat base width value.val basePositive

/-- The digit at `index`, counted from the most-significant end. -/
theorem encode_get
    (base width : Nat) (basePositive : 0 < base)
    (value : Value base width) (index : Fin width) :
    ((encode base width basePositive value).get index).val =
      (value.val / base ^ (width - 1 - index.val)) % base := by
  change
    ((encode base width basePositive value)[index.val]'index.isLt).val =
      (value.val / base ^ (width - 1 - index.val)) % base
  simp [encode, encodeNat, encodeList_getElem,
    Nat.mod_eq_of_lt value.isLt]

/-- Decode into an intrinsically range-checked value. -/
def decode {base width : Nat} (digits : Digits base width) : Value base width :=
  ⟨decodeNat digits, decodeNat_lt digits⟩

@[simp] theorem decode_encode
    (base width : Nat) (basePositive : 0 < base)
    (value : Value base width) :
    decode (encode base width basePositive value) = value := by
  apply Fin.ext
  simp [decode, encode, Nat.mod_eq_of_lt value.isLt]

@[simp] theorem encode_decode
    {base width : Nat} (basePositive : 0 < base)
    (digits : Digits base width) :
    encode base width basePositive (decode digits) = digits := by
  simp [encode, decode]

end Solcore.Util.FixedRadix
