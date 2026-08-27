import Solcore.Foundation.FixedRadix

set_option autoImplicit false

namespace Solcore.Foundation.FixedHex

abbrev Digit := Fin 16

abbrev Digits (width : Nat) := FixedRadix.Digits 16 width

abbrev Value (width : Nat) := FixedRadix.Value 16 width

def encodeDigit (digit : Digit) : Char :=
  Nat.digitChar digit.val

def decodeDigit? : Char → Option Digit
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | 'a' => some 10
  | 'b' => some 11
  | 'c' => some 12
  | 'd' => some 13
  | 'e' => some 14
  | 'f' => some 15
  | _ => none

private theorem decodeDigit?_digitChar
    (value : Nat) (inRange : value < 16) :
    decodeDigit? (Nat.digitChar value) = some ⟨value, inRange⟩ := by
  have cases :
      value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 ∨
      value = 4 ∨ value = 5 ∨ value = 6 ∨ value = 7 ∨
      value = 8 ∨ value = 9 ∨ value = 10 ∨ value = 11 ∨
      value = 12 ∨ value = 13 ∨ value = 14 ∨ value = 15 := by
    omega
  rcases cases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst value <;> rfl

@[simp] theorem decodeDigit?_encodeDigit (digit : Digit) :
    decodeDigit? (encodeDigit digit) = some digit := by
  simpa [encodeDigit] using decodeDigit?_digitChar digit.val digit.isLt

theorem encodeDigit_of_decodeDigit?_eq_some
    (character : Char) (digit : Digit)
    (success : decodeDigit? character = some digit) :
    encodeDigit digit = character := by
  simp only [decodeDigit?] at success
  split at success <;> simp_all [encodeDigit]
  all_goals subst digit <;> rfl

def encodeDigits (digits : List Digit) : List Char :=
  digits.map encodeDigit

def decodeDigits? : List Char → Option (List Digit)
  | [] => some []
  | character :: characters => do
      let digit ← decodeDigit? character
      let digits ← decodeDigits? characters
      some (digit :: digits)

@[simp] theorem encodeDigits_length (digits : List Digit) :
    (encodeDigits digits).length = digits.length := by
  simp [encodeDigits]

@[simp] theorem decodeDigits?_encodeDigits (digits : List Digit) :
    decodeDigits? (encodeDigits digits) = some digits := by
  induction digits with
  | nil => rfl
  | cons digit digits ih =>
      rw [show encodeDigits (digit :: digits) =
        encodeDigit digit :: encodeDigits digits from rfl]
      simp [decodeDigits?, ih]

theorem encodeDigits_of_decodeDigits?_eq_some
    (characters : List Char) (digits : List Digit)
    (success : decodeDigits? characters = some digits) :
    encodeDigits digits = characters := by
  induction characters generalizing digits with
  | nil =>
      simp [decodeDigits?] at success
      subst digits
      rfl
  | cons character characters ih =>
      simp only [decodeDigits?] at success
      cases digitResult : decodeDigit? character with
      | none => simp [digitResult] at success
      | some digit =>
          cases tailResult : decodeDigits? characters with
          | none => simp [digitResult, tailResult] at success
          | some tail =>
              simp [digitResult, tailResult] at success
              subst digits
              change encodeDigit digit :: encodeDigits tail =
                character :: characters
              rw [encodeDigit_of_decodeDigit?_eq_some _ _ digitResult,
                ih _ tailResult]

def encodeDigitsText (digits : List Digit) : String :=
  String.ofList ('0' :: 'x' :: encodeDigits digits)

def decodeDigitsText? (text : String) : Option (List Digit) :=
  match text.toList with
  | '0' :: 'x' :: characters => decodeDigits? characters
  | _ => none

@[simp] theorem encodeDigitsText_length (digits : List Digit) :
    (encodeDigitsText digits).length = digits.length + 2 := by
  rw [encodeDigitsText, String.length_ofList]
  simp [encodeDigits]

@[simp] theorem decodeDigitsText?_encodeDigitsText (digits : List Digit) :
    decodeDigitsText? (encodeDigitsText digits) = some digits := by
  simp [decodeDigitsText?, encodeDigitsText]

theorem encodeDigitsText_of_decodeDigitsText?_eq_some
    (text : String) (digits : List Digit)
    (success : decodeDigitsText? text = some digits) :
    encodeDigitsText digits = text := by
  apply String.toList_injective
  simp [encodeDigitsText]
  simp only [decodeDigitsText?] at success
  split at success <;> simp_all
  exact encodeDigits_of_decodeDigits?_eq_some _ _ success

theorem encodeDigitsText_injective : Function.Injective encodeDigitsText := by
  intro left right equal
  have decoded := congrArg decodeDigitsText? equal
  simpa using decoded

private def ofList? (width : Nat) (digits : List Digit) : Option (Digits width) :=
  if lengthEq : digits.length = width then
    some ⟨digits.toArray, by simpa using lengthEq⟩
  else
    none

@[simp] private theorem ofList?_toList
    {width : Nat} (digits : Digits width) :
    ofList? width digits.toList = some digits := by
  simp [ofList?]
  exact Array.toArray_toList

private theorem toList_of_ofList?_eq_some
    (width : Nat) (raw : List Digit) (digits : Digits width)
    (success : ofList? width raw = some digits) :
    digits.toList = raw := by
  simp only [ofList?] at success
  split at success
  · have vectorEq := Option.some.inj success
    have listEq := congrArg Vector.toList vectorEq
    simpa using listEq.symm
  · contradiction

def encodeText {width : Nat} (value : Value width) : String :=
  encodeDigitsText
    (FixedRadix.encode 16 width (by decide) value).toList

def decodeText? (width : Nat) (text : String) : Option (Value width) := do
  let raw ← decodeDigitsText? text
  let digits ← ofList? width raw
  some (FixedRadix.decode digits)

@[simp] theorem encodeText_length {width : Nat} (value : Value width) :
    (encodeText value).length = width + 2 := by
  simp [encodeText]

@[simp] theorem decodeText?_encodeText
    {width : Nat} (value : Value width) :
    decodeText? width (encodeText value) = some value := by
  simp [decodeText?, encodeText]

theorem encodeText_of_decodeText?_eq_some
    (width : Nat) (text : String) (value : Value width)
    (success : decodeText? width text = some value) :
    encodeText value = text := by
  simp only [decodeText?] at success
  cases rawResult : decodeDigitsText? text with
  | none => simp [rawResult] at success
  | some raw =>
      cases digitsResult : ofList? width raw with
      | none => simp [rawResult, digitsResult] at success
      | some digits =>
          simp [rawResult, digitsResult] at success
          subst value
          rw [encodeText, FixedRadix.encode_decode]
          rw [toList_of_ofList?_eq_some width raw digits digitsResult]
          exact encodeDigitsText_of_decodeDigitsText?_eq_some _ _ rawResult

theorem encodeText_injective (width : Nat) :
    Function.Injective (encodeText : Value width → String) := by
  intro left right equal
  have decoded := congrArg (decodeText? width) equal
  simpa using decoded

end Solcore.Foundation.FixedHex
