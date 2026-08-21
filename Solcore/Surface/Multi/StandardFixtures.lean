import Solcore.Standard.CanonicalData

set_option autoImplicit false

namespace Solcore.Surface.Multi

/-- Closed failure of the strict UTF-8 decoder. -/
inductive Utf8StrictError where
  | invalid
  deriving Repr, BEq, DecidableEq

/-- Kernel-reducible strict UTF-8 decoding with no replacement character. -/
def decodeUtf8Strict (raw : ByteArray) : Except Utf8StrictError String :=
  match raw.utf8Decode? with
  | none => .error .invalid
  | some characters => .ok (String.ofList characters.toList)

/-- The strict decoder accepts exactly byte arrays with a complete valid UTF-8
partition. -/
theorem decodeUtf8Strict_accepts_iff_valid (raw : ByteArray) :
    (∃ text, decodeUtf8Strict raw = .ok text) ↔ raw.IsValidUTF8 := by
  cases decoded : raw.utf8Decode? with
  | none =>
      simp only [decodeUtf8Strict, decoded, reduceCtorEq, exists_const,
        false_iff]
      intro valid
      have some : raw.utf8Decode?.isSome :=
        ByteArray.isSome_utf8Decode?_iff.mpr valid
      simp [decoded] at some
  | some characters =>
      constructor
      · intro accepted
        exact ByteArray.isSome_utf8Decode?_iff.mp (by simp [decoded])
      · intro valid
        exact ⟨String.ofList characters.toList, by
          simp [decodeUtf8Strict, decoded]⟩

/-- Every successful strict decode re-encodes to the exact input bytes. -/
theorem decodeUtf8Strict_roundTrip
    {raw : ByteArray} {text : String}
    (decoded : decodeUtf8Strict raw = .ok text) :
    String.toUTF8 text = raw := by
  cases selected : raw.utf8Decode? with
  | none => simp [decodeUtf8Strict, selected] at decoded
  | some characters =>
      have textEq : text = String.ofList characters.toList := by
        simpa [decodeUtf8Strict, selected] using decoded.symm
      subst text
      have encoded := ByteArray.utf8Encode_get_utf8Decode?
        (b := raw) (h := by simp [selected])
      simpa only [selected, Option.get_some,
        String.toUTF8_eq_toByteArray,
        String.toByteArray_ofList] using encoded

end Solcore.Surface.Multi
