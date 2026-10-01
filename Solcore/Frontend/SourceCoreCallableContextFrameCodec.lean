import Solcore.Frontend.SourceCoreCallableContextFrames

/-! Exact decoding of the ordinary nominal callable-frame carrier. This
recognizes values only; source ownership and execution history are separate
receipts supplied by the enclosing compiler artifact. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableContextFrameCodec
open Core SourceCoreCallableContextFrames

def decode (layout : Layout) : Value → Option SourceCoreCallableContextFrames.Frame
  | .constructed constructor .unit => if constructor = layout.empty then some .empty else none
  | .constructed constructor (.word origin) =>
      if constructor = layout.named then some (.named origin) else none
  | .constructed constructor (.pair (.word first) second) =>
      if constructor = layout.lambda then (decode layout second).map (.lambda first)
      else if constructor = layout.view then
        match second with
        | .pair (.word target) parent => (decode layout parent).map (.view first target)
        | _ => none
      else none
  | _ => none

theorem decode_encode (layout : Layout) (frame : SourceCoreCallableContextFrames.Frame) :
    decode layout (encode layout frame) = some frame := by
  induction frame with
  | empty => simp [decode, encode]
  | named origin => simp [decode, encode]
  | lambda origin captured ih =>
      cases captured <;> simp [decode, encode, Layout.lambda, Layout.empty, Layout.named, Layout.view, *] at * <;> assumption
  | view view target parent ih =>
      simp [decode, encode, Layout.lambda, Layout.view, ih]

theorem decode_sound (layout : Layout) (value : Value) (frame : SourceCoreCallableContextFrames.Frame)
    (decoded : decode layout value = some frame) : value = encode layout frame := by
  revert frame
  induction value using decode.induct layout with
  | case1 =>
      intro frame decoded
      simp [decode] at decoded
      subst frame
      rfl
  | case2 constructor different =>
      intro frame decoded
      simp [decode, different] at decoded
  | case3 origin =>
      intro frame decoded
      simp [decode] at decoded
      subst frame
      rfl
  | case4 constructor origin different =>
      intro frame decoded
      simp [decode, different] at decoded
  | case5 first second ih =>
      intro frame decoded
      rw [decode.eq_def] at decoded
      simp only [↓reduceIte] at decoded
      cases observed : decode layout second with
      | none => simp [observed] at decoded
      | some captured =>
          simp [observed] at decoded
          subst frame
          rw [encode, ih captured observed]
  | case6 first target parent different ih =>
      intro frame decoded
      simp [decode, different] at decoded
      cases observed : decode layout parent with
      | none => simp [observed] at decoded
      | some captured =>
          simp [observed] at decoded
          subst frame
          rw [encode, ih captured observed]
  | case7 first second malformed different =>
      intro frame decoded
      rw [decode.eq_def] at decoded
      simp only [different, ↓reduceIte] at decoded
      contradiction
  | case8 constructor first second notLambda notView =>
      intro frame decoded
      rw [decode.eq_def] at decoded
      simp [notLambda, notView] at decoded
  | case9 value notEmpty notNamed notPair =>
      intro frame decoded
      rw [decode.eq_def] at decoded
      split at decoded <;> simp_all

theorem decode_iff (layout : Layout) (value : Value) (frame : SourceCoreCallableContextFrames.Frame) :
    decode layout value = some frame ↔ value = encode layout frame :=
  ⟨decode_sound layout value frame, fun same => same ▸ decode_encode layout frame⟩

end Solcore.Frontend.SourceCoreCallableContextFrameCodec
