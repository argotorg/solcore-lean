import Solcore.Frontend.SourceCoreCallablePairedFrames

/-! Exact paired-frame decoding. A decoded tree preserves read-caller and
lexical parents in order. This is a carrier law, not source-history authority.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedFrameCodec
open Core SourceCoreCallablePairedFrames
abbrev PairedFrame := SourceCoreCallablePairedFrames.Frame

def decode (layout : Layout) : Value → Option PairedFrame
  | .constructed constructor .unit => if constructor = layout.empty then some .empty else none
  | .constructed constructor (.word origin) => if constructor = layout.named then some (.named origin) else none
  | .constructed constructor (.pair (.word first) second) =>
      if constructor = layout.lambda then (decode layout second).map (.lambda first)
      else if constructor = layout.view then
        match second with
        | .pair (.word target) caller => (decode layout caller).map (.view first target)
        | _ => none
      else if constructor = layout.appliedView then
        match second with
        | .pair (.word target) (.pair caller lexical) => do
            let caller ← decode layout caller
            let lexical ← decode layout lexical
            pure (.appliedView first target caller lexical)
        | _ => none
      else none
  | _ => none

theorem decode_encode (layout : Layout) (frame : PairedFrame) : decode layout (encode layout frame) = some frame := by
  induction frame with
  | empty => simp [decode, encode]
  | named origin => simp [decode, encode]
  | lambda origin captured ih =>
      rw [encode, decode.eq_def]
      simp only [↓reduceIte]
      rw [ih]
      rfl
  | view view target caller ih => simp [decode, encode, Layout.lambda, Layout.view, ih]
  | appliedView view target caller lexical callerIH lexicalIH =>
    simp [decode, encode, Layout.lambda, Layout.view, Layout.appliedView, callerIH, lexicalIH]

theorem decode_sound (layout : Layout) (value : Value) (frame : PairedFrame)
    (decoded : decode layout value = some frame) : value = encode layout frame := by
  revert frame
  induction value using decode.induct layout with
  | case1 => intro frame decoded; simp [decode] at decoded; subst frame; rfl
  | case2 constructor different => intro frame decoded; simp [decode, different] at decoded
  | case3 origin => intro frame decoded; simp [decode] at decoded; subst frame; rfl
  | case4 constructor origin different => intro frame decoded; simp [decode, different] at decoded
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
  | case6 first target caller different ih =>
    intro frame decoded
    simp [decode, different] at decoded
    cases observed : decode layout caller with
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
  | case8 first target caller lexical notLambda notView callerIH lexicalIH =>
    intro frame decoded
    simp only [decode, notLambda, notView, ↓reduceIte] at decoded
    cases callerFound : decode layout caller with
    | none => simp [callerFound] at decoded
    | some callerFrame =>
      cases lexicalFound : decode layout lexical with
      | none => simp [callerFound, lexicalFound] at decoded
      | some lexicalFrame =>
        simp [callerFound, lexicalFound] at decoded
        subst frame
        rw [encode, callerIH callerFrame callerFound, lexicalIH lexicalFrame lexicalFound]
  | case9 first second malformed notLambda notView =>
    intro frame decoded
    rw [decode.eq_def] at decoded
    simp only [notLambda, notView, ↓reduceIte] at decoded
    contradiction
  | case10 constructor first second notLambda notView notApplied =>
    intro frame decoded
    rw [decode.eq_def] at decoded
    simp [notLambda, notView, notApplied] at decoded
  | case11 value notEmpty notNamed notPair =>
    intro frame decoded
    rw [decode.eq_def] at decoded
    split at decoded <;> simp_all

theorem decode_iff (layout : Layout) (value : Value) (frame : PairedFrame) :
    decode layout value = some frame ↔ value = encode layout frame :=
  ⟨decode_sound layout value frame, fun same => same ▸ decode_encode layout frame⟩

end Solcore.Frontend.SourceCoreCallablePairedFrameCodec
