import Solcore.Frontend.SourceCoreCallablePairedAncestry
import Solcore.Frontend.SourceCoreCallablePairedFrameCodec
import Solcore.SourceSemantics.CoreLowering.CallablePairedContextFrames

/-! Small kernel-checked native laws. The carrier preserves parent order and
rejects malformed shapes. These tests intentionally grant no provenance to a
well-typed frame or to its numeric words; owned compiler tests supply that
separate boundary. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePairedFrames
open Solcore Core Frontend
abbrev PairedFrame := Solcore.Frontend.SourceCoreCallablePairedFrames.Frame
private def w (n : Nat) : Word := Word.ofNatModulo n
private def layout : Solcore.Frontend.SourceCoreCallablePairedFrames.Layout := ⟨⟨0⟩⟩
private def definitions : DataEnvironment := [layout.definition]
private theorem registered : layout.Registered definitions := ⟨rfl⟩
private def caller : PairedFrame := .named (w 7)
private def lexical : PairedFrame := .named (w 8)
private def current : PairedFrame := .view (w 3) (w 9) caller
private def paired : PairedFrame := .appliedView (w 3) (w 9) caller lexical

example : definitions.WellFormed := DataEnvironment.isWellFormed_sound rfl

example : RuntimeValueHasType [] (Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout paired) layout.type definitions :=
  Solcore.Frontend.SourceCoreCallablePairedFrames.encode_runtime_typed [] registered paired

example : SourceCoreCallablePairedFrameCodec.decode layout (Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout paired) = some paired :=
  SourceCoreCallablePairedFrameCodec.decode_encode layout paired

example : Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout paired ≠ Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout (.appliedView (w 3) (w 9) lexical caller) := by
  intro same
  have decoded := congrArg (SourceCoreCallablePairedFrameCodec.decode layout) same
  rw [SourceCoreCallablePairedFrameCodec.decode_encode, SourceCoreCallablePairedFrameCodec.decode_encode] at decoded
  have different : paired ≠ .appliedView (w 3) (w 9) lexical caller := by decide
  exact different (Option.some.inj decoded)

example : SourceCoreCallablePairedFrameCodec.decode layout
    (.constructed layout.appliedView (.pair (.word (w 3)) (.pair (.word (w 9)) .unit))) = none := rfl

example : SourceCoreCallablePairedFrameCodec.decode layout
    (.constructed ⟨⟨1⟩, 4⟩ (.pair (.word (w 3)) (.pair (.word (w 9))
      (.pair (Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout caller) (Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout lexical))))) = none := rfl

example : SourceCoreCallablePairedFrameCodec.decode layout (.cellRef layout.type 0) = none := rfl

example : Solcore.Frontend.SourceCoreCallablePairedFrames.selectedFrame (w 9) lexical current = paired := rfl

example : Solcore.Frontend.SourceCoreCallablePairedFrames.selectedFrame (w 10) lexical current = .lambda (w 10) lexical := rfl

example : HasType [layout.type, layout.type] (Solcore.Frontend.SourceCoreCallablePairedFrames.lambdaFrame layout (w 9) (.var 0) (.var 1))
    layout.type definitions := Solcore.Frontend.SourceCoreCallablePairedFrames.lambdaFrame_hasType registered (w 9) (.var rfl) (.var rfl)

private theorem selectedEvaluation : Evaluates [Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout lexical, Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout current] [.word (w 55)]
    (Solcore.Frontend.SourceCoreCallablePairedFrames.lambdaFrame layout (w 9) (.var 0) (.var 1)) (Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout paired) [.word (w 55)] :=
  by simpa only [Solcore.Frontend.SourceCoreCallablePairedFrames.selectedFrame, current, paired, ↓reduceIte] using
    SourceSemantics.CoreLowering.CallablePairedContextFrames.lambdaFrame_evaluates
      (layout := layout) (lexicalFrame := lexical) (currentFrame := current) (w 9) (.var rfl) (.var rfl) [.word (w 55)]

example : ∃ required, ∀ fuel, required ≤ fuel → runStateful fuel (.initial (Solcore.Frontend.SourceCoreCallablePairedFrames.lambdaFrame layout (w 9) (.var 0) (.var 1))
    [Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout lexical, Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout current] [.word (w 55)]) =
    .done (Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout paired) [.word (w 55)] :=
  evaluation_runStateful_complete_with_sufficient_fuel selectedEvaluation

/-- Failure does not read a missing administrative reference. -/
example : Evaluates [] []
    (Solcore.Frontend.SourceCoreCallablePairedAncestry.viewLower layout .word .word (w 3) (w 9) 999
      (LanguageResult.failure (CallableContract.functionType .word .word) (.word (w 44))))
    (.inLeft (CallableContract.functionType .word .word) (.word (w 44))) [] :=
  Solcore.Frontend.SourceCoreCallablePairedAncestry.viewLower_failure (.inLeft .word)

private def original : Value :=
  .pair (.pair (.inLeft .word .unit)
    (.closure .word (LanguageResult.resultType .word) (LanguageResult.success (.var 0)) [.cellRef layout.type 0])) (.word (w 9))
private def originalExpression : Expr :=
  .pair (.pair (.inLeft .word .unit)
    (.lambda .word (LanguageResult.resultType .word) (LanguageResult.success (.var 0)))) (.word (w 9))

/-- Successful wrapping saves the frame at the read, then the original
callable, and preserves the heap exactly. Both identity fields remain intact. -/
example : Evaluates [.cellRef layout.type 0] [Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout caller]
    (Solcore.Frontend.SourceCoreCallablePairedAncestry.viewLower layout .word .word (w 3) (w 9) 0 (LanguageResult.success originalExpression))
    (.inRight .word (.pair (.pair (.inLeft .word .unit)
      (.closure .word (LanguageResult.resultType .word) (Solcore.Frontend.SourceCoreCallablePairedAncestry.viewBody layout (w 3) (w 9) 0)
        [Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout caller, original, .cellRef layout.type 0])) (.word (w 9))))
    [Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout caller] :=
  Solcore.Frontend.SourceCoreCallablePairedAncestry.viewLower_evaluates (.inRight (.pair (.pair (.inLeft .unit) .lambda) .word)) rfl rfl

end Tests.SourceCoreCallablePairedFrames
