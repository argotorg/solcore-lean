import Solcore.Frontend.SourceCoreCallableContextFrameCodec

set_option autoImplicit false
namespace Tests.SourceCoreCallableContextFrameCodec
open Solcore Solcore.Frontend
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n

def run : IO Unit := do
  let layout : SourceCoreCallableContextFrames.Layout := ⟨⟨3⟩⟩
  let other : SourceCoreCallableContextFrames.Layout := ⟨⟨4⟩⟩
  let frames : List SourceCoreCallableContextFrames.Frame := [.empty, .named (w 1), .lambda (w 2) .empty,
    .view (w 7) (w 2) (.named (w 1)),
    .lambda (w 8) (.view (w 7) (w 2) (.lambda (w 2) (.named (w 1))))]
  for frame in frames do
    assertTrue (SourceCoreCallableContextFrameCodec.decode layout (SourceCoreCallableContextFrames.encode layout frame) == some frame)
      "callable frame did not retain its exact recursive ancestry"
    assertTrue ((SourceCoreCallableContextFrameCodec.decode other (SourceCoreCallableContextFrames.encode layout frame)).isNone)
      "foreign nominal frame layout was accepted"
  let malformed : List Core.Value := [.unit, .word (w 1),
    .constructed layout.empty (.word (w 1)), .constructed layout.named .unit,
    .constructed layout.lambda (.pair (.word (w 2)) (.bool true)),
    .constructed layout.view (.pair (.word (w 7)) (.pair .unit (SourceCoreCallableContextFrames.encode layout .empty))),
    .constructed ⟨layout.dataType, 4⟩ .unit,
    .constructed layout.lambda (.pair (.word (w 2)) (SourceCoreCallableContextFrames.encode other .empty))]
  assertTrue (malformed.all fun value => (SourceCoreCallableContextFrameCodec.decode layout value).isNone)
    "malformed callable frame was accepted"
  IO.println "exact recursive callable frame codec GREEN"

end Tests.SourceCoreCallableContextFrameCodec
