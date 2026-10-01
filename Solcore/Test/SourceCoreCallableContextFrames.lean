import Solcore.Frontend.SourceCoreCallableContextFrames
import Solcore.Core.BoundedSafety

set_option autoImplicit false
namespace Tests.SourceCoreCallableContextFrames
open Solcore Solcore.Core Solcore.Frontend.SourceCoreCallableContextFrames
abbrev ContextFrame := Solcore.Frontend.SourceCoreCallableContextFrames.Frame
private def w (value : Nat) : Word := Word.ofNatModulo value
private def layout : Layout := ⟨⟨0⟩⟩
private def definitions : DataEnvironment := [layout.definition]
private theorem registered : layout.Registered definitions := ⟨rfl⟩
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

example : RuntimeValueHasType [] (encode layout (.lambda (w 1) (.view (w 7) (w 1) (.named (w 3)))))
    layout.type definitions := encode_runtime_typed [] registered _

private def scopedBody (fail : Bool) : Expr :=
  .letE (.storeCell (.var 1) (.word (w 7)))
    (if fail then LanguageResult.failure .word (.word (w 23)) else LanguageResult.success (.word (w 11)))
private def program (fail : Bool) : Program := ⟨LanguageResult.resultType .word,
  .letE (.newCell .word (.word (w 99)))
    (allocate layout (withFrame (.var 0) (named layout (w 3)) (scopedBody fail))), definitions⟩

private def quoteFrame : ContextFrame → Expr
  | .empty => empty layout
  | .named origin => named layout origin
  | .lambda origin captured => lambda layout origin (quoteFrame captured)
  | .view id target parent => view layout id target (quoteFrame parent)

private def lambdaCase (current captured : ContextFrame) (expected : ContextFrame) : IO Unit := do
  let program : Program := ⟨layout.type, lambdaFrame layout (w 11) (quoteFrame captured) (quoteFrame current), definitions⟩
  assertTrue program.check "dynamic lambda context failed actual Core checking"
  match program.runStateful 10000 with
  | .done result store =>
      assertTrue (result == encode layout expected) "dynamic lambda context changed lexical ancestry"
      assertTrue store.isEmpty "context selection allocated cells"
  | result => throw (IO.userError s!"dynamic lambda context did not finish: {reprStr result}")

def run : IO Unit := do
  for fail in [false, true] do
    let program := program fail
    assertTrue program.check "administrative context save/restore failed Core checking"
    let expected := if fail then Value.inLeft .word (.word (w 23)) else .inRight .word (.word (w 11))
    match program.runStateful 10000 with
    | .done result store =>
        assertTrue (result == expected) "administrative context changed language result"
        assertTrue (store == [.word (w 7), encode layout .empty])
          "context restore lost body effects or retained the callee frame"
    | result => throw (IO.userError s!"administrative context did not finish: {reprStr result}")
    match program.runStateful 9 with
    | .outOfFuel state =>
        match runStateful 10000 state with
        | .done result store =>
            assertTrue (result == expected && store == [.word (w 7), encode layout .empty])
              "administrative context checkpoint/resume changed result or restoration"
        | result => throw (IO.userError s!"context checkpoint did not finish: {reprStr result}")
    | _ => throw (IO.userError "context regression did not suspend")
  let captured : ContextFrame := .lambda (w 17) (.named (w 3))
  lambdaCase .empty captured (.lambda (w 11) captured)
  lambdaCase (.named (w 99)) captured (.lambda (w 11) captured)
  lambdaCase (.lambda (w 99) .empty) captured (.lambda (w 11) captured)
  lambdaCase (.view (w 7) (w 11) (.named (w 99))) captured
    (.lambda (w 11) (.view (w 7) (w 11) captured))
  lambdaCase (.view (w 7) (w 12) (.named (w 99))) captured (.lambda (w 11) captured)
  IO.println "ordinary Core dynamic callable ancestry and scoped context restoration GREEN"

end Tests.SourceCoreCallableContextFrames
