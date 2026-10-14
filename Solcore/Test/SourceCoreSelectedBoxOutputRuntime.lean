import Solcore.Test.SourceCoreSelectedBoxOutputSourceFirst

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedBoxOutput
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def run : IO Unit := do
  let fixture ← fixture
  let started ← observeStarted fixture
  have _sourceFirst := from_source fixture started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "box initial call did not suspend at zero fuel")
  let .succeeded first ← suspended.resume 100000 1000
    | throw (IO.userError "box initial call did not complete")
  require (first.value == .constructed fixture.shape.instantiation [.word seed])
    "initial full constructor output changed"
  let secondWord := Word.ofNatModulo 52
  let .ok checkpoint := first.session.start fixture.named.signature.key [.word secondWord] runOptions.inputValidationFuel
    | throw (IO.userError "later box call did not start")
  let .outOfFuel suspended ← checkpoint.resume 0 0
    | throw (IO.userError "later box call did not suspend at zero fuel")
  let .succeeded second ← suspended.resume 100000 1000
    | throw (IO.userError "later box call did not complete")
  require (second.value == .constructed fixture.shape.instantiation [.word secondWord])
    "later full constructor output changed"
  require ([started.session.heapSize, first.session.heapSize, second.session.heapSize] == [2, 5, 8])
    "box physical heap sizes changed"
  require (fixture.recipe.compiled.indexed.base.functions.length == 1) "box cache changed"
  IO.println s!"SOURCE_FIRST_CONSTRUCTOR_OUTPUT_PASS: actual check/compile/profile; independent original read/constructor traces; closed initial then later full ReturnedValue and exact Source heap; no manual well-formedness; zero-fuel resume both calls; Wrap(37), Wrap(52); heaps{[started.session.heapSize, first.session.heapSize, second.session.heapSize]}"

end Tests.SourceCoreSelectedBoxOutput
