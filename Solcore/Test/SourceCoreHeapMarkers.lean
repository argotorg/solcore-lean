import Solcore.Frontend.SourceCoreHeapMarkers
import Solcore.Core.BoundedSafety

/-! Source payload references retain their caller scope when hidden marker
cells precede them. Native checkpoints can stop between the two allocations;
the marker alone does not decode as a completed source cell. -/

set_option autoImplicit false
namespace Tests.SourceCoreHeapMarkers
open Solcore Solcore.Core
open Solcore.Frontend.SourceCoreHeapMarkers

private def word (value : Nat) : Word := Word.ofNatModulo value
private def layout : Layout := ⟨⟨0⟩, .cell .word⟩
private def definitions : DataEnvironment := [layout.definition]
private def functionType : Ty := .function .word .word
private def functionBody : Expr := .binary .wordAdd (.loadCell (.var 1)) (.var 0)
private def initialized : Program := ⟨.word,
  .letE (.newCell .word (.word (word 7)))
    (.letE (allocateInitialized layout functionType (.var 0)
      (.lambda .word .word functionBody))
      (.letE (.storeCell (.var 1) (.word (word 9)))
        (.caseE (.loadCell (.var 1)) (.word Word.zero) (.apply (.var 0) (.word (word 3)))))),
  definitions⟩
private def uninitialized : Program := ⟨LanguageResult.resultType functionType,
  .letE (.newCell .word (.word (word 7)))
    (.letE (allocate layout functionType (.var 0))
      (OptionalCell.read functionType (.var 0) (word 61))), definitions⟩
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

example : layout.Registered definitions := ⟨.cell .word, rfl⟩

/-- The uninitialized function needs no dummy closure, even with metadata. -/
example : HasType [.cell .word] (allocate layout functionType (.var 0))
    (OptionalCell.referenceType functionType) definitions :=
  allocate_hasType ⟨.cell .word, rfl⟩ (.var rfl) (.function .word .word)

def run : IO Unit := do
  assertTrue initialized.check "marked function allocation failed Core checking"
  match initialized.runStateful 10000 with
  | .done value store =>
      assertTrue (value == .word (word 12)) "marker binding changed the actual closure capture"
      assertTrue (store.length == 3 && store[0]? == some (.word (word 9))) "marked allocation changed its store prefix"
      match completedPair layout store 1 with
      | some (.cellRef .word 0, .inRight .unit (.closure .word .word body captured)) =>
          assertTrue (body == functionBody && captured == [.cellRef .word 0])
            "marker or initializer temporary escaped into closure captures"
      | _ => throw (IO.userError "marked function payload or capture metadata changed")
  | other => throw (IO.userError s!"marked function did not complete: {reprStr other}")
  assertTrue uninitialized.check "marked uninitialized function failed Core checking"
  match uninitialized.runStateful 10000 with
  | .done (.inLeft type (.word reason)) store =>
      assertTrue (type == functionType && reason == word 61) "marked uninitialized read changed its source fault"
      assertTrue (completedPair layout store 1 == some (.cellRef .word 0, .inLeft functionType .unit))
        "uninitialized source cell was lost during marker observation"
  | other => throw (IO.userError s!"marked uninitialized function changed: {reprStr other}")
  let mut sawPartial := false
  for fuel in List.range 96 do
    match initialized.runStateful fuel with
    | .outOfFuel checkpoint =>
        if checkpoint.store.length == 2 then
          sawPartial := true
          assertTrue ((completedPair layout checkpoint.store 1).isNone)
            "marker-only checkpoint exported an unfinished source cell"
        match runStateful 10000 checkpoint with
        | .done value _ => assertTrue (value == .word (word 12)) "marked source cell resume changed"
        | other => throw (IO.userError s!"marked source cell resume failed: {reprStr other}")
    | .done value _ => assertTrue (value == .word (word 12)) "marked source cell finite result changed"
    | .fault error _ => throw (IO.userError s!"marked source cell machine fault: {reprStr error}")
  assertTrue sawPartial "native checkpoints did not cover a marker without its payload"
  IO.println "ordinary Core source allocation markers and native checkpoints GREEN"

end Tests.SourceCoreHeapMarkers
