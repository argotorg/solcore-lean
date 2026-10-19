import Solcore.Test.SourceCoreSelectedGeneralKeySourceFirst

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralKey
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def word (value : Nat) : Word := Word.ofNatModulo value

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

/-- The unchanged five-function program is checked and compiled with every
original function seeded. Independent Source proofs precede all first results;
exported mapping reuse is an additional native runtime check. -/
def run : IO Unit := do
  let fixture ← compileFixture
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      fixture.recipe.compiled fixture.checked
    | throw (IO.userError "general key complete checked profile rejected")
  require (fixture.recipe.compiled.sourceProgram.functions.length == 5 &&
      fixture.recipe.compiled.indexed.base.functions.length == 5 && profile.table.rows.length == 5)
    "general key original/cache/profile rows changed"
  let mut readHeaps := []
  for name in ["pairRead","proxyRead","nominalRead"] do
    let row ← observeRow fixture name
    let ⟨key,shape⟩ ← observeRead row.original.function.typedBody
    let started ← observeStarted fixture row.original.key [publicMap key (word 7) (word 90)]
    have _sourceFirst := read_from_source row profile shape (word 7) (word 90) started
    let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
      | throw (IO.userError "general key read zero fuel did not suspend")
    let .succeeded completed ← suspended.resume 100000 1000
      | throw (IO.userError s!"general key {name} failed")
    require (completed.value == .word (word 7)) "general key first-match lookup changed"
    readHeaps := readHeaps ++ [started.session.heapSize,completed.session.heapSize]
  require (readHeaps == [6,15,6,15,6,15]) "general key exact read heaps changed"
  let mut writeHeaps := []
  for (name,reader) in [("pairWrite","pairRead"),("proxyWrite","proxyRead")] do
    let row ← observeRow fixture name
    let readRow ← observeRow fixture reader
    let ⟨key,shape⟩ ← observeWrite row.original.function.typedBody
    require (shape.right.resolution.rawValue == 3) "general key original RHS value changed"
    let started ← observeStarted fixture row.original.key [publicMap key (word 7) (word 90)]
    have _sourceFirst := write_from_source row profile shape (word 7) (word 90) started
    let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
      | throw (IO.userError "general key write zero fuel did not suspend")
    let .succeeded completed ← suspended.resume 100000 1000
      | throw (IO.userError s!"general key {name} failed")
    require (completed.value == publicMap key (word 10) (word 90)) "general key first-match write changed later duplicate"
    let again ← get "general key exported mapping reuse" (completed.session.start row.original.key [completed.value])
    let .succeeded reused ← again.resume 100000 1000
      | throw (IO.userError "general key repeated compound write failed")
    require (reused.value == publicMap key (word 13) (word 90)) "general key repeated write changed ordered entries"
    let read ← get "general key updated mapping read" (reused.session.start readRow.original.key [reused.value])
    let .succeeded readBack ← read.resume 100000 1000
      | throw (IO.userError "general key read after write failed")
    require (readBack.value == .word (word 13)) "general key read after reuse changed"
    writeHeaps := writeHeaps ++ [started.session.heapSize,completed.session.heapSize,reused.session.heapSize,readBack.session.heapSize]
  require (writeHeaps == [6,27,48,57,6,27,48,57]) "general key exact write/reuse heaps changed"
  IO.println s!"GENERAL_KEY_COMPLETE_CACHE: originals5/cache5/table{profile.table.rows.length}"
  IO.println s!"GENERAL_KEY_READ_NATIVE_HEAPS: {readHeaps}"
  IO.println s!"GENERAL_KEY_WRITE_REUSE_NATIVE_HEAPS: {writeHeaps}"
  IO.println "GENERAL_KEY_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedGeneralKey
