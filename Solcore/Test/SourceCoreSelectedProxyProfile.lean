import Solcore.Test.SourceCoreSelectedProxySourceFirst

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProxy
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

/-- One complete checked cache supplies both proxy literals and a genuine
metadata-bearing initial proxy input. Source traces precede each public result. -/
def run : IO Unit := do
  let fixture ← compileFixture
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      fixture.recipe.compiled fixture.checked
    | throw (IO.userError "proxy complete checked profile rejected")
  require (fixture.recipe.compiled.sourceProgram.functions.length == 3 &&
      fixture.recipe.compiled.indexed.base.functions.length == 3 && profile.table.rows.length == 3)
    "proxy original/cache/profile rows changed"
  let echo ← observeRow fixture "echoWord"
  let echoShape ← observeEcho echo.original.function.typedBody .word
  let mut literalHeaps := []
  for (name, inner) in [("proxyWord", TypeSystem.Ty.word), ("proxyBool", .bool)] do
    let row ← observeRow fixture name
    let shape ← observeLiteral row.original.function.typedBody inner
    let started ← observeStarted fixture row.original.key []
    have _sourceFirst := literal_from_source row profile inner shape started
    let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
      | throw (IO.userError "proxy literal zero fuel did not suspend")
    let .succeeded completed ← suspended.resume 100000 1000
      | throw (IO.userError "proxy literal failed")
    require (completed.value == .proxy inner) "proxy original raw inner identity changed"
    literalHeaps := literalHeaps ++ [started.session.heapSize, completed.session.heapSize]
    if inner == .word then
      let pending ← get "proxy same-session exported input"
        (completed.session.start echo.original.key [completed.value])
      let .succeeded echoed ← pending.resume 100000 1000
        | throw (IO.userError "proxy same-session exported input failed")
      require (echoed.value == .proxy .word && echoed.session.heapSize == 7)
        "proxy same-session raw identity/heap changed"
  require (literalHeaps == [4,4,4,4]) "proxy literal exact heaps changed"
  let started ← observeStarted fixture echo.original.key [.proxy .word]
  have _sourceInput := echo_from_source echo profile .word echoShape started
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "proxy input zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "proxy initial data input failed")
  require (completed.value == .proxy .word) "proxy initial output identity changed"
  match completed.session.start echo.original.key [.proxy .bool] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "proxy mismatched raw inner type accepted")
  let again ← get "proxy valid reuse after input rejection"
    (completed.session.start echo.original.key [completed.value])
  let .succeeded reused ← again.resume 100000 1000
    | throw (IO.userError "proxy reuse after input rejection failed")
  require (reused.value == .proxy .word) "proxy reused raw identity changed"
  let inputHeaps := [started.session.heapSize, completed.session.heapSize, reused.session.heapSize]
  require (inputHeaps == [4,7,10]) "proxy initial/reuse exact heaps changed"
  IO.println s!"PROXY_COMPLETE_CACHE: originals3/cache3/table{profile.table.rows.length}"
  IO.println s!"PROXY_LITERAL_NATIVE_HEAPS: {literalHeaps}"
  IO.println s!"PROXY_INPUT_REUSE_NATIVE_HEAPS: {inputHeaps}"
  IO.println "PROXY_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedProxy
