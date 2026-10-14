import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile
import Solcore.Test.SourceCoreUnifiedCorpusSupport

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedOrdinaryStageLift
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function stagedFactory() returns (function(Word) returns (Word)) { return lam(comptime item: Word) -> Word { return item; }; }",
    "function ordinaryFactory() returns (function(Word) returns (Word)) { return lam(item: Word) -> Word { return item; }; }",
    "function touch(value: Word) returns (Word) { let copy = value; return copy; }",
    "function invoke(f: function(Word) returns (Word), value: Word) returns (Word) { return f(touch(value)); }"
  ] }]
}

def options : SourceCompiler.Options := {
  checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 512
}

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Completion artifact) := do
  let outcome ← get "ordinary stage public startup" (← session.run key arguments { executionFuel := 100000 })
  match outcome with
  | .succeeded completed => pure completed
  | _ => throw (IO.userError "ordinary stage public success missing")

private def reject {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (handle : SourceCorePublicValues.Handle) (seed : Word) : IO (SourceCoreExecution.Session artifact) := do
  let started ← get "ordinary stage rejection startup" (session.start key [.function handle, .word seed])
  let .outOfFuel suspended ← started.resume 0 0
    | throw (IO.userError "ordinary stage zero fuel did not suspend")
  let .failed reason after ← suspended.resume 100000 0
    | throw (IO.userError "ordinary stage rejection did not retain a session")
  let some diagnostic ← get "ordinary stage diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "ordinary stage rejection diagnostic missing")
  require (match diagnostic.error with
    | .comptimeArgumentStageMismatch _ _ 0 _ _ => true
    | _ => false) "ordinary stage rejection changed its guard reason"
  pure after

def run : IO Unit := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError s!"ordinary stage checking: {reprStr errors}")
  | .ok program =>
    let roots ← ["stagedFactory", "ordinaryFactory", "invoke"].mapM (SourceCoreUnifiedCorpusSupport.key program)
    match generated : SourceCoreCompiler.compileChecked program
        (roots.map (fun key => .declaration key.declaration)) options with
    | .error error => throw (IO.userError s!"ordinary stage compilation: {reprStr error}")
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "ordinary stage artifact missing")
      | some cached =>
        have sameProgram : cached.sourceProgram = program :=
          (source.artifact_fields present).1.trans
            (SourceCoreCompiler.compileChecked_program generated)
        have original : checkProgram workspace options.checkingFuel = .ok cached.sourceProgram := by
          rw [sameProgram]
          exact checked
        let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile cached original
          | throw (IO.userError "ordinary stage selected profile rejected")
        have _bodyTyping := SelectedCompilationCheckedBodyTyping.of_checked original profile
        let [stagedKey, ordinaryKey, invokeKey] := roots
          | throw (IO.userError "ordinary stage root order changed")
        let prepared ← get "ordinary stage public preparation" (SourceCoreExecution.prepare source)
        let artifact ← prepared.open
        let bootstrap ← artifact.bootstrap
        let .ready initial := bootstrap.resume 100000
          | throw (IO.userError "ordinary stage bootstrap did not complete")
        let staged ← success initial stagedKey []
        let .function stagedHandle := staged.value
          | throw (IO.userError "ordinary stage closure handle missing")
        let failed ← reject staged.session invokeKey stagedHandle (Word.ofNatModulo 17)
        let ordinary ← success failed ordinaryKey []
        let .function ordinaryHandle := ordinary.value
          | throw (IO.userError "ordinary closure handle missing")
        let accepted ← success ordinary.session invokeKey [.function ordinaryHandle, .word (Word.ofNatModulo 37)]
        require (accepted.value == .word (Word.ofNatModulo 37)) "ordinary closure returned the wrong result"
        let repeated ← reject accepted.session invokeKey stagedHandle (Word.ofNatModulo 61)
        let continued ← success repeated invokeKey [.function ordinaryHandle, .word (Word.ofNatModulo 89)]
        require (continued.value == .word (Word.ofNatModulo 89)) "ordinary closure lost after repeated rejection"
        require (cached.indexed.base.functions.length == 4) "ordinary stage selected cache changed"
        require ([initial.heapSize, staged.session.heapSize, failed.heapSize, ordinary.session.heapSize,
          accepted.session.heapSize, repeated.heapSize, continued.session.heapSize] == [5, 5, 11, 11, 26, 32, 47])
          "ordinary stage guard ran argument effects or changed the retained heap"
        IO.println "ORDINARY_STAGE_PROFILE_PASS: checked profile, closure guard rejection, exact heaps, zero-fuel resume, retained handles and continuation"

end Tests.SourceCoreSelectedOrdinaryStageLift
