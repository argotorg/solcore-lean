import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.SourceCoreUnifiedRuntimeCertificates

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runTrusted
#check_failure Solcore.Frontend.SourceTypedRuntime.runDeepCertifiedWithValidationFuel
#check_failure Solcore.Frontend.SourceCoreExecution.Checkpoint.mk

/-! Public sessions execute one cached Core artifact. Internal compatibility
observations retain raw metadata, errors and the inert source heap prefix;
public checkpoints resume native execution without a backend selector. -/
set_option autoImplicit false
namespace Tests.SourceCompilerUnifiedRouting
open Solcore Solcore.Frontend SourceInference

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function scalar(value: Word) returns (Word) { return value; }",
    "function mappingEcho(value: mapping(Word => Word)) returns (mapping(Word => Word)) { return value; }",
    "function apply(f: function(Word) returns (Word), value: Word) returns (Word) { let retained: function(Word) returns (Word) = scalar; return f(value); }",
    "function integerApply(f: function(Word) returns (integer), value: Word) returns (integer) { return f(value); }",
    "function capture(start: Word) returns (Word) { let value = start; let f = lam(step: Word) { value += step; return value; }; f(3); return f(4); }",
    "function failAfterWrite() returns (Word) { let value: Word = 1; let fail = lam() -> Word { value += 2; let missing: Word; return missing; }; return fail(); }",
    "function spin() returns (Word) { return spin(); }"
  ] }] }

private def compile (program : CheckedProgram) (name : String) : IO SourceCompilerFeatureSupport.Entry :=
  SourceCompilerFeatureSupport.compileNamed program name []
    {specializationBudget := 256, compilationFuel := 1000}

private def initial : SourceTypedRuntime.RuntimeState := { heap := [⟨.error, none⟩, ⟨.word, some (.word (w 99))⟩] }
private def options : SourceCoreExecution.RunOptions := { inputValidationFuel := 500, executionFuel := 150000 }
private def completed (compiled : SourceCompilerFeatureSupport.Entry) (arguments : List SourceTypedRuntime.Value) :
    IO (SourceTypedRuntime.Value × SourceTypedRuntime.RuntimeState) := do
  let result ← get "cached source observation" (compiled.cached.run compiled.key arguments
    options.inputValidationFuel options.executionFuel initial)
  match result.observation with
  | .done value final =>
      assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "inert prefix changed"
      pure (value, final)
  | other => throw (IO.userError s!"cached source observation did not complete: {reprStr other}")

example {compiled : SourceCoreUnifiedCompilation.Compiled} (result : SourceCoreUnifiedCompilation.Result compiled)
    {value : SourceTypedRuntime.Value} {final : SourceTypedRuntime.RuntimeState}
    (done : result.observation = .done value final) :
    ∃ execution, result.execution = some execution ∧
      SourceTypedRuntime.PreparedDeepExecution compiled.indexed.base.sourceProgram compiled.indexed.base.validationPlan
        execution.root.argumentTypes execution.root.expected execution.arguments execution.initial value final :=
  result.done_certificate done

def run : IO Unit := do
  let program ← get "routing checking" (checkProgram workspace)
  let mapping ← compile program "mappingEcho"
  let raw : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(.word (w 1), .word (w 7)), (.word (w 1), .word (w 9))]
  assertTrue (reprStr (← completed mapping [raw]).1 == reprStr raw) "raw header or ordered duplicate mapping changed"
  let scalar ← match program.signatures.functions.filter (·.name == "scalar") with
    | [signature] => pure (⟨signature.id, []⟩ : SourceSpecialization.SpecializationKey)
    | _ => throw (IO.userError "routing scalar missing")
  let apply ← compile program "apply"
  assertTrue (reprStr (← completed apply [.global scalar [], .word (w 8)]).1 == reprStr (.word (w 8) : SourceTypedRuntime.Value))
    "authenticated global argument changed"
  let builtin ← compile program "integerApply"
  assertTrue (reprStr (← completed builtin [.builtin .wordToInteger, .word (w 8)]).1 == reprStr (.integer 8 : SourceTypedRuntime.Value))
    "builtin argument changed"
  let capture ← compile program "capture"
  let paused ← get "native source checkpoint" (capture.cached.run capture.key [.word (w 10)] options.inputValidationFuel 0 initial)
  match paused.observation with
  | .outOfFuel state => assertTrue (reprStr state == reprStr initial) "zero fuel changed source prefix"
  | other => throw (IO.userError s!"zero fuel did not suspend: {reprStr other}")
  let resumed ← get "native source resume" (paused.resume 150000)
  match resumed.observation with
  | .done (.word value) final =>
      assertTrue (value == w 17 && reprStr (final.heap.take 2) == reprStr initial.heap) "resumed captures or source prefix changed"
  | other => throw (IO.userError s!"resumed source checkpoint did not complete: {reprStr other}")
  let failure ← compile program "failAfterWrite"
  let failed ← get "cached source language fault" (failure.cached.run failure.key [] options.inputValidationFuel options.executionFuel initial)
  match failed.observation with
  | .fault (.uninitializedLocal _) state =>
      assertTrue (state.heap.any fun cell => match cell.value with | some (.word value) => value == w 3 | _ => false)
        "language failure lost preceding captured mutation"
  | other => throw (IO.userError s!"public source fault changed: {reprStr other}")
  let spin ← compile program "spin"
  let paused ← get "recursive native checkpoint" (spin.cached.run spin.key [] options.inputValidationFuel 43 initial)
  let continued ← get "recursive native resume" (paused.resume 211)
  match continued.observation with
  | .outOfFuel _ => pure ()
  | other => throw (IO.userError s!"recursive native resume unexpectedly terminated: {reprStr other}")
  let artifact ← apply.execution.open
  let session ← SourceCompilerFeatureSupport.boot artifact
  let named ← get "public selected global" (← session.named scalar)
  match ← named.session.run apply.key [named.value, .word (w 8)] {executionFuel := 300000} with
  | .ok (.succeeded result) => assertTrue (result.value == .word (w 8)) "public selected global changed"
  | _ => throw (IO.userError "public selected global invocation failed")
  let rawPublic : SourceCoreExecution.Value := .mapping (.comptime .word) (.comptime .word)
    [(.word (w 1), .word (w 7)), (.word (w 1), .word (w 9))]
  assertTrue ((← mapping.run [rawPublic]) == rawPublic) "public mapping header/order changed"
  capture.checkResume [.word (w 10)] (.word (w 17)) 0
  let publicFailure ← failure.invoke []
  match publicFailure.outcome with
  | .failed reason _ =>
      match ← publicFailure.diagnostic reason with
      | some {error := .uninitializedLocal _, ..} => pure ()
      | _ => throw (IO.userError "public fault classification changed")
  | _ => throw (IO.userError "public fault failed to occur")
  let publicSpin ← spin.invoke [] {executionFuel := 43}
  match publicSpin.outcome with
  | .outOfFuel checkpoint =>
      match ← checkpoint.resume 211 with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError "public recursive resume unexpectedly terminated")
  | _ => throw (IO.userError "public recursive invocation unexpectedly terminated")
  IO.println "common public sessions and retained prefix audits use cached Core with typed resume GREEN"

end Tests.SourceCompilerUnifiedRouting
