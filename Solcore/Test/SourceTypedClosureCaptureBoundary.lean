import Solcore.SourceSemantics.CoreLowering.LegacyClosureBoundary
import Solcore.Frontend.SourceTypedRuntimeDeepSafety

/-! Checked-source examples of the legacy capture boundary.  The code and
evidence stay authentic; only caller-supplied capture lists change.  This is
an audit regression, not an implementation of a new import policy. -/

set_option autoImplicit false

namespace Tests.SourceTypedClosureCaptureBoundary

open Solcore Solcore.Frontend Solcore.TypeSystem
open SourceTypedRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "function make(value: Word) returns (function() returns (Word)) {",
    "  return lam() -> Word { return value; };",
    "}",
    "function invoke(f: function() returns (Word)) returns (Word) { return f(); }",
    "function constant() returns (Word) { return 13; }"
  ] }]
}

private def request (program : CheckedProgram) (name : String) :
    IO SourceSpecializationWorklist.Request := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"capture fixture missing function {name}")

private def prepared : IO (CheckedProgram × Plan × Key × Key × Key) := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"capture fixture check failed: {reprStr errors}")
  let requests ← ["make", "invoke", "constant"].mapM (request program)
  let plan ← match SourceSpecializationWorklist.run program requests 100 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"capture fixture plan failed: {reprStr result}")
  match plan.seedKeys with
  | [make, invoke, constant] => pure (program, plan, make, invoke, constant)
  | _ => throw (IO.userError "capture fixture seed keys changed")

private def expectedType : Ty := .function .unit .word

private def replaceCaptures (value : Value) (captured : SourceTypedRuntime.Environment) : Value :=
  match value with
  | .closure parameters result body source owner _ evidence =>
      .closure parameters result body source owner captured evidence
  | value => value

private def expectWord (expected : Nat) : RunResult → IO Unit
  | .done (.word value) _ =>
      assertTrue (value == Core.Word.ofNatModulo expected) "capture result changed"
  | result => throw (IO.userError s!"capture call did not return Word: {reprStr result}")

/-- Deep-safety alone does not certify captures.  The actual public boundary
rejects all raw closure arguments, including genuine returned ones.  Unused
initial-heap closures are admitted but do not become callable inputs. -/
def run : IO Unit := do
  let (program, plan, make, invoke, constant) ← prepared
  let (closure, state) ← match runDeepCertifiedWithValidationFuel program plan make
      [.word (Core.Word.ofNatModulo 37)] 100 1000 with
    | .done value state => pure (value, state)
    | result => throw (IO.userError s!"checked make failed: {reprStr result}")
  let captures ← match closure with
    | .closure _ _ _ _ _ captured _ => pure captured
    | _ => throw (IO.userError "checked make did not return a closure")
  let (binder, originalLocation) ← match captures with
    | [binding] => pure binding
    | _ => throw (IO.userError s!"unexpected checked captures: {reprStr captures}")
  let executablePlan ← match prepareExecutablePlanEvidence program plan with
    | .ok plan => pure plan
    | .error error => throw (IO.userError s!"capture evidence preparation failed: {reprStr error}")
  let rejected := fun value initial => do
    assertTrue (initial.isDeeplySafe 100 program.signatures executablePlan)
      "audit state must satisfy the deep validator"
    assertTrue (value.isDeeplySafe 100 program.signatures executablePlan initial expectedType)
      "audit closure must satisfy the deep validator"
    match runDeepCertifiedWithValidationFuel program plan invoke [value] 100 1000 initial with
    | .fault (.typeMismatch expected (some actual)) finalState =>
        assertTrue (expected == expectedType && actual == expectedType)
          "raw closure boundary diagnostic changed"
        assertTrue (decide (finalState.heap.length = initial.heap.length))
          "raw closure boundary executed before rejecting"
    | result => throw (IO.userError s!"raw closure input was admitted: {reprStr result}")
  rejected closure state
  let missing := replaceCaptures closure []
  rejected missing state
  let otherBinder := { binder with binderIndex := binder.binderIndex + 1000 }
  rejected (replaceCaptures closure [(otherBinder, originalLocation)]) state
  let (boolLocation, wrongState) := state.allocate .bool (some (.bool true))
  let wrong := replaceCaptures closure [(binder, boolLocation)]
  rejected wrong wrongState
  rejected (replaceCaptures closure (captures ++ [(otherBinder, boolLocation)])) wrongState
  rejected (replaceCaptures closure (captures ++ [(binder, boolLocation)])) wrongState
  rejected (replaceCaptures closure ((binder, boolLocation) :: captures)) wrongState
  -- An authentic global is an admitted callable.  Adding a deeply safe but
  -- lexically malformed closure to the unused old heap does not expose it.
  let (_, unusedMissing) := wrongState.allocate expectedType (some missing)
  let (_, unusedWrong) := unusedMissing.allocate expectedType (some wrong)
  assertTrue (unusedWrong.isDeeplySafe 100 program.signatures executablePlan)
    "unused malformed capture lists stopped satisfying current deep safety"
  expectWord 13 (runDeepCertifiedWithValidationFuel program plan invoke
    [.global constant []] 100 1000 unusedWrong)

end Tests.SourceTypedClosureCaptureBoundary
