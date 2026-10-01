import Solcore.Frontend.SourceCoreUnifiedRuntime

/-! Prepare one reusable source-compatible Core artifact. The actual common
compiler, indexed frame program, and source observation caches are prepared
once. Calls and resumptions retain the same native program and typed checkpoint.
This boundary remains separate from the existing compiler facade while its
complete feature admission and source meaning correspondence are established. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreUnifiedCompilation
open SourceInference
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Key := SourceSpecialization.SpecializationKey

inductive Error where
  | compatible (error : SourceCoreCompatibleFunctions.Error)
  | indexed (error : SourceCoreCallableIndexedPrograms.Error)
  | runtime (error : SourceCoreUnifiedRuntime.PrepareError)
  deriving Repr

structure Compiled where private mk ::
  sourceProgram : CheckedProgram
  validationPlan : Plan
  compilationFuel : Nat
  compatible : SourceCoreCompatibleFunctions.Automatic
  compatiblePrepared : SourceCoreCompatibleFunctions.prepare sourceProgram validationPlan compilationFuel = .ok compatible
  indexed : SourceCoreCallableIndexedPrograms.Prepared compatible.checked
  indexedPrepared : SourceCoreCallableIndexedPrograms.prepare compatible.prepared compilationFuel = .ok indexed
  runtime : SourceCoreUnifiedRuntime.Prepared indexed
  runtimePrepared : SourceCoreUnifiedRuntime.prepare indexed = .ok runtime

/-- All generated code and restoration metadata are cached before the first
invocation. Factory equations retain the actual owning compiler artifacts. -/
def prepare (program : CheckedProgram) (plan : Plan) (fuel : Nat) : Except Error Compiled := do
  let compatible ← match accepted : SourceCoreCompatibleFunctions.prepare program plan fuel with
    | .error error => throw (.compatible error)
    | .ok compatible => pure (⟨compatible, accepted⟩ : {compatible //
        SourceCoreCompatibleFunctions.prepare program plan fuel = .ok compatible})
  let indexed ← match accepted : SourceCoreCallableIndexedPrograms.prepare compatible.val.prepared fuel with
    | .error error => throw (.indexed error)
    | .ok indexed => pure (⟨indexed, accepted⟩ : {indexed //
        SourceCoreCallableIndexedPrograms.prepare compatible.val.prepared fuel = .ok indexed})
  let runtime ← match accepted : SourceCoreUnifiedRuntime.prepare indexed.val with
    | .error error => throw (.runtime error)
    | .ok runtime => pure (⟨runtime, accepted⟩ : {runtime //
        SourceCoreUnifiedRuntime.prepare indexed.val = .ok runtime})
  pure ⟨program, plan, fuel, compatible.val, compatible.property, indexed.val, indexed.property,
    runtime.val, runtime.property⟩

def Compiled.keys (compiled : Compiled) : List Key := compiled.indexed.entries.map (·.key)

abbrev Result (compiled : Compiled) := SourceCoreUnifiedRuntime.Result compiled.runtime

def Compiled.run (compiled : Compiled) (key : Key) (arguments : List SourceTypedRuntime.Value)
    (validationFuel executionFuel : Nat) (initial : SourceTypedRuntime.RuntimeState := {}) :
    Except SourceCoreUnifiedRuntime.Error (Result compiled) :=
  SourceCoreUnifiedRuntime.run compiled.runtime key arguments validationFuel executionFuel initial

def Result.resume {compiled : Compiled} (result : Result compiled) (fuel : Nat) :
    Except SourceCoreUnifiedRuntime.Error (Result compiled) := SourceCoreUnifiedRuntime.Result.resume result fuel

end Solcore.Frontend.SourceCoreUnifiedCompilation
