import Solcore.Frontend.SourceCoreCompiler
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Frontend.SourceRuntimeDeepValidation

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runTrusted

/-! Retained raw-value validation and inert-prefix audit. The public execution
facade uses owned values; these fixtures keep the old pure validator's exact
error ordering, and separately check that an authenticated inert source prefix
survives ordinary indexed Core execution. No source evaluator is imported. -/
set_option autoImplicit false
namespace Tests.SourceCompilerRetainedBoundary
open Solcore Solcore.Frontend SourceInference

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def plan (program : CheckedProgram) (seed : SourceCoreCompiler.Seed) :
    IO SourceSpecializationWorklist.Plan := do
  let request ← get "retained seed" (SourceProgramExecution.resolveSeed program seed)
  match ← get "retained worklist" (SourceSpecializationWorklist.run program [request] 128) with
  | .complete plan => pure plan
  | .budgetExhausted _ _ _ => throw (IO.userError "retained validator worklist exhausted")

/-- Called by the baseline compiler suite so it reuses the same checked source
and canonical seeds. This is not another public execution interface. -/
def run (program : CheckedProgram) (pairSeed directSeed blockedSeed dependentSeed : SourceCoreCompiler.Seed) : IO Unit := do
  let pairPlan ← plan program pairSeed
  let executable ← get "retained executable plan" (SourceCompilationPlan.prepareExecutablePlanEvidence program pairPlan)
  let compiled ← get "retained cached program" (SourceCoreCompiler.compileChecked program [pairSeed]
    {specializationBudget := 128, compilationFuel := 1000})
  let cached ← match compiled.artifact? with
    | some cached => pure cached | none => throw (IO.userError "retained fixture has no code")
  let key ← match cached.keys with
    | [key] => pure key | _ => throw (IO.userError "retained fixture roots changed")
  let root ← match cached.runtime.root? key with
    | some root => pure root | none => throw (IO.userError "retained runtime root missing")
  let pair : SourceTypedRuntime.Value := .product (.word (Core.Word.ofNatModulo 7)) (.word (Core.Word.ofNatModulo 8))
  let malformed : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (.bool true)⟩]}
  let retained : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (.word (Core.Word.ofNatModulo 99))⟩]}
  let openPrefix : SourceTypedRuntime.RuntimeState := {heap := ⟨.error, none⟩ :: retained.heap}
  require (!malformed.isDeeplySafe 128 program.signatures executable) "malformed cell passed pure deep validation"
  require (retained.isDeeplySafe 128 program.signatures executable && openPrefix.isDeeplySafe 128 program.signatures executable)
    "valid/inert uninitialized raw prefix failed pure validation"
  match SourceCoreUnifiedRuntime.boundaryFailure cached.runtime root [.bool true] 128 malformed with
  | some (.typeMismatch (.product .word .word) (some .bool)) => pure ()
  | _ => throw (IO.userError "raw input mismatch did not precede malformed initial heap")
  match SourceCoreUnifiedRuntime.boundaryFailure cached.runtime root [pair] 128 malformed with
  | some .deepSafetyInitialStateRejected => pure ()
  | _ => throw (IO.userError "malformed raw heap lost its pure boundary diagnostic")
  for budget in [0, 1] do
    match SourceCoreUnifiedRuntime.boundaryFailure cached.runtime root [pair] budget retained with
    | some (.inputValidationFuelExhausted (.product .word .word) actual) =>
        require (actual == budget) "nested raw validation lost its independent budget"
    | _ => throw (IO.userError "nested raw validation exhaustion changed precedence")
  require ((SourceCoreUnifiedRuntime.boundaryFailure cached.runtime root [pair] 128 retained).isNone)
    "valid retained inputs/heap failed validation"

  let recipe ← get "inert prefix recipe" (SourceCoreIndexedSession.Recipe.prepare cached)
  let artifact ← recipe.open
  require ((SourceCoreIndexedSession.InertPrefix.prepare artifact malformed 128).isNone)
    "malformed state acquired an inert-prefix receipt"
  let inert ← match SourceCoreIndexedSession.InertPrefix.prepare artifact openPrefix 128 with
    | some inert => pure inert | none => throw (IO.userError "valid inert prefix was rejected")
  let bootstrap ← artifact.bootstrap inert
  let pending ← match bootstrap.resume 0 with
    | .outOfFuel pending => pure pending | _ => throw (IO.userError "zero bootstrap fuel did not suspend")
  let session ← match pending.resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "inert-prefix bootstrap did not complete")
  require (reprStr session.inertPrefix == reprStr openPrefix) "bootstrap changed opaque source prefix"
  let checkpoint ← get "inert-prefix invocation" (session.start key
    [.product (.word (Core.Word.ofNatModulo 7)) (.word (Core.Word.ofNatModulo 8))] 128)
  let paused ← match ← checkpoint.resume 0 with
    | .outOfFuel paused => pure paused | _ => throw (IO.userError "zero execution fuel did not suspend")
  match ← paused.resume 300000 with
  | .succeeded completion =>
      require (completion.value == .word (Core.Word.ofNatModulo 12) &&
        reprStr completion.session.inertPrefix == reprStr openPrefix)
        "resumed native execution changed the value or inert source prefix"
  | _ => throw (IO.userError "retained prefix invocation did not finish")

  -- Arbitrary native stores remain a lower-level Core ABI capability, not a
  -- second public source invocation variant.
  let directPlan ← plan program directSeed
  let linked ← get "direct low-level Core link" (SourceCoreDirectLinking.linkWithStagingFuel program (.complete directPlan) 128)
  match linked.entries with
  | [entry] =>
      match entry.run? [.word (Core.Word.ofNatModulo 4)] 4096 [.bool true] with
      | some (.done (.word actual) [.bool true]) =>
          require (actual == Core.Word.ofNatModulo 8) "low-level supplied native store changed its result"
      | _ => throw (IO.userError "low-level Core ABI did not preserve its supplied store")
  | _ => throw (IO.userError "direct link changed root count")

  let blocked ← plan program blockedSeed
  match SourceCompilationPlan.validateExecutablePlanEvidence program blocked with
  | .error (.executableCoercionMethod _ _ _ (.missingTraitMethod _ "coerce")) => pure ()
  | _ => throw (IO.userError "missing coercion method lost its pure plan diagnostic")
  let dependent ← plan program dependentSeed
  match SourceCompilationPlan.validateExecutablePlanEvidence program dependent with
  | .error (.stagedExpressionType _ .integer) => pure ()
  | _ => throw (IO.userError "dependent staged Integer lost its pure plan rejection")
end Tests.SourceCompilerRetainedBoundary
