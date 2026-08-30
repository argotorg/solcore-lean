import Solcore.Semantics.OneLevelNestedExecutionResumptionProperties
import Solcore.Test.OneLevelNestedExecutionFixture

/-! Executable and external-consumer regressions for nested resumption. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open OneLevelNestedExecutionFixture

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def one : Word := ⟨1, by decide⟩

/-!
The child increments instead of assigning a constant. A resume that replayed
the completed write prefix would therefore leave `childNewValue + 1`.
-/
private def incrementChildProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageRead.index) (.word childSlot))
      (.letE
        (.apply (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word childSlot)
            (.binary .wordAdd (.var 0) (.word one))))
        (returnedExpr (.binary .wordAdd (.var 1) (.word one))))
}

private theorem incrementChildProgram_checked :
    incrementChildProgram.checkHost = true := by
  decide

private def incrementChildContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨incrementChildProgram, incrementChildProgram_checked⟩ rfl

private def rootCommitContract : CheckedCoreContract :=
  rootContract .commit childTargetWord

private def scenario (fuel : Nat) :
    OneLevelNestedExecution.Result
      (initialWorld rootCommitContract incrementChildContract)
      rootCommitContract invocation :=
  runScenario rootCommitContract incrementChildContract fuel

private def additionalFuel : Nat := 64
private def rootPrefixFuel : Nat := 0
private def writtenChildPrefixFuel : Nat := 31
private def resumedRootPrefixFuel : Nat := 39

private abbrev TerminalObservation :=
  FrameOutcome Word × Option Word × Option Word

private def terminalObservation? (result := scenario additionalFuel) :
    Option TerminalObservation :=
  match result.view with
  | .completed terminal =>
      some
        (terminal.outcome,
          childStorageValue?
            terminal.terminalContext.context.values.working.1,
          childStorageValue? terminal.finalWorld)
  | .outOfFuel _ _ _ => none

private def expectedObservation : Option TerminalObservation :=
  some
    (.returned (encodeWordBytesBE childNewValue),
      some childNewValue, some childNewValue)

private def splitMatchesOneShot (prefixFuel : Nat) : Bool :=
  let split :=
    OneLevelNestedExecution.resumeWithFuel (scenario prefixFuel)
      additionalFuel
  let oneShot := scenario (prefixFuel + additionalFuel)
  terminalObservation? split == terminalObservation? oneShot &&
    terminalObservation? split == expectedObservation

private def rootOutOfFuelAt
    (fuel : Nat) (expectedChild : Option Word) : Bool :=
  match (scenario fuel).view with
  | .outOfFuel _ (.root frame) _ =>
      childStorageValue?
          frame.context.context.values.working.1 == expectedChild
  | _ => false

private def childOutOfFuelAt
    (fuel : Nat) (expectedChild : Option Word) : Bool :=
  match (scenario fuel).view with
  | .outOfFuel _ (.child frame) _ =>
      childStorageValue?
          frame.childContext.context.values.working.1 == expectedChild
  | _ => false

private def rootOutOfFuelResumesExactly : Bool :=
  rootOutOfFuelAt rootPrefixFuel (some childOldValue) &&
    splitMatchesOneShot rootPrefixFuel

private def writtenChildOutOfFuelResumesWithoutReplay : Bool :=
  childOutOfFuelAt writtenChildPrefixFuel (some childNewValue) &&
    splitMatchesOneShot writtenChildPrefixFuel

private def childCompletedRootOutOfFuelResumesExactly : Bool :=
  rootOutOfFuelAt resumedRootPrefixFuel (some childNewValue) &&
    splitMatchesOneShot resumedRootPrefixFuel

private theorem compileTimeRootOutOfFuelResumption :
    rootOutOfFuelResumesExactly = true := by
  native_decide

private theorem compileTimeWrittenChildOutOfFuelResumption :
    writtenChildOutOfFuelResumesWithoutReplay = true := by
  native_decide

private theorem compileTimeChildCompletedRootResumption :
    childCompletedRootOutOfFuelResumesExactly = true := by
  native_decide

/-- Runtime counterparts for the three actual-run split boundaries. -/
def testOneLevelNestedExecutionResumption : IO Unit := do
  assertTrue rootOutOfFuelResumesExactly
    "root out-of-fuel resumption disagreed with one-shot execution"
  assertTrue writtenChildOutOfFuelResumesWithoutReplay
    "child resumption replayed or lost its non-idempotent storage prefix"
  assertTrue childCompletedRootOutOfFuelResumesExactly
    "post-child root resumption disagreed with one-shot execution"

end Tests

namespace ExternalOneLevelNestedExecutionResumptionConsumer

open Solcore.Semantics
open OneLevelNestedExecution

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (fuel additional : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode) :
    resumeWithFuel (runMode registry fuel mode reachable) additional =
      runMode registry (fuel + additional) mode reachable :=
  resumeWithFuel_runMode registry fuel additional mode reachable

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (fuel : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode) :
    resumeWithFuel (runMode registry fuel mode reachable) 0 =
      runMode registry fuel mode reachable :=
  resumeWithFuel_runMode_zero registry fuel mode reachable

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (first second : Nat) :
    resumeWithFuel (resumeWithFuel result first) second =
      resumeWithFuel result (first + second) :=
  resumeWithFuel_add result first second

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (fuel first second : Nat)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode) :
    resumeWithFuel
        (resumeWithFuel (runMode registry fuel mode reachable) first) second =
      runMode registry (fuel + first + second) mode reachable :=
  resumeWithFuel_runMode_add registry fuel first second mode reachable

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld rootContract rootInvocation)
    (terminal : TerminalResult initialWorld rootContract rootInvocation)
    (completed : result.view = .completed terminal)
    (additional : Nat) :
    resumeWithFuel result additional = result :=
  resumeWithFuel_completed result terminal completed additional

example
    {initialWorld : WorldState}
    {rootContract : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (registry : ExecutionEnvironment)
    (mode : Mode initialWorld rootContract rootInvocation)
    (reachable : Reachable registry mode)
    (result : Result initialWorld rootContract rootInvocation)
    (exhausted : result.view = .outOfFuel registry mode reachable)
    (additional : Nat) :
    resumeWithFuel result additional =
      runMode registry additional mode reachable :=
  resumeWithFuel_outOfFuel registry mode reachable result exhausted additional

example
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel additional : Nat) :
    resumeWithFuel
        (run rootContract rootInvocation installed registry fuel) additional =
      run rootContract rootInvocation installed registry
        (fuel + additional) :=
  resumeWithFuel_run rootContract rootInvocation installed registry
    fuel additional

example
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel : Nat) :
    resumeWithFuel
        (run rootContract rootInvocation installed registry fuel) 0 =
      run rootContract rootInvocation installed registry fuel :=
  resumeWithFuel_run_zero rootContract rootInvocation installed registry fuel

example
    {initialWorld : WorldState}
    (rootContract : CheckedCoreContract)
    (rootInvocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld rootInvocation.target
        rootContract)
    (registry : CheckedContractRegistry)
    (fuel first second : Nat) :
    resumeWithFuel
        (resumeWithFuel
          (run rootContract rootInvocation installed registry fuel) first)
        second =
      run rootContract rootInvocation installed registry
        (fuel + first + second) :=
  resumeWithFuel_run_add rootContract rootInvocation installed registry
    fuel first second

end ExternalOneLevelNestedExecutionResumptionConsumer
