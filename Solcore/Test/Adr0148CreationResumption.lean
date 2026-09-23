import Solcore.ContractRuntime.OneLevelNestedExecutionResumptionProperties
import Solcore.Test.Adr0148CreationEndToEndFixture

/-! Shared-fuel and exact-resumption regressions for checked creation. -/

set_option autoImplicit false

namespace Tests.Adr0148CreationResumption

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.OneLevelNestedExecution
open Adr0148CreationEndToEndFixture

def scenario (fuel : Nat) :
    Result commitWorld commitRoot invocation :=
  runWithEnvironment commitRoot invocation commitInstalled environment fuel

inductive Phase where
  | root
  | initializer
  | completed
  deriving Repr, BEq, DecidableEq

def phaseAt (fuel : Nat) : Phase :=
  match (scenario fuel).view with
  | .completed _ => .completed
  | .outOfFuel _ (.root _) _ => .root
  | .outOfFuel _ (.child _) _ => .root
  | .outOfFuel _ (.initializer _) _ => .initializer

def rootRequestFuel : Nat := 13
def initializerStartFuel : Nat := 14
def initializerMiddleFuel : Nat := 80
def initializerEndFuel : Nat := 142
def resumedRootFuel : Nat := 143
def completedFuel : Nat := 147
def additionalFuel : Nat := 180

/-- The actual sweep isolates both administrative mode switches. -/
def sweepClassifiesBoundaries : Bool :=
  (List.range initializerStartFuel).all
      (fun fuel => phaseAt fuel == .root) &&
    (List.range (resumedRootFuel - initializerStartFuel)).all
      (fun offset => phaseAt (initializerStartFuel + offset) == .initializer) &&
    (List.range (completedFuel - resumedRootFuel)).all
      (fun offset => phaseAt (resumedRootFuel + offset) == .root) &&
    phaseAt completedFuel == .completed

structure TerminalObservation where
  outcome : FrameOutcome Word
  creatorNonce : Option Word
  creatorBalance : Option Word
  createdBalance : Option Word
  inputWord : Option Word
  caller : Option Word
  callValue : Option Word
  runtimeInstalled : Bool
  deriving BEq

def storageValue? (world : WorldState) (address : Address) (slot : Word) :
    Option Word :=
  world.account? address >>= fun account => account.storageValue? slot

def runtimeInstalled? (world : WorldState) : Bool :=
  match world.account? created with
  | none => false
  | some account =>
      match account.code? with
      | none => false
      | some code => code.program == runtime.code.program

def terminalObservation? (result : Result commitWorld commitRoot invocation) :
    Option TerminalObservation :=
  match result.view with
  | .outOfFuel _ _ _ => none
  | .completed terminal =>
      some {
        outcome := terminal.outcome
        creatorNonce := terminal.finalWorld.nonce? creator
        creatorBalance := terminal.finalWorld.balance? creator
        createdBalance := terminal.finalWorld.balance? created
        inputWord := storageValue? terminal.finalWorld created inputWordSlot
        caller := storageValue? terminal.finalWorld created callerSlot
        callValue := storageValue? terminal.finalWorld created valueSlot
        runtimeInstalled := runtimeInstalled? terminal.finalWorld
      }

def expectedObservation : Option TerminalObservation :=
  some {
    outcome := .returned (encodeWordBytesBE (addressToWord created))
    creatorNonce := some ⟨8, by decide⟩
    creatorBalance := some ⟨8, by decide⟩
    createdBalance := some creationValue
    inputWord := some initializerInput
    caller := some (addressToWord creator)
    callValue := some creationValue
    runtimeInstalled := true
  }

def splitMatchesOneShot (prefixFuel : Nat) : Bool :=
  let resumed := resumeWithFuel (scenario prefixFuel) additionalFuel
  let oneShot := scenario (prefixFuel + additionalFuel)
  terminalObservation? resumed == terminalObservation? oneShot &&
    terminalObservation? resumed == expectedObservation

def allSplitsResumeExactly : Bool :=
  [rootRequestFuel, initializerStartFuel, initializerMiddleFuel,
      initializerEndFuel, resumedRootFuel].all splitMatchesOneShot

/-- Creation preparation has occurred exactly once at every initializer OOF. -/
def initializerPreparedOnceAt (fuel : Nat) : Bool :=
  match (scenario fuel).view with
  | .outOfFuel _ (.initializer frame) _ =>
      let world := frame.initializerContext.context.values.working.1
      world.nonce? creator == some ⟨8, by decide⟩ &&
        world.balance? creator == some ⟨8, by decide⟩ &&
        world.balance? created == some creationValue
  | _ => false

def initializerPrefixesAreNotReplayed : Bool :=
  initializerPreparedOnceAt initializerStartFuel &&
    initializerPreparedOnceAt initializerMiddleFuel &&
    initializerPreparedOnceAt initializerEndFuel

theorem compileTimeCreationResumption :
    sweepClassifiesBoundaries && allSplitsResumeExactly &&
      initializerPrefixesAreNotReplayed = true := by
  native_decide

/-- Reachability seals the initializer carrier to the OOF environment. -/
example
    {fuel : Nat} {retained : ExecutionEnvironment}
    {frame : PreparedInitializerFrame commitWorld commitRoot invocation}
    {reachable : Reachable retained (.initializer frame)}
    (_viewEq : (scenario fuel).view =
      .outOfFuel retained (.initializer frame) reachable) :
    frame.environment = retained := by
  exact reachable.anchored.environment_eq

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def testAdr0148CreationResumption : IO Unit := do
  assertTrue sweepClassifiesBoundaries
    "creation fuel sweep did not isolate root/initializer/root boundaries"
  assertTrue allSplitsResumeExactly
    "creation split execution disagreed with its one-shot execution"
  assertTrue initializerPrefixesAreNotReplayed
    "creation resumption repeated nonce increment or value transfer"

end Tests.Adr0148CreationResumption
