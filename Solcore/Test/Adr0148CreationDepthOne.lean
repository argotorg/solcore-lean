import Solcore.Semantics.OneLevelNestedExecutionProperties
import Solcore.Semantics.WorldStateDeltaProperties
import Solcore.Test.Adr0148CreationEndToEndFixture

/-! E2E depth-one rejection inside a checked contract initializer. -/

set_option autoImplicit false

namespace Tests.Adr0148CreationDepthOne

open Solcore.Core
open Solcore.Semantics
open Solcore.Semantics.OneLevelNestedExecution
open Tests.Adr0148CreationEndToEndFixture

def callDepthSlot : Word := ⟨0x201, by decide⟩
def createDepthSlot : Word := ⟨0x202, by decide⟩
def depthCode : Word := ⟨2, by decide⟩
def nestedInput : Word := ⟨0x6161, by decide⟩

/--
Accept only the fourth result branch, store its failure code, then continue.
Every other branch traps, so a successful outer creation proves depth failure.
-/
def recordFourthFailure
    (depth : Nat) (operation : Expr) (slot : Word) (rest : Expr) : Expr :=
  .caseE operation
    (trapped (.var 0))
    (.caseE (.var 0)
      (trapped (.var 0))
      (.caseE (.var 0)
        (trapped (.var 0))
        (.letE
          (.apply (.var (HostFunction.storageWrite.index + depth + 3))
            (.pair (.word slot) (.var 0)))
          rest)))

def nestedCall (depth : Nat) : Expr :=
  .apply (.var (HostFunction.callContractWord.index + depth))
    (.pair (.word (addressToWord creator)) (.word nestedInput))

def nestedCreation (depth : Nat) : Expr :=
  .apply (.var (HostFunction.createContractWord.index + depth))
    (.pair (.word templateId)
      (.pair (.word creationValue) (.word nestedInput)))

/-- Both forbidden depth-two operations are observed before normal return. -/
def depthProbeInitializerProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    recordFourthFailure 0 (nestedCall 0) callDepthSlot
      (recordFourthFailure 4 (nestedCreation 4) createDepthSlot
        (returned (.word nestedInput)))
}

theorem depthProbeInitializerProgram_checked :
    depthProbeInitializerProgram.checkHost = true := by native_decide

def depthProbeInitializer : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨depthProbeInitializerProgram, depthProbeInitializerProgram_checked⟩ rfl

def depthEnvironment : ExecutionEnvironment :=
  environmentFor depthProbeInitializer

def result :=
  runWithEnvironment commitRoot invocation commitInstalled depthEnvironment 512

def storageValue? (world : WorldState) (address : Address)
    (slot : Word) : Option Word :=
  (world.account? address).bind fun account => account.storageValue? slot

def depthOneChecks : Bool :=
  match result.view with
  | .outOfFuel _ _ _ => false
  | .completed terminal =>
      let world := terminal.finalWorld
      let delta := terminal.committedDelta
      terminal.outcome ==
          .returned (encodeWordBytesBE (addressToWord created)) &&
        storageValue? world created callDepthSlot == some depthCode &&
        storageValue? world created createDepthSlot == some depthCode &&
        (world.code? created).map CheckedHostCoreProgram.program ==
          some runtime.code.program &&
        world.nonce? creator == some ⟨8, by decide⟩ &&
        world.balance? creator == some ⟨8, by decide⟩ &&
        world.balance? created == some creationValue &&
        world.balance? unrelated == some unrelatedBalance &&
        (world.account? externalCaller).isNone &&
        delta.nonceEndpoints creator ==
          (some oldNonce, some ⟨8, by decide⟩) &&
        delta.balanceEndpoints creator ==
          (some creatorBalance, some ⟨8, by decide⟩) &&
        delta.balanceEndpoints created == (none, some creationValue) &&
        delta.storageEndpoints created callDepthSlot ==
          (none, some depthCode) &&
        delta.storageEndpoints created createDepthSlot ==
          (none, some depthCode) &&
        delta.nonceChange? unrelated == none &&
        delta.balanceChange? unrelated == none

theorem compileTimeDepthOneChecks : depthOneChecks = true := by
  native_decide

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def testAdr0148CreationDepthOne : IO Unit := do
  assertTrue depthOneChecks
    "initializer nested call/create did not return code 2 without extra effects"

end Tests.Adr0148CreationDepthOne
