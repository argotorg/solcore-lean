import Solcore.Semantics.OneLevelNestedCreationCompletion
import Solcore.Test.Adr0148CheckedCreationPreflightFixture
import Solcore.Test.OneLevelNestedExecutionFixture

/-! Actual checked root fixture for prepared initializer lifecycle helpers. -/

set_option autoImplicit false

namespace Tests.Adr0148NestedCreationLifecycleFixture

open Solcore.Core
open Solcore.Semantics
open Solcore.Semantics.OneLevelNestedExecution
open Tests.OneLevelNestedExecutionFixture
open Tests.Adr0148CheckedCreationPreflightFixture

def creationExpr : Expr :=
  .apply (.var HostFunction.createContractWord.index)
    (.pair (.word templateId) (.pair (.word value) (.word initializerPayload)))

def rootProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := consumeCallResult .commit creationExpr
}

theorem rootProgram_checked : rootProgram.checkHost = true := by decide

def rootContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨rootProgram, rootProgram_checked⟩ rfl

def rootAccount : Account :=
  (creatorAccount creatorBalance oldNonce).withCode rootContract.code

def initialWorld : WorldState :=
  WorldState.empty
    |>.putAccount unrelated unrelatedAccount
    |>.putAccount creator rootAccount

def rootInstalled :
    InstalledCheckedCoreContract initialWorld creator rootContract := {
  account := rootAccount
  account_present := by rfl
  code_present := by rfl
}

def rootInvocation : TopLevelInvocation := {
  target := creator
  caller := unrelated
  callValue := Word.zero
  inputData := HostStorageDriver.InputData.ofWord initializerPayload
}

def initialFrame : RootFrame initialWorld rootContract rootInvocation :=
  RootFrame.initial rootContract rootInvocation rootInstalled

/-- Execute real typed root steps until its first creation suspension. -/
def seekCreation : (fuel : Nat) →
    (frame : RootFrame initialWorld rootContract rootInvocation) →
    frame.context.context.storageAddress = creator →
    Option { root : SuspendedCreationRoot initialWorld rootContract rootInvocation //
      root.parentContext.context.storageAddress = creator }
  | 0, _, _ => none
  | fuel + 1, frame, anchored =>
      match advanced : Solcore.Core.hostAdvance frame.state with
      | .next next => seekCreation fuel (frame.afterNext next advanced) anchored
      | .suspended ⟨request, continuation, store⟩ =>
          match request with
          | .createContractWord actualTemplate actualValue actualInput =>
              some ⟨frame.suspendCreation
                ⟨actualTemplate, actualValue, actualInput⟩ continuation store
                advanced, anchored⟩
          | _ => none
      | _ => none

def suspendedRoot? := seekCreation 128 initialFrame rfl

def completionObservation (outcome : CheckedCoreWordOutcome) : Bool :=
  match suspendedRoot? with
  | none => false
  | some suspendedWithAnchor =>
      let suspended := suspendedWithAnchor.1
      match CheckedCreationPreflight.prepare
          suspended.parentContext.context.values.working.1 validEnvironment
          rootInvocation.executionInputs.currentAddress
          suspended.profile.templateId suspended.profile.value with
      | .error _ => false
      | .ok prepared =>
          let frame := suspended.startInitializer validEnvironment prepared
            suspendedWithAnchor.2.symm
          match frame.complete outcome with
          | .returned deployed =>
              (deployed.deployedWorld.code? created).map
                  CheckedHostCoreProgram.program == some runtime.code.program &&
                deployed.deployedAccount.storageValue? initializerPayload ==
                  deployed.latestCreatedAccount.storageValue? initializerPayload &&
                deployed.deployedAccount.balance ==
                  deployed.latestCreatedAccount.balance &&
                deployed.deployedAccount.nonce ==
                  deployed.latestCreatedAccount.nonce &&
                (deployed.resumedRoot.context.context.values.working.1.code?
                    created).map CheckedHostCoreProgram.program ==
                  some runtime.code.program
          | .reverted data root _ _ =>
              data == initializerPayload &&
                root.context.context.values.working.1.nonce? creator ==
                  some nextNonce &&
                (root.context.context.values.working.1.account? created).isNone
          | .trapped reason root _ _ =>
              reason == initializerPayload &&
                root.context.context.values.working.1.nonce? creator ==
                  some nextNonce &&
                (root.context.context.values.working.1.account? created).isNone

end Tests.Adr0148NestedCreationLifecycleFixture
