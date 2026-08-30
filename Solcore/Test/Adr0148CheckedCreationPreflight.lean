import Solcore.Semantics.CheckedCreationPreflightProperties
import Solcore.Test.Adr0148CheckedCreationPreflightFixture

/-! External theorem consumers and actual environment-aware preflight tests. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics
open Adr0148CheckedCreationPreflightFixture

example {left right : CheckedHostCoreProgram}
    (equal : left.program = right.program) : left = right :=
  CheckedHostCoreProgram.eq_of_program_eq equal

example {left right : CoreContractEntryProfile}
    (equal : left.resultType = right.resultType) : left = right :=
  CoreContractEntryProfile.eq_of_resultType_eq equal

example {left right : CheckedCoreContract}
    (equal : left.code.program = right.code.program) : left = right :=
  CheckedCoreContract.ext equal
example := RegisteredCreationRuntime.validate?_lookup_none
example := RegisteredCreationRuntime.validate?_program_mismatch
example := RegisteredCreationRuntime.validate?_some_program_eq
example := CheckedCreationPreflight.prepare_templateUnavailable
example := CheckedCreationPreflight.prepare_creatorUnavailable
example := CheckedCreationPreflight.prepare_nonceOverflow
example {state : WorldState} {environment : ExecutionEnvironment}
    {actualCreator : Address} {identifier transferred : Core.Word}
    (prepared : PreparedCheckedCreation state environment actualCreator
      identifier transferred) :
    prepared.runtimeRegistration.contract = prepared.template.runtime :=
  CheckedCreationPreflight.PreparedCheckedCreation.runtime_exact prepared

example {state : WorldState} {environment : ExecutionEnvironment}
    {actualCreator : Address} {identifier transferred : Core.Word}
    (prepared : PreparedCheckedCreation state environment actualCreator
      identifier transferred) :
    prepared.statePreparation.createdAddress =
      environment.creationAddressPolicy.derive actualCreator prepared.oldNonce :=
  CheckedCreationPreflight.PreparedCheckedCreation.address_exact prepared
example := CheckedCreationPreflightFailure.unavailable_code
example := CheckedCreationPreflightFailure.nonceOverflow_code
example := CheckedCreationPreflightFailure.addressCollision_code
example := CheckedCreationPreflightFailure.transfer_code
example := CheckedCreationPreflightFailure.result_value
example := CheckedCreationPreflightFailure.result_response

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def wordOne : Core.Word := ⟨1, by decide⟩
private def wordThree : Core.Word := ⟨3, by decide⟩
private def wordFive : Core.Word := ⟨5, by decide⟩
private def wordSix : Core.Word := ⟨6, by decide⟩

private def failedWithCode
    {α : Type}
    (result : Except CheckedCreationPreflightFailure α)
    (expected : CheckedCreationPreflightFailure)
    (code : Core.Word) : Bool :=
  match result with
  | .ok _ => false
  | .error actual =>
      actual == expected &&
        actual.toContractCallFailure.code == code &&
        actual.toContractCallResult ==
          Core.ContractCallWordResult.failed code

private def initializerCodeExact
    {current : WorldState} {environment : ExecutionEnvironment}
    {identifier transferred : Core.Word}
    (prepared :
      PreparedCheckedCreation current environment creator identifier transferred) :
    Bool :=
  match prepared.statePreparation.initializerWorld.account?
      prepared.createdAddress with
  | none => false
  | some account =>
      match account.code? with
      | none => false
      | some installed =>
          installed.program == prepared.template.initializer.code.program

private def successIsExact
    (result := prepareWith normalWorld validEnvironment) : Bool :=
  match result with
  | .error _ => false
  | .ok prepared =>
      prepared.oldNonce == oldNonce &&
        prepared.oldNonce == prepared.creatorAccount.nonce &&
        prepared.createdAddress == created &&
        prepared.createdAddress ==
          addressPolicy.derive creator prepared.oldNonce &&
        prepared.statePreparation.createdAddress == prepared.createdAddress &&
        prepared.runtimeRegistration.contract.code.program ==
          runtime.code.program &&
        prepared.runtimeRegistration.contract.code.program ==
          prepared.template.runtime.code.program &&
        prepared.statePreparation.incrementedCreator.nonce == nextNonce &&
        prepared.statePreparation.postNonceWorld.nonce? creator ==
          some nextNonce &&
        prepared.statePreparation.initializerWorld.nonce? creator ==
          some nextNonce &&
        prepared.statePreparation.initializerWorld.balance? creator ==
          some debitedBalance &&
        prepared.statePreparation.initializerWorld.balance? created ==
          some value &&
        prepared.statePreparation.initializerWorld.nonce? created == some zero &&
        initializerCodeExact prepared &&
        prepared.statePreparation.initializerWorld.balance? unrelated ==
          some unrelatedBalance

def testAdr0148CheckedCreationPreflight : IO Unit := do
  let templateAbsent :=
    prepareWith normalWorld validEnvironment missingTemplateId
  assertTrue (failedWithCode templateAbsent .unavailable wordOne)
    "a missing template must map to unavailable code 1"

  let creatorAbsent := prepareWith absentCreatorWorld validEnvironment
  assertTrue (failedWithCode creatorAbsent .unavailable wordOne)
    "an absent creator must map to unavailable code 1"

  let nonceOverflow := prepareWith overflowWorld validEnvironment
  assertTrue (failedWithCode nonceOverflow .nonceOverflow wordFive)
    "nonce overflow must precede address and registry checks with code 5"

  let collision := prepareWith collisionWorld validEnvironment
  assertTrue (failedWithCode collision .addressCollision wordSix)
    "address collision must precede runtime validation with code 6"

  let runtimeMissing :=
    prepareWith normalWorld missingRuntimeEnvironment
  assertTrue (failedWithCode runtimeMissing .unavailable wordOne)
    "missing runtime registration must map to unavailable code 1"

  let runtimeMismatch := prepareWith normalWorld mismatchEnvironment
  assertTrue (failedWithCode runtimeMismatch .unavailable wordOne)
    "a different registered runtime program must be unavailable"

  let mismatchAndInsufficient :=
    prepareWith insufficientWorld mismatchEnvironment
  assertTrue (failedWithCode mismatchAndInsufficient .unavailable wordOne)
    "runtime mismatch must win before an insufficient transfer"

  let validThenInsufficient :=
    prepareWith insufficientWorld validEnvironment
  assertTrue
    (failedWithCode validThenInsufficient
      (.transfer .insufficientBalance) wordThree)
    "a valid runtime followed by insufficient funds must use code 3"

  assertTrue successIsExact
    "successful preflight must retain exact derivation, runtime, and state"

end Tests
