import Solcore.ContractRuntime.Internal.CreationLaws
import Solcore.ContractRuntime.Internal.WorldStateDeltaLaws
import Solcore.Core.Internal.HostPreservation
import Solcore.ContractRuntime.Internal.StorageDriverLaws
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.ContractRuntime.Internal.EntryOutcomeLaws
import Solcore.ContractRuntime.Internal.NestedLaws

/-!
# Contract creation tests

The ADR-0148 creation lifecycle: checked preflight, account creation, failure boundaries, resumption and
end-to-end programs.
-/

section
-- leanmerge: from Solcore.Test.Adr0148CheckedAccountCreationFixture
/-! Actual checked initializer and explicit worlds for creation preparation. -/

set_option autoImplicit false

namespace Tests.Adr0148CheckedAccountCreationFixture

open Solcore.Core
open Solcore.ContractRuntime

def creator : Address := ⟨0x1480, by decide⟩
def created : Address := ⟨0x1481, by decide⟩
def unrelated : Address := ⟨0x1482, by decide⟩

def zero : Word := Word.zero
def oldNonce : Word := ⟨4, by decide⟩
def nextNonce : Word := ⟨5, by decide⟩
def transferValue : Word := ⟨3, by decide⟩
def creatorBalance : Word := ⟨10, by decide⟩
def debitedBalance : Word := ⟨7, by decide⟩
def insufficientBalance : Word := ⟨2, by decide⟩
def unrelatedBalance : Word := ⟨8, by decide⟩
def unrelatedNonce : Word := ⟨2, by decide⟩
def unrelatedSlot : Word := ⟨0xa8, by decide⟩
def unrelatedStored : Word := ⟨0xb8, by decide⟩
def blankSlot : Word := ⟨0xc8, by decide⟩
def initializerPayload : Word := ⟨0xd8, by decide⟩

def addressPolicy : CreationAddressPolicy := {
  derive := fun _creator _nonce => created
}

def initializerProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := .inLeft (.sum .word .word) (.word initializerPayload)
}

theorem initializerProgram_checked : initializerProgram.checkHost = true := by
  rfl

def initializer : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨initializerProgram, initializerProgram_checked⟩ rfl

def creatorAccount (balance nonce : Word) : Account :=
  Account.empty.withBalance balance |>.withNonce nonce

def unrelatedAccount : Account :=
  Account.empty
    |>.withBalance unrelatedBalance
    |>.withNonce unrelatedNonce
    |>.storageWrite unrelatedSlot unrelatedStored

def worldWithCreator (balance nonce : Word) : WorldState :=
  WorldState.empty
    |>.putAccount unrelated unrelatedAccount
    |>.putAccount creator (creatorAccount balance nonce)

def absentCreatorWorld : WorldState :=
  WorldState.empty.putAccount unrelated unrelatedAccount

def normalWorld : WorldState :=
  worldWithCreator creatorBalance oldNonce

def overflowWorld : WorldState :=
  worldWithCreator creatorBalance Word.maximum

def collisionWorld : WorldState :=
  normalWorld.putAccount created Account.empty

def insufficientWorld : WorldState :=
  worldWithCreator insufficientBalance oldNonce

def prepare (world : WorldState) (value : Word) :=
  CheckedAccountCreation.prepare world addressPolicy creator value initializer

end Tests.Adr0148CheckedAccountCreationFixture
end

section
-- leanmerge: from Solcore.Test.Adr0148CheckedAccountCreation
/-! External consumers and actual checked creation-preparation regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime
open Adr0148CheckedAccountCreationFixture

example := CheckedAccountCreation.prepare_creatorAbsent
example := CheckedAccountCreation.prepare_nonceOverflow

example {current : WorldState} {policy : CreationAddressPolicy}
    {creator : Address} {value : Core.Word}
    {initializer : CheckedCoreContract}
    (prepared :
      PreparedAccountCreation current policy creator value initializer) :
    prepared.incrementedCreator.nonce.val = prepared.oldNonce.val + 1 :=
  CheckedAccountCreation.PreparedAccountCreation.increment_exact prepared

example {current : WorldState} {policy : CreationAddressPolicy}
    {creator : Address} {value : Core.Word}
    {initializer : CheckedCoreContract}
    (prepared :
      PreparedAccountCreation current policy creator value initializer) :
    prepared.createdAddress ≠ creator :=
  CheckedAccountCreation.PreparedAccountCreation.created_ne_creator prepared

example {current : WorldState} {policy : CreationAddressPolicy}
    {creator : Address} {value : Core.Word}
    {initializer : CheckedCoreContract}
    (prepared :
      PreparedAccountCreation current policy creator value initializer) :
    prepared.postNonceWorld.account? creator =
      some prepared.incrementedCreator :=
  CheckedAccountCreation.PreparedAccountCreation.postNonce_creator prepared

example {current : WorldState} {policy : CreationAddressPolicy}
    {creator : Address} {value : Core.Word}
    {initializer : CheckedCoreContract}
    (prepared :
      PreparedAccountCreation current policy creator value initializer) :
    prepared.provisionalWorld.account? prepared.createdAddress =
      some prepared.provisionalAccount :=
  CheckedAccountCreation.PreparedAccountCreation.provisional_created prepared

example {current : WorldState} {policy : CreationAddressPolicy}
    {creator : Address} {value : Core.Word}
    {initializer : CheckedCoreContract}
    (prepared :
      PreparedAccountCreation current policy creator value initializer) :
    prepared.initializerInstalled.account.code? = some initializer.code :=
  CheckedAccountCreation.PreparedAccountCreation.initializer_code_installed
    prepared

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def failedWith
    {α : Type}
    (result : Except CreationPreflightFailure α)
    (expected : CreationPreflightFailure) : Bool :=
  match result with
  | .error actual => actual == expected
  | .ok _ => false

private def inputIdentityAt
    (world : WorldState) (address : Address) : Bool :=
  let delta := WorldStateDelta.identity world
  !delta.createdAccount? address &&
    delta.nonceChange? creator == none

private def initializerCodeInstalled
    {current : WorldState} {value : Core.Word}
    (prepared :
      PreparedAccountCreation current addressPolicy creator value initializer) :
    Bool :=
  match prepared.initializerWorld.account? prepared.createdAddress with
  | none => false
  | some account =>
      match account.code? with
      | none => false
      | some code => code.program == initializer.code.program

private def createdAccountIsFresh
    {current : WorldState} {value : Core.Word}
    (prepared :
      PreparedAccountCreation current addressPolicy creator value initializer) :
    Bool :=
  match prepared.initializerWorld.account? prepared.createdAddress with
  | none => false
  | some account =>
      account.nonce == zero &&
        account.storageRead blankSlot == zero &&
        account.storageValue? blankSlot == none

private def unrelatedIsPreserved (world : WorldState) : Bool :=
  match world.account? unrelated with
  | none => false
  | some account =>
      account.balance == unrelatedBalance &&
        account.nonce == unrelatedNonce &&
        account.storageValue? unrelatedSlot == some unrelatedStored &&
        account.code?.isNone

private def successfulPreparationHas
    (value expectedCreator expectedCreated : Core.Word)
    (result := prepare normalWorld value) : Bool :=
  match result with
  | .error _ => false
  | .ok prepared =>
      prepared.oldNonce == oldNonce &&
        prepared.oldNonce == prepared.creatorAccount.nonce &&
        prepared.createdAddress == addressPolicy.derive creator oldNonce &&
        prepared.incrementedCreator.nonce == nextNonce &&
        prepared.postNonceWorld.nonce? creator == some nextNonce &&
        prepared.initializerWorld.nonce? creator == some nextNonce &&
        prepared.initializerWorld.balance? creator == some expectedCreator &&
        prepared.initializerWorld.balance? created == some expectedCreated &&
        prepared.initializerWorld.nonce? created == some zero &&
        initializerCodeInstalled prepared &&
        createdAccountIsFresh prepared &&
        unrelatedIsPreserved prepared.initializerWorld

def testAdr0148CheckedAccountCreation : IO Unit := do
  let absentResult := prepare absentCreatorWorld transferValue
  assertTrue (failedWith absentResult .creatorAbsent)
    "an absent creator must reject before publishing a creation world"
  assertTrue
    ((absentCreatorWorld.account? created).isNone &&
      inputIdentityAt absentCreatorWorld created)
    "absent-creator rejection must leave the input world exact"

  let overflowResult := prepare overflowWorld transferValue
  assertTrue (failedWith overflowResult .nonceOverflow)
    "the maximum nonce must reject instead of wrapping"
  assertTrue
    ((overflowWorld.account? created).isNone &&
      inputIdentityAt overflowWorld created)
    "nonce overflow must not create an account or consume state"

  let collisionResult := prepare collisionWorld transferValue
  assertTrue (failedWith collisionResult .addressCollision)
    "a derived address collision must reject before value transfer"
  assertTrue (inputIdentityAt collisionWorld created)
    "collision rejection must preserve the pre-existing target account"

  let insufficientResult := prepare insufficientWorld transferValue
  assertTrue
    (failedWith insufficientResult (.transfer .insufficientBalance))
    "insufficient creator balance must be reported as transfer failure"
  assertTrue
    ((insufficientWorld.account? created).isNone &&
      inputIdentityAt insufficientWorld created)
    "insufficient balance must expose no provisional account or nonce update"

  assertTrue
    (successfulPreparationHas zero creatorBalance zero)
    "zero-value preparation must derive with the old nonce and install init code"
  assertTrue
    (successfulPreparationHas transferValue debitedBalance transferValue)
    "value preparation must increment once and transfer exact balances"

end Tests
end

section
-- leanmerge: from Solcore.Test.Adr0148CheckedCreationPreflightFixture
/-! Explicit creation environment and checked contracts for preflight tests. -/

set_option autoImplicit false

namespace Tests.Adr0148CheckedCreationPreflightFixture

open Solcore.Core
open Solcore.ContractRuntime

def creator : Address := ⟨0x1580, by decide⟩
def created : Address := ⟨0x1581, by decide⟩
def fallback : Address := ⟨0x1582, by decide⟩
def unrelated : Address := ⟨0x1583, by decide⟩

def zero : Word := Word.zero
def templateId : Word := ⟨0x15, by decide⟩
def missingTemplateId : Word := ⟨0x16, by decide⟩
def oldNonce : Word := ⟨4, by decide⟩
def nextNonce : Word := ⟨5, by decide⟩
def value : Word := ⟨3, by decide⟩
def creatorBalance : Word := ⟨10, by decide⟩
def debitedBalance : Word := ⟨7, by decide⟩
def insufficientBalance : Word := ⟨2, by decide⟩
def unrelatedBalance : Word := ⟨9, by decide⟩
def initializerPayload : Word := ⟨0x21, by decide⟩
def runtimePayload : Word := ⟨0x22, by decide⟩
def mismatchPayload : Word := ⟨0x23, by decide⟩

def programFor (payload : Word) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := .inLeft (.sum .word .word) (.word payload)
}

theorem programFor_checked (payload : Word) :
    (programFor payload).checkHost = true := by
  rfl

def contractFor (payload : Word) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨programFor payload, programFor_checked payload⟩ rfl

def initializer : CheckedCoreContract := contractFor initializerPayload
def runtime : CheckedCoreContract := contractFor runtimePayload
def mismatchedRuntime : CheckedCoreContract := contractFor mismatchPayload

def template : CheckedCreationTemplate := {
  initializer := initializer
  runtime := runtime
}

def templateRegistry : CheckedCreationTemplateRegistry := {
  lookup := fun identifier =>
    if identifier = templateId then some template else none
}

def addressPolicy : CreationAddressPolicy := {
  derive := fun actualCreator nonce =>
    if actualCreator = creator then
      if nonce = oldNonce then created else fallback
    else fallback
}

def validCallRegistry : CheckedContractRegistry := {
  lookup := fun address => if address = created then some runtime else none
}

def missingCallRegistry : CheckedContractRegistry := {
  lookup := fun _ => none
}

def mismatchCallRegistry : CheckedContractRegistry := {
  lookup := fun address =>
    if address = created then some mismatchedRuntime else none
}

def environmentWith (registry : CheckedContractRegistry) : ExecutionEnvironment := {
  callRegistry := registry
  creationTemplates := templateRegistry
  creationAddressPolicy := addressPolicy
}

def validEnvironment : ExecutionEnvironment :=
  environmentWith validCallRegistry

def missingRuntimeEnvironment : ExecutionEnvironment :=
  environmentWith missingCallRegistry

def mismatchEnvironment : ExecutionEnvironment :=
  environmentWith mismatchCallRegistry

def creatorAccount (balance nonce : Word) : Account :=
  Account.empty.withBalance balance |>.withNonce nonce

def unrelatedAccount : Account :=
  Account.empty.withBalance unrelatedBalance

def worldWithCreator (balance nonce : Word) : WorldState :=
  WorldState.empty
    |>.putAccount unrelated unrelatedAccount
    |>.putAccount creator (creatorAccount balance nonce)

def normalWorld : WorldState := worldWithCreator creatorBalance oldNonce
def overflowWorld : WorldState := worldWithCreator creatorBalance Word.maximum
def insufficientWorld : WorldState :=
  worldWithCreator insufficientBalance oldNonce
def absentCreatorWorld : WorldState :=
  WorldState.empty.putAccount unrelated unrelatedAccount
def collisionWorld : WorldState :=
  normalWorld.putAccount created Account.empty

def prepareWith
    (world : WorldState)
    (environment : ExecutionEnvironment)
    (identifier : Word := templateId) :=
  CheckedCreationPreflight.prepare world environment creator identifier value

end Tests.Adr0148CheckedCreationPreflightFixture
end

section
-- leanmerge: from Solcore.Test.Adr0148CheckedCreationPreflight
/-! External theorem consumers and actual environment-aware preflight tests. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.ContractRuntime
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
end

section
-- leanmerge: from Solcore.Test.Adr0148CreateContractWordBoundary
/-! Executable and external checks for the append-only creation host boundary. -/

set_option autoImplicit false

namespace Tests.Adr0148CreateContractWordBoundary

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

example := HostFunction.parameterType_createContractWord
example := HostFunction.resultType_createContractWord
example := HostFunction.index_createContractWord
example := hostContext_createContractWord
example := hostEnvironment_createContractWord
example := HostRequest.responseType_createContractWord
example := HostRequest.responseValue_createContractWord
example := HostSuspension.resume_createContractWord
example := hostAdvance_begin_createContractWord
example := hostAdvance_suspend_createContractWord
example := hostAdvance_invalid_createContractWord_argument
example := @typed_createContractWord_emits
example := ContractCallFailure.code_nonceOverflow
example := ContractCallFailure.code_addressCollision

private def templateId : Word := ⟨0x48, by decide⟩
private def transferredValue : Word := ⟨0x12, by decide⟩
private def input : Word := ⟨0x34, by decide⟩
private def payload : Word := ⟨0x56, by decide⟩

private def creationProgram : Program := {
  resultType := ContractCallWordResult.resultType
  body :=
    .apply
      (.var HostFunction.createContractWord.index)
      (.pair (.word templateId)
        (.pair (.word transferredValue) (.word input)))
}

private theorem creationProgram_checked :
    creationProgram.checkHost = true := by
  decide

private def creationCode : CheckedHostCoreProgram :=
  ⟨creationProgram, creationProgram_checked⟩

private def checkedCreationEmitsAndResumes : Bool :=
  match creationCode.program.runHostStateful 32 with
  | .suspended
      ⟨.createContractWord actualTemplate actualValue actualInput,
        continuation, store⟩
      remainingFuel =>
      actualTemplate == templateId && actualValue == transferredValue &&
        actualInput == input &&
        let suspension : HostSuspension :=
          ⟨.createContractWord actualTemplate actualValue actualInput,
            continuation, store⟩
        match hostRun remainingFuel
            (suspension.resume (.returned payload)) with
        | .done result finalStore =>
            result == (ContractCallWordResult.returned payload).value &&
              finalStore == []
        | _ => false
  | _ => false

private def word (value : Nat) (bound : value < wordModulus := by decide) :
    Word :=
  ⟨value, bound⟩

private def failureCodesExactAndDistinct : Bool :=
  ContractCallFailure.invalidAddress.code == word 0 &&
    ContractCallFailure.unavailable.code == word 1 &&
    ContractCallFailure.depthExceeded.code == word 2 &&
    ContractCallFailure.insufficientBalance.code == word 3 &&
    ContractCallFailure.balanceOverflow.code == word 4 &&
    ContractCallFailure.nonceOverflow.code == word 5 &&
    ContractCallFailure.addressCollision.code == word 6 &&
    decide ([ContractCallFailure.invalidAddress.code,
      ContractCallFailure.unavailable.code,
      ContractCallFailure.depthExceeded.code,
      ContractCallFailure.insufficientBalance.code,
      ContractCallFailure.balanceOverflow.code,
      ContractCallFailure.nonceOverflow.code,
      ContractCallFailure.addressCollision.code].Nodup)

private def storageAddress : Address := ⟨0x20, by decide⟩
private def callerAddress : Address := ⟨0x30, by decide⟩
private def account : Account := Account.empty
private def world : WorldState :=
  WorldState.empty.putAccount storageAddress account

private def context : HostStorageDriver.Context Unit Unit :=
  ⟨⟨storageAddress,
      ⟨⟨world, ⟨(), ()⟩⟩, (world, ⟨(), ()⟩)⟩⟩,
    account,
    by rfl⟩

private def inputs : HostStorageDriver.ExecutionInputs := {
  codeAddress := storageAddress
  callValue := Word.zero
  callerAddress := callerAddress
  inputData := HostStorageDriver.InputData.ofWord input
  currentAddress := storageAddress
}

private def flatHandled :
    HostStorageDriver.Context Unit Unit × ContractCallWordResult :=
  HostStorageDriver.handleRequest inputs context
    (.createContractWord templateId transferredValue input)

private theorem flatHandlerExact :
    flatHandled = (context, ContractCallFailure.depthExceeded.result) := by
  rfl

private theorem compileTimeBoundaryExact :
    checkedCreationEmitsAndResumes && failureCodesExactAndDistinct = true := by
  native_decide

def testAdr0148CreateContractWordBoundary : IO Unit := do
  assertTrue checkedCreationEmitsAndResumes
    "checked creation did not preserve template/value/input order"
  assertTrue failureCodesExactAndDistinct
    "creation failure codes changed or collided with existing codes"
  assertTrue (flatHandled.2 == ContractCallFailure.depthExceeded.result)
    "flat execution unexpectedly handled contract creation"

end Tests.Adr0148CreateContractWordBoundary
end

section
-- leanmerge: from Solcore.Test.Adr0148CreationEndToEndFixture
/-! Reusable checked programs and explicit state for creation E2E tests. -/

set_option autoImplicit false

namespace Tests.Adr0148CreationEndToEndFixture

open Solcore.Core
open Solcore.ContractRuntime

def creator : Address := ⟨0x2480, by decide⟩
def created : Address := ⟨0x2481, by decide⟩
def externalCaller : Address := ⟨0x2482, by decide⟩
def unrelated : Address := ⟨0x2483, by decide⟩

def templateId : Word := ⟨0x24, by decide⟩
def oldNonce : Word := ⟨7, by decide⟩
def creationValue : Word := ⟨3, by decide⟩
def creatorBalance : Word := ⟨11, by decide⟩
def unrelatedBalance : Word := ⟨19, by decide⟩
def initializerInput : Word := ⟨0xabcdef, by decide⟩
def runtimeSentinel : Word := ⟨0x5151, by decide⟩
def rootRevertReason : Word := ⟨0x5252, by decide⟩
def rootTrapReason : Word := ⟨0x5353, by decide⟩

def callerSlot : Word := ⟨0x101, by decide⟩
def valueSlot : Word := ⟨0x102, by decide⟩
def inputWordSlot : Word := ⟨0x103, by decide⟩
def inputSizeSlot : Word := ⟨0x104, by decide⟩
def storageAddressSlot : Word := ⟨0x105, by decide⟩
def currentAddressSlot : Word := ⟨0x106, by decide⟩
def codeAddressSlot : Word := ⟨0x107, by decide⟩
def runtimeSlot : Word := ⟨0x108, by decide⟩

def returned (payload : Expr) : Expr :=
  .inLeft (.sum .word .word) payload

def reverted (payload : Expr) : Expr :=
  .inRight .word (.inLeft .word payload)

def trapped (reason : Expr) : Expr :=
  .inRight .word (.inRight .word reason)

/-- Outcome selected by a root after creation returned an Address. -/
inductive RootPolicy where
  | commit
  | revert
  | trap
  deriving Repr, BEq, DecidableEq

def rootSuccess : RootPolicy → Expr
  | .commit => returned (.var 0)
  | .revert => reverted (.word rootRevertReason)
  | .trap => trapped (.word rootTrapReason)

/-- Decode the common creation/call result wire at the current lexical depth. -/
def consumeResult (policy : RootPolicy) (operation : Expr) : Expr :=
  .caseE operation
    (rootSuccess policy)
    (.caseE (.var 0)
      (reverted (.var 0))
      (.caseE (.var 0)
        (trapped (.var 0))
        (trapped (.var 0))))

def creationExpr (depth : Nat := 0) : Expr :=
  .apply (.var (HostFunction.createContractWord.index + depth))
    (.pair (.word templateId)
      (.pair (.word creationValue) (.word initializerInput)))

def rootCreationProgram (policy : RootPolicy) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body := consumeResult policy creationExpr
}

theorem rootCreationProgram_checked (policy : RootPolicy) :
    (rootCreationProgram policy).checkHost = true := by
  cases policy <;> native_decide

def rootCreationContract (policy : RootPolicy) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨rootCreationProgram policy, rootCreationProgram_checked policy⟩ rfl

/-- Create, then call the returned Address in the same root execution. -/
def rootCreateThenCallProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .caseE creationExpr
      (consumeResult .commit
        (.apply (.var (HostFunction.callContractWord.index + 1))
          (.pair (.var 0) (.word runtimeSentinel))))
      (.caseE (.var 0)
        (reverted (.var 0))
        (.caseE (.var 0)
          (trapped (.var 0))
          (trapped (.var 0))))
}

theorem rootCreateThenCallProgram_checked :
    rootCreateThenCallProgram.checkHost = true := by native_decide

def rootCreateThenCallContract : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨rootCreateThenCallProgram, rootCreateThenCallProgram_checked⟩ rfl

/-- One direct observation followed by a write to a unique storage slot. -/
def observeAndWrite
    (depth hostIndex : Nat) (argument : Expr) (slot : Word)
    (rest : Expr) : Expr :=
  .letE
    (.apply (.var (hostIndex + depth)) argument)
    (.letE
      (.apply (.var (HostFunction.storageWrite.index + depth + 1))
        (.pair (.word slot) (.var 0)))
      rest)

def initializerTerminal : CheckedCoreWordOutcome → Expr
  | .returned payload => returned (.word payload)
  | .reverted payload => reverted (.word payload)
  | .trapped reason => trapped (.word reason)

def observerTailFor
    (outcome : CheckedCoreWordOutcome) (depth : Nat) : Expr :=
  observeAndWrite depth HostFunction.callerAddress.index .unit callerSlot
    (observeAndWrite (depth + 2) HostFunction.callValue.index .unit valueSlot
      (observeAndWrite (depth + 4) HostFunction.inputDataSize.index .unit inputSizeSlot
        (observeAndWrite (depth + 6) HostFunction.storageAddress.index .unit
          storageAddressSlot
          (observeAndWrite (depth + 8) HostFunction.currentAddress.index .unit
            currentAddressSlot
            (observeAndWrite (depth + 10) HostFunction.codeAddress.index .unit
              codeAddressSlot (initializerTerminal outcome))))))

/-- Preserve the original returning observer expression. -/
def observerTail (depth : Nat) : Expr :=
  observerTailFor (.returned initializerInput) depth

/-- Observe input word zero and every initializer execution identity field. -/
def observerInitializerProgramFor
    (outcome : CheckedCoreWordOutcome) : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .caseE
      (.apply (.var HostFunction.inputDataWordBE?.index) (.word Word.zero))
      (trapped (.word Word.zero))
      (.letE
        (.apply (.var (HostFunction.storageWrite.index + 1))
          (.pair (.word inputWordSlot) (.var 0)))
        (observerTailFor outcome 2))
}

def observerInitializerProgram : Program :=
  observerInitializerProgramFor (.returned initializerInput)

theorem observerInitializerProgramFor_checked
    (outcome : CheckedCoreWordOutcome) :
    (observerInitializerProgramFor outcome).checkHost = true := by
  cases outcome <;> rfl

theorem observerInitializerProgram_checked :
    observerInitializerProgram.checkHost = true :=
  observerInitializerProgramFor_checked _

def observerInitializerFor
    (outcome : CheckedCoreWordOutcome) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨observerInitializerProgramFor outcome,
      observerInitializerProgramFor_checked outcome⟩ rfl

def observerInitializer : CheckedCoreContract :=
  observerInitializerFor (.returned initializerInput)

def revertingObserverInitializer : CheckedCoreContract :=
  observerInitializerFor (.reverted initializerInput)

def trappingObserverInitializer : CheckedCoreContract :=
  observerInitializerFor (.trapped initializerInput)

/-- Deployed runtime leaves an observable write and returns a sentinel. -/
def runtimeProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .letE
      (.apply (.var HostFunction.storageWrite.index)
        (.pair (.word runtimeSlot) (.word runtimeSentinel)))
      (returned (.word runtimeSentinel))
}

theorem runtimeProgram_checked : runtimeProgram.checkHost = true := by
  native_decide

def runtime : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨runtimeProgram, runtimeProgram_checked⟩ rfl

def templateFor (initializer : CheckedCoreContract) : CheckedCreationTemplate := {
  initializer := initializer
  runtime := runtime
}

def template : CheckedCreationTemplate := templateFor observerInitializer

def environmentFor (initializer : CheckedCoreContract) : ExecutionEnvironment := {
  callRegistry := {
    lookup := fun address => if address = created then some runtime else none
  }
  creationTemplates := {
    lookup := fun identifier =>
      if identifier = templateId then some (templateFor initializer) else none
  }
  creationAddressPolicy := {
    derive := fun actualCreator nonce =>
      if actualCreator = creator ∧ nonce = oldNonce then created else unrelated
  }
}

def environment : ExecutionEnvironment := environmentFor observerInitializer

def revertingInitializerEnvironment : ExecutionEnvironment :=
  environmentFor revertingObserverInitializer

def trappingInitializerEnvironment : ExecutionEnvironment :=
  environmentFor trappingObserverInitializer

def rootAccount (contract : CheckedCoreContract) : Account :=
  Account.empty.withBalance creatorBalance |>.withNonce oldNonce
    |>.withCode contract.code

def unrelatedAccount : Account :=
  Account.empty.withBalance unrelatedBalance

def initialWorld (contract : CheckedCoreContract) : WorldState :=
  WorldState.empty
    |>.putAccount unrelated unrelatedAccount
    |>.putAccount creator (rootAccount contract)

def rootInstalled (contract : CheckedCoreContract) :
    InstalledCheckedCoreContract (initialWorld contract) creator contract := {
  account := rootAccount contract
  account_present := by rfl
  code_present := by rfl
}

def invocation : TopLevelInvocation := {
  target := creator
  caller := externalCaller
  callValue := Word.zero
  inputData := HostStorageDriver.InputData.ofWord initializerInput
}

/-- Ready-to-run aliases keep terminal lifecycle tests declarative. -/
def commitRoot : CheckedCoreContract := rootCreationContract .commit
def revertRoot : CheckedCoreContract := rootCreationContract .revert
def trapRoot : CheckedCoreContract := rootCreationContract .trap
def sameRootCallRoot : CheckedCoreContract := rootCreateThenCallContract

def commitWorld : WorldState := initialWorld commitRoot
def revertWorld : WorldState := initialWorld revertRoot
def trapWorld : WorldState := initialWorld trapRoot
def sameRootCallWorld : WorldState := initialWorld sameRootCallRoot

def commitInstalled :
    InstalledCheckedCoreContract commitWorld creator commitRoot :=
  rootInstalled commitRoot

def revertInstalled :
    InstalledCheckedCoreContract revertWorld creator revertRoot :=
  rootInstalled revertRoot

def trapInstalled :
    InstalledCheckedCoreContract trapWorld creator trapRoot :=
  rootInstalled trapRoot

def sameRootCallInstalled :
    InstalledCheckedCoreContract sameRootCallWorld creator sameRootCallRoot :=
  rootInstalled sameRootCallRoot

end Tests.Adr0148CreationEndToEndFixture
end

section
-- leanmerge: from Solcore.Test.Adr0148CreationDepthOne
/-! E2E depth-one rejection inside a checked contract initializer. -/

set_option autoImplicit false

namespace Tests.Adr0148CreationDepthOne

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.OneLevelNestedExecution
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
end

section
-- leanmerge: from Solcore.Test.Adr0148CreationEndToEnd
/-! Executable checked-program regressions for the ADR-0148 lifecycle. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime
open Solcore.ContractRuntime.OneLevelNestedExecution
open Adr0148CreationEndToEndFixture

private def fuel : Nat := 1024

private def storageValue? (world : WorldState) (address : Address)
    (slot : Word) : Option Word :=
  (world.account? address).bind fun account => account.storageValue? slot

private def codeProgramsMatch
    (endpoints : Option CheckedHostCoreProgram ×
      Option CheckedHostCoreProgram)
    (before after : Option Program) : Bool :=
  endpoints.1.map CheckedHostCoreProgram.program == before &&
    endpoints.2.map CheckedHostCoreProgram.program == after

private def terminal?
    {initialWorld : WorldState} {root : CheckedCoreContract}
    {rootInvocation : TopLevelInvocation}
    (result : Result initialWorld root rootInvocation) :
    Option (TerminalResult initialWorld root rootInvocation) :=
  match result.view with
  | .completed terminal => some terminal
  | .outOfFuel _ _ _ => none

private def run
    (root : CheckedCoreContract) (environment : ExecutionEnvironment) :=
  runWithEnvironment root invocation (rootInstalled root) environment fuel

private def committedCreation := run commitRoot environment

private def committedCreationChecks : Bool :=
  match terminal? committedCreation with
  | none => false
  | some terminal =>
      let world := terminal.finalWorld
      let delta := terminal.committedDelta
      terminal.outcome ==
          .returned (encodeWordBytesBE (addressToWord created)) &&
        (delta.accountEndpoints creator).1.isSome &&
        (delta.accountEndpoints creator).2.isSome &&
        world.nonce? creator == some ⟨8, by decide⟩ &&
        world.balance? creator == some ⟨8, by decide⟩ &&
        world.balance? created == some creationValue &&
        (world.code? created).map CheckedHostCoreProgram.program ==
          some runtime.code.program &&
        storageValue? world created callerSlot ==
          some (addressToWord creator) &&
        storageValue? world created valueSlot == some creationValue &&
        storageValue? world created inputWordSlot == some initializerInput &&
        storageValue? world created inputSizeSlot == some ⟨32, by decide⟩ &&
        storageValue? world created storageAddressSlot ==
          some (addressToWord created) &&
        storageValue? world created currentAddressSlot ==
          some (addressToWord created) &&
        storageValue? world created codeAddressSlot ==
          some (addressToWord created) &&
        delta.nonceEndpoints creator ==
          (some oldNonce, some ⟨8, by decide⟩) &&
        delta.balanceEndpoints creator ==
          (some creatorBalance, some ⟨8, by decide⟩) &&
        delta.storageEndpoints creator callerSlot ==
          (some Word.zero, some Word.zero) &&
        codeProgramsMatch (delta.codeEndpoints creator)
          (some commitRoot.code.program) (some commitRoot.code.program) &&
        !delta.createdAccount? creator &&
        !(delta.accountEndpoints created).1.isSome &&
        (delta.accountEndpoints created).2.isSome &&
        delta.createdAccount? created &&
        delta.nonceEndpoints created == (none, some Word.zero) &&
        delta.balanceEndpoints created == (none, some creationValue) &&
        delta.storageEndpoints created callerSlot ==
          (none, some (addressToWord creator)) &&
        codeProgramsMatch (delta.codeEndpoints created)
          none (some runtime.code.program) &&
        (delta.accountEndpoints unrelated).1.isSome &&
        (delta.accountEndpoints unrelated).2.isSome &&
        !delta.createdAccount? unrelated &&
        delta.nonceEndpoints unrelated ==
          (some Word.zero, some Word.zero) &&
        delta.balanceEndpoints unrelated ==
          (some unrelatedBalance, some unrelatedBalance) &&
        codeProgramsMatch (delta.codeEndpoints unrelated) none none &&
        delta.storageEndpoints unrelated callerSlot ==
          (some Word.zero, some Word.zero)

/-- A root that commits the initializer's failure result instead of propagating it. -/
private def catchCreationProgram : Program := {
  resultType := CoreContractEntryProfile.wordOutcomeV1.resultType
  body :=
    .caseE creationExpr
      (returned (.var 0))
      (.caseE (.var 0)
        (returned (.var 0))
        (.caseE (.var 0)
          (returned (.var 0))
          (returned (.var 0))))
}

private theorem catchCreationProgram_checked :
    catchCreationProgram.checkHost = true := by native_decide

private def catchCreationRoot : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1
    ⟨catchCreationProgram, catchCreationProgram_checked⟩ rfl

private def failureRun (environment : ExecutionEnvironment) :=
  run catchCreationRoot environment

private def initializerFailureChecks
    (environment : ExecutionEnvironment) : Bool :=
  match terminal? (failureRun environment) with
  | none => false
  | some terminal =>
      let world := terminal.finalWorld
      let delta := terminal.committedDelta
      world.nonce? creator == some ⟨8, by decide⟩ &&
        world.balance? creator == some creatorBalance &&
        (world.account? created).isNone &&
        storageValue? world created callerSlot == none &&
        delta.nonceEndpoints creator ==
          (some oldNonce, some ⟨8, by decide⟩) &&
        delta.balanceChange? creator == none &&
        !delta.createdAccount? created &&
        delta.balanceChange? created == none &&
        delta.storageEndpoints created callerSlot == (none, none) &&
        delta.balanceChange? unrelated == none

private def initializerRevertChecks : Bool :=
  initializerFailureChecks revertingInitializerEnvironment

private def initializerTrapChecks : Bool :=
  initializerFailureChecks trappingInitializerEnvironment

private def rootRollbackChecks
    (root : CheckedCoreContract) (expected : FrameOutcome Word) : Bool :=
  match terminal? (run root environment) with
  | none => false
  | some terminal =>
      let world := terminal.finalWorld
      terminal.outcome == expected &&
        world.nonce? creator == some oldNonce &&
        world.balance? creator == some creatorBalance &&
        world.balance? unrelated == some unrelatedBalance &&
        (world.account? created).isNone &&
        terminal.committedDelta.nonceChange? creator == none &&
        terminal.committedDelta.balanceChange? creator == none &&
        !terminal.committedDelta.createdAccount? created

private def rootRevertChecks : Bool :=
  rootRollbackChecks revertRoot
    (.reverted (encodeWordBytesBE rootRevertReason))

private def rootTrapChecks : Bool :=
  rootRollbackChecks trapRoot (.trapped rootTrapReason)

private def sameRootCallChecks : Bool :=
  match terminal? (run sameRootCallRoot environment) with
  | none => false
  | some terminal =>
      let world := terminal.finalWorld
      terminal.outcome == .returned (encodeWordBytesBE runtimeSentinel) &&
        storageValue? world created runtimeSlot == some runtimeSentinel &&
        storageValue? world created callerSlot == some (addressToWord creator) &&
        (world.code? created).map CheckedHostCoreProgram.program ==
          some runtime.code.program &&
        terminal.committedDelta.storageEndpoints created runtimeSlot ==
          (none, some runtimeSentinel) &&
        terminal.committedDelta.createdAccount? created

private def allCreationChecks : Bool :=
  committedCreationChecks && initializerRevertChecks &&
    initializerTrapChecks && rootRevertChecks && rootTrapChecks &&
    sameRootCallChecks

private theorem compileTimeCreationChecks : allCreationChecks = true := by
  native_decide

def testAdr0148CreationEndToEnd : IO Unit := do
  assertTrue committedCreationChecks
    "initializer return did not commit observations, value, nonce, or runtime"
  assertTrue initializerRevertChecks
    "initializer revert did not refund value while retaining creator nonce"
  assertTrue initializerTrapChecks
    "initializer trap did not refund value while retaining creator nonce"
  assertTrue rootRevertChecks
    "root revert did not roll the successful creation back globally"
  assertTrue rootTrapChecks
    "root trap did not roll the successful creation back globally"
  assertTrue sameRootCallChecks
    "same-root call did not resolve and execute the deployed runtime"

end Tests
end

section
-- leanmerge: from Solcore.Test.Adr0148CreationFailureBoundary
/-! External and executable checks for stable creation failure codes. -/

set_option autoImplicit false

namespace Tests.Adr0148CreationFailureBoundary

open Solcore.Core
open Solcore.ContractRuntime

example := CheckedCreationPreflightFailure.unavailable_code
example := CheckedCreationPreflightFailure.nonceOverflow_code
example := CheckedCreationPreflightFailure.addressCollision_code
example := CheckedCreationPreflightFailure.transfer_code
example := CheckedCreationPreflightFailure.result_value
example := CheckedCreationPreflightFailure.result_response

private def codeOf
    (failure : CheckedCreationPreflightFailure) : Word :=
  failure.toContractCallFailure.code

private theorem exactCodes :
    codeOf .unavailable = ⟨1, by decide⟩ ∧
    codeOf (.transfer .insufficientBalance) = ⟨3, by decide⟩ ∧
    codeOf (.transfer .recipientOverflow) = ⟨4, by decide⟩ ∧
    codeOf .nonceOverflow = ⟨5, by decide⟩ ∧
    codeOf .addressCollision = ⟨6, by decide⟩ := by
  native_decide

def testAdr0148CreationFailureBoundary : IO Unit := do
  unless codeOf .unavailable == ⟨1, by decide⟩ do
    throw (IO.userError "creation unavailable code changed")
  unless codeOf (.transfer .insufficientBalance) == ⟨3, by decide⟩ do
    throw (IO.userError "creation balance failure compatibility changed")
  unless codeOf .nonceOverflow == ⟨5, by decide⟩ do
    throw (IO.userError "creation nonce-overflow code changed")
  unless codeOf .addressCollision == ⟨6, by decide⟩ do
    throw (IO.userError "creation collision code changed")

end Tests.Adr0148CreationFailureBoundary
end

section
-- leanmerge: from Solcore.Test.Adr0148CreationResumption
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
end
