import Solcore.Semantics.WorldStateDeltaProperties
import Solcore.Test.Adr0148CheckedAccountCreationFixture

/-! External consumers and actual checked creation-preparation regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Semantics
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
