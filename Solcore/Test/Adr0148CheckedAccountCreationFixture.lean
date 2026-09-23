import Solcore.ContractRuntime.CheckedAccountCreationProperties

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
