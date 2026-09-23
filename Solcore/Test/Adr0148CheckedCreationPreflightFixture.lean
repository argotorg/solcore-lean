import Solcore.ContractRuntime.CheckedCreationPreflightFailureProperties

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
