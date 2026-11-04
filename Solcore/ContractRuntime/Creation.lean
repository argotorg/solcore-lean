import Solcore.Core.Syntax
import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.WorldState
import Solcore.ContractRuntime.Internal.WorldStateLaws
import Solcore.ContractRuntime.Contracts
import Solcore.ContractRuntime.StorageDriver
import Solcore.Core.HostMachine
import Solcore.ContractRuntime.Internal.ContractLaws

/-!
# Value transfer and creation

`WorldState.transferBalance` is the checked transfer, and `BalanceTransferFailure` its failures.
`CheckedAccountCreation.prepare` and `CheckedCreationPreflight.prepare` validate a creation before
it starts, giving a `PreparedAccountCreation` and a `PreparedCheckedCreation`.
-/

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsBalanceTransfer
/-! Checked, non-wrapping balance transfer between present accounts. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Total failure reasons for a balance transfer. -/
inductive BalanceTransferFailure where
  | senderAbsent
  | recipientAbsent
  | insufficientBalance
  | recipientOverflow
  deriving Repr, BEq, DecidableEq

namespace Balance

/-- Subtract without wrapping at zero. -/
def checkedDebit?
    (balance amount : Core.Word) : Option Core.Word :=
  if _sufficient : amount.val ≤ balance.val then
    some ⟨balance.val - amount.val,
      Nat.lt_of_le_of_lt (Nat.sub_le balance.val amount.val) balance.isLt⟩
  else
    none

/-- Add without wrapping at the 256-bit word modulus. -/
def checkedCredit?
    (balance amount : Core.Word) : Option Core.Word :=
  Core.Word.ofNat? (balance.val + amount.val)

end Balance

namespace WorldState

/--
Transfer value between two explicitly present accounts.

Failure is total and leaves the caller's immutable input state available
unchanged. Missing accounts are not created; account creation is a separate
semantic operation. Zero and self transfers still require present accounts and
sufficient funds, then return the exact input state.
-/
def transferBalance
    (state : WorldState)
    (sender recipient : Address)
    (amount : Core.Word) : Except BalanceTransferFailure WorldState :=
  match state.account? sender with
  | none => .error .senderAbsent
  | some senderAccount =>
      match state.account? recipient with
      | none => .error .recipientAbsent
      | some recipientAccount =>
          match Balance.checkedDebit? senderAccount.balance amount with
          | none => .error .insufficientBalance
          | some debited =>
              if _zero : amount = Core.Word.zero then
                .ok state
              else if _same : sender = recipient then
                .ok state
              else
                match Balance.checkedCredit? recipientAccount.balance amount with
                | none => .error .recipientOverflow
                | some credited =>
                    .ok <|
                      (state.putAccount sender
                          (senderAccount.withBalance debited)).putAccount
                        recipient (recipientAccount.withBalance credited)

end WorldState

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferProperties`
-/

/-! Exact arithmetic and frame properties of checked balance transfer. -/
set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace WorldState

theorem transferBalance_cross_account_other (state : WorldState)
    (sender recipient other : Address) (senderAccount recipientAccount : Account)
    (debited credited : Core.Word) (hos : other ≠ sender) (hor : other ≠ recipient) :
    ((state.putAccount sender (senderAccount.withBalance debited)).putAccount
      recipient (recipientAccount.withBalance credited)).account? other =
      state.account? other := by
  rw [account?_putAccount_other _ recipient other _ hor]
  rw [account?_putAccount_other _ sender other _ hos]

theorem transferBalance_cross_preserves_payload
    (senderAccount recipientAccount : Account) (debited credited : Core.Word) :
    (senderAccount.withBalance debited).code? = senderAccount.code? ∧
      (∀ slot, (senderAccount.withBalance debited).storageValue? slot =
        senderAccount.storageValue? slot) ∧
      (recipientAccount.withBalance credited).code? = recipientAccount.code? ∧
      (∀ slot, (recipientAccount.withBalance credited).storageValue? slot =
        recipientAccount.storageValue? slot) := by simp

end WorldState

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferInstallationProperties`
-/

/-! Checked contract installation survives balance-only state transitions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

/-- A successful balance transfer preserves every installed checked contract. -/
def transferBalance_preserves_installed
    {state next : WorldState}
    {sender recipient target : Address}
    {amount : Core.Word}
    {contract : CheckedCoreContract}
    (success : state.transferBalance sender recipient amount = .ok next)
    (installed : InstalledCheckedCoreContract state target contract) :
    InstalledCheckedCoreContract next target contract := by
  unfold transferBalance at success
  split at success
  · contradiction
  · rename_i senderAccount senderPresent
    split at success
    · contradiction
    · rename_i recipientAccount recipientPresent
      split at success
      · contradiction
      · rename_i debited debitPresent
        split at success
        · cases success
          exact installed
        · rename_i nonzero
          split at success
          · cases success
            exact installed
          · rename_i different
            split at success
            · contradiction
            · rename_i credited creditPresent
              injection success with nextEq
              subst next
              have payload := transferBalance_cross_preserves_payload
                senderAccount recipientAccount debited credited
              by_cases targetRecipient : target = recipient
              · subst target
                have accountEq : installed.account = recipientAccount := by
                  exact Option.some.inj
                    (installed.account_present.symm.trans recipientPresent)
                refine {
                  account := recipientAccount.withBalance credited
                  account_present := ?_
                  code_present := ?_
                }
                · exact account?_putAccount_same _ _ _
                · calc
                    (recipientAccount.withBalance credited).code? =
                        recipientAccount.code? := payload.2.2.1
                    _ = installed.account.code? := by rw [accountEq]
                    _ = some contract.code := installed.code_present
              · by_cases targetSender : target = sender
                · subst target
                  have accountEq : installed.account = senderAccount := by
                    exact Option.some.inj
                      (installed.account_present.symm.trans senderPresent)
                  refine {
                    account := senderAccount.withBalance debited
                    account_present := ?_
                    code_present := ?_
                  }
                  · rw [account?_putAccount_other _ recipient sender _ different]
                    exact account?_putAccount_same _ _ _
                  · calc
                      (senderAccount.withBalance debited).code? =
                          senderAccount.code? := payload.1
                      _ = installed.account.code? := by rw [accountEq]
                      _ = some contract.code := installed.code_present
                · refine {
                    account := installed.account
                    account_present := ?_
                    code_present := installed.code_present
                  }
                  rw [transferBalance_cross_account_other state sender recipient
                    target senderAccount recipientAccount debited credited
                    targetSender targetRecipient]
                  exact installed.account_present

end Solcore.ContractRuntime.WorldState

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferPresenceProperties`
-/

/-! Account presence survives successful balance-only transitions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

def transferBalance_preserves_present
    {state next : WorldState}
    {sender recipient target : Address}
    {amount : Core.Word}
    (success : state.transferBalance sender recipient amount = .ok next)
    (present : PresentAccountAt state target) :
    PresentAccountAt next target := by
  unfold transferBalance at success
  split at success
  · contradiction
  · rename_i senderAccount senderPresent
    split at success
    · contradiction
    · rename_i recipientAccount recipientPresent
      split at success
      · contradiction
      · rename_i debited debitPresent
        split at success
        · cases success
          exact present
        · rename_i nonzero
          split at success
          · cases success
            exact present
          · rename_i different
            split at success
            · contradiction
            · rename_i credited creditPresent
              injection success with nextEq
              subst next
              by_cases targetRecipient : target = recipient
              · subst target
                exact ⟨recipientAccount.withBalance credited,
                  account?_putAccount_same _ _ _⟩
              · by_cases targetSender : target = sender
                · subst target
                  refine ⟨senderAccount.withBalance debited, ?_⟩
                  rw [account?_putAccount_other _ recipient sender _ different]
                  exact account?_putAccount_same _ _ _
                · refine ⟨present.account, ?_⟩
                  rw [transferBalance_cross_account_other state sender recipient
                    target senderAccount recipientAccount debited credited
                    targetSender targetRecipient]
                  exact present.present

end Solcore.ContractRuntime.WorldState

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferCallFailure`
-/

/-! Stable checked-call failures for total balance-transfer failures. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace BalanceTransferFailure

/-- Translate every checked transfer failure into the public call failure ABI. -/
def toContractCallFailure : BalanceTransferFailure → ContractCallFailure
  | .senderAbsent => .unavailable
  | .recipientAbsent => .unavailable
  | .insufficientBalance => .insufficientBalance
  | .recipientOverflow => .balanceOverflow

/-- Inject a checked transfer failure into the typed contract-call result. -/
def toContractCallResult
    (failure : BalanceTransferFailure) : Core.ContractCallWordResult :=
  failure.toContractCallFailure.result

end BalanceTransferFailure

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsCheckedAccountCreation
/-! Total state preparation for checked contract-account creation. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Ordered, total failures of creation preflight. -/
inductive CreationPreflightFailure where
  | creatorAbsent
  | nonceOverflow
  | addressCollision
  | transfer (failure : BalanceTransferFailure)
  deriving Repr, BEq, DecidableEq

/--
Exact evidence for every intermediate state produced before initializer
execution. No field is inferred from a later world: the old nonce, derived
address, increment, collision check, provisional insertion, and value transfer
are all retained explicitly.
-/
structure PreparedAccountCreation
    (current : WorldState)
    (policy : CreationAddressPolicy)
    (creator : Address)
    (value : Core.Word)
    (initializer : CheckedCoreContract) where
  creatorAccount : Account
  creator_present : current.account? creator = some creatorAccount
  oldNonce : Core.Word
  oldNonce_eq : oldNonce = creatorAccount.nonce
  createdAddress : Address
  createdAddress_eq : createdAddress = policy.derive creator oldNonce
  incrementedCreator : Account
  increment_eq : creatorAccount.incrementNonce? = some incrementedCreator
  created_absent : current.account? createdAddress = none
  postNonceWorld : WorldState
  postNonceWorld_eq :
    postNonceWorld = current.putAccount creator incrementedCreator
  provisionalAccount : Account
  provisionalAccount_eq :
    provisionalAccount = Account.empty.withCode initializer.code
  provisionalWorld : WorldState
  provisionalWorld_eq :
    provisionalWorld = postNonceWorld.putAccount createdAddress provisionalAccount
  initializerWorld : WorldState
  transfer_eq :
    provisionalWorld.transferBalance creator createdAddress value =
      .ok initializerWorld
  initializerInstalled :
    InstalledCheckedCoreContract initializerWorld createdAddress initializer

namespace CheckedAccountCreation

/--
Prepare a creation transaction in consensus order. Every failure returns before
publishing a successor world; successful value movement is checked and exact.
-/
def prepare
    (current : WorldState)
    (policy : CreationAddressPolicy)
    (creator : Address)
    (value : Core.Word)
    (initializer : CheckedCoreContract) :
    Except CreationPreflightFailure
      (PreparedAccountCreation current policy creator value initializer) :=
  match creatorEq : current.account? creator with
  | none => .error .creatorAbsent
  | some creatorAccount =>
      let oldNonce := creatorAccount.nonce
      let createdAddress := policy.derive creator oldNonce
      match incrementEq : creatorAccount.incrementNonce? with
      | none => .error .nonceOverflow
      | some incrementedCreator =>
          match absentEq : current.account? createdAddress with
          | some _ => .error .addressCollision
          | none =>
              let postNonceWorld :=
                current.putAccount creator incrementedCreator
              let provisionalAccount :=
                Account.empty.withCode initializer.code
              let provisionalWorld :=
                postNonceWorld.putAccount createdAddress provisionalAccount
              let provisionalInstalled :
                  InstalledCheckedCoreContract provisionalWorld createdAddress
                    initializer := {
                account := provisionalAccount
                account_present := by
                  exact WorldState.account?_putAccount_same _ _ _
                code_present := by rfl
              }
              match transferEq : provisionalWorld.transferBalance creator
                  createdAddress value with
              | .error failure => .error (.transfer failure)
              | .ok initializerWorld =>
                  .ok {
                    creatorAccount := creatorAccount
                    creator_present := creatorEq
                    oldNonce := oldNonce
                    oldNonce_eq := rfl
                    createdAddress := createdAddress
                    createdAddress_eq := rfl
                    incrementedCreator := incrementedCreator
                    increment_eq := incrementEq
                    created_absent := absentEq
                    postNonceWorld := postNonceWorld
                    postNonceWorld_eq := rfl
                    provisionalAccount := provisionalAccount
                    provisionalAccount_eq := rfl
                    provisionalWorld := provisionalWorld
                    provisionalWorld_eq := rfl
                    initializerWorld := initializerWorld
                    transfer_eq := transferEq
                    initializerInstalled :=
                      WorldState.transferBalance_preserves_installed transferEq
                        provisionalInstalled
                  }

end CheckedAccountCreation

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsCheckedCreationPreflight
/-! Immutable-environment validation and total checked creation preflight. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Exact call-registry registration of one template's checked runtime. -/
structure RegisteredCreationRuntime
    (environment : ExecutionEnvironment)
    (createdAddress : Address)
    (template : CheckedCreationTemplate) where
  contract : CheckedCoreContract
  lookup_eq : environment.callRegistry.lookup createdAddress = some contract
  program_eq : contract.code.program = template.runtime.code.program
  contract_eq : contract = template.runtime

namespace RegisteredCreationRuntime

/-- Validate the exact checked runtime before any creation state transition. -/
def validate?
    (environment : ExecutionEnvironment)
    (createdAddress : Address)
    (template : CheckedCreationTemplate) :
    Option (RegisteredCreationRuntime environment createdAddress template) :=
  match lookupEq : environment.callRegistry.lookup createdAddress with
  | none => none
  | some contract =>
      if programEq : contract.code.program = template.runtime.code.program then
        some {
          contract := contract
          lookup_eq := lookupEq
          program_eq := programEq
          contract_eq := CheckedCoreContract.ext programEq
        }
      else none

end RegisteredCreationRuntime

/-- Public failure classification for environment-aware creation preparation. -/
inductive CheckedCreationPreflightFailure where
  | unavailable
  | nonceOverflow
  | addressCollision
  | transfer (failure : BalanceTransferFailure)
  deriving Repr, BEq, DecidableEq

/-- All immutable selections and exact state preparation retained on success. -/
structure PreparedCheckedCreation
    (current : WorldState)
    (environment : ExecutionEnvironment)
    (creator : Address)
    (templateId value : Core.Word) where
  template : CheckedCreationTemplate
  template_lookup : environment.creationTemplates.lookup templateId = some template
  creatorAccount : Account
  creator_present : current.account? creator = some creatorAccount
  oldNonce : Core.Word
  oldNonce_eq : oldNonce = creatorAccount.nonce
  createdAddress : Address
  createdAddress_eq :
    createdAddress = environment.creationAddressPolicy.derive creator oldNonce
  runtimeRegistration :
    RegisteredCreationRuntime environment createdAddress template
  statePreparation :
    PreparedAccountCreation current environment.creationAddressPolicy creator value
      template.initializer
  preparation_address_eq : statePreparation.createdAddress = createdAddress

namespace CheckedCreationPreflight

/--
Select immutable inputs and validate runtime registration before delegating to
the state preparation primitive. No transfer occurs before all checks pass.
-/
def prepare
    (current : WorldState)
    (environment : ExecutionEnvironment)
    (creator : Address)
    (templateId value : Core.Word) :
    Except CheckedCreationPreflightFailure
      (PreparedCheckedCreation current environment creator templateId value) :=
  match templateEq : environment.creationTemplates.lookup templateId with
  | none => .error .unavailable
  | some template =>
      match creatorEq : current.account? creator with
      | none => .error .unavailable
      | some creatorAccount =>
          let oldNonce := creatorAccount.nonce
          let createdAddress :=
            environment.creationAddressPolicy.derive creator oldNonce
          match incrementEq : creatorAccount.incrementNonce? with
          | none => .error .nonceOverflow
          | some _incremented =>
              match collisionEq : current.account? createdAddress with
              | some _ => .error .addressCollision
              | none =>
                  match RegisteredCreationRuntime.validate? environment
                      createdAddress template with
                  | none => .error .unavailable
                  | some registration =>
                      match preparedEq : CheckedAccountCreation.prepare current
                          environment.creationAddressPolicy creator value
                          template.initializer with
                      | .error (.transfer failure) => .error (.transfer failure)
                      | .error .creatorAbsent => .error .unavailable
                      | .error .nonceOverflow => .error .nonceOverflow
                      | .error .addressCollision => .error .addressCollision
                      | .ok statePreparation => .ok {
                          template := template
                          template_lookup := templateEq
                          creatorAccount := creatorAccount
                          creator_present := creatorEq
                          oldNonce := oldNonce
                          oldNonce_eq := rfl
                          createdAddress := createdAddress
                          createdAddress_eq := rfl
                          runtimeRegistration := registration
                          statePreparation := statePreparation
                          preparation_address_eq := by
                            have accountEq :
                                statePreparation.creatorAccount = creatorAccount :=
                              Option.some.inj
                                (statePreparation.creator_present.symm.trans
                                  creatorEq)
                            rw [statePreparation.createdAddress_eq,
                              statePreparation.oldNonce_eq, accountEq]
                        }

end CheckedCreationPreflight

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCreationPreflightProperties`
-/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCreationPreflightFailure`
-/

/-! Stable call-result injection for checked creation preflight failures. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedCreationPreflightFailure

/-- Preserve existing call failures and append creation-specific failures. -/
def toContractCallFailure :
    CheckedCreationPreflightFailure → ContractCallFailure
  | .unavailable => .unavailable
  | .nonceOverflow => .nonceOverflow
  | .addressCollision => .addressCollision
  | .transfer failure => failure.toContractCallFailure

/-- Inject every preflight failure into the typed failed-result branch. -/
def toContractCallResult
    (failure : CheckedCreationPreflightFailure) :
    Core.ContractCallWordResult :=
  failure.toContractCallFailure.result

end Solcore.ContractRuntime.CheckedCreationPreflightFailure
end
