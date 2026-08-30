import Solcore.Semantics.CheckedAccountCreation
import Solcore.Semantics.CheckedCoreContractExtensionality
import Solcore.Semantics.ExecutionEnvironment

/-! Immutable-environment validation and total checked creation preflight. -/
set_option autoImplicit false

namespace Solcore.Semantics

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
end Solcore.Semantics
