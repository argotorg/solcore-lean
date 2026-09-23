import Solcore.ContractRuntime.CheckedAccountCreation
import Solcore.ContractRuntime.CheckedCoreContract
import Solcore.ContractRuntime.ExecutionEnvironment
import Solcore.ContractRuntime.BalanceTransfer
import Solcore.ContractRuntime.ContractCallFailure

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
namespace Solcore.ContractRuntime
namespace RegisteredCreationRuntime

@[simp] theorem validate?_lookup_none (e : ExecutionEnvironment) (a : Address)
    (t : CheckedCreationTemplate) (h : e.callRegistry.lookup a = none) :
    validate? e a t = none := by
  unfold validate?; split
  · rfl
  · simp_all

@[simp] theorem validate?_program_mismatch (e : ExecutionEnvironment) (a : Address)
    (t : CheckedCreationTemplate) (c : CheckedCoreContract)
    (hl : e.callRegistry.lookup a = some c)
    (hp : c.code.program ≠ t.runtime.code.program) : validate? e a t = none := by
  unfold validate?; split
  · simp_all
  · rename_i found heq
    have : found = c := Option.some.inj (heq.symm.trans hl)
    subst found
    simp [hp]

theorem validate?_some_program_eq (e : ExecutionEnvironment) (a : Address)
    (t : CheckedCreationTemplate) (r : RegisteredCreationRuntime e a t)
    (_h : validate? e a t = some r) :
    r.contract.code.program = t.runtime.code.program := r.program_eq
end RegisteredCreationRuntime

namespace CheckedCreationPreflight
@[simp] theorem prepare_templateUnavailable (s : WorldState)
    (e : ExecutionEnvironment) (creator : Address) (id value : Core.Word)
    (h : e.creationTemplates.lookup id = none) :
    prepare s e creator id value = .error .unavailable := by
  unfold prepare; split
  · rfl
  · simp_all

@[simp] theorem prepare_creatorUnavailable (s : WorldState)
    (e : ExecutionEnvironment) (creator : Address) (id value : Core.Word)
    (t : CheckedCreationTemplate) (ht : e.creationTemplates.lookup id = some t)
    (ha : s.account? creator = none) :
    prepare s e creator id value = .error .unavailable := by
  unfold prepare; split
  · simp_all
  · rename_i actual heq
    have : actual = t := Option.some.inj (heq.symm.trans ht)
    subst actual
    split <;> simp_all

@[simp] theorem prepare_nonceOverflow (s : WorldState)
    (e : ExecutionEnvironment) (creator : Address) (id value : Core.Word)
    (t : CheckedCreationTemplate) (account : Account)
    (ht : e.creationTemplates.lookup id = some t)
    (ha : s.account? creator = some account)
    (ho : account.incrementNonce? = none) :
    prepare s e creator id value = .error .nonceOverflow := by
  unfold prepare; split
  · simp_all
  · rename_i actualT teq
    have : actualT = t := Option.some.inj (teq.symm.trans ht); subst actualT
    split
    · simp_all
    · rename_i actualA aeq
      have : actualA = account := Option.some.inj (aeq.symm.trans ha); subst actualA
      split <;> simp_all

theorem PreparedCheckedCreation.runtime_exact
    {s : WorldState} {e : ExecutionEnvironment} {creator : Address}
    {id value : Core.Word} (p : PreparedCheckedCreation s e creator id value) :
    p.runtimeRegistration.contract = p.template.runtime := p.runtimeRegistration.contract_eq

theorem PreparedCheckedCreation.address_exact
    {s : WorldState} {e : ExecutionEnvironment} {creator : Address}
    {id value : Core.Word} (p : PreparedCheckedCreation s e creator id value) :
    p.statePreparation.createdAddress =
      e.creationAddressPolicy.derive creator p.oldNonce := by
  rw [p.preparation_address_eq, p.createdAddress_eq]
end CheckedCreationPreflight
end Solcore.ContractRuntime

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

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCreationPreflightFailureProperties`
-/

/-! Exact stable codes for checked creation preflight failure injection. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedCreationPreflightFailure

@[simp] theorem unavailable_code :
    CheckedCreationPreflightFailure.unavailable.toContractCallFailure.code =
      ⟨1, by decide⟩ := by
  rfl

@[simp] theorem nonceOverflow_code :
    CheckedCreationPreflightFailure.nonceOverflow.toContractCallFailure.code =
      ⟨5, by decide⟩ := by
  rfl

@[simp] theorem addressCollision_code :
    CheckedCreationPreflightFailure.addressCollision.toContractCallFailure.code =
      ⟨6, by decide⟩ := by
  rfl

@[simp] theorem transfer_code (failure : BalanceTransferFailure) :
    (CheckedCreationPreflightFailure.transfer failure).toContractCallFailure =
      failure.toContractCallFailure := by
  rfl

@[simp] theorem result_value (failure : CheckedCreationPreflightFailure) :
    failure.toContractCallResult.value =
      .inRight .word
        (.inRight .word
          (.inRight .word
            (.word failure.toContractCallFailure.code))) := by
  cases failure <;> rfl

@[simp] theorem result_response (failure : CheckedCreationPreflightFailure) :
    Core.HostRequest.responseValue
        (.createContractWord Core.Word.zero Core.Word.zero Core.Word.zero)
        failure.toContractCallResult =
      failure.toContractCallResult.value := by
  rfl

end Solcore.ContractRuntime.CheckedCreationPreflightFailure
