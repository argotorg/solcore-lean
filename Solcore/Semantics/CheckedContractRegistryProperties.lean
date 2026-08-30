import Solcore.Semantics.CheckedContractRegistry

/-! Exact laws for current-world checked-contract resolution. -/

set_option autoImplicit false

namespace Solcore.Semantics.CheckedContractRegistry

@[simp] theorem resolve?_of_lookup_none
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    (absent : registry.lookup target = none) :
    registry.resolve? currentWorld target = none := by
  simp [resolve?, absent]

@[simp] theorem resolve?_of_account_absent
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {contract : CheckedCoreContract}
    (registered : registry.lookup target = some contract)
    (absent : currentWorld.account? target = none) :
    registry.resolve? currentWorld target = none := by
  unfold resolve?
  simp only [registered]
  split
  · rfl
  · rename_i account accountEntry
    simp_all

@[simp] theorem resolve?_of_code_absent
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {contract : CheckedCoreContract}
    {account : Account}
    (registered : registry.lookup target = some contract)
    (accountPresent : currentWorld.account? target = some account)
    (absent : account.code? = none) :
    registry.resolve? currentWorld target = none := by
  unfold resolve?
  simp only [registered]
  split
  · rfl
  · rename_i selectedAccount accountEntry
    have accountEq : selectedAccount = account :=
      Option.some.inj (accountEntry.symm.trans accountPresent)
    subst account
    split
    · rfl
    · rename_i installedCode codeEntry
      exact False.elim (by simp_all)

@[simp] theorem resolve?_of_code_mismatch
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {contract : CheckedCoreContract}
    {account : Account}
    {installedCode : CheckedHostCoreProgram}
    (registered : registry.lookup target = some contract)
    (accountPresent : currentWorld.account? target = some account)
    (codePresent : account.code? = some installedCode)
    (mismatch : installedCode.program ≠ contract.code.program) :
    registry.resolve? currentWorld target = none := by
  unfold resolve?
  simp only [registered]
  split
  · rfl
  · rename_i selectedAccount accountEntry
    have accountEq : selectedAccount = account :=
      Option.some.inj (accountEntry.symm.trans accountPresent)
    subst account
    split
    · rfl
    · rename_i selectedCode selectedCodePresent
      have codeEq : selectedCode = installedCode :=
        Option.some.inj (selectedCodePresent.symm.trans codePresent)
      subst installedCode
      simp [mismatch]

@[simp] theorem resolve?_of_lookup_and_installed
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {contract : CheckedCoreContract}
    (registered : registry.lookup target = some contract)
    (installed :
      InstalledCheckedCoreContract currentWorld target contract) :
    registry.resolve? currentWorld target = some ⟨contract, installed⟩ := by
  cases installed with
  | mk account accountPresent codePresent =>
      unfold resolve?
      simp only [registered]
      split
      · rename_i accountAbsent
        simp_all
      · rename_i selectedAccount accountEntry
        have accountEq : selectedAccount = account :=
          Option.some.inj (accountEntry.symm.trans accountPresent)
        subst account
        split
        · rename_i codeAbsent
          simp_all
        · rename_i installedCode installedCodePresent
          have codeEq : installedCode = contract.code :=
            Option.some.inj (installedCodePresent.symm.trans codePresent)
          subst installedCode
          simp only [dif_pos]

/-- Every successful resolution identifies the registry entry it consumed. -/
theorem lookup_eq_some_of_resolve?_eq_some
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {resolved : Resolution currentWorld target}
    (resolvedEq :
      registry.resolve? currentWorld target = some resolved) :
    registry.lookup target = some resolved.1 := by
  unfold resolve? at resolvedEq
  split at resolvedEq
  · simp_all
  · rename_i contract registered
    split at resolvedEq
    · simp_all
    · rename_i account accountPresent
      split at resolvedEq
      · simp_all
      · rename_i installedCode codePresent
        split at resolvedEq
        · have resolutionEq := Option.some.inj resolvedEq
          have contractEq : contract = resolved.1 :=
            congrArg Sigma.fst resolutionEq
          exact registered.trans (congrArg some contractEq)
        · simp_all

/-- Exact pointwise success law; installation evidence supplies world matching. -/
@[simp] theorem resolve?_eq_some_iff
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    (resolved : Resolution currentWorld target) :
    registry.resolve? currentWorld target = some resolved ↔
      registry.lookup target = some resolved.1 := by
  constructor
  · exact lookup_eq_some_of_resolve?_eq_some
      registry currentWorld target
  · intro registered
    exact resolve?_of_lookup_and_installed
      registry currentWorld target registered resolved.2

/-- The account witness returned on success belongs to the queried world now. -/
theorem account_present_of_resolve?_eq_some
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {resolved : Resolution currentWorld target}
    (_resolvedEq :
      registry.resolve? currentWorld target = some resolved) :
    currentWorld.account? target = some resolved.2.account :=
  resolved.2.account_present

/-- The successful account contains exactly the resolved checked program. -/
theorem code_present_of_resolve?_eq_some
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address)
    {resolved : Resolution currentWorld target}
    (_resolvedEq :
      registry.resolve? currentWorld target = some resolved) :
    resolved.2.account.code? = some resolved.1.code :=
  resolved.2.code_present

/-- Existential success is exactly registration plus current-world installation. -/
theorem exists_resolve?_eq_some_iff
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address) :
    (∃ resolved : Resolution currentWorld target,
      registry.resolve? currentWorld target = some resolved) ↔
      ∃ contract account,
        registry.lookup target = some contract ∧
        currentWorld.account? target = some account ∧
        account.code? = some contract.code := by
  constructor
  · rintro ⟨resolved, resolvedEq⟩
    exact ⟨resolved.1, resolved.2.account,
      lookup_eq_some_of_resolve?_eq_some
        registry currentWorld target resolvedEq,
      resolved.2.account_present,
      resolved.2.code_present⟩
  · rintro ⟨contract, account, registered, accountPresent, codePresent⟩
    let installed :
        InstalledCheckedCoreContract currentWorld target contract := {
      account := account
      account_present := accountPresent
      code_present := codePresent
    }
    exact ⟨⟨contract, installed⟩,
      resolve?_of_lookup_and_installed
        registry currentWorld target registered installed⟩

/-- Exact failure law: no registered contract is installed in the current world. -/
@[simp] theorem resolve?_eq_none_iff
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address) :
    registry.resolve? currentWorld target = none ↔
      ¬ ∃ contract account,
        registry.lookup target = some contract ∧
        currentWorld.account? target = some account ∧
        account.code? = some contract.code := by
  rw [← exists_resolve?_eq_some_iff]
  constructor
  · intro resolvedNone resolved
    rcases resolved with ⟨resolved, resolvedEq⟩
    rw [resolvedNone] at resolvedEq
    contradiction
  · intro noResolved
    cases resolvedEq : registry.resolve? currentWorld target with
    | none => rfl
    | some resolved =>
        exact False.elim (noResolved ⟨resolved, resolvedEq⟩)

end Solcore.Semantics.CheckedContractRegistry
