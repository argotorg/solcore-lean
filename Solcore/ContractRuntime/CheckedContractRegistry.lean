import Solcore.ContractRuntime.CheckedCoreContract

/-! Dynamic resolution of registered checked contracts in a WorldState. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Internal checked contracts indexed by their semantic address. -/
structure CheckedContractRegistry where
  lookup : Address → Option CheckedCoreContract

namespace CheckedContractRegistry

/-- A checked contract together with evidence that it is installed now. -/
abbrev Resolution
    (currentWorld : WorldState)
    (target : Address) :=
  Sigma fun contract =>
    InstalledCheckedCoreContract currentWorld target contract

private theorem checkedCode_eq_of_program_eq
    {left right : CheckedHostCoreProgram}
    (programEq : left.program = right.program) :
    left = right := by
  cases left with
  | mk leftProgram leftChecked =>
      cases right with
      | mk rightProgram rightChecked =>
          simp only at programEq
          subst rightProgram
          rfl

/--
Resolve only when the registry entry still names the exact checked code stored in
the current world. The returned evidence is indexed by that current world.
-/
def resolve?
    (registry : CheckedContractRegistry)
    (currentWorld : WorldState)
    (target : Address) : Option (Resolution currentWorld target) :=
  match registry.lookup target with
  | none => none
  | some contract =>
      match accountEntry : currentWorld.account? target with
      | none => none
      | some account =>
          match codeEntry : account.code? with
          | none => none
          | some installedCode =>
              if exactCode :
                  installedCode.program = contract.code.program then
                let codeEq := checkedCode_eq_of_program_eq exactCode
                some ⟨contract, {
                  account := account
                  account_present := accountEntry
                  code_present := codeEntry.trans (congrArg some codeEq)
                }⟩
              else
                none

end CheckedContractRegistry

end Solcore.ContractRuntime
