import Solcore.ContractRuntime.CheckedCoreContract

/-! Checked contracts are determined by their underlying checked program. -/
set_option autoImplicit false

namespace Solcore.ContractRuntime

theorem CheckedHostCoreProgram.eq_of_program_eq
    {left right : CheckedHostCoreProgram}
    (equal : left.program = right.program) : left = right := by
  cases left
  cases right
  simp only at equal
  subst_vars
  rfl

theorem CoreContractEntryProfile.eq_of_resultType_eq
    {left right : CoreContractEntryProfile}
    (equal : left.resultType = right.resultType) : left = right := by
  cases left <;> cases right <;> simp_all [CoreContractEntryProfile.resultType]

@[ext] theorem CheckedCoreContract.ext
    {left right : CheckedCoreContract}
    (programEq : left.code.program = right.code.program) : left = right := by
  cases left with
  | mk leftCode leftProfile leftType =>
      cases right with
      | mk rightCode rightProfile rightType =>
          change leftCode.program = rightCode.program at programEq
          have codeEq : leftCode = rightCode :=
            CheckedHostCoreProgram.eq_of_program_eq programEq
          subst rightCode
          have profileEq : leftProfile = rightProfile :=
            CoreContractEntryProfile.eq_of_resultType_eq
              (leftType.symm.trans rightType)
          subst rightProfile
          rfl

end Solcore.ContractRuntime
