import Solcore.Oracle.V5.PackageResolvers
import Solcore.Oracle.V5.WorldMaterialization
import Solcore.ContractRuntime.CheckedCoreContract

/-! Exact root-contract installation at the Oracle v5 execution boundary. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.ContractRuntime
open ContractAdmission

/-- The only semantic input rejections produced at root installation. -/
inductive RootInstallationRejection where
  | targetAbsent
  | targetCodeAbsent
  deriving Repr, BEq, DecidableEq

/--
The package-selected checked contract together with exact proof that its code is
installed at the requested target in this initial world.
-/
structure InstalledRoot
    (package : ContractPackage)
    (initialWorld : WorldState)
    (target : Address) where
  private mk ::
  contractId : ContractId
  contract : CheckedCoreContract
  packageLookup : package.lookup? contractId = some contract
  installed :
    InstalledCheckedCoreContract initialWorld target contract

namespace InstalledRoot

/-- The sealed root's code maps back to its exact package identifier. -/
@[simp] theorem codeId
    {package : ContractPackage}
    {initialWorld : WorldState}
    {target : Address}
    (root : InstalledRoot package initialWorld target) :
    package.idByCode? root.contract.code = some root.contractId :=
  package.idByCode?_of_lookup?_eq_some root.packageLookup

end InstalledRoot

/-- Closed result partition for root installation. -/
inductive RootInstallationResult
    (package : ContractPackage)
    (initialWorld : WorldState)
    (target : Address) where
  | rejected (reason : RootInstallationRejection)
  | internalError (error : InternalError)
  | installed (root : InstalledRoot package initialWorld target)

namespace RootInstallation

/--
Select the target's installed checked code, resolve its canonical package ID,
and seal the exact installation witness. A present foreign code value is an
internal package/world invariant failure, never a semantic root rejection.
-/
def install
    (package : ContractPackage)
    (initialWorld : WorldState)
    (target : Address) :
    RootInstallationResult package initialWorld target :=
  match accountPresent : initialWorld.account? target with
  | none => .rejected .targetAbsent
  | some account =>
      match codePresent : account.code? with
      | none => .rejected .targetCodeAbsent
      | some installedCode =>
          match reverse : package.idByCode? installedCode with
          | none => .internalError .worldCodeReferenceInvariant
          | some contractId =>
              match entryFound : package.lookupEntry? contractId with
              | none => .internalError .worldCodeReferenceInvariant
              | some entry =>
                  have reverseProgram :
                      package.idByProgram? installedCode.program =
                        some contractId :=
                    reverse
                  have programEq : installedCode.program = entry.program :=
                    package.program_eq_of_idByProgram?_and_lookupEntry?
                      reverseProgram entryFound
                  have codeEq : installedCode = entry.contract.code :=
                    CheckedHostCoreProgram.eq_of_program_eq (by
                      simpa [AdmittedEntry.program] using programEq)
                  have packageLookup :
                      package.lookup? contractId = some entry.contract := by
                    simp [ContractPackage.lookup?, entryFound]
                  .installed {
                    contractId
                    contract := entry.contract
                    packageLookup
                    installed := {
                      account
                      account_present := accountPresent
                      code_present :=
                        codePresent.trans (congrArg some codeEq)
                    }
                  }

end RootInstallation

end Solcore.Oracle.V5
