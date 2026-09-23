import Solcore.Oracle.V5.ContractAdmission

/-! Thin resolver adapters from an admitted package to Oracle runtime layers. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.ContractAdmission.ContractPackage

open Solcore.ContractRuntime

/-- Contract resolver used by call and creation environment materialization. -/
def contractResolver
    (package : ContractPackage) : String → Option CheckedCoreContract :=
  package.lookupRaw?

/-- Checked-code resolver used by finite WorldState materialization. -/
def codeResolver
    (package : ContractPackage) : String → Option CheckedHostCoreProgram :=
  fun id => (package.lookupRaw? id).map (fun contract => contract.code)

/-- Canonical code-ID resolver used by pointwise state observations. -/
def codeIdResolver
    (package : ContractPackage) : Solcore.Core.Program → Option ContractId :=
  package.idByProgram?

end Solcore.Oracle.V5.ContractAdmission.ContractPackage
