import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceInference.FunctionFuelAgreement

/-! Successful checks at different structural budgets retain the same entire
program, including its ordered function and implementation method records. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend
open SourceInference

private theorem functions_agree
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {firstFuel secondFuel : Nat} {catalog : List ProgramFunctionSignature}
    {first second : List CheckedFunction}
    (firstChecked : FunctionBodiesChecked environment signatures firstFuel catalog first)
    (secondChecked : FunctionBodiesChecked environment signatures secondFuel catalog second) :
    first = second := by
  induction firstChecked generalizing second with
  | nil => cases secondChecked; rfl
  | cons head tail induction =>
    cases secondChecked with
    | cons other rest =>
      simp only [checkFunctionBody_success_unique_fuel head other, induction rest]

private theorem method_agrees
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {firstFuel secondFuel : Nat} {target : ImplementationMethodCheckTarget}
    {first second : CheckedImplementationMethod}
    (firstChecked : ImplementationMethodBodyChecked environment signatures firstFuel target first)
    (secondChecked : ImplementationMethodBodyChecked environment signatures secondFuel target second) :
    first = second := by
  cases firstChecked with
  | intro firstId firstTrait firstBody =>
    cases secondChecked with
    | intro secondId secondTrait secondBody =>
      have sameTrait := Option.some.inj (firstTrait.symm.trans secondTrait)
      cases sameTrait
      have sameBody := checkFunctionBody_success_unique_fuel firstBody secondBody
      cases first
      cases second
      simp_all

private theorem methods_agree
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {firstFuel secondFuel : Nat} {catalog : List ImplementationMethodCheckTarget}
    {first second : List CheckedImplementationMethod}
    (firstChecked : ImplementationMethodBodiesChecked environment signatures firstFuel catalog first)
    (secondChecked : ImplementationMethodBodiesChecked environment signatures secondFuel catalog second) :
    first = second := by
  induction firstChecked generalizing second with
  | nil => cases secondChecked; rfl
  | cons head tail induction =>
    cases secondChecked with
    | cons other rest =>
      simp only [method_agrees head other, induction rest]

/-- The entire result agrees, including the ordered original method catalog. -/
theorem checkProgram_success_unique_fuel
    {raw : Workspace.RawWorkspace} {firstFuel secondFuel : Nat}
    {first second : CheckedProgram}
    (firstChecked : checkProgram raw firstFuel = .ok first)
    (secondChecked : checkProgram raw secondFuel = .ok second) : first = second := by
  obtain ⟨firstLoaded, firstLoad, firstAccepted⟩ := checkProgram_success_load firstChecked
  obtain ⟨secondLoaded, secondLoad, secondAccepted⟩ := checkProgram_success_load secondChecked
  have sameLoad := Except.ok.inj (firstLoad.symm.trans secondLoad)
  subst secondLoaded
  have sameEnvironment := (checkLoadedProgram_success_environment firstAccepted).trans
    (checkLoadedProgram_success_environment secondAccepted).symm
  have sameSignatures := Except.ok.inj ((checkLoadedProgram_success_signatures firstAccepted).symm.trans
    (checkLoadedProgram_success_signatures secondAccepted))
  obtain ⟨firstFunctions, firstMethods⟩ := checkLoadedProgram_success_body_checks firstAccepted
  obtain ⟨secondFunctions, secondMethods⟩ := checkLoadedProgram_success_body_checks secondAccepted
  cases first
  cases second
  simp only at sameEnvironment sameSignatures firstFunctions secondFunctions firstMethods secondMethods ⊢
  cases sameEnvironment
  cases sameSignatures
  have sameFunctions := functions_agree firstFunctions secondFunctions
  have sameMethods := methods_agree firstMethods secondMethods
  cases sameFunctions
  cases sameMethods
  rfl

end Solcore.Frontend
