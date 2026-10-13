import Solcore.Frontend.SourceInference.ExpressionFuelAgreement
import Solcore.Frontend.SourceInference.Program

/-! Successful checks of the same original function retain the complete same
checked function, even when their structural inference budgets differ. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference

/-- Equality includes the typed body, substitutions, and solved requirements. -/
theorem checkFunctionBody_success_unique_fuel
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature} {firstFuel secondFuel : Nat}
    {first second : CheckedFunction}
    (firstAccepted : checkFunctionBody environment signatures signature firstFuel = .ok first)
    (secondAccepted : checkFunctionBody environment signatures signature secondFuel = .ok second) :
    first = second := by
  obtain ⟨firstDeclaration, firstBody, firstState, firstResult, firstFound,
    firstInferred, firstUnified, firstFinalized, firstExact⟩ :=
    checkFunctionBody_success_witness firstAccepted
  obtain ⟨secondDeclaration, secondBody, secondState, secondResult, secondFound,
    secondInferred, secondUnified, secondFinalized, secondExact⟩ :=
    checkFunctionBody_success_witness secondAccepted
  have declarationEq := Option.some.inj (firstFound.symm.trans secondFound)
  subst secondDeclaration
  have bodyEq := Detail.inferStatementsFuel_success_unique_fuel
    firstInferred secondInferred
  subst secondBody
  have stateEq := Except.ok.inj (firstUnified.symm.trans secondUnified)
  subst secondState
  have resultEq := Except.ok.inj (firstFinalized.symm.trans secondFinalized)
  subst secondResult
  exact firstExact.trans secondExact.symm

end Solcore.Frontend.SourceInference
