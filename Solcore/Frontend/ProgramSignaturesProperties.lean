import Solcore.Frontend.ProgramSignatures

/-!
Properties guaranteed directly by successful whole-program signature collection.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- A successfully built signature catalog stores exactly the rules projected from
its implementation signatures. -/
theorem buildProgramSignatures_success_implRules_eq
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures) :
    signatures.implRules =
      signatures.implementations.map ProgramImplementationSignature.implRule := by
  simp only [buildProgramSignatures] at success
  split at success
  · injection success with signaturesEq
    subst signatures
    rfl
  · simp at success

/-- Membership in the collected rule list has an exact implementation-signature
origin. -/
theorem buildProgramSignatures_success_implRule_mem_iff
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    (success : buildProgramSignatures environment = .ok signatures)
    {rule : ProgramImplRule} :
    rule ∈ signatures.implRules ↔
      ∃ implementation, implementation ∈ signatures.implementations ∧
        implementation.implRule = rule := by
  rw [buildProgramSignatures_success_implRules_eq success]
  simp

end Solcore.Frontend
