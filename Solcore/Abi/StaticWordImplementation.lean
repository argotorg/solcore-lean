import Solcore.Semantics.CheckedHostCoreProgram

/-! Proof-carrying checked implementations for the Static Word ABI profile. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.Core
open Solcore.Semantics

/-- Checker-accepted method code with the exact `uint256 -> uint256` Core shape.
The first ABI profile deliberately excludes named-data definitions. -/
structure WordImplementation where
  code : CheckedHostCoreProgram
  resultType_eq :
    code.program.resultType = .function .word .word
  dataDefinitions_eq : code.program.dataDefinitions = []

namespace WordImplementation

/-- Refine already checked host-aware code exactly when it has the supported
method type and no named-data definitions. -/
def ofCode? (code : CheckedHostCoreProgram) : Option WordImplementation :=
  if resultTypeEq :
      code.program.resultType = .function .word .word then
    if dataDefinitionsEq : code.program.dataDefinitions = [] then
      some ⟨code, resultTypeEq, dataDefinitionsEq⟩
    else
      none
  else
    none

/-- Check host admission before applying the Static Word refinement. -/
def ofProgram? (program : Program) : Option WordImplementation := do
  let code ← CheckedHostCoreProgram.ofProgram? program
  ofCode? code

@[simp] theorem ofCode?_of_profile
    (code : CheckedHostCoreProgram)
    (resultTypeEq :
      code.program.resultType = .function .word .word)
    (dataDefinitionsEq : code.program.dataDefinitions = []) :
    ofCode? code = some ⟨code, resultTypeEq, dataDefinitionsEq⟩ := by
  simp [ofCode?, resultTypeEq, dataDefinitionsEq]

/-- Admission succeeds exactly for the supported checked-code shape. -/
theorem ofCode?_exists_iff (code : CheckedHostCoreProgram) :
    (∃ implementation, ofCode? code = some implementation) ↔
      code.program.resultType = .function .word .word ∧
        code.program.dataDefinitions = [] := by
  constructor
  · intro admitted
    rcases admitted with ⟨implementation, admitted⟩
    simp only [ofCode?] at admitted
    split at admitted
    · split at admitted
      · exact ⟨by assumption, by assumption⟩
      · contradiction
    · contradiction
  · rintro ⟨resultTypeEq, dataDefinitionsEq⟩
    exact ⟨⟨code, resultTypeEq, dataDefinitionsEq⟩,
      ofCode?_of_profile code resultTypeEq dataDefinitionsEq⟩

/-- Rejection is exactly a result-type or definition-table mismatch. -/
@[simp] theorem ofCode?_eq_none_iff (code : CheckedHostCoreProgram) :
    ofCode? code = none ↔
      code.program.resultType ≠ .function .word .word ∨
        code.program.dataDefinitions ≠ [] := by
  constructor
  · intro rejected
    by_cases resultTypeEq :
        code.program.resultType = .function .word .word
    · right
      intro dataDefinitionsEq
      simp [ofCode?, resultTypeEq, dataDefinitionsEq] at rejected
    · exact Or.inl resultTypeEq
  · intro mismatch
    rcases mismatch with resultTypeNe | dataDefinitionsNe
    · simp [ofCode?, resultTypeNe]
    · by_cases resultTypeEq :
          code.program.resultType = .function .word .word
      · simp [ofCode?, resultTypeEq, dataDefinitionsNe]
      · simp [ofCode?, resultTypeEq]

@[simp] theorem ofProgram?_of_rejected
    (program : Program)
    (rejected : program.checkHost = false) :
    ofProgram? program = none := by
  simp [ofProgram?,
    CheckedHostCoreProgram.ofProgram?_of_rejected program rejected]

end WordImplementation

end Solcore.Abi.V1
