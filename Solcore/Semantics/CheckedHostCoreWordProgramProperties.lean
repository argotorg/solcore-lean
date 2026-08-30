import Solcore.Semantics.CheckedHostCoreProgramProperties
import Solcore.Semantics.CheckedHostCoreWordProgram

/-! Admission and projection laws for checked Word-result programs. -/

set_option autoImplicit false

namespace Solcore.Semantics.CheckedHostCoreWordProgram

@[simp] theorem mk_code
    (code : CheckedHostCoreProgram)
    (resultTypeEq : code.program.resultType = .word) :
    (CheckedHostCoreWordProgram.mk code resultTypeEq).code = code :=
  rfl

@[simp] theorem mk_resultType
    (code : CheckedHostCoreProgram)
    (resultTypeEq : code.program.resultType = .word) :
    (CheckedHostCoreWordProgram.mk code resultTypeEq).code.program.resultType =
      .word :=
  resultTypeEq

@[simp] theorem ofChecked?_of_word
    (code : CheckedHostCoreProgram)
    (resultTypeEq : code.program.resultType = .word) :
    ofChecked? code = some ⟨code, resultTypeEq⟩ := by
  simp [ofChecked?, resultTypeEq]

@[simp] theorem ofChecked?_of_nonword
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word) :
    ofChecked? code = none := by
  simp [ofChecked?, resultTypeNe]

@[simp] theorem ofProgram?_of_checked_word
    (program : Core.Program)
    (checked : program.checkHost = true)
    (resultTypeEq : program.resultType = .word) :
    ofProgram? program = some ⟨⟨program, checked⟩, resultTypeEq⟩ := by
  simp [ofProgram?, checked, resultTypeEq]

@[simp] theorem ofProgram?_of_rejected
    (program : Core.Program)
    (rejected : program.checkHost = false) :
    ofProgram? program = none := by
  simp [ofProgram?, CheckedHostCoreProgram.ofProgram?, rejected]

@[simp] theorem ofProgram?_of_checked_nonword
    (program : Core.Program)
    (checked : program.checkHost = true)
    (resultTypeNe : program.resultType ≠ .word) :
    ofProgram? program = none := by
  simp [ofProgram?, checked, ofChecked?, resultTypeNe]

end Solcore.Semantics.CheckedHostCoreWordProgram
