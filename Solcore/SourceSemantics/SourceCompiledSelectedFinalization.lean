import Solcore.SourceSemantics.SourceCompiledLocalFinalization

/-! Selected compilation exposes the original checked body and its actual
finalizer together, before parameter specialization. All states, substitutions
and solved rows belong to that one successful checking computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem

structure Selected (compiled : SourceCoreCompiler.Compiled)
    (row : SourceSpecialization.SpecializedFunction) (fuel : Nat) where
  original : CheckedFunction
  originalMember : original ∈ compiled.program.functions
  signature : ProgramFunctionSignature
  signatureMember : signature ∈ compiled.program.signatures.functions
  body : BodyReceipt compiled.program.environment compiled.program.signatures signature fuel original
  specialized : row.function = SourceSpecialization.applyCheckedFunction row.parameterSubstitution original

theorem of_compile {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    Nonempty (Selected compiled row options.checkingFuel) := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  have lowered : SourceCoreCompiler.compileChecked compiled.program seeds options = .ok compiled := by
    simpa only [SourceCoreCompiler.compile, checked, Except.mapError, bind, Except.bind] using accepted
  obtain ⟨requests, ran⟩ := SourceCompiledLocalReadOrigins.compileChecked_worklist lowered
  obtain ⟨original, originalMember, selectedSignature, supplied, specialized⟩ :=
    SourceSpecializationWorklist.run_original ran member
  obtain ⟨signature, signatureMember, bodyChecked⟩ := checkProgram_success_function_body checked originalMember
  obtain ⟨body⟩ := BodyReceipt.of_check bodyChecked
  exact ⟨⟨original, originalMember, signature, signatureMember, body,
    SourceCompiledLocalReadOrigins.specializeFunction_applied specialized⟩⟩

namespace Selected
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem source (receipt : Selected compiled row fuel) :
    row.function.typedBody = SourceSpecialization.applyTypedSource row.parameterSubstitution
      receipt.body.finalized.typedSource := by
  rw [receipt.specialized, ← receipt.body.source]
  rfl

theorem solved (receipt : Selected compiled row fuel) :
    row.function.solvedRequirements = receipt.body.finalized.solvedRequirements.map
      (SourceSpecialization.applySolvedRequirement row.parameterSubstitution) := by
  rw [receipt.specialized, ← receipt.body.solved]
  rfl

end Selected
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
