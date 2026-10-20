import Solcore.SourceSemantics.SourceCompiledGeneralizedCheckedBody
import Solcore.SourceSemantics.SourceCompiledGeneralizedRecursiveAssembly

/-! The actual recursive assembly closes original body typing. Its remaining
inputs are the concrete initialized-occurrence generalization barriers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference
open SourceCompiledLocalFinalization

theorem checked_statements_of_barriers {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations)
    (barriers : SelectedInitializerBarriers selected) :
    CheckedBodyStatementsHaveType compiled.program.signatures selected.signature selected.original :=
  checked_statements_of_recursive selected checked member
    (recursiveSoundness_of_barriers checked barriers fuel).2.2.1

/-- Initial invariants, executable interfaces and recursive child typing are
all supplied internally for the same selected original body and finalizer. -/
theorem checked_body_of_barriers {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations)
    (barriers : SelectedInitializerBarriers selected) :
    CheckedBodyHasType compiled.program.signatures selected.signature selected.original :=
  checkedBodyHasType_ofStatements selected.body.accepted
    (checked_statements_of_barriers selected checked member barriers)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
