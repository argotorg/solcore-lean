import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedBodyProducer
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedProgramProfiles

/-! A stronger output profile is retained at its actual named compiler row.
Its roots come from the same statement-root action as the accepted compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedProfiles
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation)

structure Entry {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) where
  roots : List StatementId
  extracted : CellAwareNamedProgramProfiles.statements named = .ok roots
  profile : CellAwareMaterializedBodyProducer.Profile prepared named roots
    named.specialized.function.inferredBodyType

def entry? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) : Option (Entry prepared named) :=
  match extracted : CellAwareNamedProgramProfiles.statements named with
  | .error _ => none
  | .ok roots => do
    let profile ← CellAwareMaterializedBodyProducer.profile? prepared named roots
      named.specialized.function.inferredBodyType
    pure ⟨roots, extracted, profile⟩

def Entry.for_compilation {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} (entry : Entry prepared named)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) :
    CellAwareMaterializedBodyProducer.Profile prepared named compiled.statements
      named.specialized.function.inferredBodyType := by
  have same : entry.roots = compiled.statements := Except.ok.inj (entry.extracted.symm.trans compiled.roots)
  exact same ▸ entry.profile

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedProfiles
