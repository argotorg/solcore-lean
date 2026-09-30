import Solcore.Frontend.SourceCoreGeneralFunctions

/-! Discover the closed representations used by the authenticated specialization
plan. Catalog discovery is a compilation pass and never evaluates source IR. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCorePlanCatalog

abbrev Plan := SourceSpecializationWorklist.Plan

def sourceTypes (source : SourceInference.TypedSource) : List TypeSystem.Ty :=
  source.inputs.map (·.scheme.body) ++
  (SourceCoreDataPlaces.declaredBinders source).map (·.scheme.body) ++
  source.nodes.map (fun | .expression node => node.type | .statement node => node.type)

def planTypes (plan : Plan) : List TypeSystem.Ty :=
  (plan.specializations.flatMap fun specialized =>
    specialized.function.type :: specialized.function.inferredBodyType ::
      sourceTypes specialized.function.typedBody).filter SourceCoreDataCatalog.closed

inductive Error where
  | plan (error : SourceCompilationPlan.Error)
  | catalog (error : SourceCoreDataCatalog.Error)
  | lowering (error : SourceCoreGeneralEntry.CompileError SourceCoreGeneralFunctions.Error)
  deriving Repr

structure Prepared where
  checked : SourceCoreDataCatalog.Checked
  program : SourceCoreGeneralEntry.PreparedProgram checked
  deriving Repr

def prepare (program : CheckedProgram) (plan : Plan) (fuel : Nat) : Except Error Prepared := do
  let executablePlan ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError Error.plan
  let checked ← (SourceCoreDataCatalog.prepare program.signatures fuel (planTypes executablePlan)).mapError Error.catalog
  let prepared ← (SourceCoreGeneralFunctions.prepareWithCatalog program plan checked fuel).mapError Error.lowering
  pure ⟨checked, prepared⟩

end Solcore.Frontend.SourceCorePlanCatalog
