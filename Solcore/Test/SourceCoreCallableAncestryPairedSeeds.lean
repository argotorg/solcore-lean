import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedSeeds

/-! The actual compiler equation authenticates named seeds. Cache completion
requires no successful seed, validator, recipe, or runtime-execution premise. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableAncestryPairedSeeds
open Frontend SourceSemantics.CoreLowering
open CallableAncestryPairedLookup

example {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (owned : CallEntryCertificates.AllAuthenticated base.plan inputs.callable.table.entries) :
    ∃ initial, SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial :=
  CallableAncestryPairedSeeds.seed_total inputs owned

example {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked}
    (compiled : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    (inputs : Inputs base) : CallEntryCertificates.AllAuthenticated base.plan inputs.callable.table.entries :=
  CallableAncestryPairedSeeds.factory_authenticated compiled inputs

example {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked}
    (compiled : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    {inputs : Inputs base}
    (inputsPrepared : SourceCoreCallableAncestryPreparation.prepareInputs base = .ok inputs) :
    ∃ prepared, SourceCoreCallableAncestryPairedPreparation.prepare base = .ok prepared :=
  CallableAncestryPairedSeeds.preparation_total compiled inputsPrepared

/-- The completed production cache exactly recognizes the independent paired
metadata domain. This does not assert that all native snapshots inhabit it. -/
example {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked}
    (compiled : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    {inputs : Inputs base}
    (inputsPrepared : SourceCoreCallableAncestryPreparation.prepareInputs base = .ok inputs) :
    ∃ prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base,
      SourceCoreCallableAncestryPairedPreparation.prepare base = .ok prepared ∧
      ∀ frame state, prepared.table.lookup? frame = some state ↔ Authenticates prepared.inputs frame state := by
  obtain ⟨prepared, accepted⟩ := CallableAncestryPairedSeeds.preparation_total compiled inputsPrepared
  exact ⟨prepared, accepted, fun _ _ => CallableAncestryPairedValidation.prepared_lookup_iff prepared⟩

end Solcore.Test.SourceCoreCallableAncestryPairedSeeds
