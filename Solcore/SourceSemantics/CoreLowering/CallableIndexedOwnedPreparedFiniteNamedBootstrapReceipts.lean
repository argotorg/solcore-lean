import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBootstrapReceipts

/-! Actual finite issued Headers supply the cache ledger and empty Source
locals used by bootstrap. Distinct selected input slots remain a static
inventory condition; no Header ledger or desired entry facts are supplied. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedFiniteNamedInventories
open CallableIndexedOwnedNamedBootstrapReceipts
open RecursiveNamedCatalog

private theorem closures_of_same_pass {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleMarkedFunctions.Base checked}
    {firstRepresentation secondRepresentation : SourceCoreGeneralFunctions.Representation}
    {firstFuel secondFuel : Nat}
    (representation : firstRepresentation = secondRepresentation) (fuel : firstFuel = secondFuel)
    {first : SourceCoreCompatibleMarkedFunctions.Compilation base firstRepresentation firstFuel}
    {second : SourceCoreCompatibleMarkedFunctions.Compilation base secondRepresentation secondFuel}
    (same : HEq first second) : first.closures = second.closures := by
  cases representation
  cases fuel
  exact congrArg (fun compiled => compiled.closures) (eq_of_heq same)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (inputs : List (Input compiled))

theorem slots : (headers wellFormed inputs).map (·.slot) =
    inputs.map (fun input => input.prepared.index) := by
  simp only [headers, List.map_map]
  apply List.map_congr_left
  intro input _member
  exact (issue wellFormed input).aligned.slot

theorem empty_locals : ∀ header, header ∈ headers wellFormed inputs →
    header.function.context.locals = [] := by
  intro header member
  obtain ⟨input, _member, same⟩ := List.mem_map.mp member
  subst header
  rw [(issue wellFormed input).function]
  rfl

theorem cache : ∀ header, header ∈ headers wellFormed inputs →
    compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType) header.code) := by
  intro header member
  obtain ⟨input, _member, same⟩ := List.mem_map.mp member
  subst header
  let receipt := issue wellFormed input
  have sameClosures := closures_of_same_pass receipt.aligned.representation
    receipt.aligned.compiledFuel receipt.aligned.secondPass
  simpa only [sameClosures] using receipt.header.cached

/-- All ledger fields are derived from authentic issued rows and the checked
program. The finite list must select each real physical slot at most once. -/
theorem ledger (distinct : (inputs.map (fun input => input.prepared.index)).Nodup) :
    Ledger (headers wellFormed inputs) compiled.indexed.secondPass.closures where
  slots := by rw [slots wellFormed inputs]; exact distinct
  owners := wellFormed.function_ids
  cached := cache wellFormed inputs

/-- The original entry factory runs once on the finite inventory. Global
sizes, empty locals and the entire cache ledger are internal conclusions. -/
theorem of_recipe {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ world, Nonempty (Bootstrap (headers := headers wellFormed inputs) functions registry world) :=
  CallableIndexedOwnedNamedBootstrapReceipts.of_recipe accepted
    (ledger wellFormed inputs distinct) (globals wellFormed inputs)
    (empty_locals wellFormed inputs) functions registry

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts
