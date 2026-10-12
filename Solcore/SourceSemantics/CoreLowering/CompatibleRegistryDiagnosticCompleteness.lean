import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationRanges
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts

/-! An authentic compatible diagnostic issuer rebuilds at every bounded
extension of its actual metadata registry. No execution receipt is required. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticCompleteness
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaceFaultSites

private theorem forIn_total {α β ε : Type} (items : List α)
    (step : α → β → Except ε (ForInStep β))
    (each : ∀ item, item ∈ items → ∀ state, ∃ next, step item state = .ok (.yield next)) :
    ∀ state, ∃ final, forIn items state step = .ok final := by
  induction items with
  | nil => intro state; exact ⟨state, rfl⟩
  | cons head tail ih =>
    intro state
    obtain ⟨next, advanced⟩ := each head (by simp) state
    obtain ⟨final, continued⟩ := ih (fun item member => each item (List.mem_cons_of_mem _ member)) next
    exact ⟨final, by simp only [List.forIn_cons, advanced, bind, Except.bind, continued]⟩

private theorem bind_total {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    (first : ∃ value, action = .ok value) (second : ∀ value, ∃ output, next value = .ok output) :
    ∃ output, (action >>= next) = .ok output := by
  obtain ⟨value, rfl⟩ := first
  exact second value

private theorem yield_bind_total {β ε : Type} {action : Except ε β}
    (first : ∃ value, action = .ok value) :
    ∃ output, (action >>= fun value => pure (ForInStep.yield value)) = .ok (ForInStep.yield output) := by
  obtain ⟨value, rfl⟩ := first
  exact ⟨value, rfl⟩

/-- Reserved nonwrapping ranges and the owning registry budget are sufficient
for the real pair of finite expansion loops to finish. -/
theorem missingDiagnostics_complete
    (registry : SourceCoreRawMetadata.Registry) (sites : List MissingSite)
    (bounded : registry.length ≤ registry.limits.maxEntries)
    (reserved : ∀ site, site ∈ sites → site.base.val + registry.limits.maxEntries < wordModulus) :
    ∃ rows, missingDiagnostics registry sites = .ok rows := by
  unfold missingDiagnostics
  split
  · apply bind_total
    · apply forIn_total
      intro site member rows
      apply yield_bind_total
      apply forIn_total
      rintro ⟨metadata, index⟩ stored state
      have indexBound : index < registry.entries.length := by
        exact (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp stored)).1
      cases metadata with
      | proxy | constructor => exact ⟨state, rfl⟩
      | mapping key value =>
        dsimp only
        split
        · have within : site.base.val + index + 1 < wordModulus := by
            have room := reserved site member
            change registry.entries.length ≤ registry.limits.maxEntries at bounded
            omega
          have wordAt : Word.ofNat? (site.base.val + index + 1) =
              some ⟨site.base.val + index + 1, within⟩ := by
            simp only [Word.ofNat?, within, ↓reduceDIte]
          change ∃ updated : List (Word × Diagnostic),
            ((match Word.ofNat? (site.base.val + index + 1) with
              | some value => Except.ok value
              | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted) >>= fun reason =>
                if state.any (fun previous => decide (previous.1 = reason)) then Except.ok (ForInStep.yield state)
                else Except.ok (ForInStep.yield (state ++ [(reason, {
                  error := .typeMismatch value none, site := site.site, span := some site.span })]))) =
              Except.ok (ForInStep.yield updated)
          rw [wordAt]
          simp only [bind, Except.bind]
          split <;> exact ⟨_, rfl⟩
        · exact ⟨state, rfl⟩
    · intro rows; exact ⟨rows, rfl⟩
  · contradiction

/-- Successful source preparation reserves every dynamic metadata slot before
any public input can extend the registry. -/
theorem tableForRegistry_complete
    {context : SourceCoreCompatibleValues.Context} {plan : SourceSpecializationWorklist.Plan}
    {root : SourceSpecialization.SpecializationKey} {sources : List (SourceSpecialization.SpecializationKey × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (prepared : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends context.registry registry) :
    ∃ table, program.tableForRegistry registry extension = .ok table := by
  have ranges := (CompatiblePlaceMissingPreparationRanges.prepare_ranges prepared).1
  obtain ⟨rows, expanded⟩ := missingDiagnostics_complete registry program.missing registry.length_le_limit (by
    intro site member
    rw [extension.limits]
    exact ranges.reserved site member)
  refine ⟨{program.program.rootTable with additional := program.fixed ++ rows}, ?_⟩
  simp only [Program.tableForRegistry, expanded, bind, Except.bind, pure, Except.pure]

/-- The sealed compilation supplies the authentic preparation equation. -/
theorem compiled_table_complete (compiled : SourceCoreUnifiedCompilation.Compiled)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some program)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry registry) :
    ∃ table, program.tableForRegistry registry extension = .ok table := by
  obtain ⟨root, sources, prepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  exact tableForRegistry_complete prepared registry extension

end Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticCompleteness
