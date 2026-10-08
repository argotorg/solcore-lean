import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts

/-! Public compiler receipts retain the actual diagnostic preparation and its
selected specialization Source. This is static metadata provenance; Source
execution and body meaning are not premises. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
open Core Frontend SourceInference
open RecursiveNamedPublicSpecializationMeaning

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- The compatible place pass keeps the actual program fault inventory. -/
theorem data_place_base {context : SourceCoreCompatibleValues.Context}
    {plan : SourceSpecializationWorklist.Plan} {root : SourceSpecialization.SpecializationKey}
    {sources : List (SourceSpecialization.SpecializationKey × TypedSource)}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok diagnostics) :
    SourceCoreProgramFaultSites.prepare plan root = .ok diagnostics.program.base := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.prepare at accepted
  obtain ⟨base, baseMade, accepted⟩ := bind_ok accepted
  obtain ⟨state, _stateMade, accepted⟩ := bind_ok accepted
  obtain ⟨extra, _extraMade, accepted⟩ := bind_ok accepted
  cases accepted
  exact mapError_ok baseMade

/-- The actual compatible compiler's nonempty diagnostic receipt is the
successful place preparation for its retained executable plan. -/
theorem compatible_diagnostics {source : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = source.signatures}
    {fuel : Nat} {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog source plan checked ownership fuel = .ok prepared)
    (found : prepared.diagnostics = some diagnostics) :
    ∃ root sources, SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial checked)
      prepared.plan root sources = .ok diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _executableMade, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _localsMade, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _contextsMade, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _functionsMade, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    cases found
  · obtain ⟨actual, actualMade, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _tableMade, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _callableMade, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _nativeLocalsMade, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _closuresMade, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _inputsMade, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _entriesMade, accepted⟩ := bind_ok accepted
      cases accepted
      cases found
      exact ⟨_, _, mapError_ok actualMade⟩
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _closuresMade, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _inputsMade, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _entriesMade, accepted⟩ := bind_ok accepted
      cases accepted
      cases found
      exact ⟨_, _, mapError_ok actualMade⟩

/-- Catalog preparation preserves that same actual diagnostic producer. -/
theorem automatic_diagnostics {source : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial automatic.checked)}
    (accepted : SourceCoreCompatibleFunctions.prepare source plan fuel = .ok automatic)
    (found : automatic.prepared.diagnostics = some diagnostics) :
    ∃ root sources, SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial automatic.checked)
      automatic.prepared.plan root sources = .ok diagnostics := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _executableMade, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _localsMade, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, baseMade, accepted⟩ := bind_ok accepted
    cases accepted
    exact compatible_diagnostics baseMade found

/-- The sealed indexed compilation retains the original compatible diagnostic
inventory, rather than a second table inferred from equal native code. -/
theorem compiled_diagnostics (compiled : SourceCoreUnifiedCompilation.Compiled)
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics) :
    ∃ root sources, SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial compiled.compatible.checked)
      compiled.indexed.base.plan root sources = .ok diagnostics := by
  rw [SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared] at found ⊢
  exact automatic_diagnostics compiled.compatiblePrepared found

/-- The lowered table is exactly the real second-pass table, with only the
actual callable root diagnostic replacement allowed by the compiler. -/
structure Receipt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row) : Prop where
  actual : ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
    compiled.indexed.base.diagnostics = some diagnostics ∧
    prepared.diagnostics = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}

/-- Exact cached hook authority authenticates the same specialization Source
whose actual diagnostic row supplies this prepared assignment table. -/
theorem assignments_prepared {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
    (receipt : Receipt prepared) :
    ∃ first, SourceCoreAssignmentFaultSites.prepare
      prepared.named.specialized.function.typedBody first = .ok prepared.compilation.own.assignments := by
  obtain ⟨diagnostics, found, lowered⟩ := receipt.actual
  obtain ⟨root, sources, made⟩ := compiled_diagnostics compiled found
  have programMade := data_place_base made
  have selected : diagnostics.program.base.find? prepared.named.signature.key = some prepared.compilation.own := by
    have selected := prepared.compilation.diagnostic
    have sameBase : prepared.diagnostics.base = diagnostics.program.base := by
      rw [lowered]
      cases compiled.indexed.base.callableContext <;> rfl
    rw [sameBase] at selected
    exact selected
  exact SourceCoreProgramFaultSites.prepare_assignments_at programMade
    (CallableIndexedActualNamedSourceReceipts.cached_record compiled prepared.selected prepared.compilation.hook) selected

/-- Public preparation chooses the same actual second-pass compiler receipt
and retains its diagnostic identity. Existing Prepared values remain unchanged. -/
theorem of_public_compile {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
    (issued : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe)
    (member : row ∈ recipe.compiled.validationPlan.specializations) :
    ∃ prepared : Prepared recipe.compiled row, Receipt prepared := by
  obtain ⟨programEq, origins⟩ := public_origins accepted issued
  obtain ⟨index, named, selected, same⟩ := cached_row recipe.compiled member
  obtain ⟨diagnostics, code, actual, cached, compiledCode⟩ := NamedCalls.compiled_at recipe.compiled.indexed selected
  obtain ⟨compilation⟩ := CallableIndexedNamedGeneration.of_accepted recipe.compiled.indexed compiledCode
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled
  obtain ⟨growth, covered⟩ := CallableCoercionPreparation.of_accepted prepared
  obtain ⟨available, resolved, _⟩ := covered row (growth.entries.subset member)
  let result : Prepared recipe.compiled row := ⟨index, named, _, code, compilation, available, selected, same, cached,
    by simpa only [programEq] using origins row member, resolved⟩
  exact ⟨result, ⟨⟨diagnostics, actual, rfl⟩⟩⟩

/-- A genuine Header alignment gives the assignment preparation equation
at the same full Header Source used by static profile extraction. -/
theorem assignments_at_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
    (receipt : Receipt prepared) {instantiation : DeclarationInstantiation}
    {values : SourceCoreCompatibleValues.Context}
    {header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header) :
    ∃ first, SourceCoreAssignmentFaultSites.prepare header.function.source first =
      .ok prepared.compilation.own.assignments := by
  have source : header.function.source = prepared.named.specialized.function.typedBody := by
    rw [aligned.function]
    rfl
  rw [source]
  exact assignments_prepared prepared receipt

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
