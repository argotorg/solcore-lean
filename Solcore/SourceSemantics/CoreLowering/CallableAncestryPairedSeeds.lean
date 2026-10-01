import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProgress
import Solcore.SourceSemantics.CoreLowering.CallEntryCertificates

/-! Named seeding succeeds from actual codebook-origin receipts. This closes
the worklist's remaining seed premise without assuming successful runtime
execution or recovering source provenance from native function types. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedSeeds
open Frontend SourceInference TypeSystem CallableAncestryPairedLookup
open CallableAncestryPairedExpansion CallableAncestryPairedWorklist
abbrev State := SourceCoreCallableAncestryReadRecipes.State

private theorem named_exact {plan : SourceSpecializationWorklist.Plan} {owner : SourceSpecialization.SpecializationKey}
    {contract : SourceCoreStageContracts.Contract}
    (accepted : SourceCoreStageContracts.Contract.named plan owner = .ok contract) :
    ∃ caller, SourceCompilationPlan.exactSpecialization plan owner = .ok caller := by
  unfold SourceCoreStageContracts.Contract.named at accepted
  obtain ⟨sidecar, prepared, _⟩ := bind_ok accepted
  unfold SourceCoreStageContracts.prepareSidecar at prepared
  cases selected : SourceCompilationPlan.exactSpecialization plan owner with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at prepared
  | ok caller => exact ⟨caller, rfl⟩

private theorem origin_named {plan : SourceSpecializationWorklist.Plan} {owner : SourceSpecialization.SpecializationKey}
    {count : Nat} {contract : Option SourceCoreStageContracts.Contract}
    (receipt : CallEntryCertificates.OriginContract plan (.named owner) count contract) :
    ∃ original, SourceCoreStageContracts.Contract.named plan owner = .ok original := by
  cases receipt with
  | named prepared => exact ⟨_, prepared⟩

theorem named_total {checked : Checked} {base : Base checked} {inputs : Inputs base}
    (authentic : CallEntryCertificates.AllAuthenticated base.plan inputs.callable.table.entries)
    {entry : SourceCoreStageCodebook.Entry} (member : entry ∈ inputs.callable.table.entries)
    {owner : SourceSpecialization.SpecializationKey} (origin : entry.origin = .named owner) :
    ∃ state, SourceCoreCallableAncestryPairedPreparation.named? inputs entry.id = some state := by
  have receipt := authentic entry member
  unfold CallEntryCertificates.Authenticated at receipt
  rw [origin] at receipt
  obtain ⟨original, prepared⟩ := origin_named receipt
  obtain ⟨caller, selected⟩ := named_exact prepared
  refine ⟨⟨⟨owner, [], caller.function.typedBody⟩, []⟩, ?_⟩
  simp only [SourceCoreCallableAncestryPairedPreparation.named?, SourceCoreCallableAncestryPreparation.named?,
      CallableAncestryPairedValidation.stage_entry_self inputs.callable.table member, origin, selected,
      Except.toOption, bind, Option.bind, pure, Option.map_some]

private theorem forIn_total {α β ε : Type} (items : List α) (step : α → β → Except ε (ForInStep β))
    (invariant : β → Prop) (initial : β) (valid : invariant initial)
    (next : ∀ item ∈ items, ∀ state, invariant state →
      ∃ result, step item state = .ok (.yield result) ∧ invariant result) :
    ∃ final, forIn items initial step = .ok final ∧ invariant final := by
  induction items generalizing initial with
  | nil => exact ⟨initial, rfl, valid⟩
  | cons head tail ih =>
    obtain ⟨after, executed, maintained⟩ := next head (by simp) initial valid
    obtain ⟨final, finished, preserved⟩ := ih after maintained (fun item member => next item (by simp [member]))
    refine ⟨final, ?_, preserved⟩
    simpa only [List.forIn_cons, executed, bind, Except.bind] using finished

theorem seed_total {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (authentic : CallEntryCertificates.AllAuthenticated base.plan inputs.callable.table.entries) :
    ∃ initial, SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial := by
  let step : SourceCoreStageCodebook.Entry → Table → Except SourceCoreCallableAncestryPairedPreparation.Error (ForInStep Table) :=
    fun entry table => do
      match entry.origin with
      | .named _ =>
        let state ← match SourceCoreCallableAncestryPairedPreparation.named? inputs entry.id with
          | none => throw (.invalidNamed entry.id) | some state => pure state
        let (destination, states) ← SourceCoreCallableAncestryPairedPreparation.intern table.states state
        pure (.yield {table with states, named := table.named ++ [⟨entry.id, destination⟩]})
      | _ => pure (.yield table)
  obtain ⟨initial, completed, _⟩ := forIn_total inputs.callable.table.entries step
    (fun table => StatesValid inputs table.states) ⟨[], [], [], []⟩ ⟨by simp, by simp⟩ (by
      intro entry member table previous
      dsimp only [step]
      cases origin : entry.origin with
      | named owner =>
        obtain ⟨state, selected⟩ := named_total authentic member origin
        obtain ⟨destination, states, interned, maintained, _, _⟩ := intern_total previous ⟨.named entry.id, .named selected⟩
        refine ⟨{table with states, named := table.named ++ [⟨entry.id, destination⟩]}, ?_, maintained⟩
        simp only [selected, interned, pure, Except.pure, bind, Except.bind]
      | lambda owner id active => exact ⟨table, rfl, previous⟩
      | builtin builtin => exact ⟨table, rfl, previous⟩)
  refine ⟨initial, ?_⟩
  change (forIn inputs.callable.table.entries ⟨[], [], [], []⟩ step >>= fun result => Except.ok result) = .ok initial
  simp only [completed, bind, Except.bind]

/-- A codebook prepared for the actual executable plan supplies every named
seed. All later worklist phases are total with the computed finite bound. -/
theorem completion_of_codebook {checked : Checked} {base : Base checked} (inputs : Inputs base)
    {projectType : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (prepared : SourceCoreStageCodebook.prepareWithProjection base.sourceProgram base.plan projectType limits firstId = .ok inputs.callable.table) :
    ∃ initial final, SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial ∧
      SourceCoreCallableAncestryPairedPreparation.saturate inputs
        (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial = .ok final ∧
      SourceCoreCallableAncestryPairedPreparation.valid inputs final = true ∧
      ∃ recipes, final.views.attach.mapM (fun edge =>
        SourceCoreCallableAncestryPairedPreparation.prepareRecipe inputs final edge.val edge.property) = .ok recipes := by
  obtain ⟨initial, seeded⟩ := seed_total inputs (CallEntryCertificates.prepareWithProjection_authenticates prepared)
  obtain ⟨final, completed, validated, recipes⟩ := CallableAncestryPairedProgress.seeded_completion_total inputs seeded
  exact ⟨initial, final, seeded, completed, validated, recipes⟩


private theorem mapError_ok {α ε δ : Type} {result : Except ε α} {value : α} {f : ε → δ}
    (accepted : result.mapError f = .ok value) : result = .ok value := by
  cases result with
  | error => cases accepted
  | ok selected => cases accepted; rfl

/-- Recover actual codebook provenance from the compatible compiler factory.
The native table's shape alone is not used as a source-ownership receipt. -/
theorem factory_authenticated {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    (inputs : Inputs base) : CallEntryCertificates.AllAuthenticated base.plan inputs.callable.table.entries := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨actualPlan, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    have absent := inputs.callableSelected
    cases absent
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, tablePrepared, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      have same : ({table, diagnostics := callableDiagnostics} : SourceCoreGeneralFunctions.CallableContext) = inputs.callable :=
        Option.some.inj inputs.callableSelected
      have authenticated := CallEntryCertificates.prepareWithProjection_authenticates (mapError_ok tablePrepared)
      simpa only [← same] using authenticated
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      have absent := inputs.callableSelected
      cases absent


/-- Once the compatible compiler and input metadata preparation succeed, the
paired cache factory cannot fail at named seeding, queue saturation, closure
validation, or per-edge recipe preparation. Input-metadata preparation and
native runtime-frame coverage remain separate obligations. -/
theorem preparation_total {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked}
    (compiled : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    {inputs : Inputs base}
    (inputsPrepared : SourceCoreCallableAncestryPreparation.prepareInputs base = .ok inputs) :
    ∃ prepared, SourceCoreCallableAncestryPairedPreparation.prepare base = .ok prepared := by
  obtain ⟨initial, seeded⟩ := seed_total inputs (factory_authenticated compiled inputs)
  obtain ⟨final, completed, validated, recipes, recipesPrepared⟩ :=
    CallableAncestryPairedProgress.seeded_completion_total inputs seeded
  unfold SourceCoreCallableAncestryPairedPreparation.prepare
  simp only [inputsPrepared, Except.mapError, bind, Except.bind]
  split
  · next error impossible => simp [seeded] at impossible
  · next actualInitial selected =>
    have same := Except.ok.inj (selected.symm.trans seeded)
    subst actualInitial
    split
    · next error impossible => simp [completed] at impossible
    · next actualFinal selected =>
      have same := Except.ok.inj (selected.symm.trans completed)
      subst actualFinal
      split
      · split
        · next error impossible => simp [recipesPrepared] at impossible
        · exact ⟨_, rfl⟩
      · next impossible => exact False.elim (impossible validated)

end Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedSeeds

