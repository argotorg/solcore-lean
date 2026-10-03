import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning

/-! The actual indexed-entry factory selects the same complete first row as
the public root factory. Its raw source binders and result are transported to
the independent source Header without identifying declarations by native tags. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedCatalog RecursiveNamedPublicRootMeaning

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapM_member {α β ε : Type} {action : α → Except ε β}
    {inputs : List α} {outputs : List β} {output : β}
    (accepted : inputs.mapM action = .ok outputs) (member : output ∈ outputs) :
    ∃ input, input ∈ inputs ∧ action input = .ok output := by
  induction inputs generalizing outputs with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted; subst outputs; cases member
  | cons first rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨head, headEq, accepted⟩ := bind_ok accepted
    obtain ⟨tail, tailEq, accepted⟩ := bind_ok accepted
    cases accepted
    rcases List.mem_cons.mp member with same | member
    · subst output; exact ⟨first, .head _, headEq⟩
    · obtain ⟨input, found, selected⟩ := ih tailEq member
      exact ⟨input, .tail _ found, selected⟩

/-- Every accepted indexed entry retains the raw binders and source result of
the actual first matching complete function row. Duplicate keys are allowed. -/
theorem entry_of_prepare {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked} {fuel : Nat}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    (accepted : SourceCoreCallableIndexedPrograms.prepare base fuel = .ok prepared)
    {entry : SourceCoreCallableIndexedPrograms.Entry prepared.layouts} (member : entry ∈ prepared.entries) :
    ∃ named, prepared.base.functions.find? (fun named => decide (named.signature.key = entry.key)) = some named ∧
      entry.inputs = named.inputs.map Prod.fst ∧
      entry.sourceResultType = named.specialized.function.inferredBodyType := by
  unfold SourceCoreCallableIndexedPrograms.prepare at accepted
  dsimp only at accepted
  split at accepted
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
  · rename_i ancestry ancestryPrepared
    try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
    split at accepted
    · simp [throw, throwThe, MonadExceptOf.throw] at accepted
    · rename_i contexts contextsPrepared
      try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
      split at accepted
      · simp [throw, throwThe, MonadExceptOf.throw] at accepted
      · rename_i discovery discoveryPrepared
        try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
        obtain ⟨firstPass, _, accepted⟩ := bind_ok accepted
        try dsimp only at accepted
        split at accepted
        · simp [throw, throwThe, MonadExceptOf.throw] at accepted
        · rename_i discovered scanned
          try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
          split at accepted
          · simp [throw, throwThe, MonadExceptOf.throw] at accepted
          · rename_i layouts layoutsPrepared
            try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
            obtain ⟨secondPass, _, accepted⟩ := bind_ok accepted
            obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
            obtain ⟨entries, entriesCompiled, accepted⟩ := bind_ok accepted
            cases accepted
            obtain ⟨key, _, emitted⟩ := mapM_member entriesCompiled member
            cases found : base.functions.find? (fun named => decide (named.signature.key = key)) with
            | none => simp [found, throw, throwThe, MonadExceptOf.throw] at emitted
            | some named =>
              simp only [found] at emitted
              obtain ⟨body, _, emitted⟩ := bind_ok emitted
              obtain ⟨native, _, emitted⟩ := bind_ok emitted
              cases emitted
              exact ⟨named, found, rfl, rfl⟩

/-- Forgetting the index preserves the same first-find decision, rather than
merely membership of some row with the same key. -/
theorem first_row {α : Type} {rows : List α} {predicate : α → Bool} {row : α} {slot : Nat}
    (selected : rows.zipIdx.find? (fun item => predicate item.1) = some (row, slot)) :
    rows.find? predicate = some row := by
  have equation := List.find?_map (p := predicate) (f := Prod.fst) (l := rows.zipIdx)
  rw [List.zipIdx_map_fst] at equation
  simpa only [Function.comp_def, selected, Option.map_some] using equation

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root compiled}
  {header : Header compiled.indexed.ancestry values ambient.definitions program}

/-- The compiled receipt links both actual factories before raw source types
are transported through Header's independent full parameter agreement. -/
theorem inputs_and_result (selected : RootSelection headers root header) :
    root.inputs = header.bindings.map (fun binding => binding.1.scheme.body) ∧
    root.result = header.function.resultType := by
  obtain ⟨_, entry, member, shape, found⟩ := selected
  obtain ⟨named, selectedEntry, inputs, result⟩ := entry_of_prepare compiled.indexedPrepared member
  have same : named = header.named := Option.some.inj (selectedEntry.symm.trans (first_row found))
  subst named
  obtain ⟨_, _, _, _, _, rawInputs, _, rawResult, _⟩ := shape
  refine ⟨?_, rawResult.trans (result.trans header.agreement.result.symm)⟩
  rw [rawInputs, inputs, ← header.agreement.parameters, header.parameters]
  simp only [List.map_map]
  rfl

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature
