import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization

/-! Fresh native initialization agrees with the public template environment
and its complete generated global slots. Full installed code and captured Unit
prefixes come from the actual owned cache and original closed bootstrap trace.
The native frame is at zero and globals start at one; this proof makes no claim
about a nonempty source prefix, source body meaning, or decoder-derived history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBootstrapGlobals
open Core Frontend SourceInference
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

theorem environment_eq (compiled : SourceCoreUnifiedCompilation.Compiled) :
    RecursiveNamedCatalogPreparedInitialization.environment compiled =
      SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed := by
  have leftLength : (RecursiveNamedCatalogPreparedInitialization.environment compiled).length =
      compiled.indexed.base.globals.length + 1 := by
    simp [RecursiveNamedCatalogPreparedInitialization.environment, initialEnvironment, reserved_environment]
  have rightLength : (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed).length =
      compiled.indexed.base.globals.length + 1 := by
    simp [SourceCoreCallableIndexedTemplates.globalEnvironment, SourceCoreLambdaTemplates.freshGlobals]
  apply List.ext_getElem?
  intro index
  by_cases inside : index < compiled.indexed.base.globals.length
  · have found := List.getElem?_eq_getElem inside
    have left := RecursiveNamedCatalogInitialization.global_reference compiled.indexed.base.globals
      compiled.indexed.ancestry.layout.frame found
    have location : 1 + (compiled.indexed.base.globals.length - 1 - index) =
        1 + compiled.indexed.base.globals.length - 1 - index := by omega
    change (initialEnvironment _ _)[index]? = _
    rw [left]
    simp only [SourceCoreCallableIndexedTemplates.globalEnvironment, SourceCoreLambdaTemplates.freshGlobals]
    rw [List.getElem?_append_left (by simpa using inside)]
    simp only [List.getElem?_map, List.getElem?_zipIdx, found, Option.map_some,
      Nat.zero_add, RecursiveNamedCatalogInitialization.location, location]
  · by_cases last : index = compiled.indexed.base.globals.length
    · subst index
      change (initialEnvironment _ _)[_]? = _
      rw [RecursiveNamedCatalogInitialization.frame_reference]
      simp [SourceCoreCallableIndexedTemplates.globalEnvironment, SourceCoreLambdaTemplates.freshGlobals]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapM_length {α β ε : Type} {action : α → Except ε β}
    {inputs : List α} {outputs : List β} (accepted : inputs.mapM action = .ok outputs) :
    outputs.length = inputs.length := by
  induction inputs generalizing outputs with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted; subst outputs; rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, _, accepted⟩ := bind_ok accepted
    obtain ⟨rest, acceptedRest, accepted⟩ := bind_ok accepted
    cases accepted
    simp only [List.length_cons, ih acceptedRest]

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

private theorem type_beq (left right : Core.Ty) : (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Core.instBEqTy.beq, Core.instBEqDataTypeId.beq]
  rename_i left right
  cases left; cases right; simp_all

/-- Invert the actual generator, preserving its complete closure and physical
slot. No code or capture is reconstructed from a native type tag. -/
theorem generated_slot {signatures : List (Ty × Ty)} {installed : List Expr}
    {environment : Environment} {base : Nat} {slots : List (Nat × Value)}
    (generated : SourceCoreCallableNativeSlots.expectedGlobals signatures installed environment base = .ok slots)
    {location : Nat} {value : Value} (member : (location, value) ∈ slots) :
    ∃ index parameter result body,
      signatures[index]? = some (parameter, result) ∧
      installed[index]? = some (.lambda parameter (LanguageResult.resultType result) body) ∧
      location = base + signatures.length - 1 - index ∧
      value = .inRight .unit (.closure parameter (LanguageResult.resultType result) body
        (List.replicate index .unit ++ environment)) := by
  unfold SourceCoreCallableNativeSlots.expectedGlobals at generated
  split at generated
  · cases generated
  · obtain ⟨⟨⟨parameter, result⟩, index⟩, selected, emitted⟩ := mapM_member generated member
    have signature := List.mk_mem_zipIdx_iff_getElem?.mp selected
    cases found : installed[index]? with
    | none => simp [found, bind, Except.bind, throw] at emitted
    | some code =>
      simp only [found, pure, Except.pure, bind, Except.bind] at emitted
      cases code <;> try cases emitted
      rename_i actualParameter actualResult body
      by_cases header : (actualParameter != parameter || actualResult != LanguageResult.resultType result) = true
      · simp [header, throw, throwThe, MonadExceptOf.throw] at emitted
      · have checks : (actualParameter == parameter) = true ∧
            (actualResult == LanguageResult.resultType result) = true := by
          simpa [bne] using header
        have sameParameter := (type_beq _ _).mp checks.1
        have sameResult := (type_beq _ _).mp checks.2
        simp [header] at emitted
        obtain ⟨locationEq, valueEq⟩ := emitted
        exact ⟨index, parameter, result, body, signature,
          by simp only [sameParameter, sameResult] at found; exact found,
          locationEq.symm, valueEq.symm⟩

theorem native_globals_length (compiled : SourceCoreUnifiedCompilation.Compiled)
    (cache : SourceCoreCallableIndexedTemplates.Cache compiled.indexed) :
    cache.nativeGlobals.length = compiled.indexed.base.globals.length := by
  have generated := cache.nativeGlobalsGenerated
  change SourceCoreCallableNativeSlots.expectedGlobals
    (compiled.indexed.base.globals.map (fun signature => (signature.parameterType, signature.resultType)))
    (compiled.indexed.secondPass.closures.zipIdx.map (fun (code, index) => SourceCoreLambdaTemplates.installedTemplate index code))
    (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) 1 = .ok cache.nativeGlobals at generated
  unfold SourceCoreCallableNativeSlots.expectedGlobals at generated
  split at generated
  · cases generated
  · simpa using mapM_length generated

/-- Every original cached row occurs at its physical global slot, with the
same renamed body and actual captured Unit prefix followed by public globals. -/
theorem cached_slot (compiled : SourceCoreUnifiedCompilation.Compiled)
    {slot : Nat} {code : Expr} (cached : compiled.indexed.secondPass.closures[slot]? = some code) :
    ∃ row, (RecursiveNamedCachedRows.rows compiled)[slot]? = some row ∧
      code = row.expression ∧
      (RecursiveNamedCatalogPreparedInitialization.store compiled)[RecursiveNamedCatalogInitialization.location
        compiled.indexed.base.globals slot]? = some (.inRight .unit
        (installedValue (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) slot row)) := by
  have bound := (List.getElem?_eq_some_iff.mp cached).1
  have rowBound : slot < (RecursiveNamedCachedRows.rows compiled).length := by
    simpa only [RecursiveNamedCachedRows.rows, List.length_map] using bound
  let row := (RecursiveNamedCachedRows.rows compiled)[slot]
  have found : (RecursiveNamedCachedRows.rows compiled)[slot]? = some row := List.getElem?_eq_getElem rowBound
  have same : code = row.expression := by
    rw [RecursiveNamedCachedRows.exact_cache, List.getElem?_map, found] at cached
    exact (Option.some.inj cached).symm
  have read := RecursiveNamedCatalogInitialization.closure_read compiled.indexed.base.globals
    (RecursiveNamedCachedRows.rows compiled) compiled.indexed.ancestry.layout.frame
    (RecursiveNamedCachedRows.ordered compiled) found
  refine ⟨row, found, same, ?_⟩
  change (initialStore _ _ _).read? _ = _
  rw [read, ← environment_eq]
  rfl

theorem native_slot (compiled : SourceCoreUnifiedCompilation.Compiled)
    (cache : SourceCoreCallableIndexedTemplates.Cache compiled.indexed)
    {location : Nat} {value : Value} (member : (location, value) ∈ cache.nativeGlobals) :
    (RecursiveNamedCatalogPreparedInitialization.store compiled)[location]? = some value := by
  have generated := cache.nativeGlobalsGenerated
  change SourceCoreCallableNativeSlots.expectedGlobals
    (compiled.indexed.base.globals.map (fun signature => (signature.parameterType, signature.resultType)))
    (compiled.indexed.secondPass.closures.zipIdx.map (fun (code, index) => SourceCoreLambdaTemplates.installedTemplate index code))
    (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) 1 = .ok cache.nativeGlobals at generated
  obtain ⟨index, parameter, result, body, signature, installed, locationEq, valueEq⟩ := generated_slot generated member
  have inside : index < compiled.indexed.base.globals.length := by
    simpa using (List.getElem?_eq_some_iff.mp signature).1
  have rowInside : index < (RecursiveNamedCachedRows.rows compiled).length := by
    rwa [RecursiveNamedCachedRows.rows_length]
  let row := (RecursiveNamedCachedRows.rows compiled)[index]
  have rowFound : (RecursiveNamedCachedRows.rows compiled)[index]? = some row := List.getElem?_eq_getElem rowInside
  have cached : compiled.indexed.secondPass.closures[index]? = some row.expression := by
    rw [RecursiveNamedCachedRows.exact_cache, List.getElem?_map, rowFound]
    rfl
  have actualInstalled :
      (compiled.indexed.secondPass.closures.zipIdx.map (fun (code, index) => SourceCoreLambdaTemplates.installedTemplate index code))[index]? =
        some (row.expression.rename (shift index)) := by
    simp only [List.getElem?_map, List.getElem?_zipIdx, cached, Option.map_some, Nat.zero_add,
      installed_template, shifted]
  have codeEq := Option.some.inj (actualInstalled.symm.trans installed)
  have parts := Expr.lambda.inj codeEq
  change row.parameter = parameter ∧ row.result = LanguageResult.resultType result ∧
    row.body.rename (shift index).lift = body at parts
  have read := RecursiveNamedCatalogInitialization.closure_read compiled.indexed.base.globals
    (RecursiveNamedCachedRows.rows compiled) compiled.indexed.ancestry.layout.frame
    (RecursiveNamedCachedRows.ordered compiled) rowFound
  have sameLocation : location = RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals index := by
    simp only [List.length_map] at locationEq
    simp only [RecursiveNamedCatalogInitialization.location]
    omega
  rw [sameLocation]
  change (initialStore _ _ _).read? _ = some value
  rw [read, valueEq]
  simp only [installedValue, ← environment_eq, RecursiveNamedCatalogPreparedInitialization.environment,
    parts.1, parts.2.1, parts.2.2]

theorem globals_checked (compiled : SourceCoreUnifiedCompilation.Compiled)
    (cache : SourceCoreCallableIndexedTemplates.Cache compiled.indexed) :
    ∃ globals : SourceCoreCallableIndexedTemplates.Globals compiled.indexed
        (RecursiveNamedCatalogPreparedInitialization.store compiled),
      SourceCoreCallableNativeSlots.checkPreparedGlobals cache.nativeGlobals cache.nativeGlobalsGenerated
        (RecursiveNamedCatalogPreparedInitialization.store compiled) = .ok globals := by
  have exactSlots : cache.nativeGlobals.all (fun (location, value) =>
      decide ((RecursiveNamedCatalogPreparedInitialization.store compiled)[location]? = some value)) = true := by
    apply List.all_eq_true.mpr
    intro slot member
    exact decide_eq_true (native_slot compiled cache member)
  unfold SourceCoreCallableNativeSlots.checkPreparedGlobals
  simp only [exactSlots, ↓reduceDIte, pure, Except.pure]
  exact ⟨_, rfl⟩

theorem check_isOk (compiled : SourceCoreUnifiedCompilation.Compiled)
    (cache : SourceCoreCallableIndexedTemplates.Cache compiled.indexed) :
    (SourceCoreCallableNativeSlots.checkPreparedGlobals cache.nativeGlobals cache.nativeGlobalsGenerated
      (RecursiveNamedCatalogPreparedInitialization.store compiled)).isOk = true := by
  obtain ⟨_, checked⟩ := globals_checked compiled cache
  rw [checked]
  rfl

/-- Any actual completed fresh recipe exposes these same generated slots. -/
theorem completed_globals {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧ ∃ globals : SourceCoreCallableIndexedTemplates.Globals recipe.compiled.indexed finalStore,
      SourceCoreCallableNativeSlots.checkPreparedGlobals recipe.templates.nativeGlobals recipe.templates.nativeGlobalsGenerated
        finalStore = .ok globals := by
  obtain ⟨valueEq, storeEq⟩ := RecursiveNamedCatalogPreparedInitialization.completed_store accepted completed
  have same := SourceCoreIndexedSession.Recipe.prepare_compiled accepted
  subst compiled
  rw [storeEq]
  exact ⟨valueEq, globals_checked recipe.compiled recipe.templates⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBootstrapGlobals
