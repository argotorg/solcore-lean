import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FunctionCalls
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence

/-!
# Recursive named public results: roots

The meaning of a public root, its arguments, Source signature and coverage, and the bootstrap globals.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBootstrapGlobals
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootArguments
/-! Public root arguments are pure reads of the reversed native input prefix.
The proof copies arbitrary payloads, including closures, without changing their
captures or the store. Source attribution and input encoding remain separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootArguments
open Core Frontend ReadOnly

/-- A static ordered list of the exact native input slots. -/
inductive Slots (canonical : Environment) : List SourceCoreBasic.LoweredExpr → List Value → Prop where
  | nil : Slots canonical [] []
  | cons {type index value codes values}
      (found : canonical[index]? = some value) (rest : Slots canonical codes values) :
      Slots canonical (⟨type, LanguageResult.success (.var index)⟩ :: codes) (value :: values)

theorem Slots.evaluates {canonical : Environment} {codes : List SourceCoreBasic.LoweredExpr}
    {values : List Value} (slots : Slots canonical codes values)
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    (store : Store) :
    Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
      (.inRight .word (DataPatternValues.packValues values)) store := by
  induction slots generalizing actual ξ with
  | nil => exact .inRight .unit
  | @cons type index value codes values found rest ih =>
    have first : Evaluates actual store ((LanguageResult.success (.var index)).rename ξ)
        (.inRight .word value) store := .inRight (.var (agrees found))
    cases rest with
    | nil => exact first
    | @cons nextType nextIndex nextValue nextCodes nextValues nextFound remaining =>
      have second := ih (GenericExpressionMeaning.agree_prefix agrees value)
      rw [GenericExpressionMeaning.rename_prefix] at second
      simpa [SourceCoreCalls.packArguments, DataPatternValues.packValues, DataExpressionSequence.pair_rename]
        using LocalSequence.pair_success type (SourceCoreCalls.packArguments
          (⟨nextType, LanguageResult.success (.var nextIndex)⟩ :: nextCodes)).type first second

private theorem ordered_slots (types : List Ty) (values : List Value) (canonical : Environment)
    (total start : Nat) (lengths : types.length = values.length)
    (selected : ∀ {index value}, values[index]? = some value →
      canonical[total - 1 - (start + index)]? = some value) :
    Slots canonical (types.zipIdx.map fun (type, index) =>
      ⟨type, LanguageResult.success (.var (total - 1 - (start + index)))⟩) values := by
  induction types generalizing values start with
  | nil => cases values with
    | nil => exact .nil
    | cons => simp at lengths
  | cons type types ih =>
    cases values with
    | nil => simp at lengths
    | cons value values =>
      have tailLengths : types.length = values.length := Nat.succ.inj lengths
      have first : canonical[total - 1 - start]? = some value := by simpa using selected (index := 0) rfl
      have tailSelected : ∀ {index value}, values[index]? = some value →
          canonical[total - 1 - (start + 1 + index)]? = some value := by
        intro index value found
        simpa [Nat.add_assoc, Nat.add_comm 1] using selected (index := index + 1) found
      have remaining := ih values (start + 1) tailLengths tailSelected
      simpa only [List.zipIdx_cons', List.map_cons, List.map_map, Prod.map, Function.comp_def, id_eq, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using Slots.cons (type := type) first remaining

/-- The actual reversed prefix selects each original payload in source order.
The length condition concerns native slots and never identifies a source type. -/
theorem input_slots (types : List Ty) (values globals : Environment)
    (lengths : types.length = values.length) :
    Slots (values.reverse ++ globals) (types.zipIdx.map fun (type, index) =>
      ⟨type, LanguageResult.success (.var (types.length - 1 - index))⟩) values := by
  have selected : ∀ {index value}, values[index]? = some value →
      (values.reverse ++ globals)[types.length - 1 - (0 + index)]? = some value := by
    intro index value found
    have bound : index < values.length := (List.getElem?_eq_some_iff.mp found).1
    have backwards : values.reverse[types.length - 1 - index]? = some value := by
      rw [List.getElem?_reverse' (j := index) (by omega)]
      exact found
    have within : types.length - 1 - index < values.reverse.length := by
      simp only [List.length_reverse]; omega
    simpa only [Nat.zero_add, List.getElem?_append_left within] using backwards
  simpa only [Nat.zero_add] using ordered_slots types values (values.reverse ++ globals) types.length 0 lengths selected

/-- Every public argument bundle succeeds without changing any store cell. -/
theorem arguments_evaluate (types : List Ty) (values globals : Environment) (store : Store)
    (lengths : types.length = values.length) :
    Evaluates (values.reverse ++ globals) store
      (SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (types.length - 1 - index))⟩)).expression
      (.inRight .word (DataPatternValues.packValues values)) store := by
  have evaluated := (input_slots types values globals lengths).evaluates
    (ξ := Renaming.id) (actual := values.reverse ++ globals) (by intro index value found; exact found) store
  simpa only [Expr.rename_id] using evaluated


/-- Enough fuel evaluates only the argument reads and preserves the store. -/
theorem arguments_have_sufficient_fuel (types : List Ty) (values globals : Environment) (store : Store)
    (lengths : types.length = values.length) :
    ∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
      (.initial (SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (types.length - 1 - index))⟩)).expression
        (values.reverse ++ globals) store) = .done (.inRight .word (DataPatternValues.packValues values)) store :=
  evaluation_runStateful_complete_with_sufficient_fuel (arguments_evaluate types values globals store lengths)

/-- Original native completion has the same ordered payload and full store. -/
theorem completed_arguments (types : List Ty) (values globals : Environment) (store : Store)
    (lengths : types.length = values.length) {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial (SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (types.length - 1 - index))⟩)).expression
        (values.reverse ++ globals) store) = .done value finalStore) :
    value = .inRight .word (DataPatternValues.packValues values) ∧ finalStore = store :=
  evaluation_deterministic (runStateful_evaluation_sound completed) (arguments_evaluate types values globals store lengths)

/-- The encoder's native environment typing supplies the exact native arity.
It is used only for slot lengths, with no source identity inferred from it. -/
theorem typed_arguments_evaluate {definitions : DataEnvironment} {world : StoreTyping}
    {types : List Ty} {values : Environment} (globals : Environment) (store : Store)
    (typed : RuntimeEnvironmentHasTypes world values types definitions) :
    Evaluates (values.reverse ++ globals) store
      (SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (types.length - 1 - index))⟩)).expression
      (.inRight .word (DataPatternValues.packValues values)) store := by
  have lengths : types.length = values.length := by
    have same := congrArg List.length typed.type_tags
    simpa only [List.length_map] using same.symm
  exact arguments_evaluate types values globals store lengths

/-- Factory provenance supplies the actual call; the typed native prefix
closes its pure argument evaluation, retaining every payload and store cell. -/
theorem factory_call_arguments {compiled : SourceCoreUnifiedCompilation.Compiled}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    {root : SourceCoreIndexedSession.Root compiled}
    (issued : root.FactoryShape compiled entry) {world : StoreTyping} {values : Environment}
    (store : Store) (typed : RuntimeEnvironmentHasTypes world values root.types compiled.indexed.layouts.definitions) :
    ∃ (function : SourceCoreGeneralFunctions.Function) (index : Nat),
      function.signature.key = root.key ∧
      root.body = SourceCoreCalls.call function.signature (index + root.types.length)
        (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
          ⟨type, LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression Word.zero ∧
      Evaluates (values.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store
        (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
          ⟨type, LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression
        (.inRight .word (DataPatternValues.packValues values)) store := by
  obtain ⟨function, index, _, key, rootKey, _, _, _, _, _, body, _⟩ := issued
  exact ⟨function, index, key.trans rootKey.symm, body,
    typed_arguments_evaluate (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store typed⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootArguments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
/-! Actual public-root selection fixes the full named row and its physical slot.
Pure argument reads and the prefix environment agreement are internal. Source
arguments, real catalog authority, staging and static Match profiles remain
independent inputs; native tags never identify a source declaration. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts RecursiveGlobalInitializationMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root compiled}
  {header : Header compiled.indexed.ancestry values ambient.definitions program}

/-- Static provenance of the original first matching row, including its slot.
The chosen Header retains the separate source attribution and cached receipts. -/
def RootSelection (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
    (root : SourceCoreIndexedSession.Root compiled)
    (header : Header compiled.indexed.ancestry values ambient.definitions program) : Prop :=
  header ∈ headers ∧ ∃ entry, entry ∈ compiled.indexed.entries ∧ root.FactoryShape compiled entry ∧
    compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = entry.key)) = some (header.named, header.slot)

/-- Full row equality follows from the original selected slot, even when keys
repeat. Complete inventory coverage does not replace first-match provenance. -/
theorem selection_of_issued (issued : root.Issued compiled) (complete : Complete headers) :
    ∃ header, RootSelection headers root header := by
  obtain ⟨entry, entryMember, shape⟩ := issued
  obtain ⟨named, index, found, rest⟩ := shape
  have row : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  obtain ⟨header, member, slot, _⟩ := complete index named.signature
    (CallableIndexedPreparedInventories.cached_global_at compiled row)
  have selected : compiled.indexed.base.functions[index]? = some header.named := slot ▸ header.selected
  have same : header.named = named := Option.some.inj (selected.symm.trans row)
  refine ⟨header, member, entry, entryMember, ⟨named, index, found, rest⟩, ?_⟩
  simpa only [slot, same] using found

/-- Accepted preparation supplies the actual indexed entry and first-match
receipt, retaining the caller's independent complete source inventory. -/
theorem selection_of_recipe {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {root : SourceCoreIndexedSession.Root recipe.compiled} (member : root ∈ recipe.roots)
    {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    (complete : Complete headers) : ∃ header, RootSelection headers root header :=
  selection_of_issued (SourceCoreIndexedSession.Recipe.prepare_roots accepted member) complete

namespace RootSelection

theorem member (selected : RootSelection headers root header) : header ∈ headers := selected.1

/-- The original factory equation is transported by equality of both complete
selected fields. Source input types are deliberately not inferred here. -/
theorem shape (selected : RootSelection headers root header) :
    root.types = header.named.inputs.map Prod.snd ∧
    root.body = SourceCoreCalls.call header.named.signature (header.slot + root.types.length)
      (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression Word.zero := by
  obtain ⟨_, entry, _, shape, found⟩ := selected
  obtain ⟨named, index, first, _, _, _, types, _, _, _, body, _⟩ := shape
  have same := Prod.mk.inj (Option.some.inj (found.symm.trans first))
  obtain ⟨rfl, rfl⟩ := same
  exact ⟨types, body⟩

/-- Only arity is needed by native argument reads. Raw binder identity fixes
that arity before the independent payload representation supplies its length. -/
theorem argument_length (selected : RootSelection headers root header)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {payloads : List Value}
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads) : root.types.length = payloads.length := by
  have binders := congrArg List.length (header.parameters.symm.trans header.agreement.parameters)
  simp only [List.length_map] at binders
  rw [selected.shape.1, List.length_map, ← binders]
  exact represented.length.2

/-- Actual argument code copies arbitrary payloads and preserves the full
store. Neither source meaning nor source parameter types follow from copying. -/
theorem arguments_evaluate (selected : RootSelection headers root header)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {payloads : List Value}
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world header.bindings arguments payloads) (store : Store) :
    Evaluates (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store
      (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression
      (.inRight .word (DataPatternValues.packValues payloads)) store :=
  RecursiveNamedPublicRootArguments.arguments_evaluate _ _ _ _ (selected.argument_length represented)

end RootSelection

/-- Prefix insertion preserves each original global value, including closure
captures. It does not construct or rewrite catalog authority. -/
theorem globals_agree (payloads globals : Environment) :
    EnvironmentsAgree (shift payloads.length) globals (payloads.reverse ++ globals) := by
  intro index value found
  change (payloads.reverse ++ globals)[index + payloads.length]? = some value
  rw [List.getElem?_append_right (by simp only [List.length_reverse]; omega)]
  simpa only [List.length_reverse, Nat.add_sub_cancel] using found

section Evidence
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable (authenticated runtime : Bool) {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForModeWith authenticated runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed))
  {header : Header compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root compiled} (selected : RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps in
/-- The real global reference and capture supply the emitted call's read.
Source execution supplies the body; original native completeness supplies a
budget for the complete call, including argument packing and dispatch. -/
theorem has_sufficient_fuel_with_evidence
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body
          (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) = .done value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)) := by
  have result := RecursiveNamedProgramCallMeaning.emitted_call_has_sufficient_fuel_with_evidence (reason := Word.zero) authenticated runtime functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected.member represented heaps
    (globals_agree payloads _) (selected.arguments_evaluate represented store) executed
  simpa only [selected.shape.2, selected.argument_length represented, shift, List.length_nil, Nat.zero_add] using result

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem completed_reflects_program_with_evidence
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial root.body
          (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)) := by
  apply RecursiveNamedProgramCallMeaning.completed_call_reflects_program_with_evidence (reason := Word.zero) authenticated runtime functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected.member represented heaps
    admitted heapTyped argumentsTyped (globals_agree payloads _) (selected.arguments_evaluate represented store)
  simpa only [selected.shape.2, selected.argument_length represented, shift, List.length_nil, Nat.zero_add] using completed

end Evidence

section Common
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable (runtime : Bool) {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForMode runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed))
  {header : Header compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root compiled} (selected : RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps in
/-- The real global reference and capture supply the emitted call's read.
Source execution supplies the body; original native completeness supplies a
budget for the complete call, including argument packing and dispatch. -/
theorem has_sufficient_fuel_with
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body
          (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) = .done value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)) := by
  exact has_sufficient_fuel_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem completed_reflects_program_with
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial root.body
          (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)) := by
  exact completed_reflects_program_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps admitted heapTyped argumentsTyped completed

end Common

section Meaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed))
  {header : Header compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root compiled} (selected : RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps in
/-- The real global reference and capture supply the emitted call's read.
Source execution supplies the body; original native completeness supplies a
budget for the complete call, including argument packing and dispatch. -/
theorem has_sufficient_fuel
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body
          (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) = .done value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)) := by
  exact has_sufficient_fuel_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller selected represented heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem completed_reflects_program
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial root.body
          (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)) := by
  exact completed_reflects_program_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller selected represented heaps admitted heapTyped argumentsTyped completed

end Meaning

/-- Fresh completed initialization supplies an Entry in exactly the public
native globals. All original source inventory and initialization conditions
remain explicit; arbitrary existing sessions are outside this helper. -/
theorem fresh_entry (compiled : SourceCoreUnifiedCompilation.Compiled)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
    (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
    (ledger : Ledger headers compiled.indexed.secondPass.closures)
    (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
    (locals : ∀ header, header ∈ headers → header.function.context.locals = [])
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧ ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩ finalStore ∧
      Nonempty (Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)) := by
  simpa only [RecursiveNamedPublicBootstrapGlobals.environment_eq] using
    RecursiveNamedCatalogPreparedInitialization.completed_entry compiled headers ledger sizes locals
      accepted definitions functions registry completed

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootCoverage
/-! Public Source selection covers actual public entries only. Cached method
rows remain in the physical inventory and need no ordinary Source Header. The
original first-match equation still determines the selected complete row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootCoverage
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts RecursiveNamedPublicRootMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}

def Coverage (headers : Inventory compiled.indexed.ancestry values ambient.definitions program) : Prop :=
  ∀ entry, entry ∈ compiled.indexed.entries → ∀ named slot,
    compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = entry.key)) = some (named, slot) →
    ∃ header, header ∈ headers ∧ header.slot = slot

theorem Coverage.of_complete (complete : Complete headers) : Coverage headers := by
  intro _entry _member named slot found
  have selected : compiled.indexed.base.functions[slot]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  obtain ⟨header, member, slot, _signature⟩ := complete slot named.signature
    (CallableIndexedPreparedInventories.cached_global_at compiled selected)
  exact ⟨header, member, slot⟩

theorem selection_of_issued {root : SourceCoreIndexedSession.Root compiled}
    (issued : root.Issued compiled) (coverage : Coverage headers) :
    ∃ header, RootSelection headers root header := by
  obtain ⟨entry, entryMember, shape⟩ := issued
  obtain ⟨named, index, found, rest⟩ := shape
  have row : compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  obtain ⟨header, member, slot⟩ := coverage entry entryMember named index found
  have selected : compiled.indexed.base.functions[index]? = some header.named := slot ▸ header.selected
  have same : header.named = named := Option.some.inj (selected.symm.trans row)
  refine ⟨header, member, entry, entryMember, ⟨named, index, found, rest⟩, ?_⟩
  simpa only [slot, same] using found

theorem selection_of_recipe {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {root : SourceCoreIndexedSession.Root recipe.compiled} (member : root ∈ recipe.roots)
    {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    (coverage : Coverage headers) : ∃ header, RootSelection headers root header :=
  selection_of_issued (SourceCoreIndexedSession.Recipe.prepare_roots accepted member) coverage

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootCoverage
end
