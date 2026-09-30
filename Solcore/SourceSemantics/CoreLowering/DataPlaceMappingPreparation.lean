import Solcore.Frontend.SourceCoreDataPlaces
import Solcore.SourceSemantics.CoreLowering.DataDefaults

/-! Receipts from the actual mutable preparation loop. Every emitted mapping
step retains its accepted comparator/default preparation and its ordered key
position. No helper semantics or replacement compiler is assumed here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPreparation
open Core Frontend SourceInference SourceCoreDataPlaces

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]

private theorem mapError_ok {α ε δ : Type} {first : Except ε α} {convert : ε → δ} {value : α}
    (accepted : first.mapError convert = .ok value) : first = .ok value := by
  cases first <;> cases accepted
  rfl

theorem comparison_sourceType {checked : SourceCoreDataCatalog.Checked} {fuel : Nat} {source : TypeSystem.Ty}
    {prepared : SourceCoreDataEquality.Prepared checked}
    (accepted : SourceCoreDataEquality.prepare fuel checked source = .ok prepared) : prepared.sourceType = source := by
  unfold SourceCoreDataEquality.prepare at accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  dsimp only at accepted
  split at accepted <;> cases accepted
  rfl

theorem default_sourceType {checked : SourceCoreDataCatalog.Checked} {fuel : Nat} {source : TypeSystem.Ty}
    {prepared : SourceCoreDefaultValue.Prepared checked}
    (accepted : SourceCoreDefaultValue.prepare fuel checked source = .ok prepared) : prepared.sourceType = source := by
  unfold SourceCoreDefaultValue.prepare at accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  dsimp only at accepted
  split at accepted <;> cases accepted
  rfl

inductive Steps (checked : SourceCoreDataCatalog.Checked) (fuel : Nat) (missing : TypeSystem.Ty → Word) :
    Nat → List Step → List PreparedStep → List (ExpressionId × Ty) → Prop where
  | nil (count : Nat) : Steps checked fuel missing count [] [] []
  | member {count : Nat} {id : DataTypeId} {index : Nat} {branches : List MemberBranch} {field : Ty}
      {source : List Step} {target : List PreparedStep} {keys : List (ExpressionId × Ty)}
      (tail : Steps checked fuel missing count source target keys) :
      Steps checked fuel missing count (.member id index branches field :: source)
        (.member id index branches field :: target) keys
  | index {count : Nat} {layout : Core.OrderedMapping.Layout} {key : ExpressionId} {sourceValue : TypeSystem.Ty}
      {entry : SourceCoreDataCatalog.Entry} {sourceKey registeredValue : TypeSystem.Ty}
      {comparison : SourceCoreDataEquality.Prepared checked} {default : SourceCoreDefaultValue.Prepared checked}
      {source : List Step} {target : List PreparedStep} {keys : List (ExpressionId × Ty)}
      (selected : checked.catalog.entries[layout.dataType.index]? = some entry)
      (mappingType : entry.sourceType = .mapping sourceKey registeredValue)
      (comparisonGenerated : SourceCoreDataEquality.prepare fuel checked sourceKey = .ok comparison)
      (defaultGenerated : SourceCoreDefaultValue.prepare (sourceValue.size + 1) checked sourceValue = .ok default)
      (tail : Steps checked fuel missing (count + 1) source target keys) :
      Steps checked fuel missing count (.index layout key sourceValue :: source)
        (.index ⟨layout, key, count, comparison.expression, default.expression, missing sourceValue⟩ :: target)
        ((key, layout.keyType) :: keys)

theorem Steps.append {checked : SourceCoreDataCatalog.Checked} {fuel : Nat} {missing : TypeSystem.Ty → Word}
    {count : Nat} {a b : List Step} {x y : List PreparedStep} {left right : List (ExpressionId × Ty)}
    (first : Steps checked fuel missing count a x left)
    (second : Steps checked fuel missing (count + left.length) b y right) :
    Steps checked fuel missing count (a ++ b) (x ++ y) (left ++ right) := by
  induction first with
  | nil => exact second
  | member _ ih => exact .member (ih second)
  | index selected mappingType comparisonGenerated defaultGenerated _ ih =>
    exact .index selected mappingType comparisonGenerated defaultGenerated
      (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second))

private theorem forIn_preserves {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} (accepted : forIn items initial step = .ok final)
    (invariant : List α → β → Prop) (start : invariant [] initial)
    (next : ∀ seen item remaining state outcome,
      items = seen ++ item :: remaining → invariant seen state → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ invariant (seen ++ [item]) updated) : invariant items final := by
  have loop : ∀ remaining seen state,
      items = seen ++ remaining → invariant seen state → forIn remaining state step = .ok final →
      invariant items final := by
    intro remaining
    induction remaining with
    | nil =>
      intro seen state decomposition valid finished
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at finished
      subst final
      simpa [decomposition] using valid
    | cons item remaining ih =>
      intro seen state decomposition valid finished
      rw [List.forIn_cons] at finished
      obtain ⟨outcome, ran, finished⟩ := bind_ok finished
      obtain ⟨updated, rfl, preserved⟩ := next seen item remaining state outcome decomposition valid ran
      exact ih (seen ++ [item]) updated (by simpa [List.append_assoc] using decomposition) preserved finished
  exact loop items [] initial rfl start accepted

/-- Actual preparation emits exactly the accepted helpers and preserves key
order and all diagnostics through mixed member/index routes. -/
theorem steps_of_prepare {checked : SourceCoreDataCatalog.Checked} {fuel : Nat} {route : Route}
    {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (accepted : prepare checked fuel route invalid missing = .ok prepared) :
    prepared.route = route ∧ prepared.invalidProjection = invalid ∧
      Steps checked fuel missing 0 route.steps prepared.steps prepared.keys := by
  unfold prepare at accepted
  obtain ⟨state, loopAccepted, accepted⟩ := bind_ok accepted
  let invariant := fun (seen : List Step) (state : List PreparedStep × List (ExpressionId × Ty)) =>
    Steps checked fuel missing 0 seen state.1 state.2
  have certificate : invariant route.steps state := by
    apply forIn_preserves loopAccepted invariant
    · exact .nil 0
    · intro seen item remaining state outcome decomposition previous rowAccepted
      cases item with
      | member dataType index branches field =>
        simp only [pure, Except.pure, Except.ok.injEq] at rowAccepted
        subst outcome
        exact ⟨_, rfl, by simpa using previous.append (.member (id := dataType) (index := index)
          (branches := branches) (field := field) (.nil _))⟩
      | index layout key valueType =>
        cases selected : checked.catalog.entries[layout.dataType.index]? with
        | none => simp [selected, bind, Except.bind, throw] at rowAccepted
        | some entry =>
          cases kind : entry.sourceType <;> simp only [selected, kind, pure, Except.pure, bind, Except.bind, throw] at rowAccepted
          all_goals try cases rowAccepted
          rename_i sourceKey registeredValue
          obtain ⟨comparison, comparisonGenerated, rowAccepted⟩ := bind_ok rowAccepted
          obtain ⟨default, defaultGenerated, rowAccepted⟩ := bind_ok rowAccepted
          simp only [Except.ok.injEq] at rowAccepted
          subst outcome
          refine ⟨_, rfl, previous.append ?_⟩
          simp only [Nat.zero_add]
          exact .index selected kind (mapError_ok comparisonGenerated) (mapError_ok defaultGenerated) (.nil _)
  simp only [pure, Except.pure, Except.ok.injEq] at accepted
  subst prepared
  exact ⟨rfl, rfl, certificate⟩

/-- The optional default's independent meaning and finite execution are
available directly from the retained preparation receipt. -/
theorem default_preserves {checked : SourceCoreDataCatalog.Checked} {source : TypeSystem.Ty}
    {prepared : SourceCoreDefaultValue.Prepared checked}
    (accepted : SourceCoreDefaultValue.prepare (source.size + 1) checked source = .ok prepared)
    (environment : Environment) (store : Store) :
    ∃ value, DataDefaults.ResultRepresents checked.catalog source prepared.type value ∧
      Evaluates environment store prepared.expression value store := by
  have meaning := DataDefaults.prepared_preserves prepared environment store
  rwa [default_sourceType accepted] at meaning

end Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPreparation
