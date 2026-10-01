import Solcore.SourceSemantics.CoreLowering.CompatibleMemberCertificates

/-! Static extraction from actual mixed place preparation. Each comparison is
prepared once from the catalog row and each index retains its source-order
position. Layout/source projection agreement belongs to route authentication. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedPreparation
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces

inductive Steps (checked : Checked) (fuel : Nat) (missing : TypeSystem.Ty → Word) :
    List Step → Nat → List PreparedStep → List (ExpressionId × Ty) → Prop where
  | nil {position} : Steps checked fuel missing [] position [] []
  | member {dataType index branches fieldType rest position prepared keys}
      (tail : Steps checked fuel missing rest position prepared keys) :
      Steps checked fuel missing (.member dataType index branches fieldType :: rest) position
        (.member dataType index branches fieldType :: prepared) keys
  | index {layout key valueType rest position prepared keys entry sourceKey recordedValue}
      (row : checked.catalog.entries[layout.dataType.index]? = some entry)
      (source : entry.sourceType = .mapping sourceKey recordedValue)
      {comparison : SourceCoreCompatibleDataEquality.Prepared checked}
      (generated : SourceCoreCompatibleDataEquality.prepare fuel checked sourceKey = .ok comparison)
      (tail : Steps checked fuel missing rest (position + 1) prepared keys) :
      Steps checked fuel missing (.index layout key valueType :: rest) position
        (.index ⟨layout, key, position, comparison.expression, missing valueType⟩ :: prepared) ((key, layout.keyType) :: keys)

 theorem Steps.append {checked : Checked} {fuel : Nat} {missing : TypeSystem.Ty → Word}
    {first second : List Step} {position : Nat} {left right : List PreparedStep} {leftKeys rightKeys : List (ExpressionId × Ty)}
    (a : Steps checked fuel missing first position left leftKeys)
    (b : Steps checked fuel missing second (position + leftKeys.length) right rightKeys) :
    Steps checked fuel missing (first ++ second) position (left ++ right) (leftKeys ++ rightKeys) := by
  induction a with
  | nil => simpa using b
  | member _ ih => exact .member (ih b)
  | index row source generated _ ih =>
    exact .index row source generated (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b))

/-- Successful preparation yields a receipt for every original step, without
assuming comparisons or path selection have executed. -/
theorem of_prepare {context : SourceCoreCompatibleDataPlaces.Context} {fuel : Nat} {route : Route} {invalid : Word}
    {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (accepted : prepare context fuel route invalid missing = .ok prepared) :
    prepared.route = route ∧ prepared.invalidProjection = invalid ∧
      Steps context.checked fuel missing route.steps 0 prepared.steps prepared.keys := by
  unfold prepare at accepted
  obtain ⟨state, loopAccepted, accepted⟩ := CompatibleEncoding.bind_ok accepted
  let invariant := fun seen (state : List PreparedStep × List (ExpressionId × Ty)) =>
    Steps context.checked fuel missing seen 0 state.1 state.2
  have generated : invariant route.steps state := by
    apply CompatibleMemberCertificates.forIn_preserves loopAccepted invariant
    · exact .nil
    · intro seen item remaining state outcome decomposition previous accepted
      obtain ⟨steps, keys⟩ := state
      cases item with
      | member dataType index branches fieldType =>
        simp only [pure, Except.pure, Except.ok.injEq] at accepted
        subst outcome
        refine ⟨_, rfl, ?_⟩
        simpa only [invariant, List.append_nil] using previous.append (.member (dataType := dataType) (index := index) (branches := branches) (fieldType := fieldType) .nil)
      | index layout key valueType =>
        dsimp only at accepted
        cases row : context.checked.catalog.entries[layout.dataType.index]? with
        | none => simp [row, throw, throwThe, bind, Except.bind] at accepted
        | some entry =>
          simp only [row] at accepted
          cases source : entry.sourceType <;> try (simp [source, throw, throwThe, bind, Except.bind] at accepted)
          case mapping sourceKey recordedValue =>
            simp only [pure, Except.pure] at accepted
            cases generated : SourceCoreCompatibleDataEquality.prepare fuel context.checked sourceKey with
            | error error => simp [generated, Except.mapError] at accepted
            | ok comparison =>
              simp only [generated, Except.mapError, Except.ok.injEq] at accepted
              subst outcome
              refine ⟨_, rfl, ?_⟩
              simpa only [invariant, Nat.zero_add] using previous.append (.index (key := key) (valueType := valueType) row source generated .nil)
  simp only [pure, Except.pure, Except.ok.injEq] at accepted
  subst prepared
  exact ⟨rfl, rfl, generated⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedPreparation
