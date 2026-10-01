import Solcore.SourceSemantics.CoreLowering.CompatiblePreparedPath
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingVirtualRoot

/-! Static receipts from the real compatible place description. The declared
root type and the selected source type remain distinct: only the compiler's
explicit runtime-type check relates the selected type to the assignment type.
Virtual mapping roots retain the actual encoder and quote receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open DataEqualityGeneration CompatibleMixedRoute

structure Description (context : SourceCoreCompatibleDataPlaces.Context) (source : TypedSource)
    (site : SourceCoreElaboration.ErrorSite) (assignment : AssignmentResolution) (route : Route) (binder : TypedBinder) (selected : TypeSystem.Ty) : Prop where
  binding : rootBinder source assignment.target.root = .ok binder
  rootSource : route.rootSourceType = binder.scheme.body
  rootProjected : context.checked.catalog.project binder.scheme.body = .ok route.rootType
  leafProjected : context.checked.catalog.project assignment.target.type = .ok route.leafType
  selectedType : SourceCoreRawMetadata.runtimeType selected = SourceCoreRawMetadata.runtimeType assignment.target.type
  routed : routeSteps context.checked context.checked.signatures source site assignment.target.root
    binder.scheme.body assignment.target.projections = .ok (route.steps, selected)
  virtual : ∀ key value, binder.scheme.body = .mapping key value →
    CompatibleMapping.VirtualRoot.Generated context route key value
  ordinary : (∀ key value, binder.scheme.body ≠ .mapping key value) → route.rootMapping = none

private theorem project_facts {checked : Checked} {site : SourceCoreElaboration.ErrorSite}
    {source : TypeSystem.Ty} {type : Ty} (accepted : project checked site source = .ok type) :
    checked.catalog.project source = .ok type ∧ type.WellFormed checked.catalog.definitions := by
  unfold project SourceCoreCompatibleDataExpressions.projectType SourceCoreCompatibleCatalog.Checked.project at accepted
  cases generated : checked.catalog.project source with
  | error error => simp [generated, bind, Except.bind, Except.map, Except.mapError] at accepted
  | ok native =>
    simp only [generated, bind, Except.bind] at accepted
    split at accepted
    · rename_i valid
      simp only [pure, Except.pure, Except.map, Except.mapError, Except.ok.injEq] at accepted
      subst type
      exact ⟨rfl, Ty.isWellFormed_sound valid⟩
    · cases accepted

/-- Actual description success supplies both source metadata and every route
step. No helper execution or semantic conclusion is assumed. -/
theorem of_describe {context : SourceCoreCompatibleDataPlaces.Context} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution} {route : Route}
    (accepted : describe context context.checked.signatures source site assignment = .ok route) :
    ∃ binder selected, Description context source site assignment route binder selected := by
  have original := accepted
  unfold describe at accepted
  dsimp only at accepted
  split at accepted <;> try cases accepted
  obtain ⟨binder, binding, accepted⟩ := bind_ok accepted
  obtain ⟨rootType, rootProjected, accepted⟩ := bind_ok accepted
  obtain ⟨⟨steps, selected⟩, routed, accepted⟩ := bind_ok accepted
  split at accepted <;> try cases accepted
  rename_i selectedType
  have finish : ∀ rootMapping leafType,
      route = ⟨binder.scheme.body, rootType, leafType, steps, rootMapping⟩ →
      project context.checked site assignment.target.type = .ok leafType →
      ((∀ key value, binder.scheme.body ≠ .mapping key value) → rootMapping = none) →
      ∃ binder selected, Description context source site assignment route binder selected := by
    intro rootMapping leafType routeEq leafProjected ordinary
    subst route
    refine ⟨binder, selected, ⟨binding, rfl, (project_facts rootProjected).1,
      (project_facts leafProjected).1, selectedType, routed, ?_, ordinary⟩⟩
    intro key value declared
    exact CompatibleMapping.VirtualRoot.generated_of_describe binding declared original
  split at accepted
  · rename_i key value declared
    cases identity : context.checked.catalog.identity? binder.scheme.body with
    | none => simp [identity, throw, pure, Except.pure, bind, Except.bind] at accepted
    | some identityValue =>
      simp only [identity, pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨coreKey, _, accepted⟩ := bind_ok accepted
      obtain ⟨coreValue, _, accepted⟩ := bind_ok accepted
      split at accepted <;> try cases accepted
      obtain ⟨carrier, _, accepted⟩ := bind_ok accepted
      split at accepted <;> try cases accepted
      cases quoted : SourceCoreCompatibleDataExpressions.quote carrier.value with
      | none => simp [quoted, throw] at accepted
      | some expression =>
        simp only [quoted] at accepted
        obtain ⟨leafType, leafProjected, accepted⟩ := bind_ok accepted
        cases accepted
        exact finish (some expression) leafType rfl leafProjected (fun impossible => (impossible key value declared).elim)
  · simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨leafType, leafProjected, accepted⟩ := bind_ok accepted
    cases accepted
    exact finish none leafType rfl leafProjected (fun _ => rfl)

/-- Description and preparation compose without re-proving or approximating
member authentication, mapping layout lookup, or comparison generation. -/
theorem Description.prepared {context : SourceCoreCompatibleDataPlaces.Context} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution} {route : Route}
    {binder : TypedBinder} {selected : TypeSystem.Ty}
    (description : Description context source site assignment route binder selected)
    {fuel : Nat} {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (accepted : prepare context fuel route invalid missing = .ok prepared) :
    prepared.route = route ∧ prepared.invalidProjection = invalid ∧
      PreparedPath context.checked source site binder.scheme.body assignment.target.projections
        0 prepared.steps prepared.keys selected :=
  prepared_of_success description.routed accepted

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription
