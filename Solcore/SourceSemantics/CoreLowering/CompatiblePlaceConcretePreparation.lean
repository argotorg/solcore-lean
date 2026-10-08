import Solcore.SourceSemantics.CoreLowering.CompatibleCatalogClosedSources
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes

/-! Real catalog preparation and actual place description supply the concrete
route gate used by the missing-default inventory. The authentic root binder
is selected by the original declared-binder lookup. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceConcretePreparation
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatibleCatalogRegistrationPrefix

/-- Successful description in an actually closed catalog proves the exact
concrete gate for its Source assignment and declared root binder. -/
theorem describe_concrete {context : SourceCoreCompatibleDataPlaces.Context} (closed : ClosedSources context.checked.catalog)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {route : Route}
    (described : describe context context.checked.signatures source site assignment = .ok route) :
    (SourceCoreDataCatalog.closed assignment.target.type &&
      ((SourceCoreDataPlaces.declaredBinders source).filter (fun binder =>
        decide (binder.id = assignment.target.root))).any (fun binder => SourceCoreDataCatalog.closed binder.scheme.body)) = true := by
  obtain ⟨binder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
  have binding : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder := description.binding
  have filtered := CompatibleMatchArmScopes.rootBinder_filter binding
  have targetClosed := CompatibleCatalogClosedSources.project_closed closed description.leafProjected
  have rootClosed := CompatibleCatalogClosedSources.project_closed closed description.rootProjected
  rw [targetClosed, filtered]
  simp only [List.any_cons, List.any_nil, rootClosed, Bool.true_or, Bool.true_and]

/-- The actual catalog factory discharges Source closure before the real
place description discharges the concrete inventory gate. -/
theorem describe_concrete_of_prepare {context : SourceCoreCompatibleDataPlaces.Context}
    {signatures : ProgramSignatures} {fuel : Nat} {types : List TypeSystem.Ty}
    {metadata : List SourceCoreRawMetadata.Metadata} {limits : SourceCoreRawMetadata.Limits} {profile : Bool}
    (prepared : SourceCoreCompatibleCatalog.prepare signatures fuel types metadata limits profile = .ok context.checked)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {route : Route}
    (described : describe context context.checked.signatures source site assignment = .ok route) :
    (SourceCoreDataCatalog.closed assignment.target.type &&
      ((SourceCoreDataPlaces.declaredBinders source).filter (fun binder =>
        decide (binder.id = assignment.target.root))).any (fun binder => SourceCoreDataCatalog.closed binder.scheme.body)) = true :=
  describe_concrete (CompatibleCatalogClosedSources.prepare_closed prepared) described

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceConcretePreparation
