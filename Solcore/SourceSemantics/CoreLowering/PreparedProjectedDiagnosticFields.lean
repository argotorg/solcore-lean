import Solcore.SourceSemantics.CoreLowering.ProtectedStateProjectedAssignmentHeads

/-! Project a reached diagnostic packet at its actual prepared shape before
specializing the ambient definitions of the mixed caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedProjectedDiagnosticFields
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
universe u v

theorem projected {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {source : TypedSource} {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {environment : Dynamic.Environment}
    {place : PlaceResolution} {prepared : Prepared} {operator : Syntax.ValueAssignOp} {invalid : Word}
    {initialIndex : ProtectedStateTransition.Index} {initial : protocol.State initialIndex} {faults : FunctionCalls.FaultRep}
    {codes : List SourceCoreBasic.LoweredExpr} {leaf : TypeSystem.Ty}
    {shape : GenericAssignmentStatements.Shape values source context certificate scope administrative
      ambient.definitions place prepared codes leaf}
    (errors : ShapeErrors values registry functions protocol source context certificate scope administrative environment
      place prepared operator invalid initial faults shape)
    (nonempty : place.projections ≠ []) :
    ∃ (sourceTypes : List TypeSystem.Ty) (site : SourceCoreElaboration.ErrorSite)
      (_layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) values source certificate
        scope site place prepared codes sourceTypes leaf administrative),
      ((∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none) ∧
      MissingFor values.checked registry functions protocol source site place prepared leaf initial faults ∧
      UninitializedFor values.checked registry functions protocol environment place prepared initial faults := by
  cases errors with
  | bare operands => exact (nonempty ‹place.projections = []›).elim
  | @projected _ _ sourceTypes site layout ordinary missing uninitialized =>
    exact ⟨sourceTypes, site, layout, ordinary, missing, uninitialized⟩

end Solcore.SourceSemantics.CoreLowering.PreparedProjectedDiagnosticFields
