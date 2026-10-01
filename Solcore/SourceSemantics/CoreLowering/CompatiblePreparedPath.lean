import Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingPreparation

/-! Actual route and preparation receipts compose into a path whose index
comparisons are the certified generated comparisons. Catalog identity lookup,
not equality of native mapping carrier types, authenticates each key type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces

inductive PreparedPath (checked : Checked) (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) :
    TypeSystem.Ty → List PlaceProjection → Nat → List PreparedStep → List (ExpressionId × Ty) → TypeSystem.Ty → Prop where
  | nil {type position} : PreparedPath checked source site type [] position [] [] type
  | member {root field leaf name index signature arguments identity branches fieldType projections steps position keys}
      (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments))
      (selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
      (certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root)
        field signature arguments index identity branches fieldType)
      (tail : PreparedPath checked source site field projections position steps keys leaf) :
      PreparedPath checked source site root (.member name index :: projections) position (.member identity index branches fieldType :: steps) keys leaf
  | index {root keySource valueSource leaf key layout projections steps position keys comparison missing}
      (certificate : IndexSite checked source root keySource valueSource key layout)
      (generated : CompatibleMapping.Index checked ⟨layout, key, position, comparison, missing⟩)
      (tail : PreparedPath checked source site valueSource projections (position + 1) steps keys leaf) :
      PreparedPath checked source site root (.index key :: projections) position
        (.index ⟨layout, key, position, comparison, missing⟩ :: steps) ((key, layout.keyType) :: keys) leaf

 theorem Path.prepared {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {steps : List Step}
    (path : Path checked source site root projections steps leaf)
    {fuel position : Nat} {missing : TypeSystem.Ty → Word} {prepared : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (generated : CompatibleMixedPreparation.Steps checked fuel missing steps position prepared keys) :
    PreparedPath checked source site root projections position prepared keys leaf := by
  induction path generalizing position prepared keys with
  | nil => cases generated; exact .nil
  | member nominal selected certificate tail ih => cases generated with
    | member generated => exact .member nominal selected certificate (ih generated)
  | @index root keySource valueSource leaf key layout projections steps certificate tail ih => cases generated with
    | @index _ _ _ _ _ _ _ entry sourceKey recordedValue row sourceEq comparison generated rest =>
      obtain ⟨actualEntry, actualRow, actualSource⟩ := CompatibleEquality.identity_entry certificate.identity
      have entries := Option.some.inj (actualRow.symm.trans row)
      subst actualEntry
      rw [certificate.view, sourceEq] at actualSource
      have sourceKeys := TypeSystem.Ty.mapping.inj actualSource
      obtain ⟨rfl, rfl⟩ := sourceKeys
      exact .index certificate (CompatibleMapping.Index.of_generated generated certificate.keyProjection) (ih rest)

/-- Real routeSteps and real prepare success suffice for all static path
receipts. No comparator, key, getter, or setter execution is supplied. -/
theorem prepared_of_success {context : SourceCoreCompatibleDataPlaces.Context}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {route : Route}
    {fuel : Nat} {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (routed : routeSteps context.checked context.checked.signatures source site binder root projections = .ok (route.steps, leaf))
    (generated : prepare context fuel route invalid missing = .ok prepared) :
    prepared.route = route ∧ prepared.invalidProjection = invalid ∧
      PreparedPath context.checked source site root projections 0 prepared.steps prepared.keys leaf := by
  obtain ⟨sameRoute, sameInvalid, preparedSteps⟩ := CompatibleMixedPreparation.of_prepare generated
  exact ⟨sameRoute, sameInvalid, (of_routeSteps routed).prepared preparedSteps⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
