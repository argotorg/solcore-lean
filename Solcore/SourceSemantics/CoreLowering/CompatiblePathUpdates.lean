import Solcore.SourceSemantics.CoreLowering.CompatiblePathReads

/-! Actual prepared paths automatically produce full update certificates
from independent source updates and authenticated replacement/key payloads.
The relation preserves raw metadata and every untouched sibling/entry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CompatibleMapping CompatibleMapping.MixedPaths

private theorem replaced_eq_set {values output : List Dynamic.Value} {index : Nat} {replacement : Dynamic.Value}
    (replaced : Dynamic.ValuesReplaceAt values index replacement output) : output = values.set index replacement := by
  induction replaced with
  | head => rfl
  | @tail previous rest index replacement updated replaced ih => exact congrArg (List.cons previous) ih

 theorem Arguments.updateTree {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {keys : List Value}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keySites leaf}
    {resolved : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    {current updated replacementSource : Dynamic.Value} {value replacement : Value} {type replacementType : Ty}
    (represented : ValueRep checked registry functions mapping world root current value type)
    (replacementRelated : ValueRep checked registry functions mapping world leaf replacementSource replacement replacementType)
    (update : Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some current) resolved updated) (prepared : Prepared) :
    UpdateTree checked registry functions mapping world prepared keys replacementSource replacement root current value type steps resolved updated (updateCost checked steps) := by
  induction arguments generalizing current updated value type with
  | nil =>
    cases update with
    | leaf same =>
      subst updated
      have same := Except.ok.inj (represented.projection.symm.trans replacementRelated.projection)
      subst type
      exact .leaf replacementRelated
  | @member root field leaf name index signature typeArguments identity branches fieldType projections steps position keySites nominal selectedSignature certificate tail resolved arguments ih =>
    cases update with
    | member sourceAt tailUpdate replaced =>
      obtain ⟨tag, id, values, types, valueEq, typeEq, fields⟩ := constructor_fields represented rfl
      obtain ⟨owner, branch, actual, sourceChild, valueChild, branchAt, constructor, branchTypes,
        sourceField, view, coreField, found, coreAt, childRelated⟩ := certificate.select nominal selectedSignature fields
      have same := valueAt_unique found sourceAt
      subst sourceChild
      rw [valueEq, typeEq, replaced_eq_set replaced]
      exact .member fields owner branchAt constructor branchTypes sourceField coreField found coreAt
        (.compatible view (ih (.compatible view.symm childRelated) replacementRelated tailUpdate))
  | @index root keySource valueSource leaf key layout projections steps position keySites comparison missing certificate generated tail lookup keyValue resolved keyAt keyRelated arguments ih =>
    have finish {rawKey rawValue : TypeSystem.Ty} {entries updatedEntries : List (Dynamic.Value × Dynamic.Value)} {child updatedChild : Dynamic.Value}
        (represented : ValueRep checked registry functions mapping world root (.mapping rawKey rawValue entries) value type)
        (selectedAt : Selected lookup entries rawValue child)
        (tailUpdate : Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some child) resolved updatedChild)
        (inserted : Dynamic.MappingInsert lookup updatedChild entries updatedEntries) :
        UpdateTree checked registry functions mapping world prepared keys replacementSource replacement root
          (.mapping rawKey rawValue entries) value type (.index ⟨layout, key, position, comparison, missing⟩ :: steps)
          (.index lookup :: resolved) (.mapping rawKey rawValue updatedEntries) (2 * (checked.catalog.entries.length + 1) + updateCost checked steps) := by
      obtain ⟨header, nativeEntries, fallback, valueEq, typeEq, keyView, valueView, fields⟩ := certificate.mappingFields represented
      have rawKeyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType keySource := by
        rw [keyView, SourceCoreRawMetadata.runtimeType_idempotent]
      have rawValueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType valueSource := by
        rw [valueView, SourceCoreRawMetadata.runtimeType_idempotent]
      rw [valueEq, typeEq]
      refine .compatible (certificate.view.trans (by rw [keyView, valueView]; rfl))
        (.mapping generated fields (.compatible rawKeyView keyRelated) keyAt selectedAt ?_ inserted)
      intro native related
      exact .compatible rawValueView (ih (.compatible rawValueView.symm related) replacementRelated tailUpdate)
    cases update with
    | indexFound found tailUpdate inserted => exact finish represented (.found found) tailUpdate inserted
    | indexDefault absent defaulted tailUpdate inserted => exact finish represented (.default absent defaulted) tailUpdate inserted

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
