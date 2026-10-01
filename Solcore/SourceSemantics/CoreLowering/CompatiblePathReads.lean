import Solcore.SourceSemantics.CoreLowering.CompatiblePathArguments

/-! Independent successful source reads and authenticated input/key payloads
construct the semantic tree for the actual prepared selector. No child or
helper Core evaluation is an assumption. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CompatibleMapping CompatibleMapping.MixedPaths

theorem valueAt_unique {values : List Dynamic.Value} {index : Nat} {a b : Dynamic.Value}
    (first : Dynamic.ValueAt values index a) (second : Dynamic.ValueAt values index b) : a = b := by
  induction first generalizing b with
  | head => cases second; rfl
  | tail _ ih => cases second with | tail rest => exact ih rest

 theorem Arguments.readTree {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {keys : List Value}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keySites leaf}
    {resolved : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    {current selected : Dynamic.Value} {value : Value} {type leafCore : Ty}
    (represented : ValueRep checked registry functions mapping world root current value type)
    (leafProjected : checked.catalog.project leaf = .ok leafCore)
    (read : Dynamic.ProjectionsRead (some current) resolved (some selected)) (prepared : Prepared) :
    ReadTree checked registry functions mapping world prepared keys leaf leafCore root current value steps resolved selected (readCost checked steps) := by
  induction arguments generalizing current selected value type with
  | nil =>
    cases read
    have same := Except.ok.inj (represented.projection.symm.trans leafProjected)
    subst type
    exact .leaf represented
  | @member root field leaf name index signature typeArguments identity branches fieldType projections steps position keySites nominal selectedSignature certificate tail resolved arguments ih =>
    cases read with
    | member sourceAt tailRead =>
      obtain ⟨tag, id, values, types, valueEq, typeEq, fields⟩ := constructor_fields represented rfl
      obtain ⟨owner, branch, actual, sourceChild, valueChild, branchAt, constructor, branchTypes,
        sourceField, view, coreField, found, coreAt, childRelated⟩ := certificate.select nominal selectedSignature fields
      have same := valueAt_unique found sourceAt
      subst sourceChild
      rw [valueEq]
      exact .member fields owner branchAt constructor branchTypes sourceField coreField found coreAt
        (.compatible view (ih (.compatible view.symm childRelated) leafProjected tailRead))
  | @index root keySource valueSource leaf key layout projections steps position keySites comparison missing certificate generated tail lookup keyValue resolved keyAt keyRelated arguments ih =>
    have finish {rawKey rawValue : TypeSystem.Ty} {entries : List (Dynamic.Value × Dynamic.Value)} {child : Dynamic.Value}
        (represented : ValueRep checked registry functions mapping world root (.mapping rawKey rawValue entries) value type)
        (selectedAt : Selected lookup entries rawValue child)
        (tailRead : Dynamic.ProjectionsRead (some child) resolved (some selected)) :
        ReadTree checked registry functions mapping world prepared keys leaf leafCore root
          (.mapping rawKey rawValue entries) value (.index ⟨layout, key, position, comparison, missing⟩ :: steps)
          (.index lookup :: resolved) selected (checked.catalog.entries.length + 1 + readCost checked steps) := by
      obtain ⟨header, nativeEntries, fallback, valueEq, typeEq, keyView, valueView, fields⟩ := certificate.mappingFields represented
      have rawKeyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType keySource := by
        rw [keyView, SourceCoreRawMetadata.runtimeType_idempotent]
      have rawValueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType valueSource := by
        rw [valueView, SourceCoreRawMetadata.runtimeType_idempotent]
      rw [valueEq]
      refine .compatible (certificate.view.trans (by rw [keyView, valueView]; rfl))
        (.mapping generated fields (.compatible rawKeyView keyRelated) keyAt selectedAt ?_)
      intro native related
      exact .compatible rawValueView (ih (.compatible rawValueView.symm related) leafProjected tailRead)
    cases read with
    | indexFound found tailRead => exact finish represented (.found found) tailRead
    | indexDefault absent defaulted tailRead => exact finish represented (.default absent defaulted) tailRead

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
