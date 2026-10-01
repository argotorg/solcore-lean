import Solcore.SourceSemantics.CoreLowering.CompatiblePathFaultToken

/-! Independent source structural faults determine the exact emitted token
and automatically construct the actual selector/updater fault trees. Normalized key
guards come from the source fault trace; helper execution is never assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CompatibleMapping CompatibleMapping.MixedPaths

 theorem Arguments.faultTree {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {keys : List Value}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keySites leaf}
    {resolved : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    {current : Dynamic.Value} {value : Value} {type : Ty} {reason : Dynamic.SemanticFault}
    (represented : ValueRep checked registry functions mapping world root current value type)
    (fault : Dynamic.ProjectionsFaults (some current) resolved reason) (prepared : Prepared) :
    ∃ token count, FaultToken checked registry current steps resolved reason token count ∧
      FaultTree checked registry functions mapping world prepared keys current value type steps resolved reason token count := by
  induction arguments generalizing current value type with
  | nil => cases fault
  | @member root field leaf name index signature typeArguments identity branches fieldType projections steps position keySites nominal selectedSignature certificate tail resolved arguments ih =>
    cases fault with
    | member sourceAt tailFault =>
      obtain ⟨tag, id, values, types, valueEq, typeEq, fields⟩ := constructor_fields represented rfl
      obtain ⟨owner, branch, actual, sourceChild, valueChild, branchAt, constructor, branchTypes,
        sourceField, view, coreField, found, coreAt, childRelated⟩ := certificate.select nominal selectedSignature fields
      have same := valueAt_unique found sourceAt
      subst sourceChild
      obtain ⟨token, count, receipt, tree⟩ := ih (.compatible view.symm childRelated) tailFault
      refine ⟨token, count, .member found receipt, ?_⟩
      rw [valueEq, typeEq, owner]
      exact .member fields owner branchAt branchTypes sourceField coreField found coreAt tree
  | @index root keySource valueSource leaf key layout projections steps position keySites comparison missing certificate generated tail lookup keyValue resolved keyAt keyRelated arguments ih =>
    have finish {rawKey rawValue : TypeSystem.Ty} {entries : List (Dynamic.Value × Dynamic.Value)} {child : Dynamic.Value}
        (represented : ValueRep checked registry functions mapping world root (.mapping rawKey rawValue entries) value type)
        (typed : Dynamic.ValueRuntimeTypeMatches lookup rawKey)
        (selectedAt : Selected lookup entries rawValue child)
        (tailFault : Dynamic.ProjectionsFaults (some child) resolved reason) :
        ∃ token count,
          FaultToken checked registry (.mapping rawKey rawValue entries) (.index ⟨layout, key, position, comparison, missing⟩ :: steps)
            (.index lookup :: resolved) reason token count ∧
          FaultTree checked registry functions mapping world prepared keys (.mapping rawKey rawValue entries) value type
            (.index ⟨layout, key, position, comparison, missing⟩ :: steps) (.index lookup :: resolved) reason token count := by
      obtain ⟨header, nativeEntries, fallback, valueEq, typeEq, keyView, valueView, fields⟩ := certificate.mappingFields represented
      have rawKeyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType keySource := by
        rw [keyView, SourceCoreRawMetadata.runtimeType_idempotent]
      have rawValueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType valueSource := by
        rw [valueView, SourceCoreRawMetadata.runtimeType_idempotent]
      obtain ⟨native, related⟩ := Selected.represented fields selectedAt
      obtain ⟨token, count, receipt, tree⟩ := ih (.compatible rawValueView.symm related) tailFault
      refine ⟨token, checked.catalog.entries.length + 1 + count, ?_, ?_⟩
      · cases selectedAt with
        | found found => exact .found typed found receipt
        | default absent defaulted => exact .default typed absent defaulted receipt
      · rw [valueEq, typeEq]
        refine .mapping generated fields (.compatible rawKeyView keyRelated) typed keyAt selectedAt ?_
        intro native related
        obtain ⟨other, otherCount, otherReceipt, otherTree⟩ := ih (.compatible rawValueView.symm related) tailFault
        obtain ⟨rfl, rfl⟩ := receipt.functional otherReceipt
        exact otherTree
    cases fault with
    | indexDefaultUnavailable typed absent unavailable =>
      obtain ⟨header, nativeEntries, fallback, valueEq, typeEq, keyView, valueView, fields⟩ := certificate.mappingFields represented
      refine ⟨missing.add header, checked.catalog.entries.length + 1, .missing fields.metadata typed absent unavailable, ?_⟩
      rw [valueEq, typeEq]
      refine .missing generated fields (.compatible ?_ keyRelated) typed keyAt absent unavailable
      rw [keyView, SourceCoreRawMetadata.runtimeType_idempotent]
    | indexFound typed found tailFault => exact finish represented typed (.found found) tailFault
    | indexDefault typed absent defaulted tailFault => exact finish represented typed (.default absent defaulted) tailFault

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
