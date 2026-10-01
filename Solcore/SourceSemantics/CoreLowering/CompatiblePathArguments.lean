import Solcore.SourceSemantics.CoreLowering.CompatiblePreparedPath
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingEncoding

/-! Already evaluated index values are attached to the statically prepared
path in source order. This is a payload relation, not a child evaluation or a
replacement compiler. Native projection equality does not authenticate keys. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload

inductive Arguments (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) (values : List Value) :
    {root : TypeSystem.Ty} → {projections : List PlaceProjection} → {position : Nat} →
    {steps : List PreparedStep} → {keys : List (ExpressionId × Ty)} → {leaf : TypeSystem.Ty} →
    PreparedPath checked source site root projections position steps keys leaf → List Dynamic.EvaluatedProjection → Prop where
  | nil {type position} : Arguments checked registry functions mapping world source site values (PreparedPath.nil (type := type) (position := position)) []
  | member {root field leaf : TypeSystem.Ty} {name : String} {index : Nat}
      {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty} {identity : DataTypeId}
      {branches : List MemberBranch} {fieldType : Ty} {projections : List PlaceProjection}
      {steps : List PreparedStep} {position : Nat} {keys : List (ExpressionId × Ty)}
      {nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments)}
      {selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature]}
      {certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root) field signature arguments index identity branches fieldType}
      {tail : PreparedPath checked source site field projections position steps keys leaf}
      {resolved : List Dynamic.EvaluatedProjection}
      (rest : Arguments checked registry functions mapping world source site values tail resolved) :
      Arguments checked registry functions mapping world source site values (.member (name := name) nominal selected certificate tail)
        (.member name index :: resolved)
  | index {root keySource valueSource leaf : TypeSystem.Ty} {key : ExpressionId} {layout : OrderedMapping.Layout}
      {projections : List PlaceProjection} {steps : List PreparedStep} {position : Nat} {keys : List (ExpressionId × Ty)}
      {comparison : Expr} {missing : Word}
      {certificate : IndexSite checked source root keySource valueSource key layout}
      {generated : CompatibleMapping.Index checked ⟨layout, key, position, comparison, missing⟩}
      {tail : PreparedPath checked source site valueSource projections (position + 1) steps keys leaf}
      {lookup : Dynamic.Value} {value : Value} {resolved : List Dynamic.EvaluatedProjection}
      (keyAt : values[position]? = some value)
      (represented : ValueRep checked registry functions mapping world keySource lookup value layout.keyType)
      (rest : Arguments checked registry functions mapping world source site values tail resolved) :
      Arguments checked registry functions mapping world source site values (.index certificate generated tail)
        (.index lookup :: resolved)

def readCost (checked : Checked) : List PreparedStep → Nat
  | [] => 0
  | .member _ _ _ _ :: rest => readCost checked rest
  | .index _ :: rest => checked.catalog.entries.length + 1 + readCost checked rest

def updateCost (checked : Checked) : List PreparedStep → Nat
  | [] => 0
  | .member _ _ _ _ :: rest => updateCost checked rest
  | .index _ :: rest => 2 * (checked.catalog.entries.length + 1) + updateCost checked rest

theorem IndexSite.projection {checked : Checked} {source : TypedSource} {root keySource valueSource : TypeSystem.Ty}
    {key : ExpressionId} {layout : OrderedMapping.Layout}
    (certificate : IndexSite checked source root keySource valueSource key layout) :
    checked.catalog.project root = .ok (SourceCoreMappingWithDefault.type layout) := by
  have identity : checked.catalog.identity? (.mapping keySource valueSource) = some layout.dataType := by
    have normalized : checked.catalog.identity? (SourceCoreRawMetadata.runtimeType root) = checked.catalog.identity? root := by
      simp only [SourceCoreCompatibleCatalog.Catalog.identity?, SourceCoreRawMetadata.runtimeType_idempotent]
    rw [certificate.view] at normalized
    exact normalized.trans certificate.identity
  rw [← checked.catalog.project_runtimeType root, certificate.view]
  exact CompatibleEncoding.mapping_project identity certificate.keyProjection certificate.valueProjection

theorem IndexSite.mappingFields {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {root keySource valueSource : TypeSystem.Ty}
    {key : ExpressionId} {layout : OrderedMapping.Layout}
    (certificate : IndexSite checked source root keySource valueSource key layout)
    {rawKey rawValue : TypeSystem.Ty} {entries : List (Dynamic.Value × Dynamic.Value)} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world root (.mapping rawKey rawValue entries) value type) :
    ∃ header nativeEntries fallback,
      value = CompatibleMapping.Transport.carrier header fallback layout nativeEntries ∧
      type = SourceCoreMappingWithDefault.type layout ∧
      keySource = SourceCoreRawMetadata.runtimeType rawKey ∧ valueSource = SourceCoreRawMetadata.runtimeType rawValue ∧
      CompatibleMapping.Fields checked registry functions mapping world rawKey rawValue entries header layout nativeEntries fallback := by
  obtain ⟨header, actual, nativeEntries, fallback, valueEq, typeEq, view, fields⟩ := CompatibleMapping.mapping_fields represented rfl
  have sameType := Except.ok.inj (represented.projection.symm.trans certificate.projection)
  have sameLayout := CompatibleMapping.registered_layout_eq fields.registered certificate.registered (typeEq.symm.trans sameType)
  subst actual
  have types := TypeSystem.Ty.mapping.inj (certificate.view.symm.trans view)
  exact ⟨header, nativeEntries, fallback, valueEq, sameType, types.1, types.2, fields⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
