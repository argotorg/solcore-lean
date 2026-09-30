import Solcore.SourceSemantics.CoreLowering.DataPayloadFields
import Solcore.SourceSemantics.CoreLowering.DataPayloadDefaults
import Solcore.SourceSemantics.CoreLowering.DataPlaceReadTree

/-! Read trees are derived from complete payloads, static path layout/key
receipts, and the independent source read. No child Core evaluations or
representation-promotion callbacks are assumptions of the extraction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceMappingIndex DataPlaceMembers

inductive Path (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (mapping : LocationMap) (world : StoreTyping)
    (keys : List Value) : TypeSystem.Ty → Ty → List PreparedStep → List Dynamic.EvaluatedProjection →
      TypeSystem.Ty → Ty → Nat → Prop where
  | nil {sourceType : TypeSystem.Ty} {type : Ty} (projected : checked.catalog.project sourceType = .ok type) :
      Path checked signatures functions mapping world keys sourceType type [] [] sourceType type 0
  | member {root field leaf : TypeSystem.Ty} {dataType : DataTypeId} {index : Nat} {branches : List MemberBranch}
      {fieldType leafType : Ty} {name : String} {steps : List PreparedStep}
      {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (layout : MemberLayout checked signatures root field dataType index branches)
      (fieldProjected : checked.catalog.project field = .ok fieldType)
      (tail : Path checked signatures functions mapping world keys field fieldType steps projections leaf leafType count) :
      Path checked signatures functions mapping world keys root (.namedData dataType)
        (.member dataType index branches fieldType :: steps) (.member name index :: projections) leaf leafType count
  | index {keyType valueType leaf : TypeSystem.Ty} {index : PreparedIndex} {leafType : Ty}
      {sourceKey : Dynamic.Value} {key : Value} {steps : List PreparedStep}
      {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (certificate : Index checked valueType index)
      (keyProjected : checked.catalog.project keyType = .ok index.layout.keyType)
      (valueProjected : checked.catalog.project valueType = .ok index.layout.valueType)
      (keyRelated : ValueRep checked.catalog signatures functions mapping world keyType sourceKey key index.layout.keyType)
      (keyAt : keys[index.keyPosition]? = some key)
      (tail : Path checked signatures functions mapping world keys valueType index.layout.valueType steps projections leaf leafType count) :
      Path checked signatures functions mapping world keys (.mapping keyType valueType) index.layout.type
        (.index index :: steps) (.index sourceKey :: projections) leaf leafType (checked.catalog.entries.length + 1 + count)
  | comptime {inner leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep}
      {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (tail : Path checked signatures functions mapping world keys inner type steps projections leaf leafType count) :
      Path checked signatures functions mapping world keys (.comptime inner) type steps projections leaf leafType count

private theorem comptime_parts {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {inner : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep catalog signatures functions mapping world (.comptime inner) source value type) :
    ValueRep catalog signatures functions mapping world inner source value type := by
  cases represented with
  | comptime inner => exact inner
  | constructed nominal => simp [SourceCoreDataCatalog.nominalParts] at nominal

theorem Path.read_tree {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (observations : FunctionObservations checked.catalog signatures functions identities)
    (layouts : CatalogLayouts checked.catalog) (prepared : Prepared) {keys : List Value}
    {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (path : Path checked signatures functions mapping world keys root type steps projections leaf leafType count)
    {source sourceLeaf : Dynamic.Value} {value : Value}
    (represented : ValueRep checked.catalog signatures functions mapping world root source value type)
    (read : Dynamic.ProjectionsRead (some source) projections (some sourceLeaf)) :
    DataPlaceReadTree.Tree checked signatures identities prepared keys
      (fun source core => ValueRep checked.catalog signatures functions mapping world leaf source core leafType)
      source value steps projections sourceLeaf count := by
  induction path generalizing source value sourceLeaf with
  | nil projected => cases read; exact .leaf represented
  | @member root field leaf dataType index branches fieldType leafType name steps projections count layout fieldProjected tail ih =>
    obtain ⟨declaration, arguments, nominal⟩ := layout.nominal
    obtain ⟨metadata, tag, sources, values, types, sourceEq, valueEq, typeEq, result, authenticated, registered, payloads⟩ :=
      represented.nominal_parts nominal
    subst source; subst value
    obtain ⟨owner, branch, branchAt, constructor, fieldAt, arity⟩ := layout.constructors metadata tag result authenticated
    obtain ⟨sourceChild, valueChild, childType, sourceAt, coreAt, coreTypeAt, childRep⟩ := payloads.at fieldAt
    have childTypeEq := Except.ok.inj (childRep.projection.symm.trans fieldProjected)
    subst childType
    cases read with
    | member selected read =>
      have same := sourceAt.functional selected
      subst sourceChild
      exact .member authenticated owner branchAt constructor payloads.length.1
        (arity.trans payloads.length.2.1) sourceAt coreAt (ih childRep read)
  | @index keyType valueType leaf index leafType sourceKey key steps projections count certificate keyProjected valueProjected keyRelated keyAt tail ih =>
    obtain ⟨sources, entries, sourceEq, valueEq, identity, registered, contents⟩ :=
      represented.mapping_parts index.layout keyProjected valueProjected
    subst source; subst value
    have keyObserved : KeyRep certificate signatures identities sourceKey key := by
      unfold KeyRep DataMappingComparison.KeyRep
      rw [← certificate.keyType]
      exact keyRelated.observation observations
    have entriesObserved : OrderedMapping.EntriesRel (KeyRep certificate signatures identities)
        (fun source core => ValueRep checked.catalog signatures functions mapping world valueType source core index.layout.valueType)
        sources entries := by
      unfold KeyRep DataMappingComparison.KeyRep
      rw [← certificate.keyType]
      exact contents.observed observations
    cases read with
    | indexFound found read =>
      apply DataPlaceReadTree.Tree.mapping (count := count) certificate keyObserved keyAt entriesObserved (.found found)
      intro child childRep
      rcases childRep with childRep | ⟨expression, defaulted⟩
      · exact ih childRep read
      · exact ih (default_represents_at layouts valueProjected defaulted) read
    | indexDefault absent defaulted read =>
      apply DataPlaceReadTree.Tree.mapping (count := count) certificate keyObserved keyAt entriesObserved (.default absent defaulted)
      intro child childRep
      rcases childRep with childRep | ⟨expression, defaulted⟩
      · exact ih childRep read
      · exact ih (default_represents_at layouts valueProjected defaulted) read
  | comptime tail ih => exact ih (comptime_parts represented) read

end Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
