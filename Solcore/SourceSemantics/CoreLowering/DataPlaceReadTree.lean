import Solcore.SourceSemantics.CoreLowering.DataPlaceMappingHelpers
import Solcore.SourceSemantics.CoreLowering.DataPlaceMembers

/-! Finite observations of mixed member/mapping paths. Certificates contain
structural source/Core data and compiler receipts, never evaluations of child
code. They observe the selected path only; a complete heap payload relation
must additionally authenticate unselected siblings and function bodies. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceReadTree
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPatternValues DataPlaceMappingIndex

inductive Tree (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (identities : Dynamic.Value → Word → Prop) (prepared : Prepared) (keys : List Value)
    (resultRelation : OrderedMapping.Relation) :
    Dynamic.Value → Value → List PreparedStep → List Dynamic.EvaluatedProjection → Dynamic.Value → Nat → Prop where
  | leaf {source : Dynamic.Value} {value : Value} (represented : resultRelation source value) :
      Tree checked signatures identities prepared keys resultRelation source value [] [] source 0
  | member {metadata : DataConstructorInstantiation} {tag : ConstructorId}
      {sources : List Dynamic.Value} {values : List Value} {branch : MemberBranch}
      {dataType : DataTypeId} {index : Nat} {branches : List MemberBranch} {fieldType : Ty} {name : String}
      {sourceChild sourceLeaf : Dynamic.Value} {valueChild : Value} {steps : List PreparedStep}
      {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (authenticated : checked.catalog.resolveConstructor signatures metadata = .ok tag)
      (owner : tag.owner = dataType) (branchAt : branches[tag.index]? = some branch)
      (constructor : branch.constructor = tag)
      (sourceArity : metadata.payloadTypes.length = sources.length)
      (coreArity : branch.payloadTypes.length = values.length)
      (sourceAt : Dynamic.ValueAt sources index sourceChild) (coreAt : values[index]? = some valueChild)
      (tail : Tree checked signatures identities prepared keys resultRelation sourceChild valueChild steps projections sourceLeaf count) :
      Tree checked signatures identities prepared keys resultRelation
        (.constructed metadata sources) (.constructed tag (packValues values))
        (.member dataType index branches fieldType :: steps) (.member name index :: projections) sourceLeaf count
  | mapping {sourceKeyType sourceValueType : TypeSystem.Ty} {index : PreparedIndex}
      (certificate : Index checked sourceValueType index)
      {valueRelation : OrderedMapping.Relation} {sourceKey sourceChild sourceLeaf : Dynamic.Value}
      {key : Value} {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
      {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (keyRep : KeyRep certificate signatures identities sourceKey key)
      (keyAt : keys[index.keyPosition]? = some key)
      (entriesRep : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRelation sources entries)
      (selected : Reads sourceKey sources sourceValueType sourceChild)
      (tail : ∀ value, (valueRelation sourceChild value ∨
          ∃ expression, DataDefaults.Tree checked.catalog sourceValueType sourceChild value expression) →
        Tree checked signatures identities prepared keys resultRelation sourceChild value steps projections sourceLeaf count) :
      Tree checked signatures identities prepared keys resultRelation
        (.mapping sourceKeyType sourceValueType sources) (Core.OrderedMapping.encode index.layout entries)
        (.index index :: steps) (.index sourceKey :: projections) sourceLeaf
        (checked.catalog.entries.length + 1 + count)

/-- Every certificate executes the actual recursive selector, deriving all
comparison/default/child evaluations and preserving the entire input store
prefix. Each mapping selection contributes its own ordinary helper cells. -/
theorem Tree.preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {prepared : Prepared} {keys : List Value}
    {resultRelation : OrderedMapping.Relation} {source : Dynamic.Value} {value : Value}
    {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {sourceLeaf : Dynamic.Value} {count : Nat}
    (tree : Tree checked signatures identities prepared keys resultRelation source value steps projections sourceLeaf count)
    (faithful : IdentityFaithful identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (current keyExpression : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ leaf finalStore administrative,
      Dynamic.ProjectionsRead (some source) projections (some sourceLeaf) ∧ resultRelation sourceLeaf leaf ∧
      Evaluates environment store (select prepared steps current keyExpression) (.inRight .word (.inRight .unit leaf)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  induction tree generalizing environment store current keyExpression with
  | leaf represented => exact ⟨_, store, [], .nil, represented, .inRight (.inRight (selected.evaluates store)), by simp, rfl⟩
  | @member metadata tag sources values branch dataType index branches fieldType name sourceChild sourceLeaf valueChild steps projections count authenticated owner branchAt constructor sourceArity coreArity sourceAt coreAt tail ih =>
    obtain ⟨leaf, finalStore, administrative, read, represented, evaluated, extended, counted⟩ :=
      ih (packValues values :: environment) store _ _
        (projectPacked_selects (Selects.var (index := 0) rfl) coreArity index coreAt)
        (by simpa [shift] using keysSelected.weaken (packValues values))
    exact ⟨leaf, finalStore, administrative, .member sourceAt read, represented,
      .matchData (selected.evaluates store) owner (by simp only [List.getElem?_map, branchAt, Option.map_some]; rfl) evaluated,
      extended, counted⟩
  | @mapping sourceKeyType sourceValueType index certificate valueRelation sourceKey sourceChild sourceLeaf key sources entries steps projections count keyRep keyAt entriesRep read tail ih =>
    have keySelected := projectPacked_selects keysSelected keyLength index.keyPosition keyAt
    obtain ⟨child, childRep, childEvaluated⟩ := selectedIndex_preserves certificate prepared faithful keyRep entriesRep read
      environment store current keyExpression selected keySelected
    obtain ⟨leaf, finalStore, after, tailRead, represented, tailEvaluated, extended, counted⟩ :=
      ih child childRep (child :: environment) _ (.var 0) (shift 1 keyExpression) (.var rfl)
        (by simpa [shift] using keysSelected.weaken child)
    obtain ⟨before, beforeExtended, beforeCounted⟩ := selectedStore_extension certificate environment store entries key
    refine ⟨leaf, finalStore, before ++ after, ?_, represented,
      LanguageResult.bind_success _ childEvaluated tailEvaluated, ?_, ?_⟩
    · cases read with
      | found lookup => exact .indexFound lookup tailRead
      | default absent defaulted => exact .indexDefault absent defaulted tailRead
    · rw [extended, beforeExtended, List.append_assoc]
    · simp only [List.length_append, beforeCounted, counted]

end Solcore.SourceSemantics.CoreLowering.DataPlaceReadTree
