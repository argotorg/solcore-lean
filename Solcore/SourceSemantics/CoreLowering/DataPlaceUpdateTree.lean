import Solcore.SourceSemantics.CoreLowering.DataPlaceReadTree

/-! Reconstruction of mixed finite paths from the latest supplied root.
Certificates contain structural representation closure laws, not evaluations
of generated children. Mapping defaults are derived from actual preparations;
all nested helper allocation is appended after the existing store prefix. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTree
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPatternValues DataPlaceMappingIndex

inductive Tree (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (identities : Dynamic.Value → Word → Prop) (prepared : Prepared) (keys : List Value)
    (replacementSource : Dynamic.Value) (replacement : Value) :
    OrderedMapping.Relation → Dynamic.Value → Value → List PreparedStep →
      List Dynamic.EvaluatedProjection → Dynamic.Value → Nat → Prop where
  | leaf {relation : OrderedMapping.Relation} {source : Dynamic.Value} {value : Value}
      (represented : relation replacementSource replacement) :
      Tree checked signatures identities prepared keys replacementSource replacement relation source value [] [] replacementSource 0
  | member {relation childRelation : OrderedMapping.Relation}
      {metadata : DataConstructorInstantiation} {tag : ConstructorId}
      {sources : List Dynamic.Value} {values : List Value} {branch : MemberBranch}
      {dataType : DataTypeId} {index : Nat} {branches : List MemberBranch} {fieldType : Ty} {name : String}
      {sourceChild updatedChild : Dynamic.Value} {valueChild : Value} {steps : List PreparedStep}
      {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (authenticated : checked.catalog.resolveConstructor signatures metadata = .ok tag)
      (owner : tag.owner = dataType) (branchAt : branches[tag.index]? = some branch)
      (constructor : branch.constructor = tag)
      (sourceArity : metadata.payloadTypes.length = sources.length)
      (coreArity : branch.payloadTypes.length = values.length)
      (sourceAt : Dynamic.ValueAt sources index sourceChild) (coreAt : values[index]? = some valueChild)
      (tail : Tree checked signatures identities prepared keys replacementSource replacement childRelation
        sourceChild valueChild steps projections updatedChild count)
      (represented : ∀ child, childRelation updatedChild child →
        relation (.constructed metadata (sources.set index updatedChild))
          (.constructed tag (packValues (values.set index child)))) :
      Tree checked signatures identities prepared keys replacementSource replacement relation
        (.constructed metadata sources) (.constructed tag (packValues values))
        (.member dataType index branches fieldType :: steps) (.member name index :: projections)
        (.constructed metadata (sources.set index updatedChild)) count
  | mapping {sourceKeyType sourceValueType : TypeSystem.Ty} {index : PreparedIndex}
      (certificate : Index checked sourceValueType index)
      {relation valueRelation : OrderedMapping.Relation} {sourceKey sourceChild updatedChild : Dynamic.Value}
      {key : Value} {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
      {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (keyRep : KeyRep certificate signatures identities sourceKey key)
      (keyAt : keys[index.keyPosition]? = some key)
      (entriesRep : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRelation sources entries)
      (selected : Reads sourceKey sources sourceValueType sourceChild)
      (tail : ∀ value, (valueRelation sourceChild value ∨
          ∃ expression, DataDefaults.Tree checked.catalog sourceValueType sourceChild value expression) →
        Tree checked signatures identities prepared keys replacementSource replacement valueRelation
          sourceChild value steps projections updatedChild count)
      (inserted : Dynamic.MappingInsert sourceKey updatedChild sources updated)
      (represented : ∀ value, OrderedMapping.ValueRel index.layout
          (KeyRep certificate signatures identities) valueRelation updated value →
        relation (.mapping sourceKeyType sourceValueType updated) value) :
      Tree checked signatures identities prepared keys replacementSource replacement relation
        (.mapping sourceKeyType sourceValueType sources) (Core.OrderedMapping.encode index.layout entries)
        (.index index :: steps) (.index sourceKey :: projections) (.mapping sourceKeyType sourceValueType updated)
        (2 * (checked.catalog.entries.length + 1) + count)

private theorem replaceAt {values : List Dynamic.Value} {index : Nat} {previous : Dynamic.Value}
    (selected : Dynamic.ValueAt values index previous) (replacement : Dynamic.Value) :
    Dynamic.ValuesReplaceAt values index replacement (values.set index replacement) := by
  induction selected with
  | head => exact .head
  | tail _ ih => exact .tail ih

private theorem projectPacked_weaken (types : List Ty) (index : Nat) (expression : Expr) :
    SourceCoreDataExpressions.projectPacked index types (expression.weakenAt 0) =
      (SourceCoreDataExpressions.projectPacked index types expression).weakenAt 0 := by
  induction types generalizing index expression with
  | nil => simp [SourceCoreDataExpressions.projectPacked, Expr.weakenAt]
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons next rest =>
      by_cases zero : index = 0
      · simp [SourceCoreDataExpressions.projectPacked, zero, Expr.weakenAt]
      · simpa [SourceCoreDataExpressions.projectPacked, zero, Expr.weakenAt] using ih (index - 1) (.second expression)

theorem Tree.preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {prepared : Prepared} {keys : List Value}
    {replacementSource : Dynamic.Value} {replacement : Value} {relation : OrderedMapping.Relation}
    {source : Dynamic.Value} {value : Value} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {updatedSource : Dynamic.Value} {count : Nat}
    (tree : Tree checked signatures identities prepared keys replacementSource replacement relation source value steps projections updatedSource count)
    (faithful : IdentityFaithful identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (type : Ty) (current keyExpression replacementExpression : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ updatedValue finalStore administrative,
      Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some source) projections updatedSource ∧
      relation updatedSource updatedValue ∧
      Evaluates environment store (update prepared steps type current keyExpression replacementExpression)
        (.inRight .word updatedValue) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  induction tree generalizing environment store type current keyExpression replacementExpression with
  | leaf represented =>
    exact ⟨_, store, [], .leaf rfl, represented, .inRight (replacementSelected.evaluates store), by simp, rfl⟩
  | @member relation childRelation metadata tag sources values branch dataType index branches fieldType name sourceChild updatedChild valueChild steps projections count authenticated owner branchAt constructor sourceArity coreArity sourceAt coreAt tail represented ih =>
    obtain ⟨child, finalStore, administrative, changed, childRep, evaluated, extended, counted⟩ :=
      ih (packValues values :: environment) store fieldType _ (shift 1 keyExpression) (shift 1 replacementExpression)
        (projectPacked_selects (Selects.var (index := 0) rfl) coreArity index coreAt)
        (by simpa [shift] using keysSelected.weaken (packValues values))
        (by simpa [shift] using replacementSelected.weaken (packValues values))
    refine ⟨_, finalStore, administrative, .member sourceAt changed (replaceAt sourceAt updatedChild), represented child childRep,
      Evaluates.matchData (selected.evaluates store) owner
        (by simp only [List.getElem?_map, branchAt, Option.map_some]; rfl) ?_, extended, counted⟩
    apply LanguageResult.bind_success _ evaluated
    rw [constructor]
    exact .inRight (.construct (DataPlaceMembers.replacePacked_evaluates coreArity (.var rfl) (.var rfl)))
  | @mapping sourceKeyType sourceValueType index certificate relation valueRelation sourceKey sourceChild updatedChild key sources updated entries steps projections count keyRep keyAt entriesRep read tail inserted represented ih =>
    have keySelected := projectPacked_selects keysSelected keyLength index.keyPosition keyAt
    obtain ⟨child, childRep, childEvaluated⟩ := selectedIndex_preserves certificate prepared faithful keyRep entriesRep read
      environment store current keyExpression selected keySelected
    obtain ⟨updatedChild, childStore, childCells, changed, updatedRep, tailEvaluated, childExtended, childCounted⟩ :=
      ih child childRep (child :: environment) _ index.layout.valueType (.var 0)
        (shift 1 keyExpression) (shift 1 replacementExpression) (.var rfl)
        (by simpa [shift] using keysSelected.weaken child)
        (by simpa [shift] using replacementSelected.weaken child)
    obtain ⟨updatedValue, valueRep, insertEvaluated⟩ := DataMappingComparison.insert_preserves certificate.comparison index.layout
      certificate.keyType faithful keyRep updatedRep entriesRep inserted (updatedChild :: child :: environment) childStore
      (shift 2 current) (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keyExpression)) (.var 0)
      (by simpa [shift, List.range_succ] using (selected.weaken child).weaken updatedChild)
      (by simpa [shift, List.range_succ, projectPacked_weaken] using (keySelected.weaken child).weaken updatedChild) (.var rfl)
    obtain ⟨before, beforeExtended, beforeCounted⟩ := selectedStore_extension certificate environment store entries key
    obtain ⟨after, afterExtended, afterCounted⟩ := DataMappingComparison.helper_store_extension certificate.comparison
      (updatedChild :: child :: environment) childStore _ _ _ _
    refine ⟨updatedValue, DataMappingComparison.insertStore certificate.comparison index.layout
      (updatedChild :: child :: environment) childStore entries key updatedChild, before ++ childCells ++ after, ?_, represented updatedValue valueRep,
      LanguageResult.bind_success _ childEvaluated (LanguageResult.bind_success _ tailEvaluated ?_), ?_, ?_⟩
    · cases read with
      | found lookup => exact .indexFound lookup changed inserted
      | default absent defaulted => exact .indexDefault absent defaulted changed inserted
    · simpa only [certificate.comparisonExpression] using insertEvaluated
    · change DataMappingComparison.insertStore _ _ _ _ _ _ _ = _
      rw [show DataMappingComparison.insertStore _ _ _ _ _ _ _ = _ from afterExtended,
        childExtended, beforeExtended]
      simp only [List.append_assoc]
    · simp only [List.length_append, beforeCounted, childCounted, afterCounted]
      omega

end Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTree
