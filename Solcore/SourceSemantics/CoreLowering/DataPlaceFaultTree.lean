import Solcore.SourceSemantics.CoreLowering.DataPlacePathHelpers

/-! Missing-default faults through mixed paths. Selection and update stop at
the first fault; no enclosing insertion or source-cell write runs afterwards.
All children and helper initializers are derived from structural certificates. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceFaultTree
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPatternValues DataPlaceMappingIndex

inductive Tree (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (identities : Dynamic.Value → Word → Prop) (prepared : Prepared) (keys : List Value) :
    Dynamic.Value → Value → Ty → List PreparedStep → List Dynamic.EvaluatedProjection →
      Dynamic.SemanticFault → Word → Nat → Prop where
  | missing {sourceKeyType sourceValueType : TypeSystem.Ty} {index : PreparedIndex}
      (certificate : Index checked sourceValueType index)
      {valueRelation : OrderedMapping.Relation} {sourceKey : Dynamic.Value} {key : Value}
      {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
      {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection}
      (keyRep : KeyRep certificate signatures identities sourceKey key)
      (keyType : Dynamic.ValueRuntimeType sourceKey sourceKeyType) (keyAt : keys[index.keyPosition]? = some key)
      (entriesRep : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRelation sources entries)
      (absent : Dynamic.MappingAbsent sourceKey sources) (unavailable : ¬ Dynamic.Defaultable sourceValueType) :
      Tree checked signatures identities prepared keys
        (.mapping sourceKeyType sourceValueType sources) (Core.OrderedMapping.encode index.layout entries) index.layout.type
        (.index index :: steps) (.index sourceKey :: projections) (.missingMappingDefault sourceValueType) index.missing
        (checked.catalog.entries.length + 1)
  | member {metadata : DataConstructorInstantiation} {tag : ConstructorId}
      {sources : List Dynamic.Value} {values : List Value} {branch : MemberBranch}
      {dataType : DataTypeId} {index : Nat} {branches : List MemberBranch} {fieldType : Ty} {name : String}
      {sourceChild : Dynamic.Value} {valueChild : Value} {steps : List PreparedStep}
      {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
      (authenticated : checked.catalog.resolveConstructor signatures metadata = .ok tag)
      (owner : tag.owner = dataType) (branchAt : branches[tag.index]? = some branch)
      (sourceArity : metadata.payloadTypes.length = sources.length)
      (coreArity : branch.payloadTypes.length = values.length)
      (sourceAt : Dynamic.ValueAt sources index sourceChild) (coreAt : values[index]? = some valueChild)
      (tail : Tree checked signatures identities prepared keys sourceChild valueChild fieldType steps projections reason token count) :
      Tree checked signatures identities prepared keys
        (.constructed metadata sources) (.constructed tag (packValues values)) (.namedData dataType)
        (.member dataType index branches fieldType :: steps) (.member name index :: projections) reason token count
  | mapping {sourceKeyType sourceValueType : TypeSystem.Ty} {index : PreparedIndex}
      (certificate : Index checked sourceValueType index)
      {valueRelation : OrderedMapping.Relation} {sourceKey sourceChild : Dynamic.Value}
      {key : Value} {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
      {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection}
      {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
      (keyRep : KeyRep certificate signatures identities sourceKey key)
      (keyType : Dynamic.ValueRuntimeType sourceKey sourceKeyType) (keyAt : keys[index.keyPosition]? = some key)
      (entriesRep : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRelation sources entries)
      (selected : Reads sourceKey sources sourceValueType sourceChild)
      (tail : ∀ value, (valueRelation sourceChild value ∨
          ∃ expression, DataDefaults.Tree checked.catalog sourceValueType sourceChild value expression) →
        Tree checked signatures identities prepared keys sourceChild value index.layout.valueType steps projections reason token count) :
      Tree checked signatures identities prepared keys
        (.mapping sourceKeyType sourceValueType sources) (Core.OrderedMapping.encode index.layout entries) index.layout.type
        (.index index :: steps) (.index sourceKey :: projections) reason token
        (checked.catalog.entries.length + 1 + count)

/-- Reading and reconstruction observe the same first unavailable default.
The arbitrary replacement is never inspected along this failing path. -/
theorem Tree.preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {prepared : Prepared} {keys : List Value}
    {source : Dynamic.Value} {value : Value} {type : Ty} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
    (tree : Tree checked signatures identities prepared keys source value type steps projections reason token count)
    (faithful : IdentityFaithful identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (current keyExpression replacement : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ finalStore administrative,
      Dynamic.ProjectionsFaults (some source) projections reason ∧
      Evaluates environment store (select prepared steps current keyExpression)
        (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      Evaluates environment store (update prepared steps type current keyExpression replacement)
        (.inLeft type (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  induction tree generalizing environment store current keyExpression replacement with
  | @missing sourceKeyType sourceValueType index certificate valueRelation sourceKey key sources entries steps projections keyRep keyType keyAt entriesRep absent unavailable =>
    have evaluated := selectedIndex_missing certificate prepared faithful keyRep entriesRep absent unavailable
      environment store current keyExpression selected (projectPacked_selects keysSelected keyLength index.keyPosition keyAt)
    obtain ⟨administrative, extended, counted⟩ := selectedStore_extension certificate environment store entries key
    exact ⟨_, administrative, .indexDefaultUnavailable keyType absent unavailable,
      LanguageResult.bind_failure _ evaluated, LanguageResult.bind_failure _ evaluated, extended, counted⟩
  | @member metadata tag sources values branch dataType index branches fieldType name sourceChild valueChild steps projections reason token count authenticated owner branchAt sourceArity coreArity sourceAt coreAt tail ih =>
    obtain ⟨finalStore, administrative, fault, readEvaluation, updateEvaluation, extended, counted⟩ :=
      ih (packValues values :: environment) store _ (shift 1 keyExpression) (shift 1 replacement)
        (projectPacked_selects (Selects.var (index := 0) rfl) coreArity index coreAt)
        (by simpa [shift] using keysSelected.weaken (packValues values))
    refine ⟨finalStore, administrative, .member sourceAt fault, ?_, ?_, extended, counted⟩
    · exact .matchData (selected.evaluates store) owner
        (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl) readEvaluation
    · exact .matchData (selected.evaluates store) owner
        (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl)
        (LanguageResult.bind_failure _ updateEvaluation)
  | @mapping sourceKeyType sourceValueType index certificate valueRelation sourceKey sourceChild key sources entries steps projections reason token count keyRep keyType keyAt entriesRep read tail ih =>
    obtain ⟨child, represented, evaluated⟩ := selectedIndex_preserves certificate prepared faithful keyRep entriesRep read
      environment store current keyExpression selected (projectPacked_selects keysSelected keyLength index.keyPosition keyAt)
    obtain ⟨finalStore, after, fault, readEvaluation, updateEvaluation, extended, counted⟩ :=
      ih child represented (child :: environment) _ (.var 0) (shift 1 keyExpression) (shift 1 replacement) (.var rfl)
        (by simpa [shift] using keysSelected.weaken child)
    obtain ⟨before, beforeExtended, beforeCounted⟩ := selectedStore_extension certificate environment store entries key
    refine ⟨finalStore, before ++ after, ?_, LanguageResult.bind_success _ evaluated readEvaluation,
      LanguageResult.bind_success _ evaluated (LanguageResult.bind_failure _ updateEvaluation), ?_, ?_⟩
    · cases read with
      | found lookup => exact .indexFound keyType lookup fault
      | default absent defaulted => exact .indexDefault keyType absent defaulted fault
    · rw [extended, beforeExtended, List.append_assoc]
    · simp only [List.length_append, beforeCounted, counted]

end Solcore.SourceSemantics.CoreLowering.DataPlaceFaultTree
