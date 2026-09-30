import Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths

/-! Independent source missing-default faults determine the actual generated
read/update failures. Child evaluations are derived from complete payloads and
static helper receipts; no replacement expression is evaluated on this path. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceMappingIndex DataPlaceMembers DataEquality

private theorem comptime_parts {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {inner : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep catalog signatures functions mapping world (.comptime inner) source value type) :
    ValueRep catalog signatures functions mapping world inner source value type := by
  cases represented with
  | comptime inner => exact inner
  | constructed nominal => simp [SourceCoreDataCatalog.nominalParts] at nominal

theorem Path.fault_preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (path : Path checked signatures functions mapping world keys root type steps projections leaf leafType count)
    {source : Dynamic.Value} {value : Value} {reason : Dynamic.SemanticFault}
    (represented : ValueRep checked.catalog signatures functions mapping world root source value type)
    (fault : Dynamic.ProjectionsFaults (some source) projections reason)
    (environment : Environment) (store : Store) (current keyExpression replacementExpression : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ token finalStore administrative,
      Evaluates environment store (select prepared steps current keyExpression)
        (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      Evaluates environment store (update prepared steps type current keyExpression replacementExpression)
        (.inLeft type (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length ≤ count := by
  induction path generalizing source value environment store current keyExpression replacementExpression with
  | nil projected => cases fault
  | @member root field leaf dataType index branches fieldType leafType name steps projections count layout fieldProjected tail ih =>
    obtain ⟨declaration, arguments, nominal⟩ := layout.nominal
    obtain ⟨metadata, tag, sources, values, types, sourceEq, valueEq, typeEq, result, authenticated, registered, payloads⟩ :=
      represented.nominal_parts nominal
    subst source; subst value
    obtain ⟨owner, branch, branchAt, constructor, fieldAt, arity⟩ := layout.constructors metadata tag result authenticated
    obtain ⟨sourceChild, valueChild, childType, sourceAt, coreAt, coreTypeAt, childRep⟩ := payloads.at fieldAt
    have childTypeEq := Except.ok.inj (childRep.projection.symm.trans fieldProjected)
    subst childType
    cases fault with
    | member selectedAt fault =>
      have same := sourceAt.functional selectedAt
      subst sourceChild
      obtain ⟨token, finalStore, admin, readEval, updateEval, extended, counted⟩ :=
        ih childRep fault (packValues values :: environment) store _ (shift 1 keyExpression) (shift 1 replacementExpression)
          (projectPacked_selects (Selects.var (index := 0) rfl) (arity.trans payloads.length.2.1) index coreAt)
          (by simpa [shift] using keysSelected.weaken (packValues values))
      refine ⟨token, finalStore, admin, ?_, ?_, extended, counted⟩
      · exact .matchData (selected.evaluates store) owner
          (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl) readEval
      · exact .matchData (selected.evaluates store) owner
          (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl)
          (LanguageResult.bind_failure _ updateEval)
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
    have keySelected := projectPacked_selects keysSelected keyLength index.keyPosition keyAt
    have finish {sourceChild : Dynamic.Value} (read : Reads sourceKey sources valueType sourceChild)
        (fault : Dynamic.ProjectionsFaults (some sourceChild) projections reason) :
        ∃ token finalStore administrative,
          Evaluates environment store (select prepared (.index index :: steps) current keyExpression)
            (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
          Evaluates environment store (update prepared (.index index :: steps) index.layout.type current keyExpression replacementExpression)
            (.inLeft index.layout.type (.word token)) finalStore ∧
          finalStore = store ++ administrative ∧ administrative.length ≤ checked.catalog.entries.length + 1 + count := by
      obtain ⟨child, childRep, childEvaluated⟩ := selectedIndex_preserves certificate prepared faithful keyObserved entriesObserved read
        environment store current keyExpression selected keySelected
      have completeChild : ValueRep checked.catalog signatures functions mapping world valueType sourceChild child index.layout.valueType := by
        rcases childRep with childRep | ⟨expression, defaulted⟩
        · exact childRep
        · exact default_represents_at layouts valueProjected defaulted
      obtain ⟨token, finalStore, after, readEval, updateEval, extended, counted⟩ :=
        ih completeChild fault (child :: environment) _ (.var 0) (shift 1 keyExpression) (shift 1 replacementExpression)
          (.var rfl) (by simpa [shift] using keysSelected.weaken child)
      obtain ⟨before, beforeExtended, beforeCounted⟩ := selectedStore_extension certificate environment store entries key
      refine ⟨token, finalStore, before ++ after, LanguageResult.bind_success _ childEvaluated readEval,
        LanguageResult.bind_success _ childEvaluated (LanguageResult.bind_failure _ updateEval), ?_, ?_⟩
      · rw [extended, beforeExtended, List.append_assoc]
      · simp only [List.length_append, beforeCounted]; omega
    cases fault with
    | indexDefaultUnavailable keyType absent unavailable =>
      have evaluated := selectedIndex_missing certificate prepared faithful keyObserved entriesObserved absent unavailable
        environment store current keyExpression selected keySelected
      obtain ⟨admin, extended, counted⟩ := selectedStore_extension certificate environment store entries key
      exact ⟨index.missing, _, admin, LanguageResult.bind_failure _ evaluated,
        LanguageResult.bind_failure _ evaluated, extended, by rw [counted]; omega⟩
    | indexFound keyType found fault => exact finish (.found found) fault
    | indexDefault keyType absent defaulted fault => exact finish (.default absent defaulted) fault
  | comptime tail ih =>
    exact ih (comptime_parts represented) fault environment store current keyExpression replacementExpression selected keysSelected

end Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
