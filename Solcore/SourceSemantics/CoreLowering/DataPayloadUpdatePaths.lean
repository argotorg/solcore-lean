import Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths

/-! Complete payload preservation for the actual recursive place updater.
The induction follows static path receipts and independent source updates.
Comparison/default/recursive Core evaluations are all derived internally;
strong key authentication is retained when reconstructing mappings. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceMappingIndex DataPlaceMembers DataEquality

private theorem replacement_set {sources : List Dynamic.Value} {index : Nat} {replacement : Dynamic.Value}
    {updated : List Dynamic.Value} (changed : Dynamic.ValuesReplaceAt sources index replacement updated) :
    updated = sources.set index replacement := by
  induction changed with
  | head => rfl
  | tail _ ih => simp [List.set, ih]

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

private theorem comptime_parts {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {inner : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep catalog signatures functions mapping world (.comptime inner) source value type) :
    ValueRep catalog signatures functions mapping world inner source value type := by
  cases represented with
  | comptime inner => exact inner
  | constructed nominal => simp [SourceCoreDataCatalog.nominalParts] at nominal

theorem Path.update_preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (path : Path checked signatures functions mapping world keys root type steps projections leaf leafType count)
    {source updatedSource replacementSource : Dynamic.Value} {value replacement : Value}
    (represented : ValueRep checked.catalog signatures functions mapping world root source value type)
    (replacementRep : ValueRep checked.catalog signatures functions mapping world leaf replacementSource replacement leafType)
    (changed : Dynamic.ProjectionsUpdate (fun _ new => new = replacementSource) (some source) projections updatedSource)
    (environment : Environment) (store : Store) (current keyExpression replacementExpression : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ updatedValue finalStore administrative,
      ValueRep checked.catalog signatures functions mapping world root updatedSource updatedValue type ∧
      Evaluates environment store (update prepared steps type current keyExpression replacementExpression)
        (.inRight .word updatedValue) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = 2 * count := by
  induction path generalizing source value updatedSource environment store current keyExpression replacementExpression with
  | nil projected =>
    cases changed with
    | leaf modified => subst updatedSource; exact ⟨_, store, [], replacementRep, .inRight (replacementSelected.evaluates store), by simp, rfl⟩
  | @member root field leaf dataType index branches fieldType leafType name steps projections count layout fieldProjected tail ih =>
    obtain ⟨declaration, arguments, nominal⟩ := layout.nominal
    obtain ⟨metadata, tag, sources, values, types, sourceEq, valueEq, typeEq, result, authenticated, registered, payloads⟩ :=
      represented.nominal_parts nominal
    subst source; subst value
    obtain ⟨owner, branch, branchAt, constructor, fieldAt, arity⟩ := layout.constructors metadata tag result authenticated
    obtain ⟨sourceChild, valueChild, childType, sourceAt, coreAt, coreTypeAt, childRep⟩ := payloads.at fieldAt
    have childTypeEq := Except.ok.inj (childRep.projection.symm.trans fieldProjected)
    subst childType
    cases changed with
    | member selectedAt changed replaced =>
      have same := sourceAt.functional selectedAt
      subst sourceChild
      obtain ⟨child, finalStore, administrative, updatedRep, evaluated, extended, counted⟩ :=
        ih childRep replacementRep changed (packValues values :: environment) store _ (shift 1 keyExpression) (shift 1 replacementExpression)
          (projectPacked_selects (Selects.var (index := 0) rfl) (arity.trans payloads.length.2.1) index coreAt)
          (by simpa [shift] using keysSelected.weaken (packValues values))
          (by simpa [shift] using replacementSelected.weaken (packValues values))
      rw [replacement_set replaced]
      have reconstructed := DataPayload.ValueRep.constructed nominal result authenticated
        (by simpa only [owner] using represented.projection) registered
        (payloads.replace fieldAt coreTypeAt updatedRep)
      refine ⟨.constructed tag (packValues (values.set index child)), finalStore, administrative, ?_, ?_, extended, counted⟩
      · simpa only [owner] using reconstructed
      · apply Evaluates.matchData (selected.evaluates store) owner
          (by simp only [List.getElem?_map, branchAt, Option.map_some]; rfl)
        apply LanguageResult.bind_success _ evaluated
        rw [constructor]
        exact .inRight (.construct (replacePacked_evaluates (arity.trans payloads.length.2.1) (.var rfl) (.var rfl)))
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
    have finish {sourceChild updatedChild : Dynamic.Value} {updatedEntries : List (Dynamic.Value × Dynamic.Value)}
        (read : Reads sourceKey sources valueType sourceChild)
        (changed : Dynamic.ProjectionsUpdate (fun _ new => new = replacementSource) (some sourceChild) projections updatedChild)
        (inserted : Dynamic.MappingInsert sourceKey updatedChild sources updatedEntries) :
        ∃ updatedValue finalStore administrative,
          ValueRep checked.catalog signatures functions mapping world (.mapping keyType valueType)
            (.mapping keyType valueType updatedEntries) updatedValue index.layout.type ∧
          Evaluates environment store (update prepared (.index index :: steps) index.layout.type current keyExpression replacementExpression)
            (.inRight .word updatedValue) finalStore ∧
          finalStore = store ++ administrative ∧ administrative.length = 2 * (checked.catalog.entries.length + 1 + count) := by
      obtain ⟨child, childRep, childEvaluated⟩ := selectedIndex_preserves certificate prepared faithful keyObserved entriesObserved read
        environment store current keyExpression selected keySelected
      have completeChild : ValueRep checked.catalog signatures functions mapping world valueType sourceChild child index.layout.valueType := by
        rcases childRep with childRep | ⟨expression, defaulted⟩
        · exact childRep
        · exact default_represents_at layouts valueProjected defaulted
      obtain ⟨updatedChild, childStore, childCells, updatedRep, tailEvaluated, childExtended, childCounted⟩ :=
        ih completeChild replacementRep changed (child :: environment) _ (.var 0)
          (shift 1 keyExpression) (shift 1 replacementExpression) (.var rfl)
          (by simpa [shift] using keysSelected.weaken child)
          (by simpa [shift] using replacementSelected.weaken child)
      obtain ⟨updatedValue, valueRep, insertEvaluated⟩ := DataPayload.insert_preserves observations faithful certificate.comparison
        index.layout certificate.keyType identity keyProjected valueProjected registered keyRelated updatedRep contents inserted
        (updatedChild :: child :: environment) childStore (shift 2 current)
        (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keyExpression)) (.var 0)
        (by simpa [shift, List.range_succ] using (selected.weaken child).weaken updatedChild)
        (by simpa [shift, List.range_succ, projectPacked_weaken] using (keySelected.weaken child).weaken updatedChild) (.var rfl)
      obtain ⟨before, beforeExtended, beforeCounted⟩ := selectedStore_extension certificate environment store entries key
      obtain ⟨after, afterExtended, afterCounted⟩ := DataMappingComparison.helper_store_extension certificate.comparison
        (updatedChild :: child :: environment) childStore _ _ _ _
      refine ⟨updatedValue, DataMappingComparison.insertStore certificate.comparison index.layout
        (updatedChild :: child :: environment) childStore entries key updatedChild, before ++ childCells ++ after, valueRep,
        LanguageResult.bind_success _ childEvaluated (LanguageResult.bind_success _ tailEvaluated ?_), ?_, ?_⟩
      · simpa only [certificate.comparisonExpression] using insertEvaluated
      · change DataMappingComparison.insertStore _ _ _ _ _ _ _ = _
        rw [show DataMappingComparison.insertStore _ _ _ _ _ _ _ = _ from afterExtended, childExtended, beforeExtended]
        simp only [List.append_assoc]
      · simp only [List.length_append, beforeCounted, afterCounted, childCounted]
        omega
    cases changed with
    | indexFound found changed inserted => exact finish (.found found) changed inserted
    | indexDefault absent defaulted changed inserted => exact finish (.default absent defaulted) changed inserted
  | comptime tail ih =>
    obtain ⟨output, finalStore, admin, represented, evaluated, extended, counted⟩ :=
      ih (comptime_parts represented) replacementRep changed environment store current keyExpression replacementExpression selected keysSelected replacementSelected
    exact ⟨output, finalStore, admin, .comptime represented, evaluated, extended, counted⟩

end Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
