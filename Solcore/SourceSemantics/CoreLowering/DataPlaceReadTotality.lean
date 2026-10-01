import Solcore.SourceSemantics.CoreLowering.DataPlaceRouteCertificates
import Solcore.SourceSemantics.CoreLowering.DataPayloadRuntimeTypes
import Solcore.SourceSemantics.CoreLowering.DataPayloadFaultPaths

/-! Independent source read-or-fault totality for authenticated compiled paths.
It follows source ordered mappings and actual default-generation receipts,
without assuming either a source projection trace or a Core helper execution.
This is the semantic existence step needed for finite-execution reflection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceReadTotality
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceRouteCertificates

/-- First source match or source absence, with the selected full payload.
Equivalence deliberately need not be reflexive for function/mapping keys. -/
theorem entries_lookup_or_absent {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {keyType valueType : TypeSystem.Ty} {keyCore valueCore : Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {entries : Core.OrderedMapping.Entries}
    (related : EntriesRep catalog signatures functions mapping world keyType valueType keyCore valueCore sources entries)
    (key : Dynamic.Value) :
    (∃ selected value, Dynamic.MappingLookup key sources selected ∧
      ValueRep catalog signatures functions mapping world valueType selected value valueCore) ∨
      Dynamic.MappingAbsent key sources := by
  classical
  induction sources generalizing entries with
  | nil => cases related; exact .inr .nil
  | cons sourceEntry sources ih =>
    obtain ⟨sourceKey, sourceValue⟩ := sourceEntry
    cases related with
    | prepend keyRelated valueRelated rest =>
      by_cases equivalent : Dynamic.ValueEquivalent key sourceKey
      · exact .inl ⟨sourceValue, _, .head equivalent, valueRelated⟩
      · rcases ih rest with ⟨selected, core, found, represented⟩ | absent
        · exact .inl ⟨selected, core, .tail equivalent found, represented⟩
        · exact .inr (.cons equivalent absent)

/-- Every authenticated mixed route either selects a fully represented source
value or produces the independent missing-default fault. The initial root is
present here; absent ordinary roots and virtual mappings are handled by the
separate root normalization rules. -/
theorem read_or_fault {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {root leaf : TypeSystem.Ty} {rootType leafType : Ty} {steps : List Step}
    {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source root rootType steps projections leaf leafType sourceTypes)
    {fuel position : Nat} {missing : TypeSystem.Ty → Word} {preparedSteps : List PreparedStep}
    {preparedKeys : List (ExpressionId × Ty)} {sources : List Dynamic.Value} {values : List Value}
    {evaluated : List Dynamic.EvaluatedProjection} {coreTypes : List Ty}
    (prepared : DataPlaceMappingPreparation.Steps checked fuel missing position steps preparedSteps preparedKeys)
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    {sourceRoot : Dynamic.Value} {coreRoot : Value}
    (rootRelated : ValueRep checked.catalog signatures functions mapping world root sourceRoot coreRoot rootType) :
    (∃ selected value, Dynamic.ProjectionsRead (some sourceRoot) evaluated (some selected) ∧
      ValueRep checked.catalog signatures functions mapping world leaf selected value leafType) ∨
      ∃ reason, Dynamic.ProjectionsFaults (some sourceRoot) evaluated reason := by
  induction path generalizing position preparedSteps preparedKeys sources values evaluated coreTypes sourceRoot coreRoot with
  | nil projected => cases prepared; cases shaped; exact .inl ⟨_, _, .nil, rootRelated⟩
  | @member root field leaf dataType index name branches fieldType leafType steps rest types layout rootProjected fieldProjected tail ih =>
    cases prepared with
    | member prepared =>
      cases shaped with
      | member shaped =>
        obtain ⟨declaration, arguments, nominal⟩ := layout.nominal
        obtain ⟨metadata, tag, sourceFields, fields, fieldTypes, sourceEq, coreEq, typeEq,
          result, authenticated, registered, payloads⟩ := rootRelated.nominal_parts nominal
        subst sourceRoot
        obtain ⟨owner, branch, branchAt, constructor, fieldAt, arity⟩ := layout.constructors metadata tag result authenticated
        obtain ⟨sourceChild, coreChild, coreChildType, sourceAt, coreAt, typeAt, childRelated⟩ := payloads.at fieldAt
        have same := Except.ok.inj (childRelated.projection.symm.trans fieldProjected)
        subst coreChildType
        rcases ih prepared shaped keysRelated childRelated with ⟨selected, value, read, represented⟩ | ⟨reason, fault⟩
        · exact .inl ⟨selected, value, .member sourceAt read, represented⟩
        · exact .inr ⟨reason, .member sourceAt fault⟩
  | @index key value leaf layout id node steps rest leafType types identity erased keyProjected valueProjected found typed tail ih =>
    cases prepared with
    | @index _ _ _ _ entry sourceKey registeredValue comparison default _ _ _ selected mappingType comparisonGenerated defaultGenerated prepared =>
      cases shaped with
      | @index _ _ sourceKeyValue remainingValues evaluatedRest shaped =>
        cases keysRelated with
        | cons keyRelated keysRelated =>
          have keyRep : ValueRep checked.catalog signatures functions mapping world key _ _ _ := keyRelated
          have keyCanonical := (TypeSystem.Ty.mapping.inj erased).1
          have keyRuntime := (keyRep.source_runtimeType functionTypes keyCanonical).matches
          obtain ⟨entries, coreEntries, sourceEq, coreEq, identity, registered, contents⟩ :=
            rootRelated.mapping_parts layout keyProjected valueProjected
          subst sourceRoot
          have finish {sourceChild : Dynamic.Value} {coreChild : Value}
              (related : ValueRep checked.catalog signatures functions mapping world value sourceChild coreChild layout.valueType)
              (selected : DataPlaceMappingIndex.Reads sourceKeyValue entries value sourceChild) :
              (∃ selected coreResult, Dynamic.ProjectionsRead (some (.mapping key value entries))
                  (.index sourceKeyValue :: evaluatedRest) (some selected) ∧
                ValueRep checked.catalog signatures functions mapping world leaf selected coreResult leafType) ∨
                ∃ reason, Dynamic.ProjectionsFaults (some (.mapping key value entries))
                  (.index sourceKeyValue :: evaluatedRest) reason := by
            rcases ih prepared shaped keysRelated related with ⟨selectedValue, result, read, represented⟩ | ⟨reason, fault⟩
            · cases selected with
              | found lookup => exact .inl ⟨selectedValue, result, .indexFound lookup read, represented⟩
              | default absent defaulted => exact .inl ⟨selectedValue, result, .indexDefault absent defaulted read, represented⟩
            · cases selected with
              | found lookup => exact .inr ⟨reason, .indexFound keyRuntime lookup fault⟩
              | default absent defaulted => exact .inr ⟨reason, .indexDefault keyRuntime absent defaulted fault⟩
          rcases entries_lookup_or_absent contents _ with ⟨selected, core, lookup, represented⟩ | absent
          · exact finish represented (.found lookup)
          · obtain ⟨result, defaultMeaning, _⟩ := DataDefaults.prepared_preserves default [] []
            rw [DataPlaceMappingPreparation.default_sourceType defaultGenerated] at defaultMeaning
            cases defaultMeaning with
            | absent unavailable => exact .inr ⟨_, .indexDefaultUnavailable keyRuntime absent (by intro available; obtain ⟨v, defaulted⟩ := available.exists_default; exact unavailable v defaulted)⟩
            | present defaulted =>
              exact finish (default_represents_at layouts valueProjected defaulted) (.default absent defaulted.meaning)

end Solcore.SourceSemantics.CoreLowering.DataPlaceReadTotality
