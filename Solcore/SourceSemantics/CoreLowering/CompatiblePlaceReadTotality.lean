import Solcore.SourceSemantics.CoreLowering.CompatiblePathReads
import Solcore.SourceSemantics.CoreLowering.CompatiblePathFaults
import Solcore.SourceSemantics.CoreLowering.CompatiblePayloadRuntimeTypes

/-! Independent total path selection on authenticated compatible payloads.
Runtime-compatible raw aliases retain their metadata, ordered entries and raw
default. Actual native helpers are not premises: this source classification
will construct their finite semantic trees and reflect completed executions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceReadTotality
open Core Frontend SourceInference GeneralHeap DataPatternValues
open CompatiblePayload CompatibleEquality CompatibleMixedRoute CompatibleMapping CompatibleMapping.MixedPaths SourceCoreCompatibleDataPlaces

private theorem source_mapping {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {key result}, SourceCoreRawMetadata.runtimeType sourceType = .mapping key result →
      ∃ rawKey rawResult entries, source = .mapping rawKey rawResult entries := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | function | proxy => intro _ _ impossible; cases impossible
  | constructed metadata =>
    intro key result view
    have facts := CompatibleConstructorMetadata.facts metadata.authenticated
    cases facts with
    | mk signature constructor arguments _ _ _ _ _ resultType =>
      rw [resultType, CompatibleConstructorMetadata.runtimeType_nominal] at view
      have impossible := congrArg SourceCoreDataCatalog.nominalParts view
      simp only [DataPatternAuthenticity.nominalParts_nominal, SourceCoreDataCatalog.nominalParts, reduceCtorEq] at impossible
  | mappingValue => intro _ _ _; exact ⟨_, _, _, rfl⟩
  | compatible same _ ih => intro _ _ view; exact ih (same.symm.trans view)
  | nil | cons | empty | entry | absent | present => trivial

private theorem source_constructor {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {owner arguments}, SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType sourceType) = some (owner, arguments) →
      ∃ metadata payloads, source = .constructed metadata payloads := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | function | proxy | mappingValue => intro _ _ impossible; cases impossible
  | constructed => intro _ _ _; exact ⟨_, _, rfl⟩
  | compatible same _ ih => intro _ _ view; exact ih (by rw [← same]; exact view)
  | nil | cons | empty | entry | absent | present => trivial

/-- Every represented root and key vector selects one represented leaf or
produces an independent missing-default fault. Function leaves require only
the explicit shallow metadata law, not any function-body evaluation. -/
theorem read_or_fault {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {keys : List Value}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keySites leaf}
    {resolved : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    (functionTypes : FunctionRuntimeViews functions)
    {current : Dynamic.Value} {value : Value} {type leafCore : Ty}
    (represented : ValueRep checked registry functions mapping world root current value type)
    (leafProjected : checked.catalog.project leaf = .ok leafCore) :
    (∃ selected native, Dynamic.ProjectionsRead (some current) resolved (some selected) ∧
      ValueRep checked registry functions mapping world leaf selected native leafCore) ∨
    ∃ reason, Dynamic.ProjectionsFaults (some current) resolved reason := by
  induction arguments generalizing current value type with
  | nil =>
    have same := Except.ok.inj (represented.projection.symm.trans leafProjected)
    exact .inl ⟨current, value, .nil, same ▸ represented⟩
  | @member root field leaf name index signature typeArguments identity branches fieldType projections steps position keySites nominal selectedSignature certificate tail resolved arguments ih =>
    obtain ⟨metadata, payloads, rfl⟩ := source_constructor represented nominal
    obtain ⟨tag, id, values, types, _, _, fields⟩ := constructor_fields represented rfl
    obtain ⟨owner, branch, actual, child, native, branchAt, constructor, branchTypes,
      sourceField, view, coreField, found, coreAt, childRelated⟩ := certificate.select nominal selectedSignature fields
    rcases ih (.compatible view.symm childRelated) leafProjected with ⟨selected, output, read, related⟩ | ⟨reason, fault⟩
    · exact .inl ⟨selected, output, .member found read, related⟩
    · exact .inr ⟨reason, .member found fault⟩
  | @index root keySource valueSource leaf key layout projections steps position keySites comparison missing certificate generated tail lookup keyValue resolved keyAt keyRelated arguments ih =>
    obtain ⟨rawKey, rawValue, entries, rfl⟩ := source_mapping represented certificate.view
    obtain ⟨header, nativeEntries, fallback, _, _, keyView, valueView, fields⟩ := certificate.mappingFields represented
    have rawKeyRelated : ValueRep checked registry functions mapping world rawKey lookup keyValue layout.keyType :=
      .compatible (by rw [keyView, SourceCoreRawMetadata.runtimeType_idempotent]) keyRelated
    have typed := rawKeyRelated.source_runtimeView functionTypes
    have finish {child : Dynamic.Value} (selected : Selected lookup entries rawValue child) :
        (∃ selected native, Dynamic.ProjectionsRead (some (.mapping rawKey rawValue entries)) (.index lookup :: resolved) (some selected) ∧
          ValueRep checked registry functions mapping world leaf selected native leafCore) ∨
        ∃ reason, Dynamic.ProjectionsFaults (some (.mapping rawKey rawValue entries)) (.index lookup :: resolved) reason := by
      obtain ⟨native, related⟩ := CompatibleMixedRoute.Selected.represented fields selected
      have childRelated : ValueRep checked registry functions mapping world valueSource child native layout.valueType :=
        .compatible (by rw [valueView, SourceCoreRawMetadata.runtimeType_idempotent]) related
      rcases ih childRelated leafProjected with ⟨selectedValue, output, read, result⟩ | ⟨reason, fault⟩
      · refine .inl ⟨selectedValue, output, ?_, result⟩
        cases selected with
        | found found => exact .indexFound found read
        | default absent defaulted => exact .indexDefault absent defaulted read
      · refine .inr ⟨reason, ?_⟩
        cases selected with
        | found found => exact .indexFound typed found fault
        | default absent defaulted => exact .indexDefault typed absent defaulted fault
    obtain ⟨found, classification⟩ := lookup_total lookup entries
    cases classification with
    | found found => exact finish (.found found)
    | absent absent =>
      cases fields.default with
      | absent missing => exact .inr ⟨_, .indexDefaultUnavailable typed absent missing⟩
      | present defaulted related => exact finish (.default absent defaulted)

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceReadTotality
