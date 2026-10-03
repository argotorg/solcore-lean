import Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCertificateNativeTyping
import Solcore.Core.DefinitionExtension

/-! Successful compatible data encoding contains only structural data. Its
native typing can therefore be restricted from appended administrative
definitions to the actual catalog prefix. Catalog projection certifies the
type annotation independently; runtime type tags do not supply that fact.
Closures and references require a separate representation boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEncodedDataTyping
open Core Frontend
open SourceCoreCompatibleValues (encodeRaw encodePayloadsRaw encodeEntriesRaw encodeDefaultRaw)
open CompatibleEncoding (bind_ok mapError_ok)

/-- Structural data excludes executable closures and store references. Sum
annotations and constructor identities remain exactly those in the value. -/
inductive DataOnly : Value → Prop where
  | unit : DataOnly .unit
  | bool {value : Bool} : DataOnly (.bool value)
  | word {value : Word} : DataOnly (.word value)
  | integer {value : Int} : DataOnly (.integer value)
  | pair {left right : Value} : DataOnly left → DataOnly right → DataOnly (.pair left right)
  | inLeft {type : Ty} {payload : Value} : DataOnly payload → DataOnly (.inLeft type payload)
  | inRight {type : Ty} {payload : Value} : DataOnly payload → DataOnly (.inRight type payload)
  | constructed {constructor : ConstructorId} {payload : Value} :
      DataOnly payload → DataOnly (.constructed constructor payload)

/-- The existing projection proof follows actual catalog entry IDs and their
ordered definition lookup, including callable and mapping wrappers. -/
theorem project_wellFormed {catalog : SourceCoreCompatibleCatalog.Catalog}
    {sourceType : TypeSystem.Ty} {type : Ty}
    (projected : catalog.project sourceType = .ok type) : type.WellFormed catalog.definitions :=
  CompatibleExpressionCertificateNativeTyping.project_wellFormed projected

/-- Named payloads are selected from the original well formed definition,
then identified with the actual lookup in its appended environment. -/
theorem DataOnly.restrict_definitions {value : Value} (data : DataOnly value)
    {base future : DataEnvironment} (wellFormed : base.WellFormed)
    (extension : base.Extends future) {world : StoreTyping} {type : Ty}
    (annotation : type.WellFormed base)
    (typed : RuntimeValueHasType world value type future) : RuntimeValueHasType world value type base := by
  induction data generalizing type with
  | unit => cases typed; exact .unit
  | bool => cases typed; exact .bool
  | word => cases typed; exact .word
  | integer => cases typed; exact .integer
  | pair _ _ first second =>
    cases typed with
    | pair left right => cases annotation with
      | product firstType secondType => exact .pair (first firstType left) (second secondType right)
  | inLeft _ child =>
    cases typed with
    | inLeft payload => cases annotation with
      | sum payloadType _ => exact .inLeft (child payloadType payload)
  | inRight _ child =>
    cases typed with
    | inRight payload => cases annotation with
      | sum _ payloadType => exact .inRight (child payloadType payload)
  | @constructed constructor payload _ child =>
    cases typed with
    | constructed selected payloadTyped => cases annotation with
      | namedData owner =>
        obtain ⟨definition, selectedOwner, selectedPayload⟩ :=
          DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mp selected
        have same := Option.some.inj ((extension.lookup owner).symm.trans selectedOwner)
        subst definition
        have original := DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mpr
          ⟨_, owner, selectedPayload⟩
        exact .constructed original
          (child (wellFormed.constructorPayloadType_wellFormed original) payloadTyped)

private def RawData (fuel : Nat) : Prop :=
  ∀ (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    (expected : TypeSystem.Ty) (carrier : SourceCoreDataValues.Value)
    (encoded : SourceCoreCompatibleValues.Extended registry Value),
    encodeRaw fuel checked registry expected carrier = .ok encoded → DataOnly encoded.value

private def PayloadData (fuel : Nat) : Prop :=
  ∀ (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    (types : List TypeSystem.Ty) (carriers : List SourceCoreDataValues.Value) (index : Nat)
    (encoded : SourceCoreCompatibleValues.Extended registry Value),
    encodePayloadsRaw fuel checked registry types carriers index = .ok encoded → DataOnly encoded.value

private def EntriesData (fuel : Nat) : Prop :=
  ∀ (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    (key value : TypeSystem.Ty) (layout : OrderedMapping.Layout)
    (carriers : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value)) (index : Nat)
    (encoded : SourceCoreCompatibleValues.Extended registry Value),
    encodeEntriesRaw fuel checked registry key value layout carriers index = .ok encoded → DataOnly encoded.value

private theorem default_data {fuel : Nat} (raw : RawData fuel)
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {sourceType : TypeSystem.Ty} {type : Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : encodeDefaultRaw fuel checked registry sourceType type = .ok encoded) : DataOnly encoded.value := by
  cases found : SourceCoreCompatibleValues.defaultValue? (sourceType.size + 1) sourceType with
  | none =>
    simp only [encodeDefaultRaw, found, pure, Except.pure] at accepted
    cases accepted
    exact .inLeft .unit
  | some carrier =>
    simp only [encodeDefaultRaw, found] at accepted
    obtain ⟨inner, generated, accepted⟩ := bind_ok accepted
    cases accepted
    exact .inRight (raw checked registry sourceType carrier inner generated)

private theorem raw_data_succ {fuel : Nat} (raw : RawData fuel)
    (payload : PayloadData fuel) (entries : EntriesData fuel) : RawData (fuel + 1) := by
  intro checked registry expected carrier encoded accepted
  cases carrier with
  | unit | bool value | word value | integer value =>
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    all_goals try (solve | cases accepted)
    case constructor id =>
      cases id with
      | declaration => cases accepted
      | builtin builtin => cases builtin <;> try (solve | cases accepted)
                           all_goals cases accepted; constructor
  | product left right =>
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    case product leftType rightType =>
      obtain ⟨a, first, accepted⟩ := bind_ok accepted
      obtain ⟨b, second, accepted⟩ := bind_ok accepted
      cases accepted
      exact .pair (raw checked registry leftType left a (mapError_ok first))
        (raw checked a.registry rightType right b (mapError_ok second))
    all_goals try (solve | cases accepted)
    case constructor id => cases id <;> try (solve | cases accepted)
                           rename_i builtin; cases builtin <;> cases accepted
  | proxy inner =>
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    case proxy expectedInner =>
      obtain ⟨inserted, _, accepted⟩ := bind_ok accepted
      obtain ⟨identity, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact .constructed .word
    all_goals try (solve | cases accepted)
    case constructor id => cases id <;> try (solve | cases accepted)
                           rename_i builtin; cases builtin <;> cases accepted
  | mapping key value carriers =>
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    case mapping keyType valueType =>
      obtain ⟨inserted, _, accepted⟩ := bind_ok accepted
      obtain ⟨layout, _, accepted⟩ := bind_ok accepted
      obtain ⟨encodedEntries, entryEq, accepted⟩ := bind_ok accepted
      obtain ⟨fallback, fallbackEq, accepted⟩ := bind_ok accepted
      cases accepted
      exact .pair .word (.pair (default_data raw fallbackEq)
        (entries checked inserted.registry key value layout carriers 0 encodedEntries entryEq))
    all_goals try (solve | cases accepted)
    case constructor id => cases id <;> try (solve | cases accepted)
                           rename_i builtin; cases builtin <;> cases accepted
  | constructed metadata carriers =>
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    case function => cases accepted
    case constructor id =>
      cases id <;> try (rename_i builtin; cases builtin)
      all_goals
        obtain ⟨inserted, _, accepted⟩ := bind_ok accepted
        obtain ⟨tag, _, accepted⟩ := bind_ok accepted
        obtain ⟨fields, fieldEq, accepted⟩ := bind_ok accepted
        cases accepted
        exact .constructed (.pair .word (payload checked inserted.registry metadata.payloadTypes carriers 0 fields fieldEq))
    all_goals
      obtain ⟨inserted, _, accepted⟩ := bind_ok accepted
      obtain ⟨tag, _, accepted⟩ := bind_ok accepted
      obtain ⟨fields, fieldEq, accepted⟩ := bind_ok accepted
      cases accepted
      exact .constructed (.pair .word (payload checked inserted.registry metadata.payloadTypes carriers 0 fields fieldEq))

private theorem payload_data_succ {fuel : Nat} (raw : RawData fuel)
    (payload : PayloadData fuel) : PayloadData (fuel + 1) := by
  intro checked registry types carriers index encoded accepted
  by_cases length : types.length = carriers.length
  · cases types with
    | nil => cases carriers with
      | nil => simp [encodePayloadsRaw] at accepted; subst encoded; exact .unit
      | cons => simp at length
    | cons type types => cases carriers with
      | nil => simp at length
      | cons carrier carriers => cases types with
        | nil =>
          have empty : carriers = [] := by simpa using length.symm
          subst carriers
          simp only [encodePayloadsRaw, length, ↓reduceIte] at accepted
          exact raw checked registry type carrier encoded (mapError_ok accepted)
        | cons next types =>
          simp only [encodePayloadsRaw, length, ↓reduceIte] at accepted
          obtain ⟨first, firstEq, accepted⟩ := bind_ok accepted
          obtain ⟨rest, restEq, accepted⟩ := bind_ok accepted
          cases accepted
          exact .pair (raw checked registry type carrier first (mapError_ok firstEq))
            (payload checked first.registry (next :: types) carriers (index + 1) rest restEq)
  · unfold encodePayloadsRaw at accepted
    simp [length, bind, Except.bind, throw, throwThe] at accepted

private theorem entries_data_succ {fuel : Nat} (raw : RawData fuel)
    (entries : EntriesData fuel) : EntriesData (fuel + 1) := by
  intro checked registry keyType valueType layout carriers index encoded accepted
  cases carriers with
  | nil =>
    simp only [encodeEntriesRaw, pure, Except.pure] at accepted
    cases accepted
    exact .constructed .unit
  | cons pair rest =>
    obtain ⟨key, value⟩ := pair
    simp only [encodeEntriesRaw] at accepted
    obtain ⟨a, first, accepted⟩ := bind_ok accepted
    obtain ⟨b, second, accepted⟩ := bind_ok accepted
    obtain ⟨tail, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    exact .constructed (.pair (.pair (raw checked registry keyType key a (mapError_ok first))
      (raw checked a.registry valueType value b (mapError_ok second)))
      (entries checked b.registry keyType valueType layout rest (index + 1) tail remaining))

/-- One fuel induction closes the actual raw, payload and ordered-entry
encoders. The mapping default consumes the raw child at that same fuel. -/
private theorem data_only (fuel : Nat) : RawData fuel ∧ PayloadData fuel ∧ EntriesData fuel := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro checked registry expected carrier encoded accepted
      unfold encodeRaw at accepted
      cases accepted
    · intro checked registry types carriers index encoded accepted
      cases types with
      | nil => cases carriers with
        | nil => simp [encodePayloadsRaw] at accepted; subst encoded; exact .unit
        | cons => simp [encodePayloadsRaw, bind, Except.bind, throw, throwThe] at accepted
      | cons head tail =>
        simp only [encodePayloadsRaw] at accepted
        split at accepted <;> simp_all [bind, Except.bind, throw, throwThe]
    · intro checked registry key value layout carriers index encoded accepted
      cases carriers with
      | nil =>
        simp only [encodeEntriesRaw, pure, Except.pure] at accepted
        cases accepted
        exact .constructed .unit
      | cons => simp [encodeEntriesRaw, throw, throwThe] at accepted
  | succ fuel ih => exact ⟨raw_data_succ ih.1 ih.2.1 ih.2.2,
      payload_data_succ ih.1 ih.2.1, entries_data_succ ih.1 ih.2.2⟩

theorem encodeRaw_dataOnly {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {expected : TypeSystem.Ty} {carrier : SourceCoreDataValues.Value}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : encodeRaw fuel checked registry expected carrier = .ok encoded) : DataOnly encoded.value :=
  (data_only fuel).1 checked registry expected carrier encoded accepted

theorem encodePayloadsRaw_dataOnly {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {types : List TypeSystem.Ty}
    {carriers : List SourceCoreDataValues.Value} {index : Nat}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : encodePayloadsRaw fuel checked registry types carriers index = .ok encoded) : DataOnly encoded.value :=
  (data_only fuel).2.1 checked registry types carriers index encoded accepted

theorem encodeEntriesRaw_dataOnly {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {key value : TypeSystem.Ty} {layout : OrderedMapping.Layout}
    {carriers : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value)} {index : Nat}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : encodeEntriesRaw fuel checked registry key value layout carriers index = .ok encoded) :
    DataOnly encoded.value :=
  (data_only fuel).2.2 checked registry key value layout carriers index encoded accepted

theorem encodeDefaultRaw_dataOnly {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {sourceType : TypeSystem.Ty} {type : Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : encodeDefaultRaw fuel checked registry sourceType type = .ok encoded) : DataOnly encoded.value :=
  default_data (data_only fuel).1 accepted

/-- The actual codec and catalog projection remove the extended-definition
typing premise needed by the existing compatible raw soundness theorem. -/
theorem encodeRaw_restrict_typing {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {expected : TypeSystem.Ty} {carrier : SourceCoreDataValues.Value}
    {encoded : SourceCoreCompatibleValues.Extended registry Value} {world : StoreTyping}
    {type : Ty} {future : DataEnvironment}
    (accepted : encodeRaw fuel checked registry expected carrier = .ok encoded)
    (projected : checked.catalog.project expected = .ok type)
    (extension : checked.catalog.definitions.Extends future)
    (typed : RuntimeValueHasType world encoded.value type future) :
    RuntimeValueHasType world encoded.value type checked.catalog.definitions :=
  (encodeRaw_dataOnly accepted).restrict_definitions checked.definitionsTyped extension
    (project_wellFormed projected) typed

end Solcore.SourceSemantics.CoreLowering.CompatibleEncodedDataTyping
