import Solcore.SourceSemantics.CoreLowering.DataPayloadCatalog
import Solcore.SourceSemantics.CoreLowering.DataPayloadEncoding
import Solcore.SourceSemantics.CoreLowering.DataPayloadEquality
import Solcore.SourceSemantics.CoreLowering.GenericHeap

/-! Actual public encoding supplies a complete nominal/mapping/proxy payload,
then the same certificate supplies equality observations and mapped heap cells.
Duplicate mapping keys and raw comptime proxy identities are retained. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreDataPayload
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open DataPayload DataPayloadEncoding
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"payload", by decide⟩], by decide⟩⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "payload.solc"⟩, 0, 1⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def proxyInner : TypeSystem.Ty := .comptime .integer
private def proxyType : TypeSystem.Ty := .proxy proxyInner
private def mappingType : TypeSystem.Ty := .mapping (.comptime .word) proxyType
private def layout : Core.OrderedMapping.Layout := ⟨.word, .namedData ⟨2⟩, ⟨1⟩⟩
private def payloadTypes : List TypeSystem.Ty := [mappingType, .product .bool .integer]
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", payloadTypes, ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := boxType, definition := some ⟨[.product layout.type (.product .bool .integer)]⟩, constructors := [⟨dataId, 0⟩] },
  { sourceType := .mapping .word proxyType, definition := some layout.definition },
  { sourceType := proxyType, definition := some ⟨[.unit]⟩ }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def context : SourceCoreDataValues.Context := ⟨checked, signatures⟩
private def metadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], payloadTypes, boxType⟩
private def emptyFunctions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private def model := payloadModel catalog signatures emptyFunctions
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero => cases selected; trivial
  | succ index => cases index with
    | zero =>
      cases selected
      exact ⟨.word, .namedData ⟨2⟩, rfl, rfl, ⟨.word, .namedData (by rfl), rfl⟩⟩
    | succ index => cases index with
      | zero => cases selected; rfl
      | succ index => simp [catalog] at selected
private theorem observedFunctions : FunctionObservations catalog signatures emptyFunctions (fun _ _ => False) :=
  fun impossible => False.elim impossible
private def publicValue : SourceCoreDataValues.Value := .constructed metadata [
  .mapping (.comptime .word) proxyType [(.word Word.zero, .proxy proxyInner), (.word Word.zero, .proxy proxyInner)],
  .product (.bool true) (.integer (-7))]
private def sourceValue : Dynamic.Value := .constructed metadata [
  .mapping (.comptime .word) proxyType [(.word Word.zero, .proxy proxyInner), (.word Word.zero, .proxy proxyInner)],
  .product (.bool true) (.integer (-7))]
private def proxyCore : Value := .constructed ⟨⟨2⟩, 0⟩ .unit
private def coreValue : Value := .constructed ⟨⟨0⟩, 0⟩
  (.pair (Core.OrderedMapping.encode layout [(.word Word.zero, proxyCore), (.word Word.zero, proxyCore)])
    (.pair (.bool true) (.integer (-7))))
private theorem meaning : Means publicValue sourceValue :=
  .constructed (.cons (.mapping (.prepend (.word _) (.proxy _) (.prepend (.word _) (.proxy _) .empty)))
    (.cons (.product (.bool _) (.integer _)) .nil))
private theorem encoded : SourceCoreDataValues.encode 40 context boxType publicValue = .ok coreValue := by cbv
private theorem receipt : SourceCoreDataValues.Encodes 40 context boxType publicValue coreValue :=
  SourceCoreDataValues.encodes_of_encode encoded
private theorem represented : ValueRep catalog signatures emptyFunctions [] [] boxType sourceValue coreValue (.namedData ⟨0⟩) :=
  encodes_represents_at layouts meaning (by rfl) receipt

example : SourceCoreDataCatalog.prepare signatures 100 [boxType] = .ok checked := by cbv
example : SourceCoreDataValues.decode 40 context boxType coreValue = .ok publicValue := by cbv
example : RuntimeValueHasType [] coreValue (.namedData ⟨0⟩) catalog.definitions := represented.runtime_hasType
example : DataEqualityValues.Observation catalog signatures (fun _ _ => False) (.namedData ⟨0⟩) sourceValue coreValue :=
  represented.observation observedFunctions
example : ValueRep catalog signatures emptyFunctions [4, 8] [.word, .integer]
    boxType sourceValue coreValue (.namedData ⟨0⟩) :=
  represented.extend ⟨[4, 8], rfl⟩ ⟨[.word, .integer], rfl⟩

/-- The full payload model uses the same source/Core location map API. -/
example : GenericHeap.HeapRepresents model [0] [OptionalCell.cellType (.namedData ⟨0⟩)]
    ⟨[⟨boxType, some sourceValue, none⟩]⟩ [.inRight .unit coreValue] := by
  exact (GenericHeap.HeapRepresents.empty.allocate (.initialized represented) .append).1

/-- A missing mapping default is still authenticated through the actual raw
proxy identity and actual catalog layout. -/
example : ValueRep catalog signatures emptyFunctions [] [] (.comptime mappingType)
    (.mapping (.comptime .word) proxyType []) (Core.OrderedMapping.encode layout []) layout.type := by
  apply default_represents_at layouts (by rfl)
  exact .comptime (.mapping _ _ _ (by rfl))

/-- Changing the raw identity inside a proxy is rejected even if its runtime
projection would erase the same outer staging wrapper. -/
example : (SourceCoreDataValues.encode 40 context proxyType (.proxy .integer)).toOption.isNone = true := by cbv

/-- Registered Core typing alone cannot authenticate source constructor
payload metadata; the public encoder rejects this tampering. -/
example : (SourceCoreDataValues.encode 40 context boxType
    (.constructed { metadata with payloadTypes := [.integer] } [.integer 0])).toOption.isNone = true := by cbv

end Tests.SourceCoreDataPayload
