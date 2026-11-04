import Solcore.SourceSemantics.CoreLowering.CompatibleMappings
import Solcore.SourceSemantics.CoreLowering.CompatiblePayload

/-!
# Compatible payload tests

Payloads and mappings, kept apart because they stay independent of the compiler's encoder.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleMappings
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCompatibleValues.encode

/-! Recursive nominal/mapping payloads, repeated keys, raw staged proxy
fallbacks, and absence of nominal defaults through authenticated registries. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
namespace Tests.SourceCoreCompatibleMappings
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering CompatiblePayload

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_mapping", by decide⟩], by decide⟩⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_mapping.solc"⟩, 0, 1⟩
private def treeType : TypeSystem.Ty := .nominal dataId []
private def mapType : TypeSystem.Ty := .mapping .word treeType
private def signature : ProgramDataSignature := {
  id := dataId, name := "Tree", parameters := []
  constructors := [
    ⟨⟨dataId, 0⟩, "Leaf", [], ⟨span, ⟨[], ⟨span, "Leaf"⟩, none⟩⟩⟩,
    ⟨⟨dataId, 1⟩, "Node", [mapType], ⟨span, ⟨[], ⟨span, "Node"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Tree"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def leafMetadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [], treeType⟩
private def nodeMetadata : DataConstructorInstantiation := ⟨⟨dataId, 1⟩, [], [mapType], treeType⟩
private def treeLayout : OrderedMapping.Layout := ⟨.word, .namedData ⟨0⟩, ⟨1⟩⟩
private def proxyLayout : OrderedMapping.Layout := ⟨.word, .namedData ⟨2⟩, ⟨3⟩⟩
private def nestedLayout : OrderedMapping.Layout := ⟨.word, SourceCoreMappingWithDefault.type proxyLayout, ⟨4⟩⟩
private def catalog : SourceCoreCompatibleCatalog.Catalog := { entries := [
  { sourceType := treeType, constructors := [⟨dataId, 0⟩, ⟨dataId, 1⟩], definition := some ⟨[
      .product .word .unit, .product .word (SourceCoreMappingWithDefault.type treeLayout)]⟩ },
  { sourceType := mapType, definition := some treeLayout.definition },
  { sourceType := .proxy .word, definition := some ⟨[.word]⟩ },
  { sourceType := .mapping .word (.proxy .word), definition := some proxyLayout.definition },
  { sourceType := .mapping .word (.mapping .word (.proxy .word)), definition := some nestedLayout.definition }] }
private def checked (registry : SourceCoreRawMetadata.Registry) (owner : registry.signatures = signatures) : SourceCoreCompatibleCatalog.Checked :=
  ⟨catalog, DataEnvironment.isWellFormed_sound (by decide), signatures, registry, owner⟩
private def functions : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def one : Word := ⟨1, by decide⟩
private def missing : Word := ⟨99, by decide⟩
private theorem treeRegistered : treeLayout.Registered catalog.definitions :=
  ⟨.word, .namedData (by rfl), rfl⟩
private theorem proxyRegistered : proxyLayout.Registered catalog.definitions :=
  ⟨.word, .namedData (by rfl), rfl⟩
private theorem nestedRegistered : nestedLayout.Registered catalog.definitions :=
  ⟨.word, SourceCoreMappingWithDefault.type_wellFormed proxyRegistered, rfl⟩
private theorem treeNotDefaultable : ¬ Dynamic.Defaultable treeType := by intro impossible; cases impossible

private def sourceTree : Nat → Dynamic.Value
  | 0 => .constructed leafMetadata []
  | depth + 1 => .constructed nodeMetadata [
      .mapping .word treeType [(.word one, sourceTree depth), (.word one, sourceTree 0)]]
private def coreTree (leaf node header : Word) : Nat → Value
  | 0 => .constructed ⟨⟨0⟩, 0⟩ (.pair (.word leaf) .unit)
  | depth + 1 => .constructed ⟨⟨0⟩, 1⟩ (.pair (.word node)
      (SourceCoreMappingWithDefault.value header none treeLayout [
        (.word one, coreTree leaf node header depth), (.word one, coreTree leaf node header 0)]))

/-- This is universal in depth. Mapping values may contain the same nominal
that in turn contains mappings, while both occurrences of the key survive. -/
private theorem treeRep {static registry : SourceCoreRawMetadata.Registry}
    (staticOwner : static.signatures = signatures) (owner : registry.signatures = signatures)
    {leaf node header : Word}
    (leafRep : MetadataRep registry (.constructor leafMetadata) leaf)
    (nodeRep : MetadataRep registry (.constructor nodeMetadata) node)
    (headerRep : MetadataRep registry (.mapping .word treeType) header)
    (depth : Nat) {mapping : GeneralHeap.LocationMap} {world : StoreTyping} :
    ValueRep (checked static staticOwner) registry functions mapping world treeType (sourceTree depth)
      (coreTree leaf node header depth) (.namedData ⟨0⟩) := by
  have leafRelated : ValueRep (checked static staticOwner) registry functions mapping world treeType (sourceTree 0)
      (coreTree leaf node header 0) (.namedData ⟨0⟩) :=
    by
      simpa only [sourceTree, coreTree, DataPatternValues.packValues, leafMetadata] using
        (ValueRep.constructed (checked := checked static staticOwner) (functions := functions)
          (mapping := mapping) (world := world) (tag := ⟨⟨0⟩, 0⟩) leafRep owner (by cbv) (by cbv) (by cbv) .nil)
  induction depth with
  | zero => exact leafRelated
  | succ depth ih =>
    have mapRelated : ValueRep (checked static staticOwner) registry functions mapping world mapType
        (.mapping .word treeType [(.word one, sourceTree depth), (.word one, sourceTree 0)])
        (SourceCoreMappingWithDefault.value header none treeLayout [
          (.word one, coreTree leaf node header depth), (.word one, coreTree leaf node header 0)])
        (SourceCoreMappingWithDefault.type treeLayout) :=
      .mappingValue headerRep (by cbv) (by cbv) (by cbv) treeRegistered
        (.entry (.word one) ih (.entry (.word one) leafRelated (.empty _ _ _ _)))
        (.absent treeNotDefaultable (by cbv) (.namedData (by rfl)))
    simpa only [sourceTree, coreTree, DataPatternValues.packValues, nodeMetadata] using
      (ValueRep.constructed (checked := checked static staticOwner) (functions := functions)
        (mapping := mapping) (world := world) (tag := ⟨⟨0⟩, 1⟩) nodeRep owner (by cbv) (by cbv) (by cbv)
        (.cons mapRelated .nil))

example {static registry future : SourceCoreRawMetadata.Registry}
    (staticOwner : static.signatures = signatures) (owner : registry.signatures = signatures)
    {leaf node header : Word}
    (leafRep : MetadataRep registry (.constructor leafMetadata) leaf)
    (nodeRep : MetadataRep registry (.constructor nodeMetadata) node)
    (headerRep : MetadataRep registry (.mapping .word treeType) header)
    (extension : SourceCoreRawMetadata.Extends registry future) (depth : Nat) :
    RuntimeValueHasType [.word] (coreTree leaf node header depth) (.namedData ⟨0⟩) catalog.definitions :=
  ((treeRep staticOwner owner leafRep nodeRep headerRep depth (mapping := []) (world := [])).extend
    extension ⟨[5], rfl⟩ ⟨[.word], rfl⟩).runtime_hasType

private def rawProxyType : TypeSystem.Ty := .proxy (.comptime .word)
private def rawMapType : TypeSystem.Ty := .mapping .word rawProxyType
private def proxyCore (id : Word) : Value := .constructed ⟨⟨2⟩, 0⟩ (.word id)
private theorem rawMappingRep {static registry : SourceCoreRawMetadata.Registry}
    (staticOwner : static.signatures = signatures) {header proxy : Word}
    (headerRep : MetadataRep registry (.mapping .word rawProxyType) header)
    (proxyRep : MetadataRep registry (.proxy (.comptime .word)) proxy)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} :
    ValueRep (checked static staticOwner) registry functions mapping world (.mapping .word (.proxy .word))
      (.mapping .word rawProxyType []) (SourceCoreMappingWithDefault.value header (some (proxyCore proxy)) proxyLayout [])
      (SourceCoreMappingWithDefault.type proxyLayout) :=
  .compatible (actual := rawMapType) rfl
    (.mappingValue headerRep (by cbv) (by cbv) (by cbv) proxyRegistered (.empty _ _ _ _)
      (.present (.proxy _) (.proxy proxyRep (by cbv) (by cbv))))

/-- An empty mapping's transported default can itself be an empty mapping,
whose transported proxy default still carries the original staged metadata. -/
private theorem nestedMappingRep {static registry : SourceCoreRawMetadata.Registry}
    (staticOwner : static.signatures = signatures) {outer inner proxy : Word}
    (outerRep : MetadataRep registry (.mapping .word rawMapType) outer)
    (innerRep : MetadataRep registry (.mapping .word rawProxyType) inner)
    (proxyRep : MetadataRep registry (.proxy (.comptime .word)) proxy)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} :
    ValueRep (checked static staticOwner) registry functions mapping world (.mapping .word rawMapType)
      (.mapping .word rawMapType [])
      (SourceCoreMappingWithDefault.value outer
        (some (SourceCoreMappingWithDefault.value inner (some (proxyCore proxy)) proxyLayout [])) nestedLayout [])
      (SourceCoreMappingWithDefault.type nestedLayout) :=
  .mappingValue outerRep (by cbv) (by cbv) (by cbv) nestedRegistered (.empty _ _ _ _)
    (.present (.mapping _ _)
      (.compatible (actual := .mapping .word (.proxy .word)) rfl (rawMappingRep staticOwner innerRep proxyRep)))

/-- Missing nominal default is a semantic absence, not fuel exhaustion. -/
example : SourceTypedRuntime.defaultValue? (treeType.size + 1) treeType = none :=
  (defaultValue?_absent_iff (by omega)).mpr treeNotDefaultable

/-- Outer staging is removed, but metadata inside the produced proxy and
empty mapping stays raw. This differs from defaulting their erased types. -/
example : ∃ raw,
    SourceTypedRuntime.defaultValue? 20 (.comptime (.product rawProxyType rawMapType)) = some raw ∧
    DefaultData raw (.product (.proxy (.comptime .word)) (.mapping .word rawProxyType [])) :=
  defaultValue?_complete (.comptime (.product (.proxy _) (.mapping _ _))) 20 (by decide)

example {registry : SourceCoreRawMetadata.Registry} {a b : Word}
    (raw : MetadataRep registry (.mapping .word rawProxyType) a)
    (canonical : MetadataRep registry (.mapping .word (.proxy .word)) b) : a ≠ b := by
  intro same
  have metadata := (mapping_headers_equal_iff raw canonical).mp same
  cases metadata.2

private def treeExpr (leaf node header : Word) : Nat → Expr
  | 0 => .construct ⟨⟨0⟩, 0⟩ (.pair (.word leaf) .unit)
  | depth + 1 => .construct ⟨⟨0⟩, 1⟩ (.pair (.word node)
      (SourceCoreMappingWithDefault.pack (.word header) (.inLeft (.namedData ⟨0⟩) .unit)
        (OrderedMapping.cons treeLayout (.word one) (treeExpr leaf node header depth)
          (OrderedMapping.cons treeLayout (.word one) (treeExpr leaf node header 0) (OrderedMapping.empty treeLayout)))))
private def wordEqual : Expr := .lambda (.product .word .word) .bool
  (.binary .wordEq (.first (.var 0)) (.second (.var 0)))
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  match prepared : SourceCoreRawMetadata.prepare signatures [
      .constructor leafMetadata, .constructor nodeMetadata, .mapping .word treeType,
      .mapping .word (.proxy .word), .proxy .word] with
  | .error error => throw (IO.userError s!"mapping registry failed: {reprStr error}")
  | .ok static =>
    let owner := SourceCoreRawMetadata.prepare_signatures prepared
    match leafFound : static.id? (.constructor leafMetadata), nodeFound : static.id? (.constructor nodeMetadata),
        headerFound : static.id? (.mapping .word treeType) with
    | some leaf, some node, some header =>
      let leafRep : MetadataRep static (.constructor leafMetadata) leaf := ⟨static.id?_reconstruct leafFound⟩
      let nodeRep : MetadataRep static (.constructor nodeMetadata) node := ⟨static.id?_reconstruct nodeFound⟩
      let headerRep : MetadataRep static (.mapping .word treeType) header := ⟨static.id?_reconstruct headerFound⟩
      have _typed := (treeRep owner owner leafRep nodeRep headerRep 4 (mapping := []) (world := [])).runtime_hasType
      let program : Core.Program := ⟨.namedData ⟨0⟩, treeExpr leaf node header 4, catalog.definitions⟩
      assertTrue program.check "nested nominal/mapping rejected"
      match program.runStateful 2000 with
      | .done result [] => assertTrue (result == coreTree leaf node header 4) "nested mapping changed order or metadata"
      | _ => throw (IO.userError "nested mapping did not finish")
      -- First duplicate wins, with the later Leaf still in the represented list.
      let mapExpr := SourceCoreMappingWithDefault.pack (.word header) (.inLeft (.namedData ⟨0⟩) .unit)
        (OrderedMapping.cons treeLayout (.word one) (treeExpr leaf node header 2)
          (OrderedMapping.cons treeLayout (.word one) (treeExpr leaf node header 0) (OrderedMapping.empty treeLayout)))
      let lookup : Core.Program := ⟨LanguageResult.resultType treeLayout.valueType,
        SourceCoreMappingWithDefault.lookup treeLayout missing wordEqual mapExpr (.word one), catalog.definitions⟩
      assertTrue lookup.check "duplicate mapping lookup rejected"
      match lookup.runStateful 3000 with
      | .done (.inRight .word result) _ => assertTrue (result == coreTree leaf node header 2) "duplicate key order changed"
      | _ => throw (IO.userError "first duplicate lookup failed")
    | _, _, _ => throw (IO.userError "static mapping metadata missing")
    let rawProxy ← match static.intern (.proxy .word) (.proxy (.comptime .word)) with
      | .ok receipt => pure receipt | .error error => throw (IO.userError s!"raw proxy: {reprStr error}")
    let rawHeader ← match rawProxy.registry.intern (.mapping .word (.proxy .word)) (.mapping .word rawProxyType) with
      | .ok receipt => pure receipt | .error error => throw (IO.userError s!"raw mapping: {reprStr error}")
    let proxyRep : MetadataRep rawHeader.registry (.proxy (.comptime .word)) rawProxy.id :=
      ⟨rawHeader.preserves.lookup rawProxy.reconstruct⟩
    let headerRep : MetadataRep rawHeader.registry (.mapping .word rawProxyType) rawHeader.id := ⟨rawHeader.reconstruct⟩
    have represented := rawMappingRep owner headerRep proxyRep (mapping := []) (world := [])
    have _typed := represented.runtime_hasType
    have _sourceShape := represented.mapping_shape rfl
    let mapExpr := SourceCoreMappingWithDefault.pack (.word rawHeader.id)
      (.inRight .unit (.construct ⟨⟨2⟩, 0⟩ (.word rawProxy.id))) (OrderedMapping.empty proxyLayout)
    let lookup : Core.Program := ⟨LanguageResult.resultType proxyLayout.valueType,
      SourceCoreMappingWithDefault.lookup proxyLayout missing wordEqual mapExpr (.word one), catalog.definitions⟩
    assertTrue lookup.check "raw default lookup rejected"
    match lookup.runStateful 2000 with
    | .done (.inRight .word (.constructed tag (.word id))) _ =>
      assertTrue (tag == ⟨⟨2⟩, 0⟩ && id == rawProxy.id) "transported proxy default lost raw metadata"
    | _ => throw (IO.userError "raw proxy fallback failed")
    let outer ← match rawHeader.registry.intern (.mapping .word (.mapping .word (.proxy .word))) (.mapping .word rawMapType) with
      | .ok receipt => pure receipt | .error error => throw (IO.userError s!"outer raw mapping: {reprStr error}")
    have nested := nestedMappingRep owner (show MetadataRep outer.registry (.mapping .word rawMapType) outer.id from ⟨outer.reconstruct⟩)
      (headerRep.extend outer.preserves) (proxyRep.extend outer.preserves) (mapping := []) (world := [])
    have _nestedTyped := nested.runtime_hasType
    let nestedExpr := SourceCoreMappingWithDefault.pack (.word outer.id) (.inRight .unit mapExpr)
      (OrderedMapping.empty nestedLayout)
    let nestedLookup : Core.Program := ⟨LanguageResult.resultType nestedLayout.valueType,
      SourceCoreMappingWithDefault.lookup nestedLayout missing wordEqual nestedExpr (.word one), catalog.definitions⟩
    assertTrue nestedLookup.check "nested transported default rejected"
    match nestedLookup.runStateful 2000 with
    | .done (.inRight .word result) _ =>
      assertTrue (result == SourceCoreMappingWithDefault.value rawHeader.id (some (proxyCore rawProxy.id)) proxyLayout [])
        "nested default lost its own header or raw proxy fallback"
    | _ => throw (IO.userError "nested raw default lookup failed")
    match SourceTypedRuntime.defaultValue? (rawProxyType.size + 1) rawProxyType with
    | some (.proxy inner) => assertTrue (decide (inner = .comptime .word)) "pure default erased raw inner type"
    | _ => throw (IO.userError "pure raw proxy default absent")
    IO.println "compatible mapping nesting, duplicate order and raw defaults GREEN"

end Tests.SourceCoreCompatibleMappings
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatiblePayload
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCompatibleValues.encode

/-! The independent relation consumes real static-registry and dynamic-intern
receipts. Equal native nominal/proxy types retain distinct raw comptime IDs;
source constructor substitution and payload authenticity are still checked. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
namespace Tests.SourceCoreCompatiblePayload
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatiblePayload

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_payload", by decide⟩], by decide⟩⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def parameter : TypeSystem.TypeParameterId := ⟨dataId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_payload.solc"⟩, 0, 1⟩
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := [parameter]
  constructors := [⟨⟨dataId, 0⟩, "Box", [.parameter parameter, .proxy (.parameter parameter)],
    ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def boxType : TypeSystem.Ty := .nominal dataId [.word]
private def rawBoxType : TypeSystem.Ty := .nominal dataId [.comptime .word]
private def ordinaryMetadata : DataConstructorInstantiation :=
  ⟨⟨dataId, 0⟩, [(parameter, .word)], [.word, .proxy .word], boxType⟩
private def rawMetadata : DataConstructorInstantiation :=
  ⟨⟨dataId, 0⟩, [(parameter, .comptime .word)], [.comptime .word, .proxy (.comptime .word)], rawBoxType⟩
private def catalog : SourceCoreCompatibleCatalog.Catalog := { entries := [
  { sourceType := boxType, constructors := [⟨dataId, 0⟩],
    definition := some ⟨[.product .word (.product .word (.namedData ⟨1⟩))]⟩ },
  { sourceType := .proxy .word, definition := some ⟨[.word]⟩ }] }
private def checked (registry : SourceCoreRawMetadata.Registry) (owner : registry.signatures = signatures) : SourceCoreCompatibleCatalog.Checked :=
  ⟨catalog, DataEnvironment.isWellFormed_sound (by decide), signatures, registry, owner⟩
private def functions : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def seven : Word := ⟨7, by decide⟩
private def sourceValue : Dynamic.Value := .constructed rawMetadata [.word seven, .proxy (.comptime .word)]
private def coreValue (constructorId proxyId : Word) : Value := .constructed ⟨⟨0⟩, 0⟩
  (.pair (.word constructorId) (.pair (.word seven) (.constructed ⟨⟨1⟩, 0⟩ (.word proxyId))))

/-- Raw constructor fields keep their comptime wrappers even though their
native payload types are Word and the same proxy data identity. Registry
receipts authenticate the IDs without reinterpreting native typing as source
metadata authenticity. -/
private theorem represented {static registry : SourceCoreRawMetadata.Registry}
    (staticOwner : static.signatures = signatures) (registryOwner : registry.signatures = signatures)
    {constructorId proxyId : Word}
    (constructor : MetadataRep registry (.constructor rawMetadata) constructorId)
    (proxy : MetadataRep registry (.proxy (.comptime .word)) proxyId)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} :
    ValueRep (checked static staticOwner) registry functions mapping world boxType sourceValue
      (coreValue constructorId proxyId) (.namedData ⟨0⟩) := by
  apply ValueRep.compatible (actual := rawBoxType) (by rfl)
  exact .constructed constructor registryOwner (by cbv) (by cbv) (by cbv)
    (.cons (.compatible (actual := .word) rfl (.word seven)) (.cons (.proxy proxy (by cbv) (by cbv)) .nil))

example {static registry : SourceCoreRawMetadata.Registry}
    (staticOwner : static.signatures = signatures) (registryOwner : registry.signatures = signatures)
    {constructorId proxyId : Word}
    (constructor : MetadataRep registry (.constructor rawMetadata) constructorId)
    (proxy : MetadataRep registry (.proxy (.comptime .word)) proxyId) (world : StoreTyping) :
    RuntimeValueHasType world (coreValue constructorId proxyId) (.namedData ⟨0⟩) catalog.definitions :=
  (represented staticOwner registryOwner constructor proxy (mapping := []) (world := world)).runtime_hasType

example : catalog.project boxType = catalog.project rawBoxType := by cbv
example : catalog.identity? (.proxy .word) = catalog.identity? (.proxy (.comptime .word)) := by cbv

/-- Native ID equality distinguishes raw identities despite equal projections. -/
example {registry : SourceCoreRawMetadata.Registry} {a b : Word}
    (ordinary : MetadataRep registry (.proxy .word) a)
    (staged : MetadataRep registry (.proxy (.comptime .word)) b) : a ≠ b := by
  intro same
  have rawSame := (ordinary.ids_equal_iff staged).mp same
  cases rawSame

example {registry : SourceCoreRawMetadata.Registry} {a b : Word}
    (ordinary : MetadataRep registry (.constructor ordinaryMetadata) a)
    (staged : MetadataRep registry (.constructor rawMetadata) b) : a ≠ b := by
  intro same
  have rawSame := (ordinary.ids_equal_iff staged).mp same
  have results := congrArg (fun entry => entry.type) rawSame
  cases results

/-- Registry extension preserves the source metadata and native payload,
including map/world extension at an abstract authenticated function leaf. -/
example {static registry future : SourceCoreRawMetadata.Registry}
    (staticOwner : static.signatures = signatures) (registryOwner : registry.signatures = signatures)
    {constructorId proxyId : Word}
    (constructor : MetadataRep registry (.constructor rawMetadata) constructorId)
    (proxy : MetadataRep registry (.proxy (.comptime .word)) proxyId)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    ValueRep (checked static staticOwner) future functions [4, 8] [.word, .integer] boxType sourceValue
      (coreValue constructorId proxyId) (.namedData ⟨0⟩) :=
  (represented staticOwner registryOwner constructor proxy (mapping := []) (world := [])).extend extension
    ⟨[4, 8], rfl⟩ ⟨[.word, .integer], rfl⟩

/-- A forged raw constructor payload cannot be authenticated by any ID in an
owning registry, even though a native Word payload would be well typed. -/
example {registry : SourceCoreRawMetadata.Registry} (owner : registry.signatures = signatures) (id : Word) :
    ¬ MetadataRep registry (.constructor {rawMetadata with payloadTypes := [.bool]}) id := by
  intro related
  have authenticated := related.authenticated
  rw [owner] at authenticated
  have invalid : SourceCoreRawMetadata.Metadata.authentic signatures (.constructor {rawMetadata with payloadTypes := [.bool]}) = false := by decide
  rw [invalid] at authenticated
  cases authenticated

example {registry : SourceCoreRawMetadata.Registry} (owner : registry.signatures = signatures)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} :
    ValueRep (checked registry owner) registry functions mapping world
      (.comptime (.product .unit (.product .bool (.product .word .integer))))
      (.product .unit (.product (.bool true) (.product (.word seven) (.integer (-(2 ^ 400))))))
      (.pair .unit (.pair (.bool true) (.pair (.word seven) (.integer (-(2 ^ 400))))))
      (.product .unit (.product .bool (.product .word .integer))) :=
  .compatible (actual := .product .unit (.product .bool (.product .word .integer))) rfl
    (.product .unit (.product (.bool true) (.product (.word seven) (.integer _))))

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

/-- Execute real registry preparation/interning and instantiate the independent
relation using those receipts. Neither source runtime nor value codecs are used. -/
def run : IO Unit := do
  match prepared : SourceCoreRawMetadata.prepare signatures [.constructor ordinaryMetadata, .proxy .word] with
  | .error error => throw (IO.userError s!"compatible payload registry failed: {reprStr error}")
  | .ok static =>
    let owner := SourceCoreRawMetadata.prepare_signatures prepared
    let ordinaryProxy ← match static.id? (.proxy .word) with
      | some id => pure id | none => throw (IO.userError "static proxy ID absent")
    let ordinaryConstructor ← match static.id? (.constructor ordinaryMetadata) with
      | some id => pure id | none => throw (IO.userError "static constructor ID absent")
    let proxy ← match static.intern (.proxy .word) (.proxy (.comptime .word)) with
      | .ok receipt => pure receipt | .error error => throw (IO.userError s!"raw proxy failed: {reprStr error}")
    let constructor ← match proxy.registry.intern boxType (.constructor rawMetadata) with
      | .ok receipt => pure receipt | .error error => throw (IO.userError s!"raw constructor failed: {reprStr error}")
    let extension := proxy.preserves.trans constructor.preserves
    let header : MetadataRep constructor.registry (.constructor rawMetadata) constructor.id := ⟨constructor.reconstruct⟩
    let proxyHeader : MetadataRep constructor.registry (.proxy (.comptime .word)) proxy.id :=
      ⟨constructor.preserves.lookup proxy.reconstruct⟩
    have independent := represented owner (extension.signatures.trans owner) header proxyHeader (mapping := []) (world := [])
    have _typed : RuntimeValueHasType [] (coreValue constructor.id proxy.id) (.namedData ⟨0⟩) catalog.definitions := independent.runtime_hasType
    assertTrue (constructor.registry.staticLength == static.staticLength && constructor.registry.length == 4)
      "dynamic metadata changed static prefix or duplicate handling"
    assertTrue (ordinaryProxy != proxy.id && ordinaryConstructor != constructor.id)
      "raw comptime metadata collapsed to canonical native identity"
    assertTrue (constructor.registry.lookup ordinaryProxy == some (.proxy .word)) "old proxy ID changed"
    assertTrue (constructor.registry.lookup constructor.id == some (.constructor rawMetadata)) "raw constructor metadata changed"
    let expression : Expr := .construct ⟨⟨0⟩, 0⟩
      (.pair (.word constructor.id) (.pair (.word seven) (.construct ⟨⟨1⟩, 0⟩ (.word proxy.id))))
    let program : Core.Program := ⟨.namedData ⟨0⟩, expression, catalog.definitions⟩
    assertTrue program.check "compatible payload native program rejected"
    match program.runStateful 100 with
    | .done value store =>
      assertTrue (value == coreValue constructor.id proxy.id && store.isEmpty)
        "compatible payload native run changed metadata words"
    | _ => throw (IO.userError "compatible payload native run failed")
    let compareRaw : Expr := .matchData ⟨0⟩ (.product .bool .bool) expression [
      .pair (.binary .wordEq (.first (.var 0)) (.word ordinaryConstructor))
        (.matchData ⟨1⟩ .bool (.second (.second (.var 0))) [
          .binary .wordEq (.var 0) (.word ordinaryProxy)])]
    let comparison : Core.Program := ⟨.product .bool .bool, compareRaw, catalog.definitions⟩
    assertTrue comparison.check "raw ID comparison program rejected"
    match comparison.runStateful 200 with
    | .done (.pair (.bool false) (.bool false)) [] => pure ()
    | _ => throw (IO.userError "native comparison erased raw proxy or constructor metadata")
    IO.println "compatible payload registry authentication, extension and native typing GREEN"

end Tests.SourceCoreCompatiblePayload
end
