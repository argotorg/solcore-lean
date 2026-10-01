import Solcore.SourceSemantics.CoreLowering.CompatibleMappings

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
