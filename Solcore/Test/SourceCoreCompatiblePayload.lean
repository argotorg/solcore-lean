import Solcore.SourceSemantics.CoreLowering.CompatiblePayload

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
