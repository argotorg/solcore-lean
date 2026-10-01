import Solcore.SourceSemantics.CoreLowering.CompatiblePayloadRuntimeTypes
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingEncoding
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingPreparation
import Solcore.Frontend.SourceRuntimeValues

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRuntimeKeyGuards
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality CompatibleMapping

/-- The independent normalizer matches the historical pure runtime type view
on every type, including nested nominal arguments, proxies and function types. -/
theorem normalization (type : TypeSystem.Ty) : Dynamic.runtimeType type = SourceTypedRuntime.runtimeType type := by
  induction type <;> simp_all [Dynamic.runtimeType, SourceTypedRuntime.runtimeType]

theorem staged_boolean (value : Bool) : Dynamic.ValueRuntimeTypeMatches (.bool value) (.comptime .bool) :=
  .intro (.bool value) rfl

theorem staged_product (value : Bool) (inner : TypeSystem.Ty) :
    Dynamic.ValueRuntimeTypeMatches (.product (.bool value) (.proxy (.comptime inner)))
      (.product (.comptime .bool) (.proxy inner)) :=
  .intro (.product (.bool value) (.proxy _)) rfl

theorem staged_nominal (metadata : DataConstructorInstantiation) (arguments : List Dynamic.Value) :
    Dynamic.ValueRuntimeTypeMatches (.constructed metadata arguments) (.comptime metadata.resultType) :=
  .intro (.constructed metadata arguments) rfl

private def keyType : TypeSystem.Ty := .comptime .bool
private def valueType : TypeSystem.Ty := .comptime (.function .bool .bool)
private def mapType : TypeSystem.Ty := .mapping keyType valueType
private def sourceRoot : Dynamic.Value := .mapping keyType valueType []
private def carrier : SourceCoreDataValues.Value := .mapping keyType valueType []
private theorem unavailable : ¬ Dynamic.Defaultable valueType := by
  intro impossible; cases impossible with | comptime inner => cases inner

/-- Former counterexample: normalization accepts the Bool key, while the
missing default and fault retain the raw staged function type. -/
theorem source_missing : Dynamic.ProjectionsFaults (some sourceRoot) [.index (.bool true)] (.missingMappingDefault valueType) :=
  .indexDefaultUnavailable (staged_boolean true) .nil unavailable

/-- A raw type difference caused only by staging cannot trigger the
independent expression key-type mismatch rule. -/
theorem no_false_key_mismatch : ¬ (Dynamic.runtimeType .bool ≠ Dynamic.runtimeType keyType) := by simp [keyType]

private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := ⟨False.elim, fun impossible _ => False.elim impossible⟩
private theorem observations (catalog : SourceCoreCompatibleCatalog.Catalog) :
    FunctionObservations catalog (noFunctions catalog) (fun _ _ => False) := fun impossible => False.elim impossible
private theorem functionViews (catalog : SourceCoreCompatibleCatalog.Catalog) :
    FunctionRuntimeViews (noFunctions catalog) := fun impossible => False.elim impossible

/-- Actual encoder and comparator receipts give finite completion and
reflection with the corrected independent key guard. No helper run is assumed. -/
theorem actual_missing {context : SourceCoreCompatibleValues.Context} {layout : OrderedMapping.Layout}
    (comparison : SourceCoreCompatibleDataEquality.Prepared context.checked)
    (registered : layout.Registered context.checked.catalog.definitions) (sameKey : layout.keyType = comparison.type)
    (mappingProjection : context.checked.catalog.project mapType = .ok (SourceCoreMappingWithDefault.type layout))
    (keyProjection : context.checked.catalog.project keyType = .ok layout.keyType)
    {encodedMapping : SourceCoreCompatibleValues.Encoded 100 context mapType carrier}
    {encodedKey : SourceCoreCompatibleValues.Encoded 100 encodedMapping.context keyType (.bool true)}
    (mappingAccepted : SourceCoreCompatibleValues.encode 100 context mapType carrier = .ok encodedMapping)
    (keyAccepted : SourceCoreCompatibleValues.encode 100 encodedMapping.context keyType (.bool true) = .ok encodedKey)
    (missing : Word) :
    ∃ header finalStore,
      MetadataRep encodedKey.context.registry (.mapping keyType valueType) header ∧
      Dynamic.ProjectionsFaults (some sourceRoot) [.index (.bool true)] (.missingMappingDefault valueType) ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (SourceCoreMappingWithDefault.lookup layout missing comparison.expression (.var 0) (.var 1))
          [encodedMapping.value, encodedKey.value] [.integer (-9)]) =
          .done (.inLeft layout.valueType (.word (missing.add header))) finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (SourceCoreMappingWithDefault.lookup layout missing comparison.expression (.var 0) (.var 1))
          [encodedMapping.value, encodedKey.value] [.integer (-9)]) = .done actual actualStore →
          actual = .inLeft layout.valueType (.word (missing.add header)) ∧ actualStore = finalStore) := by
  obtain ⟨header, result, finalStore, metadata, meaning, completes, reflects, _⟩ :=
    encoded_lookup_run comparison layout registered sameKey mappingProjection keyProjection mappingAccepted keyAccepted
      (show CompatibleEncoding.Means carrier sourceRoot from .mapping .empty) (.bool true)
      faithful (observations context.checked.catalog) [] [.integer] [encodedMapping.value, encodedKey.value] [.integer (-9)] missing
      (.var 0) (.var 1) (.var rfl) (.var rfl)
  cases meaning with
  | found located => cases located
  | default _ defaulted => exact (unavailable defaulted.defaultable).elim
  | missing absent _ =>
    have keyRep := CompatibleEncoding.encode_represents_at (context := encodedMapping.context) (functions := noFunctions context.checked.catalog) keyAccepted
      (show CompatibleEncoding.Means (.bool true) (.bool true) from .bool true) [] [.integer]
    have typed := keyRep.source_runtimeView (functionViews context.checked.catalog)
    exact ⟨header, finalStore, metadata, .indexDefaultUnavailable typed absent unavailable, completes, reflects⟩

private def exercise (context : SourceCoreCompatibleValues.Context) : IO Unit := do
  match layoutAccepted : context.checked.catalog.mappingLayout keyType valueType with
  | .error error => throw (IO.userError s!"key guard layout rejected {reprStr error}")
  | .ok layout =>
    have facts := CompatibleEncoding.mappingLayout_facts (checked := context.checked) layoutAccepted
    have projection := CompatibleEncoding.mapping_project facts.1 facts.2.1 facts.2.2.1
    match comparisonAccepted : SourceCoreCompatibleDataEquality.prepare 100 context.checked keyType with
    | .error error => throw (IO.userError s!"key guard comparison rejected {reprStr error}")
    | .ok comparison =>
      have comparisonProjection : context.checked.catalog.project keyType = .ok comparison.type := by
        simpa only [comparison_sourceType comparisonAccepted] using comparison.projection
      have keySame := Except.ok.inj (facts.2.1.symm.trans comparisonProjection)
      match mappingAccepted : SourceCoreCompatibleValues.encode 100 context mapType carrier with
      | .error error => throw (IO.userError s!"key guard mapping rejected {reprStr error}")
      | .ok encodedMapping =>
        match keyAccepted : SourceCoreCompatibleValues.encode 100 encodedMapping.context keyType (.bool true) with
        | .error error => throw (IO.userError s!"key guard key rejected {reprStr error}")
        | .ok encodedKey =>
          have _receipt := actual_missing comparison facts.2.2.2 keySame projection facts.2.1 mappingAccepted keyAccepted (Word.ofNatModulo 100)
          let code := SourceCoreMappingWithDefault.lookup layout (Word.ofNatModulo 100) comparison.expression (.var 0) (.var 1)
          unless infer? [SourceCoreMappingWithDefault.type layout, layout.keyType] code context.checked.catalog.definitions ==
              some (LanguageResult.resultType layout.valueType) do
            throw (IO.userError "key guard actual helper checker rejected")
          let header ← match encodedMapping.value with
            | .pair (.word header) _ => pure header
            | _ => throw (IO.userError "key guard header missing")
          unless encodedKey.context.registry.lookup header == some (.mapping keyType valueType) do
            throw (IO.userError "key guard raw expected metadata erased")
          let initial := Core.State.initial code [encodedMapping.value, encodedKey.value] [.integer (-9)]
          match runStateful 200000 initial with
          | .done (.inLeft _ (.word token)) after =>
            unless token == (Word.ofNatModulo 100).add header && after[0]? == some (.integer (-9)) &&
                after.length == context.checked.catalog.entries.length + 2 do
              throw (IO.userError "key guard missing-default or helper effects changed")
            match runStateful 11 initial with
            | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done (.inLeft layout.valueType (.word token)) after do
                throw (IO.userError "key guard checkpoint changed result")
            | _ => throw (IO.userError "key guard expected checkpoint")
          | result => throw (IO.userError s!"key guard helper unexpected {reprStr result}")

def run : IO Unit := do
  match SourceCoreCompatibleCatalog.prepare ⟨[], [], [], [], [], []⟩ 100 [mapType] with
  | .error error => throw (IO.userError s!"key guard catalog rejected {reprStr error}")
  | .ok checked => exercise (SourceCoreCompatibleValues.Context.initial checked)
  IO.println "independent normalized key guards, raw defaults and actual native reflection GREEN"

end Tests.SourceCoreRuntimeKeyGuards
