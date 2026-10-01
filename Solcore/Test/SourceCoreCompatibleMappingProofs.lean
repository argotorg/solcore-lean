import Solcore.SourceSemantics.CoreLowering.CompatibleMappingEncoding
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingPreparation
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingPlaceRuns
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Actual encoding/comparator/place preparation exercises the independent
mapping theorems. Raw aliases and duplicate order remain visible on decode. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMappingProofs
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality CompatibleMapping

private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def noIdentities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful noIdentities := ⟨False.elim, fun impossible _ => False.elim impossible⟩
private theorem noFunctionObservations (catalog : SourceCoreCompatibleCatalog.Catalog) :
    FunctionObservations catalog (noFunctions catalog) noIdentities := fun impossible => False.elim impossible
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Item(Word) }", "function main() returns (Word) { return 0; }"
  ]}] }

private def completed (expression : Expr) (environment : Environment) (store : Store) : IO (Value × Store) := do
  let result ← match runStateful 200000 (.initial expression environment store) with
    | .done value finalStore => pure (value, finalStore)
    | other => throw (IO.userError s!"compatible mapping helper did not finish: {reprStr other}")
  match runStateful 1 (.initial expression environment store) with
  | .outOfFuel checkpoint =>
    match runStateful 200000 checkpoint with
    | .done value finalStore => assertTrue (value == result.1 && finalStore == result.2) "mapping helper resume changed value/store"
    | other => throw (IO.userError s!"mapping helper resume failed: {reprStr other}")
  | _ => throw (IO.userError "mapping regression no longer yields a checkpoint")
  assertTrue (result.2[0]? == store[0]?) "mapping helper modified earlier store"
  pure result

private def decoded (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty)
    (native : Value) (expected : SourceCoreDataValues.Value) : IO Unit := do
  match SourceCoreCompatibleValues.decode 500 context type native with
  | .ok actual => assertTrue (actual == expected) "raw mapping metadata/default/ordered entries changed"
  | .error error => throw (IO.userError s!"compatible mapping result decode failed: {reprStr error}")

private def exercise (context : SourceCoreCompatibleValues.Context) (owner : Resolved.DeclarationId)
    (sourceKey sourceValue : TypeSystem.Ty) (carrier keyCarrier replacementCarrier : SourceCoreDataValues.Value)
    (sources : List (Dynamic.Value × Dynamic.Value)) (sourceLookup : Dynamic.Value)
    (mappingMeaning : CompatibleEncoding.Means carrier (.mapping sourceKey sourceValue sources))
    (keyMeaning : CompatibleEncoding.Means keyCarrier sourceLookup)
    (expectedRead : Option SourceCoreDataValues.Value) (expectedInserted : SourceCoreDataValues.Value) : IO Unit := do
  match layoutAccepted : context.checked.catalog.mappingLayout sourceKey sourceValue with
  | .error error => throw (IO.userError s!"mapping layout rejected: {reprStr error}")
  | .ok layout =>
    have facts := CompatibleEncoding.mappingLayout_facts (checked := context.checked) layoutAccepted
    have projection := CompatibleEncoding.mapping_project facts.1 facts.2.1 facts.2.2.1
    match comparisonAccepted : SourceCoreCompatibleDataEquality.prepare 200 context.checked sourceKey with
    | .error error => throw (IO.userError s!"mapping comparator rejected: {reprStr error}")
    | .ok comparison =>
      have comparisonProjection : context.checked.catalog.project sourceKey = .ok comparison.type := by
        simpa only [CompatibleMapping.comparison_sourceType comparisonAccepted] using comparison.projection
      have keyType := Except.ok.inj (facts.2.1.symm.trans comparisonProjection)
      match mappingAccepted : SourceCoreCompatibleValues.encode 500 context (.mapping sourceKey sourceValue) carrier with
      | .error error => throw (IO.userError s!"mapping encoding rejected: {reprStr error}")
      | .ok encodedMapping =>
        match keyAccepted : SourceCoreCompatibleValues.encode 500 encodedMapping.context sourceKey keyCarrier with
        | .error error => throw (IO.userError s!"mapping key encoding rejected: {reprStr error}")
        | .ok encodedKey =>
          let environment := [encodedMapping.value, encodedKey.value]
          let before := [Value.integer (-99)]
          let missing := word 1000
          have _whole := encoded_lookup_run comparison layout facts.2.2.2 keyType projection facts.2.1 mappingAccepted keyAccepted
            mappingMeaning keyMeaning faithful (noFunctionObservations context.checked.catalog) [] [] environment before missing
            (.var 0) (.var 1) (.var rfl) (.var rfl)
          let header ← match encodedMapping.value with
            | .pair (.word header) _ => pure header
            | _ => throw (IO.userError "mapping carrier omitted raw header")
          assertTrue (encodedKey.context.registry.lookup header == some (.mapping sourceKey sourceValue)) "raw header identity erased"
          let lookup := SourceCoreMappingWithDefault.lookup layout missing comparison.expression (.var 0) (.var 1)
          assertTrue (infer? [SourceCoreMappingWithDefault.type layout, layout.keyType] lookup context.checked.catalog.definitions == some (LanguageResult.resultType layout.valueType)) "mapping lookup checker failed"
          let (result, store) ← completed lookup environment before
          assertTrue (store.length == before.length + context.checked.catalog.entries.length + 1) "mapping lookup administrative count changed"
          match expectedRead, result with
          | some expected, .inRight .word value => decoded encodedKey.context sourceValue value expected
          | none, .inLeft _ (.word token) => assertTrue (token == missing.add header) "missing-default raw header token changed"
          | _, _ => throw (IO.userError s!"mapping lookup outcome mismatch: {reprStr result}")
          let encodedReplacement ← match SourceCoreCompatibleValues.encode 500 encodedKey.context sourceValue replacementCarrier with
            | .ok encoded => pure encoded
            | .error error => throw (IO.userError s!"mapping replacement encoding rejected: {reprStr error}")
          let insert := SourceCoreMappingWithDefault.insert layout comparison.expression (.var 0) (.var 1) (.var 2)
          assertTrue (infer? [SourceCoreMappingWithDefault.type layout, layout.keyType, layout.valueType] insert context.checked.catalog.definitions == some (LanguageResult.resultType (SourceCoreMappingWithDefault.type layout))) "mapping insertion checker failed"
          let (inserted, insertStore) ← completed insert [encodedMapping.value, encodedKey.value, encodedReplacement.value] before
          assertTrue (insertStore.length == before.length + context.checked.catalog.entries.length + 1) "mapping insertion administrative count changed"
          match inserted with
          | .inRight .word value => decoded encodedReplacement.context (.mapping sourceKey sourceValue) value expectedInserted
          | _ => throw (IO.userError "standalone insertion unexpectedly applied missing-default guard")
          let keyId : ExpressionId := ⟨⟨owner, 7⟩⟩
          let route : SourceCoreCompatibleDataPlaces.Route := ⟨.mapping sourceKey sourceValue,
            SourceCoreMappingWithDefault.type layout, layout.valueType, [.index layout keyId sourceValue], none⟩
          let prepared ← match SourceCoreCompatibleDataPlaces.prepare context 200 route (word 900) (fun _ => missing) with
            | .ok prepared => pure prepared
            | .error error => throw (IO.userError s!"compatible place preparation failed: {reprStr error}")
          let getter := SourceCoreCompatibleDataPlaces.getter prepared layout.keyType
          let setter := SourceCoreCompatibleDataPlaces.setter prepared layout.keyType
          assertTrue (infer? [] getter context.checked.catalog.definitions == some (.function (.product (OptionalCell.cellType route.rootType) layout.keyType) (LanguageResult.resultType prepared.optionalLeaf))) "generated getter checker failed"
          assertTrue (infer? [] setter context.checked.catalog.definitions == some (.function (.product (OptionalCell.cellType route.rootType) (.product layout.keyType layout.valueType)) (LanguageResult.resultType route.rootType))) "generated setter checker failed"
          let (read, readStore) ← completed (.apply getter (.var 0)) [.pair (.inRight .unit encodedMapping.value) encodedKey.value] before
          assertTrue (readStore.length == before.length + context.checked.catalog.entries.length + 1) "getter allocation count changed"
          match expectedRead, read with
          | some expected, .inRight .word (.inRight .unit value) => decoded encodedReplacement.context sourceValue value expected
          | none, .inLeft _ (.word token) => assertTrue (token == missing.add header) "getter changed missing-default token"
          | _, _ => throw (IO.userError "generated getter result differs from lookup")
          let (updated, updateStore) ← completed (.apply setter (.var 0))
            [.pair (.inRight .unit encodedMapping.value) (.pair encodedKey.value encodedReplacement.value)] before
          match expectedRead, updated with
          | some _, .inRight .word value =>
            decoded encodedReplacement.context (.mapping sourceKey sourceValue) value expectedInserted
            assertTrue (updateStore.length == before.length + 2 * (context.checked.catalog.entries.length + 1)) "setter did not select before insert"
          | none, .inLeft _ (.word token) =>
            assertTrue (token == missing.add header) "setter missing-default token changed"
            assertTrue (updateStore.length == before.length + context.checked.catalog.entries.length + 1) "setter inserted after missing default"
          | _, _ => throw (IO.userError "setter guard/result mismatch")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"mapping fixture failed: {reprStr error}")
  let box ← match program.signatures.dataTypes.filter (·.name == "Box") with
    | [signature] => pure signature | _ => throw (IO.userError "mapping Box signature missing")
  let constructor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "mapping Box constructor missing")
  let boxType : TypeSystem.Ty := .nominal box.id []
  let item : DataConstructorInstantiation := ⟨constructor.id, [], [.word], boxType⟩
  let proxy : TypeSystem.Ty := .proxy .word
  let rawProxy : TypeSystem.Ty := .proxy (.comptime .word)
  let table : TypeSystem.Ty := .mapping .word rawProxy
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 300
      [.mapping .word proxy, .mapping proxy .word, .mapping .word boxType, .mapping .word table] with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"mapping catalog failed: {reprStr error}")
  let context := SourceCoreCompatibleValues.Context.initial checked
  let duplicates : SourceCoreDataValues.Value := .mapping .word rawProxy [(.word (word 1), .proxy (.comptime .word)), (.word (word 1), .proxy .word)]
  let sources : List (Dynamic.Value × Dynamic.Value) := [(.word (word 1), .proxy (.comptime .word)), (.word (word 1), .proxy .word)]
  have duplicatesMeaning : CompatibleEncoding.Means duplicates (.mapping .word rawProxy sources) := .mapping (.prepend (.word _) (.proxy _) (.prepend (.word _) (.proxy _) .empty))
  exercise context box.id .word rawProxy duplicates (.word (word 1)) (.proxy .word) sources (.word (word 1)) duplicatesMeaning (.word _)
    (some (.proxy (.comptime .word))) (.mapping .word rawProxy [(.word (word 1), .proxy .word), (.word (word 1), .proxy .word)])
  exercise context box.id .word rawProxy duplicates (.word (word 2)) (.proxy .word) sources (.word (word 2)) duplicatesMeaning (.word _)
    (some (.proxy (.comptime .word))) (.mapping .word rawProxy ([(.word (word 1), .proxy (.comptime .word)), (.word (word 1), .proxy .word), (.word (word 2), .proxy .word)]))
  exercise context box.id proxy .word (.mapping proxy .word [(.proxy .word, .word (word 3)), (.proxy (.comptime .word), .word (word 4))])
    (.proxy (.comptime .word)) (.word (word 8)) [(.proxy .word, .word (word 3)), (.proxy (.comptime .word), .word (word 4))] (.proxy (.comptime .word))
    (.mapping (.prepend (.proxy _) (.word _) (.prepend (.proxy _) (.word _) .empty))) (.proxy _)
    (some (.word (word 4))) (.mapping proxy .word [(.proxy .word, .word (word 3)), (.proxy (.comptime .word), .word (word 8))])
  exercise context box.id .word boxType (.mapping .word boxType []) (.word (word 1)) (.constructed item [.word (word 7)]) [] (.word (word 1))
    (.mapping .empty) (.word _) none (.mapping .word boxType [(.word (word 1), .constructed item [.word (word 7)])])
  exercise context box.id .word table (.mapping .word table []) (.word (word 1)) (.mapping .word rawProxy []) [] (.word (word 1))
    (.mapping .empty) (.word _) (some (.mapping .word rawProxy [])) (.mapping .word table [(.word (word 1), .mapping .word rawProxy [])])
  IO.println "compatible mapping lookup/default/fault/ordered update proofs GREEN"

end Tests.SourceCoreCompatibleMappingProofs
