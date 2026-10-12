import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryEncoding
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectHandleMeaning

/-! Packed host arguments keep the original encoder and current function
history. Structural input descriptions supply Source values; no representation
or body execution law is a premise. Inputs that register new raw metadata need
an actual extension into the chosen receiving registry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open CallableIndexedOwnedFunctionValues (Header)

/-- The actual direct startup, including its complete packed input and current
native store. Packing has no implicit host-list arity convention. -/
structure StartAt {artifact : Artifact} (session : Session artifact)
    (handle : SourceCorePublicValues.Handle) (argument : SourceCorePublicValues.Value) (fuel : Nat)
    (checkpoint : Checkpoint artifact) (recipe : Recipe) (world : StoreTyping) (store : Store)
    (parameter result : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
    (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context) : Prop where
  recipe_eq : ArtifactRecipe artifact recipe
  state : session.NativeAt world store
  original : checkpoint.HandleStart session handle argument fuel
  selected : session.HandleSelectionAt handle parameter result nativeParameter nativeResult callable
  parameterProjection : recipe.compiled.compatible.checked.catalog.project parameter = .ok nativeParameter
  resultProjection : recipe.compiled.compatible.checked.catalog.project result = .ok nativeResult
  requested : checkpoint.ResultTypeAt result
  payloadType : checkpoint.PayloadTypeAt nativeResult
  callableTyped : RuntimeValueHasType world callable (CallableContract.functionType nativeParameter nativeResult)
    recipe.compiled.indexed.layouts.definitions
  packedTyped : RuntimeValueHasType world packed nativeParameter recipe.compiled.indexed.layouts.definitions
  initial : CheckpointInitial checkpoint CallableIndexedLambdaCalls.applyPayload
    (callable :: packed :: SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) store
  values : CheckpointValues checkpoint encodedValues
  owner : encodedValues.checked = recipe.compiled.compatible.checked
  raw : ∃ (before : SourceCoreRawMetadata.Registry)
    (encoded : SourceCoreCompatibleValues.Extended before Core.Value),
    session.RegistryAt before ∧ before.signatures = recipe.compiled.compatible.checked.signatures ∧
    session.RawEncodedAt fuel before parameter argument encoded ∧
    encoded.value = packed ∧ encoded.registry = encodedValues.registry

/-- Inverting the successful original startup derives all input and state
receipts. The real selection fixes the requested raw signature. -/
theorem of_original {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {checkpoint : Checkpoint artifact} {fuel : Nat} {world : StoreTyping} {store : Store}
    (atRecipe : ArtifactRecipe artifact recipe) (nativeAt : session.NativeAt world store)
    (started : checkpoint.HandleStart session handle argument fuel) :
    ∃ parameter result nativeParameter nativeResult callable packed encodedValues,
      StartAt session handle argument fuel checkpoint recipe world store
        parameter result nativeParameter nativeResult callable packed encodedValues := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst actualRecipe
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, before, raw, encodedValues,
    selected, registryAt, encoded, valuesAt, rawRegistry, owner, packedTyped, requested, payloadType, initial⟩ :=
    started.details
  have selectedSpec := selected.spec
  cases session
  rename_i sessionAuthority actualWorld actualStore stored environmentTyped slots values valuesOwner sourcePrefix
  change actualWorld = world ∧ actualStore = store at nativeAt
  rcases nativeAt with ⟨rfl, rfl⟩
  have beforeOwner : before.signatures = recipe.compiled.compatible.checked.signatures := by
    change values.registry = before at registryAt
    rw [← registryAt]
    exact values.registryOwner.trans
      (congrArg SourceCoreCompatibleCatalog.Checked.signatures valuesOwner)
  refine ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, raw.value, encodedValues,
    ⟨rfl, ⟨rfl, rfl⟩, started, selected, selectedSpec.2.2.1, selectedSpec.2.2.2.1,
      requested, payloadType, selectedSpec.2.2.2.2.2.1, packedTyped, ?_, ?_, owner,
      before, raw, registryAt, beforeOwner, encoded, rfl, rawRegistry.symm⟩⟩
  · cases checkpoint
    exact initial
  · cases checkpoint
    exact valuesAt

/-- Whole function exports can identify the exact selected raw signature. -/
theorem actual_start {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {checkpoint : Checkpoint artifact} {fuel : Nat} {world : StoreTyping} {store : Store}
    {parameter result : TypeSystem.Ty}
    (atRecipe : ArtifactRecipe artifact recipe) (nativeAt : session.NativeAt world store)
    (handleType : handle.sourceType = .function parameter result)
    (started : checkpoint.HandleStart session handle argument fuel) :
    ∃ nativeParameter nativeResult callable packed encodedValues,
      StartAt session handle argument fuel checkpoint recipe world store
        parameter result nativeParameter nativeResult callable packed encodedValues := by
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues, actual⟩ :=
    of_original atRecipe nativeAt started
  obtain ⟨rfl, rfl⟩ := actual.selected.signature handleType
  exact ⟨nativeParameter, nativeResult, callable, packed, encodedValues, actual⟩

/-- Prior real import proves compatibility with the selected raw signature.
Source annotations remain independent from annotations erased by a containing
product's original encoder and decoder. -/
theorem actual_start_compatible {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {checkpoint : Checkpoint artifact} {fuel oldFuel : Nat} {world : StoreTyping} {store : Store}
    {parameter result : TypeSystem.Ty} {native : Core.Value}
    (atRecipe : ArtifactRecipe artifact recipe) (nativeAt : session.NativeAt world store)
    (imported : session.EncodesAt oldFuel (.function parameter result) (.function handle) native)
    (started : checkpoint.HandleStart session handle argument fuel) :
    ∃ actualParameter actualResult nativeParameter nativeResult callable packed encodedValues,
      StartAt session handle argument fuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result := by
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues, actual⟩ :=
    of_original atRecipe nativeAt started
  have actualView := actual.selected.spec.2.1
  have importedView := imported.function_type
  have same := TypeSystem.Ty.function.inj (actualView.symm.trans importedView.symm)
  exact ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues, actual, same⟩

section Inputs
variable {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
  {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
  {checkpoint : Checkpoint artifact} {fuel : Nat} {world : StoreTyping} {store : Store}
  {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
  {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session handle argument fuel checkpoint recipe world store
    parameter result nativeParameter nativeResult callable packed encodedValues)

include started

/-- Existing history supplies current meanings for every nested handle. The
actual encoder supplies the packed native payload and all registry changes. -/
theorem StartAt.history_input_compatible
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
    {receiving : SourceCoreRawMetadata.Registry}
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {mapping : LocationMap} {heap : Dynamic.Heap} {caller : Caller headers keys mapping world heap store}
    {entries : List Entry} {source : Dynamic.Value} {sourceParameter : TypeSystem.Ty}
    (history : History headers keys functions receiving anchor session mapping world heap store caller entries)
    (receipt : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      sourceParameter argument source)
    (compatible : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType sourceParameter)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving) :
    ValueRep recipe.compiled.compatible.checked receiving functions mapping world
      sourceParameter source packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context heap source sourceParameter := by
  have current := history.current
  obtain ⟨meaning, sourceTyped⟩ := RecursiveNamedPublicFunctionHistoryEncoding.Input.meaning
    receipt started.recipe_eq
    (fun entry member => (current.2.2.2.2 entry member).1)
    (fun entry member => (current.2.2.2.2 entry member).2.1)
    (fun entry member => (current.2.2.2.2 entry member).2.2)
  obtain ⟨before, encoded, _registry, owner, accepted, valueEq, registryEq⟩ := started.raw
  have typed := started.packedTyped
  rw [← valueEq] at typed
  have extended : SourceCoreRawMetadata.Extends encoded.registry receiving := registryEq ▸ metadata
  have represented := meaning owner compatible accepted started.parameterProjection typed extended
  rw [valueEq] at represented
  exact ⟨represented, sourceTyped⟩

/-- Exact source signatures are the reflexive compatibility case. -/
theorem StartAt.history_input
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
    {receiving : SourceCoreRawMetadata.Registry}
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {mapping : LocationMap} {heap : Dynamic.Heap} {caller : Caller headers keys mapping world heap store}
    {entries : List Entry} {source : Dynamic.Value}
    (history : History headers keys functions receiving anchor session mapping world heap store caller entries)
    (receipt : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument source)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving) :
    ValueRep recipe.compiled.compatible.checked receiving functions mapping world parameter source packed nativeParameter ∧
      Dynamic.ValueHasType anchor.function.context heap source parameter :=
  started.history_input_compatible history receipt rfl metadata

/-- A whole-function export retains literal requested result type equality. -/
theorem StartAt.requested_exact {expectedParameter expectedResult : TypeSystem.Ty}
    (handleType : handle.sourceType = .function expectedParameter expectedResult) :
    checkpoint.ResultTypeAt expectedResult := by
  have same := started.selected.signature handleType
  exact same.2 ▸ started.requested

/-- The retained callee encoding identifies exactly the original selected
native callable, including its captured environment. -/
theorem StartAt.callable_eq {oldFuel : Nat} {expected : TypeSystem.Ty} {native : Core.Value}
    (imported : session.EncodesAt oldFuel expected (.function handle) native) : callable = native :=
  started.selected.callable_eq imported

/-- Actual simple input encoding preserves the session's metadata registry. -/
theorem StartAt.simple_registry (simple : SimplePublic argument)
    {registry : SourceCoreRawMetadata.Registry} (atRegistry : session.RegistryAt registry) :
    encodedValues.registry = registry := by
  have same := started.original.simple_registry simple
  have values := started.values
  cases checkpoint
  change _ = encodedValues at values
  dsimp only at same
  rw [values] at same
  exact same.trans atRegistry

/-- The real encoder preserves metadata for arbitrary products of simple
values and retained function handles. -/
theorem StartAt.function_tree_registry (simple : FunctionTreeSimple argument)
    {registry : SourceCoreRawMetadata.Registry} (atRegistry : session.RegistryAt registry) :
    encodedValues.registry = registry := by
  obtain ⟨before, encoded, beforeAt, _owner, accepted, _value, registryEq⟩ := started.raw
  have encodedRegistry := accepted.function_tree_registry simple
  have beforeEq : before = registry := beforeAt.symm.trans atRegistry
  exact registryEq.symm.trans (encodedRegistry.trans beforeEq)

/-- Metadata-free packed input trees derive their receiving condition from
the actual session registry, including handles at arbitrary product depth. -/
theorem StartAt.history_input_function_tree
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
    {receiving registry : SourceCoreRawMetadata.Registry}
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {mapping : LocationMap} {heap : Dynamic.Heap} {caller : Caller headers keys mapping world heap store}
    {entries : List Entry} {source : Dynamic.Value}
    (history : History headers keys functions receiving anchor session mapping world heap store caller entries)
    (receipt : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument source)
    (simple : FunctionTreeSimple argument) (atRegistry : session.RegistryAt registry)
    (extension : SourceCoreRawMetadata.Extends registry receiving) :
    ValueRep recipe.compiled.compatible.checked receiving functions mapping world
      parameter source packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context heap source parameter := by
  apply started.history_input history receipt
  rw [started.function_tree_registry simple atRegistry]
  exact extension

/-- The successful exporter returns the very metadata context retained by
this startup, allowing the next invocation to use the actual registry. -/
theorem StartAt.returned_registry
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {native : Core.Value} {finalStore : Store} {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion) :
    completion.session.RegistryAt encodedValues.registry := by
  have registry := started.original.returned_registry succeeded
  have values := started.values
  cases checkpoint
  change _ = encodedValues at values
  dsimp only at registry
  rw [values] at registry
  exact registry
end Inputs
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
