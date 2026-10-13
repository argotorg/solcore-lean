import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory

/-! Extract selected functions from an authentic named result. The whole Source
value and native payload come from execution; the real recursive export supplies
ordered leaves and each leaf's validation budget. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Core GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open RecursiveNamedPublicFunctionHistory (Entry Caller Result Addition)
open RecursiveNamedPublicNestedOutputSelections (Selection Selected)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {receiving : SourceCoreRawMetadata.Registry}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {owner : OwnedKey keys} {caller : Caller headers keys mapping world heap store}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  {artifact : Artifact} {checkpoint : Checkpoint artifact} {completion : Completion artifact}
  {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}

/-- The genuine full result and successful output receipt determine the selected
Source leaves and the exact history addition, with no body or encoding premise. -/
theorem named_collection {recipe : Recipe} (sameCompiled : recipe.compiled = compiled)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    {actualRegistry : SourceCoreRawMetadata.Registry}
    (atRegistry : completion.session.RegistryAt actualRegistry)
    (extension : SourceCoreRawMetadata.Extends receiving actualRegistry)
    (selection : Selection header.function.resultType completion.value) :
    ∃ (source : Dynamic.Value) (payload : Core.Value) (added : List Entry),
      outcome = .value source ∧ native = .inRight .word payload ∧
      Selected compiled.compatible.checked completion.session selection source payload header.output outputFuel added ∧
      added.map Entry.handle = selection.handles ∧
      Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel
        header.function.resultType header.output outcome native added := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨source, sourceValue, represented, _heaps, _world, _returned, _related, _stable, _typed, _valueTyped⟩ :=
    RecursiveNamedPublicReturnedValues.returned_value result decoded
  have nativeValue : native = .inRight .word payload := by
    have represented := result.2.1
    cases represented with
    | value represented =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
        subst payload
        rfl
    | fault represented => cases decoded
  obtain ⟨_sourceType, encoded, encodedAt, payloadAt⟩ := succeeded.reimports_payload requested decoded
  have before := atRegistry.symm ▸ extension
  obtain ⟨added, selected, handles⟩ := selection.collect atRecipe
    (congrArg (fun compiled => compiled.compatible.checked) sameCompiled).symm represented
    encodedAt rfl payloadAt before
  exact ⟨source, payload, added, sourceValue, nativeValue, selected, handles,
    .selectNestedCompatible requested rfl sourceValue nativeValue selection selected⟩

/-- Selecting both public function leaves recovers exactly two ordered Source
entries, retaining their original payload types and recursive encoder fuel. -/
theorem pair_entries {checked : SourceCoreCompatibleCatalog.Checked}
    {session : Session artifact} {leftType rightType : TypeSystem.Ty}
    {left right : SourceCorePublicValues.Handle} {source : Dynamic.Value}
    {payload : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected checked session
      (Selection.product (Selection.function (type := leftType) (handle := left))
        (Selection.function (type := rightType) (handle := right)))
      source payload nativeType fuel entries) :
    ∃ first second : Entry,
      entries = [first, second] ∧ source = .product first.source second.source ∧
      first.sourceType = leftType ∧ second.sourceType = rightType ∧
      first.handle = left ∧ second.handle = right := by
  cases selected with
  | product first second =>
      cases first with
      | function firstImported =>
          cases second with
          | function secondImported => exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

def pairSelection {sourceType : TypeSystem.Ty} {publicValue : SourceCorePublicValues.Value}
    {leftType rightType : TypeSystem.Ty} {left right : SourceCorePublicValues.Handle}
    (raw : sourceType = .product leftType rightType)
    (value : publicValue = .product (.function left) (.function right)) : Selection sourceType publicValue := by
  cases raw
  cases value
  exact .product .function .function

/-- Transport along the actual result signature and public value leaves the
selected order and Source product unchanged. -/
theorem pair_selection_entries {checked : SourceCoreCompatibleCatalog.Checked}
    {session : Session artifact} {sourceType leftType rightType : TypeSystem.Ty}
    {publicValue : SourceCorePublicValues.Value} {left right : SourceCorePublicValues.Handle}
    {source : Dynamic.Value} {payload : Core.Value} {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (raw : sourceType = .product leftType rightType)
    (value : publicValue = .product (.function left) (.function right))
    (selected : Selected checked session (pairSelection raw value) source payload nativeType fuel entries) :
    ∃ first second : Entry,
      entries = [first, second] ∧ source = .product first.source second.source ∧
      first.sourceType = leftType ∧ second.sourceType = rightType ∧
      first.handle = left ∧ second.handle = right := by
  cases raw
  cases value
  exact pair_entries selected

theorem encoded_function_shape {session : Session artifact} {fuel : Nat}
    {registry : SourceCoreRawMetadata.Registry} {parameter result : TypeSystem.Ty}
    {publicValue : SourceCorePublicValues.Value} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry (.function parameter result) publicValue encoded)
    (paired : ∃ a b, encoded.value = .pair a b) :
    ∃ handle, publicValue = .function handle := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      cases publicValue <;> try cases accepted
      case function handle => exact ⟨handle, rfl⟩
      case constructed metadata values =>
        obtain ⟨_, _, _, _, _, _, _, _, same⟩ := accepted.constructed
        obtain ⟨_, _, paired⟩ := paired
        rw [same] at paired
        cases paired

theorem encoded_pair_shape {session : Session artifact} {fuel : Nat}
    {registry : SourceCoreRawMetadata.Registry} {leftType rightType : TypeSystem.Ty}
    {publicValue : SourceCorePublicValues.Value} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry (.product leftType rightType) publicValue encoded)
    (paired : ∃ a b, encoded.value = .pair a b) :
    ∃ left right, publicValue = .product left right := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      cases publicValue <;> try cases accepted
      case product left right => exact ⟨left, right, rfl⟩
      case constructed metadata values =>
        obtain ⟨_, _, _, _, _, _, _, _, same⟩ := accepted.constructed
        obtain ⟨_, _, paired⟩ := paired
        rw [same] at paired
        cases paired

private theorem native_function_pair {catalog : SourceCoreCompatibleCatalog.Catalog}
    {native : Core.Value} {parameter result : Core.Ty} {nativeWorld : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    (typed : Core.RuntimeValueHasType nativeWorld native (catalog.functionType parameter result) definitions) :
    ∃ a b, native = .pair a b := by
  unfold SourceCoreCompatibleCatalog.Catalog.functionType at typed
  split at typed <;> cases typed <;> exact ⟨_, _, rfl⟩

/-- A genuine encoded pair of represented nullary Word functions has exactly
that public shape. This derives the shape of every sufficiently fueled export. -/
theorem pair_public_shape {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {model : FunctionModel checked.catalog ambient} {sourceRegistry : SourceCoreRawMetadata.Registry}
    {sourceMap : LocationMap} {sourceWorld : StoreTyping} {source : Dynamic.Value}
    {session : Session artifact} {fuel : Nat} {registry : SourceCoreRawMetadata.Registry}
    {publicValue : SourceCorePublicValues.Value} {payload : Core.Value} {nativeType : Core.Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (represented : ValueRep checked sourceRegistry model sourceMap sourceWorld
      (.product (.function .unit .word) (.function .unit .word)) source payload nativeType)
    (accepted : session.RawEncodedAt fuel registry
      (.product (.function .unit .word) (.function .unit .word)) publicValue encoded)
    (payloadAt : encoded.value = payload) :
    ∃ left right, publicValue = .product (.function left) (.function right) := by
  have projected := represented.projection
  have nativeEq : nativeType = .product (checked.catalog.functionType .unit .word)
      (checked.catalog.functionType .unit .word) := by
    simpa [SourceCoreCompatibleCatalog.Catalog.project] using (Except.ok.inj projected).symm
  have typed := represented.runtime_hasType
  rw [nativeEq] at typed
  cases typed with
  | pair firstTyped secondTyped =>
      obtain ⟨left, right, publicEq⟩ := encoded_pair_shape accepted ⟨_, _, payloadAt⟩
      subst publicValue
      obtain ⟨remaining, _fuelEq, first, second, firstAt, secondAt, encodedEq⟩ := accepted.product rfl
      rw [encodedEq] at payloadAt
      have payloads := Core.Value.pair.inj payloadAt
      obtain ⟨leftHandle, leftEq⟩ := encoded_function_shape firstAt
        (payloads.1.symm ▸ native_function_pair firstTyped)
      obtain ⟨rightHandle, rightEq⟩ := encoded_function_shape secondAt
        (payloads.2.symm ▸ native_function_pair secondTyped)
      exact ⟨leftHandle, rightHandle, by rw [leftEq, rightEq]⟩

end Tests.SourceCoreRecursiveFormation
