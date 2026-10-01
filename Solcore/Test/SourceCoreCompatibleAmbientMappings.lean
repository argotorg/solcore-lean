import Solcore.SourceSemantics.CoreLowering.CompatibleMappingPlaceRuns
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingPreparation
import Solcore.SourceSemantics.CoreLowering.CompatiblePayloadMembers
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientPayload
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
import Solcore.Frontend.SourceCoreCallableIndexedLedger
import Solcore.Frontend.ProgramChecking

/-! Full-definition mapping regressions. An explicitly modeled anonymous
function captures a fresh frame constructor, so its value cannot be typed in
the base catalog. Mapping proofs retain that leaf and duplicate order. The
model does not authenticate arbitrary source closure bodies. A separate actual
indexed program supplies the real prefix/suffix receipt for raw alias/default
and duplicate update execution checks. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Solcore.Test.SourceCoreCompatibleAmbientMappings
open Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleMapping CompatibleEquality DataEquality

private def functionSource : TypeSystem.Ty := .function .unit .word
private def functionCore : Core.Ty := TaggedFunction.functionType .unit .word
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem existsChecked : (SourceCoreCompatibleCatalog.prepare signatures 30
    [.mapping .word functionSource] [] {} false).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 30
    [.mapping .word functionSource] [] {} false).toOption.get existsChecked
private def layout : Core.OrderedMapping.Layout := ⟨.word, functionCore, ⟨0⟩⟩
private def frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨1⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frame.definition]
private theorem frameRegistered : frame.Registered ambient.definitions := ⟨by cbv⟩
private theorem functionWellFormed : functionCore.WellFormed checked.catalog.definitions :=
  .product (.sum .unit .word) (.function .unit (.sum .word .word))
private theorem registered : layout.Registered checked.catalog.definitions :=
  ⟨.word, functionWellFormed, by cbv⟩
private def snapshot := SourceCoreCallableIndexedFrames.encode frame .empty
private def seven : Word := Word.ofNatModulo 7
private def closure : Value := .closure .unit (LanguageResult.resultType .word)
  (LanguageResult.success (.word seven)) [snapshot]
private def native : Value := .pair (.inLeft .word .unit) closure
private theorem nativeTyped (world : StoreTyping) : RuntimeValueHasType world native functionCore ambient.definitions :=
  .pair (.inLeft .unit) (.closure
    (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world frameRegistered .empty) .nil)
    (.inRight .word .word))

theorem fresh_capture_not_base_typed (world : StoreTyping) :
    ¬ RuntimeValueHasType world native functionCore checked.catalog.definitions := by
  intro typed
  cases typed with
  | pair _ closureTyped => cases closureTyped with
    | closure environment _ => cases environment with
      | cons captured _ => cases captured with
        | constructed selected _ => cases selected

private def functions (source : Dynamic.Closure) : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ sourceType value core type =>
    sourceType = functionSource ∧ value = .closure source ∧ core = native ∧ type = functionCore
  projection := by rintro _ _ _ _ _ _ _ ⟨rfl, _, _, rfl⟩; cbv
  runtime_hasType := by rintro _ _ _ _ _ _ _ ⟨_, _, rfl, rfl⟩; exact nativeTyped _
  source_function := by rintro _ _ _ _ _ _ _ ⟨_, rfl, _, _⟩; exact .closure source
  extend := fun related _ _ _ => related
private def identities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : IdentityFaithful identities := ⟨False.elim, fun impossible _ => False.elim impossible⟩
private theorem functionObservations (source : Dynamic.Closure) :
    FunctionObservations checked.catalog (functions source) identities := by
  rintro _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩
  exact .anonymous source .unit .word closure rfl
private def one : Word := Word.ofNatModulo 1
private def header : Word := Word.ofNatModulo 1
private def sources (source : Dynamic.Closure) : List (Dynamic.Value × Dynamic.Value) :=
  [(.word one, .closure source), (.word one, .closure source)]
private def entries : Core.OrderedMapping.Entries := [(.word one, native), (.word one, native)]
private theorem fields (source : Dynamic.Closure) (mapping : LocationMap) (world : StoreTyping) :
    Fields checked checked.staticRegistry (functions source) mapping world .word functionSource (sources source)
      header layout entries none := by
  refine ⟨⟨by decide⟩, by cbv, by cbv, by cbv, registered, ?_, ?_⟩
  · exact .entry (.word one) (.function ⟨rfl, rfl, rfl, rfl⟩)
      (.entry (.word one) (.function ⟨rfl, rfl, rfl, rfl⟩) (.empty _ _ _ _))
  · exact .absent (by intro impossible; cases impossible) (by cbv) functionWellFormed

/-- Both repeated function entries survive with full native typing. Their
captured frame cannot be justified by shrinking to the source catalog. -/
theorem function_entries_typed (source : Dynamic.Closure) (world : StoreTyping) :
    RuntimeValueHasType world (Core.OrderedMapping.encode layout entries) layout.type ambient.definitions :=
  (fields source [] world).stored.runtime_hasType registered

theorem function_default_absent (source : Dynamic.Closure) (world : StoreTyping) :
    RuntimeValueHasType world (.inLeft functionCore .unit) (.sum .unit functionCore) ambient.definitions :=
  (fields source [] world).default.runtime_hasType

private theorem comparatorExists : (SourceCoreCompatibleDataEquality.prepare 30 checked .word).toOption.isSome = true := by cbv
private def comparator := (SourceCoreCompatibleDataEquality.prepare 30 checked .word).toOption.get comparatorExists

/-- Actual generated helpers yield an independent first-match/default/missing
classification even when represented values contain fresh ambient closures. -/
theorem function_lookup (source : Dynamic.Closure) (store : Store) :
    ∃ result,
      ReadResult checked checked.staticRegistry (functions source) [] [] functionSource (.word one)
        (sources source) functionCore Word.zero header result ∧
      Evaluates [SourceCoreMappingWithDefault.value header none layout entries, .word one] store
        (SourceCoreMappingWithDefault.lookup layout Word.zero comparator.expression (.var 0) (.var 1)) result
        (Transport.lookupStore comparator layout
          [SourceCoreMappingWithDefault.value header none layout entries, .word one] store header none entries (.word one)) := by
  exact lookup_meaning comparator (by cbv) faithful (functionObservations source) (fields source [] []) (.word one)
    _ store Word.zero (.var 0) (.var 1) (.var rfl) (.var rfl)

private def index (id : ExpressionId) : SourceCoreCompatibleDataPlaces.PreparedIndex :=
  ⟨layout, id, 0, comparator.expression, Word.zero⟩
private def place (id : ExpressionId) : SourceCoreCompatibleDataPlaces.Prepared :=
  ⟨⟨.mapping .word functionSource, SourceCoreMappingWithDefault.type layout, functionCore,
    [.index layout id functionSource], none⟩, [.index (index id)], [(id, .word)], Word.zero⟩
private def setterInput (key : Word) : Value :=
  .pair (.inRight .unit (SourceCoreMappingWithDefault.value header none layout entries)) (.pair (.word key) native)

/-- Finite completion and reflection apply to the actual ordinary setter,
including the missing-default alternative. No child evaluation is a premise. -/
theorem function_setter_runs (source : Dynamic.Closure) (id : ExpressionId) (key : Word) (store : Store) :
    ∃ result finalStore administrative count,
      UpdateResult checked checked.staticRegistry (functions source) [] [] .word functionSource
        (.word key) (.closure source) (sources source) header layout none Word.zero result count ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (.apply (SourceCoreCompatibleDataPlaces.setter (place id) .word) (.var 0)) [setterInput key] store) =
          .done result finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (.apply (SourceCoreCompatibleDataPlaces.setter (place id) .word) (.var 0)) [setterInput key] store) =
          .done actual actualStore → actual = result ∧ actualStore = finalStore) ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  have certificate : Index checked (index id) := ⟨comparator, rfl, by cbv⟩
  exact setter_initialized_run certificate (place id) rfl rfl faithful (functionObservations source)
    (fields source [] []) (.word key) (.function ⟨rfl, rfl, rfl, rfl⟩)
    [setterInput key] store .word [.word key] (.var 0) rfl rfl (.var rfl)

private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog)
    (ambient : AmbientDefinitions catalog.definitions := .original _) : FunctionModel catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible

/-- The data-only codec receipt transports into any ambient function model;
no new native closure is inferred to be well typed under base definitions. -/
theorem encoded_ambient {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient}
    {expected : TypeSystem.Ty} {carrier : SourceCoreDataValues.Value}
    {encoded : SourceCoreCompatibleValues.Encoded fuel context expected carrier} {source : Dynamic.Value}
    (accepted : SourceCoreCompatibleValues.encode fuel context expected carrier = .ok encoded)
    (meaning : CompatibleEncoding.Means carrier source) (mapping : LocationMap) (world : StoreTyping) :
    ValueRep context.checked encoded.context.registry functions mapping world expected source encoded.value encoded.type :=
  (CompatibleEncoding.encode_represents_at (functions := noFunctions context.checked.catalog)
    accepted meaning mapping world).map_functions (initial := noFunctions context.checked.catalog) (future := functions) (fun impossible => False.elim impossible)

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def word (n : Nat) : Word := Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function main(seed: Word) returns (Word) { let cache: mapping(Word => Word); cache[0] = seed; return cache[0]; }"}] }

private def complete (code : Expr) (environment : Environment) (store : Store) : IO (Value × Store) := do
  let output ← match runStateful 100000 (.initial code environment store) with
    | .done value after => pure (value, after)
    | other => throw (IO.userError s!"ambient mapping helper: {reprStr other}")
  match runStateful 3 (.initial code environment store) with
  | .outOfFuel checkpoint =>
    match runStateful 100000 checkpoint with
    | .done value after => assertTrue (value == output.1 && after == output.2) "ambient mapping resume differs"
    | _ => throw (IO.userError "ambient mapping resume did not finish")
  | _ => throw (IO.userError "ambient mapping fixture failed to suspend")
  assertTrue (output.2.take store.length == store) "ambient mapping helper modified the existing store"
  pure output

def run : IO Unit := do
  let program ← get "ambient mapping source" (checkProgram workspace)
  let key ← match program.signatures.functions with
    | [signature] => pure (⟨signature.id, []⟩ : SourceSpecialization.SpecializationKey)
    | _ => throw (IO.userError "ambient mapping root missing")
  let plan ← match SourceSpecializationWorklist.run program [⟨key.declaration, []⟩] 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"ambient mapping plan: {reprStr other}")
  let automatic ← get "ambient mapping base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← get "ambient mapping indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let completion ← get "ambient mapping native start" (prepared.runSource key [.word (word 5)] 100000 500)
  let before := SourceCoreCallableIndexedLedger.store completion
  let full := CallableIndexedAmbient.ambientDefinitions prepared
  let context : SourceCoreCompatibleValues.Context := .initial automatic.checked
  let rawKey : TypeSystem.Ty := .comptime .word
  let rawValue : TypeSystem.Ty := .comptime .word
  let rawType : TypeSystem.Ty := .mapping rawKey rawValue
  let carrier : SourceCoreDataValues.Value := .mapping rawKey rawValue [(.word (word 1), .word (word 11)), (.word (word 1), .word (word 22))]
  let source : Dynamic.Value := .mapping rawKey rawValue [(.word (word 1), .word (word 11)), (.word (word 1), .word (word 22))]
  have sourceMeaning : CompatibleEncoding.Means carrier source := .mapping (.prepend (.word _) (.word _) (.prepend (.word _) (.word _) .empty))
  match accepted : SourceCoreCompatibleValues.encode 500 context rawType carrier with
  | .error error => throw (IO.userError s!"ambient mapping encode: {reprStr error}")
  | .ok encoded =>
    have represented := encoded_ambient (functions := noFunctions automatic.checked.catalog full) accepted sourceMeaning [] []
    have _view := mapping_fields represented rfl
    let layout ← get "ambient mapping layout" (automatic.checked.catalog.mappingLayout rawKey rawValue)
    let comparator ← get "ambient mapping comparison" (SourceCoreCompatibleDataEquality.prepare 500 automatic.checked rawKey)
    let nativeHeader ← match encoded.value with
      | .pair (.word header) _ => pure header
      | _ => throw (IO.userError "ambient mapping raw header missing")
    assertTrue (encoded.context.registry.lookup nativeHeader == some (.mapping rawKey rawValue)) "ambient mapping erased raw header"
    for sought in [1, 2] do
      let lookup := SourceCoreMappingWithDefault.lookup layout (word 1000) comparator.expression (.var 0) (.var 1)
      assertTrue (infer? [SourceCoreMappingWithDefault.type layout, .word] lookup full.definitions == some (LanguageResult.resultType .word))
        "ambient lookup failed actual full-definition checker"
      let (result, after) ← complete lookup [encoded.value, .word (word sought)] before
      assertTrue (result == .inRight .word (.word (word (if sought == 1 then 11 else 0)))) "ambient first-match/default changed"
      assertTrue (after.length == before.length + automatic.checked.catalog.entries.length + 1) "ambient lookup allocation count changed"
      let inserted := SourceCoreMappingWithDefault.insert layout comparator.expression (.var 0) (.var 1) (.var 2)
      let (result, _) ← complete inserted [encoded.value, .word (word sought), .word (word 99)] before
      let updated ← match result with
        | .inRight .word value => pure value | _ => throw (IO.userError "ambient insert failed")
      let decoded ← get "ambient inserted decode" (SourceCoreCompatibleValues.decode 500 encoded.context rawType updated)
      let expected : SourceCoreDataValues.Value := .mapping rawKey rawValue
        (if sought == 1 then [(.word (word 1), .word (word 99)), (.word (word 1), .word (word 22))]
         else [(.word (word 1), .word (word 11)), (.word (word 1), .word (word 22)), (.word (word 2), .word (word 99))])
      assertTrue (decoded == expected) "ambient insert changed ordered duplicates/raw metadata"
      let keyId : ExpressionId := ⟨⟨key.declaration, 7⟩⟩
      let route : SourceCoreCompatibleDataPlaces.Route := ⟨rawType, SourceCoreMappingWithDefault.type layout,
        layout.valueType, [.index layout keyId rawValue], none⟩
      let place ← get "ambient actual place preparation"
        (SourceCoreCompatibleDataPlaces.prepare context 500 route (word 900) (fun _ => word 1000))
      let getter := SourceCoreCompatibleDataPlaces.getter place layout.keyType
      let setter := SourceCoreCompatibleDataPlaces.setter place layout.keyType
      assertTrue (infer? [] setter full.definitions == some (.function
        (.product (OptionalCell.cellType route.rootType) (.product layout.keyType layout.valueType))
        (LanguageResult.resultType route.rootType))) "ambient setter failed actual full-definition checker"
      let (read, _) ← complete (.apply getter (.var 0))
        [.pair (.inRight .unit encoded.value) (.word (word sought))] before
      assertTrue (read == .inRight .word (.inRight .unit (.word (word (if sought == 1 then 11 else 0)))))
        "ambient getter lost snapshot selection/default"
      let (written, after) ← complete (.apply setter (.var 0))
        [.pair (.inRight .unit encoded.value) (.pair (.word (word sought)) (.word (word 99)))] before
      match written with
      | .inRight .word value =>
        let source ← get "ambient setter decode" (SourceCoreCompatibleValues.decode 500 encoded.context rawType value)
        assertTrue (source == expected) "ambient setter changed duplicate order/raw header"
      | _ => throw (IO.userError "ambient setter failed")
      assertTrue (after.length == before.length + 2 * (automatic.checked.catalog.entries.length + 1))
        "ambient setter changed lookup-before-insert allocation count"
  -- This separate explicit leaf model uses the synthetic ambient frame table.
  -- Missing function defaults must fail before insertion, preserving the header.
  let syntheticId : ExpressionId := ⟨⟨key.declaration, 8⟩⟩
  let syntheticSetter := SourceCoreCompatibleDataPlaces.setter (place syntheticId) .word
  assertTrue (infer? [] syntheticSetter ambient.definitions == some (.function
    (.product (OptionalCell.cellType (SourceCoreMappingWithDefault.type layout)) (.product .word functionCore))
    (LanguageResult.resultType (SourceCoreMappingWithDefault.type layout)))) "function-valued ambient setter failed checker"
  for sought in [1, 2] do
    let (result, after) ← complete (.apply syntheticSetter (.var 0)) [setterInput (word sought)] []
    if sought == 1 then
      assertTrue (result == .inRight .word (SourceCoreMappingWithDefault.value header none layout entries))
        "function-valued mapping changed duplicate payloads"
      assertTrue (after.length == 2 * (checked.catalog.entries.length + 1)) "function setter skipped its lookup or insertion"
    else
      assertTrue (result == .inLeft (SourceCoreMappingWithDefault.type layout) (.word header))
        "function-valued mapping changed missing-default token"
      assertTrue (after.length == checked.catalog.entries.length + 1) "function setter inserted after missing default"
  IO.println "source core compatible ambient mapping tests passed"

end Solcore.Test.SourceCoreCompatibleAmbientMappings
