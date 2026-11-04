import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBootstrapGlobals
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataInputs
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeFactoryMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSelectedExpressionFactory
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallScalarArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceSignatureFacts
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedRows
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedResidualExpressionFactory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedRetainedSubstitutionFacts
import Solcore.SourceSemantics.SubstitutionCorrespondence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration

/-!
# Recursive named public tests

Public entries of recursive named functions: reached selection, residuals and retained results.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPublicBootstrapGlobals
/-! Formal consumers connect the actual owned cache to the public native
checker after fresh initialization. IO audits the whole ordered cache, exact
closure bodies and captures, occupied slots, checker rejection and both native
and public bootstrap resumption. Source body meaning is outside this unit. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicBootstrapGlobals
open Solcore Core Frontend SourceSemantics.CoreLowering
open RecursiveGlobalInitializationMeaning

section Formal
variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  (cache : SourceCoreCallableIndexedTemplates.Cache compiled.indexed)

theorem public_environment :
    RecursiveNamedCatalogPreparedInitialization.environment compiled =
      SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed :=
  RecursiveNamedPublicBootstrapGlobals.environment_eq compiled

theorem actual_complete_native_slots :
    cache.nativeGlobals.length = compiled.indexed.base.globals.length ∧
      ∀ slot, slot ∈ cache.nativeGlobals →
        (RecursiveNamedCatalogPreparedInitialization.store compiled)[slot.1]? = some slot.2 :=
  ⟨RecursiveNamedPublicBootstrapGlobals.native_globals_length compiled cache,
    fun _ member => RecursiveNamedPublicBootstrapGlobals.native_slot compiled cache member⟩

theorem actual_cached_code_capture {slot : Nat} {code : Expr}
    (cached : compiled.indexed.secondPass.closures[slot]? = some code) :
    ∃ row, (RecursiveNamedCachedRows.rows compiled)[slot]? = some row ∧ code = row.expression ∧
      (RecursiveNamedCatalogPreparedInitialization.store compiled)[RecursiveNamedCatalogInitialization.location
        compiled.indexed.base.globals slot]? = some (.inRight .unit
          (installedValue (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) slot row)) :=
  RecursiveNamedPublicBootstrapGlobals.cached_slot compiled cached

theorem actual_public_check :
    ∃ globals : SourceCoreCallableIndexedTemplates.Globals compiled.indexed
        (RecursiveNamedCatalogPreparedInitialization.store compiled),
      SourceCoreCallableNativeSlots.checkPreparedGlobals cache.nativeGlobals cache.nativeGlobalsGenerated
        (RecursiveNamedCatalogPreparedInitialization.store compiled) = .ok globals :=
  RecursiveNamedPublicBootstrapGlobals.globals_checked compiled cache

variable {recipe : SourceCoreIndexedSession.Recipe}
  (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
include accepted in
theorem actual_completed_public_check {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧
      ∃ globals : SourceCoreCallableIndexedTemplates.Globals recipe.compiled.indexed finalStore,
        SourceCoreCallableNativeSlots.checkPreparedGlobals recipe.templates.nativeGlobals recipe.templates.nativeGlobalsGenerated
          finalStore = .ok globals :=
  RecursiveNamedPublicBootstrapGlobals.completed_globals accepted completed
end Formal

private def content : String := String.intercalate "\n" [
  "function step(value: Word) returns (Word) { return value + 1; }",
  "function left(n: Word) returns (Bool) { if (n == 0) { return true; } return right(n - 1); }",
  "function right(n: Word) returns (Bool) { if (n == 0) { return false; } return left(n - 1); }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { let extra = step(seed); return lam(value: Word) -> Word { extra += value; return extra; }; }",
  "function terminal(flag: Bool) returns (Word) { if (flag) { return 7; } else { return 9; } }",
  "function failed() returns (Word) { let gap: Word; return gap; }",
  "function zero() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def finish (state : State) : IO (Value × Store) :=
  match runStateful 300000 state with
  | .done value store => pure (value, store)
  | other => throw (IO.userError s!"public bootstrap globals did not finish: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "public bootstrap globals" content
    ["step", "left", "right", "make", "terminal", "failed", "zero"]
  let recipe ← get "public bootstrap recipe" (SourceCoreIndexedSession.Recipe.prepare compiled)
  let base := compiled.indexed.base
  let rows := RecursiveNamedCachedRows.rows compiled
  let canonical := RecursiveNamedCatalogPreparedInitialization.environment compiled
  let publicGlobals := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed
  require (reprStr canonical == reprStr publicGlobals) "actual initial environment differs from public globals"
  require (rows.length == base.globals.length && recipe.templates.nativeGlobals.length == base.globals.length)
    "public bootstrap omits a cached/global slot"
  let expectedSlots := rows.zipIdx.map fun (row, slot) =>
    (RecursiveNamedCatalogInitialization.location base.globals slot, Value.inRight .unit (installedValue publicGlobals slot row))
  require (reprStr recipe.templates.nativeGlobals == reprStr expectedSlots)
    "actual generator changed ordered full code/capture slots"
  let (value, store) ← finish (.initial recipe.bootstrap [] [])
  require (reprStr value == reprStr (Value.inRight .word .unit) &&
    reprStr store == reprStr (RecursiveNamedCatalogPreparedInitialization.store compiled))
    "closed fresh initialization changed value or whole store"
  require (store.length == base.globals.length + 1 &&
    reprStr store[0]? == reprStr (some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame .empty)))
    "fresh initialization changed frame zero or physical slot count"
  for (row, slot) in rows.zipIdx do
    let location := RecursiveNamedCatalogInitialization.location base.globals slot
    require (reprStr publicGlobals[slot]? == reprStr (some (Value.cellRef (OptionalCell.cellType (.function row.parameter row.result)) location)))
      "public environment lost actual full signature/reference order"
    require (reprStr store[location]? == reprStr (some (Value.inRight .unit (installedValue publicGlobals slot row))))
      "cached code, Unit prefix or captured public globals changed"
  for (location, closure) in recipe.templates.nativeGlobals do
    require (reprStr store[location]? == reprStr (some closure)) "generated native slot missing in bootstrap store"
    require (!(SourceCoreCallableNativeSlots.checkPreparedGlobals recipe.templates.nativeGlobals recipe.templates.nativeGlobalsGenerated
      (store.set location .unit)).isOk) "public checker accepted a corrupted installed closure"
  require (SourceCoreCallableNativeSlots.checkPreparedGlobals recipe.templates.nativeGlobals recipe.templates.nativeGlobalsGenerated store).isOk
    "public checker rejected closed initialization"
  require (SourceCoreCallableNativeSlots.checkPreparedGlobals recipe.templates.nativeGlobals recipe.templates.nativeGlobalsGenerated
    (store ++ [.word (Word.ofNatModulo 88)])).isOk "public global checker changed occupied slots under extra cell"
  let (_, shiftedStore) ← finish (.initial recipe.bootstrap [] [.word (Word.ofNatModulo 88)])
  require (!(SourceCoreCallableNativeSlots.checkPreparedGlobals recipe.templates.nativeGlobals recipe.templates.nativeGlobalsGenerated shiftedStore).isOk)
    "fresh-base-zero checker accepted a displaced native initialization"
  for fuel in [0, 1, 43, 300000] do
    let resumed ← match runStateful fuel (.initial recipe.bootstrap [] []) with
      | .done value store => pure (value, store)
      | .outOfFuel state => finish state
      | other => throw (IO.userError s!"public bootstrap native fault: {reprStr other}")
    require (reprStr resumed == reprStr (value, store)) s!"full fresh native bootstrap resume changed {fuel}"
    let artifact ← recipe.open
    let bootstrap ← artifact.bootstrapFresh
    let session ← match bootstrap.resume fuel with
      | .ready session => pure session
      | .outOfFuel next => match next.resume 300000 with
        | .ready session => pure session
        | .error error => throw (IO.userError s!"public bootstrap resume rejected globals: {reprStr error}")
        | .outOfFuel _ => throw (IO.userError "public bootstrap resume did not finish")
      | .error error => throw (IO.userError s!"public bootstrap rejected globals: {reprStr error}")
    require (session.installedGlobalsPresent && session.heapSize == store.length)
      "public bootstrap lacks complete installed globals"
    let step ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "step"
    let outcome ← get "public call after bootstrap" (← session.run step [.word (Word.ofNatModulo 40)] 300000)
    let afterStep ← match outcome with
      | .succeeded result =>
        require (result.value == .word (Word.ofNatModulo 41) && result.session.installedGlobalsPresent)
          "public success changed installed globals or result"
        pure result.session
      | _ => throw (IO.userError "public initialized step did not succeed")
    let failed ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "failed"
    let outcome ← get "public fault after bootstrap" (← afterStep.run failed [] 300000)
    match outcome with
    | .failed _ session => require session.installedGlobalsPresent "public language fault replaced installed globals"
    | _ => throw (IO.userError "public initialized fault changed category")
  IO.println "public bootstrap globals: complete ordered native slots/code/captures, exact public environment, checker rejection and full native/public resume GREEN"

end Tests.SourceCoreRecursiveNamedPublicBootstrapGlobals
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPublicDataInputs
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicDataInputs
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicDataInputs

theorem actual_start_inputs {artifact : Artifact} (session : Session artifact)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact}
    (accepted : session.start key arguments fuel = .ok checkpoint)
    (data : ∀ argument ∈ arguments, DataPublic argument) : checkpoint.DataInputs session key arguments :=
  (Session.start_root_receipt session accepted).data_inputs data

abbrev same_start_inputs := @RecursiveNamedPublicDataInputs.StartAt.data_inputs
abbrev actual_source_arguments := @RecursiveNamedPublicDataInputs.StartAt.data_arguments

/-- These raw metadata fields and duplicate entries are independent syntax.
Source representation additionally requires the real accepted encoding. -/
theorem raw_mapping_meaning (first second : Word) :
    Means (.mapping (.proxy (.comptime .word)) (.comptime .word)
      [(.proxy (.comptime .word), .word first), (.proxy (.comptime .word), .word second)])
      (.mapping (.proxy (.comptime .word)) (.comptime .word)
        [(.proxy (.comptime .word), .word first), (.proxy (.comptime .word), .word second)]) :=
  ⟨_, by simp [DataInput.publicValue, DataInput.publicEntries], .mapping (.prepend (.proxy _) (.word _) (.prepend (.proxy _) (.word _) .empty))⟩

theorem raw_constructor_meaning (metadata : DataConstructorInstantiation) (inner : TypeSystem.Ty) :
    Means (.constructed metadata [.proxy inner]) (.constructed metadata [.proxy inner]) :=
  ⟨_, by simp [DataInput.publicValue, DataInput.publicValues], .constructed (.cons (.proxy _) .nil)⟩

theorem raw_nested_product (metadata : DataConstructorInstantiation) (inner : TypeSystem.Ty) (value : Word) :
    Means (.product (.constructed metadata [.proxy inner]) (.mapping .word .word [(.word value, .word value)]))
      (.product (.constructed metadata [.proxy inner]) (.mapping .word .word [(.word value, .word value)])) :=
  ⟨_, by simp [DataInput.publicValue, DataInput.publicValues, DataInput.publicEntries], .product (.constructed (.cons (.proxy _) .nil)) (.mapping (.prepend (.word _) (.word _) .empty))⟩

theorem handle_boundary (handle : SourceCorePublicValues.Handle) : ¬ DataPublic (.function handle) := by
  intro related
  obtain ⟨carrier, image⟩ := related
  cases carrier <;> simp [DataInput.publicValue] at image

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (value : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "enum Box<T> { Put(T) }",
  "function box(value: Box<@Word>) returns (Box<@Word>) { return value; }",
  "function proxy(value: @Word) returns (@Word) { return value; }",
  "function alias(value: mapping(@Word => Word)) returns (mapping(@Word => Word)) { return value; }",
  "function lookup(value: mapping(Word => Word), key: Word) returns (Word) { return value[key]; }",
  "function nested(value: mapping(Word => mapping(Word => Word))) returns (mapping(Word => mapping(Word => Word))) { return value; }",
  "function fault(value: mapping(Word => Word)) returns (Word) { let prior = value; let missing: Word; return missing; }"
]

private def cells {artifact : Artifact} (session : Session artifact)
    (expected : List (TypeSystem.Ty × Option SourceCorePublicValues.Value)) : IO Unit := do
  let snapshot ← get "data input full heap" (← session.snapshot)
  let actual := snapshot.cells.map fun cell =>
    (cell.type, cell.value.map fun value => match value with
      | .data value => some value
      | _ => none)
  require (reprStr actual == reprStr (expected.map fun (type, value) => (type, value.map some)))
    s!"data input ordered heap changed: {reprStr actual}"
  require session.installedGlobalsPresent "data input run lost installed globals"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "actual public data inputs" content
    ["box", "proxy", "alias", "lookup", "nested", "fault"]
  let recipe ← get "data input recipe" (Recipe.prepare compiled)
  let artifact ← recipe.open
  let boot ← artifact.bootstrapFresh
  let initial ← match boot.resume 300000 with
    | .ready session => pure session
    | .error error => throw (IO.userError s!"data bootstrap: {reprStr error}")
    | .outOfFuel _ => throw (IO.userError "data bootstrap exhausted")
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  let box ← match compiled.sourceProgram.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "public input Box missing")
  let constructor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "public input Put missing")
  let inner := TypeSystem.Ty.proxy (.comptime .word)
  let substitution : TypeSystem.ParameterSubstitution := box.parameters.zip [inner]
  let rawType := TypeSystem.Ty.nominal box.id [inner]
  let metadata : DataConstructorInstantiation := {
    constructor := constructor.id, parameterSubstitution := substitution,
    payloadTypes := constructor.payloadTypes.map substitution.apply, resultType := rawType }
  let boxed : SourceCorePublicValues.Value := .constructed metadata [.proxy (.comptime .word)]
  let duplicate : SourceCorePublicValues.Value := .mapping (.comptime .word) (.comptime .word)
    [(word 1, word 7), (word 1, word 9), (word 2, word 11)]
  let aliases : SourceCorePublicValues.Value := .mapping (.proxy (.comptime .word)) (.comptime .word)
    [(.proxy (.comptime .word), word 13), (.proxy (.comptime .word), word 17), (.proxy .word, word 19)]
  let nested : SourceCorePublicValues.Value := .mapping (.comptime .word)
    (.mapping (.comptime .word) (.comptime .word)) [(word 3, duplicate), (word 3, .mapping .word .word [])]
  let boxType := TypeSystem.Ty.nominal box.id [.proxy .word]
  let successes : List (String × List SourceCorePublicValues.Value × SourceCorePublicValues.Value ×
      List (TypeSystem.Ty × Option SourceCorePublicValues.Value)) := [
    ("box", [boxed], boxed, [(boxType, some boxed)]),
    ("proxy", [.proxy (.comptime .word)], .proxy (.comptime .word), [(.proxy .word, some (.proxy (.comptime .word)))]),
    ("alias", [aliases], aliases, [(.mapping (.proxy .word) .word, some aliases)]),
    ("lookup", [duplicate, word 1], word 7, [(.mapping .word .word, some duplicate), (.word, some (word 1))]),
    ("lookup", [duplicate, word 19], word 0, [(.mapping .word .word, some duplicate), (.word, some (word 19))]),
    ("nested", [nested], nested, [(.mapping .word (.mapping .word .word), some nested)])]
  for fuel in [0, 1, 31, 300000] do
    for (name, arguments, expected, heap) in successes do
      let checkpoint ← get "actual data public start" (initial.start (← key name) arguments)
      let first ← checkpoint.resume fuel
      let finished ← match first with
        | .outOfFuel checkpoint => checkpoint.resume 300000
        | result => pure result
      match finished with
      | .succeeded completion =>
        require (completion.value == expected) "public data result, raw metadata or duplicate order changed"
        cells completion.session heap
      | _ => throw (IO.userError "public data success did not complete")
    let checkpoint ← get "actual data fault start" (initial.start (← key "fault") [duplicate])
    let first ← checkpoint.resume fuel
    let finished ← match first with
      | .outOfFuel checkpoint => checkpoint.resume 300000
      | result => pure result
    match finished with
    | .failed _ session =>
      cells session [(.mapping .word .word, some duplicate), (.mapping .word .word, some duplicate), (.word, none)]
    | _ => throw (IO.userError "public data fault did not complete")
  require (initial.start (← key "box") [.constructed {metadata with payloadTypes := [.word]} [word 1]]).toOption.isNone
    "public input accepted altered raw constructor metadata"
  require (initial.start (← key "alias") [.mapping .word .word [(word 1, word 2)]]).toOption.isNone
    "public input accepted wrong mapping key metadata"
  require (initial.start (← key "lookup") [duplicate, .bool false]).toOption.isNone
    "public input accepted wrong scalar kind after metadata encoding"
  IO.println "actual public data encoding / raw constructor and proxy metadata / ordered mappings and defaults / full heap / fault and resume GREEN"

end Tests.SourceCoreRecursiveNamedPublicDataInputs
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPublicRootFactory
/-! Successful public preparation retains the exact indexed entry, function,
argument slots and emitted call. These consumers use factory provenance. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicRootFactory
open Solcore Frontend SourceCoreIndexedSession

abbrev factory_issued := @Recipe.prepare_roots

theorem actual_entry_and_call {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (accepted : Recipe.prepare compiled = .ok recipe) {root : Root recipe.compiled}
    (member : root ∈ recipe.roots) :
    ∃ entry function index,
      entry ∈ recipe.compiled.indexed.entries ∧
      recipe.compiled.indexed.base.functions.zipIdx.find?
        (fun item => decide (item.1.signature.key = entry.key)) = some (function, index) ∧
      function.signature.key = root.key ∧
      root.inputs = entry.inputs.map (·.scheme.body) ∧
      root.result = entry.sourceResultType ∧
      root.body = SourceCoreCalls.call function.signature (index + root.types.length)
        (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
          ⟨type, Core.LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression Core.Word.zero := by
  obtain ⟨entry, entryMember, function, index, selected, key, rootKey, inputs,
    _, result, _, _, body, _⟩ := Recipe.prepare_roots accepted member
  exact ⟨entry, function, index, entryMember, selected, key.trans rootKey.symm, inputs, result, body⟩

private def require := SourceCoreUnifiedCorpusSupport.assertTrue

def run : IO Unit := do
  let content := String.intercalate "\n" [
    "function zero() returns (Word) { return 0; }",
    "function one(n: Word) returns (Word) { return n + 1; }",
    "function ordered(a: Word, b: Word, c: Word) returns (Word) { return a - b + c; }",
    "function truth(value: Bool) returns (Bool) { return value; }",
    "function unit() { }"
  ]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "public root factory" content
    ["zero", "one", "ordered", "truth", "unit"]
  let recipe ← SourceCoreUnifiedCorpusSupport.get "public root recipe" (Recipe.prepare compiled)
  require (recipe.roots.length == 5) "public root factory lost requested roots"
  for root in recipe.roots do
    let some entry := recipe.compiled.indexed.entries.find? (fun entry => decide (entry.key = root.key))
      | throw (IO.userError "public root has no actual indexed entry")
    let some (function, index) := recipe.compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = entry.key))
      | throw (IO.userError "public root has no actual selected function")
    let types := function.inputs.map Prod.snd
    let arguments := SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
      ⟨type, Core.LanguageResult.success (.var (types.length - 1 - index))⟩)
    let expected := SourceCoreCalls.call function.signature (index + types.length) arguments.expression Core.Word.zero
    require (decide (root.inputs = entry.inputs.map (·.scheme.body))) "public root changed full raw source input types"
    require (decide (root.result = entry.sourceResultType)) "public root changed raw source result type"
    require (decide (root.types = types)) "public root changed ordered native input types"
    require (decide (root.type = function.signature.resultType)) "public root changed selected result type"
    require (decide (root.body = expected)) "public root changed selected call, reversed input slots or shifted global index"
    require (decide (Core.infer? (types.reverse ++
      (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed).map Core.Value.type)
      root.body recipe.compiled.indexed.layouts.definitions = some (Core.LanguageResult.resultType root.type)))
      "public root lost its actual native checker equation"
  IO.println "actual public root factory GREEN"
end Tests.SourceCoreRecursiveNamedPublicRootFactory
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPublicRootArguments
/-! Actual public root preparation and typed native inputs close the pure
argument premise. Arbitrary closure payloads keep their complete captures. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicRootArguments
open Solcore Core Frontend SourceSemantics.CoreLowering
open RecursiveNamedPublicRootArguments SourceCoreIndexedSession

abbrev argument_fuel := @arguments_have_sufficient_fuel
abbrev completed_payload := @completed_arguments

theorem prepared_call_arguments {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (accepted : Recipe.prepare compiled = .ok recipe) {root : Root recipe.compiled}
    (member : root ∈ recipe.roots) {world : StoreTyping} {values : Environment} (store : Store)
    (typed : RuntimeEnvironmentHasTypes world values root.types recipe.compiled.indexed.layouts.definitions) :
    ∃ entry, entry ∈ recipe.compiled.indexed.entries ∧
      ∃ (function : SourceCoreGeneralFunctions.Function) (index : Nat),
        function.signature.key = root.key ∧
        root.body = SourceCoreCalls.call function.signature (index + root.types.length)
          (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
            ⟨type, LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression Word.zero ∧
        Evaluates (values.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) store
          (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
            ⟨type, LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression
          (.inRight .word (DataPatternValues.packValues values)) store := by
  obtain ⟨entry, entryMember, issued⟩ := Recipe.prepare_roots accepted member
  exact ⟨entry, entryMember, factory_call_arguments issued store typed⟩

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (value : Nat) : Core.Value := .word (Word.ofNatModulo value)

def run : IO Unit := do
  let captured := Core.Value.closure .word .word (.var 0)
    [.cellRef (OptionalCell.cellType .word) 0, word 109]
  let carried := Core.Value.pair captured (.cellRef (OptionalCell.cellType .word) 0)
  let store : Store := [.inRight .unit (word 107), captured, carried]
  let globals : Environment := [.cellRef (OptionalCell.cellType .word) 0, carried, word 997]
  let inputs : List Environment := [[], [word 5], [word 7, word 11, word 13],
    [.bool true, .integer (-17), .pair (word 19) .unit], [captured],
    [carried, .integer 23, captured, .cellRef (OptionalCell.cellType .word) 0]]
  for payloads in inputs do
    let types := payloads.map Core.Value.type
    let expression := (SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
      ⟨type, LanguageResult.success (.var (types.length - 1 - index))⟩)).expression
    let native := payloads.reverse ++ globals
    let expected := Core.Value.inRight .word (DataPatternValues.packValues payloads)
    for fuel in [0, 1, 7, 10000] do
      let observed := runStateful fuel (.initial expression native store)
      let completed := match observed with
        | .outOfFuel checkpoint => runStateful 10000 checkpoint
        | result => result
      match completed with
      | .done actual after =>
        require (decide (actual = expected)) "public root argument bundle changed order or closure capture"
        require (decide (after = store)) "public root argument bundle changed complete native store"
      | other => throw (IO.userError s!"public root arguments did not finish: {reprStr other}")
  IO.println "public root arguments: exact ordered reads, arbitrary captured payloads, complete store and native resume GREEN"
end Tests.SourceCoreRecursiveNamedPublicRootArguments
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPublicRootMeaning
/-! Actual root consumers close argument evaluation and environment transport.
Independent source representation, real Entry, staging and Match profiles remain
visible. Duplicate keys retain the first complete row and its original slot.
This file adds formal consumers only; existing public runtime tests are reused. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicRootMeaning
open Solcore SourceSemantics SourceSemantics.CoreLowering
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts RecursiveGlobalInitializationMeaning
open RecursiveNamedPublicRootMeaning
section Actual
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed))
  {header : Header compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root compiled} (selected : RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps in
/-- The real global reference and capture supply the emitted call's read.
Source execution supplies the body; original native completeness supplies a
budget for the complete call, including argument packing and dispatch. -/
theorem actual_has_sufficient_fuel
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial root.body
          (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) = .done value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)) := by
  exact RecursiveNamedPublicRootMeaning.has_sufficient_fuel functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected represented heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem actual_completed_reflects_program
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial root.body
          (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)) := by
  exact RecursiveNamedPublicRootMeaning.completed_reflects_program functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected represented heaps admitted heapTyped argumentsTyped completed

end Actual

abbrev actual_recipe_selection := @RecursiveNamedPublicRootMeaning.selection_of_recipe
abbrev actual_fresh_entry := @RecursiveNamedPublicRootMeaning.fresh_entry

section Boundaries

/-- Identical keys and complete rows still retain the first physical slot. -/
theorem duplicate_keeps_first (named : SourceCoreGeneralFunctions.Function) :
    [named, named].zipIdx.find? (fun item => decide (item.1.signature.key = named.signature.key)) =
      some (named, 0) := by simp

/-- A later same-key row cannot replace the actual first-find receipt. -/
theorem duplicate_later_slot (named : SourceCoreGeneralFunctions.Function) :
    [named, named].zipIdx.find? (fun item => decide (item.1.signature.key = named.signature.key)) ≠
      some (named, 1) := by simp

/-- Reversed native storage still packs the original argument order. Arbitrary
payloads, including closures, are copied without changing their captures. -/
theorem ordered_arguments (leftType rightType : Core.Ty) (left right : Core.Value)
    (globals : Environment) (store : Store) :
    Evaluates (right :: left :: globals) store
      (SourceCoreCalls.packArguments ([leftType, rightType].zipIdx.map fun (type, index) =>
        ⟨type, LanguageResult.success (.var (2 - 1 - index))⟩)).expression
      (.inRight .word (.pair left right)) store := by
  simpa only [List.length_cons, List.length_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.append_assoc, List.cons_append, DataPatternValues.packValues] using
    RecursiveNamedPublicRootArguments.arguments_evaluate [leftType, rightType] [left, right] globals store rfl

/-- Zero inputs remain empty; a Unit payload is one distinct input slot. -/
theorem empty_and_unit_arity : ([] : List Core.Value).length ≠ [Core.Value.unit].length := by decide

end Boundaries
end Tests.SourceCoreRecursiveNamedPublicRootMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPublicRootSourceSignature
/-! Formal consumers keep complete first-find provenance, raw binder order and
the independent source Header. No encoder or runtime authority is inferred. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicRootSourceSignature
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload RecursiveNamedCatalog RecursiveNamedPublicRootMeaning
open RecursiveNamedCatalogNativeContexts

abbrev actual_entry_fields := @RecursiveNamedPublicRootSourceSignature.entry_of_prepare

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root compiled}
  {header : Header compiled.indexed.ancestry values ambient.definitions program}

theorem actual_source_signature (selected : RootSelection headers root header) :
    root.inputs = header.bindings.map (fun binding => binding.1.scheme.body) ∧
    root.result = header.function.resultType :=
  RecursiveNamedPublicRootSourceSignature.inputs_and_result selected

/-- Successful preparation and a complete source inventory suffice to choose
the same Header before transporting the source signature. -/
theorem actual_recipe_signature {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {root : SourceCoreIndexedSession.Root recipe.compiled} (member : root ∈ recipe.roots)
    {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    (complete : Complete headers) :
    ∃ header, RootSelection headers root header ∧
      root.inputs = header.bindings.map (fun binding => binding.1.scheme.body) ∧
      root.result = header.function.resultType := by
  obtain ⟨header, selected⟩ := selection_of_recipe accepted member complete
  exact ⟨header, selected, RecursiveNamedPublicRootSourceSignature.inputs_and_result selected⟩

/-- Even two distinct complete rows with the same key retain the first row.
The second row's raw binders cannot replace the factory's chosen signature. -/
theorem duplicate_first_row (first second : SourceCoreGeneralFunctions.Function)
    (distinct : first ≠ second) :
    [first, second].find? (fun named => decide (named.signature.key = first.signature.key)) = some first ∧
    [first, second].find? (fun named => decide (named.signature.key = first.signature.key)) ≠ some second := by
  constructor
  · simp
  · simpa using distinct

theorem indexed_first_row {α : Type} {rows : List α} {predicate : α → Bool} {row : α} {slot : Nat}
    (selected : rows.zipIdx.find? (fun item => predicate item.1) = some (row, slot)) :
    rows.find? predicate = some row :=
  RecursiveNamedPublicRootSourceSignature.first_row selected

end Tests.SourceCoreRecursiveNamedPublicRootSourceSignature
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPublicRuntimeMeaning
/-! These consumers use the actual public checkpoint, retained full data receipt
and runtime profiles. Independent source arguments/types, heap, staging and Entry
remain explicit. Execution regressions reuse the existing public data, simple
input and Match runners; no second executable fixture is introduced. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicRuntimeMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreIndexedSession

section Meaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicStartMeaning RecursiveNamedPublicDataInputs
open RecursiveNamedCatalogInvocationBounds
variable {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (data : ∀ argument ∈ publicArguments, DataPublic argument)
  (sameChecked : values.checked = recipe.compiled.compatible.checked)
  (programTyped : ProgramWellFormed program)
  (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
    .ok header.named.specialized)
  (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem actual_start_has_fuel
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicRuntimeMeaning.has_sufficient_fuel functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem actual_completed_start
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicRuntimeMeaning.completed_reflects_program functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps admitted heapTyped argumentsTyped completed

end Meaning
/-- Source arguments come from the real data codec; body meaning is not an input. -/
abbrev actual_encoded_arguments := @RecursiveNamedPublicRuntimeMeaning.source_arguments
/-- This consumer keeps the original body EvaluationSize and its enclosing bound. -/
abbrev original_body_reflects := @RecursiveNamedCatalogFiniteCompletion.reflects_sized_with
/-- The original successful session start retains every indexed receipt. -/
abbrev actual_start_receipt := @RecursiveNamedPublicStartMeaning.actual_start

/-- Duplicate keys retain their first value and the full ordered tail. -/
theorem duplicate_order :
    DataInput.publicValue (.mapping .bool .bool
      [(.bool true, .bool false), (.bool true, .bool true)]) ≠
    DataInput.publicValue (.mapping .bool .bool
      [(.bool true, .bool true), (.bool true, .bool false)]) := by
  simp [DataInput.publicValue, DataInput.publicEntries]

/-- Raw staging wrappers on proxy types cannot be identified by native erasure. -/
theorem raw_proxy :
    DataInput.publicValue (.proxy (.comptime .word)) ≠ DataInput.publicValue (.proxy .word) := by
  simp only [DataInput.publicValue]
  intro impossible
  cases impossible

/-- Empty source argument order is distinct from a single Unit argument. -/
theorem empty_not_unit : ([] : List SourceCorePublicValues.Value) ≠ [.unit] := by decide

/-- The independent meaning relation fixes the exact source list, including raw rows. -/
theorem same_arguments {publicValues : List SourceCorePublicValues.Value} {left right : List Dynamic.Value}
    (first : RecursiveNamedPublicDataInputs.Meanings publicValues left)
    (second : RecursiveNamedPublicDataInputs.Meanings publicValues right) : left = right :=
  RecursiveNamedPublicRuntimeMeaning.meanings_functional first second

/-- Equal public inputs cannot change constructor metadata or payload order. -/
theorem same_constructor {value : SourceCorePublicValues.Value}
    {left right : DataConstructorInstantiation} {first second : List Dynamic.Value}
    (one : RecursiveNamedPublicDataInputs.Means value (.constructed left first))
    (two : RecursiveNamedPublicDataInputs.Means value (.constructed right second)) :
    left = right ∧ first = second :=
  Dynamic.Value.constructed.inj (RecursiveNamedPublicRuntimeMeaning.means_functional one two)

end Tests.SourceCoreRecursiveNamedPublicRuntimeMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPublicEvidenceMeaning
/-! Authenticated public consumers take only pointwise static inputs with an interpreted
existential receipt. They keep independent source typing/staging/heap/Entry and
reuse existing public execution regressions. The negative receipt below shows
why an arbitrary Nonempty receipt cannot determine a diagnostic obligation. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicEvidenceMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicRuntimeFactoryMeaning
open CallableAncestryPairedLookup GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogInvocationBounds
section Meaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicStartMeaning RecursiveNamedPublicDataInputs
open RecursiveNamedCatalogInvocationBounds
variable {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = 1)
  {tracked : Header recipe.compiled.indexed.ancestry values ambient.definitions program → Bool}
  (catalog : SignatureCatalogWellFormed values.checked.signatures)
  (inputs : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations 0 functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      InputsWith true (tracked header) diagnosticPolicy headers header (compilation header) (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations 0 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (data : ∀ argument ∈ publicArguments, DataPublic argument)
  (sameChecked : values.checked = recipe.compiled.compatible.checked)
  (programTyped : ProgramWellFormed program)
  (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
    .ok header.named.specialized)
  (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem actual_start_has_fuel
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicRuntimeFactoryMeaning.has_sufficient_fuel_evidence true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem actual_completed_start
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicRuntimeFactoryMeaning.completed_reflects_program_evidence true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps admitted heapTyped argumentsTyped completed

end Meaning

section Static
variable {checked : SourceCoreCompatibleCatalog.Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {administrative : Core.Context} {diagnosticPolicy : AssignmentDiagnosticPolicy} {tracked : Bool}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable
  (actual : RecursiveNamedCatalogRuntimeProfileFactory.InputsWith true tracked diagnosticPolicy headers header compilation expressionSyntax administrative)
  (result : RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith true diagnosticPolicy headers header compilation expressionSyntax administrative)
  (interpreted : result.extracted.diagnostics registry faults)
  (catalog : SignatureCatalogWellFormed values.checked.signatures)

include actual result interpreted in
theorem actual_package : InputsWith true tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults :=
  InputsWith.of_receipt actual result interpreted

include result interpreted catalog in
theorem same_receipt :
    ∃ profile : RuntimeMatchProfileForWith true diagnosticPolicy headers header compilation header.readFuel expressionSyntax administrative registry faults,
      profile.flow = result.flow ∧ HEq profile.tree result.extracted.tree :=
  ⟨result.profile catalog interpreted, rfl, HEq.rfl⟩

include result in
/-- The same Tree and compiler equalities permit a stronger, unsatisfied
obligation. Nonempty by itself cannot select an interpretable receipt. -/
theorem blocked_receipt :
    ∃ blocked : RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith true diagnosticPolicy headers header compilation expressionSyntax administrative,
      blocked.flow = result.flow ∧ HEq blocked.extracted.tree result.extracted.tree ∧
      ∀ registry faults, ¬ blocked.extracted.diagnostics registry faults := by
  let blocked : RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith true diagnosticPolicy headers header compilation expressionSyntax administrative := { result with extracted := { result.extracted with
    diagnostics := fun _ _ => False
    materialize := fun _ _ impossible => False.elim impossible } }
  exact ⟨blocked, rfl, HEq.rfl, fun _ _ impossible => impossible⟩

include actual result interpreted in
/-- This receipt is interpreted while a second receipt for the same emitted
code is not; callers need not establish diagnostics for every receipt. -/
theorem good_does_not_require_all :
    InputsWith true tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults ∧
    ¬ (∀ other : RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith true diagnosticPolicy headers header compilation expressionSyntax administrative,
      other.extracted.diagnostics registry faults) := by
  refine ⟨InputsWith.of_receipt actual result interpreted, ?_⟩
  obtain ⟨blocked, _, _, fails⟩ := blocked_receipt result
  intro all
  exact fails registry faults (all blocked)
end Static

section ActualCache
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
  (accepted : Recipe.prepare compiled = .ok recipe)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
  {header rootHeader : Header compiled.indexed.ancestry values ambient.definitions program}
  {root : Root compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root rootHeader)
  (definitions : ambient.definitions = compiled.indexed.layouts.definitions)
  (sameCache : header.compiled.closures = compiled.indexed.secondPass.closures)


variable {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {tracked : Bool}
  (actualInputs : RecursiveNamedCatalogRuntimeProfileFactory.InputsWith true tracked diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (complete : Complete headers) (globals : header.globals = compiled.indexed.base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include accepted selected definitions sameCache actualInputs complete globals entry in
/-- The existing single extractor returns a receipt before its diagnostic
obligation is interpreted. Only that result is packaged; no arbitrary choice of
a Nonempty Receipt and no universal diagnostic premise is used. -/
theorem actual_extraction :
    ∃ result : RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith true diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ faults : FunctionCalls.FaultRep, result.extracted.diagnostics registry faults →
        InputsWith true tracked diagnosticPolicy headers header compilation expressionSyntax
          (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults :=
  RecursiveNamedPublicRuntimeFactoryMeaning.extract_source_with_evidence (authenticated := true) accepted selected definitions sameCache actualInputs complete globals entry
end ActualCache

/-- Codec representation preserves the complete independent source list. -/
abbrev exact_arguments := @RecursiveNamedPublicRuntimeMeaning.meanings_functional
/-- Duplicate mapping order and raw proxy metadata remain distinct. -/
abbrev duplicate_order := Tests.SourceCoreRecursiveNamedPublicRuntimeMeaning.duplicate_order
abbrev raw_proxy := Tests.SourceCoreRecursiveNamedPublicRuntimeMeaning.raw_proxy

/-- The public entry retains the entire chosen dictionary, including order. -/
theorem entry_evidence {checked : SourceCoreCompatibleCatalog.Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
    {definitions : DataEnvironment} {program : SourceSemantics.Program}
    (header : Header prepared values definitions program) (arguments : List Dynamic.Value) :
    (RecursiveNamedProgramEntrySource.entry header arguments).evidence = header.function.evidence := rfl

/-- This finite adapter still consumes the original measured body evaluation. -/
abbrev original_body := @RecursiveNamedCatalogFiniteCompletion.reflects_sized_with_evidence
abbrev program_value := @RecursiveNamedProgramEntrySource.program_has_sufficient_native_fuel_evidence
abbrev program_success := @RecursiveNamedProgramEntrySource.native_success_reflects_program_evidence

end Tests.SourceCoreRecursiveNamedPublicEvidenceMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPublicRuntimeFactoryMeaning
/-! The public consumers take only pointwise static inputs with an interpreted
existential receipt. They keep independent source typing/staging/heap/Entry and
reuse existing public execution regressions. The negative receipt below shows
why an arbitrary Nonempty receipt cannot determine a diagnostic obligation. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicRuntimeFactoryMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicRuntimeFactoryMeaning
open CallableAncestryPairedLookup GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogInvocationBounds
section Meaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicStartMeaning RecursiveNamedPublicDataInputs
open RecursiveNamedCatalogInvocationBounds
variable {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = 1)
  {tracked : Header recipe.compiled.indexed.ancestry values ambient.definitions program → Bool}
  (catalog : SignatureCatalogWellFormed values.checked.signatures)
  (inputs : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations 0 functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      Inputs (tracked header) diagnosticPolicy headers header (compilation header) (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations 0 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (data : ∀ argument ∈ publicArguments, DataPublic argument)
  (sameChecked : values.checked = recipe.compiled.compatible.checked)
  (programTyped : ProgramWellFormed program)
  (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
    .ok header.named.specialized)
  (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem actual_start_has_fuel
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicRuntimeFactoryMeaning.has_sufficient_fuel functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem actual_completed_start
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicRuntimeFactoryMeaning.completed_reflects_program functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps admitted heapTyped argumentsTyped completed

end Meaning

section Static
variable {checked : SourceCoreCompatibleCatalog.Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {administrative : Core.Context} {diagnosticPolicy : AssignmentDiagnosticPolicy} {tracked : Bool}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable
  (actual : RecursiveNamedCatalogRuntimeProfileFactory.Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative)
  (result : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax administrative)
  (interpreted : result.extracted.diagnostics registry faults)
  (catalog : SignatureCatalogWellFormed values.checked.signatures)

include actual result interpreted in
theorem actual_package : Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults :=
  Inputs.of_receipt actual result interpreted

include result interpreted catalog in
theorem same_receipt :
    ∃ profile : RuntimeMatchProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax administrative registry faults,
      profile.flow = result.flow ∧ HEq profile.tree result.extracted.tree :=
  ⟨result.profile catalog interpreted, rfl, HEq.rfl⟩

include result in
/-- The same Tree and compiler equalities permit a stronger, unsatisfied
obligation. Nonempty by itself cannot select an interpretable receipt. -/
theorem blocked_receipt :
    ∃ blocked : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax administrative,
      blocked.flow = result.flow ∧ HEq blocked.extracted.tree result.extracted.tree ∧
      ∀ registry faults, ¬ blocked.extracted.diagnostics registry faults := by
  let blocked : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax administrative := { result with extracted := { result.extracted with
    diagnostics := fun _ _ => False
    materialize := fun _ _ impossible => False.elim impossible } }
  exact ⟨blocked, rfl, HEq.rfl, fun _ _ impossible => impossible⟩

include actual result interpreted in
/-- This receipt is interpreted while a second receipt for the same emitted
code is not; callers need not establish diagnostics for every receipt. -/
theorem good_does_not_require_all :
    Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults ∧
    ¬ (∀ other : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax administrative,
      other.extracted.diagnostics registry faults) := by
  refine ⟨Inputs.of_receipt actual result interpreted, ?_⟩
  obtain ⟨blocked, _, _, fails⟩ := blocked_receipt result
  intro all
  exact fails registry faults (all blocked)
end Static

section ActualCache
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
  (accepted : Recipe.prepare compiled = .ok recipe)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
  {header rootHeader : Header compiled.indexed.ancestry values ambient.definitions program}
  {root : Root compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root rootHeader)
  (definitions : ambient.definitions = compiled.indexed.layouts.definitions)
  (sameCache : header.compiled.closures = compiled.indexed.secondPass.closures)


variable {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {tracked : Bool}
  (actualInputs : RecursiveNamedCatalogRuntimeProfileFactory.Inputs tracked diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (complete : Complete headers) (globals : header.globals = compiled.indexed.base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include accepted selected definitions sameCache actualInputs complete globals entry in
/-- The existing single extractor returns a receipt before its diagnostic
obligation is interpreted. Only that result is packaged; no arbitrary choice of
a Nonempty Receipt and no universal diagnostic premise is used. -/
theorem actual_extraction :
    ∃ result : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ faults : FunctionCalls.FaultRep, result.extracted.diagnostics registry faults →
        Inputs tracked diagnosticPolicy headers header compilation expressionSyntax
          (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults :=
  RecursiveNamedPublicRuntimeFactoryMeaning.extract_source accepted selected definitions sameCache actualInputs complete globals entry
end ActualCache

/-- Codec representation preserves the complete independent source list. -/
abbrev exact_arguments := @RecursiveNamedPublicRuntimeMeaning.meanings_functional
/-- Duplicate mapping order and raw proxy metadata remain distinct. -/
abbrev duplicate_order := Tests.SourceCoreRecursiveNamedPublicRuntimeMeaning.duplicate_order
abbrev raw_proxy := Tests.SourceCoreRecursiveNamedPublicRuntimeMeaning.raw_proxy

end Tests.SourceCoreRecursiveNamedPublicRuntimeFactoryMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPublicSimpleInputs
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicSimpleInputs
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open GeneralHeap ReadOnly CompatiblePayload RecursiveNamedPublicSimpleInputs

theorem actual_start_inputs {artifact : Artifact} (session : Session artifact)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact}
    (accepted : session.start key arguments fuel = .ok checkpoint)
    (simple : ∀ argument ∈ arguments, SimplePublic argument) :
    checkpoint.SimpleInputs session key arguments :=
  (Session.start_root_receipt session accepted).simple_inputs simple

abbrev same_start_inputs := @RecursiveNamedPublicSimpleInputs.StartAt.simple_inputs
abbrev actual_source_arguments := @RecursiveNamedPublicSimpleInputs.StartAt.simple_arguments

/-- Expected type erasure keeps the original raw input type in the receipt. -/
theorem raw_word_view (value : Word) :
    SimpleInput (.comptime .word) (.word value) (.word value) := .word value rfl

theorem nested_order (word : Word) (flag : Bool) (integer : Int) :
    SimpleInput (.product .word (.product .bool .integer))
      (.product (.word word) (.product (.bool flag) (.integer integer)))
      (.pair (.word word) (.pair (.bool flag) (.integer integer))) :=
  .product rfl (.word word rfl) (.product rfl (.bool flag rfl) (.integer integer rfl))

theorem preserves_distinct_scalar_kind (value : Word) :
    ¬ SimpleInput .word (.bool false) (.word value) := by
  intro related
  cases related

theorem handle_boundary (handle : SourceCorePublicValues.Handle) :
    ¬ SimplePublic (.function handle) := by intro simple; cases simple

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (value : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "function mixed(a: Word, b: integer, gate: Bool) returns ((Word, integer)) { return (gate ? a : a + 1, b); }",
  "function echo(value: (Word, (Bool, integer))) returns ((Word, (Bool, integer))) { return value; }",
  "function fault(n: Word, pair: (Bool, integer)) returns (Word) { let prior = n; let missing: Word; return missing; }"
]

private def cells {artifact : Artifact} (session : Session artifact)
    (expected : List (TypeSystem.Ty × Option SourceCorePublicValues.Value)) : IO Unit := do
  let snapshot ← get "simple input full heap" (← session.snapshot)
  let actual := snapshot.cells.map fun cell =>
    (cell.type, cell.value.map fun value => match value with
      | .data value => some value
      | _ => none)
  require (reprStr actual == reprStr (expected.map fun (type, value) => (type, value.map some)))
    s!"simple input ordered heap changed: {reprStr actual}"
  require session.installedGlobalsPresent "public input run lost installed globals"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "actual public simple inputs" content ["mixed", "echo", "fault"]
  let recipe ← get "simple input recipe" (Recipe.prepare compiled)
  let artifact ← recipe.open
  let boot ← artifact.bootstrapFresh
  let initial ← match boot.resume 300000 with
    | .ready session => pure session
    | .error error => throw (IO.userError s!"simple bootstrap: {reprStr error}")
    | .outOfFuel _ => throw (IO.userError "simple bootstrap exhausted")
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  let huge : Int := -(2^130 + 71)
  let nested := SourceCorePublicValues.Value.product (word 29) (.product (.bool false) (.integer huge))
  let successes : List (String × List SourceCorePublicValues.Value × SourceCorePublicValues.Value ×
      List (TypeSystem.Ty × Option SourceCorePublicValues.Value)) := [
    ("mixed", [word 13, .integer huge, .bool true], .product (word 13) (.integer huge),
      [(.word, some (word 13)), (.integer, some (.integer huge)), (.bool, some (.bool true))]),
    ("mixed", [word 17, .integer 73, .bool false], .product (word 18) (.integer 73),
      [(.word, some (word 17)), (.integer, some (.integer 73)), (.bool, some (.bool false))]),
    ("echo", [nested], nested, [(.product .word (.product .bool .integer), some nested)])]
  for fuel in [0, 1, 31, 300000] do
    for (name, arguments, expected, heap) in successes do
      let checkpoint ← get "actual simple public start" (initial.start (← key name) arguments)
      let first ← checkpoint.resume fuel
      let finished ← match first with
        | .outOfFuel checkpoint => checkpoint.resume 300000
        | result => pure result
      match finished with
      | .succeeded completion =>
        require (completion.value == expected) "simple public result or argument order changed"
        cells completion.session heap
      | _ => throw (IO.userError "simple public success did not complete")
    let checkpoint ← get "actual simple fault start" (initial.start (← key "fault") [word 37, .product (.bool true) (.integer huge)])
    let first ← checkpoint.resume fuel
    let finished ← match first with
      | .outOfFuel checkpoint => checkpoint.resume 300000
      | result => pure result
    match finished with
    | .failed _ session =>
      cells session [(.word, some (word 37)), (.product .bool .integer, some (.product (.bool true) (.integer huge))),
        (.word, some (word 37)), (.word, none)]
    | _ => throw (IO.userError "simple public language fault did not complete")
  require (initial.start (← key "mixed") [.bool true, .integer 3, .bool false]).toOption.isNone
    "public encoder accepted Bool in the Word position"
  require (initial.start (← key "mixed") [word 3, .integer 5]).toOption.isNone
    "public encoder accepted missing final argument"
  IO.println "actual public scalar/product encoding / ordered source inputs / full heap / fault and resume GREEN"

end Tests.SourceCoreRecursiveNamedPublicSimpleInputs
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPublicSpecializationMeaning
/-! Actual public worklist and cached receipts supply the generic source body,
complete dictionary and compiled roots. Formal consumers keep independent
source typing/raw range formation and arity. Runtime audits use actual parser,
checker, public compile and recipe preparation; they do not prove all staged
or constrained catalog execution from these source-only laws. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicSpecializationMeaning
open Solcore Frontend SourceInference TypeSystem SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedPublicSpecializationMeaning

section Public
variable {program : CheckedProgram} {seeds : List SourceCompiler.Seed} {options : SourceCompiler.Options}
  {compiled : SourceCompiler.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
  (issued : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe)
  (member : row ∈ recipe.compiled.validationPlan.specializations)

include accepted issued member

theorem actual_row : Nonempty (Prepared recipe.compiled row) :=
  of_public_compile accepted issued member

theorem actual_source_frame
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures recipe.compiled.sourceProgram.signatures) row.parameterSubstitution) :
    ∃ prepared : Prepared recipe.compiled row,
      NamedCalls.SourceFrame (Program.ofChecked recipe.compiled.sourceProgram) (CallableNamedMetadata.instantiation row)
        (RecursiveNamedSpecializationBodyFacts.bodyInstance recipe.compiled.sourceProgram row) prepared.view := by
  obtain ⟨prepared⟩ := actual_row accepted issued member
  exact ⟨prepared, prepared.source_frame wellFormed range⟩

end Public

section Meaning
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)

include prepared

theorem original_generic_body :
    ∃ signature generic supplied,
      signature ∈ compiled.sourceProgram.signatures.functions ∧ generic ∈ compiled.sourceProgram.functions ∧
      SourceSpecialization.specializeFunction signature generic supplied = .ok row ∧
      row.function.typedBody = StructuralSubstitution.applyTypedSource row.parameterSubstitution generic.typedBody ∧
      row.function.solvedRequirements = generic.solvedRequirements.map
        (StructuralSubstitution.applySolvedRequirement row.parameterSubstitution) := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _, accepted⟩ := prepared.origin
  exact ⟨signature, generic, request.parameterSubstitution, signatureMember, genericMember, accepted,
    RecursiveNamedSpecializationBodyFacts.body accepted, RecursiveNamedSpecializationBodyFacts.ledger accepted⟩

include wellFormed range

theorem generic_call_forward {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : row.function.typedBody.inputs.length = arguments.length)
    (executed : FunctionCallBody.Outcome (Program.ofChecked compiled.sourceProgram) context caller prepared.view.evidence before
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩) arguments outcome after) :
    NamedCalls.BodyOutcome (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      prepared.view.evidence before arguments outcome after :=
  (prepared.call_outcome_iff wellFormed range arity).mp executed

theorem generic_call_backward {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : row.function.typedBody.inputs.length = arguments.length)
    (executed : NamedCalls.BodyOutcome (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      prepared.view.evidence before arguments outcome after) :
    FunctionCallBody.Outcome (Program.ofChecked compiled.sourceProgram) context caller prepared.view.evidence before
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩) arguments outcome after :=
  (prepared.call_outcome_iff wellFormed range arity).mpr executed

theorem retained_source_frame :
    NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) (CallableNamedCanonicalOrder.retainedInstantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view :=
  prepared.retained_frame wellFormed range

omit range in
theorem actual_stages : Staging.FunctionHasStages row.function := prepared.has_stages wellFormed

omit wellFormed range in
theorem full_dictionary {actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence
      compiled.sourceProgram.signatures row.key row.assumptions actual = .ok ()) : actual = prepared.available :=
  prepared.authenticated_dictionary authenticated

end Meaning

section Boundaries
theorem budget_candidate_not_retained {program : CheckedProgram} {request : SourceSpecializationWorklist.Request}
    {specialized : SourceSpecialization.SpecializedFunction}
    (resolved : SourceSpecializationWorklist.resolveRequest program request = .ok specialized) :
    SourceSpecializationWorklist.run program [request] 0 = .ok
      (.budgetExhausted ⟨[specialized.key], [], [], []⟩ specialized.key [request]) :=
  SourceSpecializationWorklist.run_zero_single program request specialized resolved

theorem wrong_generic_declaration_rejected {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution} {row : SourceSpecialization.SpecializedFunction}
    (different : signature.id ≠ generic.declaration) :
    SourceSpecialization.specializeFunction signature generic supplied ≠ .ok row := by
  intro accepted
  exact different (RecursiveNamedSpecializationBodyFacts.identities accepted).1

end Boundaries

private def content : String := String.intercalate "\n" [
  "trait Marker<T> {}", "impl Marker<Word> {}",
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
  "function relay<T>(value: T) returns (T) where T: Marker { return keep(value); }",
  "function recur<T>(value: T, count: Word) returns (T) { if (count == 0) { return value; } else { return recur(value, count - 1); } }",
  "function missing<T>(value: T) returns (T) { let absent: T; return absent; }",
  "function wordRoot() returns (Word) { return choose(7, true); }",
  "function boolRoot() returns (Bool) { return choose(false, 9); }",
  "function constrained(value: Word) returns (Word) where Word: Marker { return relay(value); }",
  "function recurRoot() returns (Word) { return recur(13, 3); }",
  "function faultRoot() returns (Word) { return missing(7); }"
]

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word := SourceCoreUnifiedCorpusSupport.word

private def inspect (program : CheckedProgram) (cached : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut genericRows := 0
  let mut constrainedRows := 0
  let mut reverseRows := 0
  let mut fullLedger := 0
  for index in List.range cached.validationPlan.specializations.length do
    let row ← match cached.validationPlan.specializations[index]? with
      | some row => pure row | none => throw (IO.userError "original worklist row absent")
    let signature ← match program.signatures.functions.filter (·.id == row.declaration) with
      | [signature] => pure signature | _ => throw (IO.userError "original signature not singleton")
    let generic ← match program.functions.filter (·.declaration == row.declaration) with
      | [generic] => pure generic | _ => throw (IO.userError "original generic definition not singleton")
    let request : SourceSpecializationWorklist.Request := ⟨row.declaration, row.parameterSubstitution.reverse⟩
    let actual ← get "original full worklist resolution" (SourceSpecializationWorklist.resolveRequest program request)
    require (reprStr actual == reprStr row) "actual full specialization carrier changed"
    require (reprStr row.function.typedBody == reprStr
      (StructuralSubstitution.applyTypedSource row.parameterSubstitution generic.typedBody))
      "independent generic source substitution changed"
    require (reprStr row.function.solvedRequirements == reprStr
      (generic.solvedRequirements.map (StructuralSubstitution.applySolvedRequirement row.parameterSubstitution)))
      "complete original ordered ledger changed"
    require (row.parameterSubstitution.map Prod.fst == signature.scheme.parameters)
      "canonical domain lost unused or ordered parameters"
    let retained ← match cached.indexed.base.plan.specializations[index]? with
      | some retained => pure retained | none => throw (IO.userError "original row was removed during method extension")
    require (reprStr retained == reprStr row) "method extension changed a full original carrier"
    let slot := cached.indexed.base.plan.specializations.length - 1 - index
    let named ← match cached.indexed.base.functions[slot]? with
      | some named => pure named | none => throw (IO.userError "original reverse mapM slot absent")
    require (reprStr named.specialized == reprStr row && named.signature.key == row.key)
      "cached native slot selected by key instead of complete row"
    require (named.inputs.map Prod.fst == row.function.typedBody.inputs)
      "actual named preparation changed original binder order"
    let available ← get "actual full dictionary resolver"
      (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program row.key row.assumptions)
    let _ ← get "actual full dictionary authentication"
      (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures row.key row.assumptions available)
    require ((CallableNamedMetadata.environment available).map Prod.fst == row.assumptions)
      "actual full dictionary lost an assumption or its position"
    require (reprStr row.stageAnalysis == reprStr (← get "actual stage pass" (SourceStageAnalysis.analyzeFunction row.function)))
      "stored analysis was not produced by the actual specialization pass"
    fullLedger := fullLedger + row.function.solvedRequirements.length
    if !row.parameterSubstitution.isEmpty then genericRows := genericRows + 1
    if !row.assumptions.isEmpty then
      constrainedRows := constrainedRows + 1
      require (!available.isEmpty) "constrained source view acquired an empty dictionary"
    if row.parameterSubstitution.length == 2 then
      reverseRows := reverseRows + 1
      require (row.parameterSubstitution != row.parameterSubstitution.reverse) "distinct raw domain order collapsed"
  require (genericRows ≥ 5 && constrainedRows ≥ 3 && reverseRows == 2 && fullLedger > 0)
    s!"actual generic/dictionary/order coverage changed {genericRows}/{constrainedRows}/{reverseRows}/{fullLedger}"

/-- Read the complete original machine observation, including administrative
cells and every installed closure, beside its source export. -/
private def full_native (cached : SourceCoreUnifiedCompilation.Compiled)
    (root : SourceSpecialization.SpecializationKey) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) : IO (String × String × Bool) := do
  let first ← get "actual generic native startup" (cached.run root arguments 500 fuel)
  let final ← get "actual generic native resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution
    | none => throw (IO.userError "actual generic native execution was rejected")
  let native := execution.completion.result.native.observation
  let failed ← match native with
    | .succeeded _ store =>
      require (!store.isEmpty) "actual installed closure store was empty"
      pure false
    | .failed _ store =>
      require (!store.isEmpty) "actual fault discarded the installed closure store"
      pure true
    | _ => throw (IO.userError "actual generic native run did not finish")
  pure (reprStr final.observation, reprStr native, failed)

def run : IO Unit := do
  let program ← get "public generic checked source" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] })
  let names := ["wordRoot", "boolRoot", "constrained", "recurRoot", "faultRoot"]
  let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
  let seeds := roots.map fun key => SourceCoreCompiler.Seed.declaration key.declaration
  let options : SourceCompiler.Options := {specializationBudget := 512, compilationFuel := 1000}
  let facade ← get "actual public specialization compilation" (SourceCompiler.compileChecked program seeds options)
  let source ← get "same actual Core source compiler" (SourceCoreCompiler.compileChecked program seeds options)
  let cached ← match source.artifact? with
    | some cached => pure cached | none => throw (IO.userError "nonempty generic roots lost cache")
  let recipe ← get "actual generic recipe preparation" (SourceCoreIndexedSession.Recipe.prepare cached)
  require (facade.keys == source.keys && recipe.compiled.keys == roots) "actual public root order changed"
  inspect program recipe.compiled
  require (SourceCompiler.compileChecked program seeds {options with specializationBudget := 0}).toOption.isNone
    "zero budget treated a pending candidate as completed"
  for (name, arguments) in ([
      ("wordRoot", []), ("boolRoot", []), ("constrained", [.word (word 17)]),
      ("recurRoot", []), ("faultRoot", [])] : List (String × List SourceTypedRuntime.Value)) do
    let root ← SourceCoreUnifiedCorpusSupport.key program name
    let baseline ← full_native recipe.compiled root arguments 300000
    require (baseline.2.2 == (name == "faultRoot")) "actual generic native outcome changed"
    for fuel in [0, 1, 31, 300000] do
      let actual ← full_native recipe.compiled root arguments fuel
      require (actual == baseline) "actual generic full native store/source heap/fault resume changed"
  let artifact ← recipe.open
  let boot ← artifact.bootstrapFresh
  let initial ← match boot.resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "actual generic bootstrap incomplete")
  for (name, arguments, expected) in [
      ("wordRoot", [], SourceCorePublicValues.Value.word (word 7)),
      ("boolRoot", [], .bool false),
      ("constrained", [.word (word 17)], .word (word 17)),
      ("recurRoot", [], .word (word 13))] do
    let root ← SourceCoreUnifiedCorpusSupport.key program name
    let baseline ← get "actual full generic checkpoint" (initial.start root arguments)
    let baselineResult ← baseline.resume 300000
    let baselineCompletion ← match baselineResult with
      | .succeeded completion => pure completion | _ => throw (IO.userError "actual generic baseline failed")
    let baselineSnapshot ← get "baseline full snapshot" (← baselineCompletion.session.snapshot)
    for fuel in [0, 1, 31, 300000] do
      let checkpoint ← get "actual generic startup" (initial.start root arguments)
      let first ← checkpoint.resume fuel
      let final ← match first with | .outOfFuel checkpoint => checkpoint.resume 300000 | other => pure other
      match final with
      | .succeeded completion =>
        let snapshot ← get "resumed full snapshot" (← completion.session.snapshot)
        require (completion.value == expected && completion.session.installedGlobalsPresent)
          "actual generic value or global prefix changed"
        require (reprStr snapshot.cells == reprStr baselineSnapshot.cells && snapshot.heapSize == baselineSnapshot.heapSize &&
          snapshot.nativeHeapSize == baselineSnapshot.nativeHeapSize)
          "actual generic ordered full heap or resume changed"
      | _ => throw (IO.userError "actual generic completion failed")
  let root ← SourceCoreUnifiedCorpusSupport.key program "faultRoot"
  let baseline ← get "actual generic fault startup" (initial.start root [])
  let baselineResult ← baseline.resume 300000
  let (expectedReason, expectedSession) ← match baselineResult with
    | .failed reason session => pure (reason, session) | _ => throw (IO.userError "actual generic missing fault absent")
  let expectedSnapshot ← get "fault baseline full snapshot" (← expectedSession.snapshot)
  for fuel in [0, 1, 31, 300000] do
    let checkpoint ← get "actual generic fault repeat" (initial.start root [])
    let first ← checkpoint.resume fuel
    let final ← match first with | .outOfFuel checkpoint => checkpoint.resume 300000 | other => pure other
    match final with
    | .failed reason session =>
      let snapshot ← get "fault resumed full snapshot" (← session.snapshot)
      require (reprStr reason == reprStr expectedReason && session.installedGlobalsPresent &&
        reprStr snapshot.cells == reprStr expectedSnapshot.cells &&
        snapshot.nativeHeapSize == expectedSnapshot.nativeHeapSize)
        "actual generic fault payload/full heap/resume changed"
    | _ => throw (IO.userError "actual generic fault was lost")
  IO.println "actual public worklist full carriers / generic source bodies / constrained complete dictionaries / native reverse slots / full heap and fault resume GREEN"

end Tests.SourceCoreRecursiveNamedPublicSpecializationMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedPublicStartMeaning
/-! Consumers keep the actual startup state and encoded registry. Source input
representation and Entry authority are independent; no public encoder law or
result decoder is inferred from native typing. Runtime regressions are reused. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicStartMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts
open RecursiveNamedPublicStartMeaning

abbrev actual_start := @RecursiveNamedPublicStartMeaning.actual_start
abbrev actual_selection := @StartAt.selection
abbrev original_native_state := @CheckpointInitial.native_done_iff

section Meaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem actual_has_sufficient_fuel
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicStartMeaning.has_sufficient_fuel functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started represented heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem actual_completed_reflects_program
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicStartMeaning.completed_reflects_program functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started represented heaps
    admitted heapTyped argumentsTyped completed

end Meaning

/-- Two views of the same checkpoint cannot replace any part of its initial state. -/
theorem same_initial {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {left right : Expr} {first second : Environment} {before after : Store}
    (one : CheckpointInitial checkpoint left first before)
    (two : CheckpointInitial checkpoint right second after) :
    Core.State.initial left first before = Core.State.initial right second after := by
  cases checkpoint
  change _ = Core.State.initial left first before at one
  change _ = Core.State.initial right second after at two
  exact one.symm.trans two

/-- Recipe equality preserves the full object, including roots and cached code. -/
theorem same_recipe {artifact : Artifact} {left right : Recipe}
    (one : ArtifactRecipe artifact left) (two : ArtifactRecipe artifact right) : left = right := by
  cases artifact
  exact one.symm.trans two

/-- Metadata values are the exact retained context, including every unused row. -/
theorem same_metadata {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {left right : SourceCoreCompatibleValues.Context}
    (one : CheckpointValues checkpoint left) (two : CheckpointValues checkpoint right) : left = right := by
  cases checkpoint
  exact one.symm.trans two

end Tests.SourceCoreRecursiveNamedPublicStartMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedReachedExpressions
/-! Actual reached selection closes full named argument Trees without covering
unrelated global methods. The original ordered source metadata, separate
occurrence order, empty caller assumptions, constructor raw ranges, source
typing and installed catalog authority remain explicit. The tests do not
reinterpret authenticated special calls as ordinary emissions. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreRecursiveNamedReachedExpressions
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning
open CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem sequence
    {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
    {headers : Inventory prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {readFuel : Nat} {context : SourceSemantics.Context} {ids : List ExpressionId}
    {types : List TypeSystem.Ty} {codes : List Lowered}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source context ids types)
    (accepted : ids.mapM (fun id => child fuel source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type → child fuel source scope id reasonAt = .ok code →
      Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id code) :
    DataExpressionSequence.Tree source
      (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
      scope ids types codes ∧ types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst codes
    exact ⟨.nil, rfl⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at accepted
      obtain ⟨code, first, accepted⟩ := bind_ok accepted
      obtain ⟨restCodes, rest, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have tree := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨remaining, projected⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      have sequence : DataExpressionSequence.Tree source
          (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
          scope (id :: ids) (type :: types) (code :: restCodes) := by
        cases remaining with
        | nil => exact sourceType ▸ .single found tree
        | single nextFound nextTree => exact sourceType ▸ .cons found tree (.single nextFound nextTree)
        | cons nextFound nextTree tailTree => exact sourceType ▸ .cons found tree (.cons nextFound nextTree tailTree)
      refine ⟨sequence, ?_⟩
      simp [List.mapM_cons, ← sourceType, RecursiveNamedExpressionCompilerCertificates.tree_projected tree found, projected, bind, Except.bind]


section Accepted
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : ((Program.ofChecked compilerProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (bodyCompilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (bodyCompilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {reasonAt : ExpressionId → Word} {readFuel fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {project : Projector} {callerFunction : Specialized} {child : SourceCoreEvidence.Child}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project callerFunction compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)
  {header : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)}
  (reached : Reached receipt (headers := headers) header)
  (programTyped : ProgramWellFormed (Program.ofChecked compilerProgram))
  (nativeProjections : ∀ memberHeader, memberHeader ∈ headers →
    (memberHeader.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (memberHeader.bindings.map Prod.snd))
  (ordinaryEvidence : ∀ memberHeader, memberHeader ∈ headers → memberHeader.function.evidence = [])
  (sourceSignatures : context.signatures = (Program.ofChecked compilerProgram).signatures)
  (nativeSignatures : context.signatures = values.checked.signatures)
  (typed : ExpressionHasType source context id node.type)
  (lexical : context.typeVariables = [])
  {admitted : ExpressionId → Prop}
  (admission : RecursiveNamedExpressionCompilerCertificates.Admission source admitted)
  (coverage : RecursiveNamedCallSelectionCertificates.ReachedCoverage headers compilation source admitted)
  (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) → RecursiveNamedCallSelectionCertificates.Ordered compilation.plan instantiation)
  (constructorRanges : CompatibleExpressionInstantiationLaws.ConstructorRanges source
    (fun id => admitted id ∨ CompatibleExpressionBuiltins.Syntax source id))
  {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
  {localCatalog : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
  {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {native : SourceCoreGeneralFunctions.CallableContext}
  {skipInitializer : Option ExpressionId}
  (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures localCatalog parents
    assignments diagnostics compilation (some native) none skipInitializer)
  (allowed : ∀ argument, argument ∈ arguments → admitted argument)
  (ordinary : RecursiveNamedExpressionCompilerCertificates.Ordinary source localCatalog compilation.owner admitted)
  (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok callerFunction)
  (callerClosed : callerFunction.assumptions = [])
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
  (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
  (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative
    scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : RecursiveNamedCatalog.Entry headers locations capturePrefix compilation.administrativePrefix
    scope mapping world before store canonical)

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {methods : CallableCoercionPathMeaning.Profiles (prepared := prepared) (values := values)
    (program := Program.ofChecked compilerProgram) (context := context) (evidence := evidence)}
  (methodUninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (methodMissing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {calls : List CallableCoercionSpine.Call}
  (emitted : CallableCoercionMethodEntries.Emitted compilerProgram project compilation callerFunction receipt.available
    scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : CallableCoercionPathMeaning.Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (methodEntry : CallableCoercionMethodEntries.Entry methods ambient.definitions actual mapping world before store)


include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing reached programTyped nativeProjections ordinaryEvidence sourceSignatures nativeSignatures typed lexical constructorRanges admission coverage order childEq allowed ordinary callerSelected callerClosed declarations readPolicy lowerPolicy leafPolicy
  environments heaps locals agrees actualTyped installed methodUninitialized methodMissing emitted steps chain methodEntry checkedAccepted owners ledger in
theorem accepted_preserves
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  have sourceTypes := RecursiveNamedSourceSignatureFacts.source_types programTyped sourceSignatures nativeProjections ordinaryEvidence
  have argumentsTyped := CallableCoercionRawNamedCallScalarArguments.argument_types receipt reached sourceTypes sourceUnique typed
  obtain ⟨children, projected⟩ := sequence (headers := headers) (compilation := compilation) sourceUnique argumentsTyped receipt.argumentsAccepted
    (fun argument member node code found typed accepted =>
      RecursiveNamedSelectedExpressionFactory.tree_of_contextual_at admission coverage sourceTypes order ordinary callerSelected callerClosed
        sourceUnique lexical constructorRanges sourceSignatures declarations nativeSignatures (allowed argument member) found typed
        readPolicy lowerPolicy leafPolicy (by simpa only [childEq] using accepted))
  have nativeTypes := Except.ok.inj (projected.symm.trans (sourceTypes.projections header reached.member))
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallAdmission.of_tree receipt reached sourceTypes sourceUnique sourceSignatures typed children nativeTypes
  exact CallableCoercionRawNamedCallMeaning.preserves
    (functions := functions) (extension := extension) (definitions := definitions) (registered := registered)
    (faithful := faithful) (observations := observations) (runtimeViews := runtimeViews) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (prefixMatches := prefixMatches) (profiles := profiles)
    (valid := valid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt)
    (certified := certified) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (actualTyped := actualTyped) (installed := installed) (methodUninitialized := methodUninitialized)
    (methodMissing := methodMissing) (emitted := emitted) (steps := steps) (chain := chain)
    (methodEntry := methodEntry) (checkedAccepted := checkedAccepted) (owners := owners) (sourceUnique := sourceUnique)
    (ledger := ledger) trace

include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing reached programTyped nativeProjections ordinaryEvidence sourceSignatures nativeSignatures typed lexical constructorRanges admission coverage order childEq allowed ordinary callerSelected callerClosed declarations readPolicy lowerPolicy leafPolicy
  environments heaps locals agrees actualTyped installed methodUninitialized methodMissing emitted steps chain methodEntry in
theorem accepted_reflects
    {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  have sourceTypes := RecursiveNamedSourceSignatureFacts.source_types programTyped sourceSignatures nativeProjections ordinaryEvidence
  have argumentsTyped := CallableCoercionRawNamedCallScalarArguments.argument_types receipt reached sourceTypes sourceUnique typed
  obtain ⟨children, projected⟩ := sequence (headers := headers) (compilation := compilation) sourceUnique argumentsTyped receipt.argumentsAccepted
    (fun argument member node code found typed accepted =>
      RecursiveNamedSelectedExpressionFactory.tree_of_contextual_at admission coverage sourceTypes order ordinary callerSelected callerClosed
        sourceUnique lexical constructorRanges sourceSignatures declarations nativeSignatures (allowed argument member) found typed
        readPolicy lowerPolicy leafPolicy (by simpa only [childEq] using accepted))
  have nativeTypes := Except.ok.inj (projected.symm.trans (sourceTypes.projections header reached.member))
  obtain ⟨certified⟩ := CallableCoercionRawNamedCallAdmission.of_tree receipt reached sourceTypes sourceUnique sourceSignatures typed children nativeTypes
  exact CallableCoercionRawNamedCallMeaning.reflects
    (functions := functions) (extension := extension) (definitions := definitions) (registered := registered)
    (faithful := faithful) (observations := observations) (runtimeViews := runtimeViews) (uninitialized := uninitialized)
    (missing := missing) (escaped := escaped) (prefixMatches := prefixMatches) (profiles := profiles)
    (valid := valid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt)
    (certified := certified) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (actualTyped := actualTyped) (installed := installed) (methodUninitialized := methodUninitialized)
    (methodMissing := methodMissing) (emitted := emitted) (steps := steps) (chain := chain)
    (methodEntry := methodEntry) completed
end Accepted



section Boundaries
open RecursiveNamedCallSelectionCertificates
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {definitions : DataEnvironment} {program : SourceSemantics.Program}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource}

theorem empty_domain (plan : compilation.plan = base.plan) :
    ReachedCoverage ([] : Inventory prepared values definitions program) compilation source (fun _ => False) := by
  refine ⟨plan, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ _ allowed
    exact False.elim allowed
  · simp

theorem unrelated_global_not_covered {index : Nat} {signature : SourceCoreCalls.Signature}
    {specialized : SourceSpecialization.SpecializedFunction}
    (slot : compilation.globals[index]? = some signature)
    (selected : SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized) :
    ¬ Coverage ([] : Inventory prepared values definitions program) compilation := by
  intro coverage
  obtain ⟨header, member, _⟩ := coverage.slots index signature specialized slot selected
  cases member
end Boundaries

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Word, integer> { function coerce(value: Word) returns (integer) { let seen = value; if (value == 0) { let coercionGap: integer; return coercionGap; } return wordToInteger(value); } }",
    "function choose<A, B>(unused: A, value: B) returns (B) { return value; }",
    "function tag<T>(value: T) returns (T) { let seen = value; return value; }",
    "function flag(value: Word) returns (Bool) { let seen = value; return value == 1; }",
    "function failWord(value: Word) returns (Word) { let nestedGap: Word; return nestedGap; }",
    "function last(a: Word, b: Word, c: Word) returns (Word) { return c; }",
    "function one() returns (Word) { return 1; }",
    "function good(value: Word) returns (integer) { return choose(flag(value), tag(value)); }",
    "function first(value: Word) returns (integer) { return choose(failWord(value), tag(value)); }",
    "function later(value: Word) returns (integer) { return choose(tag(value), failWord(value)); }",
    "function single(value: Word) returns (integer) { return tag(tag(value)); }",
    "function repeated(value: Word) returns (integer) { return last(tag(value), tag(value), tag(value)); }",
    "function zero() returns (integer) { return one(); }",
    "function empty(value: Word) returns (Word) { return choose(flag(value), tag(value)); }",
    "function boxed(value: Word) returns (integer) { return choose(Box(tag(value)), tag(value)); }",
    "function builtin(value: Word) returns (integer) { return choose(integerEq(wordToInteger(tag(value)), wordToInteger(1)), tag(value)); }",
    "function lazy(value: Word) returns (integer) { return choose(flag(value), value == 1 ? tag(value) : failWord(value)); }"
  ]}] }
private def require := SourceCompilerFeatureSupport.require
private def get {α ε : Type} [Repr ε] := @SourceCompilerFeatureSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"reached arguments ordered cells changed: {reprStr state.heap}"

/-- Audit real child callbacks and selected records. A method slot is kept in
the global list and deliberately is not interpreted as an ordinary Header. -/
private def inspect (entry : SourceCompilerFeatureSupport.Entry) (outerName : String)
    (arity pathCount nestedCount : Nat) : IO Unit := do
  let indexed := entry.cached.indexed
  let base := indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "reached arguments caller missing")
  let caller := named.specialized
  let source := caller.function.typedBody
  let context := declarationContext base.sourceProgram.signatures source.owner [] caller.assumptions caller.function.solvedRequirements
  require (context.residualTypeVariables && context.typeVariables.isEmpty && context.solvedRequirements == caller.function.solvedRequirements)
    "reached arguments actual caller context changed"
  let scope ← get "reached arguments scope" ((SourceCoreDataPlaces.declaredBinders source).reverse.mapM fun binder => do
    let type ← entry.cached.compatible.checked.catalog.project binder.scheme.body
    pure (binder.id, type))
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals, administrativePrefix := 1,
    solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
  let representation := (SourceCoreCallableIndexedPrograms.markedRepresentation indexed.ancestry indexed.fuel indexed.layouts).atContext named.signature.key []
  let diagnostics ← match base.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "reached arguments diagnostics missing")
  let diagnostics := match base.callableContext with
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable} | none => diagnostics
  let own ← match diagnostics.base.find? named.signature.key with
    | some own => pure own | none => throw (IO.userError "reached arguments own diagnostics missing")
  let child := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
    base.locals base.contexts own.assignments diagnostics compilation base.callableContext none none
  let policy := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
  let reasonAt := diagnostics.reasonAt named.signature.key
  let available ← get "reached arguments available" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  require caller.assumptions.isEmpty "reached arguments require the actual closed caller"
  let ordinaryPolicy := {representation.expressions with callables := policy}
  let mut outerCount := 0
  let mut reachedCount := 0
  let mut methodCount := 0
  for signature in base.globals do
    let selected ← get "reached global full record" (SourceCompilationPlan.exactSpecialization base.plan signature.key)
    if !(base.sourceProgram.signatures.functions.any (·.id == selected.key.declaration)) then
      methodCount := methodCount + 1
  for item in source.nodes do
    if let .expression node := item then
      if let .call callee arguments (.declaration instantiation) := node.form then
        let target ← get "reached target" (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
        let key ← get "reached edge" (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id target)
        let selected ← get "reached record" (SourceCompilationPlan.exactSpecialization base.plan key)
        let declared ← match base.sourceProgram.signatures.functions.find? (·.id == selected.key.declaration) with
          | some signature => pure signature | none => throw (IO.userError "reached call is not an ordinary declaration")
        let isOuter := declared.name == outerName && node.coercions.length == pathCount
        require (instantiation == CallableNamedCanonicalOrder.retainedInstantiation selected && selected.assumptions.isEmpty &&
          instantiation.parameterSubstitution.map Prod.fst == (selected.parameterSubstitution.map Prod.fst).reverse &&
          selected.function.typedBody.inputs.length == arguments.length) "reached full metadata/domain/arity changed"
        discard <| get "reached direct callee" (SourceCompilationPlan.validateDirectDeclarationCallee source node.id callee instantiation)
        let (signature, index) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
          | [row] => pure row | _ => throw (IO.userError "reached global not singleton")
        let codes ← get "reached ordered mapM" (arguments.mapM (fun argument => child 150 source scope argument reasonAt))
        let projected ← get "reached ordered native types" (selected.function.typedBody.inputs.mapM fun binder =>
          entry.cached.compatible.checked.catalog.project binder.scheme.body)
        require (codes.map (·.type) == projected && signature.parameterType == (SourceCoreCalls.packArguments codes).type)
          "reached ordered code/native vector mismatch"
        let raw : SourceCoreBasic.LoweredExpr := ⟨signature.resultType, SourceCoreCalls.call signature
          (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments codes).expression compilation.internalReason⟩
        let special ← get "reached actual special" (SourceCoreEvidence.lowerWithProjector base.sourceProgram
          representation.expressions.projectType caller compilation child 150 source scope node.id reasonAt policy)
        if isOuter && pathCount > 0 then
          require (arguments.length == arity) "reached parent arity changed"
          let expected ← get "reached actual suffix" (SourceCoreEvidence.applyCoercions base.sourceProgram
            representation.expressions.projectType compilation caller available scope node policy raw node.coercions)
          require (special == some expected) "reached actual outer emission mismatch"
          let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
            (base.globals.map SourceCoreCalls.Signature.referenceType ++ [.cell indexed.ancestry.layout.frame.type])
          require (Core.infer? nativeContext expected.expression indexed.layouts.definitions == some (LanguageResult.resultType expected.type))
            "reached actual parent native typing changed"
          outerCount := outerCount + 1
        else
          require (special == none && node.coercions.isEmpty && node.requirements.isEmpty)
            "reached ordinary child cannot use authenticated special emission"
          let (selectedIndex, selectedSignature) ← get "reached ordinary selectedSignature"
            (SourceCoreFunctions.selectedSignature ordinaryPolicy compilation source node instantiation false)
          require (selectedIndex == index && selectedSignature == signature) "reached ordinary full signature changed"
          let full ← match base.functions[index]? with
            | some full => pure full | none => throw (IO.userError "reached actual ordinary row missing")
          require (full.signature == signature && full.specialized == selected) "reached full prepared row changed"
          let code ← get "reached original contextual child" (child 151 source scope node.id reasonAt)
          require (code == raw) "reached original ordinary child/code changed"
          if isOuter then outerCount := outerCount + 1 else reachedCount := reachedCount + 1
  require (outerCount == 1 && reachedCount == nestedCount) s!"reached site count changed {outerCount}/{reachedCount}"
  require (methodCount == pathCount) s!"reached unrelated method count changed {methodCount}"

private def gap (entry : SourceCompilerFeatureSupport.Entry) (name : String) : IO Resolved.LocalId := do
  let binders := entry.cached.indexed.base.functions.flatMap fun named =>
    SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody
  match binders.filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"reached arguments gap {name} is not unique")

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← SourceCompilerFeatureSupport.get "reached arguments fault"
    (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  let (fault, session) ← match finished with
    | .failed fault session => pure (fault, session)
    | _ => throw (IO.userError "reached arguments expected fault")
  let expected ← SourceCompilerFeatureSupport.get "reached arguments fault snapshot" (← session.snapshot 2048)
  for budget in [0, 41, 137] do
    let started ← SourceCompilerFeatureSupport.get "reached arguments suspend"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048
      | outcome => pure outcome
    match resumed with
    | .failed observed session =>
      let snapshot ← SourceCompilerFeatureSupport.get "reached arguments resumed snapshot" (← session.snapshot 2048)
      require (observed == fault && reprStr snapshot.cells == reprStr expected.cells)
        "reached arguments public fault/full snapshot changed on resume"
    | _ => throw (IO.userError "reached arguments fault resume changed outcome")


private def words (n count : Nat) : List (TypeSystem.Ty × Option SourceTypedRuntime.Value) :=
  List.replicate count (.word, some (word n))

def run : IO Unit := do
  let program ← get "reached arguments checker" (checkProgram workspace 1024)
  let entries ← ["good", "first", "later", "single", "repeated", "zero", "empty", "boxed", "builtin", "lazy"].mapM
    (SourceCompilerFeatureSupport.compileNamed program)
  let [good, first, later, single, repeated, zero, empty, data, builtin, lazy] := entries
    | throw (IO.userError "reached fixture entries missing")
  inspect good "choose" 2 1 2
  inspect first "choose" 2 1 2
  inspect later "choose" 2 1 2
  inspect single "tag" 1 1 1
  inspect repeated "last" 3 1 3
  inspect zero "one" 0 1 0
  inspect empty "choose" 2 0 2
  inspect data "choose" 2 1 2
  inspect builtin "choose" 2 1 2
  inspect lazy "choose" 2 1 3
  let coercionGap ← gap good "coercionGap"
  let nestedGap ← gap first "nestedGap"
  let lazyGap ← gap lazy "nestedGap"
  let laterGap ← gap later "nestedGap"
  let named ← match data.cached.indexed.base.functions.find? (·.signature.key == data.key) with
    | some named => pure named | none => throw (IO.userError "reached data root missing")
  let ctor ← match named.specialized.function.typedBody.nodes.filterMap (fun item => match item with
    | .expression node => match node.form with | .constructor instantiation _ => some (node.type, instantiation) | _ => none
    | _ => none) with
    | [row] => pure row | _ => throw (IO.userError "reached constructor missing")
  require (ctor.2.parameterSubstitution.map Prod.snd == [.word]) "reached complete constructor raw range changed"
  let successes : List (SourceCompilerFeatureSupport.Entry × List SourceCompilerFeatureSupport.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    (good, [SourceCompilerFeatureSupport.scalar 1], .integer 1, words 1 5 ++ [(.bool, some (.bool true))] ++ words 1 3),
    (single, [SourceCompilerFeatureSupport.scalar 2], .integer 2, words 2 7),
    (repeated, [SourceCompilerFeatureSupport.scalar 3], .integer 3, words 3 12),
    (zero, [], .integer 1, words 1 2),
    (empty, [SourceCompilerFeatureSupport.scalar 2], word 2, words 2 5 ++ [(.bool, some (.bool false))] ++ words 2 1),
    (data, [SourceCompilerFeatureSupport.scalar 7], .integer 7, words 7 5 ++ [(ctor.1, some (.constructed ctor.2 [word 7]))] ++ words 7 3),
    (builtin, [SourceCompilerFeatureSupport.scalar 1], .integer 1, words 1 5 ++ [(.bool, some (.bool true))] ++ words 1 3),
    (lazy, [SourceCompilerFeatureSupport.scalar 1], .integer 1, words 1 5 ++ [(.bool, some (.bool true))] ++ words 1 3)]
  let failures : List (SourceCompilerFeatureSupport.Entry × Nat × Resolved.LocalId × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    (first, 1, nestedGap, words 1 2 ++ [(.word, none)]),
    (later, 1, laterGap, words 1 4 ++ [(.word, none)]),
    (lazy, 2, lazyGap, words 2 4 ++ [(.word, none)]),
    (good, 0, coercionGap, words 0 5 ++ [(.bool, some (.bool false))] ++ words 0 3 ++ [(.integer, none)])]
  for budget in [0, 41, 137, 500000] do
    for (entry, arguments, expected, expectedCells) in successes do
      let started ← entry.audit arguments budget
      let finished ← get "reached arguments success resume" (started.resume 500000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr expected) "reached arguments result changed"
        cells state expectedCells
      | other => throw (IO.userError s!"reached arguments success failed: {reprStr other}")
    for (entry, input, expectedGap, expectedCells) in failures do
      let started ← entry.audit [SourceCompilerFeatureSupport.scalar input] budget
      let finished ← get "reached arguments fault resume" (started.resume 500000)
      match finished.observation with
      | .fault (.uninitializedLocal actualGap) state =>
        require (actualGap == expectedGap) "reached arguments first fault changed"
        cells state expectedCells
      | other => throw (IO.userError s!"reached arguments fault changed: {reprStr other}")
  for (entry, arguments, expected, _) in successes do
    let nativeExpected : SourceCoreExecution.Value := match expected with | .word w => .word w | .integer i => .integer i | _ => .unit
    entry.checkResume arguments nativeExpected 41
  for (entry, input, _, _) in failures do faultResume entry [SourceCompilerFeatureSupport.scalar input]
  IO.println "reached expressions: actual named/builtin ordered children with uncovered method slots, full metadata, first/later/path faults, complete heaps/resume GREEN"

end Tests.SourceCoreRecursiveNamedReachedExpressions
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedResidualContexts
/-! The actual named source context retains residual variables. The new
entry consumes true-mode child certificates and derives both root scope facts
from SourceFrame and parameter installation. Cached support and assignment
native typing are internal; source admission and diagnostics stay explicit. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedResidualContexts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory
open NativeExpressionContextSupport RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

variable (cached : SourceCoreUnifiedCompilation.Compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare cached = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
  (member : nativeEntry ∈ cached.indexed.entries)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (definitions : ambient.definitions = cached.indexed.layouts.definitions)
  {headers : Inventory cached.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {header : Header cached.indexed.ancestry values ambient.definitions program}
  (sameCache : header.compiled.closures = cached.indexed.secondPass.closures)
  (complete : Complete headers) (globals : header.globals = cached.indexed.base.globals.length)
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

variable {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

include member definitions sameCache complete globals recipeAccepted entry in
/-- This consumer feeds the real prepared root's native proof into the single
compiler traversal, without requesting body/loop HasType at actual Γ. -/
theorem actual_extraction (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :=
  RecursiveNamedCachedSupport.extract_source cached recipeAccepted
    (RecursiveNamedCachedRows.rows cached) (RecursiveNamedCachedRows.exact_cache cached) (RecursiveNamedCachedRows.ordered cached)
    member definitions sameCache complete globals entry
    diagnosticPolicy registered prefixEq factory readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy
    syntaxTree sourceSignatures declarations projection accepted

/-- The selected receipt still owns the diagnostic obligations. -/
theorem actual_profile {diagnosticPolicy : AssignmentDiagnosticPolicy} {faults : FunctionCalls.FaultRep}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (interpreted : receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults) :=
  ⟨receipt.profile initialValid interpreted⟩

/-- This is a source structural fact, independent of native code or execution. -/
theorem actual_header_context :
    header.context.typeVariables = [] ∧ header.context.residualTypeVariables = true :=
  RecursiveNamedSourceContextFacts.header_fields header

theorem old_false_excluded : header.context.residualTypeVariables ≠ false :=
  RecursiveNamedSourceContextFacts.header_not_false header

section Boundary
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {policy : SourceCoreLoops.Policy} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {sourceOwner : Resolved.DeclarationId}

/-- A real empty emitted flow is extracted in the unchanged declaration
context. Its false expression admission is vacuous because it has no children. -/
theorem empty_declaration_flow
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope
      (declarationContext values.checked.signatures sourceOwner [] [] [])) :
    GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun _ _ _ _ => False) (declarationContext values.checked.signatures sourceOwner [] [] []) scope
      true [] .unit .unit (LocalLoop.fallthrough .unit) := by
  exact GenericLexicalStatements.tree_of_flow_with_residual true readPolicy binderPolicy allocationPolicy
    (expressionSyntax := fun _ => False)
    (by intro context closed residual signatures scope fuel id node lowered declarations impossible; cases impossible)
    (.nil (.inr rfl)) rfl rfl rfl declarations (fuel := 0) (reasonAt := fun _ => Word.ofNatModulo 0)
    (selfReason := Word.ofNatModulo 0) rfl rfl
end Boundary

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def flexible : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withResidualTypeVariables

/-- A true residual scope permits used metavariables; it does not prove closed
well-formedness. Expression Valid/Closed receipts remain separate work. -/
theorem residual_admissibility_boundary :
    TypeAdmissible flexible (.variable ⟨0⟩) ∧ ¬ TypeWellFormed flexible (.variable ⟨0⟩) := by
  refine ⟨⟨⟨by simp [flexible, Context.withResidualTypeVariables, Context.ofSignatures, signatures],
    by simp [flexible, Context.withResidualTypeVariables, Context.ofSignatures, signatures]⟩,
    .variable (by simp [admissibleTypeVariables, flexible, Context.withResidualTypeVariables, Context.ofSignatures, TypeSystem.Ty.freeVariables])⟩, ?_⟩
  intro typed
  have impossible := TypeWellScoped.variable_iff.mp typed.typeWellScoped
  cases impossible

private def content : String := String.intercalate "\n" [
  "function step(n: Word) returns (Word) { return n + 1; }",
  "function self(n: Word) returns (Word) { if (n == 0) { return 0; } return self(n - 1); }",
  "function loop(n: Word) returns (Word) { let total = 0; for (let i = 0; i < n; i += 1) { total += step(i); } return total; }",
  "function down(n: Word) returns (Word) { while (n != 0) { n -= 1; } return n; }",
  "function assign(m: mapping(Bool => Word)) returns (Word) { m[true] = step(6); return m[true]; }",
  "function fail() returns (Word) { let saved = 17; let gap: Word; return gap; }",
  "function zero() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  require (compiled.indexed.base.functions.length > 1) "residual actual named inventory missing"
  for (named, slot) in compiled.indexed.base.functions.zipIdx do
    let context := declarationContext compiled.sourceProgram.signatures named.specialized.key.declaration []
      named.specialized.assumptions named.specialized.function.solvedRequirements
    require context.residualTypeVariables "actual declaration scope lost residual variables"
    require context.typeVariables.isEmpty "actual declaration acquired lexical inference variables"
    require (named.specialized.function.typedBody.inputs.map (·.id) == named.inputs.map (·.1.id))
      "actual prepared input order changed"
    let stored ← match compiled.indexed.secondPass.closures[slot]? with
      | some stored => pure stored
      | none => throw (IO.userError "residual full cached row missing")
    match stored with
    | .lambda parameter result _ =>
      require (parameter == named.signature.parameterType && result == LanguageResult.resultType named.signature.resultType)
        "residual cached signature changed"
    | _ => throw (IO.userError "residual cache is not the emitted lambda")

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "residual source context public resume" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"residual old cells changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"residual full ordered cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "actual residual source context" content
    ["self", "loop", "down", "assign", "fail", "zero"]
  inspect compiled
  let mapping : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 31), (.bool true, w 91), (.bool false, w 4)]
  let updated : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 7), (.bool true, w 91), (.bool false, w 4)]
  let tests : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("self", [w 2], w 0, [(.word, some (w 2)), (.word, some (w 1)), (.word, some (w 0))]),
    ("loop", [w 2], w 3, [(.word, some (w 2)), (.word, some (w 3)), (.word, some (w 2)), (.word, some (w 0)), (.word, some (w 1))]),
    ("down", [w 2], w 0, [(.word, some (w 0))]),
    ("assign", [mapping], w 7, [(.mapping .bool .word, some updated), (.word, some (w 6))]),
    ("zero", [], .unit, [])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩, ⟨.bool, some (.bool false)⟩]}
  let baselines ← tests.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failed ← finish compiled "fail" [] 300000 initial
  for fuel in [0, 7, 43, 300000] do
    for (test, baseline) in tests.zip baselines do
      let (name, arguments, expected, expectedCells) := test
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"residual full public resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"residual result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"residual expected success {name}")
    let observed ← finish compiled "fail" [] fuel initial
    require (reprStr observed == reprStr failed) "residual first fault/resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final => cells initial final [(.word, some (w 17)), (.word, none)] "fail"
    | _ => throw (IO.userError "residual first fault lost")
  IO.println "residual contexts: actual named scopes, ordered inputs/cache signatures, loops/assignments, cells/fault/resume GREEN"


end Tests.SourceCoreRecursiveNamedResidualContexts
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedResidualExpressions
/-! Same-context instantiation closure is used by the real contextual compiler
and the unique body extractor. These tests keep full raw retained ranges;
execution checks are separate from the source/static proofs. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedResidualExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates
open CompatibleExpressionInstantiationLaws CompatibleSourceInstantiationClosure
open RecursiveNamedResidualExpressionFactory

variable (cached : SourceCoreUnifiedCompilation.Compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare cached = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
  (member : nativeEntry ∈ cached.indexed.entries)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (definitions : ambient.definitions = cached.indexed.layouts.definitions)
  {headers : Inventory cached.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {header : Header cached.indexed.ancestry values ambient.definitions program}
  (sameCache : header.compiled.closures = cached.indexed.secondPass.closures)
  (complete : Complete headers) (globals : header.globals = cached.indexed.base.globals.length)
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

variable {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}


include member definitions sameCache complete globals recipeAccepted entry in
theorem actual_extraction (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    {checkedProgram : CheckedProgram} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignmentTable : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {skipInitializer : Option ExpressionId}
    {caller : SourceSpecialization.SpecializedFunction}
    (policyExpression : header.policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      checkedProgram header.representation signatures locals parents assignmentTable diagnostics compilation
      (some native) none skipInitializer)
    (sameLedger : compilation.solvedRequirements = header.solved)
    (admission : Admission header.function.source expressionSyntax)
    (coverage : Coverage headers compilation) (sourceTypes : SourceTypes headers header.context)
    (order : ∀ id callee arguments instantiation node, expressionSyntax id →
      header.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary header.function.source locals compilation.owner expressionSyntax)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (constructorRanges : ConstructorRanges header.function.source
      (fun id => expressionSyntax id ∨ CompatibleExpressionBuiltins.Syntax header.function.source id))
    (declarationRanges : DeclarationRanges header.function.source expressionSyntax)
    (expressionRead : header.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (expressionLower : header.representation.expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead header.readFuel values)
    (expressionLeaf : header.representation.expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  exact RecursiveNamedResidualExpressionFactory.extract
    (cached := cached) (recipeAccepted := recipeAccepted)
    (rows := RecursiveNamedCachedRows.rows cached) (cachedRows := RecursiveNamedCachedRows.exact_cache cached)
    (ordered := RecursiveNamedCachedRows.ordered cached) (member := member) (definitions := definitions)
    (sameCache := sameCache) (complete := complete) (globals := globals) (entry := entry)
    (diagnosticPolicy := diagnosticPolicy)
    (catalogSignatures := catalogSignatures)
    (catalogFuel := catalogFuel)
    (catalogTypes := catalogTypes)
    (metadata := metadata)
    (limits := limits)
    (contracts := contracts)
    (registered := registered)
    (prefixEq := prefixEq)
    (tracked := tracked)
    (factory := factory)
    (readPolicy := readPolicy)
    (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy)
    (checkedProgram := checkedProgram)
    (signatures := signatures)
    (locals := locals)
    (parents := parents)
    (assignmentTable := assignmentTable)
    (diagnostics := diagnostics)
    (native := native)
    (skipInitializer := skipInitializer)
    (caller := caller)
    (policyExpression := policyExpression)
    (sameLedger := sameLedger)
    (admission := admission)
    (coverage := coverage)
    (sourceTypes := sourceTypes)
    (order := order)
    (ordinary := ordinary)
    (callerSelected := callerSelected)
    (callerClosed := callerClosed)
    (constructorRanges := constructorRanges)
    (declarationRanges := declarationRanges)
    (expressionRead := expressionRead)
    (expressionLower := expressionLower)
    (expressionLeaf := expressionLeaf)
    (assignments := assignments)
    (unaryPolicy := unaryPolicy)
    (syntaxTree := syntaxTree)
    (sourceSignatures := sourceSignatures)
    (declarations := declarations)
    (projection := projection)
    (accepted := accepted)

/-- The selected receipt still owns the diagnostic obligations. -/
theorem actual_profile {diagnosticPolicy : AssignmentDiagnosticPolicy} {faults : FunctionCalls.FaultRep}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (interpreted : receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults) :=
  ⟨receipt.profile initialValid interpreted⟩

/-- This is a source structural fact, independent of native code or execution. -/
theorem actual_header_context :
    header.context.typeVariables = [] ∧ header.context.residualTypeVariables = true :=
  RecursiveNamedSourceContextFacts.header_fields header

theorem old_false_excluded : header.context.residualTypeVariables ≠ false :=
  RecursiveNamedSourceContextFacts.header_not_false header


section Boundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def flexible : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withResidualTypeVariables

/-- Residual admission alone cannot fill the raw closure receipt. In particular,
an unused substitution row is not discarded by looking only at result types. -/
theorem unused_range_not_closed (parameter : TypeSystem.TypeParameterId) :
    ParameterSubstitution.RangeAdmissible flexible [(parameter, .variable ⟨37⟩)] ∧
    TypeSystem.ParameterSubstitution.apply [(parameter, .variable ⟨37⟩)] .word = .word ∧
    ¬ ClosedParameterRange [(parameter, .variable ⟨37⟩)] := by
  refine ⟨?_, rfl, ?_⟩
  · intro other replacement member
    cases List.mem_singleton.mp member
    exact TypeAdmissible.variableOfResidual (by
      simp [TypeParameterBindersWellFormed, flexible, Context.ofSignatures, Context.withResidualTypeVariables]) rfl ⟨37⟩
  · intro closed
    have impossible := closed parameter (.variable ⟨37⟩) (by simp)
    cases impossible

theorem same_raw_constructor {source : TypedSource} {admitted : ExpressionId → Prop}
    (ranges : ConstructorRanges source admitted) : ConstructorLaw source flexible admitted :=
  ConstructorLaw.of_ranges rfl ranges

theorem same_raw_declaration {source : TypedSource} {admitted : ExpressionId → Prop}
    (ranges : DeclarationRanges source admitted) : DeclarationLaw source flexible admitted :=
  DeclarationLaw.of_ranges rfl ranges
end Boundary

private def content : String := String.intercalate "\n" [
  "enum Pair<A, B> { Pair(A, B) }",
  "function side(x: Word) returns (Word) { return x; }",
  "function truth(x: Bool) returns (Bool) { return x; }",
  "function choose<A, B>(a: A, b: B) returns (A) { return a; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function rootWord() returns (Word) { return choose(side(7), truth(true)); }",
  "function rootBool() returns (Bool) { return choose(truth(false), side(9)); }",
  "function rootData() returns (Pair<Word, Bool>) { return Pair(side(11), truth(true)); }",
  "function nested() returns (Word) { return choose(choose(side(3), truth(true)), side(5)); }",
  "function paired() returns ((Word, Bool)) { return (choose(side(13), truth(true)), truth(false)); }",
  "function indexed(m: mapping(Bool => Word)) returns (Word) { return m[choose(truth(true), side(17))]; }",
  "function firstFault() returns (Word) { return choose(fail(), side(99)); }",
  "function laterFault() returns (Word) { return choose(side(19), fail()); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- Re-enter the actual compiler callback using the real named source, global
inventory and parameter scope. These checks do not synthesize static source
judgments or treat runtime observation as evidence for a formal Tree. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) (names : List String) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "residual expressions diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "residual expressions parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut callCount := 0
  let mut genericCount := 0
  let mut formCount := 0
  let mut constructorCount := 0
  for named in prepared.base.functions do
    let original ← match prepared.base.sourceProgram.signatures.functions.find? (·.id == named.signature.key.declaration) with
      | some signature => pure signature | none => throw (IO.userError "residual expressions source signature missing")
    if names.contains original.name then
      let own ← match diagnostics.base.find? named.signature.key with
        | some own => pure own | none => throw (IO.userError "residual expressions own diagnostics missing")
      let source := CallableIndexedNamedGeneration.source named
      let compilation := CallableIndexedNamedGeneration.context prepared named
      let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
      let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
      let reasonAt := diagnostics.reasonAt named.signature.key
      let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
        prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics compilation
        prepared.base.callableContext none none
      for item in source.nodes do
        match item with
        | .expression node =>
          match node.form with
          | .reference _ (.declaration _) => pure ()
          | _ =>
            let code ← get "actual contextual expression" (lower prepared.fuel source scope node.id reasonAt)
            let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
              prepared.base.globals.map (·.referenceType) ++ [.cell prepared.ancestry.layout.frame.type]
            require (Core.infer? nativeContext code.expression prepared.layouts.definitions == some (LanguageResult.resultType code.type))
              "actual contextual expression lost native type"
            formCount := formCount + 1
            match node.form with
            | .call _ arguments (.declaration instantiation) =>
              let key ← get "actual static instantiation target" (SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation)
              let specialized ← get "actual full static record" (SourceCompilationPlan.exactSpecialization compilation.plan key)
              require (decide (instantiation = CallableNamedCanonicalOrder.retainedInstantiation specialized))
                "residual expressions changed complete retained instantiation"
              require (decide (instantiation.parameterSubstitution.map Prod.fst = (specialized.parameterSubstitution.map Prod.fst).reverse))
                "residual expressions changed retained domain order"
              require (instantiation.parameterSubstitution.all (fun row => SourceCoreDataCatalog.closed row.2))
                "residual expressions retained open named substitution"
              let rows := compilation.globals.zipIdx.filter (fun row => decide (row.1.key = key))
              let (signature, index) ← match rows with
                | [row] => pure row | _ => throw (IO.userError "residual expressions actual full global row missing")
              require (compiled.indexed.base.functions[index]?.map (·.signature) == some signature)
                "residual expressions header slot does not contain complete signature"
              let codes ← arguments.mapM (fun id => get "ordered actual child code" (lower (prepared.fuel - 1) source scope id reasonAt))
              require (codes.length == arguments.length && arguments.length == specialized.function.typedBody.inputs.length)
                "residual expressions actual argument arity/order lost"
              require (code.expression == SourceCoreCalls.call signature
                (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments codes).expression compilation.internalReason)
                "residual expressions ordered argument emission changed"
              callCount := callCount + 1
              if specialized.parameterSubstitution.length == 2 then genericCount := genericCount + 1
            | .constructor instantiation _ =>
              constructorCount := constructorCount + 1
              require (instantiation.parameterSubstitution.length == 2 &&
                instantiation.parameterSubstitution.all (fun row => SourceCoreDataCatalog.closed row.2))
                "residual expressions lost full closed constructor range"
            | _ => pure ()
        | _ => pure ()
  require (callCount == 26 && genericCount == 8 && formCount == 46 && constructorCount == 1)
    s!"residual expressions fixture coverage changed: calls={callCount}, generic={genericCount}, nodes={formCount}, constructors={constructorCount}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "residual expressions public resume" (first.resume 300000)).observation
private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"residual expressions old heap changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"residual expressions ordered source cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let names := ["rootWord", "rootBool", "rootData", "nested", "paired", "indexed", "firstFault", "laterFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named residual expressions" content names
  inspect compiled names
  let mut pair : Option DataConstructorInstantiation := none
  for named in compiled.indexed.base.functions do
    for item in (CallableIndexedNamedGeneration.source named).nodes do
      match item with
      | .expression node => match node.form with
        | .constructor instantiation _ => pair := some instantiation
        | _ => pure ()
      | _ => pure ()
  let actualPair ← match pair with
    | some instantiation => pure instantiation
    | none => throw (IO.userError "residual expressions generic constructor missing")
  let mapping : SourceTypedRuntime.Value := .mapping .bool .word [(.bool true, w 31), (.bool true, w 91)]
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("rootWord", [], w 7, [(.word, some (w 7)), (.bool, some (.bool true)), (.word, some (w 7)), (.bool, some (.bool true))]),
    ("rootBool", [], .bool false, [(.bool, some (.bool false)), (.word, some (w 9)), (.bool, some (.bool false)), (.word, some (w 9))]),
    ("rootData", [], .constructed actualPair [w 11, .bool true], [(.word, some (w 11)), (.bool, some (.bool true))]),
    ("nested", [], w 3, [(.word, some (w 3)), (.bool, some (.bool true)), (.word, some (w 3)), (.bool, some (.bool true)),
      (.word, some (w 5)), (.word, some (w 3)), (.word, some (w 5))]),
    ("paired", [], .product (w 13) (.bool false), [(.word, some (w 13)), (.bool, some (.bool true)),
      (.word, some (w 13)), (.bool, some (.bool true)), (.bool, some (.bool false))]),
    ("indexed", [mapping], w 31, [(.mapping .bool .word, some mapping), (.bool, some (.bool true)),
      (.word, some (w 17)), (.bool, some (.bool true)), (.word, some (w 17))])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩]}
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failed ← ["firstFault", "laterFault"].mapM (fun name => finish compiled name [] 300000 initial)
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip baselines do
      let (name, arguments, expected, expectedCells) := test
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"residual expressions complete resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"residual expressions result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"residual expressions expected completion {name}")
    for (name, baseline) in ["firstFault", "laterFault"].zip failed do
      let observed ← finish compiled name [] fuel initial
      require (reprStr observed == reprStr baseline) s!"residual expressions fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal _) final =>
        let earlier := if name == "laterFault" then [(.word, some (w 19))] else []
        cells initial final (earlier ++ [(.word, some (w 5)), (.word, none)]) name
      | _ => throw (IO.userError "residual expressions lost ordered source fault")
  IO.println "recursive named residual expressions: actual contextual output, full closed raw ranges, same-header extraction, ordered heap/fault/resume GREEN"
end Tests.SourceCoreRecursiveNamedResidualExpressions
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedRetainedSubstitutionFacts
/-! Reversal retains the same structural body without equating the ordered
instantiation records. Duplicate keys expose the first-match boundary. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedRetainedSubstitutionFacts
open Solcore Frontend SourceInference TypeSystem SourceSemantics SourceSemantics.CoreLowering
open StructuralSubstitution RecursiveNamedRetainedSubstitutionFacts

theorem exact_source {substitution : TypeSystem.ParameterSubstitution} {parameters : List TypeParameterId}
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution parameters) (source : TypedSource) :
    applyTypedSource substitution.reverse source = applyTypedSource substitution source :=
  typedSource_reverse exact.domain_nodup source

theorem exact_full_ledger {substitution : TypeSystem.ParameterSubstitution} {parameters : List TypeParameterId}
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution parameters) (rows : List SolvedRequirement) :
    rows.map (applySolvedRequirement substitution.reverse) = rows.map (applySolvedRequirement substitution) :=
  ledger_reverse exact.domain_nodup rows

theorem full_valid {context : SourceSemantics.Context} {instantiation : DeclarationInstantiation}
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation) :
    SourceSemantics.DeclarationInstantiation.Valid context (CallableNamedReversal.instantiation instantiation) :=
  valid_reverse valid

theorem same_body {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation} {body : Dynamic.BodyInstance}
    (actual : Dynamic.FunctionInstantiates program instantiation body) :
    Dynamic.FunctionInstantiates program (CallableNamedReversal.instantiation instantiation) body :=
  instantiates_reverse actual

theorem retained_body {program : SourceSemantics.Program} {specialized : SourceSpecialization.SpecializedFunction}
    {body : Dynamic.BodyInstance}
    (actual : Dynamic.FunctionInstantiates program (CallableNamedMetadata.instantiation specialized) body) :
    Dynamic.FunctionInstantiates program (CallableNamedCanonicalOrder.retainedInstantiation specialized) body :=
  retained_instantiates actual

/-- A range row is retained even if its parameter does not occur in the body. -/
theorem unused_range_retained {context : SourceSemantics.Context} {substitution : TypeSystem.ParameterSubstitution}
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed context substitution)
    {parameter : TypeParameterId} {replacement : TypeSystem.Ty}
    (member : (parameter, replacement) ∈ substitution) :
    (parameter, replacement) ∈ substitution.reverse ∧ TypeWellFormed context replacement :=
  ⟨List.mem_reverse.mpr member, range parameter replacement member⟩

theorem duplicate_key_changes_raw_result (parameter : TypeParameterId) :
    TypeSystem.ParameterSubstitution.apply [(parameter, .word), (parameter, .bool)] (.parameter parameter) ≠
      TypeSystem.ParameterSubstitution.apply ([(parameter, .word), (parameter, .bool)].reverse) (.parameter parameter) := by
  simp [TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, TypeSystem.Ty.word, TypeSystem.Ty.bool]

theorem records_keep_their_order (first second : TypeParameterId) (different : first ≠ second) :
    ([(first, .word), (second, .bool)] : TypeSystem.ParameterSubstitution) ≠
      [(first, .word), (second, .bool)].reverse := by
  intro same
  have head := congrArg (fun rows : TypeSystem.ParameterSubstitution => rows.head?) same
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.head?_cons, Option.some.injEq, Prod.mk.injEq] at head
  exact different head.1

theorem raw_staging_preserved (parameter : TypeParameterId) :
    TypeSystem.ParameterSubstitution.apply [(parameter, .comptime .word)] (.parameter parameter) = .comptime .word ∧
      TypeSystem.ParameterSubstitution.apply [(parameter, .comptime .word)] (.parameter parameter) ≠ .word := by
  simp [TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, TypeSystem.Ty.word]

private def content : String := String.intercalate "\n" [
  "enum Box<T> { Box(T) }",
  "function choose<A, B>(first: A, second: B) returns (A) { let saved = first; return saved; }",
  "function pair<A, B>(first: A, second: B) returns ((A, B)) { return (first, second); }",
  "function wrap<T>(value: T) returns (Box<T>) { return Box(value); }",
  "function wordRoot() returns (Word) { return choose(9, false); }",
  "function boolRoot() returns (Bool) { return choose(true, 8); }",
  "function pairRoot() returns ((Word, Bool)) { return pair(7, true); }",
  "function boxRoot() returns (Box<Word>) { return wrap(5); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _

private def recursive_ledger (parameter : TypeParameterId) : List SolvedRequirement :=
  let goal := ProgramSignatures.builtinIntPredicate (.parameter parameter)
  let nested := ProgramSignatures.builtinIntPredicate (.proxy (.parameter parameter))
  let staged := ProgramSignatures.builtinIntPredicate (.comptime (.parameter parameter))
  [{id := ⟨77⟩, predicate := goal, evidence := .assumption goal},
   {id := ⟨79⟩, predicate := nested, evidence := .implementation
      (.byImpl nested (.builtin .intWord)
        [.byImpl staged (.builtin .intInteger) [.byImpl goal (.builtin .intWord) []]])},
   {id := ⟨77⟩, predicate := goal, evidence := .assumption goal}]

/-- Real specialization rows exercise the structural equations. Synthetic
unused rows and nested evidence exercise full raw retention separately. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut selectedCount := 0
  let mut reversedCount := 0
  let mut ledgerCount := 0
  for specialized in compiled.compatible.prepared.plan.specializations do
    let generic ← match compiled.sourceProgram.functions.find? (fun f => f.declaration == specialized.declaration) with
      | some generic => pure generic
      | none => throw (IO.userError "retained substitution original function missing")
    let signature ← match compiled.sourceProgram.signatures.functions.find? (fun s => s.id == specialized.declaration) with
      | some signature => pure signature
      | none => throw (IO.userError "retained substitution original signature missing")
    let actual ← get "retained actual specialization"
      (SourceSpecialization.specializeFunction signature generic specialized.parameterSubstitution)
    require (reprStr actual == reprStr specialized) "retained full actual specialization changed"
    let substitution := specialized.parameterSubstitution
    require (decide ((substitution.map Prod.fst).Nodup)) "retained actual substitution has duplicate keys"
    let original := applyTypedSource substitution generic.typedBody
    let reversed := applyTypedSource substitution.reverse generic.typedBody
    require (reprStr original == reprStr specialized.function.typedBody && reprStr reversed == reprStr original)
      "retained full source application changed"
    require (substitution.apply generic.inferredBodyType == specialized.function.inferredBodyType &&
        TypeSystem.ParameterSubstitution.apply substitution.reverse generic.inferredBodyType == specialized.function.inferredBodyType)
      "retained full raw result changed"
    let originalLedger := generic.solvedRequirements.map (applySolvedRequirement substitution)
    require (reprStr originalLedger == reprStr specialized.function.solvedRequirements &&
        reprStr (generic.solvedRequirements.map (applySolvedRequirement substitution.reverse)) == reprStr originalLedger)
      "retained actual full requirement ledger changed"
    let retained := CallableNamedCanonicalOrder.retainedInstantiation specialized
    require (retained.parameterSubstitution == substitution.reverse && retained.type == specialized.function.type &&
        reprStr retained.predicates == reprStr specialized.assumptions)
      "retained record order or non-substitution metadata changed"
    if substitution.length > 1 then
      require (retained.parameterSubstitution != substitution) "retained ordered records were collapsed"
      reversedCount := reversedCount + 1
    if let some (parameter, _) := substitution.head? then
      let extra : TypeParameterId := ⟨parameter.owner, 10000⟩
      require (!(substitution.map Prod.fst).contains extra) "retained synthetic unused key is not fresh"
      let extended := substitution ++ [(extra, .comptime (.proxy .bool))]
      let rows := recursive_ledger parameter
      let full := rows.map (applySolvedRequirement extended)
      require (reprStr full == reprStr (rows.map (applySolvedRequirement extended.reverse)))
        "retained recursive evidence/staging changed"
      require (full.map (·.id.index) == [77, 79, 77]) "retained duplicate requirement IDs/order changed"
      require (extended.reverse.head? == some (extra, .comptime (.proxy .bool))) "retained unused raw row was dropped"
      require (reprStr (applyTypedSource extended generic.typedBody) == reprStr original)
        "retained synthetic unused replacement affected original source"
      require (TypeSystem.ParameterSubstitution.lookup? [(parameter, .word), (parameter, .bool)] parameter !=
          TypeSystem.ParameterSubstitution.lookup? [(parameter, .bool), (parameter, .word)] parameter)
        "retained duplicate-key first-match boundary missing"
      ledgerCount := ledgerCount + 1
    selectedCount := selectedCount + 1
  require (selectedCount == 8 && reversedCount == 3 && ledgerCount == 4)
    s!"retained actual specialization coverage changed {selectedCount}/{reversedCount}/{ledgerCount}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named retained substitutions" content
    ["wordRoot", "boolRoot", "pairRoot", "boxRoot"]
  inspect compiled
  IO.println "recursive named retained substitutions: actual full source/results/ledgers, reverse record order, unused raw rows and nested evidence GREEN"

end Tests.SourceCoreRecursiveNamedRetainedSubstitutionFacts
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedSelectedExpressions
/-! Selected headers supply named validity at the real contextual compiler
and the unique body extractor. Constructor raw ranges remain explicit;
execution checks are separate from the source/static proofs. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedSelectedExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates
open CompatibleExpressionInstantiationLaws CompatibleSourceInstantiationClosure
open RecursiveNamedSelectedExpressionFactory

variable (cached : SourceCoreUnifiedCompilation.Compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare cached = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
  (member : nativeEntry ∈ cached.indexed.entries)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (definitions : ambient.definitions = cached.indexed.layouts.definitions)
  {headers : Inventory cached.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {header : Header cached.indexed.ancestry values ambient.definitions program}
  (sameCache : header.compiled.closures = cached.indexed.secondPass.closures)
  (complete : Complete headers) (globals : header.globals = cached.indexed.base.globals.length)
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

variable {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}


include member definitions sameCache complete globals recipeAccepted entry in
theorem actual_extraction (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    {checkedProgram : CheckedProgram} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignmentTable : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {skipInitializer : Option ExpressionId}
    {caller : SourceSpecialization.SpecializedFunction}
    (policyExpression : header.policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      checkedProgram header.representation signatures locals parents assignmentTable diagnostics compilation
      (some native) none skipInitializer)
    (sameLedger : compilation.solvedRequirements = header.solved)
    (admission : Admission header.function.source expressionSyntax)
    (coverage : Coverage headers compilation) (sourceTypes : SourceTypes headers header.context)
    (order : ∀ id callee arguments instantiation node, expressionSyntax id →
      header.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary header.function.source locals compilation.owner expressionSyntax)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (constructorRanges : ConstructorRanges header.function.source
      (fun id => expressionSyntax id ∨ CompatibleExpressionBuiltins.Syntax header.function.source id))
    (expressionRead : header.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (expressionLower : header.representation.expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead header.readFuel values)
    (expressionLeaf : header.representation.expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  exact RecursiveNamedSelectedExpressionFactory.extract
    (cached := cached) (recipeAccepted := recipeAccepted)
    (rows := RecursiveNamedCachedRows.rows cached) (cachedRows := RecursiveNamedCachedRows.exact_cache cached)
    (ordered := RecursiveNamedCachedRows.ordered cached) (member := member) (definitions := definitions)
    (sameCache := sameCache) (complete := complete) (globals := globals) (entry := entry)
    (diagnosticPolicy := diagnosticPolicy)
    (catalogSignatures := catalogSignatures)
    (catalogFuel := catalogFuel)
    (catalogTypes := catalogTypes)
    (metadata := metadata)
    (limits := limits)
    (contracts := contracts)
    (registered := registered)
    (prefixEq := prefixEq)
    (tracked := tracked)
    (factory := factory)
    (readPolicy := readPolicy)
    (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy)
    (checkedProgram := checkedProgram)
    (signatures := signatures)
    (locals := locals)
    (parents := parents)
    (assignmentTable := assignmentTable)
    (diagnostics := diagnostics)
    (native := native)
    (skipInitializer := skipInitializer)
    (caller := caller)
    (policyExpression := policyExpression)
    (sameLedger := sameLedger)
    (admission := admission)
    (coverage := coverage)
    (sourceTypes := sourceTypes)
    (order := order)
    (ordinary := ordinary)
    (callerSelected := callerSelected)
    (callerClosed := callerClosed)
    (constructorRanges := constructorRanges)
    (expressionRead := expressionRead)
    (expressionLower := expressionLower)
    (expressionLeaf := expressionLeaf)
    (assignments := assignments)
    (unaryPolicy := unaryPolicy)
    (syntaxTree := syntaxTree)
    (sourceSignatures := sourceSignatures)
    (declarations := declarations)
    (projection := projection)
    (accepted := accepted)

/-- The selected receipt still owns the diagnostic obligations. -/
theorem actual_profile {diagnosticPolicy : AssignmentDiagnosticPolicy} {faults : FunctionCalls.FaultRep}
    (initialValid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (interpreted : receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults) :=
  ⟨receipt.profile initialValid interpreted⟩

/-- This is a source structural fact, independent of native code or execution. -/
theorem actual_header_context :
    header.context.typeVariables = [] ∧ header.context.residualTypeVariables = true :=
  RecursiveNamedSourceContextFacts.header_fields header

theorem old_false_excluded : header.context.residualTypeVariables ≠ false :=
  RecursiveNamedSourceContextFacts.header_not_false header


section Boundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def flexible : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withResidualTypeVariables

/-- Residual admission alone cannot fill the raw closure receipt. In particular,
an unused substitution row is not discarded by looking only at result types. -/
theorem unused_range_not_closed (parameter : TypeSystem.TypeParameterId) :
    ParameterSubstitution.RangeAdmissible flexible [(parameter, .variable ⟨37⟩)] ∧
    TypeSystem.ParameterSubstitution.apply [(parameter, .variable ⟨37⟩)] .word = .word ∧
    ¬ ClosedParameterRange [(parameter, .variable ⟨37⟩)] := by
  refine ⟨?_, rfl, ?_⟩
  · intro other replacement member
    cases List.mem_singleton.mp member
    exact TypeAdmissible.variableOfResidual (by
      simp [TypeParameterBindersWellFormed, flexible, Context.ofSignatures, Context.withResidualTypeVariables]) rfl ⟨37⟩
  · intro closed
    have impossible := closed parameter (.variable ⟨37⟩) (by simp)
    cases impossible

theorem same_raw_constructor {source : TypedSource} {admitted : ExpressionId → Prop}
    (ranges : ConstructorRanges source admitted) : ConstructorLaw source flexible admitted :=
  ConstructorLaw.of_ranges rfl ranges

/-- Empty substitution ranges do not justify rigid-binder well-formedness.
The selected-site consumer obtains that fact from actual source typing. -/
theorem empty_range_no_binders (parameter : TypeSystem.TypeParameterId) :
    let context : SourceSemantics.Context := {flexible with typeParameters := [parameter, parameter]}
    ParameterSubstitution.RangeAdmissible context [] ∧ ¬ TypeParameterBindersWellFormed context := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro other replacement member
    cases member
  · intro valid
    have unique := valid.1
    simp at unique
end Boundary

/-- Program signature identity is extracted from the same real source frame. -/
theorem actual_program_signatures : header.context.signatures = program.signatures :=
  header_program_signatures header

/-- This law is provided without any declaration range or validity callback.
It is scoped to successful selection and keeps the actual reached header. -/
theorem actual_selected_law {source : TypedSource} {context : SourceSemantics.Context}
    {admitted : ExpressionId → Prop} (same : context.signatures = program.signatures) :
    SelectedDeclarationLaw headers compilation source context admitted :=
  selected_validity same

private def content : String := String.intercalate "\n" [
  "enum Pair<A, B> { Pair(A, B) }",
  "function choose<A, B>(a: A, b: B) returns (A) { return a; }",
  "function side(x: Word) returns (Word) { return x; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function unitRoot() { return choose((), 7); }",
  "function wordRoot() returns (Word) { return choose(side(7), side(7)); }",
  "function flagRoot() returns (Bool) { return choose(false, 13); }",
  "function dataRoot() returns (Pair<Word, Bool>) { return Pair(choose(17, false), true); }",
  "function lateFault() returns (Word) { return choose(side(19), fail()); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) (names : List String) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "selected expressions diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "selected expressions parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut calls := 0
  let mut generic := 0
  for named in prepared.base.functions do
    let original ← match prepared.base.sourceProgram.signatures.functions.find? (·.id == named.signature.key.declaration) with
      | some signature => pure signature | none => throw (IO.userError "selected expressions source signature missing")
    if names.contains original.name then
      let own ← match diagnostics.base.find? named.signature.key with
        | some own => pure own | none => throw (IO.userError "selected expressions own diagnostics missing")
      let source := CallableIndexedNamedGeneration.source named
      let compilation := CallableIndexedNamedGeneration.context prepared named
      let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
      let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
      let reasonAt := diagnostics.reasonAt named.signature.key
      let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
        prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics compilation
        prepared.base.callableContext none none
      let policy := {actual.expressions with callables := SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []}
      for item in source.nodes do
        match item with
        | .expression node => match node.form with
          | .call _ arguments (.declaration instantiation) =>
            let code ← get "selected expressions actual contextual output" (lower prepared.fuel source scope node.id reasonAt)
            let (slot, signature) ← get "selected expressions actual selection"
              (SourceCoreFunctions.selectedSignature policy compilation source node instantiation false)
            let reached ← match prepared.base.functions[slot]? with
              | some reached => pure reached | none => throw (IO.userError "selected expressions missing reached header")
            require (reached.signature == signature) "selected expressions full signature/slot mismatch"
            require (decide (instantiation = CallableNamedCanonicalOrder.retainedInstantiation reached.specialized))
              "selected expressions full retained source metadata mismatch"
            require (decide (instantiation.parameterSubstitution.map Prod.fst =
              (reached.specialized.parameterSubstitution.map Prod.fst).reverse))
              "selected expressions full domain order mismatch"
            let codes ← arguments.mapM (fun id => get "selected expressions ordered child" (lower (prepared.fuel - 1) source scope id reasonAt))
            require (code.expression == SourceCoreCalls.call signature
              (scope.length + compilation.administrativePrefix + slot) (SourceCoreCalls.packArguments codes).expression compilation.internalReason)
              "selected expressions actual call emission mismatch"
            calls := calls + 1
            if instantiation.parameterSubstitution.length == 2 then generic := generic + 1
          | _ => pure ()
        | _ => pure ()
  require (calls == 9 && generic == 5) s!"selected expressions coverage changed: calls={calls}, generic={generic}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
  pure (← get "selected expressions public resume" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) s!"selected expressions old heap changed {label}"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"selected expressions ordered source cells changed {label}: {reprStr final.heap}"

def run : IO Unit := do
  let names := ["unitRoot", "wordRoot", "flagRoot", "dataRoot", "lateFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named selected expressions" content names
  inspect compiled names
  let mut pair : Option DataConstructorInstantiation := none
  for named in compiled.indexed.base.functions do
    for item in (CallableIndexedNamedGeneration.source named).nodes do
      match item with
      | .expression node => match node.form with
        | .constructor instantiation _ => pair := some instantiation
        | _ => pure ()
      | _ => pure ()
  let actualPair ← match pair with
    | some instantiation => pure instantiation
    | none => throw (IO.userError "selected expressions constructor missing")
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("unitRoot", .unit, [(.unit, some .unit), (.word, some (w 7))]),
    ("wordRoot", w 7, [(.word, some (w 7)), (.word, some (w 7)), (.word, some (w 7)), (.word, some (w 7))]),
    ("flagRoot", .bool false, [(.bool, some (.bool false)), (.word, some (w 13))]),
    ("dataRoot", .constructed actualPair [w 17, .bool true], [(.word, some (w 17)), (.bool, some (.bool false))])]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 819)⟩]}
  let baselines ← successes.mapM (fun test => finish compiled test.1 300000 initial)
  let failed ← finish compiled "lateFault" 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip baselines do
      let (name, expected, expectedCells) := test
      let observed ← finish compiled name fuel initial
      require (reprStr observed == reprStr baseline) s!"selected expressions complete resume changed {name}"
      match observed with
      | .done actual final =>
        require (reprStr actual == reprStr expected) s!"selected expressions result changed {name}"
        cells initial final expectedCells name
      | _ => throw (IO.userError s!"selected expressions expected completion {name}")
    let observed ← finish compiled "lateFault" fuel initial
    require (reprStr observed == reprStr failed) "selected expressions fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
      cells initial final [(.word, some (w 19)), (.word, some (w 5)), (.word, none)] "lateFault"
    | _ => throw (IO.userError "selected expressions lost fault prefix")
  IO.println "recursive named selected expressions: actual selected header/full metadata/code, no named range callback, ordered cells/fault/resume GREEN"
end Tests.SourceCoreRecursiveNamedSelectedExpressions
end

section
-- leanmerge: from Solcore.Test.SourceCoreRecursiveNamedSourceSignatureFacts
/-! Source parameter lists and results come from independent program typing,
signature identity and actual structural body instantiation. Packed type
collisions do not authenticate source parameter rows. The runtime fixture
inspects real generic metadata and both parameter orders. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedSourceSignatureFacts
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedCatalog RecursiveNamedSourceSignatureFacts

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : Core.DataEnvironment} {program : Program}

theorem actual_source_parameters (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    (selected : header.instantiation.declaration = signature.id) :
    signature.parameterTypes.map header.instantiation.parameterSubstitution.apply =
      header.bindings.map (fun binding => binding.1.scheme.body) :=
  (header_shape header programTyped member selected).1

theorem actual_source_result (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    (selected : header.instantiation.declaration = signature.id) :
    header.instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) =
      header.function.resultType := (header_shape header programTyped member selected).2

theorem actual_source_types {ambient : Core.AmbientDefinitions values.checked.catalog.definitions}
    {headers : Inventory prepared values ambient.definitions program} {context : SourceSemantics.Context}
    (programTyped : ProgramWellFormed program) (sameSignatures : context.signatures = program.signatures)
    (projections : ∀ header, header ∈ headers →
      (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
        .ok (header.bindings.map Prod.snd))
    (evidence : ∀ header, header ∈ headers → header.function.evidence = []) :
    RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context :=
  source_types programTyped sameSignatures projections evidence

/-- Packing alone cannot recover a source parameter list. -/
theorem packed_parameter_collision :
    TypeSystem.Ty.productMany [] = TypeSystem.Ty.productMany [.unit] ∧
    ([] : List TypeSystem.Ty) ≠ [.unit] ∧
    TypeSystem.Ty.productMany [.bool, .word] =
      TypeSystem.Ty.productMany [.product .bool .word] ∧
    ([.bool, .word] : List TypeSystem.Ty) ≠ [.product .bool .word] := by
  exact ⟨rfl, by simp, rfl, by simp⟩

private def content : String := String.intercalate "\n" [
  "function first<A, B>(one: A, two: B) returns (A) { return one; }",
  "function reverse<A, B>(one: A, two: B) returns ((B, A)) { return (two, one); }",
  "function wordRoot() returns (Word) { return first(7, true); }",
  "function boolRoot() returns (Bool) { return first(false, 9); }",
  "function pairRoot() returns ((Bool, Word)) { return reverse(11, false); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "source signature facts" content
    ["wordRoot", "boolRoot", "pairRoot"]
  let mut generic := 0
  for named in compiled.indexed.base.functions do
    let signature ← match compiled.sourceProgram.signatures.functions.find? (·.id == named.specialized.declaration) with
      | some signature => pure signature
      | none => throw (IO.userError "source signature facts declaration missing")
    let substitution := named.specialized.parameterSubstitution
    let source := CallableIndexedNamedGeneration.source named
    require (decide (signature.parameterTypes.map substitution.apply = source.inputs.map (fun binder => binder.scheme.body)))
      "source signature facts changed raw parameter positions"
    require (decide (signature.parameterTypes.map substitution.apply = named.inputs.map (fun binding => binding.1.scheme.body)))
      "source signature facts changed complete binder row"
    require (decide (substitution.apply (TypeSystem.Ty.productMany signature.returnTypes) = named.specialized.function.inferredBodyType))
      "source signature facts changed raw result"
    require (decide (substitution.map Prod.fst = signature.scheme.parameters))
      "source signature facts lost declaration order"
    if signature.scheme.parameters.length == 2 then
      require (substitution.length == 2) "source signature facts lost unused/result-independent type argument"
      generic := generic + 1
  require (generic == 3) s!"source signature facts generic coverage changed: {generic}"
  IO.println "source signature facts: independent shape consumers, raw generic parameters/results and full declaration order GREEN"

end Tests.SourceCoreRecursiveNamedSourceSignatureFacts
end
