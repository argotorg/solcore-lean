import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOrdinaryAllocation
import Solcore.Frontend.SourceCoreCallableIndexedAncestry

/-! An actual indexed snapshot-lambda contains a source allocation marker in
its body and captures a nominal frame outside the base source catalog. It is
represented and stored under the full definitions, retaining the supplied raw
source closure exactly. This is a formation/indexing regression; call meaning
and source ownership remain separate from the test's explicit leaf model. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCompatibleAmbientHeap
open Core Frontend SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem existsChecked : (SourceCoreCompatibleCatalog.prepare signatures 10 [] [] {} false).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [] [] {} false).toOption.get existsChecked
private def frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨0⟩⟩
private def marker : SourceCoreHeapMarkers.Layout := ⟨⟨1⟩, .unit⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frame.definition, marker.definition]
private theorem frameRegistered : frame.Registered ambient.definitions := ⟨rfl⟩
private theorem markerRegistered : marker.Registered ambient.definitions := ⟨.unit, rfl⟩
private theorem definitionsTyped : ambient.definitions.WellFormed := Core.DataEnvironment.isWellFormed_sound (by decide)
private def table : SourceCoreCallableIndexedDispatch.Table := ⟨[], [], [], []⟩
private def snapshot := SourceCoreCallableIndexedFrames.encode frame .empty
private def environment : Environment := [.cellRef frame.type 0]
private def world : StoreTyping := [frame.type]
private def store : Store := [snapshot]
private def body : Expr := .letE (SourceCoreHeapMarkers.allocate marker .unit .unit) (LanguageResult.success .unit)
private def emitted : Expr := SourceCoreCallableIndexedAncestry.snapshotLambda table frame Word.zero 0 .unit .unit body
private def closureBody : Expr := SourceCoreCallableIndexedFrames.withFrame (.var 2)
  (SourceCoreCallableIndexedDispatch.lambdaFrame table frame Word.zero (.var 1) (.loadCell (.var 2))) (body.weakenAt 1)
private def nativeClosure : Value := .closure .unit (LanguageResult.resultType .unit) closureBody (snapshot :: environment)
private def carrier : Value := .pair (.inLeft .word .unit) nativeClosure
private def nativeType : Ty := TaggedFunction.functionType .unit .unit

private theorem bodyTyped : HasType [.unit, .cell frame.type] body (LanguageResult.resultType .unit) ambient.definitions :=
  .letE (SourceCoreHeapMarkers.allocate_hasType markerRegistered .unit .unit) (.inRight .word .unit)
private theorem emittedTyped : HasType [.cell frame.type] emitted (.function .unit (LanguageResult.resultType .unit)) ambient.definitions :=
  SourceCoreCallableIndexedAncestry.snapshotLambda_hasType frameRegistered table Word.zero .unit .unit rfl bodyTyped

/-- The exact compiler helper runs in the actual administrative environment. -/
theorem emitted_evaluates : Evaluates environment store emitted nativeClosure store :=
  SourceCoreCallableIndexedAncestry.snapshotLambda_evaluates table Word.zero rfl rfl

private theorem nativeTyped {future : StoreTyping} (typed : future[0]? = some frame.type) :
    RuntimeValueHasType future carrier nativeType ambient.definitions := by
  have bodyTyping := emittedTyped
  cases bodyTyping with
  | letE loaded lambdaTyping =>
    cases loaded with
    | loadCell reference =>
      cases reference with
      | var selected =>
        have eqType := Option.some.inj selected
        cases eqType
        cases lambdaTyping with
        | lambda _ _ code =>
          exact .pair (.inLeft .unit) (.closure
            (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed future frameRegistered .empty)
              (.cons (.cellRef typed) .nil)) code)

/-- Native typing under the smaller source catalog is actually impossible:
the captured nominal snapshot has no constructor there. -/
theorem not_base_typed : ¬ RuntimeValueHasType world carrier nativeType checked.catalog.definitions := by
  intro typed
  cases typed with
  | pair _ closureTyping =>
    cases closureTyping with
    | closure captured _ =>
      cases captured with
      | cons snapshotTyping _ =>
        cases snapshotTyping with
        | constructed registered _ => cases registered

private def functions (source : Dynamic.Closure) : FunctionModel checked.catalog ambient where
  Represents := fun _ _ future sourceType value native type =>
    sourceType = .function .unit .unit ∧ value = .closure source ∧ native = carrier ∧ type = nativeType ∧
      future[0]? = some frame.type
  projection := by rintro _ _ _ _ _ _ _ ⟨rfl, _, _, rfl, _⟩; rfl
  runtime_hasType := by rintro _ _ _ _ _ _ _ ⟨_, _, rfl, rfl, typed⟩; exact nativeTyped typed
  source_function := by rintro _ _ _ _ _ _ _ ⟨_, rfl, _, _, _⟩; exact .closure source
  extend := by
    rintro _ _ _ _ _ _ _ _ _ _ ⟨sourceType, value, native, type, typed⟩ _ _ worlds
    exact ⟨sourceType, value, native, type, worlds.lookup typed⟩

private def model (source : Dynamic.Closure) := CompatibleAmbientHeap.payloadModel checked checked.staticRegistry (functions source)
private theorem represented (source : Dynamic.Closure) :
    ValueRep checked checked.staticRegistry (functions source) [] world (.function .unit .unit) (.closure source) carrier nativeType :=
  .function ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Snapshot and marker cells stay outside the source location map; a source
cell holds the emitted closure under the real suffix definitions. -/
theorem closure_heap (source : Dynamic.Closure) :
    GenericHeap.HeapRepresents (model source) [3]
      [frame.type, frame.type, marker.type, OptionalCell.cellType nativeType]
      ⟨[⟨.function .unit .unit, some (.closure source), none⟩]⟩
      [snapshot, snapshot, SourceCoreHeapMarkers.markerValue marker .unit, .inRight .unit carrier] ∧
    ReferenceRepresents [3] [frame.type, frame.type, marker.type, OptionalCell.cellType nativeType] ⟨0⟩ 3 nativeType := by
  have empty : GenericHeap.HeapRepresents (model source) [] [] ⟨[]⟩ [] := .empty
  have contextHeap := empty.allocate_administrative (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty)
  exact CallableIndexedOrdinaryAllocation.heap_allocate contextHeap
    (SourceCoreCallableIndexedFrames.encode_runtime_typed world frameRegistered .empty)
    (.constructed markerRegistered.payloadLookup .unit) (.initialized (represented source)) .append

/-- The raw source catalog remains empty; no administrative entries are
invented to justify the larger Core table. -/
example : checked.catalog.entries = [] ∧ ambient.definitions.length = 2 := ⟨rfl, rfl⟩

/-- An already related base store and its raw staged source type transport
unchanged to the full table without admitting new function leaves. -/
private def noFunctions : FunctionModel checked.catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible

example {mapping : LocationMap} {heap : Dynamic.Heap} {store : Store} {world : StoreTyping}
    (heaps : CompatibleHeap.HeapRepresents checked checked.staticRegistry noFunctions mapping world heap store) :
    CompatibleAmbientHeap.HeapRepresents checked checked.staticRegistry
      (noFunctions.extend_definitions (after := ambient) ambient.basePrefix) mapping world heap store := by
  exact CompatibleAmbientHeap.extend_definitions
    (initial := noFunctions)
    (future := noFunctions.extend_definitions (after := ambient) ambient.basePrefix)
    (fun represented => represented) ambient.basePrefix heaps

end Solcore.Test.SourceCoreCompatibleAmbientHeap
