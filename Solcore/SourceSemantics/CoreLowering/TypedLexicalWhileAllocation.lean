import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileTree
import Solcore.SourceSemantics.CoreLowering.LoopAdministration

/-! The actual generated while self-cell is an administrative allocation in the
common compatible heap. Static native typing validates the installed closure;
it does not authenticate any source value or supply a source execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedLexicalWhile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalControl (LexicalResult source_view_absent source_view_initialized allocate_absent allocate_initialized sequence_rename valid_extend)

/-- Environment agreement plus deep typing determines the renaming's native
slot types. This does not identify two source types sharing a native carrier. -/
theorem environment_respects {definitions : DataEnvironment} {world : StoreTyping}
    {canonical actual : Environment} {source target : Core.Context} {ξ : Renaming}
    (canonicalTyped : RuntimeEnvironmentHasTypes world canonical source definitions)
    (actualTyped : RuntimeEnvironmentHasTypes world actual target definitions)
    (agrees : EnvironmentsAgree ξ canonical actual) : Renaming.Respects ξ source target := by
  intro index type found
  have canonicalTypes := canonicalTyped.type_tags
  have actualTypes := actualTyped.type_tags
  rw [← canonicalTypes] at found
  rw [List.getElem?_map] at found
  cases selected : canonical[index]? with
  | none => simp [selected] at found
  | some value =>
    simp only [selected, Option.map_some, Option.some.injEq] at found
    rw [← actualTypes, List.getElem?_map, agrees selected]
    exact congrArg some found

abbrev installedStore := LoopAdministration.installedStore
abbrev installedWorld := LoopAdministration.installedWorld

/-- Invert the real generated allocation/store/lambda envelope. The function
result annotation fixes the installed body and its capture context exactly. -/
theorem installed_body_typed {definitions : DataEnvironment} {context : Core.Context}
    {type : Ty} {condition body : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.whileLoop type condition body reason) (LocalLoop.resultType type) definitions) :
    HasType (.unit :: OptionalCell.referenceType (LocalLoop.functionType type) :: context)
      (LocalLoop.loopBody type condition body (LocalLoop.fallthrough type) reason) (LocalLoop.resultType type) definitions := by
  cases typed with
  | letE allocation next =>
    cases allocation with
    | newCell initializer =>
      cases next with
      | letE write invocation =>
        cases write with
        | storeCell reference value =>
          cases reference with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Ty.cell.injEq] at found
            cases found
            cases value with
            | inRight _ closure =>
              cases closure with
              | lambda _ _ typedBody => exact typedBody

/-- Install exactly the closure allocated by `LocalLoop.whileLoop`, preserving
all source cells and every pre-existing administrative location. -/
theorem install {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {environment : Environment} {context : Core.Context} {type : Ty} {condition body : Expr}
    (reason : Word)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (typed : HasType context (LocalLoop.whileLoop type condition body reason) (LocalLoop.resultType type) ambient.definitions) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping (installedWorld world type) heap
      (installedStore store type condition body (LocalLoop.fallthrough type) reason environment) ∧
    WorldExtends world (installedWorld world type) ∧ store.length ∉ mapping ∧
    (installedWorld world type)[store.length]? = some (OptionalCell.cellType (LocalLoop.functionType type)) ∧
    (installedStore store type condition body (LocalLoop.fallthrough type) reason environment).read? store.length =
      some (.inRight .unit (LocalLoop.installedClosure type condition body (LocalLoop.fallthrough type) reason store.length environment)) ∧
    AdministrativePreserved mapping store mapping (installedStore store type condition body (LocalLoop.fallthrough type) reason environment) := by
  have worlds : WorldExtends world (installedWorld world type) := ⟨_, rfl⟩
  have found : (installedWorld world type)[store.length]? = some (OptionalCell.cellType (LocalLoop.functionType type)) := by
    rw [← heaps.runtime_hasTypes.length_eq]
    simp [installedWorld, LoopAdministration.installedWorld]
  have closureTyped : RuntimeValueHasType (installedWorld world type)
      (LocalLoop.installedClosure type condition body (LocalLoop.fallthrough type) reason store.length environment)
      (LocalLoop.functionType type) ambient.definitions :=
    .closure (.cons (.cellRef found) (environmentTyped.weaken worlds)) (installed_body_typed typed)
  have absentTyped : RuntimeValueHasType world (.inLeft (LocalLoop.functionType type) .unit)
      (OptionalCell.cellType (LocalLoop.functionType type)) ambient.definitions := .inLeft .unit
  have allocated := heaps.allocate_administrative absentTyped
  have written : (store.allocate (.inLeft (LocalLoop.functionType type) .unit)).1.write? store.length
      (.inRight .unit (LocalLoop.installedClosure type condition body (LocalLoop.fallthrough type) reason store.length environment)) =
      some (installedStore store type condition body (LocalLoop.fallthrough type) reason environment) := by
    simp [Store.allocate, Store.write?, installedStore, LoopAdministration.installedStore]
  have filled := allocated.write_administrative heaps.fresh_unmapped found (.inRight closureTyped) written
  refine ⟨filled, worlds, ?_, found, ?_, AdministrativePreserved.allocate_administrative _ _ _⟩
  · intro member
    obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
    exact heaps.fresh_unmapped lookup
  · simp [installedStore, LoopAdministration.installedStore, Store.read?]

/-- A later represented computation preserves the exact recursive code and the
fact that its cell is outside the source location map. -/
theorem retain {mapping futureMapping : LocationMap} {before after : Store} {location : Location} {value : Value}
    (unmapped : location ∉ mapping) (read : before.read? location = some value)
    (frame : AdministrativePreserved mapping before futureMapping after) :
    location ∉ futureMapping ∧ after.read? location = some value := by
  obtain ⟨unmapped, same⟩ := frame location unmapped (List.getElem?_eq_some_iff.mp read).1
  exact ⟨unmapped, same.trans read⟩
end Solcore.SourceSemantics.CoreLowering.TypedLexicalWhile
