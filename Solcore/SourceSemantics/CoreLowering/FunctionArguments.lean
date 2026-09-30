import Solcore.SourceSemantics.CoreLowering.GenericMatchAllocation
import Solcore.Frontend.SourceCoreFunctions

/-! The actual parameter wrapper allocates source and Core cells in the same
order while preserving arbitrary represented argument payloads.  Administrative
cells and source/Core index differences are retained.  A continuation agreement
covers both finite evaluation directions without assuming that newly generated
closures have equal capture environments under insertion. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.FunctionArguments
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof DataPatternValues
open DataMatchCoreAllocation ReadOnly DataEquality

inductive Arguments {catalog : SourceCoreDataCatalog.Catalog} (model : GenericHeap.PayloadModel catalog)
    (mapping : LocationMap) (world : StoreTyping) :
    List (TypedBinder × Ty) → List Dynamic.Value → List Value → Prop where
  | nil : Arguments model mapping world [] [] []
  | cons {binder : TypedBinder} {payload : Ty} {source : Dynamic.Value} {value : Value}
      {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
      (head : model.Represents mapping world binder.scheme.body source value payload)
      (tail : Arguments model mapping world bindings sources values) :
      Arguments model mapping world ((binder, payload) :: bindings) (source :: sources) (value :: values)

theorem Arguments.length {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {bindings : List (TypedBinder × Ty)}
    {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values) :
    bindings.length = sources.length ∧ bindings.length = values.length := by
  induction represented with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩

theorem Arguments.extend {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Arguments model futureMapping futureWorld bindings sources values := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons (model.extend head maps worlds) ih

private theorem selects_rename {environment target : Environment} {expression : Expr} {value : Value} {ξ : Renaming}
    (selected : Selects environment expression value) (agrees : EnvironmentsAgree ξ environment target) :
    Selects target (expression.rename ξ) value := by
  induction selected with
  | var lookup => exact .var (agrees lookup)
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

private theorem agree_insert {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index foundValue found
  exact agrees found

/-- All actual allocation-prefix steps are constructed; only the arbitrary
continuation remains as the universally quantified continuation agreement. -/
theorem Arguments.prefix {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping}
    {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {κ ξ : Renaming}
    {start : Nat} {allTypes : List Ty} {allValues : List Value} {outputType : Ty} {tail : Expr}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (sourceLayout : EnvironmentsAgree κ canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (bundleSlot : logical[start]? = some (packValues allValues))
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree (liftMany bindings.length κ) finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      ContinuationAgreement actual store ((allocationCode bindings start allTypes outputType tail).rename ξ)
        finalActual finalStore (tail.rename finalEmbedding) := by
  induction bindings generalizing mapping world scope environment canonical logical actual heap store κ ξ start sources values with
  | nil =>
    cases represented
    exact ⟨environment, heap, canonical, logical, actual, store, mapping, world, ξ,
      .nil _ _, environments, heaps, .refl _, .refl _, .refl _ _, sourceLayout, actualLayout, .refl _ _ _⟩
  | cons binding bindings ih =>
    obtain ⟨binder, payload⟩ := binding
    cases represented with
    | @cons _ _ sourceValue value _ sources values head rest =>
      have selected : allValues[start]? = some value := by simpa using valuesSelected (index := 0) rfl
      have projectionPath := DataPatternValues.projectPacked_selects (Selects.var bundleSlot) bundleLength start selected
      have initializer : Evaluates actual store
          ((LanguageResult.success (SourceCoreDataExpressions.projectPacked start allTypes (.var start))).rename ξ)
          (.inRight .word value) store := .inRight ((selects_rename projectionPath actualLayout).evaluates store)
      let reference := Value.cellRef (OptionalCell.cellType payload) store.length
      obtain ⟨nextEnvironments, nextHeaps⟩ := GenericHeap.bind (id := binder.id) environments heaps (.initialized head)
        (Dynamic.Heap.Allocates.append (type := binder.scheme.body) (value := some sourceValue))
      have nextSourceLayout : EnvironmentsAgree κ.lift (reference :: canonical) (reference :: logical) := sourceLayout.lift reference
      have insertedLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) logical (value :: actual) :=
        agree_insert actualLayout value
      have nextActualLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
          (reference :: logical) (reference :: value :: actual) := insertedLayout.lift reference
      have nextSelected : ∀ {index selectedValue}, values[index]? = some selectedValue →
          allValues[(start + 1) + index]? = some selectedValue := by
        intro index selectedValue found
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valuesSelected (index := index + 1) found
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap,
        finalWorld, finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame,
        finalSourceLayout, finalActualLayout, agreement⟩ :=
        ih (rest.extend (show LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩)
            (show WorldExtends world (world ++ [OptionalCell.cellType payload]) from ⟨_, rfl⟩))
            nextEnvironments nextHeaps nextSourceLayout nextActualLayout
          (show (reference :: logical)[start + 1]? = some (packValues allValues) from bundleSlot) nextSelected
      refine ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, .cons .append allocated, finalEnv, finalHeapRep,
        (show LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        (AdministrativePreserved.allocate mapping store (.inRight .unit value)).trans frame,
        finalSourceLayout, finalActualLayout, ?_⟩
      have allocation : Evaluates (value :: actual) store (OptionalCell.allocateInitialized payload (.var 0))
          reference (store ++ [.inRight .unit value]) := OptionalCell.allocateInitialized_evaluates (.var rfl)
      simp only [LoopStatements.rename_insert_lift] at agreement
      simp only [allocationCode, List.zipIdx_cons, List.foldr_cons, LoopRenaming.letInitialized]
      apply ContinuationAgreement.trans ?_ agreement
      exact (ContinuationAgreement.bind initializer).trans (ContinuationAgreement.letE allocation)

theorem argumentProjection_eq (index : Nat) (types : List Ty) (bundle : Expr) :
    SourceCoreFunctions.argumentProjection index types.length bundle =
      SourceCoreDataExpressions.projectPacked index types bundle := by
  induction types generalizing index bundle with
  | nil => rfl
  | cons type types ih =>
    cases types with
    | nil => rfl
    | cons next rest =>
      simp only [List.length_cons, SourceCoreFunctions.argumentProjection,
        SourceCoreDataExpressions.projectPacked]
      split
      · rfl
      · exact ih (index - 1) (.second bundle)

/-- The prefix above is the production function parameter wrapper, rather
than a second implementation with a similar allocation order. -/
theorem bindParameters_eq (bindings : List (TypedBinder × Ty)) (result : Ty) (body : Expr) :
    SourceCoreFunctions.bindParameters bindings result body =
      allocationCode bindings 0 (bindings.map Prod.snd) result body := by
  unfold SourceCoreFunctions.bindParameters allocationCode
  apply congrArg (fun step => bindings.zipIdx.foldr step body)
  funext item continuation
  obtain ⟨⟨binder, type⟩, index⟩ := item
  have same := argumentProjection_eq index (bindings.map Prod.snd) (.var index)
  simpa only [List.length_map] using congrArg
    (fun projection => LocalSequence.letInitialized result type (LanguageResult.success projection) continuation) same

private theorem liftMany_insertion (count cutoff : Nat) :
    liftMany count (Renaming.insertion cutoff) = Renaming.insertion (cutoff + count) := by
  induction count generalizing cutoff with
  | zero => rfl
  | succ count ih =>
    simp only [liftMany, Renaming.lift_insertion, ih]
    congr 1
    omega

/-- A closure call enters with one packed argument bundle. Its generated
parameter prefix reaches a body under related lexical environments and the
actual temporary-slot embedding. Both finite directions use the returned
continuation agreement, without any premise about executing that body. -/
theorem parameters_prefix {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping}
    {bindings : List (TypedBinder × Ty)} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {outputType : Ty} {body : Expr}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: canonical) actual) :
    ∃ finalEnvironment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      ContinuationAgreement actual store
        ((SourceCoreFunctions.bindParameters bindings outputType (body.weakenAt bindings.length)).rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  let κ := Renaming.insertion 0
  have sourceLayout : EnvironmentsAgree κ canonical (packValues values :: canonical) := by
    intro index value found
    exact found
  have length : (bindings.map Prod.snd).length = values.length := by simpa using represented.length.2
  obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap,
    finalWorld, finalEmbedding, allocated, finalEnv, finalHeapRep, maps, worlds, frame,
    finalSourceLayout, finalActualLayout, agreement⟩ :=
    represented.prefix (tail := body.weakenAt bindings.length)
      environments heaps sourceLayout actualLayout (start := 0) rfl length
      (fun {_ _} found => by simpa using found)
  refine ⟨finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap,
    finalWorld, Renaming.comp finalEmbedding (liftMany bindings.length κ), allocated, finalEnv,
    finalHeapRep, maps, worlds, frame, ?_, ?_⟩
  · intro index value found
    exact finalActualLayout (finalSourceLayout found)
  · rw [bindParameters_eq]
    have same : (body.weakenAt bindings.length).rename finalEmbedding =
        body.rename (Renaming.comp finalEmbedding (liftMany bindings.length κ)) := by
      simp only [κ, liftMany_insertion, Nat.zero_add]
      rw [← Expr.rename_insertion, Expr.rename_comp]
    rw [same] at agreement
    exact agreement

end Solcore.SourceSemantics.CoreLowering.FunctionArguments
