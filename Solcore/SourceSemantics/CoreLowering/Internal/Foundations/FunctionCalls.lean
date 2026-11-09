import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericMatches
import Solcore.Frontend.SourceCore.Lowering
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CaptureCopies
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Patterns
import Solcore.Frontend.SourceCore.GeneralFunctions
import Solcore.SourceSemantics.Staging.CallGuard

/-!
# Function values and calls

Function values and arguments, capture copies, the shared call body and `FunctionCalls`, with the contracted forms of values and calls and the call stage guard.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.FunctionArguments
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CaptureCopies
/-! Captures by value: the copies a closure makes of its captured cells, at
its creation and at each call. The lowering copies a slot, and the source
semantics copies a binding, exactly when
`SourceSemantics.CaptureBinders.copiedBinder?` selects its identifier, so the
copies of a represented scope pair up slot by slot. A copied internal slot,
which has no source binding, gets a fresh Core cell and stays internal. The
copy prefix keeps the heap and lexical relations and composes with any
continuation in both evaluation directions. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CaptureCopies
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly CaptureCopyRenaming
open SourceSemantics.CaptureBinders (copiedBinder?)
open Frontend.SourceCoreSourceCells (copyRenaming copyChainPlain scopeCopyRenaming)

private theorem environment_append {definitions : DataEnvironment} {world : StoreTyping}
    {left right : Environment} {leftTypes rightTypes : Core.Context}
    (leftTyped : RuntimeEnvironmentHasTypes world left leftTypes definitions)
    (rightTyped : RuntimeEnvironmentHasTypes world right rightTypes definitions) :
    RuntimeEnvironmentHasTypes world (left ++ right) (leftTypes ++ rightTypes) definitions := by
  induction left generalizing leftTypes with
  | nil => cases leftTyped; exact rightTyped
  | cons head tail inductionHypothesis =>
      cases leftTyped with
      | cons valueTyped tailTyped => exact .cons valueTyped (inductionHypothesis tailTyped)

/-- Copying binds no identifier that the original environment leaves unbound. -/
private theorem copies_absent {source : TypedSource} {environment copies : Dynamic.Environment}
    {heap finalHeap : Dynamic.Heap} {id : Resolved.LocalId}
    (copy : Dynamic.EnvironmentCopies source environment heap copies finalHeap)
    (absent : ∀ location, ¬ Dynamic.Environment.LooksUp environment id location) :
    ∀ location, ¬ Dynamic.Environment.LooksUp copies id location := by
  intro location lookup
  obtain ⟨original, originalLookup, _⟩ := copy.looksUp lookup
  exact absent original originalLookup

/-- One copy's `let` reads the slot's cell into a fresh cell, then continues
with the copies of the remaining slots under one more binder. -/
private theorem copy_continuation {source : TypedSource} {offset index : Nat} {done : List Nat}
    {id : Resolved.LocalId} {binder : TypedBinder} {payload : Ty} {rest : SourceCoreLocalCell.Scope}
    {inner : Expr} {η finalRenaming : Renaming} {current added : Environment} {store finalStore : Store}
    {target : Core.Location} {value : Value}
    (copied : copiedBinder? source id = some binder)
    (read : current[η (index + offset + done.length)]? = some (.cellRef (OptionalCell.cellType payload) target))
    (stored : store.read? target = some value)
    (continuation : ContinuationAgreement (.cellRef (OptionalCell.cellType payload) store.length :: current)
      (store.allocate value).1
      ((copyChainPlain source (· + offset) rest (index + 1) (done ++ [index + offset]).length inner).rename
        η.lift)
      (added ++ .cellRef (OptionalCell.cellType payload) store.length :: current) finalStore
      (inner.rename finalRenaming)) :
    ContinuationAgreement current store
      ((copyChainPlain source (· + offset) ((id, payload) :: rest) index done.length inner).rename η)
      ((added ++ [.cellRef (OptionalCell.cellType payload) store.length]) ++ current) finalStore
      (inner.rename finalRenaming) := by
  have evaluated : Evaluates current store
      (.newCell (OptionalCell.cellType payload) (.loadCell (.var (η (index + offset + done.length)))))
      (.cellRef (OptionalCell.cellType payload) store.length) (store.allocate value).1 :=
    .newCell (.loadCell (.var read) stored)
  have continued : ContinuationAgreement (.cellRef (OptionalCell.cellType payload) store.length :: current)
      (store.allocate value).1
      ((copyChainPlain source (· + offset) rest (index + 1) (done.length + 1) inner).rename η.lift)
      (added ++ .cellRef (OptionalCell.cellType payload) store.length :: current) finalStore
      (inner.rename finalRenaming) := by
    simpa only [List.length_append, List.length_singleton] using continuation
  have whole := (ContinuationAgreement.letE evaluated).trans continued
  simp only [copyChainPlain, copied, Expr.rename, List.append_assoc, List.singleton_append]
  exact whole

/-- The copies of the remaining slots `rest` of a scope, the first at scope
index `index`, after copies of the positions `done`. The processed slots hold
the values `before`, and lookups through the earlier copies extend through the
remaining ones, for the values and for any typing context of the same shape.
A copied source binding gets a fresh mapped cell, and a copied internal slot a
fresh administrative one. -/
private theorem copies_chain {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {source : TypedSource} {administrativeContext : Core.Context} {offset : Nat} {inner : Expr} :
    ∀ (rest : SourceCoreLocalCell.Scope) (index : Nat) (done : List Nat) (environment : Dynamic.Environment)
      (canonical : Environment) (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap)
      (store : Store) (before current : Environment) (η : Renaming),
      DataHeap.EnvRepresents catalog mapping world administrativeContext rest environment canonical
        definitions →
      GenericHeap.HeapRepresents model mapping world heap store →
      Agrees (Renaming.comp η (copyRenaming done)) (before ++ canonical) current →
      before.length = index + offset →
      (∀ position ∈ done, position < index + offset) →
      ∃ copies finalHeap finalCanonical added finalStore finalMap finalWorld finalRenaming addedTypes,
        Dynamic.EnvironmentCopies source environment heap copies finalHeap ∧
        DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext rest copies finalCanonical
          definitions ∧
        GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧
        Agrees
          (Renaming.comp finalRenaming (copyRenaming (done ++ chainPositions source (· + offset) rest index)))
          (before ++ finalCanonical) (added ++ current) ∧
        RuntimeEnvironmentHasTypes finalWorld added addedTypes definitions ∧
        (∀ (beforeTypes currentTypes : Core.Context), beforeTypes.length = index + offset →
          Agrees (Renaming.comp η (copyRenaming done))
            (beforeTypes ++ (SourceCoreLocalCell.coreContext rest ++ administrativeContext)) currentTypes →
          Agrees
            (Renaming.comp finalRenaming (copyRenaming (done ++ chainPositions source (· + offset) rest index)))
            (beforeTypes ++ (SourceCoreLocalCell.coreContext rest ++ administrativeContext))
            (addedTypes ++ currentTypes)) ∧
        ContinuationAgreement current store
          ((copyChainPlain source (· + offset) rest index done.length inner).rename η)
          (added ++ current) finalStore (inner.rename finalRenaming)
  | [], _, done, _, canonical, mapping, world, heap, store, _, current, η, environments, heaps, agree, _, _ => by
      cases environments with
      | nil typed =>
          refine ⟨[], heap, canonical, [], store, mapping, world, η, [], .nil heap, .nil typed, heaps,
            LocationMap.Extends.refl mapping, WorldExtends.refl world, AdministrativePreserved.refl mapping store,
            by simpa [chainPositions] using agree, .nil, ?_, ?_⟩
          · intro beforeTypes currentTypes _ typesAgree
            simpa [chainPositions] using typesAgree
          · simpa [copyChainPlain] using ContinuationAgreement.refl current store (inner.rename η)
  | (id, payload) :: rest, index, done, environment, canonical, mapping, world, heap, store, before, current, η,
      environments, heaps, agree, layout, below => by
      have fresh : before.length ∉ done := fun member => by
        have := below _ member
        omega
      have nextLayout : ∀ added : Value, (before ++ [added]).length = index + 1 + offset := by
        intro added
        simp [layout]
        omega
      have copyBelow : ∀ position ∈ done ++ [index + offset], position < index + 1 + offset := by
        intro position member
        rcases List.mem_append.mp member with old | new
        · have := below _ old
          omega
        · rw [List.mem_singleton.mp new]
          omega
      have skipBelow : ∀ position ∈ done, position < index + 1 + offset := by
        intro position member
        have := below _ member
        omega
      have shape : SourceCoreLocalCell.coreContext ((id, payload) :: rest) ++ administrativeContext =
          .cell (OptionalCell.cellType payload) ::
            (SourceCoreLocalCell.coreContext rest ++ administrativeContext) := rfl
      cases environments with
      | @cons _ tailEnvironment tailCanonical _ location target _ reference tail =>
          cases copied : copiedBinder? source id with
          | none =>
              obtain ⟨copies, finalHeap, finalCanonical, added, finalStore, finalMap, finalWorld, finalRenaming,
                  addedTypes, copiedTail, related, finalHeaps, maps, worlds, frame, finalAgree, addedTyped,
                  typesStep, continuation⟩ :=
                copies_chain rest (index + 1) done tailEnvironment tailCanonical mapping world heap store
                  (before ++ [.cellRef (OptionalCell.cellType payload) target]) current η tail heaps agree.skip
                  (nextLayout _) skipBelow
              refine ⟨(id, location) :: copies, finalHeap,
                .cellRef (OptionalCell.cellType payload) target :: finalCanonical, added, finalStore, finalMap,
                finalWorld, finalRenaming, addedTypes, .shared copied copiedTail,
                .cons (reference.extend maps worlds) related, finalHeaps, maps, worlds, frame, ?_, addedTyped,
                ?_, ?_⟩
              · simpa [chainPositions, copied] using finalAgree
              · intro beforeTypes currentTypes typesLength typesAgree
                rw [shape] at typesAgree
                have step := typesStep (beforeTypes ++ [.cell (OptionalCell.cellType payload)]) currentTypes
                  (by simp [typesLength]; omega) typesAgree.skip
                simpa [chainPositions, copied, shape] using step
              · simpa [copyChainPlain, copied] using continuation
          | some binder =>
              obtain ⟨cell, value, cellPayload, sourceRead, cellTyped, stored, represents⟩ :=
                heaps.cells reference.mapped
              obtain rfl : payload = cellPayload := by
                have same := reference.typed.symm.trans cellTyped
                simp only [OptionalCell.cellType, Option.some.injEq, Ty.sum.injEq, true_and] at same
                exact same
              obtain ⟨copiedHeaps, copiedReference⟩ := heaps.allocate_copy represents
                (Dynamic.Heap.AllocatesCopy.append (heap := heap) (cell := cell))
              have read := agree.read fresh
              rw [layout] at read
              have agreeNext := agree.copy fresh (.cellRef (OptionalCell.cellType payload) store.length)
              rw [layout] at agreeNext
              obtain ⟨copies, finalHeap, finalCanonical, added, finalStore, finalMap, finalWorld, finalRenaming,
                  addedTypes, copiedTail, related, finalHeaps, maps, worlds, frame, finalAgree, addedTyped,
                  typesStep, continuation⟩ :=
                copies_chain rest (index + 1) (done ++ [index + offset]) tailEnvironment tailCanonical
                  (mapping ++ [store.length]) (world ++ [OptionalCell.cellType payload]) ⟨heap.cells ++ [cell]⟩
                  (store.allocate value).1 (before ++ [.cellRef (OptionalCell.cellType payload) store.length])
                  (.cellRef (OptionalCell.cellType payload) store.length :: current) η.lift
                  (tail.extend ⟨[store.length], rfl⟩ ⟨[_], rfl⟩) copiedHeaps agreeNext (nextLayout _) copyBelow
              refine ⟨(id, ⟨heap.cells.length⟩) :: copies, finalHeap,
                .cellRef (OptionalCell.cellType payload) store.length :: finalCanonical,
                added ++ [.cellRef (OptionalCell.cellType payload) store.length], finalStore, finalMap, finalWorld,
                finalRenaming, addedTypes ++ [.cell (OptionalCell.cellType payload)],
                .copied copied sourceRead .append copiedTail, .cons (copiedReference.extend maps worlds) related,
                finalHeaps, LocationMap.Extends.trans ⟨[store.length], rfl⟩ maps,
                WorldExtends.trans ⟨[_], rfl⟩ worlds, (AdministrativePreserved.allocate mapping store value).trans frame,
                ?_,
                environment_append addedTyped (.cons (.cellRef (worlds.lookup copiedReference.typed)) .nil), ?_,
                copy_continuation copied read stored continuation⟩
              · simpa [chainPositions, copied] using finalAgree
              · intro beforeTypes currentTypes typesLength typesAgree
                rw [shape] at typesAgree
                have typesNext := typesAgree.copy (by rw [typesLength, ← layout]; exact fresh)
                  (.cell (OptionalCell.cellType payload))
                rw [typesLength] at typesNext
                have step := typesStep (beforeTypes ++ [.cell (OptionalCell.cellType payload)])
                  (.cell (OptionalCell.cellType payload) :: currentTypes) (by simp [typesLength]; omega) typesNext
                simpa [chainPositions, copied, shape] using step
      | @internal _ _ tailCanonical _ target _ typed absent tail =>
          cases copied : copiedBinder? source id with
          | none =>
              obtain ⟨copies, finalHeap, finalCanonical, added, finalStore, finalMap, finalWorld, finalRenaming,
                  addedTypes, copiedTail, related, finalHeaps, maps, worlds, frame, finalAgree, addedTyped,
                  typesStep, continuation⟩ :=
                copies_chain rest (index + 1) done environment tailCanonical mapping world heap store
                  (before ++ [.cellRef (OptionalCell.cellType payload) target]) current η tail heaps agree.skip
                  (nextLayout _) skipBelow
              refine ⟨copies, finalHeap, .cellRef (OptionalCell.cellType payload) target :: finalCanonical, added,
                finalStore, finalMap, finalWorld, finalRenaming, addedTypes, copiedTail,
                .internal (worlds.lookup typed) (copies_absent copiedTail absent) related, finalHeaps, maps, worlds,
                frame, ?_, addedTyped, ?_, ?_⟩
              · simpa [chainPositions, copied] using finalAgree
              · intro beforeTypes currentTypes typesLength typesAgree
                rw [shape] at typesAgree
                have step := typesStep (beforeTypes ++ [.cell (OptionalCell.cellType payload)]) currentTypes
                  (by simp [typesLength]; omega) typesAgree.skip
                simpa [chainPositions, copied, shape] using step
              · simpa [copyChainPlain, copied] using continuation
          | some binder =>
              obtain ⟨value, stored, valueTyped⟩ := heaps.runtime_hasTypes.read typed
              have copiedHeaps := heaps.allocate_administrative valueTyped
              have freshType : (world ++ [OptionalCell.cellType payload])[store.length]? =
                  some (OptionalCell.cellType payload) := by
                rw [← heaps.runtime_hasTypes.length_eq]
                simp
              have read := agree.read fresh
              rw [layout] at read
              have agreeNext := agree.copy fresh (.cellRef (OptionalCell.cellType payload) store.length)
              rw [layout] at agreeNext
              obtain ⟨copies, finalHeap, finalCanonical, added, finalStore, finalMap, finalWorld, finalRenaming,
                  addedTypes, copiedTail, related, finalHeaps, maps, worlds, frame, finalAgree, addedTyped,
                  typesStep, continuation⟩ :=
                copies_chain rest (index + 1) (done ++ [index + offset]) environment tailCanonical mapping
                  (world ++ [OptionalCell.cellType payload]) heap (store.allocate value).1
                  (before ++ [.cellRef (OptionalCell.cellType payload) store.length])
                  (.cellRef (OptionalCell.cellType payload) store.length :: current) η.lift
                  (tail.extend (LocationMap.Extends.refl mapping) ⟨[_], rfl⟩) copiedHeaps agreeNext
                  (nextLayout _) copyBelow
              refine ⟨copies, finalHeap, .cellRef (OptionalCell.cellType payload) store.length :: finalCanonical,
                added ++ [.cellRef (OptionalCell.cellType payload) store.length], finalStore, finalMap, finalWorld,
                finalRenaming, addedTypes ++ [.cell (OptionalCell.cellType payload)], copiedTail,
                .internal (worlds.lookup freshType) (copies_absent copiedTail absent) related, finalHeaps, maps,
                WorldExtends.trans ⟨[_], rfl⟩ worlds,
                (AdministrativePreserved.allocate_administrative mapping store value).trans frame, ?_,
                environment_append addedTyped (.cons (.cellRef (worlds.lookup freshType)) .nil), ?_,
                copy_continuation copied read stored continuation⟩
              · simpa [chainPositions, copied] using finalAgree
              · intro beforeTypes currentTypes typesLength typesAgree
                rw [shape] at typesAgree
                have typesNext := typesAgree.copy (by rw [typesLength, ← layout]; exact fresh)
                  (.cell (OptionalCell.cellType payload))
                rw [typesLength] at typesNext
                have step := typesStep (beforeTypes ++ [.cell (OptionalCell.cellType payload)])
                  (.cell (OptionalCell.cellType payload) :: currentTypes) (by simp [typesLength]; omega) typesNext
                simpa [chainPositions, copied, shape] using step

/-- The copies of a whole scope, with the embedding of the original layout
into the copies and the typing of the copies under any context of the scope's
shape. -/
private theorem copies_scope {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {source : TypedSource} {mapping : LocationMap} {world : StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {pre scopeCanonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {body : Expr}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment
      scopeCanonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (pre ++ scopeCanonical) actual) :
    ∃ copies finalHeap finalScopeCanonical added finalStore finalMap finalWorld finalEmbedding addedTypes,
      Dynamic.EnvironmentCopies source environment heap copies finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext scope copies
        finalScopeCanonical definitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding (pre ++ finalScopeCanonical) (added ++ actual) ∧
      RuntimeEnvironmentHasTypes finalWorld added addedTypes definitions ∧
      (∀ (preContext actualContext : Core.Context), preContext.length = pre.length →
        Renaming.Respects ξ (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
          actualContext →
        Renaming.Respects finalEmbedding
          (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
          (addedTypes ++ actualContext)) ∧
      ContinuationAgreement actual store
        ((SourceCoreSourceCells.copyScopePlain source scope (· + pre.length) body).rename ξ)
        (added ++ actual) finalStore (body.rename finalEmbedding) := by
  obtain ⟨copies, finalHeap, finalScopeCanonical, added, finalStore, finalMap, finalWorld, finalRenaming,
      addedTypes, copied, related, finalHeaps, maps, worlds, frame, finalAgree, addedTyped, typesStep,
      continuation⟩ :=
    copies_chain (source := source) (offset := pre.length)
      (inner := body.rename (scopeCopyRenaming source scope (· + pre.length)))
      scope 0 [] environment scopeCanonical mapping world heap store pre actual ξ environments heaps
      (fun _ _ found => by simpa only [Renaming.comp, copyRenaming_nil] using actualLayout found)
      (by simp) (by simp)
  have positions : copyRenaming ([] ++ chainPositions source (· + pre.length) scope 0) =
      scopeCopyRenaming source scope (· + pre.length) := by
    rw [scopeCopyRenaming_eq, List.nil_append]
  rw [positions] at finalAgree typesStep
  refine ⟨copies, finalHeap, finalScopeCanonical, added, finalStore, finalMap, finalWorld,
    Renaming.comp finalRenaming (scopeCopyRenaming source scope (· + pre.length)), addedTypes, copied, related,
    finalHeaps, maps, worlds, frame, fun found => finalAgree found, addedTyped, ?_, ?_⟩
  · intro preContext actualContext preLength types
    exact Agrees.respects.mp (typesStep preContext actualContext (by simp [preLength])
      (fun _ _ found => by simpa only [Renaming.comp, copyRenaming_nil] using types found))
  · rw [← Expr.rename_comp]
    exact continuation

/-- The actual copies made for a scope reach copied source cells related to
fresh Core cells. Both finite directions use the returned
continuation agreement; the continuation's execution is not a premise. -/
theorem copies_prefix {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {source : TypedSource} {mapping : LocationMap} {world : StoreTyping}
    {administrativeContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {pre scopeCanonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {body : Expr}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment
      scopeCanonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (pre ++ scopeCanonical) actual) :
    ∃ copies finalHeap finalScopeCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.EnvironmentCopies source environment heap copies finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext scope copies
        finalScopeCanonical definitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding (pre ++ finalScopeCanonical) finalActual ∧
      ContinuationAgreement actual store
        ((SourceCoreSourceCells.copyScopePlain source scope (· + pre.length) body).rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨copies, finalHeap, finalScopeCanonical, added, finalStore, finalMap, finalWorld, finalEmbedding, _,
      copied, related, finalHeaps, maps, worlds, frame, finalAgree, _, _, continuation⟩ :=
    copies_scope (source := source) (body := body) environments heaps actualLayout
  exact ⟨copies, finalHeap, finalScopeCanonical, added ++ actual, finalStore, finalMap, finalWorld,
    finalEmbedding, copied, related, finalHeaps, maps, worlds, frame, finalAgree, continuation⟩

/-- `copies_prefix` with the actual environment's typing: the copied slots of
the final environment keep the types of the slots they copy. -/
theorem copies_prefix_typed {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {source : TypedSource} {mapping : LocationMap} {world : StoreTyping}
    {administrativeContext preContext actualContext : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {pre scopeCanonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {body : Expr}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment
      scopeCanonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (pre ++ scopeCanonical) actual)
    (preLength : preContext.length = pre.length)
    (types : Renaming.Respects ξ
      (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions) :
    ∃ copies finalHeap finalScopeCanonical finalActual finalActualContext finalStore finalMap finalWorld
      finalEmbedding,
      Dynamic.EnvironmentCopies source environment heap copies finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext scope copies
        finalScopeCanonical definitions ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding (pre ++ finalScopeCanonical) finalActual ∧
      Renaming.Respects finalEmbedding
        (preContext ++ (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) finalActualContext ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalActualContext definitions ∧
      ContinuationAgreement actual store
        ((SourceCoreSourceCells.copyScopePlain source scope (· + pre.length) body).rename ξ)
        finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨copies, finalHeap, finalScopeCanonical, added, finalStore, finalMap, finalWorld, finalEmbedding,
      addedTypes, copied, related, finalHeaps, maps, worlds, frame, finalAgree, addedTyped, typesStep,
      continuation⟩ :=
    copies_scope (source := source) (body := body) environments heaps actualLayout
  exact ⟨copies, finalHeap, finalScopeCanonical, added ++ actual, addedTypes ++ actualContext, finalStore,
    finalMap, finalWorld, finalEmbedding, copied, related, finalHeaps, maps, worlds, frame, finalAgree,
    typesStep preContext actualContext preLength types,
    environment_append addedTyped (actualTyped.weaken worlds), continuation⟩

end Solcore.SourceSemantics.CoreLowering.CaptureCopies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.FunctionValues
/-! Authenticated ordinary lambda leaves for the generic payload model.

The source frame and actual compiler structure are static certificates.  Core
typing authenticates the emitted wrapper in its canonical lexical context.
The value relation retains the real renamed code and captured environment;
it never identifies closures made under different administrative layouts.

Exact source capture metadata is heap indexed and supplied separately.  None
of these certificates assumes a child execution or proves function-call
meaning. Named functions, builtin values, generalized local closures, and
stage guards remain separate obligations.
-/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.FunctionValues

open Frontend Frontend.SourceInference GeneralHeap FunctionCode

def sourceType (function : Dynamic.Closure) : TypeSystem.Ty :=
  .function (TypeSystem.Ty.productMany (function.parameters.map (·.scheme.body))) function.resultType

structure Code (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : BodyCertificate) (policy : SourceCoreFunctions.Policy)
    (function : Dynamic.Closure) (scope : SourceCoreLocalCell.Scope)
    (administrativeContext : Core.Context) where
  id : ExpressionId
  node : ExpressionNode
  reportedType : Core.Ty
  lowered : SourceCoreBasic.LoweredExpr
  artifact : LambdaCertificate bodyCertificate policy function.source scope id node
    function.parameters function.resultType function.body reportedType lowered
  frame : Dynamic.ClosureFrame program function
  projection : catalog.project (sourceType function) = .ok
    (Core.TaggedFunction.functionType artifact.parameterCore artifact.resultCore)
  outputTyped : Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext)
    lowered.expression (Core.LanguageResult.resultType
      (Core.TaggedFunction.functionType artifact.parameterCore artifact.resultCore)) catalog.definitions

/-- Code validity does not depend on the captured environment, so the same
code describes the closure over any copy of its captures. -/
def Code.recapture {catalog : SourceCoreDataCatalog.Catalog} {program : Program}
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    (code : Code catalog program bodyCertificate policy function scope administrativeContext)
    (captured : Dynamic.Environment) :
    Code catalog program bodyCertificate policy { function with captured := captured } scope
      administrativeContext where
  id := code.id
  node := code.node
  reportedType := code.reportedType
  lowered := code.lowered
  artifact := code.artifact
  frame := ⟨code.frame.signatures, code.frame.owner,
    ⟨code.frame.code.owner, code.frame.code.closed, code.frame.code.variables_closed,
      code.frame.code.residual_variables_open, code.frame.code.graph, code.frame.code.requirement_ledger,
      code.frame.code.occurrence⟩,
    code.frame.requirements, code.frame.evidence_covers⟩
  projection := code.projection
  outputTyped := code.outputTyped

def value (parameter result : Core.Ty) (body : Core.Expr)
    (embedding : Core.Renaming) (captured : Core.Environment) : Core.Value :=
  .pair (.inLeft .word .unit)
    (.closure parameter (Core.LanguageResult.resultType result) (body.rename embedding.lift) captured)

/-- Only ordinary anonymous source lambdas inhabit this leaf model.  Other
function identities can be composed with it through a separate constructor. -/
inductive Represents (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : BodyCertificate) (policy : SourceCoreFunctions.Policy)
    (mapping : LocationMap) (world : Core.StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Core.Value → Core.Ty → Prop where
  | closure {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Core.Environment}
      (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
      (code : Code catalog program bodyCertificate policy function scope layout.administrativeContext) :
      Represents catalog program bodyCertificate policy mapping world (sourceType function) (.closure function)
        (value code.artifact.parameterCore code.artifact.resultCore code.artifact.rawBody layout.embedding actual)
        (Core.TaggedFunction.functionType code.artifact.parameterCore code.artifact.resultCore)

variable {catalog : SourceCoreDataCatalog.Catalog} {program : Program}
  {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy}
  {mapping futureMapping : LocationMap} {world futureWorld : Core.StoreTyping}
  {type : TypeSystem.Ty} {source : Dynamic.Value} {core : Core.Value} {payload : Core.Ty}

theorem Represents.projection
    (related : Represents catalog program bodyCertificate policy mapping world type source core payload) :
    catalog.project type = .ok payload := by
  cases related with
  | closure _ code => exact code.projection

theorem Represents.runtime_hasType
    (related : Represents catalog program bodyCertificate policy mapping world type source core payload) :
    Core.RuntimeValueHasType world core payload catalog.definitions := by
  cases related with
  | closure layout code =>
    exact .pair (.inLeft .unit) (.closure layout.actualTyped
      (code.artifact.rawBody_hasType code.outputTyped |>.rename (layout.types.lift _)))

private theorem catalog_plain {catalog : SourceCoreDataCatalog.Catalog} {sourceParameter sourceResult : TypeSystem.Ty}
    {parameter result : Core.Ty}
    (projected : catalog.project (.function sourceParameter sourceResult) =
      .ok (Core.TaggedFunction.functionType parameter result)) : catalog.callableContracts = false := by
  cases first : catalog.project sourceParameter with
  | error error => simp [SourceCoreDataCatalog.Catalog.project, first, bind, Except.bind] at projected
  | ok parameterType =>
    cases second : catalog.project sourceResult with
    | error error => simp [SourceCoreDataCatalog.Catalog.project, first, second, bind, Except.bind] at projected
    | ok resultType =>
      cases profile : catalog.callableContracts with
      | false => rfl
      | true =>
        simp [SourceCoreDataCatalog.Catalog.project, first, second, SourceCoreDataCatalog.Catalog.functionType,
          profile, Core.TaggedFunction.functionType, Core.CallableContract.functionType, Core.TaggedFunction.identityType,
          bind, Except.bind] at projected

theorem Represents.observation
    (related : Represents catalog program bodyCertificate policy mapping world type source core payload)
    (signatures : ProgramSignatures) (identities : Dynamic.Value → Core.Word → Prop) :
    DataEqualityValues.Observation catalog signatures identities payload source core := by
  cases related with
  | closure layout code => exact .anonymous _ _ _ _ (catalog_plain code.projection)

theorem Represents.extend
    (related : Represents catalog program bodyCertificate policy mapping world type source core payload)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    Represents catalog program bodyCertificate policy futureMapping futureWorld type source core payload := by
  cases related with
  | closure layout code => exact .closure (layout.extend maps worlds) code

def model (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : BodyCertificate) (policy : SourceCoreFunctions.Policy) : GenericHeap.PayloadModel catalog where
  Represents := Represents catalog program bodyCertificate policy
  projection := Represents.projection
  runtime_hasType := Represents.runtime_hasType
  extend := Represents.extend

/-- Source lexical validity observes source cell declarations and generalized
storage metadata. It cannot be recovered from projected Core types alone. -/
def SourceCapturesValid (heap : Dynamic.Heap) : Dynamic.Value → Prop
  | .closure function => Dynamic.EnvironmentAgrees heap function.context.locals function.captured
  | _ => False

theorem SourceCapturesValid.extend {heap futureHeap : Dynamic.Heap}
    (valid : SourceCapturesValid heap source) (metadata : Dynamic.HeapMetadataExtend heap futureHeap) :
    SourceCapturesValid futureHeap source := by
  cases source <;> try cases valid
  exact valid.mono metadata

/-- The two independent parts together imply declarative source value typing.
This theorem still contains no assumption about executing the closure body. -/
theorem Represents.source_hasType
    (related : Represents catalog program bodyCertificate policy mapping world type source core payload)
    {heap : Dynamic.Heap} {context : Context}
    (signatures : context.signatures = program.signatures)
    (captures : SourceCapturesValid heap source) : Dynamic.ValueHasType context heap source type := by
  cases related with
  | closure layout code =>
    exact .closure (code.frame.signatures.trans signatures.symm) code.frame.code code.frame.evidence_covers captures

/-- Formation copies the captured cells of its creation environment and then
evaluates the emitted callable. The closure's layout relates the copies to the
fresh Core cells and records its renamed body and administrative captures. -/
theorem formation {model : GenericHeap.PayloadModel catalog}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
    {actual : Core.Environment} {heap : Dynamic.Heap} {store : Core.Store}
    (layout : FunctionCaptures.Layout catalog mapping world scope environment actual)
    (code : Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store) :
    ∃ captured finalHeap finalStore finalMap finalWorld closureActual embedding,
      Dynamic.EnvironmentCopies function.source environment heap captured finalHeap ∧
      Core.Evaluates actual store (code.lowered.expression.rename layout.embedding)
        (.inRight .word (value code.artifact.parameterCore code.artifact.resultCore
          code.artifact.rawBody embedding closureActual)) finalStore ∧
      Represents catalog program bodyCertificate policy finalMap finalWorld (sourceType function)
        (.closure { function with captured := captured })
        (value code.artifact.parameterCore code.artifact.resultCore code.artifact.rawBody embedding closureActual)
        (Core.TaggedFunction.functionType code.artifact.parameterCore code.artifact.resultCore) ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  obtain ⟨captured, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap,
      finalWorld, finalEmbedding, copy, environments, finalHeaps, maps, worlds, frame, lookups, types,
      actualTyped, agreement⟩ :=
    CaptureCopies.copies_prefix_typed (pre := []) (preContext := [])
      (body := code.artifact.callable) layout.represented heaps
      layout.lookups rfl layout.types layout.actualTyped
  let closureLayout : FunctionCaptures.Layout catalog finalMap finalWorld scope captured finalActual := {
    administrativeContext := layout.administrativeContext
    canonical := finalCanonical
    actualContext := finalActualContext
    embedding := finalEmbedding
    represented := environments
    lookups := lookups
    types := types
    actualTyped := actualTyped }
  have represented : Represents catalog program bodyCertificate policy finalMap finalWorld
      (sourceType { function with captured := captured }) (.closure { function with captured := captured })
      (value code.artifact.parameterCore code.artifact.resultCore code.artifact.rawBody finalEmbedding finalActual)
      (Core.TaggedFunction.functionType code.artifact.parameterCore code.artifact.resultCore) := by
    exact @Represents.closure catalog program bodyCertificate policy finalMap finalWorld
      { function with captured := captured } scope finalActual closureLayout (code.recapture captured)
  refine ⟨captured, finalHeap, finalStore, finalMap, finalWorld, finalActual, finalEmbedding, copy, ?_,
    represented, finalHeaps, maps, worlds, frame⟩
  have emitted := congrArg SourceCoreBasic.LoweredExpr.expression code.artifact.emitted_callable
  dsimp only at emitted
  rw [emitted]
  have base : (fun index : Nat => index) = (· + ([] : Core.Environment).length) := by
    funext index
    simp
  rw [base]
  apply agreement.wrap
  exact .inRight (.pair (.inLeft .unit) .lambda)

/-- Independent source formation and the emitted Core lambda describe the
same closure over the same copies of the creation environment. Output
coercions and requirement execution are deliberately outside this ordinary
formation rule. -/
theorem formation_corresponds {model : GenericHeap.PayloadModel catalog}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
    {actual : Core.Environment} {heap : Dynamic.Heap} {store : Core.Store}
    (layout : FunctionCaptures.Layout catalog mapping world scope environment actual)
    (code : Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (requirements : code.node.requirements = []) (coercions : code.node.coercions = []) :
    ∃ captured finalHeap finalStore finalMap finalWorld closureActual embedding,
      Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment
        heap code.id (.closure { function with captured := captured }) finalHeap ∧
      Core.Evaluates actual store (code.lowered.expression.rename layout.embedding)
        (.inRight .word (value code.artifact.parameterCore code.artifact.resultCore
          code.artifact.rawBody embedding closureActual)) finalStore ∧
      Represents catalog program bodyCertificate policy finalMap finalWorld (sourceType function)
        (.closure { function with captured := captured })
        (value code.artifact.parameterCore code.artifact.resultCore code.artifact.rawBody embedding closureActual)
        (Core.TaggedFunction.functionType code.artifact.parameterCore code.artifact.resultCore) ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  obtain ⟨captured, finalHeap, finalStore, finalMap, finalWorld, closureActual, embedding, copy, evaluated,
      represented, heaps, maps, worlds, frame⟩ := formation layout code heaps
  refine ⟨captured, finalHeap, finalStore, finalMap, finalWorld, closureActual, embedding, ?_, evaluated,
    represented, heaps, maps, worlds, frame⟩
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound code.artifact.found)
  · rw [code.artifact.form, requirements, coercions]
    exact .lambda rfl copy
  · rw [coercions]
    exact .nil

end Solcore.SourceSemantics.CoreLowering.FunctionValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.FunctionCallBody
/-! Ordinary closure invocation uses the independent source call rules. This
module factors their body outcomes and constructs the actual entry prefix: the
copies of the captured cells, then the parameters. It assumes no body
execution when authenticating code, copying captures or allocating arguments.
The source heap metadata invariant remains separate from Core world typing. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.FunctionCallBody
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open FunctionArguments

inductive Outcome (program : Program) (context : SourceSemantics.Context)
    (caller invocation : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (function : Dynamic.Value) (arguments : List Dynamic.Value) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {result after} (execution : Dynamic.CallableApplies program context caller invocation before
      function arguments result after) : Outcome program context caller invocation before function arguments (.value result) after
  | fault {reason after} (execution : Dynamic.CallableFaults program context caller invocation before
      function arguments reason after) : Outcome program context caller invocation before function arguments (.fault reason) after

/-- These are precisely the body exits represented by the independent closure
call rules. Non-Unit fallthrough is not assigned an invented source fault. -/
inductive Trace (program : Program) (function : Dynamic.Closure) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | returned {finalContext result after}
      (execution : Dynamic.FunctionStatementsExecute program context function.evidence function.source
        environment before function.body finalContext (.returned result) after) :
      Trace program function context environment before (.value result) after
  | unit {finalContext finalEnvironment after}
      (resultUnit : function.resultType = .unit)
      (execution : Dynamic.FunctionStatementsExecute program context function.evidence function.source
        environment before function.body finalContext (.fallthrough finalEnvironment) after) :
      Trace program function context environment before (.value .unit) after
  | fault {finalContext reason after}
      (execution : Dynamic.FunctionStatementsFault program context function.evidence function.source
        environment before function.body finalContext reason after) :
      Trace program function context environment before (.fault reason) after
  | escaped {finalContext control after}
      (execution : Dynamic.FunctionStatementsExecute program context function.evidence function.source
        environment before function.body finalContext control after)
      (escape : (∃ environment, control = .breaking environment) ∨
        (∃ environment, control = .continuing environment)) :
      Trace program function context environment before (.fault .controlEscapedFunction) after

variable {program : Program} {function : Dynamic.Closure}

theorem Trace.call {context callContext : SourceSemantics.Context}
    {caller : Dynamic.EvidenceEnvironment} {before copied bound after : Dynamic.Heap}
    {arguments : List Dynamic.Value} {entry environment : Dynamic.Environment}
    {types : List TypeSystem.Ty} {outcome : Dynamic.ExpressionOutcome}
    (frame : Dynamic.ClosureFrame program function)
    (extension : MonoBindersExtend function.source.owner function.context function.parameters types callContext)
    (copy : Dynamic.EnvironmentCopies function.source function.captured before entry copied)
    (allocation : Dynamic.BindersAllocate entry copied function.parameters arguments environment bound)
    (trace : Trace program function callContext environment bound outcome after) :
    Outcome program context caller function.evidence before (.closure function) arguments outcome after := by
  cases trace with
  | returned execution => exact .value (.closure rfl frame extension copy allocation execution rfl)
  | unit resultUnit execution =>
      exact .value (.closureUnit rfl frame resultUnit extension copy allocation execution ⟨_, rfl⟩)
  | fault execution => exact .fault (.closureBody rfl frame extension copy allocation execution)
  | escaped execution escape =>
      exact .fault (.closureControlEscape rfl frame extension copy allocation execution escape)

/-- A finite source closure call exposes a body trace after copying the
captures and allocating the parameters in source order. The represented
argument list rules out arity faults. -/
theorem Outcome.trace {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : function.parameters.length = arguments.length)
    (execution : Outcome program context caller function.evidence before (.closure function) arguments outcome after) :
    ∃ types callContext entry copied environment bound,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext ∧
      Dynamic.EnvironmentCopies function.source function.captured before entry copied ∧
      Dynamic.BindersAllocate entry copied function.parameters arguments environment bound ∧
      Trace program function callContext environment bound outcome after := by
  cases execution with
  | value execution =>
    cases execution with
    | closure _ _ extended copy allocated executed returned =>
      subst returned
      exact ⟨_, _, _, _, _, _, extended, copy, allocated, .returned executed⟩
    | closureUnit _ _ resultUnit extended copy allocated executed fellThrough =>
      obtain ⟨_, rfl⟩ := fellThrough
      exact ⟨_, _, _, _, _, _, extended, copy, allocated, .unit resultUnit executed⟩
  | fault execution =>
    cases execution with
    | notCallable invalid => exact False.elim (invalid trivial)
    | closureArity mismatch => exact False.elim (mismatch arity)
    | closureBody _ _ extended copy allocated fault =>
      exact ⟨_, _, _, _, _, _, extended, copy, allocated, .fault fault⟩
    | closureControlEscape _ _ extended copy allocated executed escape =>
      exact ⟨_, _, _, _, _, _, extended, copy, allocated, .escaped executed escape⟩

theorem mono_binders {owner : Resolved.DeclarationId} {context finalContext : SourceSemantics.Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extension : MonoBindersExtend owner context parameters types finalContext) :
    BindersExtend owner context parameters finalContext ∧
      (∀ binder, binder ∈ parameters → binder.scheme.quantified = []) := by
  induction extension with
  | nil => exact ⟨.nil _, by intro binder member; cases member⟩
  | cons scheme head tail ih =>
    refine ⟨.cons head ih.1, ?_⟩
    intro binder member
    rcases List.mem_cons.mp member with rfl | member
    · simp [scheme, TypeSystem.Scheme.mono]
    · exact ih.2 binder member

/-- Static body and parameter typing are recovered from independent code
validity. They are not inferred from Core typing or successful execution. -/
theorem frame_body (frame : Dynamic.ClosureFrame program function) :
    ∃ types context finalContext facts,
      MonoBindersExtend function.source.owner function.context function.parameters types context ∧
      StatementsHaveType function.source {returnType := function.resultType, loopDepth := 0}
        context function.body finalContext facts ∧ BodyCompletes function.resultType facts := by
  obtain ⟨id, node, _, form, _, typed⟩ := frame.code.occurrence
  rw [form] at typed
  generalize annotated : (TypeSystem.Ty.function
    (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) function.resultType) = type at typed
  cases typed with
  | lambda _ extended body completes => exact ⟨_, _, _, _, extended, body, completes⟩

/-- Every independently valid parameter installation reaches the statically
certified lambda body context. -/
theorem frame_body_at (frame : Dynamic.ClosureFrame program function)
    {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    (extension : MonoBindersExtend function.source.owner function.context function.parameters types context) :
    ∃ finalContext facts,
      StatementsHaveType function.source {returnType := function.resultType, loopDepth := 0}
        context function.body finalContext facts ∧ BodyCompletes function.resultType facts := by
  obtain ⟨otherTypes, otherContext, finalContext, facts, other, body, completes⟩ := frame_body frame
  have typesSame : otherTypes = types := other.bodyTypes_eq.symm.trans extension.bodyTypes_eq
  subst otherTypes
  have contextSame := other.functional extension
  subst otherContext
  exact ⟨finalContext, facts, body, completes⟩

private theorem parameters_scope {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope finalScope : SourceCoreLocalCell.Scope} {parameters : List TypedBinder}
    {lowered : List (TypedBinder × Ty)}
    (tree : FunctionCode.Parameters policy source scope parameters lowered finalScope) :
    lowered.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope = finalScope := by
  induction tree with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- A body entry records the copied captures, the real administrative captures
and the temporary slots. The continuation agreement is bidirectional and
applies to arbitrary bodies, including bodies that construct new closures. -/
structure Entry {catalog : SourceCoreDataCatalog.Catalog}
    (model : GenericHeap.PayloadModel catalog) {bodyCertificate : FunctionCode.BodyCertificate}
    {policy : SourceCoreFunctions.Policy} {scope : SourceCoreLocalCell.Scope}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {entryActual : Environment}
    (layout : FunctionCaptures.Layout catalog initialMap initialWorld scope function.captured entryActual)
    (code : FunctionValues.Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (before : Dynamic.Heap) (initialStore : Store) (context : SourceSemantics.Context)
    (arguments : List Dynamic.Value) (values : List Value) where
  entry : Dynamic.Environment
  copied : Dynamic.Heap
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actual : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  copy : Dynamic.EnvironmentCopies function.source function.captured before entry copied
  allocation : Dynamic.BindersAllocate entry copied function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents catalog mapping world layout.administrativeContext
    code.artifact.bodyScope environment canonical
  heaps : GenericHeap.HeapRepresents model mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actual
  agreement : ContinuationAgreement (DataPatternValues.packValues values :: entryActual) initialStore
    (code.artifact.rawBody.rename layout.embedding.lift) actual store (code.artifact.bodyCode.rename embedding)

/-- Copying the captures and installing the real parameter prefix constructs
all heap and lexical facts. No source or Core evaluation of the body is a
premise. -/
theorem entry_exists {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog} {bodyCertificate : FunctionCode.BodyCertificate}
    {policy : SourceCoreFunctions.Policy} {scope : SourceCoreLocalCell.Scope}
    {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    {before : Dynamic.Heap} {store : Store} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {arguments : List Dynamic.Value} {values : List Value}
    (extension : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured) :
    Nonempty (Entry model layout code before store context arguments values) := by
  obtain ⟨entry, copied, copiedCanonical, copiedActual, copiedStore, copiedMap, copiedWorld, copiedEmbedding,
      copy, copiedEnvironments, copiedHeaps, copiedMaps, copiedWorlds, copiedFrame, copiedLookups, copies⟩ :=
    CaptureCopies.copies_prefix (pre := [DataPatternValues.packValues values])
      (body := SourceCoreFunctions.bindParameters code.artifact.loweredParameters code.artifact.resultCore
        (code.artifact.bodyCode.weakenAt code.artifact.loweredParameters.length))
      layout.represented heaps
      (EnvironmentsAgree.lift (mapping := layout.embedding) layout.lookups (DataPatternValues.packValues values))
  obtain ⟨environment, heap, canonical, actual, finalStore, finalMap, finalWorld, embedding,
      allocation, environments, finalHeaps, maps, worlds, frame, lookups, agreement⟩ :=
    parameters_prefix (represented.extend copiedMaps copiedWorlds) (body := code.artifact.bodyCode)
      (outputType := code.artifact.resultCore) copiedEnvironments copiedHeaps copiedLookups
  rw [code.artifact.parametersTree.binders] at allocation
  rw [parameters_scope code.artifact.parametersTree] at environments
  have mono := mono_binders extension
  exact ⟨⟨entry, copied, environment, heap, canonical, actual, finalStore, finalMap, finalWorld, embedding,
    copy, allocation, environments, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 (copy.agrees locals) allocation,
    copiedMaps.trans maps, copiedWorlds.trans worlds, copiedFrame.trans frame,
    copy.metadata_extends.trans (GenericLexicalContext.binders_metadata allocation), lookups,
    copies.trans agreement⟩⟩

/-- Independent source parameter allocation is deterministic. -/
theorem allocations_same {environment leftEnv rightEnv : Dynamic.Environment}
    {before left right : Dynamic.Heap} {binders : List TypedBinder} {values : List Dynamic.Value}
    (first : Dynamic.BindersAllocate environment before binders values leftEnv left)
    (second : Dynamic.BindersAllocate environment before binders values rightEnv right) :
    leftEnv = rightEnv ∧ left = right := by
  induction first generalizing rightEnv right with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | cons allocation rest ih =>
    cases second with
    | cons other rest' => cases allocation; cases other; exact ih rest'

end Solcore.SourceSemantics.CoreLowering.FunctionCallBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.FunctionCalls
/-! Finite ordinary closure-call composition. Static code/capture certificates
are separate from the universal child body preservation/reflection hypotheses.
The parameter wrapper, heap extensions and source call trace are derived here.
This is not an unconditional theorem for every accepted function compiler:
instantiating the child body hypotheses, caller expression evaluation, staged
calls, globals and generalized local functions remain separate work. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.FunctionCalls
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open FunctionArguments FunctionCallBody

abbrev FaultRep := Dynamic.SemanticFault → Word → Prop

/-- The fault-to-token laws that hold at every site, unlike the per-site
`uninitialized` hypotheses. `Panic(code)` fails with the code's own reason in
every function. Theorems whose code may panic take this class as an instance
argument, which callers pass on from their own binder. -/
class FaultTokens (faults : FaultRep) : Prop where
  panic (code : UInt8) : faults (.panic code) (SourceCorePanics.reason code)

inductive ResultRepresents {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : StoreTyping) (sourceType : TypeSystem.Ty) (type : Ty) (faults : FaultRep) :
    Dynamic.ExpressionOutcome → Value → Prop where
  | value {source value} (represented : model.Represents mapping world sourceType source value type) :
      ResultRepresents model mapping world sourceType type faults (.value source) (.inRight .word value)
  | fault {reason token} (represented : faults reason token) :
      ResultRepresents model mapping world sourceType type faults (.fault reason) (.inLeft type (.word token))

/-- A universal semantic IH for an independently certified body. It is not a
field of the static function code certificate. Source traces supply finiteness. -/
def BodyPreserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (function : Dynamic.Closure) (certificate : FunctionCode.BodyCertificate)
    (faults : FaultRep) : Prop :=
  ∀ {scope type body}, certificate function.source scope function.body type body →
  ∀ {context staticFinal facts}, StatementsHaveType function.source
    {returnType := function.resultType, loopDepth := 0} context function.body staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Trace program function context environment before outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (body.rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld function.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-- The source body trace is constructed from Core execution. No finite source
trace is a premise of this universal reflection obligation. -/
def BodyReflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (function : Dynamic.Closure) (certificate : FunctionCode.BodyCertificate)
    (faults : FaultRep) : Prop :=
  ∀ {scope type body}, certificate function.source scope function.body type body →
  ∀ {context staticFinal facts}, StatementsHaveType function.source
    {returnType := function.resultType, loopDepth := 0} context function.body staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (body.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Trace program function context environment before outcome after ∧
      ResultRepresents model finalMap finalWorld function.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

variable {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
  {program : Program} {function : Dynamic.Closure} {bodyCertificate : FunctionCode.BodyCertificate}
  {policy : SourceCoreFunctions.Policy} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  {faults : FaultRep}

/-- Source closure-call preservation includes the production parameter wrapper.
Previously existing administrative values and shared captured locations remain
related through the returned map/world extension and administrative frame. -/
theorem preserves
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (bodyMeaning : BodyPreserves model program function bodyCertificate faults)
    {before after : Dynamic.Heap} {store : Store} {arguments : List Dynamic.Value} {values : List Value}
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment} {outcome : Dynamic.ExpressionOutcome}
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (execution : Outcome program context caller function.evidence before (.closure function) arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues values :: actual) store
        (code.artifact.rawBody.rename layout.embedding.lift) value finalStore ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have arity : function.parameters.length = arguments.length := by
    rw [← code.artifact.parametersTree.binders, List.length_map]
    exact represented.length.1
  obtain ⟨types, callContext, entryEnvironment, copied, environment, bound, extension, copy, allocated, trace⟩ :=
    execution.trace arity
  obtain ⟨entry⟩ := entry_exists layout code extension represented heaps locals
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy entry.copy
  obtain ⟨rfl, rfl⟩ := allocations_same allocated entry.allocation
  obtain ⟨_, _, typed, _⟩ := frame_body_at code.frame extension
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
    bodyMeaning code.artifact.bodyTree typed entry.environments entry.heaps entry.locals entry.lookups trace
  exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, result, finalHeaps,
    entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata⟩

/-- A completed Core closure body constructs its source call, including body
faults and escaped control. Only the reusable universal child theorem is assumed;
there is no source execution premise and no first-order restriction on the store. -/
theorem reflects
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (bodyMeaning : BodyReflects model program function bodyCertificate faults)
    {before : Dynamic.Heap} {store finalStore : Store} {arguments : List Dynamic.Value} {values : List Value}
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment) {value : Value}
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (evaluated : Evaluates (DataPatternValues.packValues values :: actual) store
      (code.artifact.rawBody.rename layout.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Outcome program context caller function.evidence before (.closure function) arguments outcome after ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨types, callContext, _, _, extension, typed, _⟩ := frame_body code.frame
  obtain ⟨entry⟩ := entry_exists layout code extension represented heaps locals
  obtain ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
    bodyMeaning code.artifact.bodyTree typed entry.environments entry.heaps entry.locals entry.lookups
      (entry.agreement.unwrap evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace.call code.frame extension entry.copy entry.allocation,
    result, finalHeaps, entry.maps.trans maps, entry.worlds.trans worlds,
    entry.frame.trans frame, entry.metadata.trans metadata⟩

/-- A finite source invocation supplies sufficient fuel for the existing Core
machine. Fuel exhaustion is not interpreted as a terminal source outcome. -/
theorem preserves_sufficient_fuel
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (bodyMeaning : BodyPreserves model program function bodyCertificate faults)
    {before after : Dynamic.Heap} {store : Store} {arguments : List Dynamic.Value} {values : List Value}
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment} {outcome : Dynamic.ExpressionOutcome}
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (execution : Outcome program context caller function.evidence before (.closure function) arguments outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (code.artifact.rawBody.rename layout.embedding.lift)
          (DataPatternValues.packValues values :: actual) store) = .done value finalStore) ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    preserves layout code bodyMeaning represented heaps locals execution
  obtain ⟨required, runs⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required, runs, represented, finalHeaps, maps, worlds, frame, metadata⟩

/-- Every completed machine run of the authenticated closure body constructs
an independent source call under the explicit child reflection theorem. -/
theorem reflects_done
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (bodyMeaning : BodyReflects model program function bodyCertificate faults)
    {before : Dynamic.Heap} {store finalStore : Store} {arguments : List Dynamic.Value} {values : List Value}
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment) {value : Value} {fuel : Nat}
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (completed : runStateful fuel (.initial (code.artifact.rawBody.rename layout.embedding.lift)
      (DataPatternValues.packValues values :: actual) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Outcome program context caller function.evidence before (.closure function) arguments outcome after ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects layout code bodyMeaning context caller represented heaps locals
    (runStateful_evaluation_sound completed)

/-- The last application expression emitted by the tagged call helper enters
exactly the captured body and actual environment authenticated above. -/
theorem application_agreement (parameter result : Ty) (body : Expr) (ξ : Renaming)
    (captured caller : Environment) (arguments : Value) (store : Store) :
    ContinuationAgreement
      (arguments :: FunctionValues.value parameter result body ξ captured :: caller) store
      (.apply (.second (.var 1)) (.var 0)) (arguments :: captured) store (body.rename ξ.lift) := by
  constructor
  · intro value finalStore evaluated
    exact .apply (.second (.var rfl)) (.var rfl) evaluated
  · intro value finalStore evaluated
    obtain ⟨size, sized⟩ := evaluation_has_size evaluated
    obtain ⟨_, _, bodyEvaluation⟩ := sized.apply_body
      (show Evaluates (arguments :: FunctionValues.value parameter result body ξ captured :: caller) store
        (.second (.var 1)) (.closure parameter (LanguageResult.resultType result) (body.rename ξ.lift) captured) store
        from .second (.var rfl)) (.var rfl)
    exact bodyEvaluation.sound

end Solcore.SourceSemantics.CoreLowering.FunctionCalls
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning
/-! Universal child-expression interfaces for arbitrary authenticated payloads.
The outcome relation is shared with ordinary function calls. These obligations
are semantic induction hypotheses, not fields of static compilation receipts.
Temporary Core slots are represented by an explicit lexical renaming. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly

abbrev Certificate := SourceCoreLocalCell.Scope → ExpressionId → SourceCoreBasic.LoweredExpr → Prop
abbrev FaultRep := FunctionCalls.FaultRep
abbrev ResultRepresents := @FunctionCalls.ResultRepresents

/-- Every finite independent child execution has a matching Core execution.
The payload model may include closures, mappings and catalog-authenticated data. -/
def Preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-- Every completed Core child execution constructs its independent source
outcome. No source child execution is a premise. -/
def Reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

theorem ResultRepresents.extend {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions} {mapping futureMapping : LocationMap}
    {world futureWorld : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty} {faults : FaultRep}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (represented : ResultRepresents model mapping world sourceType type faults outcome value)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ResultRepresents model futureMapping futureWorld sourceType type faults outcome value := by
  cases represented with
  | value payload => exact .value (model.extend payload maps worlds)
  | fault reason => exact .fault reason

/-- Inserting an administrative value changes the code's renaming, not the
canonical captured environment or any existing value. -/
theorem agree_prefix {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index foundValue found
  exact agrees found

theorem rename_prefix (expression : Expr) (ξ : Renaming) :
    expression.rename (Renaming.comp (Renaming.insertion 0) ξ) =
      (expression.rename ξ).weakenAt 0 := by
  rw [← Expr.rename_comp, Expr.rename_insertion]

end Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ContractedFunctionValues
/-! Anonymous closures with authenticated artifact-owned callable descriptors.
The raw code/captures and the descriptor origin are independent static fields.
The descriptor authenticates its origin lookup; reconstruction of the original
staging flags from prepared source needs the enclosing compiler receipt.
A concrete profile must prove its lambda-decoration equation; code acceptance
alone does not establish that an arbitrary callable hook preserves meaning.

This relation proves formation, typing and world extension. It does not identify
legacy staging guards with the independent source call rules, and does not
import arbitrary external closure bodies or instantiate a full body theorem. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ContractedFunctionValues
open Frontend Frontend.SourceInference GeneralHeap

structure Code (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : FunctionCode.BodyCertificate) (policy : SourceCoreFunctions.Policy)
    (compilation : SourceCoreFunctions.Context) (table : SourceCoreStageCodebook.Table)
    (active : TypeSystem.Substitution) (function : Dynamic.Closure)
    (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context) where
  id : ExpressionId
  node : ExpressionNode
  reportedType : Core.Ty
  lowered : SourceCoreBasic.LoweredExpr
  artifact : DecoratedFunctionCode.LambdaCertificate bodyCertificate policy compilation function.source scope id node
    function.parameters function.resultType function.body reportedType lowered
  owner : compilation.owner.declaration = function.source.owner
  descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id active)
  decoration : ∀ value, policy.callables.decorateCallable compilation function.source node (.lambda id)
    artifact.raw.parameterCore artifact.raw.resultCore (Core.LanguageResult.success value) =
      .ok (Core.LanguageResult.success (descriptor.wrap value))
  frame : Dynamic.ClosureFrame program function
  projection : catalog.project (FunctionValues.sourceType function) = .ok
    (Core.CallableContract.functionType artifact.raw.parameterCore artifact.raw.resultCore)
  outputTyped : Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext)
    lowered.expression (Core.LanguageResult.resultType
      (Core.CallableContract.functionType artifact.raw.parameterCore artifact.raw.resultCore)) catalog.definitions

variable {catalog : SourceCoreDataCatalog.Catalog} {program : Program}
  {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
  {compilation : SourceCoreFunctions.Context} {table : SourceCoreStageCodebook.Table}
  {active : TypeSystem.Substitution} {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrativeContext : Core.Context}

/-- The decorated callable created at the lambda, before its creation-time copies. -/
def Code.callable
    (code : Code catalog program bodyCertificate policy compilation table active function scope administrativeContext) :
    Core.Expr :=
  Core.LanguageResult.success (code.descriptor.wrap
    (Core.TaggedFunction.anonymous (.lambda code.artifact.raw.parameterCore
      (Core.LanguageResult.resultType code.artifact.raw.resultCore) code.artifact.raw.rawBody)))

theorem Code.emitted
    (code : Code catalog program bodyCertificate policy compilation table active function scope administrativeContext) :
    code.lowered.expression =
      SourceCoreSourceCells.copyScopePlain function.source scope (fun index => index) code.callable := by
  have accepted := code.artifact.decoration
  have expected := code.decoration (Core.TaggedFunction.anonymous (.lambda code.artifact.raw.parameterCore
    (Core.LanguageResult.resultType code.artifact.raw.resultCore) code.artifact.raw.rawBody))
  have same := Except.ok.inj (accepted.symm.trans expected)
  rw [congrArg SourceCoreBasic.LoweredExpr.expression code.artifact.emitted]
  dsimp only
  rw [same]
  rfl

/-- Code validity does not depend on the captured environment, so the same
code describes the closure over any copy of its captures. -/
def Code.recapture
    (code : Code catalog program bodyCertificate policy compilation table active function scope administrativeContext)
    (captured : Dynamic.Environment) :
    Code catalog program bodyCertificate policy compilation table active { function with captured := captured }
      scope administrativeContext where
  id := code.id
  node := code.node
  reportedType := code.reportedType
  lowered := code.lowered
  artifact := code.artifact
  owner := code.owner
  descriptor := code.descriptor
  decoration := code.decoration
  frame := ⟨code.frame.signatures, code.frame.owner,
    ⟨code.frame.code.owner, code.frame.code.closed, code.frame.code.variables_closed,
      code.frame.code.residual_variables_open, code.frame.code.graph, code.frame.code.requirement_ledger,
      code.frame.code.occurrence⟩,
    code.frame.requirements, code.frame.evidence_covers⟩
  projection := code.projection
  outputTyped := code.outputTyped

theorem Code.rawBody_hasType
    (code : Code catalog program bodyCertificate policy compilation table active function scope administrativeContext) :
    Core.HasType (code.artifact.raw.parameterCore :: SourceCoreLocalCell.coreContext scope ++ administrativeContext)
      code.artifact.raw.rawBody (Core.LanguageResult.resultType code.artifact.raw.resultCore) catalog.definitions := by
  have typed := code.outputTyped
  rw [code.emitted] at typed
  replace typed := CaptureCopyTyping.copyScopePlain_body_hasType (fun _ _ same => same) typed
  cases typed with
  | inRight _ wrapped =>
    cases wrapped with
    | pair tagged _ =>
      cases tagged with
      | pair _ closure =>
        cases closure with
        | lambda _ _ body => exact body

private theorem contracted_catalog {sourceParameter sourceResult : TypeSystem.Ty} {parameter result : Core.Ty}
    (projected : catalog.project (.function sourceParameter sourceResult) =
      .ok (Core.CallableContract.functionType parameter result)) : catalog.callableContracts = true := by
  cases first : catalog.project sourceParameter with
  | error error => simp [SourceCoreDataCatalog.Catalog.project, first, bind, Except.bind] at projected
  | ok parameterType =>
    cases second : catalog.project sourceResult with
    | error error => simp [SourceCoreDataCatalog.Catalog.project, first, second, bind, Except.bind] at projected
    | ok resultType =>
      cases profile : catalog.callableContracts with
      | true => rfl
      | false =>
        simp [SourceCoreDataCatalog.Catalog.project, first, second, SourceCoreDataCatalog.Catalog.functionType,
          profile, Core.TaggedFunction.functionType, Core.CallableContract.functionType,
          Core.TaggedFunction.identityType, bind, Except.bind] at projected

def value (parameter result : Core.Ty) (body : Core.Expr) (embedding : Core.Renaming)
    (captured : Core.Environment) (contract : Core.Word) : Core.Value :=
  .pair (FunctionValues.value parameter result body embedding captured) (.word contract)

inductive Represents (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : FunctionCode.BodyCertificate) (table : SourceCoreStageCodebook.Table)
    (mapping : LocationMap) (world : Core.StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Core.Value → Core.Ty → Prop where
  | closure {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
      {active : TypeSystem.Substitution} {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Core.Environment}
      (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
      (code : Code catalog program bodyCertificate policy compilation table active function scope layout.administrativeContext) :
      Represents catalog program bodyCertificate table mapping world
        (FunctionValues.sourceType function) (.closure function)
        (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
          layout.embedding actual code.descriptor.id)
        (Core.CallableContract.functionType code.artifact.raw.parameterCore code.artifact.raw.resultCore)

variable {mapping futureMapping : LocationMap} {world futureWorld : Core.StoreTyping}
  {type : TypeSystem.Ty} {source : Dynamic.Value} {core : Core.Value} {payload : Core.Ty}

theorem Represents.projection
    (related : Represents catalog program bodyCertificate table mapping world type source core payload) :
    catalog.project type = .ok payload := by
  cases related with
  | closure _ code => exact code.projection

theorem Represents.runtime_hasType
    (related : Represents catalog program bodyCertificate table mapping world type source core payload) :
    Core.RuntimeValueHasType world core payload catalog.definitions := by
  cases related with
  | closure layout code =>
    exact .pair (.pair (.inLeft .unit) (.closure layout.actualTyped
      (code.rawBody_hasType.rename (layout.types.lift _)))) .word

theorem Represents.observation
    (related : Represents catalog program bodyCertificate table mapping world type source core payload)
    (signatures : ProgramSignatures) (identities : Dynamic.Value → Core.Word → Prop) :
    DataEqualityValues.Observation catalog signatures identities payload source core := by
  cases related with
  | closure layout code => exact .contractedAnonymous _ _ _ _ _ (contracted_catalog code.projection)

theorem Represents.extend
    (related : Represents catalog program bodyCertificate table mapping world type source core payload)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : Core.WorldExtends world futureWorld) :
    Represents catalog program bodyCertificate table futureMapping futureWorld type source core payload := by
  cases related with
  | closure layout code => exact .closure (layout.extend maps worlds) code

def model (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : FunctionCode.BodyCertificate) (table : SourceCoreStageCodebook.Table) :
    GenericHeap.PayloadModel catalog where
  Represents := Represents catalog program bodyCertificate table
  projection := Represents.projection
  runtime_hasType := Represents.runtime_hasType
  extend := Represents.extend

theorem Represents.source_hasType
    (related : Represents catalog program bodyCertificate table mapping world type source core payload)
    {heap : Dynamic.Heap} {context : Context} (signatures : context.signatures = program.signatures)
    (captures : FunctionValues.SourceCapturesValid heap source) : Dynamic.ValueHasType context heap source type := by
  cases related with
  | closure layout code =>
    exact .closure (code.frame.signatures.trans signatures.symm) code.frame.code code.frame.evidence_covers captures

/-- The actual emitted wrapper copies the captured cells of its creation
environment, then preserves the renamed code and the closure's capture layout
while retaining the exact artifact descriptor. -/
theorem formation {model : GenericHeap.PayloadModel catalog}
    {environment : Dynamic.Environment} {actual : Core.Environment} {heap : Dynamic.Heap} {store : Core.Store}
    (layout : FunctionCaptures.Layout catalog mapping world scope environment actual)
    (code : Code catalog program bodyCertificate policy compilation table active function scope layout.administrativeContext)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store) :
    ∃ captured finalHeap finalStore finalMap finalWorld closureActual embedding,
      Dynamic.EnvironmentCopies function.source environment heap captured finalHeap ∧
      Core.Evaluates actual store (code.lowered.expression.rename layout.embedding)
        (.inRight .word (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
          embedding closureActual code.descriptor.id)) finalStore ∧
      Represents catalog program bodyCertificate table finalMap finalWorld
        (FunctionValues.sourceType function) (.closure { function with captured := captured })
        (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
          embedding closureActual code.descriptor.id)
        (Core.CallableContract.functionType code.artifact.raw.parameterCore code.artifact.raw.resultCore) ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  obtain ⟨captured, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap,
      finalWorld, finalEmbedding, copy, environments, finalHeaps, maps, worlds, frame, lookups, types,
      actualTyped, agreement⟩ :=
    CaptureCopies.copies_prefix_typed (pre := []) (preContext := [])
      (body := code.callable) layout.represented heaps
      layout.lookups rfl layout.types layout.actualTyped
  let closureLayout : FunctionCaptures.Layout catalog finalMap finalWorld scope captured finalActual := {
    administrativeContext := layout.administrativeContext
    canonical := finalCanonical
    actualContext := finalActualContext
    embedding := finalEmbedding
    represented := environments
    lookups := lookups
    types := types
    actualTyped := actualTyped }
  have represented : Represents catalog program bodyCertificate table finalMap finalWorld
      (FunctionValues.sourceType { function with captured := captured }) (.closure { function with captured := captured })
      (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
        finalEmbedding finalActual code.descriptor.id)
      (Core.CallableContract.functionType code.artifact.raw.parameterCore code.artifact.raw.resultCore) := by
    exact @Represents.closure catalog program bodyCertificate table finalMap finalWorld policy compilation active
      { function with captured := captured } scope finalActual closureLayout (code.recapture captured)
  refine ⟨captured, finalHeap, finalStore, finalMap, finalWorld, finalActual, finalEmbedding, copy, ?_,
    represented, finalHeaps, maps, worlds, frame⟩
  rw [code.emitted]
  have base : (fun index : Nat => index) = (· + ([] : Core.Environment).length) := by
    funext index
    simp
  rw [base]
  apply agreement.wrap
  exact .inRight (.pair (.pair (.inLeft .unit) .lambda) .word)

/-- Ordinary source lambda formation over copies of its creation environment
corresponds to the authenticated wrapper. This does not add the separate
runtime stage-call guard to source evaluation. -/
theorem formation_corresponds {model : GenericHeap.PayloadModel catalog}
    {environment : Dynamic.Environment} {actual : Core.Environment} {heap : Dynamic.Heap} {store : Core.Store}
    (layout : FunctionCaptures.Layout catalog mapping world scope environment actual)
    (code : Code catalog program bodyCertificate policy compilation table active function scope layout.administrativeContext)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (requirements : code.node.requirements = []) (coercions : code.node.coercions = []) :
    ∃ captured finalHeap finalStore finalMap finalWorld closureActual embedding,
      Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment
        heap code.id (.closure { function with captured := captured }) finalHeap ∧
      Core.Evaluates actual store (code.lowered.expression.rename layout.embedding)
        (.inRight .word (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
          embedding closureActual code.descriptor.id)) finalStore ∧
      Represents catalog program bodyCertificate table finalMap finalWorld
        (FunctionValues.sourceType function) (.closure { function with captured := captured })
        (value code.artifact.raw.parameterCore code.artifact.raw.resultCore code.artifact.raw.rawBody
          embedding closureActual code.descriptor.id)
        (Core.CallableContract.functionType code.artifact.raw.parameterCore code.artifact.raw.resultCore) ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  obtain ⟨captured, finalHeap, finalStore, finalMap, finalWorld, closureActual, embedding, copy, evaluated,
      represented, heaps, maps, worlds, frame⟩ := formation layout code heaps
  refine ⟨captured, finalHeap, finalStore, finalMap, finalWorld, closureActual, embedding, ?_, evaluated,
    represented, heaps, maps, worlds, frame⟩
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound code.artifact.raw.found)
  · rw [code.artifact.raw.form, requirements, coercions]
    exact .lambda rfl copy
  · rw [coercions]
    exact .nil

end Solcore.SourceSemantics.CoreLowering.ContractedFunctionValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallStageGuard
/-! The executable metadata validator agrees with independent call-stage
judgments. Only this compiler bridge mentions the old validator. The source
rules themselves are in Staging.CallGuard and have no execution-function
premise. Sealed receipts recover the same diagnostic and check precedence. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallStageGuard
open Frontend Frontend.SourceInference
open Staging.CallGuard

abbrev Caller := SourceSpecialization.SpecializedFunction
abbrev RuntimeError := SourceCompilationPlan.Error
abbrev Key := SourceSpecialization.SpecializationKey

def frame (caller : Caller) : Frame := {
  callerReturnComptime := caller.function.returnComptime
  callerResultType := caller.function.inferredBodyType
  stages := fun expression => (caller.stageAnalysis.expressionStage? expression).map SourceStageAnalysis.Stage.toSemantic }

def toFrontend : Staging.Stage → SourceStageAnalysis.Stage
  | .comptime => .comptime
  | .runtime => .runtime
  | .deferred => .deferred

def error (caller : Caller) (node : ExpressionNode) (callee : Key) : Fault → RuntimeError
  | .missingStage expression => .missingExpressionStage caller.key node.id expression
  | .argumentStage index expression actual => .comptimeArgumentStageMismatch caller.key node.id index expression (toFrontend actual)
  | .resultStage actual => .comptimeResultStageMismatch caller.key node.id callee (toFrontend actual)
  | .arity parameters arguments => .argumentArityMismatch parameters arguments

private theorem comptimeOnly (type : TypeSystem.Ty) :
    SourceCompilationPlan.sourceTypeIsComptimeOnly type = true ↔ Staging.ComptimeOnlyType type := by
  exact SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff type

private theorem required_iff (force : Bool) (parameter : TypedBinder) :
    (force || parameter.comptime || SourceCompilationPlan.sourceTypeIsComptimeOnly parameter.scheme.body) = true ↔
      RequiresComptime force parameter := by
  simp only [Bool.or_eq_true, comptimeOnly, RequiresComptime, or_assoc]

private theorem effectful_iff (caller : Caller) :
    (caller.function.returnComptime || SourceCompilationPlan.sourceTypeIsComptimeOnly caller.function.inferredBodyType) = true ↔
      Effectful (frame caller) := by
  simp only [Bool.or_eq_true, comptimeOnly, Effectful, frame]

private theorem stage_found {caller : Caller} {expression : ExpressionId} {stage : Staging.Stage}
    (found : (frame caller).stages expression = some stage) :
    caller.stageAnalysis.expressionStage? expression = some (toFrontend stage) := by
  cases actual : caller.stageAnalysis.expressionStage? expression with
  | none => simp [frame, actual] at found
  | some value =>
    cases value <;> simp [frame, actual, SourceStageAnalysis.Stage.toSemantic] at found <;>
      subst stage <;> rfl

private theorem stage_absent {caller : Caller} {expression : ExpressionId}
    (absent : (frame caller).stages expression = none) : caller.stageAnalysis.expressionStage? expression = none := by
  cases actual : caller.stageAnalysis.expressionStage? expression with
  | none => rfl
  | some value => simp [frame, actual] at absent

private def argumentCheck (caller : Caller) (node : ExpressionNode) (force : Bool)
    (index : Nat) (parameter : TypedBinder) (argument : ExpressionId) : Except RuntimeError Unit :=
  if force || parameter.comptime || SourceCompilationPlan.sourceTypeIsComptimeOnly parameter.scheme.body then
    SourceCompilationPlan.requireComptimeArgumentStage caller node index argument
  else pure ()

private theorem argument_accepts {caller : Caller} {node : ExpressionNode} {force : Bool} {index : Nat}
    {parameter : TypedBinder} {argument : ExpressionId}
    (accepted : ArgumentAccepts (frame caller) force parameter argument) :
    argumentCheck caller node force index parameter argument = .ok () := by
  cases accepted with
  | ordinary notRequired =>
    have skipped : (force || parameter.comptime || SourceCompilationPlan.sourceTypeIsComptimeOnly parameter.scheme.body) ≠ true :=
      fun checked => notRequired ((required_iff force parameter).mp checked)
    simp [argumentCheck, skipped]
  | comptime found =>
    have actual := stage_found found
    simp only [argumentCheck]
    split
    · simp [SourceCompilationPlan.requireComptimeArgumentStage, actual, toFrontend]
    · rfl

private theorem argument_rejects {caller : Caller} {node : ExpressionNode} {callee : Key}
    {force : Bool} {index : Nat} {parameter : TypedBinder} {argument : ExpressionId} {reason : Fault}
    (rejected : ArgumentRejects (frame caller) force index parameter argument reason) :
    argumentCheck caller node force index parameter argument = .error (error caller node callee reason) := by
  cases rejected with
  | missing required absent =>
    have test := (required_iff force parameter).mpr required
    simp [argumentCheck, test, SourceCompilationPlan.requireComptimeArgumentStage, stage_absent absent, error]
    rfl
  | @wrongStage required actual found notComptime =>
    have test := (required_iff force parameter).mpr required
    have selected := stage_found found
    cases actual with
    | comptime => exact False.elim (notComptime rfl)
    | runtime | deferred =>
      simp [argumentCheck, test, SourceCompilationPlan.requireComptimeArgumentStage, selected, error, toFrontend]
      rfl

private theorem arguments_cons (caller : Caller) (node : ExpressionNode) (force : Bool) (index : Nat)
    (parameter : TypedBinder) (parameters : List TypedBinder) (argument : ExpressionId) (arguments : List ExpressionId) :
    SourceCompilationPlan.validateStagedArguments caller node force index (parameter :: parameters) (argument :: arguments) =
      (do
        argumentCheck caller node force index parameter argument
        SourceCompilationPlan.validateStagedArguments caller node force (index + 1) parameters arguments) := by
  rw [SourceCompilationPlan.validateStagedArguments]
  unfold argumentCheck
  split <;> rfl

theorem arguments_accept {caller : Caller} {node : ExpressionNode} {force : Bool} {index : Nat}
    {parameters : List TypedBinder} {arguments : List ExpressionId}
    (accepted : ArgumentsAccept (frame caller) force index parameters arguments) :
    SourceCompilationPlan.validateStagedArguments caller node force index parameters arguments = .ok () := by
  induction accepted with
  | nil => rfl
  | cons head tail ih =>
    rw [arguments_cons, argument_accepts head]
    exact ih

theorem arguments_reject {caller : Caller} {node : ExpressionNode} {callee : Key}
    {force : Bool} {index : Nat} {parameters : List TypedBinder} {arguments : List ExpressionId} {reason : Fault}
    (rejected : ArgumentsReject (frame caller) force index parameters arguments reason) :
    SourceCompilationPlan.validateStagedArguments caller node force index parameters arguments = .error (error caller node callee reason) := by
  induction rejected with
  | parametersRemain => rfl
  | argumentsRemain => rfl
  | head rejected =>
    rw [arguments_cons, argument_rejects (callee := callee) rejected]
    rfl
  | tail accepted rejected ih =>
    rw [arguments_cons, argument_accepts accepted]
    exact ih

private theorem result_accepts {caller : Caller} {node : ExpressionNode} {callee : Key} {staged : Bool}
    (accepted : ResultAccepts (frame caller) node.id staged) :
    (if staged then match caller.stageAnalysis.expressionStage? node.id with
      | none => Except.error (.missingExpressionStage caller.key node.id node.id)
      | some .comptime => .ok ()
      | some actual => .error (.comptimeResultStageMismatch caller.key node.id callee actual)
     else .ok ()) = (Except.ok () : Except RuntimeError Unit) := by
  cases accepted with
  | ordinary runtime => simp [runtime]
  | comptime found => simp [stage_found found, toFrontend]

private theorem result_rejects {caller : Caller} {node : ExpressionNode} {callee : Key} {staged : Bool} {reason : Fault}
    (rejected : ResultRejects (frame caller) node.id staged reason) :
    (if staged then match caller.stageAnalysis.expressionStage? node.id with
      | none => Except.error (.missingExpressionStage caller.key node.id node.id)
      | some .comptime => .ok ()
      | some actual => .error (.comptimeResultStageMismatch caller.key node.id callee actual)
     else .ok ()) = (Except.error (error caller node callee reason) : Except RuntimeError Unit) := by
  cases rejected with
  | missing required absent => simp [required, stage_absent absent, error]
  | @wrongStage required actual found notComptime =>
    have selected := stage_found found
    cases actual with
    | comptime => exact False.elim (notComptime rfl)
    | runtime | deferred => simp [required, selected, error, toFrontend]

/-- Every independent acceptance produces the executable validator's success. -/
theorem accepts {caller : Caller} {node : ExpressionNode} {callee : Key} {contract : Contract}
    {arguments : List ExpressionId} (accepted : Accepts (frame caller) contract node.id arguments) :
    SourceCompilationPlan.validateStagedCallableContract caller node arguments contract.parameters contract.stagedResult callee = .ok () := by
  cases accepted with
  | effectful effectful =>
    simp [SourceCompilationPlan.validateStagedCallableContract, (effectful_iff caller).mpr effectful]
  | ordinary notEffectful argumentsPass resultPass =>
    have test : (caller.function.returnComptime || SourceCompilationPlan.sourceTypeIsComptimeOnly caller.function.inferredBodyType) ≠ true :=
      fun checked => notEffectful ((effectful_iff caller).mp checked)
    simp only [SourceCompilationPlan.validateStagedCallableContract, test, arguments_accept argumentsPass, bind, Except.bind]
    exact result_accepts resultPass

/-- Every independent rejection gives the same first diagnostic. -/
theorem rejects {caller : Caller} {node : ExpressionNode} {callee : Key} {contract : Contract}
    {arguments : List ExpressionId} {reason : Fault} (rejected : Rejects (frame caller) contract node.id arguments reason) :
    SourceCompilationPlan.validateStagedCallableContract caller node arguments contract.parameters contract.stagedResult callee =
      .error (error caller node callee reason) := by
  cases rejected with
  | arguments notEffectful rejected =>
    have test : (caller.function.returnComptime || SourceCompilationPlan.sourceTypeIsComptimeOnly caller.function.inferredBodyType) ≠ true :=
      fun checked => notEffectful ((effectful_iff caller).mp checked)
    simp [SourceCompilationPlan.validateStagedCallableContract, test, arguments_reject (callee := callee) rejected, bind, Except.bind]
  | result notEffectful argumentsPass rejected =>
    have test : (caller.function.returnComptime || SourceCompilationPlan.sourceTypeIsComptimeOnly caller.function.inferredBodyType) ≠ true :=
      fun checked => notEffectful ((effectful_iff caller).mp checked)
    simp only [SourceCompilationPlan.validateStagedCallableContract, test, arguments_accept argumentsPass, bind, Except.bind]
    exact result_rejects rejected

/-- The compiler validator accepts exactly the independent judgment. -/
theorem accepts_iff {caller : Caller} {node : ExpressionNode} {callee : Key} {contract : Contract}
    {arguments : List ExpressionId} :
    SourceCompilationPlan.validateStagedCallableContract caller node arguments contract.parameters contract.stagedResult callee = .ok () ↔
      Accepts (frame caller) contract node.id arguments := by
  constructor
  · intro accepted
    rcases complete (frame caller) contract node.id arguments with yes | ⟨reason, no⟩
    · exact yes
    · have different := rejects (callee := callee) no
      rw [accepted] at different
      cases different
  · exact accepts

/-- Every executable failure is represented by an independent rejection. -/
theorem rejects_iff {caller : Caller} {node : ExpressionNode} {callee : Key} {contract : Contract}
    {arguments : List ExpressionId} {diagnostic : RuntimeError} :
    SourceCompilationPlan.validateStagedCallableContract caller node arguments contract.parameters contract.stagedResult callee = .error diagnostic ↔
      ∃ reason, Rejects (frame caller) contract node.id arguments reason ∧ diagnostic = error caller node callee reason := by
  constructor
  · intro failed
    rcases complete (frame caller) contract node.id arguments with yes | ⟨reason, no⟩
    · have different := accepts (callee := callee) yes
      rw [failed] at different
      cases different
    · exact ⟨reason, no, Except.error.inj (failed.symm.trans (rejects no))⟩
  · rintro ⟨reason, no, rfl⟩
    exact rejects no

/-- The sealed receipt's exact metadata result is interpreted independently. -/
theorem guard_accepts_iff (guard : SourceCoreStageContracts.Guard) :
    guard.decision = .ok () ↔
      Accepts (frame guard.sidecar.caller) ⟨guard.contract.parameters, guard.contract.stagedResult⟩ guard.node.id guard.arguments := by
  rw [← guard.exact]
  exact accepts_iff (caller := guard.sidecar.caller) (node := guard.node) (callee := guard.contract.owner)
    (contract := ⟨guard.contract.parameters, guard.contract.stagedResult⟩) (arguments := guard.arguments)

theorem guard_rejects_iff (guard : SourceCoreStageContracts.Guard) (diagnostic : RuntimeError) :
    guard.decision = .error diagnostic ↔
      ∃ reason, Rejects (frame guard.sidecar.caller) ⟨guard.contract.parameters, guard.contract.stagedResult⟩
        guard.node.id guard.arguments reason ∧ diagnostic = error guard.sidecar.caller guard.node guard.contract.owner reason := by
  rw [← guard.exact]
  exact rejects_iff (caller := guard.sidecar.caller) (node := guard.node) (callee := guard.contract.owner)
    (contract := ⟨guard.contract.parameters, guard.contract.stagedResult⟩) (arguments := guard.arguments)

end Solcore.SourceSemantics.CoreLowering.CallStageGuard
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ContractedFunctionCalls
/-! Ordinary source closure calls beneath accepted callable-contract gates.
The generated argument-cell prefix and complete body composition preserve the
generic heap. Callee/argument Core evaluations in the gate-prefix theorem are
explicit compositional premises, not fields of code authentication. Rejected
runtime stage gates are intentionally not claimed to be existing Dynamic faults. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ContractedFunctionCalls
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open FunctionArguments FunctionCallBody FunctionCalls

private theorem parameters_scope {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope finalScope : SourceCoreLocalCell.Scope} {parameters : List TypedBinder}
    {lowered : List (TypedBinder × Ty)}
    (tree : FunctionCode.Parameters policy source scope parameters lowered finalScope) :
    lowered.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope = finalScope := by
  induction tree with
  | nil => rfl
  | cons _ _ ih => exact ih

variable {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
  {program : Program} {function : Dynamic.Closure} {bodyCertificate : FunctionCode.BodyCertificate}
  {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
  {table : SourceCoreStageCodebook.Table} {active : TypeSystem.Substitution}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {actual : Environment} {faults : FunctionCalls.FaultRep}

/-- Contract wrappers do not change the copies of the captures or the closure
parameter allocation. All source metadata and mapped lexical references are
constructed by the real prefix. -/
structure Entry
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    (before : Dynamic.Heap) (initialStore : Store) (context : SourceSemantics.Context)
    (arguments : List Dynamic.Value) (values : List Value) where
  entry : Dynamic.Environment
  copied : Dynamic.Heap
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  bodyEnvironment : Environment
  store : Store
  finalMap : LocationMap
  finalWorld : StoreTyping
  embedding : Renaming
  copy : Dynamic.EnvironmentCopies function.source function.captured before entry copied
  allocation : Dynamic.BindersAllocate entry copied function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents catalog finalMap finalWorld layout.administrativeContext
    code.artifact.raw.bodyScope environment canonical
  heaps : GenericHeap.HeapRepresents model finalMap finalWorld heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends mapping finalMap
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping initialStore finalMap store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical bodyEnvironment
  agreement : ContinuationAgreement (DataPatternValues.packValues values :: actual) initialStore
    (code.artifact.raw.rawBody.rename layout.embedding.lift) bodyEnvironment store
      (code.artifact.raw.bodyCode.rename embedding)

theorem entry_exists
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    {before : Dynamic.Heap} {store : Store} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {arguments : List Dynamic.Value} {values : List Value}
    (extension : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (represented : Arguments model mapping world code.artifact.raw.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured) :
    Nonempty (Entry (model := model) layout code before store context arguments values) := by
  obtain ⟨entry, copied, copiedCanonical, copiedActual, copiedStore, copiedMap, copiedWorld, copiedEmbedding,
      copy, copiedEnvironments, copiedHeaps, copiedMaps, copiedWorlds, copiedFrame, copiedLookups, copies⟩ :=
    CaptureCopies.copies_prefix (pre := [DataPatternValues.packValues values])
      (body := SourceCoreFunctions.bindParameters code.artifact.raw.loweredParameters code.artifact.raw.resultCore
        (code.artifact.raw.bodyCode.weakenAt code.artifact.raw.loweredParameters.length))
      layout.represented heaps
      (EnvironmentsAgree.lift (mapping := layout.embedding) layout.lookups (DataPatternValues.packValues values))
  obtain ⟨environment, heap, canonical, bodyEnvironment, finalStore, finalMap, finalWorld, embedding,
      allocation, environments, finalHeaps, maps, worlds, frame, lookups, agreement⟩ :=
    parameters_prefix (represented.extend copiedMaps copiedWorlds) (body := code.artifact.raw.bodyCode)
      (outputType := code.artifact.raw.resultCore) copiedEnvironments copiedHeaps copiedLookups
  rw [code.artifact.raw.parametersTree.binders] at allocation
  rw [parameters_scope code.artifact.raw.parametersTree] at environments
  have mono := mono_binders extension
  exact ⟨⟨entry, copied, environment, heap, canonical, bodyEnvironment, finalStore, finalMap, finalWorld, embedding,
    copy, allocation, environments, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 (copy.agrees locals) allocation,
    copiedMaps.trans maps, copiedWorlds.trans worlds, copiedFrame.trans frame,
    copy.metadata_extends.trans (GenericLexicalContext.binders_metadata allocation), lookups,
    copies.trans agreement⟩⟩

theorem preserves
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    (bodyMeaning : BodyPreserves model program function bodyCertificate faults)
    {before after : Dynamic.Heap} {store : Store} {arguments : List Dynamic.Value} {values : List Value}
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment} {outcome : Dynamic.ExpressionOutcome}
    (represented : Arguments model mapping world code.artifact.raw.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (execution : Outcome program context caller function.evidence before (.closure function) arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues values :: actual) store
        (code.artifact.raw.rawBody.rename layout.embedding.lift) value finalStore ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.raw.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have arity : function.parameters.length = arguments.length := by
    rw [← code.artifact.raw.parametersTree.binders, List.length_map]
    exact represented.length.1
  obtain ⟨types, callContext, entryEnvironment, copied, environment, bound, extension, copy, allocated, trace⟩ :=
    execution.trace arity
  obtain ⟨entry⟩ := entry_exists layout code extension represented heaps locals
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy entry.copy
  obtain ⟨rfl, rfl⟩ := allocations_same allocated entry.allocation
  obtain ⟨_, _, typed, _⟩ := frame_body_at code.frame extension
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
    bodyMeaning code.artifact.raw.bodyTree typed entry.environments entry.heaps entry.locals entry.lookups trace
  exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, result, finalHeaps,
    entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata⟩

theorem reflects
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    (bodyMeaning : BodyReflects model program function bodyCertificate faults)
    {before : Dynamic.Heap} {store finalStore : Store} {arguments : List Dynamic.Value} {values : List Value}
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment) {value : Value}
    (represented : Arguments model mapping world code.artifact.raw.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (evaluated : Evaluates (DataPatternValues.packValues values :: actual) store
      (code.artifact.raw.rawBody.rename layout.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Outcome program context caller function.evidence before (.closure function) arguments outcome after ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.raw.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨types, callContext, _, _, extension, typed, _⟩ := frame_body code.frame
  obtain ⟨entry⟩ := entry_exists layout code extension represented heaps locals
  obtain ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
    bodyMeaning code.artifact.raw.bodyTree typed entry.environments entry.heaps entry.locals entry.lookups
      (entry.agreement.unwrap evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace.call code.frame extension entry.copy entry.allocation,
    result, finalHeaps, entry.maps.trans maps, entry.worlds.trans worlds,
    entry.frame.trans frame, entry.metadata.trans metadata⟩

/-- Once both actual gate decisions accept, the call prefix enters precisely
the real closure body. Callee and argument effects occur once and in order;
reflection recovers the same body evaluation from any completed whole call. -/
theorem accepted_call_agreement {environment captured : Environment} {before middle applied : Store}
    {parameter result : Ty} {callee arguments body : Expr} {identity argument : Value} {contract : Word}
    (gates : List CallableContract.Gate) (unknown : Word)
    (calleeEvaluation : Evaluates environment before callee
      (.inRight .word (.pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured))
        (.word contract))) middle)
    (stageAccepted : CallableContract.decision gates .beforeArguments unknown contract = none)
    (argumentsEvaluation : Evaluates (.unit ::
      .pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured)) (.word contract) :: environment)
      middle ((arguments.weakenAt 0).weakenAt 0) (.inRight .word argument) applied)
    (arityAccepted : CallableContract.decision gates .beforeApplication unknown contract = none) :
    ContinuationAgreement environment before (CallableContract.call gates unknown result callee arguments)
      (argument :: captured) applied body := by
  constructor
  · intro value finalStore evaluated
    exact CallableContract.call_success gates unknown calleeEvaluation stageAccepted argumentsEvaluation arityAccepted evaluated
  · intro value finalStore evaluated
    obtain ⟨_, sized⟩ := evaluation_has_size evaluated
    obtain ⟨_, _, afterCallee⟩ := sized.bind_success calleeEvaluation
    have beforeArguments := CallableContract.dispatch_evaluates gates .beforeArguments unknown contract
      (show Evaluates (.pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured))
        (.word contract) :: environment) middle (.second (.var 0)) (.word contract) middle from .second (.var rfl))
    rw [stageAccepted] at beforeArguments
    obtain ⟨_, _, afterGuard⟩ := afterCallee.bind_success beforeArguments
    obtain ⟨_, _, afterArguments⟩ := afterGuard.bind_success argumentsEvaluation
    have beforeApplication := CallableContract.dispatch_evaluates gates .beforeApplication unknown contract
      (show Evaluates (argument :: .unit :: .pair (.pair identity
        (.closure parameter (LanguageResult.resultType result) body captured)) (.word contract) :: environment)
        applied (.second (.var 2)) (.word contract) applied from .second (.var rfl))
    rw [arityAccepted] at beforeApplication
    obtain ⟨_, _, application⟩ := afterArguments.bind_success beforeApplication
    obtain ⟨_, _, bodyEvaluation⟩ := application.apply_body
      (show Evaluates (.unit :: argument :: .unit :: .pair (.pair identity
        (.closure parameter (LanguageResult.resultType result) body captured)) (.word contract) :: environment)
        applied (.second (.first (.var 3))) (.closure parameter (LanguageResult.resultType result) body captured) applied
        from .second (.first (.var rfl))) (.var rfl)
    exact bodyEvaluation.sound

end Solcore.SourceSemantics.CoreLowering.ContractedFunctionCalls
end
