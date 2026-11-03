import Solcore.SourceSemantics.CoreLowering.FunctionArguments
import Solcore.SourceSemantics.CoreLowering.CaptureCopyRenaming

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
