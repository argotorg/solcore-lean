import Solcore.SourceSemantics.CoreLowering.ForHeaderMeaning

/-! A certified finite default header constructs its independent source
prefix execution or specified fault. Successful prefixes retain a two-way
agreement around the unevaluated static continuation, including exact lexical
binder insertion and mapped source/Core allocations and writes. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements CoreProof
open LoopStatements Reflection

private theorem valid_extend
    {compilation : SourceCorePrimitive.Context} {owner : Resolved.DeclarationId}
    {context middle : Context} {binder : TypedBinder}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (extension : BinderExtends owner context binder middle) :
    PrimitiveExpressions.ContextValid compilation middle := by
  cases extension
  exact ⟨valid.ledger, valid.valid.transport rfl rfl rfl⟩

private theorem cellsWrite_set {cells : List Dynamic.Cell} {index : Nat}
    {previous : Dynamic.Cell} (selected : Dynamic.Heap.CellAt cells index previous)
    (replacement : Dynamic.Cell) :
    Dynamic.Heap.CellsWrite cells index replacement (cells.set index replacement) := by
  induction selected with
  | head => exact .head
  | tail _ ih => exact .tail ih

/-- Basic expression RHS evaluation leaves its heap unchanged. The captured
source location and independently mapped Core location identify the same cell. -/
private theorem equal_assignment
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap : Dynamic.Heap} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    {target : PlaceResolution} {rhs : ExpressionId} {index : Nat} {payloadType : Core.Ty}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (slot : SourceCoreLocalCell.lookup? scope target.root = some (index, payloadType))
    (bare : target.projections = []) (value : SourceStagedValue.Value)
    (valueType : SourceStagedValue.coreType value = payloadType)
    (rhsEvaluated : Dynamic.ExpressionEvaluates program context evidence source environment
      heap rhs (StagedValue.toSource value) heap) :
    ∃ (coreLocation : Core.Location) (after : Dynamic.Heap) (finalStore : Core.Store),
      Dynamic.SourcePlaceAssignment program context evidence source
        (Dynamic.AssignmentValueApplies .equal) environment heap target rhs (StagedValue.toSource value) after ∧
      coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation) ∧
      (∃ oldValue, store.read? coreLocation = some oldValue) ∧
      store.write? coreLocation (.inRight .unit (SourceStagedValue.toCore value)) = some finalStore ∧
      GeneralHeap.HeapRepresents mapping world after finalStore ∧
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store mapping finalStore := by
  obtain ⟨location, coreLocation, cell, stored, lookup, coreLookup, reference, read, coreRead, represented⟩ :=
    environments.lookup_heap heaps slot
  let replacement : Dynamic.Cell := { cell with value := some (StagedValue.toSource value) }
  let after : Dynamic.Heap := ⟨heap.cells.set location.index replacement⟩
  have sourceWrite : Dynamic.Heap.Writes heap location (some (StagedValue.toSource value)) after := by
    cases read with
    | intro selected => exact .intro (.intro selected) (cellsWrite_set selected replacement)
  obtain ⟨finalStore, written, heapRelated⟩ := heaps.write_initialized reference value valueType sourceWrite
  let captured : Dynamic.ResolvedPlace := {
    location, rootType := cell.type, valueType := target.type, projections := [], selected := cell.value
  }
  have resolved : Dynamic.SourcePlaceResolves program context evidence source environment heap target captured heap := by
    apply Dynamic.SourcePlaceResolves.intro lookup read
    · rw [bare]; exact .nil
    · exact read
    · exact represented.rootInitialValue
    · exact .nil
  exact ⟨coreLocation, after, finalStore,
    .intro resolved rhsEvaluated
      (.intro read rfl represented.rootInitialValue (.leaf (.equal cell.value (StagedValue.toSource value))) sourceWrite),
    coreLookup, ⟨stored, coreRead⟩, written, heapRelated, environments,
    GeneralHeap.AdministrativePreserved.write (List.mem_of_getElem? reference.mapped) written⟩



theorem Tree.construct
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {resultType : Core.Ty} {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {code : Core.Expr}
    (tree : Tree compilation source reasonAt resultType continuation scope context items code)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store : Core.Store}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ) :
    Result program context evidence source reasonAt resultType continuation administrativeContext
      environment heap items mapping world actual store (code.rename ξ) := by
  induction tree generalizing mapping world administrativeContext environment canonical actual actualContext ξ heap store with
  | nil next =>
    exact .continues {
      scope := _, context := _, environment := environment, heap := heap, mapping := mapping,
      world := world, canonical := canonical, actual := actual, actualContext := actualContext,
      embedding := ξ, store := store, code := _, certificate := next,
      environments := environments, heaps := heaps, layout := layout }
      .nil (.refl _ _) (.refl _) (.refl _) (.refl _ _) (.refl _ _ _)
  | @letUninitialized scope context middleContext binder rest payload body binding extension tail ih =>
    have allocated : Dynamic.Heap.Allocates heap binder.scheme.body none
        ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩ := .append
    obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
    have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
    have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
      rw [← heaps.runtime_hasTypes.length_eq]; simp
    have nextLayout := (layout.extend worlds).bind (Core.RuntimeValueHasType.cellRef found)
    apply Result.prepend (.letUninitialized binding.monomorphic extension allocated) (.binder extension)
      (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩) worlds
      (GeneralHeap.AdministrativePreserved.allocate mapping store (.inLeft payload .unit))
      (tail := ih (valid_extend valid extension) nextEnvironments nextHeaps nextLayout)
    rw [Core.LoopRenaming.letUninitialized]
    simpa only [Core.LocalSequence.letUninitialized, Core.Store.allocate] using
      (ContinuationAgreement.letE (body := body.rename ξ.lift) (Core.OptionalCell.allocate_evaluates payload actual store))
  | @letInitialized scope context middleContext binder rest payload initializer initializerCode body depth binding extension valueTree tail ih =>
    obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
    cases related with
    | value staged typed =>
      cases sourceEval with
      | value sourceEval =>
        have allocated : Dynamic.Heap.Allocates heap binder.scheme.body (some (StagedValue.toSource staged))
            ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := some (StagedValue.toSource staged) }]⟩ := .append
        have sameSource : binder.scheme.body = SourceStagedValue.sourceType staged := binding.types.source_unique (typed ▸ stagedTypes staged)
        have cell : CellRepresents {type := binder.scheme.body, value := some (StagedValue.toSource staged)}
            (.inRight .unit (SourceStagedValue.toCore staged)) payload := by
          rw [sameSource, ← typed]; exact .initialized staged
        obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
        have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
        have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
          rw [← heaps.runtime_hasTypes.length_eq]; simp
        have nextLayout := ((layout.extend worlds).insert (stagedTyped staged _)).bind (Core.RuntimeValueHasType.cellRef found)
        have restResult := ih (valid_extend valid extension) nextEnvironments nextHeaps nextLayout
        simp only [rename_insert_lift] at restResult
        apply Result.prepend (.letInitialized sourceEval binding.monomorphic extension allocated) (.binder extension)
          (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩) worlds
          (GeneralHeap.AdministrativePreserved.allocate mapping store (.inRight .unit (SourceStagedValue.toCore staged)))
          (tail := restResult)
        simp only [Core.LoopRenaming.letInitialized]
        exact (ContinuationAgreement.bind coreEval).trans
          (ContinuationAgreement.letE (Core.OptionalCell.allocateInitialized_evaluates (.var rfl)))
    | uninitialized site location origin =>
      cases sourceEval with
      | fault sourceFault =>
        apply Result.fault (.head (.letInitializer binding.monomorphic sourceFault))
          (.uninitialized site location origin) heaps (.refl _) (.refl _) (.refl _ _)
        simpa only [Core.LoopRenaming.letInitialized] using
          Core.LocalSequence.letInitialized_failure (Core.LocalLoop.controlType resultType) payload coreEval
  | @discard scope context expression expressionType expressionCode rest body depth valueTree tail ih =>
    obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
    cases related with
    | value staged typed =>
      cases sourceEval with
      | value sourceEval =>
        have restResult := ih valid environments heaps (layout.insert (stagedTyped staged world))
        simp only [rename_insert] at restResult
        apply Result.prepend (.expression sourceEval) (.refl _ _) (.refl _) (.refl _) (.refl _ _) (tail := restResult)
        rw [Core.LoopRenaming.discard]
        simpa only [Core.LocalSequence.discard] using
          (ContinuationAgreement.bind (type := Core.LocalLoop.controlType resultType)
            (body := (body.rename ξ).weakenAt 0) coreEval)
    | uninitialized site location origin =>
      cases sourceEval with
      | fault sourceFault =>
        apply Result.fault (.head (.expression sourceFault)) (.uninitialized site location origin) heaps (.refl _) (.refl _) (.refl _ _)
        simpa only [Core.LoopRenaming.discard] using
          Core.LocalSequence.discard_failure (Core.LocalLoop.controlType resultType) coreEval
  | @assign scope context assignment index payload rhs rhsCode rest body depth target valueTree tail ih =>
    obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
    cases related with
    | value staged typed =>
      cases sourceEval with
      | value sourceEval =>
        obtain ⟨location, afterWrite, writtenStore, assigned, lookup, ⟨old, readable⟩, written,
          updatedHeaps, updatedEnvironments, writeFrame⟩ := equal_assignment environments heaps target.slot target.bare staged typed sourceEval
        have actualLookup := layout.agrees lookup
        have referenceTyped : Core.RuntimeValueHasType world
            (.cellRef (Core.OptionalCell.cellType payload) location) (Core.OptionalCell.referenceType payload) := by
          obtain ⟨found, foundEq, foundTyped⟩ := Core.RuntimeEnvironmentHasTypes.lookup layout.typed
            (layout.respects (SourceCoreLocalCell.lookup?_context target.slot))
          rw [actualLookup] at foundEq
          cases foundEq
          exact foundTyped
        have nextLayout := ((layout.insert referenceTyped).insert (stagedTyped staged world)).insert Core.RuntimeValueHasType.unit
        have restResult := ih valid updatedEnvironments updatedHeaps nextLayout
        simp only [rename_insert] at restResult
        apply Result.prepend (.assignValue assigned) (.refl _ _) (.refl _) (.refl _) writeFrame (tail := restResult)
        simp only [Core.LoopRenaming.assign]
        refine (ContinuationAgreement.letE (Core.Evaluates.var actualLookup)).trans ?_
        refine (ContinuationAgreement.bind
          (((GeneralExpressions.Primitive.readOnly valueTree).rename ξ).evaluation_weakenAt_zero coreEval _)).trans ?_
        exact ContinuationAgreement.letE (.storeCell (.var rfl) readable (.inRight (.var rfl)) written)
    | uninitialized site location origin =>
      cases sourceEval with
      | fault sourceFault =>
        obtain ⟨sourceLocation, coreLocation, cell, stored, lookup, coreLookup, reference, read, coreRead, represented⟩ :=
          environments.lookup_heap heaps target.slot
        let captured : Dynamic.ResolvedPlace := {
          location := sourceLocation, rootType := cell.type, valueType := assignment.target.type,
          projections := [], selected := cell.value
        }
        have resolved : Dynamic.SourcePlaceResolves program context evidence source environment heap assignment.target captured heap := by
          apply Dynamic.SourcePlaceResolves.intro lookup read
          · rw [target.bare]; exact .nil
          · exact read
          · exact represented.rootInitialValue
          · exact .nil
        apply Result.fault (.head (.assignValue (.rhs resolved sourceFault))) (.uninitialized site location origin)
          heaps (.refl _) (.refl _) (.refl _ _)
        simpa only [Core.LoopRenaming.assign, Core.Expr.rename] using
          Core.LocalSequence.assign_failure (Core.LocalLoop.controlType resultType)
            (Core.Evaluates.var (layout.agrees coreLookup))
            (((GeneralExpressions.Primitive.readOnly valueTree).rename ξ).evaluation_weakenAt_zero coreEval _)

end Solcore.SourceSemantics.CoreLowering.ForHeaders
