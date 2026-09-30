import Solcore.SourceSemantics.CoreLowering.ForHeaderConstruction
import Solcore.SourceSemantics.CoreLowering.ScalarAssignmentReflection

/-! A supplied independent successful header derivation reaches a related
static continuation. Exact source context, environment and heap are retained,
so a later loop proof may use the supplied source trace without assuming that
it coincides with a separately constructed trace. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements CoreProof
open LoopStatements Reflection

def SuccessResult (continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop)
    (administrativeContext : Core.Context) (finalContext : Context) (finalEnvironment : Dynamic.Environment)
    (after : Dynamic.Heap) (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (actual : Core.Environment) (store : Core.Store) (code : Core.Expr) : Prop :=
  ∃ tail : TailState administrativeContext continuation,
    tail.context = finalContext ∧ tail.environment = finalEnvironment ∧ tail.heap = after ∧
    GeneralHeap.LocationMap.Extends mapping tail.mapping ∧ Core.WorldExtends world tail.world ∧
    GeneralHeap.AdministrativePreserved mapping store tail.mapping tail.store ∧
    ContinuationAgreement actual store code tail.actual tail.store (tail.code.rename tail.embedding)

theorem SuccessResult.prepend
    {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    {administrativeContext : Core.Context} {finalContext : Context} {finalEnvironment : Dynamic.Environment}
    {after : Dynamic.Heap} {mapping middleMap : GeneralHeap.LocationMap} {world middleWorld : Core.StoreTyping}
    {actual middleActual : Core.Environment} {store middleStore : Core.Store} {code middleCode : Core.Expr}
    (maps : GeneralHeap.LocationMap.Extends mapping middleMap) (worlds : Core.WorldExtends world middleWorld)
    (frame : GeneralHeap.AdministrativePreserved mapping store middleMap middleStore)
    (agreement : ContinuationAgreement actual store code middleActual middleStore middleCode)
    (tail : SuccessResult continuation administrativeContext finalContext finalEnvironment after
      middleMap middleWorld middleActual middleStore middleCode) :
    SuccessResult continuation administrativeContext finalContext finalEnvironment after mapping world actual store code := by
  obtain ⟨tail, contextEq, environmentEq, heapEq, moreMaps, moreWorlds, moreFrame, moreAgreement⟩ := tail
  exact ⟨tail, contextEq, environmentEq, heapEq, maps.trans moreMaps, worlds.trans moreWorlds,
    frame.trans moreFrame, agreement.trans moreAgreement⟩

private theorem expression_success
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap after : Dynamic.Heap} {store : Core.Store} {value : Dynamic.Value}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ)
    (executed : Dynamic.ExpressionEvaluates program context evidence source environment heap id value after) :
    after = heap ∧ ∃ staged : SourceStagedValue.Value,
      value = StagedValue.toSource staged ∧ SourceStagedValue.coreType staged = type ∧
      Core.Evaluates actual store (code.rename ξ) (.inRight .word (SourceStagedValue.toCore staged)) store := by
  obtain ⟨rfl, staged, same, typed, evaluated⟩ :=
    ScalarExpressionReflection.Primitive.source_success tree unique environments heaps executed
  exact ⟨rfl, staged, same, typed, (GeneralExpressions.Primitive.readOnly tree).evaluation_rename evaluated layout.agrees⟩

theorem Tree.source_success
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {resultType : Core.Ty} {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {code : Core.Expr}
    (tree : Tree compilation source reasonAt resultType continuation scope context items code)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap after : Dynamic.Heap} {store : Core.Store} {finalContext : Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ)
    (executed : Dynamic.ForItemsExecute program context evidence source environment heap items finalContext finalEnvironment after) :
    SuccessResult continuation administrativeContext finalContext finalEnvironment after mapping world actual store (code.rename ξ) := by
  induction tree generalizing mapping world administrativeContext environment finalEnvironment canonical actual actualContext ξ heap after store finalContext with
  | nil next =>
    cases executed
    exact ⟨{
      scope := _, context := _, environment := environment, heap := heap, mapping := mapping,
      world := world, canonical := canonical, actual := actual, actualContext := actualContext,
      embedding := ξ, store := store, code := _, certificate := next,
      environments := environments, heaps := heaps, layout := layout },
      rfl, rfl, rfl, .refl _, .refl _, .refl _ _, .refl _ _ _⟩
  | @letUninitialized scope context middleContext binder rest payload body binding extension tail ih =>
    cases executed with
    | cons head remaining =>
      cases head with
      | letUninitialized _ otherExtension allocated =>
        have sameContext := Dynamic.BinderExtends.functional otherExtension extension
        subst_vars
        obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
        have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
        have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
          rw [← heaps.runtime_hasTypes.length_eq]; simp
        have nextLayout := (layout.extend worlds).bind (Core.RuntimeValueHasType.cellRef found)
        apply SuccessResult.prepend (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩) worlds
          (GeneralHeap.AdministrativePreserved.allocate mapping store (.inLeft payload .unit))
          (tail := ih nextEnvironments nextHeaps nextLayout remaining)
        rw [Core.LoopRenaming.letUninitialized]
        simpa only [Core.LocalSequence.letUninitialized, Core.Store.allocate] using
          (ContinuationAgreement.letE (body := body.rename ξ.lift) (Core.OptionalCell.allocate_evaluates payload actual store))
  | @letInitialized scope context middleContext binder rest payload initializer initializerCode body depth binding extension valueTree tail ih =>
    cases executed with
    | cons head remaining =>
      cases head with
      | letInitialized sourceEval _ otherExtension allocated =>
        have sameContext := Dynamic.BinderExtends.functional otherExtension extension
        subst_vars
        obtain ⟨rfl, staged, rfl, typed, coreEval⟩ := expression_success valueTree unique environments heaps layout sourceEval
        have sameSource : binder.scheme.body = SourceStagedValue.sourceType staged := binding.types.source_unique (typed ▸ stagedTypes staged)
        have cell : CellRepresents {type := binder.scheme.body, value := some (StagedValue.toSource staged)}
            (.inRight .unit (SourceStagedValue.toCore staged)) payload := by
          rw [sameSource, ← typed]; exact .initialized staged
        obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
        have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
        have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
          rw [← heaps.runtime_hasTypes.length_eq]; simp
        have nextLayout := ((layout.extend worlds).insert (stagedTyped staged _)).bind (Core.RuntimeValueHasType.cellRef found)
        have restResult := ih nextEnvironments nextHeaps nextLayout remaining
        simp only [rename_insert_lift] at restResult
        apply SuccessResult.prepend (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩) worlds
          (GeneralHeap.AdministrativePreserved.allocate mapping store (.inRight .unit (SourceStagedValue.toCore staged)))
          (tail := restResult)
        simp only [Core.LoopRenaming.letInitialized]
        exact (ContinuationAgreement.bind coreEval).trans
          (ContinuationAgreement.letE (Core.OptionalCell.allocateInitialized_evaluates (.var rfl)))
      | letInitializedGeneralized _ polymorphic _ _ => exact False.elim (polymorphic binding.monomorphic)
  | @discard scope context expression expressionType expressionCode rest body depth valueTree tail ih =>
    cases executed with
    | cons head remaining =>
      cases head with
      | expression sourceEval =>
        obtain ⟨rfl, staged, _, _, coreEval⟩ := expression_success valueTree unique environments heaps layout sourceEval
        have restResult := ih environments heaps (layout.insert (stagedTyped staged world)) remaining
        simp only [rename_insert] at restResult
        apply SuccessResult.prepend (.refl _) (.refl _) (.refl _ _) (tail := restResult)
        rw [Core.LoopRenaming.discard]
        simpa only [Core.LocalSequence.discard] using
          (ContinuationAgreement.bind (type := Core.LocalLoop.controlType resultType)
            (body := (body.rename ξ).weakenAt 0) coreEval)
  | @assign scope context assignment index payload rhs rhsCode rest body depth target valueTree tail ih =>
    cases executed with
    | cons head remaining =>
      cases head with
      | assignValue assigned =>
        obtain ⟨staged, location, writtenStore, _, typed, rhsCore, lookup, ⟨old, readable⟩, written,
          updatedHeaps, writeFrame⟩ := ScalarAssignmentReflection.source_success valueTree unique target.slot target.bare environments heaps assigned
        have actualLookup := layout.agrees lookup
        have referenceTyped : Core.RuntimeValueHasType world
            (.cellRef (Core.OptionalCell.cellType payload) location) (Core.OptionalCell.referenceType payload) := by
          obtain ⟨found, foundEq, foundTyped⟩ := Core.RuntimeEnvironmentHasTypes.lookup layout.typed
            (layout.respects (SourceCoreLocalCell.lookup?_context target.slot))
          rw [actualLookup] at foundEq
          cases foundEq
          exact foundTyped
        have nextLayout := ((layout.insert referenceTyped).insert (stagedTyped staged world)).insert Core.RuntimeValueHasType.unit
        have restResult := ih environments updatedHeaps nextLayout remaining
        simp only [rename_insert] at restResult
        have coreEval := (GeneralExpressions.Primitive.readOnly valueTree).evaluation_rename rhsCore layout.agrees
        apply SuccessResult.prepend (.refl _) (.refl _) writeFrame (tail := restResult)
        simp only [Core.LoopRenaming.assign]
        refine (ContinuationAgreement.letE (Core.Evaluates.var actualLookup)).trans ?_
        refine (ContinuationAgreement.bind
          (((GeneralExpressions.Primitive.readOnly valueTree).rename ξ).evaluation_weakenAt_zero coreEval _)).trans ?_
        exact ContinuationAgreement.letE (.storeCell (.var rfl) readable (.inRight (.var rfl)) written)

end Solcore.SourceSemantics.CoreLowering.ForHeaders
