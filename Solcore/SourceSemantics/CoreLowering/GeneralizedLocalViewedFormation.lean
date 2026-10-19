import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation

/-! Native typing for the materialized wrapper follows from its accepted
emission and actual read execution in the unchanged store. The resulting
positive association is the one used by mixed public function values. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {material : Materialization compiled mapping world function}

theorem View.formation (view : View material) {store : Store}
    (read : Evaluates view.environment store (view.original.expression.rename view.embedding)
      (.inRight .word (CallableIndexedLambdaValues.value material.code material.captured.embedding
        material.origin.native material.actual)) store)
    (snapshot : store.read? view.location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.callerNative)) :
    Evaluates view.environment store (view.lowered.expression.rename view.embedding)
      (.inRight .word view.native) store := by
  rw [view.emitted]
  exact GeneralizedLocalReadView.formation read view.reference snapshot

theorem View.runtime_hasType (view : View material) {context : Core.Context}
    (environments : RuntimeEnvironmentHasTypes world view.environment context compiled.indexed.layouts.definitions) :
    RuntimeValueHasType world view.native
      (CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore)
      compiled.indexed.layouts.definitions := by
  have raw := material.rawTyped
  rw [material.native_type] at raw
  exact GeneralizedLocalReadView.runtime_hasType (CallableIndexedAmbient.frame_registered compiled.indexed)
    raw environments view.reference

theorem View.represents (view : View material) {store : Store} {context : Core.Context}
    (read : Evaluates view.environment store (view.original.expression.rename view.embedding)
      (.inRight .word (CallableIndexedLambdaValues.value material.code material.captured.embedding
        material.origin.native material.actual)) store)
    (snapshot : store.read? view.location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.callerNative))
    (typed : HasType context (view.lowered.expression.rename view.embedding)
      (LanguageResult.resultType (CallableContract.functionType material.code.receipt.parameterCore
        material.code.receipt.resultCore)) compiled.indexed.layouts.definitions)
    (environments : RuntimeEnvironmentHasTypes world view.environment context compiled.indexed.layouts.definitions)
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    Nonempty (Association compiled mapping world function view.native material.code.receipt.loweredParameters
      material.code.receipt.parameterCore material.code.receipt.resultCore) := by
  have evaluated := view.formation read snapshot
  obtain ⟨future, _, finalStored, outputTyped⟩ := evaluation_preserves_type evaluated typed environments stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  cases outputTyped with
  | inRight typed => exact ⟨.viewed material view typed⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
