import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization

/-! The outer read wrapper and inner lexical wrapper compose around the same
real frame cell. A completed body retains all other writes and allocations,
while both successful and failed calls restore the current caller's frame. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues
open GeneralizedLocalAcceptedMaterialization

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {viewRelation : TypedSource → TypedSource → Prop}
  {material : Materialization compiled mapping world function viewRelation}

def View.transient (view : View material) : NativeFrame :=
  SourceCoreCallableIndexedDispatch.readFrame view.id material.code.descriptor.id view.callerNative

def View.selected (view : View material) : NativeFrame :=
  SourceCoreCallableIndexedDispatch.selectedFrame compiled.indexed.ancestry.graph.table
    material.code.descriptor.id material.origin.native view.transient

def View.bodyEnvironment (view : View material) (argument : Value) : Environment :=
  .unit :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.transient :: argument ::
    SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual

def View.entry (view : View material) (argument : Value) : Environment :=
  argument :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.callerNative ::
    CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual :: view.environment

def View.body (view : View material) : Expr :=
  (SourceCoreCallableIndexedAncestry.viewBody compiled.indexed.ancestry.layout.frame view.id material.code.descriptor.id
    view.referenceIndex).rename view.embedding.lift.lift.lift

theorem View.agreement (view : View material) {argument saved : Value} {store : Store}
    (current : store.read? view.location = some saved) :
    let selected := SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.selected
    (∀ {output finalStore},
      Evaluates (view.bodyEnvironment argument) (store.set view.location selected)
        (material.code.receipt.rawBody.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding material.captured.embedding))
        output finalStore →
      Evaluates (view.entry argument) store view.body output (finalStore.set view.location saved)) ∧
    (∀ {output finalStore}, Evaluates (view.entry argument) store view.body output finalStore →
      ∃ bodyStore,
        Evaluates (view.bodyEnvironment argument) (store.set view.location selected)
          (material.code.receipt.rawBody.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding material.captured.embedding))
          output bodyStore ∧ finalStore = bodyStore.set view.location saved) := by
  let transient := SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.transient
  have bound : view.location < store.length := (List.getElem?_eq_some_iff.mp current).choose
  have installed : Store.read? (store.set view.location transient) view.location = some transient :=
    Store.write?_reads_written (Store.write?_eq_some_iff.mpr ⟨bound, rfl⟩)
  have inner := GeneralizedLocalCallFrame.agreement material.origin material.captured material.code
    view.carried view.recipe view.lexicalReference installed (argument := argument)
  have outer := GeneralizedLocalReadView.agreement view.reference current
    (parameter := material.code.receipt.parameterCore) (result := material.code.receipt.resultCore)
    (id := view.id) (target := material.code.descriptor.id) (caller := view.callerNative)
    (identity := .inLeft .word .unit)
    (innerBody := material.code.body.rename material.captured.embedding.lift.lift)
    (innerEnvironment := SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual)
    (argument := argument)
  constructor
  · intro output finalStore evaluated
    have bodyEvaluation := inner.1 (by simpa only [List.set_set, View.bodyEnvironment, View.selected, View.transient, View.entry, View.body, CallableIndexedLambdaValues.value] using evaluated)
    simpa only [List.set_set, View.bodyEnvironment, View.selected, View.transient, View.entry, View.body, CallableIndexedLambdaValues.value] using outer.1 bodyEvaluation
  · intro output finalStore evaluated
    obtain ⟨innerStore, innerEvaluation, outerEq⟩ := outer.2 evaluated
    obtain ⟨bodyStore, bodyEvaluation, innerEq⟩ := inner.2 innerEvaluation
    refine ⟨bodyStore, ?_, ?_⟩
    · simpa only [List.set_set, View.bodyEnvironment, View.selected, View.transient, View.entry, View.body, CallableIndexedLambdaValues.value] using bodyEvaluation
    · simpa only [innerEq, List.set_set] using outerEq

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
