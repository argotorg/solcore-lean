import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix

/-! The actual materialized lambda wrapper installs its paired child frame,
enters the emitted raw body once, and restores the real transient caller frame.
Parameter allocation and body meaning can be composed after this boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallFrame
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open GeneralizedLocalDescriptorOrigin

private theorem body_rename (body : Expr) (embedding : Renaming) :
    (((body.weakenAt 1).rename embedding.lift.lift).weakenAt 0).weakenAt 0 =
      body.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding embedding) := by
  simp only [← Expr.rename_insertion, Expr.rename_comp, CallableIndexedLambdaEntryPrefix.bodyEmbedding]
  congr 1
  funext index
  cases index <;> rfl

theorem agreement {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution}
    (origin : Origin prepared descriptor binding lexical)
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {actual : Core.Environment}
    (captured : Captures prepared mapping world scope function.captured actual)
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope captured.administrative viewRelation)
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id : Word}
    (callerCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      callerNative callerGhost (some caller))
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id code.descriptor.id)
    {argument : Value} {store : Store} {location : Core.Location}
    (reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))) :
    let current := SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative
    let next := SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table
      code.descriptor.id origin.native current
    let bodyEnvironment := .unit :: encode prepared.ancestry.layout.frame current :: argument ::
      encode prepared.ancestry.layout.frame origin.native :: actual
    (∀ {result finalStore},
      Evaluates bodyEnvironment (store.set location (encode prepared.ancestry.layout.frame next))
        (code.receipt.rawBody.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding captured.embedding)) result finalStore →
      Evaluates (argument :: encode prepared.ancestry.layout.frame origin.native :: actual) store
        (code.body.rename captured.embedding.lift.lift) result
        (finalStore.set location (encode prepared.ancestry.layout.frame current))) ∧
    (∀ {result finalStore},
      Evaluates (argument :: encode prepared.ancestry.layout.frame origin.native :: actual) store
        (code.body.rename captured.embedding.lift.lift) result finalStore →
      ∃ bodyStore,
        Evaluates bodyEnvironment (store.set location (encode prepared.ancestry.layout.frame next))
          (code.receipt.rawBody.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding captured.embedding)) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current)) := by
  let layout := prepared.ancestry.layout.frame
  let current := SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative
  let saved := encode layout current
  let lexicalValue := encode layout origin.native
  let next := SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id origin.native current
  have selected : DataEquality.Selects (argument :: lexicalValue :: actual)
      (.var (captured.embedding code.referenceIndex + 2)) (.cellRef layout.type location) :=
    .var (by simpa using captured.agrees reference)
  have nextEvaluation : Evaluates (saved :: argument :: lexicalValue :: actual) store
      ((SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table layout code.descriptor.id
        (.var 1) (.loadCell (.var (captured.embedding code.referenceIndex + 2)))).weakenAt 0)
      (encode layout next) store := by
    rw [CallableIndexedRenaming.lambdaFrame_weaken]
    simpa only [Expr.weakenAt, Nat.zero_le, ↓reduceIte] using
      (GeneralizedLocalCallPrefix.evaluates origin callerCarried recipe
        (environment := saved :: argument :: lexicalValue :: actual)
        (lexicalExpression := .var 2)
        (referenceIndex := captured.embedding code.referenceIndex + 3)
        (.var rfl) (by simpa [Nat.add_assoc] using captured.agrees reference) read).1
  have wrapper : code.body.rename captured.embedding.lift.lift =
      withFrame (.var (captured.embedding code.referenceIndex + 2))
        (SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table layout code.descriptor.id (.var 1)
          (.loadCell (.var (captured.embedding code.referenceIndex + 2))))
        ((code.receipt.rawBody.weakenAt 1).rename captured.embedding.lift.lift) := by
    simp only [Code.body, NamedCalls.withFrame_rename, CallableIndexedRenaming.lambdaFrame, Expr.rename, Renaming.lift]
    rfl
  constructor
  · intro result finalStore evaluated
    rw [wrapper]
    apply CallableContextFrames.withFrame_evaluates selected read nextEvaluation
    rw [body_rename]
    exact evaluated
  · intro result finalStore evaluated
    rw [wrapper] at evaluated
    obtain ⟨nextValue, nextStore, bodyStore, nextEval, bodyEval, finalEq⟩ :=
      CallableContextFrames.withFrame_reflects selected read evaluated
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEval nextEvaluation
    rw [body_rename] at bodyEval
    exact ⟨bodyStore, bodyEval, finalEq⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallFrame
