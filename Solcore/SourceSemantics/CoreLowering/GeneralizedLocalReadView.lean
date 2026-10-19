import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallFrame

/-! The emitted read wrapper saves the caller at the read occurrence. Later
application installs that saved view before invoking the original carrier and
restores the actual application caller, including on language failure. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadView
open Core Frontend ReadOnly
open SourceCoreCallableIndexedFrames SourceCoreCallableIndexedAncestry
open CallableIndexedHistory

def value (layout : SourceCoreCallableIndexedFrames.Layout) (parameter result : Ty) (id target : Word)
    (referenceIndex : Nat) (embedding : Renaming) (caller : NativeFrame)
    (identity payload : Value) (environment : Environment) : Value :=
  .pair (.pair identity
    (.closure parameter (LanguageResult.resultType result)
      ((viewBody layout id target referenceIndex).rename embedding.lift.lift.lift)
      (encode layout caller :: .pair (.pair identity payload) (.word target) :: environment))) (.word target)

theorem formation {layout : SourceCoreCallableIndexedFrames.Layout} {parameter result : Ty} {id target : Word}
    {referenceIndex location : Nat} {embedding : Renaming} {caller : NativeFrame}
    {identity payload : Value} {environment : Environment} {before after : Store} {readCode : Expr}
    (read : Evaluates environment before (readCode.rename embedding)
      (.inRight .word (.pair (.pair identity payload) (.word target))) after)
    (reference : environment[embedding referenceIndex]? = some (.cellRef layout.type location))
    (snapshot : after.read? location = some (encode layout caller)) :
    Evaluates environment before
      ((viewLower layout parameter result id target referenceIndex readCode).rename embedding)
      (.inRight .word (value layout parameter result id target referenceIndex embedding caller identity payload environment)) after := by
  apply Evaluates.caseRight read
  apply Evaluates.letE (.loadCell (.var (by simpa [Renaming.lift] using reference)) snapshot)
  exact .inRight (.pair (.pair (.first (.first (.var rfl))) .lambda) (.second (.var rfl)))

private theorem body_rename (layout : SourceCoreCallableIndexedFrames.Layout) (id target : Word) (referenceIndex : Nat) (embedding : Renaming) :
    (viewBody layout id target referenceIndex).rename embedding.lift.lift.lift =
      viewBody layout id target (embedding referenceIndex) := by
  simp only [viewBody, NamedCalls.withFrame_rename, CallableIndexedRenaming.readView, Expr.rename, Renaming.lift]

/-- The returned wrapper is typed from the actual stored carrier and the
read-time environment. No typing relation for an arbitrary embedding is assumed. -/
theorem runtime_hasType {definitions : DataEnvironment} {world : StoreTyping}
    {layout : SourceCoreCallableIndexedFrames.Layout} {parameter result : Ty} {id target : Word}
    {referenceIndex location : Nat} {embedding : Renaming} {caller : NativeFrame}
    {identity payload : Value} {environment : Environment} {context : Core.Context}
    (registered : layout.Registered definitions)
    (carrier : RuntimeValueHasType world (.pair (.pair identity payload) (.word target))
      (CallableContract.functionType parameter result) definitions)
    (environments : RuntimeEnvironmentHasTypes world environment context definitions)
    (reference : environment[embedding referenceIndex]? = some (.cellRef layout.type location)) :
    RuntimeValueHasType world
      (value layout parameter result id target referenceIndex embedding caller identity payload environment)
      (CallableContract.functionType parameter result) definitions := by
  have typedReference : context[embedding referenceIndex]? = some (.cell layout.type) := by
    rw [← environments.type_tags]
    simp only [List.getElem?_map, reference, Option.map_some, Value.type]
  have frameTyped : RuntimeValueHasType world (encode layout caller) layout.type definitions := by
    exact SourceCoreCallableIndexedFrames.encode_runtime_typed world registered caller
  have original := carrier
  cases carrier with
  | pair tagged contract =>
    cases tagged with
    | pair identityTyped _ =>
      refine .pair (.pair identityTyped (.closure (.cons frameTyped (.cons original environments)) ?_)) contract
      rw [body_rename]
      unfold viewBody
      apply SourceCoreCallableContextFrames.withFrame_hasType
      · exact .var (by simpa only [List.getElem?_cons_succ] using typedReference)
      · exact SourceCoreCallableIndexedDispatch.readView_hasType registered id target (.var rfl)
      · exact .apply (.second (.first (.var rfl))) (.var rfl)

/-- The wrapper exposes one call to the retained inner lambda. Its saved
read-time frame and the current caller are different values throughout. -/
theorem agreement {layout : SourceCoreCallableIndexedFrames.Layout} {parameter result : Ty} {id target : Word}
    {referenceIndex location : Nat} {embedding : Renaming} {caller : NativeFrame}
    {identity : Value} {innerBody : Expr} {innerEnvironment environment : Environment}
    {argument saved : Value} {store : Store}
    (reference : environment[embedding referenceIndex]? = some (.cellRef layout.type location))
    (current : store.read? location = some saved) :
    let payload := Value.closure parameter (LanguageResult.resultType result) innerBody innerEnvironment
    let original := Value.pair (.pair identity payload) (.word target)
    let entry := argument :: encode layout caller :: original :: environment
    let next := encode layout (SourceCoreCallableIndexedDispatch.readFrame id target caller)
    (∀ {output finalStore}, Evaluates (argument :: innerEnvironment) (store.set location next)
      innerBody output finalStore →
      Evaluates entry store ((viewBody layout id target referenceIndex).rename embedding.lift.lift.lift)
        output (finalStore.set location saved)) ∧
    (∀ {output finalStore},
      Evaluates entry store ((viewBody layout id target referenceIndex).rename embedding.lift.lift.lift)
        output finalStore →
      ∃ bodyStore, Evaluates (argument :: innerEnvironment) (store.set location next) innerBody output bodyStore ∧
        finalStore = bodyStore.set location saved) := by
  let payload := Value.closure parameter (LanguageResult.resultType result) innerBody innerEnvironment
  let original := Value.pair (.pair identity payload) (.word target)
  let entry := argument :: encode layout caller :: original :: environment
  let next := encode layout (SourceCoreCallableIndexedDispatch.readFrame id target caller)
  have selected : DataEquality.Selects entry (.var (embedding referenceIndex + 3)) (.cellRef layout.type location) :=
    .var (by simpa [entry] using reference)
  have nextEval : Evaluates (saved :: entry) store
      ((SourceCoreCallableIndexedDispatch.readView layout id target (.var 1)).weakenAt 0) next store := by
    rw [CallableIndexedRenaming.readView_weaken]
    simpa only [Expr.weakenAt, Nat.zero_le, ↓reduceIte] using CallableIndexedContextFrames.readView_evaluates id target
      (show DataEquality.Selects (saved :: entry) (.var 2) (encode layout caller) from .var rfl) store
  rw [body_rename]
  constructor
  · intro output finalStore evaluated
    apply CallableContextFrames.withFrame_evaluates selected current nextEval
    simp only [Expr.weakenAt, Nat.zero_le, ↓reduceIte]
    exact .apply (.second (.first (.var rfl))) (.var rfl) evaluated
  · intro output finalStore evaluated
    obtain ⟨installed, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
      CallableContextFrames.withFrame_reflects selected current evaluated
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEval nextEvaluation
    simp only [Expr.weakenAt, Nat.zero_le, ↓reduceIte] at bodyEvaluation
    cases bodyEvaluation with
    | apply callee arg body =>
      obtain ⟨sameClosure, rfl⟩ := evaluation_deterministic callee
        (show Evaluates (.unit :: saved :: entry) (store.set location next)
          (.second (.first (.var 4))) payload (store.set location next) from .second (.first (.var rfl)))
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj sameClosure
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic arg (Evaluates.var (show
        (.unit :: saved :: entry)[2]? = some argument from rfl))
      exact ⟨bodyStore, body, finalEq⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadView
