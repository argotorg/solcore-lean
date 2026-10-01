import Solcore.Frontend.SourceCoreCallablePairedFrames
import Solcore.SourceSemantics.CoreLowering.CallableContextFrames

/-! Native finite semantics for the two-parent carrier. A matching read view
keeps its saved caller separate from the lexical creation frame. These laws
concern actual Core evaluation and stores, not source history inferred from IDs.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePairedContextFrames
open Core Frontend.SourceCoreCallablePairedFrames
open DataEquality (Selects)
abbrev PairedFrame := Frontend.SourceCoreCallablePairedFrames.Frame

theorem allocate_evaluates {layout : Layout} {environment : Environment} {before after : Store}
    {body : Expr} {result : Value}
    (evaluated : Evaluates (.cellRef layout.type before.length :: environment)
      (before ++ [encode layout .empty]) body result after) :
    Evaluates environment before (allocate layout body) result after :=
  .letE (.newCell (.construct .unit)) evaluated

private theorem lambda_selected {layout : Layout} {environment : Environment} {lexical : Expr}
    {frame : PairedFrame} (selected : Selects environment lexical (encode layout frame))
    (origin : Word) (store : Store) :
    Evaluates environment store (lambda layout origin lexical) (encode layout (.lambda origin frame)) store :=
  .construct (.pair .word (selected.evaluates store))

theorem lambdaFrame_evaluates {layout : Layout} {environment : Environment} {lexical current : Expr}
    {lexicalFrame currentFrame : PairedFrame} (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentSelected : Selects environment current (encode layout currentFrame)) (store : Store) :
    Evaluates environment store (lambdaFrame layout origin lexical current)
      (encode layout (selectedFrame origin lexicalFrame currentFrame)) store := by
  cases currentFrame with
  | empty =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (lexicalSelected.weaken .unit) origin store)
  | named id =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (lexicalSelected.weaken (.word id)) origin store)
  | lambda id parent =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (lexicalSelected.weaken (.pair (.word id) (encode layout parent))) origin store)
  | view id target caller =>
    apply Evaluates.matchData (currentSelected.evaluates store) rfl rfl
    by_cases equal : target = origin
    · simp only [selectedFrame, if_pos equal]
      apply Evaluates.ifTrue (.binary (.first (.second (.var rfl))) .word ?_)
      · exact .construct (.pair (.first (.var rfl)) (.pair .word
          (.pair (.second (.second (.var rfl))) ((lexicalSelected.weaken _).evaluates store))))
      · simp [BinaryOp.apply, equal]
    · simp only [selectedFrame, if_neg equal]
      apply Evaluates.ifFalse (.binary (.first (.second (.var rfl))) .word ?_)
      · simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected
          (lexicalSelected.weaken (.pair (.word id) (.pair (.word target) (encode layout caller)))) origin store
      · simp [BinaryOp.apply, equal]
  | appliedView id target caller saved =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected
        (lexicalSelected.weaken (.pair (.word id) (.pair (.word target)
          (.pair (encode layout caller) (encode layout saved))))) origin store)

theorem lambdaFrame_reflects {layout : Layout} {environment : Environment} {before after : Store}
    {lexical current : Expr} {lexicalFrame currentFrame : PairedFrame} {origin : Word} {result : Value}
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentSelected : Selects environment current (encode layout currentFrame))
    (evaluated : Evaluates environment before (lambdaFrame layout origin lexical current) result after) :
    result = encode layout (selectedFrame origin lexicalFrame currentFrame) ∧ after = before :=
  evaluation_deterministic evaluated (lambdaFrame_evaluates origin lexicalSelected currentSelected before)

theorem lambdaFrame_run {layout : Layout} {environment : Environment} {store : Store}
    {lexical current : Expr} {lexicalFrame currentFrame : PairedFrame} (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentSelected : Selects environment current (encode layout currentFrame)) :
    (∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (lambdaFrame layout origin lexical current) environment store) =
        .done (encode layout (selectedFrame origin lexicalFrame currentFrame)) store) ∧
    (∀ fuel actual after,
      runStateful fuel (.initial (lambdaFrame layout origin lexical current) environment store) = .done actual after →
        actual = encode layout (selectedFrame origin lexicalFrame currentFrame) ∧ after = store) :=
  ⟨evaluation_runStateful_complete_with_sufficient_fuel (lambdaFrame_evaluates origin lexicalSelected currentSelected store),
    fun _ _ _ ran => lambdaFrame_reflects lexicalSelected currentSelected (runStateful_evaluation_sound ran)⟩

end Solcore.SourceSemantics.CoreLowering.CallablePairedContextFrames
