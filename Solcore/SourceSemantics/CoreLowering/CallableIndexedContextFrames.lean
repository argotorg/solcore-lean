import Solcore.Frontend.SourceCoreCallableIndexedDispatch
import Solcore.SourceSemantics.CoreLowering.CallableContextFrames

/-! Finite ordinary Core evaluation of table-derived indexed dispatch. These
laws concern exact native values and unchanged stores. Source history, graph
coverage and actual closure provenance are separate owned proof boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedContextFrames
open Core Frontend.SourceCoreCallableIndexedFrames Frontend.SourceCoreCallableIndexedDispatch
open DataEquality (Selects)
abbrev IndexedFrame := Frontend.SourceCoreCallableIndexedFrames.Frame

theorem literal_evaluates (layout : Layout) (frame : IndexedFrame)
    (environment : Environment) (store : Store) :
    Evaluates environment store (literal layout frame) (encode layout frame) store := by
  cases frame with
  | empty => exact .construct .unit
  | state index => exact .construct .integer
  | view id target caller => exact .construct (.pair .word (.pair .word .integer))
  | invalid => exact .construct .unit

private theorem integerEq_evaluates {environment : Environment} {expression : Expr} {value : Int}
    (selected : Selects environment expression (.integer value)) (expected : Int) (store : Store) :
    Evaluates environment store (.binary .integerEq expression (.integer expected)) (.bool (value == expected)) store :=
  .binary (selected.evaluates store) .integer rfl

private theorem wordEq_evaluates {environment : Environment} {expression : Expr} {value : Word}
    (selected : Selects environment expression (.word value)) (expected : Word) (store : Store) :
    Evaluates environment store (.binary .wordEq expression (.word expected)) (.bool (value == expected)) store :=
  .binary (selected.evaluates store) .word rfl

theorem plainDispatch_evaluates {layout : Layout} {environment : Environment} {lexical : Expr} {index : Int}
    (table : Table) (origin : Word) (selected : Selects environment lexical (.integer index))
    (rows : List LambdaEdge) (store : Store) :
    Evaluates environment store (plainDispatch table layout origin lexical rows)
      (encode layout (plainRows table origin index rows)) store := by
  induction rows with
  | nil => exact .construct .unit
  | cons edge rest ih =>
    by_cases owned : edge.origin = origin
    · simp only [plainDispatch, if_pos owned]
      by_cases same : index = Int.ofNat edge.state
      · simp only [plainRows, owned, same, and_self, ↓reduceIte]
        exact .ifTrue (by simpa [same] using integerEq_evaluates selected (Int.ofNat edge.state) store)
          (literal_evaluates layout _ environment store)
      · simp only [plainRows, owned, same, and_false, ↓reduceIte]
        exact .ifFalse (by simpa only [beq_eq_false_iff_ne.mpr same] using integerEq_evaluates selected (Int.ofNat edge.state) store) ih
    · simpa only [plainDispatch, plainRows, owned, false_and, ↓reduceIte] using ih

theorem viewDispatch_evaluates {layout : Layout} {environment : Environment}
    {id caller lexical : Expr} {view : Word} {callerIndex lexicalIndex : Int}
    (table : Table) (origin : Word)
    (idSelected : Selects environment id (.word view))
    (callerSelected : Selects environment caller (.integer callerIndex))
    (lexicalSelected : Selects environment lexical (.integer lexicalIndex))
    (rows : List ViewEdge) (store : Store) :
    Evaluates environment store (viewDispatch table layout origin id caller lexical rows)
      (encode layout (viewRows table origin view callerIndex lexicalIndex rows)) store := by
  induction rows with
  | nil => exact .construct .unit
  | cons edge rest ih =>
    by_cases owned : edge.target = origin
    · simp only [viewDispatch, if_pos owned]
      by_cases viewSame : edge.view = view
      · by_cases callerSame : callerIndex = Int.ofNat edge.caller
        · by_cases lexicalSame : lexicalIndex = Int.ofNat edge.lexical
          · simp only [viewRows, owned, viewSame, callerSame, lexicalSame, and_self, ↓reduceIte]
            exact .ifTrue (.ifTrue (by simpa [viewSame] using wordEq_evaluates idSelected edge.view store)
                (.ifTrue (by simpa [callerSame] using integerEq_evaluates callerSelected (Int.ofNat edge.caller) store)
                  (by simpa [lexicalSame] using integerEq_evaluates lexicalSelected (Int.ofNat edge.lexical) store)))
              (literal_evaluates layout _ environment store)
          · simp only [viewRows, owned, viewSame, callerSame, lexicalSame, and_false, ↓reduceIte]
            exact .ifFalse (.ifTrue (by simpa [viewSame] using wordEq_evaluates idSelected edge.view store)
                (.ifTrue (by simpa [callerSame] using integerEq_evaluates callerSelected (Int.ofNat edge.caller) store)
                  (by simpa only [beq_eq_false_iff_ne.mpr lexicalSame] using integerEq_evaluates lexicalSelected (Int.ofNat edge.lexical) store)))
              (by simpa only [callerSame] using ih)
        · simp only [viewRows, owned, viewSame, callerSame, false_and, and_false, ↓reduceIte]
          exact .ifFalse (.ifTrue (by simpa [viewSame] using wordEq_evaluates idSelected edge.view store)
              (.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr callerSame] using integerEq_evaluates callerSelected (Int.ofNat edge.caller) store) .bool)) ih
      · simp only [viewRows, owned, viewSame, false_and, and_false, ↓reduceIte]
        exact .ifFalse (.ifFalse (by simpa only [beq_eq_false_iff_ne.mpr (Ne.symm viewSame)] using wordEq_evaluates idSelected edge.view store) .bool) ih
    · simpa only [viewDispatch, viewRows, owned, false_and, ↓reduceIte] using ih

theorem lambdaFrame_evaluates {layout : Layout} {environment : Environment} {lexical current : Expr}
    {lexicalFrame currentFrame : IndexedFrame} (table : Table) (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentSelected : Selects environment current (encode layout currentFrame)) (store : Store) :
    Evaluates environment store (lambdaFrame table layout origin lexical current)
      (encode layout (selectedFrame table origin lexicalFrame currentFrame)) store := by
  cases lexicalFrame with
  | empty => exact .matchData (lexicalSelected.evaluates store) rfl rfl (.construct .unit)
  | invalid => exact .matchData (lexicalSelected.evaluates store) rfl rfl (.construct .unit)
  | view id target caller => exact .matchData (lexicalSelected.evaluates store) rfl rfl (.construct .unit)
  | state index =>
    apply Evaluates.matchData (lexicalSelected.evaluates store) rfl rfl
    cases currentFrame with
    | empty =>
      exact .matchData ((currentSelected.weaken (.integer index)).evaluates store) rfl rfl
        (plainDispatch_evaluates table origin (.var rfl) _ store)
    | state currentIndex =>
      exact .matchData ((currentSelected.weaken (.integer index)).evaluates store) rfl rfl
        (plainDispatch_evaluates table origin (.var rfl) _ store)
    | invalid =>
      exact .matchData ((currentSelected.weaken (.integer index)).evaluates store) rfl rfl
        (plainDispatch_evaluates table origin (.var rfl) _ store)
    | view id target caller =>
      apply Evaluates.matchData ((currentSelected.weaken (.integer index)).evaluates store) rfl rfl
      have targetSelected : Selects (.pair (.word id) (.pair (.word target) (.integer caller)) :: .integer index :: environment)
          (.first (.second (.var 0))) (.word target) := .first (.second (.var rfl))
      by_cases same : target = origin
      · simp only [selectedFrame, if_pos same]
        exact .ifTrue (by simpa [same] using wordEq_evaluates targetSelected origin store)
          (viewDispatch_evaluates table origin (.first (.var rfl))
            (.second (.second (.var rfl))) (.var rfl) _ store)
      · simp only [selectedFrame, if_neg same]
        exact .ifFalse (by simpa only [beq_eq_false_iff_ne.mpr same] using wordEq_evaluates targetSelected origin store)
          (plainDispatch_evaluates table origin (.var rfl) _ store)

theorem readView_evaluates {layout : Layout} {environment : Environment} {current : Expr}
    {currentFrame : IndexedFrame} (id target : Word)
    (selected : Selects environment current (encode layout currentFrame)) (store : Store) :
    Evaluates environment store (readView layout id target current)
      (encode layout (readFrame id target currentFrame)) store := by
  cases currentFrame with
  | empty => exact .matchData (selected.evaluates store) rfl rfl (.construct .unit)
  | state index => exact .matchData (selected.evaluates store) rfl rfl (.construct (.pair .word (.pair .word (.var rfl))))
  | view id target caller => exact .matchData (selected.evaluates store) rfl rfl (.construct .unit)
  | invalid => exact .matchData (selected.evaluates store) rfl rfl (.construct .unit)

theorem lambdaFrame_reflects {layout : Layout} {environment : Environment} {before after : Store}
    {lexical current : Expr} {lexicalFrame currentFrame : IndexedFrame} {table : Table} {origin : Word} {result : Value}
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentSelected : Selects environment current (encode layout currentFrame))
    (evaluated : Evaluates environment before (lambdaFrame table layout origin lexical current) result after) :
    result = encode layout (selectedFrame table origin lexicalFrame currentFrame) ∧ after = before :=
  evaluation_deterministic evaluated (lambdaFrame_evaluates table origin lexicalSelected currentSelected before)

theorem lambdaFrame_run {layout : Layout} {environment : Environment} {store : Store}
    {lexical current : Expr} {lexicalFrame currentFrame : IndexedFrame} (table : Table) (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentSelected : Selects environment current (encode layout currentFrame)) :
    (∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (lambdaFrame table layout origin lexical current) environment store) =
        .done (encode layout (selectedFrame table origin lexicalFrame currentFrame)) store) ∧
    (∀ fuel actual after,
      runStateful fuel (.initial (lambdaFrame table layout origin lexical current) environment store) = .done actual after →
        actual = encode layout (selectedFrame table origin lexicalFrame currentFrame) ∧ after = store) :=
  ⟨evaluation_runStateful_complete_with_sufficient_fuel (lambdaFrame_evaluates table origin lexicalSelected currentSelected store),
    fun _ _ _ ran => lambdaFrame_reflects lexicalSelected currentSelected (runStateful_evaluation_sound ran)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedContextFrames
