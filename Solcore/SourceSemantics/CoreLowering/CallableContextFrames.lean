import Solcore.Frontend.SourceCoreCallableContextFrames
import Solcore.SourceSemantics.CoreLowering.DataEquality
import Solcore.Core.FuelResumptionProperties

/-! Finite semantics of the ordinary Core callable-frame helpers. Reference
selection is restricted to heap-independent lexical projection paths. The next
frame and body run under their actual administrative binders; no exact-value
weakening theorem for arbitrary closure-producing code is assumed.

These laws authenticate native evaluation and restoration, not source ownership
of origin/view words, lexical capture metadata, or dynamic source ancestry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableContextFrames
open Core Frontend.SourceCoreCallableContextFrames
open DataEquality (Selects)
abbrev ContextFrame := Frontend.SourceCoreCallableContextFrames.Frame

/-- The helper restores exactly its one administrative cell. All other writes
and allocations remain as the body left them, including language failures. -/
theorem withFrame_evaluates {environment : Environment} {before nextStore bodyStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location}
    {saved installedValue result : Value}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved)
    (nextEvaluation : Evaluates (saved :: environment) before (next.weakenAt 0) installedValue nextStore)
    (bodyEvaluation : Evaluates (.unit :: saved :: environment) (nextStore.set location installedValue)
      ((body.weakenAt 0).weakenAt 0) result bodyStore) :
    Evaluates environment before (withFrame reference next body) result (bodyStore.set location saved) := by
  have beforeBound : location < before.length := (List.getElem?_eq_some_iff.mp savedRead).choose
  have nextBound : location < nextStore.length := Nat.lt_of_lt_of_le beforeBound (evaluation_store_length_monotone nextEvaluation)
  have bodyBound : location < bodyStore.length := by
    have grows := evaluation_store_length_monotone bodyEvaluation
    simp only [List.length_set] at grows
    exact Nat.lt_of_lt_of_le nextBound grows
  apply Evaluates.letE (.loadCell (referenceSelected.evaluates before) savedRead)
  apply Evaluates.letE (.storeCell ((referenceSelected.weaken saved).evaluates before) savedRead nextEvaluation
    (Store.write?_eq_some_iff.mpr ⟨nextBound, rfl⟩))
  apply Evaluates.letE bodyEvaluation
  apply Evaluates.letE (.storeCell (oldValue := bodyStore[location]) (((referenceSelected.weaken saved).weaken .unit).weaken result |>.evaluates bodyStore)
    (by exact List.getElem?_eq_getElem bodyBound) (.var rfl)
    (Store.write?_eq_some_iff.mpr ⟨bodyBound, rfl⟩))
  exact .var rfl

/-- Inversion extracts actual child evaluations from a completed helper. It
never assumes that a shifted closure body is equal to an unshifted result. -/
theorem withFrame_reflects {environment : Environment} {before finalStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location} {saved result : Value}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved)
    (evaluation : Evaluates environment before (withFrame reference next body) result finalStore) :
    ∃ installedValue nextStore bodyStore,
      Evaluates (saved :: environment) before (next.weakenAt 0) installedValue nextStore ∧
      Evaluates (.unit :: saved :: environment) (nextStore.set location installedValue)
        ((body.weakenAt 0).weakenAt 0) result bodyStore ∧
      finalStore = bodyStore.set location saved := by
  cases evaluation with
  | letE save remaining =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic save (.loadCell (referenceSelected.evaluates before) savedRead)
    cases remaining with
    | letE install remaining =>
      cases install with
      | storeCell referenceEvaluation _ nextEvaluation written =>
        obtain ⟨referenceEqual, storeEqual⟩ := evaluation_deterministic referenceEvaluation ((referenceSelected.weaken _).evaluates _)
        cases storeEqual
        cases referenceEqual
        obtain ⟨_, rfl⟩ := Store.write?_eq_some_iff.mp written
        cases remaining with
        | letE bodyEvaluation restore =>
          cases restore with
          | letE restored returned =>
            cases restored with
            | storeCell selected _ oldEvaluation written =>
              obtain ⟨referenceEqual, storeEqual⟩ := evaluation_deterministic selected
                ((((referenceSelected.weaken _).weaken .unit).weaken _).evaluates _)
              cases storeEqual
              cases referenceEqual
              cases oldEvaluation with
              | var found =>
                simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
                cases found
                cases returned with
                | var found =>
                  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
                  cases found
                  exact ⟨_, _, _, nextEvaluation, bodyEvaluation, (Store.write?_eq_some_iff.mp written).2⟩

theorem withFrame_iff {environment : Environment} {before finalStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location} {saved result : Value}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved) :
    Evaluates environment before (withFrame reference next body) result finalStore ↔
    ∃ installedValue nextStore bodyStore,
      Evaluates (saved :: environment) before (next.weakenAt 0) installedValue nextStore ∧
      Evaluates (.unit :: saved :: environment) (nextStore.set location installedValue)
        ((body.weakenAt 0).weakenAt 0) result bodyStore ∧
      finalStore = bodyStore.set location saved := by
  constructor
  · exact withFrame_reflects referenceSelected savedRead
  · rintro ⟨_, _, _, nextEvaluation, bodyEvaluation, rfl⟩
    exact withFrame_evaluates referenceSelected savedRead nextEvaluation bodyEvaluation

theorem withFrame_restores {environment : Environment} {before finalStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location} {saved result : Value}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved)
    (evaluation : Evaluates environment before (withFrame reference next body) result finalStore) :
    finalStore.read? location = some saved ∧
    ∃ bodyStore : Store, finalStore.length = bodyStore.length ∧
      (∀ other, other ≠ location → finalStore.read? other = bodyStore.read? other) := by
  obtain ⟨installedValue, nextStore, bodyStore, nextEvaluation, bodyEvaluation, rfl⟩ :=
    withFrame_reflects referenceSelected savedRead evaluation
  have beforeBound : location < before.length := (List.getElem?_eq_some_iff.mp savedRead).choose
  have nextBound := Nat.lt_of_lt_of_le beforeBound (evaluation_store_length_monotone nextEvaluation)
  have bodyBound : location < bodyStore.length := by
    have grows := evaluation_store_length_monotone bodyEvaluation
    simp only [List.length_set] at grows
    exact Nat.lt_of_lt_of_le nextBound grows
  have written : bodyStore.write? location saved = some (bodyStore.set location saved) :=
    Store.write?_eq_some_iff.mpr ⟨bodyBound, rfl⟩
  exact ⟨Store.write?_reads_written written, bodyStore, List.length_set,
    fun _ different => Store.write?_preserves_other written different⟩

theorem withFrame_run_done_iff {environment : Environment} {before finalStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location} {saved result : Value}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved) :
    (∃ fuel, runStateful fuel (.initial (withFrame reference next body) environment before) = .done result finalStore) ↔
    ∃ installedValue nextStore bodyStore,
      Evaluates (saved :: environment) before (next.weakenAt 0) installedValue nextStore ∧
      Evaluates (.unit :: saved :: environment) (nextStore.set location installedValue)
        ((body.weakenAt 0).weakenAt 0) result bodyStore ∧
      finalStore = bodyStore.set location saved := by
  constructor
  · rintro ⟨fuel, completed⟩
    exact withFrame_reflects referenceSelected savedRead (runStateful_evaluation_sound completed)
  · intro children
    exact evaluation_runStateful_complete ((withFrame_iff referenceSelected savedRead).mpr children)

theorem withFrame_run {environment : Environment} {before nextStore bodyStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location}
    {saved installedValue result : Value}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved)
    (nextEvaluation : Evaluates (saved :: environment) before (next.weakenAt 0) installedValue nextStore)
    (bodyEvaluation : Evaluates (.unit :: saved :: environment) (nextStore.set location installedValue)
      ((body.weakenAt 0).weakenAt 0) result bodyStore) :
    (∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (withFrame reference next body) environment before) = .done result (bodyStore.set location saved)) ∧
    (∀ fuel actual after,
      runStateful fuel (.initial (withFrame reference next body) environment before) = .done actual after →
        actual = result ∧ after = bodyStore.set location saved) := by
  have evaluated := withFrame_evaluates referenceSelected savedRead nextEvaluation bodyEvaluation
  exact ⟨evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

/-- The usual administrative frame allocation has an exact append-only cell. -/
theorem allocate_evaluates {layout : Layout} {environment : Environment} {before after : Store}
    {body : Expr} {result : Value}
    (evaluated : Evaluates (.cellRef layout.type before.length :: environment)
      (before ++ [encode layout .empty]) body result after) :
    Evaluates environment before (allocate layout body) result after :=
  .letE (.newCell (.construct .unit)) evaluated

theorem allocate_reflects {layout : Layout} {environment : Environment} {before after : Store}
    {body : Expr} {result : Value}
    (evaluated : Evaluates environment before (allocate layout body) result after) :
    Evaluates (.cellRef layout.type before.length :: environment)
      (before ++ [encode layout .empty]) body result after := by
  cases evaluated with
  | letE allocated body =>
    cases allocated with
    | newCell value =>
      cases value with
      | construct unit => cases unit; exact body

/-- Only an incoming leading view whose target is this lambda survives.
Its parent is rebased onto the lexically captured frame. -/
def selectedFrame (origin : Word) (captured : ContextFrame) : ContextFrame → ContextFrame
  | .view id target _ => if target = origin then .lambda origin (.view id origin captured) else .lambda origin captured
  | _ => .lambda origin captured

private theorem lambda_selected {layout : Layout} {environment : Environment} {captured : Expr}
    {frame : ContextFrame} (selected : Selects environment captured (encode layout frame))
    (origin : Word) (store : Store) :
    Evaluates environment store (lambda layout origin captured) (encode layout (.lambda origin frame)) store :=
  .construct (.pair .word (selected.evaluates store))

theorem lambdaFrame_evaluates {layout : Layout} {environment : Environment} {captured current : Expr}
    {capturedFrame currentFrame : ContextFrame} (origin : Word)
    (capturedSelected : Selects environment captured (encode layout capturedFrame))
    (currentSelected : Selects environment current (encode layout currentFrame)) (store : Store) :
    Evaluates environment store (lambdaFrame layout origin captured current)
      (encode layout (selectedFrame origin capturedFrame currentFrame)) store := by
  cases currentFrame with
  | empty =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (capturedSelected.weaken .unit) origin store)
  | named id =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (capturedSelected.weaken (.word id)) origin store)
  | lambda id parent =>
    exact .matchData (currentSelected.evaluates store) rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (capturedSelected.weaken (.pair (.word id) (encode layout parent))) origin store)
  | view id target parent =>
    apply Evaluates.matchData (currentSelected.evaluates store) rfl (by rfl)
    by_cases equal : target = origin
    · simp only [selectedFrame, if_pos equal]
      apply Evaluates.ifTrue (.binary (.first (.second (.var rfl))) .word ?_)
      · exact .construct (.pair .word (.construct (.pair (.first (.var rfl))
          (.pair .word ((capturedSelected.weaken _).evaluates store)))))
      · simp [BinaryOp.apply, equal]
    · simp only [selectedFrame, if_neg equal]
      apply Evaluates.ifFalse (.binary (.first (.second (.var rfl))) .word ?_)
      · simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (capturedSelected.weaken (.pair (.word id) (.pair (.word target) (encode layout parent)))) origin store
      · simp [BinaryOp.apply, equal]

/-- Reflection is unconditional on a successful source trace: lexical native
selection determines the exact finite result and unchanged native store. -/
theorem lambdaFrame_reflects {layout : Layout} {environment : Environment} {before after : Store}
    {captured current : Expr} {capturedFrame currentFrame : ContextFrame} {origin : Word} {result : Value}
    (capturedSelected : Selects environment captured (encode layout capturedFrame))
    (currentSelected : Selects environment current (encode layout currentFrame))
    (evaluated : Evaluates environment before (lambdaFrame layout origin captured current) result after) :
    result = encode layout (selectedFrame origin capturedFrame currentFrame) ∧ after = before :=
  evaluation_deterministic evaluated (lambdaFrame_evaluates origin capturedSelected currentSelected before)

theorem lambdaFrame_run {layout : Layout} {environment : Environment} {store : Store}
    {captured current : Expr} {capturedFrame currentFrame : ContextFrame} (origin : Word)
    (capturedSelected : Selects environment captured (encode layout capturedFrame))
    (currentSelected : Selects environment current (encode layout currentFrame)) :
    (∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (lambdaFrame layout origin captured current) environment store) =
        .done (encode layout (selectedFrame origin capturedFrame currentFrame)) store) ∧
    (∀ fuel actual after,
      runStateful fuel (.initial (lambdaFrame layout origin captured current) environment store) = .done actual after →
        actual = encode layout (selectedFrame origin capturedFrame currentFrame) ∧ after = store) :=
  ⟨evaluation_runStateful_complete_with_sufficient_fuel (lambdaFrame_evaluates origin capturedSelected currentSelected store),
    fun _ _ _ ran => lambdaFrame_reflects capturedSelected currentSelected (runStateful_evaluation_sound ran)⟩

/-- Real exhaustion retains the continuation that performs restoration. A
checkpoint need not itself have the caller frame installed. -/
theorem withFrame_resume {environment : Environment} {before : Store} {reference next body : Expr}
    {spent : Nat} {checkpoint : State}
    (exhausted : runStateful spent (.initial (withFrame reference next body) environment before) = .outOfFuel checkpoint)
    (additional : Nat) :
    runStateful additional checkpoint = runStateful (spent + additional)
      (.initial (withFrame reference next body) environment before) := runStateful_resume exhausted additional

/-- A genuine suspended helper with finite child evaluations has enough
remaining fuel to finish restoration. Before completion the frame may still
be the callee's, and the checkpoint is retained unchanged. -/
theorem withFrame_resumed_finishes {environment : Environment} {before nextStore bodyStore : Store}
    {reference next body : Expr} {frameType : Ty} {location : Location}
    {saved installedValue result : Value} {spent : Nat} {checkpoint : State}
    (referenceSelected : Selects environment reference (.cellRef frameType location))
    (savedRead : before.read? location = some saved)
    (nextEvaluation : Evaluates (saved :: environment) before (next.weakenAt 0) installedValue nextStore)
    (bodyEvaluation : Evaluates (.unit :: saved :: environment) (nextStore.set location installedValue)
      ((body.weakenAt 0).weakenAt 0) result bodyStore)
    (exhausted : runStateful spent (.initial (withFrame reference next body) environment before) = .outOfFuel checkpoint) :
    ∃ remaining, ∀ additional, remaining ≤ additional →
      runStateful additional checkpoint = .done result (bodyStore.set location saved) := by
  obtain ⟨required, sufficient⟩ := (withFrame_run referenceSelected savedRead nextEvaluation bodyEvaluation).1
  refine ⟨required, fun additional enough => ?_⟩
  rw [withFrame_resume exhausted additional]
  exact sufficient _ (by omega)

end Solcore.SourceSemantics.CoreLowering.CallableContextFrames
