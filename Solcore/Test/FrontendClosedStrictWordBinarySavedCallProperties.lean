import Solcore.Frontend.ClosedSourceStrictWordBinaryProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties

/- Original saved closures can occur on either strict operand side. Caller
arguments are read before the fresh saved-owner parameter shadows saved p.
All tails and stores are arbitrary mixed rows; duplicate identities are allowed.
These reference/identity-body fixtures preserve stores and make no claim about
additional state-changing caller prefixes, typing, or Core closure identity. -/
set_option autoImplicit false
open Solcore Solcore.Frontend
namespace Tests.ClosedStrictWordBinarySavedCall

private def ref (s : Nat → Syntax.SourceSpan) (i : Nat) (name : String) : Syntax.Expr :=
  ⟨s i, .identifier ⟨s (i + 1), name⟩⟩
private def body (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 10, [⟨s 11, .returnStmt (some (ref s 12 "p"))⟩]⟩
private def original (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 4, .lambda (s 5) ⟨s 6, [⟨s 7, .inferred ⟨s 8, "p"⟩⟩]⟩ none (body s)⟩
private def call (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 14, .call (ref s 15 "picked") ⟨s 17, [ref s 18 "p"]⟩⟩
private def binary (s : Nat → Syntax.SourceSpan) (onLeft : Bool)
    (operator : Syntax.BinaryOp) : Syntax.Expr :=
  ⟨s 0, .binary (if onLeft then call s else ref s 20 "other") ⟨s 1, operator⟩
    (if onLeft then ref s 20 "other" else call s)⟩
private def savedNames (owner : Resolved.DeclarationId) (tail : LocalNameTable) : LocalNameTable :=
  ("p", ⟨owner, 2⟩) :: tail
private def savedCaptured (owner : Resolved.DeclarationId) (old : RuntimeValue)
    (tail : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  (⟨owner, 2⟩, old) :: tail
private def callerNames (owner : Resolved.DeclarationId) (tail : LocalNameTable) : LocalNameTable :=
  ("picked", ⟨owner, 0⟩) :: ("p", ⟨owner, 1⟩) :: ("other", ⟨owner, 2⟩) :: tail
private def callerCaptured (owner : Resolved.DeclarationId) (made : RuntimeValue)
    (argument other : Core.Word) (tail : Resolved.LocalScope RuntimeValue) :
    Resolved.LocalScope RuntimeValue :=
  (⟨owner, 0⟩, made) :: (⟨owner, 1⟩, .word argument) :: (⟨owner, 2⟩, .word other) :: tail

private theorem index_ne (owner : Resolved.DeclarationId) {i j : Nat} (different : i ≠ j) :
    (⟨owner, i⟩ : Resolved.LocalId) ≠ ⟨owner, j⟩ := by
  intro equal
  exact different (congrArg Resolved.LocalId.binderIndex equal)

private theorem strict_endpoints {owner names captured store middle final left right}
    {leftWord rightWord result} (s : Nat → Syntax.SourceSpan) (operator : Syntax.BinaryOp)
    (l : ClosedSourceExpressionEvaluates owner names captured store left (.word leftWord) middle)
    (r : ClosedSourceExpressionEvaluates owner names captured middle right (.word rightWord) final)
    (meaning : StrictWordBinaryDenotes operator leftWord rightWord result) :
    ∀ actual actualFinal, ClosedSourceExpressionEvaluates owner names captured store
      ⟨s 0, .binary left ⟨s 1, operator⟩ right⟩ actual actualFinal ↔
      actual = RuntimeValue.ofCore result ∧ actualFinal = final := by
  intro actual actualFinal
  obtain ⟨notAnd, notOr⟩ := meaning.operator_is_strict
  constructor
  · intro evaluated
    obtain ⟨lw, rw, value, actualMiddle, sameValue, actualLeft, actualRight, actualMeaning⟩ :=
      (closedSourceExpressionEvaluates_strictWordBinary_iff notAnd notOr).mp evaluated
    obtain ⟨sameLeft, sameMiddle⟩ := l.deterministic actualLeft
    cases RuntimeValue.word.inj sameLeft
    cases sameMiddle
    obtain ⟨sameRight, sameFinal⟩ := r.deterministic actualRight
    cases RuntimeValue.word.inj sameRight
    cases sameFinal
    cases meaning.value_unique actualMeaning
    exact ⟨sameValue, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact (closedSourceExpressionEvaluates_strictWordBinary_iff notAnd notOr).mpr
      ⟨leftWord, rightWord, result, middle, rfl, l, r, meaning⟩

theorem original_saved_call_on_either_side_and_all_actual_endpoints
    (s : Nat → Syntax.SourceSpan) (savedOwner callerOwner : Resolved.DeclarationId)
    (different : callerOwner ≠ savedOwner) (onLeft : Bool)
    (savedNameTail callerNameTail : LocalNameTable)
    (savedTail callerTail : Resolved.LocalScope RuntimeValue)
    (oldSavedP : RuntimeValue) (argument other : Core.Word) (store : List RuntimeValue)
    (operator : Syntax.BinaryOp) (result : Core.Value)
    (meaning : StrictWordBinaryDenotes operator
      (if onLeft then argument else other) (if onLeft then other else argument) result) :
    let sn := savedNames savedOwner savedNameTail
    let sc := savedCaptured savedOwner oldSavedP savedTail
    let closure := RuntimeValue.sourceClosure (original s) savedOwner sn sc
    ClosedSourceExpressionEvaluates savedOwner sn sc store (original s) closure store ∧
    ∀ made madeStore,
      ClosedSourceExpressionEvaluates savedOwner sn sc store (original s) made madeStore →
      let cn := callerNames callerOwner callerNameTail
      let cc := callerCaptured callerOwner made argument other callerTail
      let parameter := Resolved.freshLocalId savedOwner (sn.map Prod.snd)
      made = closure ∧ madeStore = store ∧ callerOwner ≠ savedOwner ∧
      parameter ∉ sn.map Prod.snd ∧
      ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
        (ref s 15 "picked") made madeStore ∧
      ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
        (ref s 18 "p") (.word argument) madeStore ∧
      ClosedSourceBodyEvaluates savedOwner (("p", parameter) :: sn)
        ((parameter, .word argument) :: sc) madeStore (body s) (.word argument) madeStore ∧
      ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
        (call s) (.word argument) madeStore ∧
      ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
        (binary s onLeft operator) (RuntimeValue.ofCore result) madeStore ∧
      (∀ actual final, ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
        (binary s onLeft operator) actual final ↔
        actual = RuntimeValue.ofCore result ∧ final = madeStore) := by
  dsimp only
  let sn := savedNames savedOwner savedNameTail
  let sc := savedCaptured savedOwner oldSavedP savedTail
  let closure := RuntimeValue.sourceClosure (original s) savedOwner sn sc
  have created : ClosedSourceExpressionEvaluates savedOwner sn sc store
      (original s) closure store := .creation .inferred
  refine ⟨created, ?_⟩
  intro made madeStore returned
  obtain ⟨actualClosure, actualCreationStore⟩ := returned.deterministic created
  let cn := callerNames callerOwner callerNameTail
  let cc := callerCaptured callerOwner made argument other callerTail
  let calleeStore := madeStore
  let argumentStore := calleeStore
  have fetched : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (ref s 15 "picked") made calleeStore := .reference .head .head
  have fetchedClosure : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (ref s 15 "picked") closure calleeStore := by
    rw [← actualClosure]
    exact fetched
  have actualArgument : ClosedSourceExpressionEvaluates callerOwner cn cc calleeStore
      (ref s 18 "p") (.word argument) argumentStore :=
    .reference (.tail (by change "picked" ≠ "p"; decide) .head)
      (.tail (index_ne callerOwner (by decide)) .head)
  have actualOther : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (ref s 20 "other") (.word other) madeStore :=
    .reference (.tail (by change "picked" ≠ "other"; decide)
      (.tail (by change "p" ≠ "other"; decide) .head))
      (.tail (index_ne callerOwner (by decide)) (.tail (index_ne callerOwner (by decide)) .head))
  let parameter := Resolved.freshLocalId savedOwner (sn.map Prod.snd)
  have actualBody : ClosedSourceBodyEvaluates savedOwner (("p", parameter) :: sn)
      ((parameter, .word argument) :: sc) argumentStore (body s) (.word argument) argumentStore :=
    .expression (.reference .head .head)
  have invoked : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (call s) (.word argument) argumentStore :=
    .call (calleeStore := calleeStore) (argumentStore := argumentStore)
      .inferred fetchedClosure actualArgument actualBody
  have originalBinary : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (binary s onLeft operator) (RuntimeValue.ofCore result) madeStore := by
    cases onLeft
    · exact .strictWordBinary actualOther invoked meaning
    · exact .strictWordBinary invoked actualOther meaning
  refine ⟨actualClosure, actualCreationStore, different, Resolved.freshLocalId_not_mem _ _,
    fetched, actualArgument, actualBody, invoked, originalBinary, ?_⟩
  cases onLeft
  · exact strict_endpoints s operator actualOther invoked meaning
  · exact strict_endpoints s operator invoked actualOther meaning

theorem saved_calls_preserve_wrap_and_zero_division
    (s : Nat → Syntax.SourceSpan) (savedOwner callerOwner : Resolved.DeclarationId)
    (different : callerOwner ≠ savedOwner) (savedNameTail callerNameTail : LocalNameTable)
    (savedTail callerTail : Resolved.LocalScope RuntimeValue)
    (oldSavedP : RuntimeValue) (dividend : Core.Word) (store : List RuntimeValue) :
    let closure := RuntimeValue.sourceClosure (original s) savedOwner
      (savedNames savedOwner savedNameTail) (savedCaptured savedOwner oldSavedP savedTail)
    let cn := callerNames callerOwner callerNameTail
    ClosedSourceExpressionEvaluates callerOwner cn
      (callerCaptured callerOwner closure Core.Word.maximum (Core.Word.ofNatModulo 1) callerTail)
      store (binary s true .add) (.word Core.Word.zero) store ∧
    ClosedSourceExpressionEvaluates callerOwner cn
      (callerCaptured callerOwner closure Core.Word.zero dividend callerTail)
      store (binary s false .divide) (.word Core.Word.zero) store := by
  have wrapped := original_saved_call_on_either_side_and_all_actual_endpoints
    s savedOwner callerOwner different true savedNameTail callerNameTail savedTail callerTail
    oldSavedP Core.Word.maximum (Core.Word.ofNatModulo 1) store .add (.word Core.Word.zero) .add
  have divided := original_saved_call_on_either_side_and_all_actual_endpoints
    s savedOwner callerOwner different false savedNameTail callerNameTail savedTail callerTail
    oldSavedP Core.Word.zero dividend store .divide (.word Core.Word.zero) .divide
  obtain ⟨wrapCreation, wrapActual⟩ := wrapped
  obtain ⟨divideCreation, divideActual⟩ := divided
  obtain ⟨_, _, _, _, _, _, _, _, wrapResult, _⟩ := wrapActual _ _ wrapCreation
  obtain ⟨_, _, _, _, _, _, _, _, divideResult, _⟩ := divideActual _ _ divideCreation
  constructor
  · simpa only [RuntimeValue.ofCore] using wrapResult
  · simpa only [RuntimeValue.ofCore] using divideResult

end Tests.ClosedStrictWordBinarySavedCall
