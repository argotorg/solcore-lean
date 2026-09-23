import Solcore.Frontend.ClosedSource

/- A selected lambda captures
the original saved rows; the actual returned closure and store are reused by a
foreign caller. The argument named p is evaluated in the caller, then the fresh
parameter p shadows the saved p. Capture tails and runtime payloads are arbitrary.
No typing, NoDup, Core correspondence, exact-depth or parser claim is made. -/
set_option autoImplicit false
open Solcore Solcore.Frontend
namespace Tests.ClosedShortCircuitSavedCall

private def ref (s : Nat → Syntax.SourceSpan) (i : Nat) (name : String) : Syntax.Expr :=
  ⟨s i, .identifier ⟨s (i + 1), name⟩⟩
private def selected (b : Bool) (s : Nat → Syntax.SourceSpan) (l r : Syntax.Expr) : Syntax.Expr :=
  ⟨s 0, .binary l ⟨s 1, if b then .logicalAnd else .logicalOr⟩ r⟩
private def skipped (b : Bool) (s : Nat → Syntax.SourceSpan) (l r : Syntax.Expr) : Syntax.Expr :=
  ⟨s 0, .binary l ⟨s 1, if b then .logicalOr else .logicalAnd⟩ r⟩
private def body (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 10, [⟨s 11, .returnStmt (some (ref s 12 "p"))⟩]⟩
private def original (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 4, .lambda (s 5) ⟨s 6, [⟨s 7, .inferred ⟨s 8, "p"⟩⟩]⟩ none (body s)⟩
private def call (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 14, .call (ref s 15 "picked") ⟨s 17, [ref s 18 "p"]⟩⟩
private def savedNames (owner : Resolved.DeclarationId) (tail : LocalNameTable) : LocalNameTable :=
  ("guard", ⟨owner, 0⟩) :: ("p", ⟨owner, 2⟩) :: tail
private def savedCaptured (owner : Resolved.DeclarationId) (b : Bool) (old : RuntimeValue)
    (tail : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  (⟨owner, 0⟩, .bool b) :: (⟨owner, 2⟩, old) :: tail
private def callerNames (owner : Resolved.DeclarationId) : LocalNameTable :=
  [("guard", ⟨owner, 0⟩), ("picked", ⟨owner, 1⟩), ("p", ⟨owner, 2⟩)]
private def callerCaptured (owner : Resolved.DeclarationId) (b : Bool) (made argument : RuntimeValue)
    (tail : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  (⟨owner, 0⟩, .bool b) :: (⟨owner, 1⟩, made) :: (⟨owner, 2⟩, argument) :: tail

private theorem index_ne (owner : Resolved.DeclarationId) {i j : Nat} (different : i ≠ j) :
    (⟨owner, i⟩ : Resolved.LocalId) ≠ ⟨owner, j⟩ := by
  intro equal
  exact different (congrArg Resolved.LocalId.binderIndex equal)

private theorem endpoint {owner names captured store source value finalStore}
    (original : ClosedSourceExpressionEvaluates owner names captured store source value finalStore) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store source actual final ↔
      actual = value ∧ final = finalStore := by
  intro actual final
  constructor
  · exact fun evaluated => evaluated.deterministic original
  · rintro ⟨rfl, rfl⟩
    exact original

private theorem selected_original {owner names captured store middle final left right value}
    (b : Bool) (s : Nat → Syntax.SourceSpan)
    (l : ClosedSourceExpressionEvaluates owner names captured store left (.bool b) middle)
    (r : ClosedSourceExpressionEvaluates owner names captured middle right value final) :
    ClosedSourceExpressionEvaluates owner names captured store (selected b s left right) value final := by
  cases b
  · exact .orFalse l r
  · exact .andTrue l r

private theorem skipped_original {owner names captured store final left right}
    (b : Bool) (s : Nat → Syntax.SourceSpan)
    (l : ClosedSourceExpressionEvaluates owner names captured store left (.bool b) final) :
    ClosedSourceExpressionEvaluates owner names captured store (skipped b s left right) (.bool b) final := by
  cases b
  · exact .andFalse l
  · exact .orTrue l

private theorem selected_iff {owner names captured store middle left right value final}
    (b : Bool) (s : Nat → Syntax.SourceSpan)
    (l : ClosedSourceExpressionEvaluates owner names captured store left (.bool b) middle) :
    ClosedSourceExpressionEvaluates owner names captured store (selected b s left right) value final ↔
      ClosedSourceExpressionEvaluates owner names captured middle right value final := by
  cases b
  · constructor
    · intro evaluated
      rcases closedSourceExpressionEvaluates_logicalOr_iff.mp evaluated with
        ⟨_, forced⟩ | ⟨actualMiddle, forced, child⟩
      · cases (l.deterministic forced).1
      · obtain ⟨_, sameStore⟩ := l.deterministic forced
        rw [← sameStore] at child
        exact child
    · intro child
      exact closedSourceExpressionEvaluates_logicalOr_iff.mpr (.inr ⟨middle, l, child⟩)
  · constructor
    · intro evaluated
      rcases closedSourceExpressionEvaluates_logicalAnd_iff.mp evaluated with
        ⟨_, forced⟩ | ⟨actualMiddle, forced, child⟩
      · cases (l.deterministic forced).1
      · obtain ⟨_, sameStore⟩ := l.deterministic forced
        rw [← sameStore] at child
        exact child
    · intro child
      exact closedSourceExpressionEvaluates_logicalAnd_iff.mpr (.inr ⟨middle, l, child⟩)

private theorem missing {owner captured store value final} (s : Nat → Syntax.SourceSpan) :
    ¬ ClosedSourceExpressionEvaluates owner (callerNames owner) captured store
      (ref s 20 "missing") value final := by
  intro evaluated
  cases evaluated with
  | creation shape => cases shape
  | reference named _ =>
      have impossible := LocalNameTable.lookup?_iff.mpr named
      simp [callerNames, LocalNameTable.lookup?] at impossible

theorem selected_returned_closure_shadow_call_and_all_actual_endpoints
    (s : Nat → Syntax.SourceSpan) (savedOwner callerOwner : Resolved.DeclarationId)
    (different : callerOwner ≠ savedOwner) (choice : Bool)
    (savedNameTail : LocalNameTable) (savedTail callerTail : Resolved.LocalScope RuntimeValue)
    (oldSavedP argument : RuntimeValue) (creationStore : List RuntimeValue) :
    let sn := savedNames savedOwner savedNameTail
    let sc := savedCaptured savedOwner choice oldSavedP savedTail
    let creation := selected choice s (ref s 2 "guard") (original s)
    let closure := RuntimeValue.sourceClosure (original s) savedOwner sn sc
    ClosedSourceExpressionEvaluates savedOwner sn sc creationStore creation closure creationStore ∧
    (∀ actual final, ClosedSourceExpressionEvaluates savedOwner sn sc creationStore creation actual final ↔
      actual = closure ∧ final = creationStore) ∧
    ∀ made madeStore, ClosedSourceExpressionEvaluates savedOwner sn sc creationStore creation made madeStore →
      let cn := callerNames callerOwner
      let cc := callerCaptured callerOwner (!choice) made argument callerTail
      let run := selected (!choice) s (ref s 2 "guard") (call s)
      let skip := skipped (!choice) s (ref s 2 "guard") (ref s 20 "missing")
      callerOwner ≠ savedOwner ∧ made = closure ∧ madeStore = creationStore ∧
      ClosedSourceExpressionEvaluates callerOwner cn cc madeStore run argument madeStore ∧
      ClosedSourceExpressionEvaluates callerOwner cn cc madeStore skip (.bool (!choice)) madeStore ∧
      (∀ actual final, ClosedSourceExpressionEvaluates callerOwner cn cc madeStore run actual final ↔
        actual = argument ∧ final = madeStore) ∧
      (∀ actual final, ClosedSourceExpressionEvaluates callerOwner cn cc madeStore skip actual final ↔
        actual = .bool (!choice) ∧ final = madeStore) ∧
      (∀ actual final, ¬ ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
        (ref s 20 "missing") actual final) ∧
      (∀ budget actual final,
        evaluateClosedSourceExpression? budget callerOwner cn cc madeStore run = some (actual, final) →
        actual = argument ∧ final = madeStore) ∧
      (∃ required, ∀ budget, required ≤ budget →
        evaluateClosedSourceExpression? budget callerOwner cn cc madeStore run = some (argument, madeStore)) := by
  dsimp only
  let sn := savedNames savedOwner savedNameTail
  let sc := savedCaptured savedOwner choice oldSavedP savedTail
  let closure := RuntimeValue.sourceClosure (original s) savedOwner sn sc
  have savedLeft : ClosedSourceExpressionEvaluates savedOwner sn sc creationStore
      (ref s 2 "guard") (.bool choice) creationStore := .reference .head .head
  have literalCreation : ClosedSourceExpressionEvaluates savedOwner sn sc creationStore
      (original s) closure creationStore := .creation .inferred
  have created := selected_original choice s savedLeft literalCreation
  have creationExact : ∀ actual final, ClosedSourceExpressionEvaluates savedOwner sn sc creationStore
      (selected choice s (ref s 2 "guard") (original s)) actual final ↔
      actual = closure ∧ final = creationStore := by
    intro actual final
    exact (selected_iff choice s savedLeft).trans (endpoint literalCreation actual final)
  refine ⟨created, creationExact, ?_⟩
  intro made madeStore returned
  obtain ⟨actualClosure, actualCreationStore⟩ := (creationExact made madeStore).mp returned
  let cn := callerNames callerOwner
  let cc := callerCaptured callerOwner (!choice) made argument callerTail
  let calleeStore := madeStore
  let argumentStore := calleeStore
  have callerLeft : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (ref s 2 "guard") (.bool (!choice)) madeStore := .reference .head .head
  have fetchedActual : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (ref s 15 "picked") made calleeStore :=
    .reference (.tail (by change "guard" ≠ "picked"; decide) .head)
      (.tail (index_ne callerOwner (by decide)) .head)
  have fetchedClosure : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (ref s 15 "picked") closure calleeStore := by
    rw [← actualClosure]
    exact fetchedActual
  have argumentEvaluation : ClosedSourceExpressionEvaluates callerOwner cn cc calleeStore
      (ref s 18 "p") argument argumentStore :=
    .reference (.tail (by change "guard" ≠ "p"; decide)
      (.tail (by change "picked" ≠ "p"; decide) .head))
      (.tail (index_ne callerOwner (by decide)) (.tail (index_ne callerOwner (by decide)) .head))
  let parameter := Resolved.freshLocalId savedOwner (sn.map Prod.snd)
  have bodyEvaluation : ClosedSourceBodyEvaluates savedOwner (("p", parameter) :: sn)
      ((parameter, argument) :: sc) argumentStore (body s) argument argumentStore :=
    .expression (.reference .head .head)
  have invoked : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore (call s) argument argumentStore :=
    .call (calleeStore := calleeStore) (argumentStore := argumentStore)
      .inferred fetchedClosure argumentEvaluation bodyEvaluation
  have selectedCall := selected_original (!choice) s callerLeft invoked
  have skippedMissing : ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (skipped (!choice) s (ref s 2 "guard") (ref s 20 "missing")) (.bool (!choice)) madeStore :=
    skipped_original (!choice) s callerLeft
  have callExact : ∀ actual final, ClosedSourceExpressionEvaluates callerOwner cn cc madeStore
      (selected (!choice) s (ref s 2 "guard") (call s)) actual final ↔
      actual = argument ∧ final = madeStore := by
    intro actual final
    exact (selected_iff (!choice) s callerLeft).trans (endpoint invoked actual final)
  refine ⟨different, actualClosure, actualCreationStore, selectedCall, skippedMissing,
    callExact, endpoint skippedMissing, ?_, ?_, ?_⟩
  · intro actual final
    exact missing s
  · intro budget actual final accepted
    exact (callExact actual final).mp (evaluateClosedSourceExpression?_sound accepted)
  · exact evaluateClosedSourceExpression?_eventually_complete selectedCall

end Tests.ClosedShortCircuitSavedCall
