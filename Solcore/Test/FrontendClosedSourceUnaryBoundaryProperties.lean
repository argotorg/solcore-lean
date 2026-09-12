import Solcore.Frontend.ClosedSourceUnaryProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties

/- Original saved-scope calls and actual-shape boundaries for unary primitives. -/
set_option autoImplicit false
namespace Tests.ClosedSourceUnaryBoundary
open Solcore Solcore.Frontend

private def one (op : Syntax.UnaryOp) (spans : Nat → Syntax.SourceSpan)
    (term : Syntax.Expr) : Syntax.Expr := ⟨spans 0, .unary ⟨spans 1, op⟩ term⟩
private def ref (spans : Nat → Syntax.SourceSpan) (name : String) : Syntax.Expr :=
  ⟨spans 2, .identifier ⟨spans 3, name⟩⟩
private def savedOriginal (spans : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨spans 4, .lambda (spans 5)
    ⟨spans 6, [⟨spans 7, .inferred ⟨spans 8, "ignored"⟩⟩]⟩ none
    ⟨spans 9, [⟨spans 10, .returnStmt (some (one .logicalNot spans (ref spans "saved")))⟩]⟩⟩
private def savedNames (owner : Resolved.DeclarationId) (tail : LocalNameTable) :=
  ("saved", (⟨owner, 7⟩ : Resolved.LocalId)) :: tail
private def savedCaptured (owner : Resolved.DeclarationId) (b : Bool)
    (tail : Resolved.LocalScope RuntimeValue) := (⟨owner, 7⟩, RuntimeValue.bool b) :: tail
private def callerNames (owner : Resolved.DeclarationId) (tail : LocalNameTable) :=
  ("picked", (⟨owner, 0⟩ : Resolved.LocalId)) :: ("saved", ⟨owner, 7⟩) :: tail
private def callerCaptured (owner : Resolved.DeclarationId) (made : RuntimeValue) (b : Bool)
    (tail : Resolved.LocalScope RuntimeValue) :=
  (⟨owner, 0⟩, made) :: (⟨owner, 7⟩, RuntimeValue.bool (!b)) :: tail
private def call (spans : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨spans 11, .call (ref (fun n => spans (n + 12)) "picked")
    ⟨spans 16, [⟨spans 17, .tuple ⟨spans 18, []⟩⟩]⟩⟩
private def outer (spans : Nat → Syntax.SourceSpan) :=
  one .logicalNot (fun n => spans (n + 19)) (call spans)

theorem saved_body_and_outer_call_images
    (spans : Nat → Syntax.SourceSpan) (callerOwner savedOwner : Resolved.DeclarationId)
    (different : callerOwner ≠ savedOwner) (input : Bool)
    (savedNameTail callerNameTail : LocalNameTable)
    (savedTail callerTail : Resolved.LocalScope RuntimeValue)
    (creationStore store : List RuntimeValue) :
    let original := savedOriginal spans
    let sn := savedNames savedOwner savedNameTail
    let sc := savedCaptured savedOwner input savedTail
    ClosedSourceExpressionEvaluates savedOwner sn sc creationStore original
      (.sourceClosure original savedOwner sn sc) creationStore ∧
    ∀ made, ClosedSourceExpressionEvaluates savedOwner sn sc creationStore
      original made creationStore →
      let cn := callerNames callerOwner callerNameTail
      let cc := callerCaptured callerOwner made input callerTail
      ClosedSourceExpressionEvaluates callerOwner cn cc store (call spans)
        (.bool (!input)) store ∧
      (∀ actual final, ClosedSourceExpressionEvaluates callerOwner cn cc store
        (outer spans) actual final ↔ actual = .bool input ∧ final = store) := by
  have created : ClosedSourceExpressionEvaluates savedOwner
      (savedNames savedOwner savedNameTail) (savedCaptured savedOwner input savedTail)
      creationStore (savedOriginal spans)
      (.sourceClosure (savedOriginal spans) savedOwner (savedNames savedOwner savedNameTail)
        (savedCaptured savedOwner input savedTail)) creationStore := .creation .inferred
  refine ⟨created, ?_⟩
  intro made returned
  obtain ⟨rfl, _⟩ := returned.deterministic created
  have fresh : Resolved.freshLocalId savedOwner
      ((savedNames savedOwner savedNameTail).map Prod.snd) ≠ ⟨savedOwner, 7⟩ := by
    intro same
    apply Resolved.freshLocalId_not_mem savedOwner
      ((savedNames savedOwner savedNameTail).map Prod.snd)
    rw [same]
    exact List.mem_cons_self
  have conflict : (⟨callerOwner, 7⟩ : Resolved.LocalId) ≠ ⟨savedOwner, 7⟩ := by
    intro same
    exact different (congrArg Resolved.LocalId.owner same)
  have invoked : ClosedSourceExpressionEvaluates callerOwner
      (callerNames callerOwner callerNameTail)
      (callerCaptured callerOwner
        (.sourceClosure (savedOriginal spans) savedOwner (savedNames savedOwner savedNameTail)
          (savedCaptured savedOwner input savedTail)) input callerTail)
      store (call spans) (.bool (!input)) store :=
    .call .inferred (.reference .head .head) .unit
      (.expression (.logicalNot
        (.reference (.tail (by change "ignored" ≠ "saved"; decide) .head) (.tail fresh .head))))
  refine ⟨invoked, ?_⟩
  intro actual final
  constructor
  · intro evaluated
    obtain ⟨b, child, same⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp evaluated
    obtain ⟨valueSame, rfl⟩ := child.deterministic invoked
    cases valueSame
    exact ⟨by simpa only [Bool.not_not] using same, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact closedSourceExpressionEvaluates_logicalNot_iff.mpr
      ⟨!input, invoked, by simp only [Bool.not_not]⟩

private def rejectNames (owner : Resolved.DeclarationId) (tail : LocalNameTable) :=
  ("w", (⟨owner, 0⟩ : Resolved.LocalId)) :: ("b", ⟨owner, 1⟩) ::
    ("u", ⟨owner, 2⟩) :: ("f", ⟨owner, 3⟩) :: tail
private def rejectCaptured (owner : Resolved.DeclarationId) (w : Core.Word) (b : Bool)
    (closure : Syntax.Expr) (tail : Resolved.LocalScope RuntimeValue) :=
  (⟨owner, 0⟩, RuntimeValue.word w) :: (⟨owner, 1⟩, .bool b) ::
    (⟨owner, 2⟩, .unit) :: (⟨owner, 3⟩, .sourceClosure closure owner [] []) :: tail
private def rejectedTerms (spans : Nat → Syntax.SourceSpan) : List Syntax.Expr :=
  [one .logicalNot spans (ref spans "w"), one .bitNot spans (ref spans "b"),
    one .logicalNot spans (one .bitNot (fun n => spans (n + 4)) (ref spans "w")),
    one .bitNot spans (one .logicalNot (fun n => spans (n + 4)) (ref spans "b")),
    one .logicalNot spans (ref spans "u"), one .bitNot spans (ref spans "u"),
    one .logicalNot spans (ref spans "f"), one .bitNot spans (ref spans "f")]
private def missingRef (spans : Nat → Syntax.SourceSpan) := ref spans "missing"

private theorem wrong_bool {owner names captured store operand value finalStore}
    (original : ClosedSourceExpressionEvaluates owner names captured store operand value finalStore)
    (wrong : ∀ b, value ≠ .bool b) (spans : Nat → Syntax.SourceSpan) :
    ∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names captured store
      (one .logicalNot spans operand) actual final := by
  intro actual final evaluated
  obtain ⟨b, child, _⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp evaluated
  exact wrong b (original.deterministic child).1

private theorem wrong_word {owner names captured store operand value finalStore}
    (original : ClosedSourceExpressionEvaluates owner names captured store operand value finalStore)
    (wrong : ∀ w, value ≠ .word w) (spans : Nat → Syntax.SourceSpan) :
    ∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names captured store
      (one .bitNot spans operand) actual final := by
  intro actual final evaluated
  obtain ⟨w, child, _⟩ := closedSourceExpressionEvaluates_bitNot_iff.mp evaluated
  exact wrong w (original.deterministic child).1

theorem wrong_missing_zero_and_nested_mismatch
    (spans : Nat → Syntax.SourceSpan) (owner : Resolved.DeclarationId)
    (nameTail : LocalNameTable) (captureTail : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (word : Core.Word) (choice : Bool)
    (closure : Syntax.Expr) :
    let names := rejectNames owner nameTail
    let captured := rejectCaptured owner word choice closure captureTail
    (∀ term ∈ rejectedTerms spans, ∀ budget,
      evaluateClosedSourceExpression? budget owner names captured store term = none ∧
      ∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names captured store
        term actual final) ∧
    (∀ op : Syntax.UnaryOp, ∀ budget,
      evaluateClosedSourceExpression? budget owner [] captureTail store
        (one op spans (missingRef spans)) = none) ∧
    (∀ term, evaluateClosedSourceExpression? 0 owner names captured store term = none) := by
  have w : ClosedSourceExpressionEvaluates owner (rejectNames owner nameTail)
      (rejectCaptured owner word choice closure captureTail) store
      (ref spans "w") (.word word) store := .reference .head .head
  have b : ClosedSourceExpressionEvaluates owner (rejectNames owner nameTail)
      (rejectCaptured owner word choice closure captureTail) store
      (ref spans "b") (.bool choice) store :=
    .reference (.tail (by change "w" ≠ "b"; decide) .head)
      (.tail (by intro h; have := congrArg Resolved.LocalId.binderIndex h; simp at this) .head)
  have u : ClosedSourceExpressionEvaluates owner (rejectNames owner nameTail)
      (rejectCaptured owner word choice closure captureTail) store (ref spans "u") .unit store :=
    .reference (.tail (by change "w" ≠ "u"; decide) (.tail (by change "b" ≠ "u"; decide) .head))
      (.tail (by intro h; have := congrArg Resolved.LocalId.binderIndex h; simp at this)
        (.tail (by intro h; have := congrArg Resolved.LocalId.binderIndex h; simp at this) .head))
  have f : ClosedSourceExpressionEvaluates owner (rejectNames owner nameTail)
      (rejectCaptured owner word choice closure captureTail) store (ref spans "f")
      (.sourceClosure closure owner [] []) store :=
    .reference (.tail (by change "w" ≠ "f"; decide) (.tail (by change "b" ≠ "f"; decide)
      (.tail (by change "u" ≠ "f"; decide) .head)))
      (.tail (by intro h; have := congrArg Resolved.LocalId.binderIndex h; simp at this)
        (.tail (by intro h; have := congrArg Resolved.LocalId.binderIndex h; simp at this)
          (.tail (by intro h; have := congrArg Resolved.LocalId.binderIndex h; simp at this) .head)))
  have innerW : ClosedSourceExpressionEvaluates owner (rejectNames owner nameTail)
      (rejectCaptured owner word choice closure captureTail) store
      (one .bitNot (fun n => spans (n + 4)) (ref spans "w")) (.word word.bitNot) store := .bitNot w
  have innerB : ClosedSourceExpressionEvaluates owner (rejectNames owner nameTail)
      (rejectCaptured owner word choice closure captureTail) store
      (one .logicalNot (fun n => spans (n + 4)) (ref spans "b")) (.bool (!choice)) store := .logicalNot b
  have innerRuns :
      evaluateClosedSourceExpression? 2 owner (rejectNames owner nameTail)
        (rejectCaptured owner word choice closure captureTail) store
        (one .bitNot (fun n => spans (n + 4)) (ref spans "w")) = some (.word word.bitNot, store) ∧
      evaluateClosedSourceExpression? 2 owner (rejectNames owner nameTail)
        (rejectCaptured owner word choice closure captureTail) store
        (one .logicalNot (fun n => spans (n + 4)) (ref spans "b")) = some (.bool (!choice), store) := by
    simp only [one, evaluateClosedSourceExpression?_logicalNot, evaluateClosedSourceExpression?_bitNot]
    simp [ref, evaluateClosedSourceExpression?, rejectNames, rejectCaptured,
      LocalNameTable.lookup?, Resolved.LocalScope.lookup?]
  refine ⟨?_, ?_, fun _ => by rw [evaluateClosedSourceExpression?]⟩
  · intro term member budget
    constructor
    · simp only [rejectedTerms, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases budget with _ | (_ | (_ | budget)) <;>
        simp only [one, evaluateClosedSourceExpression?_logicalNot, evaluateClosedSourceExpression?_bitNot] <;>
        simp [ref, evaluateClosedSourceExpression?, rejectNames, rejectCaptured,
          LocalNameTable.lookup?, Resolved.LocalScope.lookup?]
    · simp only [rejectedTerms, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact wrong_bool w (by intro _ h; cases h) spans
      · exact wrong_word b (by intro _ h; cases h) spans
      · exact wrong_bool innerW (by intro _ h; cases h) spans
      · exact wrong_word innerB (by intro _ h; cases h) spans
      · exact wrong_bool u (by intro _ h; cases h) spans
      · exact wrong_word u (by intro _ h; cases h) spans
      · exact wrong_bool f (by intro _ h; cases h) spans
      · exact wrong_word f (by intro _ h; cases h) spans
  · intro op budget
    cases op <;> rcases budget with _ | (_ | budget) <;>
      simp only [one, evaluateClosedSourceExpression?_logicalNot, evaluateClosedSourceExpression?_bitNot] <;>
      simp [missingRef, ref, evaluateClosedSourceExpression?, LocalNameTable.lookup?]

end Tests.ClosedSourceUnaryBoundary
