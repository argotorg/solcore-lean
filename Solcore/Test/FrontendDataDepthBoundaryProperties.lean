import Solcore.Frontend.ClosedSource
import Solcore.Test.FrontendStrictWordDataBoundaryProperties

/- Original rejection and child witnesses precede the finite-depth decision laws.
Mixed stores and duplicate lexical/runtime rows are unrestricted throughout.
Zero assigned to unsupported syntax is not a bound for successful source calls. -/
set_option autoImplicit false
namespace Tests.DataDepthBoundaries
open Solcore Solcore.Frontend

private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨s,.identifier name⟩
private def bin (s opSpan : Syntax.SourceSpan) (op : Syntax.BinaryOp)
    (left right : Syntax.Expr) : Syntax.Expr := ⟨s,.binary left ⟨opSpan,op⟩ right⟩
private def Failed (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.LocalScope RuntimeValue) (st : List RuntimeValue) (x : Syntax.Expr) : Prop :=
  evaluateClosedSourceExpression? (closedSourceDataDepthBound x) o n e st x = none ∧
  (∀ budget, evaluateClosedSourceExpression? budget o n e st x = none) ∧
  ∀ value final, ¬ ClosedSourceExpressionEvaluates o n e st x value final

variable (owner : Resolved.DeclarationId) (names : LocalNameTable)
  (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)

private theorem reject (x : Syntax.Expr) (gate : ClosedSourceDataExpression x)
    (original : ∀ value final, ¬ ClosedSourceExpressionEvaluates owner names captured store x value final) :
    Failed owner names captured store x := by
  have absence := (gate.evaluate_depth_none_iff owner names captured store (Nat.le_refl _)).mpr original
  exact ⟨absence,(gate.evaluate_depth_none_iff_all_budgets owner names captured store).mp absence,
    (gate.evaluate_depth_none_iff owner names captured store (Nat.le_refl _)).mp absence⟩

theorem missing_name_or_capture_at_every_depth (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (missing : LocalNameTable.lookup? names name.value = none ∨
      ∃ id, LocalNameTable.Lookup names name.value id ∧ Resolved.LocalScope.lookup? captured id = none) :
    ClosedSourceDataExpression (ref s name) ∧ closedSourceDataDepthBound (ref s name) = 1 ∧
    Failed owner names captured store (ref s name) := by
  have original : ∀ value final, ¬ ClosedSourceExpressionEvaluates owner names captured store (ref s name) value final := by
    intro value final evaluated
    cases evaluated with
    | reference named found =>
        rcases missing with absent | ⟨id,correct,absent⟩
        · have accepted := LocalNameTable.lookup?_iff.mpr named
          rw [absent] at accepted; cases accepted
        · cases named.id_unique correct
          have accepted := Resolved.LocalScope.lookup?_iff.mpr found
          rw [absent] at accepted; cases accepted
    | creation shape => cases shape
  exact ⟨.reference,by simp [ref,closedSourceDataDepthBound],reject owner names captured store _ .reference original⟩

theorem missing_first_capture_never_uses_a_later_duplicate
    (s : Syntax.SourceSpan) (first later : Resolved.LocalId) (different : later ≠ first)
    (word : Core.Word) (missing : Resolved.LocalScope.lookup? captured first = none) :
    let n := ("x",first)::("x",later)::names
    let e := (later,.word word)::captured
    ClosedSourceDataExpression (ref s ⟨s,"x"⟩) ∧
    closedSourceDataDepthBound (ref s ⟨s,"x"⟩) = 1 ∧
    Failed owner n e store (ref s ⟨s,"x"⟩) := by
  dsimp only
  have absent : Resolved.LocalScope.lookup? ((later,RuntimeValue.word word)::captured) first = none := by
    simp only [Resolved.LocalScope.lookup?,if_neg different,missing]
  exact missing_name_or_capture_at_every_depth owner _ _ store s ⟨s,"x"⟩
    (.inr ⟨first,.head,absent⟩)

theorem strings_at_every_depth (s : Syntax.SourceSpan) (text : String) :
    ClosedSourceDataExpression ⟨s,.literal ⟨s,.string text⟩⟩ ∧
    closedSourceDataDepthBound ⟨s,.literal ⟨s,.string text⟩⟩ = 1 ∧
    Failed owner names captured store ⟨s,.literal ⟨s,.string text⟩⟩ := by
  have original : ∀ value final, ¬ ClosedSourceExpressionEvaluates owner names captured store
      ⟨s,.literal ⟨s,.string text⟩⟩ value final := by
    intro value final evaluated
    cases evaluated with
    | wordLiteral meaning => cases meaning
    | creation shape => cases shape
  exact ⟨.literal,by simp [closedSourceDataDepthBound],reject owner names captured store _ .literal original⟩

theorem overflow_at_every_depth (s : Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
    (natural : Nat) (meaning : NumericLiteralDenotes literal.value natural)
    (overflow : Core.wordModulus ≤ natural) :
    ClosedSourceDataExpression ⟨s,.literal literal⟩ ∧
    closedSourceDataDepthBound ⟨s,.literal literal⟩ = 1 ∧
    Failed owner names captured store ⟨s,.literal literal⟩ := by
  have original : ∀ value final, ¬ ClosedSourceExpressionEvaluates owner names captured store
      ⟨s,.literal literal⟩ value final := by
    intro value final evaluated
    cases evaluated with
    | @wordLiteral _ _ _ _ _ _ word wordMeaning =>
        have same := NumericLiteralDenotes.value_unique meaning wordMeaning
        have small := word.isLt
        omega
    | creation shape => cases shape
  exact ⟨.literal,by simp [closedSourceDataDepthBound],reject owner names captured store _ .literal original⟩

theorem actual_modulus_spelling_at_every_depth (s : Syntax.SourceSpan) :
    let literal : Syntax.CoreLiteral :=
      ⟨s,.hexadecimal "0x10000000000000000000000000000000000000000000000000000000000000000"⟩
    NumericLiteralDenotes literal.value Core.wordModulus ∧
    ClosedSourceDataExpression ⟨s,.literal literal⟩ ∧
    closedSourceDataDepthBound ⟨s,.literal literal⟩ = 1 ∧
    Failed owner names captured store ⟨s,.literal literal⟩ := by
  dsimp only
  have natural : NumericLiteralDenotes
      (.hexadecimal "0x10000000000000000000000000000000000000000000000000000000000000000")
      Core.wordModulus := numericLiteralValue?_sound (by decide)
  exact ⟨natural,overflow_at_every_depth owner names captured store s _ _ natural (Nat.le_refl _)⟩

theorem non_word_on_either_side_at_every_depth
    (s opSpan goodSpan badSpan : Syntax.SourceSpan) (op : Syntax.BinaryOp)
    (notAnd : op ≠ .logicalAnd) (notOr : op ≠ .logicalOr)
    (goodName badName : Syntax.Identifier) (goodId badId : Resolved.LocalId)
    (word : Core.Word) (bad : RuntimeValue) (notWord : ∀ w, bad ≠ .word w)
    (goodNamed : LocalNameTable.Lookup names goodName.value goodId)
    (badNamed : LocalNameTable.Lookup names badName.value badId)
    (goodFound : Resolved.LocalScope.Lookup captured goodId (.word word))
    (badFound : Resolved.LocalScope.Lookup captured badId bad) :
    let left := bin s opSpan op (ref badSpan badName) (ref goodSpan goodName)
    let right := bin s opSpan op (ref goodSpan goodName) (ref badSpan badName)
    ClosedSourceExpressionEvaluates owner names captured store (ref goodSpan goodName) (.word word) store ∧
    ClosedSourceExpressionEvaluates owner names captured store (ref badSpan badName) bad store ∧
    ClosedSourceDataExpression left ∧ ClosedSourceDataExpression right ∧
    closedSourceDataDepthBound left = 2 ∧ closedSourceDataDepthBound right = 2 ∧
    Failed owner names captured store left ∧ Failed owner names captured store right := by
  dsimp only
  obtain ⟨lg,rg,good,badRun,original⟩ := StrictWordDataBoundary.admitted_non_word_operands_still_never_succeed
    owner names captured store s opSpan goodSpan badSpan op notAnd notOr
    goodName badName goodId badId word bad notWord goodNamed badNamed goodFound badFound
  exact ⟨good,badRun,lg,rg,by simp [bin,ref,closedSourceDataDepthBound],by simp [bin,ref,closedSourceDataDepthBound],
    reject owner names captured store _ lg (fun v st => (original v st).1),
    reject owner names captured store _ rg (fun v st => (original v st).2)⟩

theorem duplicate_first_non_word_hides_later_word
    (s : Syntax.SourceSpan) (first later : Resolved.LocalId) (word : Core.Word)
    (bad : RuntimeValue) (notWord : ∀ w, bad ≠ .word w) :
    let n := ("x",first)::("x",later)::names
    let e := (first,bad)::(first,.word word)::(later,.word word)::captured
    let x := ref s ⟨s,"x"⟩
    ClosedSourceExpressionEvaluates owner n e store x bad store ∧
    ClosedSourceDataExpression (bin s s .multiply x x) ∧
    Failed owner n e store (bin s s .multiply x x) := by
  dsimp only
  have head : ClosedSourceExpressionEvaluates owner (("x",first)::("x",later)::names)
      ((first,bad)::(first,.word word)::(later,.word word)::captured) store (ref s ⟨s,"x"⟩) bad store :=
    .reference .head .head
  have gate : ClosedSourceDataExpression (bin s s .multiply (ref s ⟨s,"x"⟩) (ref s ⟨s,"x"⟩)) :=
    .strictWordBinary .reference .reference (by decide) (by decide)
  refine ⟨head,gate,reject owner _ _ store _ gate ?_⟩
  intro actual final evaluated
  obtain ⟨lw,_,_,_,_,left,_,_⟩ :=
    (closedSourceExpressionEvaluates_strictWordBinary_iff (by decide) (by decide)).mp evaluated
  exact notWord lw (head.deterministic left).1

theorem zero_still_needs_both_operands_at_every_depth
    (s opSpan zeroSpan missingSpan : Syntax.SourceSpan) (op : Syntax.BinaryOp)
    (notAnd : op ≠ .logicalAnd) (notOr : op ≠ .logicalOr)
    (zeroName missingName : Syntax.Identifier) (zeroId : Resolved.LocalId)
    (zeroNamed : LocalNameTable.Lookup names zeroName.value zeroId)
    (zeroFound : Resolved.LocalScope.Lookup captured zeroId (.word Core.Word.zero))
    (missing : LocalNameTable.lookup? names missingName.value = none ∨
      ∃ id, LocalNameTable.Lookup names missingName.value id ∧ Resolved.LocalScope.lookup? captured id = none) :
    let left := bin s opSpan op (ref zeroSpan zeroName) (ref missingSpan missingName)
    let right := bin s opSpan op (ref missingSpan missingName) (ref zeroSpan zeroName)
    ClosedSourceExpressionEvaluates owner names captured store (ref zeroSpan zeroName) (.word Core.Word.zero) store ∧
    ClosedSourceDataExpression left ∧ ClosedSourceDataExpression right ∧
    closedSourceDataDepthBound left = 2 ∧ closedSourceDataDepthBound right = 2 ∧
    Failed owner names captured store left ∧ Failed owner names captured store right := by
  dsimp only
  obtain ⟨lg,rg,zero,original⟩ := StrictWordDataBoundary.admitted_zero_never_skips_a_missing_operand
    owner names captured store s opSpan zeroSpan missingSpan op notAnd notOr
    zeroName missingName zeroId zeroNamed zeroFound missing
  exact ⟨zero,lg,rg,by simp [bin,ref,closedSourceDataDepthBound],by simp [bin,ref,closedSourceDataDepthBound],
    reject owner names captured store _ lg (fun v st => (original v st).1),
    reject owner names captured store _ rg (fun v st => (original v st).2)⟩

private def body (s : Syntax.SourceSpan) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (ref s ⟨s,"p"⟩))⟩]⟩
private def identity (s : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,.inferred ⟨s,"p"⟩⟩]⟩ none (body s)⟩
private def applied (s : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s,.call (identity s) ⟨s,[⟨s,.tuple ⟨s,[]⟩⟩]⟩⟩

theorem zero_for_unsupported_shapes_does_not_decide_success (s : Syntax.SourceSpan) :
    let closure := RuntimeValue.sourceClosure (identity s) owner names captured
    closedSourceDataDepthBound (identity s) = 0 ∧ closedSourceDataDepthBound (applied s) = 0 ∧
    (¬ ClosedSourceDataExpression (identity s)) ∧ (¬ ClosedSourceDataExpression (applied s)) ∧
    ClosedSourceExpressionEvaluates owner names captured store (identity s) closure store ∧
    ClosedSourceExpressionEvaluates owner names captured store (applied s) .unit store ∧
    evaluateClosedSourceExpression? (closedSourceDataDepthBound (identity s)) owner names captured store (identity s) = none ∧
    evaluateClosedSourceExpression? (closedSourceDataDepthBound (applied s)) owner names captured store (applied s) = none ∧
    evaluateClosedSourceExpression? 1 owner names captured store (identity s) = some (closure,store) ∧
    evaluateClosedSourceExpression? 3 owner names captured store (applied s) = some (.unit,store) := by
  dsimp only
  have created : ClosedSourceExpressionEvaluates owner names captured store (identity s)
      (.sourceClosure (identity s) owner names captured) store := .creation .inferred
  have argument : ClosedSourceExpressionEvaluates owner names captured store ⟨s,.tuple ⟨s,[]⟩⟩ .unit store := .unit
  have beta : ClosedSourceBodyEvaluates owner
      (("p",Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),.unit)::captured) store (body s) .unit store :=
    .expression (.reference .head .head)
  have called : ClosedSourceExpressionEvaluates owner names captured store (applied s) .unit store :=
    .call .inferred created argument beta
  refine ⟨by simp [identity,closedSourceDataDepthBound],by simp [applied,closedSourceDataDepthBound],
    (by intro g; cases g),(by intro g; cases g),created,called,
    by simp [identity,closedSourceDataDepthBound,evaluateClosedSourceExpression?],
    by simp [applied,closedSourceDataDepthBound,evaluateClosedSourceExpression?],?_,?_⟩
  · simp only [identity,evaluateClosedSourceExpression?,sourceUnaryLambdaShape?,bind,Option.bind_some,pure]
  · simp [applied,identity,body,ref,evaluateClosedSourceExpression?,evaluateClosedSourceBody?,
      sourceUnaryLambdaShape?,LocalNameTable.lookup?,Resolved.LocalScope.lookup?]

end Tests.DataDepthBoundaries
