import Solcore.Frontend.ClosedSource

/- Independent child witnesses precede semantic rejection of every whole endpoint.
Both strict operands are required, including beside zero; mixed rows remain unrestricted. -/
set_option autoImplicit false
namespace Tests.ClosedStrictWordBinaryNegative
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .identifier name⟩
private def binary (span operatorSpan : Syntax.SourceSpan) (operator : Syntax.BinaryOp)
    (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨operatorSpan, operator⟩ right⟩

private theorem wrong_left {owner names captured store left value middle}
    (original : ClosedSourceExpressionEvaluates owner names captured store left value middle)
    (notWord : ∀ word, value ≠ .word word)
    {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
    (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr)
    (right : Syntax.Expr) :
    ∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names captured store
      (binary span operatorSpan operator left right) actual final := by
  intro actual final evaluated
  obtain ⟨lw, _, _, _, _, leftRun, _, _⟩ :=
    (closedSourceExpressionEvaluates_strictWordBinary_iff notAnd notOr).mp evaluated
  exact notWord lw (original.deterministic leftRun).1

private theorem wrong_right {owner names captured store left leftWord middle right value final}
    (leftOriginal : ClosedSourceExpressionEvaluates owner names captured store left (.word leftWord) middle)
    (rightOriginal : ClosedSourceExpressionEvaluates owner names captured middle right value final)
    (notWord : ∀ word, value ≠ .word word)
    {span operatorSpan : Syntax.SourceSpan} {operator : Syntax.BinaryOp}
    (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr) :
    ∀ actual actualFinal, ¬ ClosedSourceExpressionEvaluates owner names captured store
      (binary span operatorSpan operator left right) actual actualFinal := by
  intro actual actualFinal evaluated
  obtain ⟨_, rw, _, actualMiddle, _, leftRun, rightRun, _⟩ :=
    (closedSourceExpressionEvaluates_strictWordBinary_iff notAnd notOr).mp evaluated
  have sameMiddle := (leftRun.deterministic leftOriginal).2
  cases sameMiddle
  exact notWord rw (rightOriginal.deterministic rightRun).1

private theorem missing_reference {owner names captured store final actual span name}
    (missing : LocalNameTable.lookup? names name.value = none ∨
      ∃ id, LocalNameTable.Lookup names name.value id ∧ Resolved.LocalScope.lookup? captured id = none) :
    ¬ ClosedSourceExpressionEvaluates owner names captured store (reference span name) actual final := by
  intro evaluated
  cases evaluated with
  | reference named found =>
      rcases missing with missing | ⟨id, correctName, missing⟩
      · have accepted := LocalNameTable.lookup?_iff.mpr named
        rw [missing] at accepted
        cases accepted
      · cases named.id_unique correctName
        have accepted := Resolved.LocalScope.lookup?_iff.mpr found
        rw [missing] at accepted
        cases accepted
  | creation shape => cases shape

theorem non_word_reference_on_either_side_never_succeeds
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span operatorSpan goodSpan badSpan : Syntax.SourceSpan)
    (operator : Syntax.BinaryOp) (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr)
    (goodName badName : Syntax.Identifier) (goodId badId : Resolved.LocalId)
    (word : Core.Word) (bad : RuntimeValue) (notWord : ∀ w, bad ≠ .word w)
    (goodNamed : LocalNameTable.Lookup names goodName.value goodId)
    (badNamed : LocalNameTable.Lookup names badName.value badId)
    (goodFound : Resolved.LocalScope.Lookup captured goodId (.word word))
    (badFound : Resolved.LocalScope.Lookup captured badId bad) :
    ClosedSourceExpressionEvaluates owner names captured store (reference goodSpan goodName) (.word word) store ∧
    ClosedSourceExpressionEvaluates owner names captured store (reference badSpan badName) bad store ∧
    (∀ actual final,
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span operatorSpan operator (reference badSpan badName) (reference goodSpan goodName)) actual final) ∧
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span operatorSpan operator (reference goodSpan goodName) (reference badSpan badName)) actual final)) := by
  have goodOriginal : ClosedSourceExpressionEvaluates owner names captured store
      (reference goodSpan goodName) (.word word) store := .reference goodNamed goodFound
  have badOriginal : ClosedSourceExpressionEvaluates owner names captured store
      (reference badSpan badName) bad store := .reference badNamed badFound
  refine ⟨goodOriginal, badOriginal, ?_⟩
  intro actual final
  exact ⟨wrong_left badOriginal notWord notAnd notOr _ actual final,
    wrong_right goodOriginal badOriginal notWord notAnd notOr actual final⟩

theorem missing_reference_on_either_side_never_succeeds
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span operatorSpan missingSpan : Syntax.SourceSpan)
    (operator : Syntax.BinaryOp) (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr)
    (other : Syntax.Expr) (missingName : Syntax.Identifier)
    (missing : LocalNameTable.lookup? names missingName.value = none ∨
      ∃ id, LocalNameTable.Lookup names missingName.value id ∧ Resolved.LocalScope.lookup? captured id = none) :
    ∀ actual final,
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span operatorSpan operator other (reference missingSpan missingName)) actual final) ∧
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span operatorSpan operator (reference missingSpan missingName) other) actual final) := by
  intro actual final
  constructor
  · intro evaluated
    obtain ⟨_, _, _, _, _, _, rightRun, _⟩ :=
      (closedSourceExpressionEvaluates_strictWordBinary_iff notAnd notOr).mp evaluated
    exact missing_reference missing rightRun
  · intro evaluated
    obtain ⟨_, _, _, _, _, leftRun, _, _⟩ :=
      (closedSourceExpressionEvaluates_strictWordBinary_iff notAnd notOr).mp evaluated
    exact missing_reference missing leftRun

theorem zero_never_skips_a_missing_reference_on_either_side
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span operatorSpan zeroSpan missingSpan : Syntax.SourceSpan)
    (operator : Syntax.BinaryOp) (notAnd : operator ≠ .logicalAnd) (notOr : operator ≠ .logicalOr)
    (zeroName missingName : Syntax.Identifier) (zeroId : Resolved.LocalId)
    (zeroNamed : LocalNameTable.Lookup names zeroName.value zeroId)
    (zeroFound : Resolved.LocalScope.Lookup captured zeroId (.word Core.Word.zero))
    (missing : LocalNameTable.lookup? names missingName.value = none ∨
      ∃ id, LocalNameTable.Lookup names missingName.value id ∧ Resolved.LocalScope.lookup? captured id = none) :
    ClosedSourceExpressionEvaluates owner names captured store
      (reference zeroSpan zeroName) (.word Core.Word.zero) store ∧
    (∀ actual final,
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span operatorSpan operator (reference zeroSpan zeroName) (reference missingSpan missingName)) actual final) ∧
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span operatorSpan operator (reference missingSpan missingName) (reference zeroSpan zeroName)) actual final)) := by
  have zeroOriginal : ClosedSourceExpressionEvaluates owner names captured store
      (reference zeroSpan zeroName) (.word Core.Word.zero) store := .reference zeroNamed zeroFound
  exact ⟨zeroOriginal, missing_reference_on_either_side_never_succeeds owner names captured store
    span operatorSpan missingSpan operator notAnd notOr (reference zeroSpan zeroName) missingName missing⟩

end Tests.ClosedStrictWordBinaryNegative
