import Solcore.Frontend.ClosedSourceDataExpression
import Solcore.Test.FrontendClosedStrictWordBinaryNegativeProperties
import Solcore.Frontend.LocalExpression

/- Admission is recursive syntax, not runtime typing, successful evaluation or
whole name resolution. Conversely original calls can succeed outside this gate. -/
set_option autoImplicit false
namespace Tests.StrictWordDataBoundary
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def binary (span opSpan : Syntax.SourceSpan) (op : Syntax.BinaryOp)
    (left right : Syntax.Expr) : Syntax.Expr := ⟨span,.binary left ⟨opSpan,op⟩ right⟩

theorem admitted_non_word_operands_still_never_succeed
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span opSpan goodSpan badSpan : Syntax.SourceSpan)
    (op : Syntax.BinaryOp) (notAnd : op ≠ .logicalAnd) (notOr : op ≠ .logicalOr)
    (goodName badName : Syntax.Identifier) (goodId badId : Resolved.LocalId)
    (word : Core.Word) (bad : RuntimeValue) (notWord : ∀ w, bad ≠ .word w)
    (goodNamed : LocalNameTable.Lookup names goodName.value goodId)
    (badNamed : LocalNameTable.Lookup names badName.value badId)
    (goodFound : Resolved.LocalScope.Lookup captured goodId (.word word))
    (badFound : Resolved.LocalScope.Lookup captured badId bad) :
    ClosedSourceDataExpression (binary span opSpan op
      (reference badSpan badName) (reference goodSpan goodName)) ∧
    ClosedSourceDataExpression (binary span opSpan op
      (reference goodSpan goodName) (reference badSpan badName)) ∧
    ClosedSourceExpressionEvaluates owner names captured store
      (reference goodSpan goodName) (.word word) store ∧
    ClosedSourceExpressionEvaluates owner names captured store
      (reference badSpan badName) bad store ∧
    ∀ actual final,
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span opSpan op (reference badSpan badName) (reference goodSpan goodName)) actual final) ∧
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span opSpan op (reference goodSpan goodName) (reference badSpan badName)) actual final) := by
  have independent := ClosedStrictWordBinaryNegative.non_word_reference_on_either_side_never_succeeds
    owner names captured store span opSpan goodSpan badSpan op notAnd notOr
    goodName badName goodId badId word bad notWord goodNamed badNamed goodFound badFound
  exact ⟨.strictWordBinary .reference .reference notAnd notOr,
    .strictWordBinary .reference .reference notAnd notOr,independent⟩

theorem admitted_zero_never_skips_a_missing_operand
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span opSpan zeroSpan missingSpan : Syntax.SourceSpan)
    (op : Syntax.BinaryOp) (notAnd : op ≠ .logicalAnd) (notOr : op ≠ .logicalOr)
    (zeroName missingName : Syntax.Identifier) (zeroId : Resolved.LocalId)
    (zeroNamed : LocalNameTable.Lookup names zeroName.value zeroId)
    (zeroFound : Resolved.LocalScope.Lookup captured zeroId (.word Core.Word.zero))
    (missing : LocalNameTable.lookup? names missingName.value = none ∨
      ∃ id, LocalNameTable.Lookup names missingName.value id ∧ Resolved.LocalScope.lookup? captured id = none) :
    ClosedSourceDataExpression (binary span opSpan op
      (reference zeroSpan zeroName) (reference missingSpan missingName)) ∧
    ClosedSourceDataExpression (binary span opSpan op
      (reference missingSpan missingName) (reference zeroSpan zeroName)) ∧
    ClosedSourceExpressionEvaluates owner names captured store
      (reference zeroSpan zeroName) (.word Core.Word.zero) store ∧
    ∀ actual final,
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span opSpan op (reference zeroSpan zeroName) (reference missingSpan missingName)) actual final) ∧
      (¬ ClosedSourceExpressionEvaluates owner names captured store
        (binary span opSpan op (reference missingSpan missingName) (reference zeroSpan zeroName)) actual final) := by
  have independent := ClosedStrictWordBinaryNegative.zero_never_skips_a_missing_reference_on_either_side
    owner names captured store span opSpan zeroSpan missingSpan op notAnd notOr
    zeroName missingName zeroId zeroNamed zeroFound missing
  exact ⟨.strictWordBinary .reference .reference notAnd notOr,
    .strictWordBinary .reference .reference notAnd notOr,independent⟩

theorem admitted_addition_does_not_imply_name_resolution
    (names : LocalNameTable) (span opSpan missingSpan : Syntax.SourceSpan)
    (name : Syntax.Identifier) (missing : LocalNameTable.lookup? names name.value = none) :
    ClosedSourceDataExpression (binary span opSpan .add
      (reference missingSpan name) (reference missingSpan name)) ∧
    ∀ resolved, ¬ ResolvesLocalExpression names
      (binary span opSpan .add (reference missingSpan name) (reference missingSpan name)) resolved := by
  refine ⟨.strictWordBinary .reference .reference (by decide) (by decide),?_⟩
  intro resolved resolution
  cases resolution with
  | add left _ =>
      cases left with
      | identifier named =>
          have found := LocalNameTable.lookup?_iff.mpr named
          rw [missing] at found
          cases found

private def identityBody (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 0,[⟨s 1,.returnStmt (some (reference (s 2) ⟨s 3,"p"⟩))⟩]⟩
private def identity (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 4,.lambda (s 5) ⟨s 6,[⟨s 7,.inferred ⟨s 8,"p"⟩⟩]⟩ none (identityBody s)⟩
private def call (s : Nat → Syntax.SourceSpan) (argument : Syntax.Expr) : Syntax.Expr :=
  ⟨s 9,.call (identity s) ⟨s 10,[argument]⟩⟩

/-- Actual creation, argument and body evidence build a successful strict original
path. The call/lambda exclusion of the syntax-only Core-image gate is retained. -/
theorem original_call_operand_succeeds_outside_the_data_gate
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (s : Nat → Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (word : Core.Word) (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.word word))
    (op : Syntax.BinaryOp) (result : Core.Value) (meaning : StrictWordBinaryDenotes op word word result) :
    let argument := reference (s 11) name
    let src := binary (s 12) (s 13) op (call s argument) argument
    ClosedSourceExpressionEvaluates owner names captured store (identity s)
      (.sourceClosure (identity s) owner names captured) store ∧
    ClosedSourceExpressionEvaluates owner names captured store argument (.word word) store ∧
    ClosedSourceBodyEvaluates owner
      (("p",Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),.word word)::captured)
      store (identityBody s) (.word word) store ∧
    ClosedSourceExpressionEvaluates owner names captured store (call s argument) (.word word) store ∧
    ClosedSourceExpressionEvaluates owner names captured store src (RuntimeValue.ofCore result) store ∧
    (¬ ClosedSourceDataExpression (identity s)) ∧
    (¬ ClosedSourceDataExpression (call s argument)) ∧
    ¬ ClosedSourceDataExpression src := by
  dsimp only
  have created : ClosedSourceExpressionEvaluates owner names captured store (identity s)
      (.sourceClosure (identity s) owner names captured) store := .creation .inferred
  have argument : ClosedSourceExpressionEvaluates owner names captured store
      (reference (s 11) name) (.word word) store := .reference named found
  have body : ClosedSourceBodyEvaluates owner
      (("p",Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),.word word)::captured)
      store (identityBody s) (.word word) store := .expression (.reference .head .head)
  have invoked : ClosedSourceExpressionEvaluates owner names captured store
      (call s (reference (s 11) name)) (.word word) store := .call .inferred created argument body
  have original : ClosedSourceExpressionEvaluates owner names captured store
      (binary (s 12) (s 13) op (call s (reference (s 11) name)) (reference (s 11) name))
      (RuntimeValue.ofCore result) store := .strictWordBinary invoked argument meaning
  have noLambda : ¬ ClosedSourceDataExpression (identity s) := by intro gate; cases gate
  have noCall : ¬ ClosedSourceDataExpression (call s (reference (s 11) name)) := by intro gate; cases gate
  refine ⟨created,argument,body,invoked,original,noLambda,noCall,?_⟩
  intro gate
  cases gate with
  | logicalAnd _ _ => exact meaning.operator_is_strict.1 rfl
  | logicalOr _ _ => exact meaning.operator_is_strict.2 rfl
  | strictWordBinary left _ _ _ => exact noCall left

end Tests.StrictWordDataBoundary
