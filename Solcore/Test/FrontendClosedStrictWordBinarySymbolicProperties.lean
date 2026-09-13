import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Frontend.ClosedSourceStrictWordBinaryProperties
import Solcore.Frontend.ClosedSourceDataExpression

/- Fourteen original strict Word witnesses over arbitrary ordered mixed inputs.
No typing, unique-row, whole-resolution or bounded-execution premise is used. -/
set_option autoImplicit false
namespace Tests.ClosedStrictWordBinarySymbolic
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .identifier name⟩
private def source (spans : Fin 4 → Syntax.SourceSpan) (left right : Syntax.Identifier)
    (operator : Syntax.BinaryOp) : Syntax.Expr :=
  ⟨spans 0, .binary (reference (spans 2) left) ⟨spans 1, operator⟩
    (reference (spans 3) right)⟩
private def outcomes (left right : Core.Word) : List (Syntax.BinaryOp × Core.Value) :=
  [(.add, .word (left.add right)), (.subtract, .word (left.sub right)),
   (.multiply, .word (left.mul right)), (.divide, .word (left.udiv right)),
   (.modulo, .word (left.umod right)), (.bitAnd, .word (left.bitAnd right)),
   (.bitOr, .word (left.bitOr right)), (.bitXor, .word (left.bitXor right)),
   (.greater, .bool (decide (left > right))), (.less, .bool (decide (left < right))),
   (.equal, .bool (left == right)), (.notEqual, .bool (!(left == right))),
   (.lessEqual, .bool (!(decide (left > right)))),
   (.greaterEqual, .bool (!(decide (left < right))))]

private theorem original_meaning {left right : Core.Word} {operator : Syntax.BinaryOp}
    {value : Core.Value} (member : (operator, value) ∈ outcomes left right) :
    StrictWordBinaryDenotes operator left right value := by
  simp only [outcomes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals cases h; constructor

theorem all_fourteen_original_and_exact_actual_results
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (spans : Fin 4 → Syntax.SourceSpan) (leftName rightName : Syntax.Identifier)
    (leftId rightId : Resolved.LocalId) (leftWord rightWord : Core.Word)
    (leftNamed : LocalNameTable.Lookup names leftName.value leftId)
    (rightNamed : LocalNameTable.Lookup names rightName.value rightId)
    (leftFound : Resolved.LocalScope.Lookup captured leftId (.word leftWord))
    (rightFound : Resolved.LocalScope.Lookup captured rightId (.word rightWord)) :
    ∀ operator result, (operator, result) ∈ outcomes leftWord rightWord →
      ClosedSourceExpressionEvaluates owner names captured store
        (source spans leftName rightName operator) (RuntimeValue.ofCore result) store ∧
      (∀ actual final, ClosedSourceExpressionEvaluates owner names captured store
        (source spans leftName rightName operator) actual final ↔
        actual = RuntimeValue.ofCore result ∧ final = store) ∧
      ¬ ClosedSourceDataExpression (source spans leftName rightName operator) := by
  intro operator result member
  have meaning := original_meaning member
  have leftOriginal : ClosedSourceExpressionEvaluates owner names captured store
      (reference (spans 2) leftName) (.word leftWord) store := .reference leftNamed leftFound
  have rightOriginal : ClosedSourceExpressionEvaluates owner names captured store
      (reference (spans 3) rightName) (.word rightWord) store := .reference rightNamed rightFound
  have original : ClosedSourceExpressionEvaluates owner names captured store
      (source spans leftName rightName operator) (RuntimeValue.ofCore result) store :=
    .strictWordBinary leftOriginal rightOriginal meaning
  obtain ⟨notAnd, notOr⟩ := meaning.operator_is_strict
  refine ⟨original, ?_, ?_⟩
  · intro actual final
    have decomposition := closedSourceExpressionEvaluates_strictWordBinary_iff
      (owner := owner) (names := names) (captured := captured) (initialStore := store)
      (finalStore := final) (span := spans 0) (operatorSpan := spans 1)
      (left := reference (spans 2) leftName) (right := reference (spans 3) rightName)
      (value := actual) notAnd notOr
    constructor
    · intro evaluated
      obtain ⟨lw, rw, value, middle, actualEq, leftRun, rightRun, actualMeaning⟩ :=
        decomposition.mp evaluated
      obtain ⟨leftEq, middleEq⟩ := leftRun.deterministic leftOriginal
      cases RuntimeValue.word.inj leftEq
      cases middleEq
      obtain ⟨rightEq, finalEq⟩ := rightRun.deterministic rightOriginal
      cases RuntimeValue.word.inj rightEq
      exact ⟨actualEq.trans (congrArg RuntimeValue.ofCore (actualMeaning.value_unique meaning)), finalEq⟩
    · intro endpoints
      exact decomposition.mpr ⟨leftWord, rightWord, result, store, endpoints.1,
        leftOriginal, by simpa only [endpoints.2] using rightOriginal, meaning⟩
  · intro admitted
    cases admitted with
    | logicalAnd _ _ => exact notAnd rfl
    | logicalOr _ _ => exact notOr rfl

end Tests.ClosedStrictWordBinarySymbolic
