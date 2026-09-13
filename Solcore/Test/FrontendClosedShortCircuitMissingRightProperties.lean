import Solcore.Frontend.ClosedSourceShortCircuitProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties

/- Original-syntax consumers. Missing lookup is excluded before any
whole-expression argument. Successful skipped witnesses precede iff conversion;
selected impossibility precedes the all-budget consequence from soundness.
Opaque capture tails, foreign or repeated IDs and full stores are unrestricted.
No whole-expression checking, parser, Core-cost or canonical-runtime claim. -/
set_option autoImplicit false
open Solcore Solcore.Frontend

namespace Tests.ClosedShortCircuitMissingRight

private theorem missing_lookup_is_impossible (id target : Resolved.LocalId) :
    ¬ LocalNameTable.Lookup [("guard", id)] "missing" target := by
  intro found
  have pairEq : ("missing", target) = ("guard", id) := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using found.mem
  exact (by decide : ("missing" : String) ≠ "guard") (Prod.mk.inj pairEq).1

variable {owner : Resolved.DeclarationId} {id : Resolved.LocalId}
  {captured : Resolved.LocalScope RuntimeValue} {store : List RuntimeValue}
  {span operatorSpan guardSpan guardNameSpan missingSpan missingNameSpan : Syntax.SourceSpan}
  {unitSpan tupleSpan : Syntax.SourceSpan}

/-- The missing reference has no endpoint at any complete input store. -/
theorem missing_reference_has_no_success :
    ∀ value finalStore,
      ¬ ClosedSourceExpressionEvaluates owner [("guard", id)] captured store
        ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩ value finalStore := by
  intro value finalStore evaluated
  cases evaluated with
  | reference named _ => exact missing_lookup_is_impossible id _ named
  | creation shape => cases shape

/-- A missing right operand has no premise in either independently built skip. -/
theorem missing_right_skip_successes :
    ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool false) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalAnd⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩
      (.bool false) store ∧
    ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool true) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalOr⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩
      (.bool true) store := by
  have leftFalse : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool false) :: captured) store
      ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩ (.bool false) store :=
    .reference .head .head
  have leftTrue : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool true) :: captured) store
      ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩ (.bool true) store :=
    .reference .head .head
  have originalAnd : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool false) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalAnd⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩
      (.bool false) store := .andFalse leftFalse
  have originalOr : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool true) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalOr⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩
      (.bool true) store := .orTrue leftTrue
  have decomposedAnd := closedSourceExpressionEvaluates_logicalAnd_iff.mp originalAnd
  have decomposedOr := closedSourceExpressionEvaluates_logicalOr_iff.mp originalOr
  exact ⟨closedSourceExpressionEvaluates_logicalAnd_iff.mpr decomposedAnd,
    closedSourceExpressionEvaluates_logicalOr_iff.mpr decomposedOr⟩

/-- Selecting the missing right excludes all values and all complete final stores. -/
theorem missing_right_selected_has_no_success :
    ∀ value finalStore,
      (¬ ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool true) :: captured) store
        ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
          ⟨operatorSpan, .logicalAnd⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩
        value finalStore) ∧
      (¬ ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool false) :: captured) store
        ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
          ⟨operatorSpan, .logicalOr⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩
        value finalStore) := by
  have leftTrue : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool true) :: captured) store
      ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩ (.bool true) store :=
    .reference .head .head
  have leftFalse : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool false) :: captured) store
      ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩ (.bool false) store :=
    .reference .head .head
  intro value finalStore
  constructor
  · intro evaluated
    rcases closedSourceExpressionEvaluates_logicalAnd_iff.mp evaluated with
      ⟨_, forcedLeft⟩ | ⟨middleStore, _, forcedRight⟩
    · cases (leftTrue.deterministic forcedLeft).1
    · exact missing_reference_has_no_success value finalStore forcedRight
  · intro evaluated
    rcases closedSourceExpressionEvaluates_logicalOr_iff.mp evaluated with
      ⟨_, forcedLeft⟩ | ⟨middleStore, _, forcedRight⟩
    · cases (leftFalse.deterministic forcedLeft).1
    · exact missing_reference_has_no_success value finalStore forcedRight

/-- Rejection at every budget is a consequence of the preceding semantic exclusion. -/
theorem missing_right_selected_none_at_every_depth :
    ∀ budget,
      evaluateClosedSourceExpression? budget owner [("guard", id)] ((id, .bool true) :: captured) store
        ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
          ⟨operatorSpan, .logicalAnd⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩ = none ∧
      evaluateClosedSourceExpression? budget owner [("guard", id)] ((id, .bool false) :: captured) store
        ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
          ⟨operatorSpan, .logicalOr⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩ = none := by
  intro budget
  constructor
  · cases accepted : evaluateClosedSourceExpression? budget owner [("guard", id)]
        ((id, .bool true) :: captured) store
        ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
          ⟨operatorSpan, .logicalAnd⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩ with
    | none => rfl
    | some endpoint =>
        rcases endpoint with ⟨value, finalStore⟩
        exact False.elim
          ((missing_right_selected_has_no_success value finalStore).1
            (evaluateClosedSourceExpression?_sound accepted))
  · cases accepted : evaluateClosedSourceExpression? budget owner [("guard", id)]
        ((id, .bool false) :: captured) store
        ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
          ⟨operatorSpan, .logicalOr⟩ ⟨missingSpan, .identifier ⟨missingNameSpan, "missing"⟩⟩⟩ with
    | none => rfl
    | some endpoint =>
        rcases endpoint with ⟨value, finalStore⟩
        exact False.elim
          ((missing_right_selected_has_no_success value finalStore).2
            (evaluateClosedSourceExpression?_sound accepted))

/-- The available empty-tuple right gives four direct original-rule witnesses.
The selected result is unit, not a claim of Boolean whole-expression typing. -/
theorem unit_right_has_all_four_original_witnesses :
    ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool false) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalAnd⟩ ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩⟩ (.bool false) store ∧
    ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool true) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalAnd⟩ ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩⟩ .unit store ∧
    ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool true) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalOr⟩ ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩⟩ (.bool true) store ∧
    ClosedSourceExpressionEvaluates owner [("guard", id)] ((id, .bool false) :: captured) store
      ⟨span, .binary ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩
        ⟨operatorSpan, .logicalOr⟩ ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩⟩ .unit store := by
  have leftFalse : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool false) :: captured) store
      ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩ (.bool false) store :=
    .reference .head .head
  have leftTrue : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool true) :: captured) store
      ⟨guardSpan, .identifier ⟨guardNameSpan, "guard"⟩⟩ (.bool true) store :=
    .reference .head .head
  have rightFalse : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool false) :: captured) store ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩ .unit store := .unit
  have rightTrue : ClosedSourceExpressionEvaluates owner [("guard", id)]
      ((id, .bool true) :: captured) store ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩ .unit store := .unit
  exact ⟨.andFalse leftFalse, .andTrue leftTrue rightTrue,
    .orTrue leftTrue, .orFalse leftFalse rightFalse⟩

end Tests.ClosedShortCircuitMissingRight
