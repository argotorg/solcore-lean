import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalExpression
import Solcore.Frontend.LocalReference

set_option autoImplicit false
namespace Tests.ClosedSourceShortCircuitDataBoundaries
open Solcore Solcore.Frontend

private def ref (span : Syntax.SourceSpan) (name : String) : Syntax.Expr :=
  ⟨span, .identifier ⟨span, name⟩⟩
private def binary (span : Syntax.SourceSpan) (isOr : Bool) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .binary left ⟨span, if isOr then .logicalOr else .logicalAnd⟩ right⟩
private def unit (span : Syntax.SourceSpan) : Syntax.Expr := ⟨span, .tuple ⟨span, []⟩⟩
private def lambda (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span, .lambda span ⟨span, [⟨span, .inferred ⟨span, "p"⟩⟩]⟩ none
    ⟨span, [⟨span, .returnStmt none⟩]⟩⟩
private def call (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span, .call (lambda span) ⟨span, [unit span]⟩⟩

private theorem skip (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span : Syntax.SourceSpan) (isOr : Bool) (right : Syntax.Expr) (id : Resolved.LocalId)
    (named : LocalNameTable.Lookup names "flag" id)
    (found : Resolved.LocalScope.Lookup captured id (.bool isOr)) :
    ClosedSourceExpressionEvaluates owner names captured store
      (binary span isOr (ref span "flag") right) (.bool isOr) store := by
  cases isOr
  · exact .andFalse (.reference named found)
  · exact .orTrue (.reference named found)

private theorem outside (span : Syntax.SourceSpan) (isOr : Bool) (left right : Syntax.Expr)
    (excluded : ¬ ClosedSourceDataExpression right) :
    ¬ ClosedSourceDataExpression (binary span isOr left right) := by
  cases isOr
  · intro admitted
    cases admitted with
    | logicalAnd _ child => exact excluded child
    | strictWordBinary _ _ notAnd _ => exact notAnd rfl
  · intro admitted
    cases admitted with
    | logicalOr _ child => exact excluded child
    | strictWordBinary _ _ _ notOr => exact notOr rfl

/-- A short-circuit expression can succeed outside the gate from opaque mixed inputs. -/
theorem skipped_lambda_and_call_remain_outside
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span : Syntax.SourceSpan) (isOr : Bool) (id : Resolved.LocalId)
    (named : LocalNameTable.Lookup names "flag" id)
    (found : Resolved.LocalScope.Lookup captured id (.bool isOr)) :
    ClosedSourceExpressionEvaluates owner names captured store
      (binary span isOr (ref span "flag") (lambda span)) (.bool isOr) store ∧
    ClosedSourceExpressionEvaluates owner names captured store
      (binary span isOr (ref span "flag") (call span)) (.bool isOr) store ∧
    ¬ ClosedSourceDataExpression (binary span isOr (ref span "flag") (lambda span)) ∧
    ¬ ClosedSourceDataExpression (binary span isOr (ref span "flag") (call span)) := by
  have originalLambda := skip owner names captured store span isOr (lambda span) id named found
  have originalCall := skip owner names captured store span isOr (call span) id named found
  exact ⟨originalLambda, originalCall,
    outside span isOr _ _ (by intro gate; cases gate),
    outside span isOr _ _ (by intro gate; cases gate)⟩

/-- Both written references are admitted; skipping a missing one does not resolve it. -/
theorem admitted_missing_right_skips_without_whole_resolution
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span : Syntax.SourceSpan) (isOr : Bool) (id : Resolved.LocalId)
    (named : LocalNameTable.Lookup names "flag" id)
    (found : Resolved.LocalScope.Lookup captured id (.bool isOr))
    (missing : LocalNameTable.lookup? names "missing" = none) :
    ClosedSourceDataExpression (binary span isOr (ref span "flag") (ref span "missing")) ∧
    ClosedSourceExpressionEvaluates owner names captured store
      (binary span isOr (ref span "flag") (ref span "missing")) (.bool isOr) store ∧
    (∀ resolved, ¬ ResolvesLocalExpression names
      (binary span isOr (ref span "flag") (ref span "missing")) resolved) := by
  have original := skip owner names captured store span isOr (ref span "missing") id named found
  have absent : ∀ target, ¬ LocalNameTable.Lookup names "missing" target := by
    intro target lookup
    have present := LocalNameTable.lookup?_iff.mpr lookup
    rw [missing] at present
    cases present
  refine ⟨?_, original, ?_⟩
  · cases isOr
    · exact .logicalAnd .reference .reference
    · exact .logicalOr .reference .reference
  · intro resolved resolution
    cases isOr
    · cases resolution with
      | logicalAnd _ right =>
          cases right with
          | identifier lookup => exact absent _ lookup
    · cases resolution with
      | logicalOr _ right =>
          cases right with
          | identifier lookup => exact absent _ lookup

/-- Recursive syntax admission still establishes no successful endpoint. -/
theorem admitted_unit_left_has_no_success
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span : Syntax.SourceSpan) (isOr : Bool) :
    ClosedSourceDataExpression (binary span isOr (unit span) (unit span)) ∧
    (∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names captured store
      (binary span isOr (unit span) (unit span)) actual final) := by
  constructor
  · cases isOr
    · exact .logicalAnd .unit .unit
    · exact .logicalOr .unit .unit
  · intro actual final evaluated
    cases isOr
    · cases evaluated with
      | andTrue left _ => cases left
      | andFalse left => cases left
      | creation shape => cases shape
      | strictWordBinary _ _ meaning => cases meaning
    · cases evaluated with
      | orTrue left => cases left
      | orFalse left _ => cases left
      | creation shape => cases shape
      | strictWordBinary _ _ meaning => cases meaning

end Tests.ClosedSourceShortCircuitDataBoundaries
