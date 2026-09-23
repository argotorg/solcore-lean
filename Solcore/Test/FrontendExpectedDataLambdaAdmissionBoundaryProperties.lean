import Solcore.Frontend.Expected
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.ClosedSource
import Solcore.Frontend.RuntimeValue

/- Raw source calls can bypass unvisited syntax and produce non-Core intermediates. -/
set_option autoImplicit false
namespace Tests.ExpectedDataLambdaAdmissionBoundaries
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"LambdaAdmission", by decide⟩], by decide⟩⟩, 295⟩
private def name (s : Syntax.SourceSpan) : Syntax.Identifier := ⟨s, "p"⟩
private def ref (s : Syntax.SourceSpan) (text : String) : Syntax.Expr :=
  ⟨s, .identifier ⟨s, text⟩⟩
private def unit (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s, .tuple ⟨s, []⟩⟩
private def output (s : Syntax.SourceSpan) (e : Syntax.Expr) : Syntax.Block :=
  ⟨s, [⟨s, .returnStmt (some e)⟩]⟩
private def bare (s : Syntax.SourceSpan) : Syntax.Block := ⟨s, [⟨s, .returnStmt none⟩]⟩
private def lambda (s : Syntax.SourceSpan) (b : Syntax.Block) : Syntax.Expr :=
  ⟨s, .lambda s ⟨s, [⟨s, .inferred (name s)⟩]⟩ none b⟩
private def call (s : Syntax.SourceSpan) (f a : Syntax.Expr) : Syntax.Expr :=
  ⟨s, .call f ⟨s, [a]⟩⟩
private def branching (s : Syntax.SourceSpan) : Syntax.Block :=
  ⟨s, [⟨s, .ifThen (ref s "p") (bare s) (some (output s (ref s "missing")))⟩]⟩
private def matching (s : Syntax.SourceSpan) : Syntax.Block :=
  ⟨s, [⟨s, .matchWith ⟨s, ⟨ref s "p", []⟩⟩
    ⟨s, ⟨[⟨s, ⟨⟨s, .wildcard s⟩, bare s⟩⟩,
      ⟨s, ⟨⟨s, .literal ⟨s, .string "bad"⟩⟩, bare s⟩⟩], none⟩⟩⟩]⟩
private def hiddenArgument (s : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s, .conditional (ref s "flag") s (unit s) s (ref s "missing")⟩
private def inputs : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "flag" .bool
private def environment : List (Resolved.LocalId × RuntimeValue) :=
  [(Resolved.freshLocalId owner [], .bool true)]
private def argumentName (s : Syntax.SourceSpan) : Syntax.Expr := ref s "flag"

variable (s : Syntax.SourceSpan) (store : List RuntimeValue)

/-- The selected original branch succeeds while the checker rejects an unselected missing name. -/
theorem unselected_body_is_still_checked :
    ClosedSourceDataBody (branching s) ∧
    ClosedSourceExpressionEvaluates owner inputs.names environment store
      (call s (lambda s (branching s)) (argumentName s)) .unit store ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner inputs
      (lambda s (branching s)) (.function .bool .unit) = none := by
  have raw : ClosedSourceExpressionEvaluates owner inputs.names environment store
      (call s (lambda s (branching s)) (argumentName s)) .unit store :=
    .call .inferred (.creation .inferred) (.reference .head .head)
      (.ifTrue (.reference .head .head) .bare)
  exact ⟨.conditional .reference .bare (.expression .reference), raw, by cbv⟩

/-- A first wildcard bypasses a malformed written pattern at runtime, not in the checker. -/
theorem unselected_pattern_is_still_checked :
    ClosedSourceDataBody (matching s) ∧
    ClosedSourceExpressionEvaluates owner [] [] store
      (call s (lambda s (matching s)) (unit s)) .unit store ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      (lambda s (matching s)) (.function .unit .unit) = none := by
  have raw : ClosedSourceExpressionEvaluates owner [] [] store
      (call s (lambda s (matching s)) (unit s)) .unit store :=
    .call .inferred (.creation .inferred) .unit
      (.wordMatch (.reference .head .head) (.wildcard (.wildcard rfl)) .bare)
  refine ⟨?_, raw, by cbv⟩
  refine .wordMatch .reference ?_ ?_
  · intro arm member
    rcases List.mem_cons.mp member with rfl | member
    · exact .bare
    · rcases List.mem_cons.mp member with rfl | member
      · exact .bare
      · cases member
  · intro body member; cases member

/-- An admitted argument can run its selected branch despite lacking whole original resolution. -/
theorem unselected_argument_name_blocks_application_admission :
    ClosedSourceDataExpression (hiddenArgument s) ∧
    ClosedSourceDataBody (bare s) ∧
    ClosedSourceExpressionEvaluates owner inputs.names environment store
      (call s (lambda s (bare s)) (hiddenArgument s)) .unit store ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner inputs
      (lambda s (bare s)) (.function .unit .unit) = some (.lambda .unit .unit .unit) ∧
    resolveLocalExpression? inputs.names (hiddenArgument s) = none := by
  have raw : ClosedSourceExpressionEvaluates owner inputs.names environment store
      (call s (lambda s (bare s)) (hiddenArgument s)) .unit store :=
    .call .inferred (.creation .inferred) (.conditionalTrue (.reference .head .head) .unit) .bare
  exact ⟨.conditional .reference .unit .reference, .bare, raw, by cbv, by cbv⟩

private def created (s : Syntax.SourceSpan) := lambda s (bare s)
private def returning (s : Syntax.SourceSpan) := output s (created s)
private def discarding (s : Syntax.SourceSpan) : Syntax.Block :=
  ⟨s, [⟨s, .expression (created s) true⟩, ⟨s, .returnStmt none⟩]⟩
private def innerNames (s : Syntax.SourceSpan) : LocalNameTable :=
  [((name s).value, Resolved.freshLocalId owner [])]
private def innerCaptured : List (Resolved.LocalId × RuntimeValue) :=
  [(Resolved.freshLocalId owner [], .unit)]

/-- Creation preserves the entire original unchecked body and captures without evaluating it. -/
theorem creation_does_not_admit_a_nongated_body :
    ClosedSourceExpressionEvaluates owner [] [] store (lambda s (returning s))
      (.sourceClosure (lambda s (returning s)) owner [] []) store ∧
    (¬ ClosedSourceDataBody (returning s)) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      (lambda s (returning s)) (.function .unit .unit) = none := by
  have raw : ClosedSourceExpressionEvaluates owner [] [] store (lambda s (returning s))
      (.sourceClosure (lambda s (returning s)) owner [] []) store := .creation .inferred
  refine ⟨raw, ?_, by cbv⟩
  intro gate
  cases gate with
  | expression child => cases child

/-- The original returned closure is not the embedding of any Core value. -/
theorem returned_source_closure_is_not_a_core_result :
    ClosedSourceExpressionEvaluates owner [] [] store
      (call s (lambda s (returning s)) (unit s))
      (.sourceClosure (created s) owner (innerNames s) innerCaptured) store ∧
    (¬ ∃ value, RuntimeValue.sourceClosure (created s) owner (innerNames s) innerCaptured =
      RuntimeValue.ofCore value) := by
  have raw : ClosedSourceExpressionEvaluates owner [] [] store
      (call s (lambda s (returning s)) (unit s))
      (.sourceClosure (created s) owner (innerNames s) innerCaptured) store :=
    .call .inferred (.creation .inferred) .unit (.expression (.creation .inferred))
  refine ⟨raw, ?_⟩
  rintro ⟨value, same⟩
  have contradiction := congrArg RuntimeValue.toCore? same
  simp only [RuntimeValue.toCore?, RuntimeValue.toCore?_ofCore, reduceCtorEq] at contradiction

/-- A Core-image final Unit cannot justify dropping a discarded source-only closure. -/
theorem discarded_source_closure_prevents_body_admission :
    ClosedSourceExpressionEvaluates owner [] [] store
      (call s (lambda s (discarding s)) (unit s)) .unit store ∧
    (¬ ClosedSourceDataBody (discarding s)) ∧
    elaborateExpectedComputationLambda? elaborateLocalExpression? [] owner .empty
      (lambda s (discarding s)) (.function .unit .unit) = none := by
  have raw : ClosedSourceExpressionEvaluates owner [] [] store
      (call s (lambda s (discarding s)) (unit s)) .unit store :=
    .call .inferred (.creation .inferred) .unit (.discard (.creation .inferred) .bare)
  refine ⟨raw, ?_, by cbv⟩
  intro gate
  cases gate with
  | discard child _ => cases child

end Tests.ExpectedDataLambdaAdmissionBoundaries
