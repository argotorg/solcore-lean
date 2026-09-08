import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.LocalExpressionEvaluationProperties
import Solcore.Core.Machine

/-! Canonical conditional consumers distinguish whole-expression static checks
from selected-branch evaluation. All names and types remain caller supplied. -/

set_option autoImplicit false

namespace Tests.FrontendLocalExpression

open Solcore Solcore.Frontend

private def modulePath : Workspace.ModulePath := ⟨[⟨"Conditional", by decide⟩], by decide⟩
private def localId (index : Nat) : Resolved.LocalId := ⟨⟨⟨.main, modulePath⟩, 0⟩, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "conditional.sol"⟩, 0, 4⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def group (inner : Syntax.Expr) : Syntax.Expr := ⟨span, .group inner⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .conditional condition span left span right⟩
private def names : LocalNameTable :=
  [("cond", localId 1), ("left", localId 2), ("right", localId 3), ("word", localId 4)]
private def context : Resolved.Context :=
  [(localId 0, .unit), (localId 1, .bool), (localId 2, .bool), (localId 3, .bool), (localId 4, .word)]
private def environment (choice : Bool) : Resolved.Environment :=
  [(localId 0, .unit), (localId 1, .bool choice), (localId 2, .bool false),
    (localId 3, .bool true), (localId 4, .word Core.Word.zero)]
private def simple : Syntax.Expr :=
  group (branch (group (ref "cond")) (group (ref "left")) (ref "right"))
private def resolvedSimple : Resolved.Expr := .ifE (.var (localId 1)) (.var (localId 2)) (.var (localId 3))
private def simpleCore : Core.Expr := .ifE (.var 1) (.var 2) (.var 3)

private theorem left_named : LocalNameTable.Lookup names "left" (localId 2) := .tail (by decide) .head
private theorem right_named : LocalNameTable.Lookup names "right" (localId 3) :=
  .tail (by decide) (.tail (by decide) .head)
private theorem simple_resolved : ResolvesLocalExpression names simple resolvedSimple :=
  .group (.conditional (.group (.identifier .head)) (.group (.identifier left_named)) (.identifier right_named))
private theorem simple_typed : LocalExpressionHasType names context simple .bool :=
  .group (.conditional (.group (.identifier .head (.tail (by decide) .head)))
    (.group (.identifier left_named (.tail (by decide) (.tail (by decide) .head))))
    (.identifier right_named (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem simple_lowered : Resolved.Lowers (Resolved.LocalScope.ids context) resolvedSimple simpleCore :=
  .ifE (.var (.tail (by decide) .head))
    (.var (.tail (by decide) (.tail (by decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))

theorem grouped_conditional_has_exact_static_result :
    ResolvesLocalExpression names simple resolvedSimple ∧
    LocalExpressionHasType names context simple .bool ∧
    elaborateLocalExpression? names context simple = some (simpleCore, .bool) :=
  ⟨simple_resolved, simple_typed, elaborateLocalExpression?_complete simple_resolved
    simple_lowered (simple_resolved.preserves_type simple_typed)⟩

private theorem selected_left (right : Syntax.Expr) (store : Core.Store) :
    LocalExpressionEvaluates names (environment true) store
      (branch (ref "cond") (ref "left") right) (.bool false) store :=
  .ifTrue (.identifier .head (.tail (by decide) .head))
    (.identifier left_named (.tail (by decide) (.tail (by decide) .head)))

theorem both_boolean_conditions_select_the_expected_value (choice : Bool) (store : Core.Store) :
    LocalExpressionEvaluates names (environment choice) store simple (.bool (!choice)) store ∧
    Core.Evaluates (Resolved.LocalScope.values (environment choice)) store simpleCore (.bool (!choice)) store := by
  have evaluation : LocalExpressionEvaluates names (environment choice) store simple (.bool (!choice)) store := by
    cases choice
    · exact .group (.ifFalse (.group (.identifier .head (.tail (by decide) .head)))
        (.identifier right_named (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
    · exact .group (.ifTrue (.group (.identifier .head (.tail (by decide) .head)))
        (.group (.identifier left_named (.tail (by decide) (.tail (by decide) .head)))))
  exact ⟨evaluation, (simple_resolved.core_evaluates_iff
    (environment := environment choice) simple_lowered).mp evaluation⟩

private def wordCondition : Syntax.Expr := branch (ref "word") (ref "left") (ref "right")
private def mismatchedBranches : Syntax.Expr := branch (ref "cond") (ref "left") (ref "word")

private theorem word_condition_rejected : elaborateLocalExpression? names context wordCondition = none := by
  simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
    wordCondition, branch, ref, Resolved.Expr.lower?, Resolved.LocalScope.ids,
    Resolved.LocalScope.values, Resolved.LocalScope.index?, localId]
  intro type inferred
  cases Core.infer_sound inferred with
  | ifE condition _ _ => cases condition with | var found => cases found

private theorem mismatched_branches_rejected :
    elaborateLocalExpression? names context mismatchedBranches = none := by
  simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
    mismatchedBranches, branch, ref, Resolved.Expr.lower?, Resolved.LocalScope.ids,
    Resolved.LocalScope.values, Resolved.LocalScope.index?, localId]
  intro type inferred
  cases Core.infer_sound inferred with
  | ifE _ left right =>
      cases left with
      | var found => cases found; cases right with | var found => cases found

theorem word_condition_and_mismatched_branches_have_no_type :
    elaborateLocalExpression? names context wordCondition = none ∧
    elaborateLocalExpression? names context mismatchedBranches = none ∧
    (¬ ∃ type, LocalExpressionHasType names context wordCondition type) ∧
    (¬ ∃ type, LocalExpressionHasType names context mismatchedBranches type) :=
  ⟨word_condition_rejected, mismatched_branches_rejected,
    elaborateLocalExpression?_eq_none_iff.mp word_condition_rejected,
    elaborateLocalExpression?_eq_none_iff.mp mismatched_branches_rejected⟩

private def unsupported : Syntax.Expr := ⟨span, .literal ⟨span, .string "7"⟩⟩
private def withSkipped (right : Syntax.Expr) : Syntax.Expr := branch (ref "cond") (ref "left") right

/-- Raw dynamic rules inspect only the selected left branch; all three different
right-branch defects still prevent a checked whole-expression result. -/
theorem unselected_bad_branches_are_static_failures (store : Core.Store) :
    elaborateLocalExpression? names context (withSkipped (ref "missing")) = none ∧
    elaborateLocalExpression? names context (withSkipped unsupported) = none ∧
    elaborateLocalExpression? names context (withSkipped wordCondition) = none ∧
    LocalExpressionEvaluates names (environment true) store
      (withSkipped (ref "missing")) (.bool false) store ∧
    LocalExpressionEvaluates names (environment true) store (withSkipped unsupported) (.bool false) store ∧
    LocalExpressionEvaluates names (environment true) store (withSkipped wordCondition) (.bool false) store := by
  refine ⟨?_, ?_, ?_, selected_left _ store, selected_left _ store, selected_left _ store⟩
  all_goals simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
    withSkipped, unsupported, interpretWordLiteral?, numericLiteralValue?,
    wordCondition, branch, ref, Resolved.Expr.lower?, Resolved.LocalScope.ids,
    Resolved.LocalScope.values, Resolved.LocalScope.index?, localId]
  intro type inferred
  cases Core.infer_sound inferred with
  | ifE _ _ right =>
      cases right with
      | ifE condition _ _ => cases condition with | var found => cases found

theorem duplicate_names_select_the_first_conditional_binding :
    elaborateLocalExpression? (("cond", localId 2) :: names) context simple =
      some (.ifE (.var 2) (.var 2) (.var 3), .bool) := by
  simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
    simple, group, branch, ref, Resolved.Expr.lower?, Resolved.LocalScope.ids,
    Resolved.LocalScope.values, Resolved.LocalScope.index?, localId]
  have inferred : Core.infer? [.unit, .bool, .bool, .bool, .word]
      (.ifE (.var 2) (.var 2) (.var 3)) = some .bool :=
    Core.infer_complete (.ifE (.var rfl) (.var rfl) (.var rfl))
  simp only [inferred, Option.bind_some]

theorem conditional_punctuation_and_outer_ranges_do_not_change_elaboration
    (outer question colon : Syntax.SourceSpan) :
    elaborateLocalExpression? names context
      ⟨outer, .conditional (ref "cond") question (ref "left") colon (ref "right")⟩ =
        some (simpleCore, .bool) :=
  elaborateLocalExpression?_complete
    (.conditional (.identifier .head) (.identifier left_named) (.identifier right_named))
    simple_lowered (simple_resolved.preserves_type simple_typed)

/-- The three lookups use nonzero positions. The fourth transition reads the
selected branch; at fuel three its initial state is retained exactly. -/
theorem simple_conditional_exact_fuel (choice : Bool) (store : Core.Store) :
    Core.runStateful 3 (Core.State.initial simpleCore (Resolved.LocalScope.values (environment choice)) store) =
      .outOfFuel (Core.State.initial (.var (if choice then 2 else 3))
        (Resolved.LocalScope.values (environment choice)) store) ∧
    ∀ extra, Core.runStateful (extra + 4)
      (Core.State.initial simpleCore (Resolved.LocalScope.values (environment choice)) store) =
        .done (.bool (!choice)) store := by
  cases choice <;> constructor
  · rfl
  · intro extra; simp [Core.runStateful, Core.State.initial, Core.advance,
      simpleCore, Resolved.LocalScope.values, environment]
  · rfl
  · intro extra; simp [Core.runStateful, Core.State.initial, Core.advance,
      simpleCore, Resolved.LocalScope.values, environment]

private def nested : Syntax.Expr := group (branch (ref "cond") simple (ref "right"))
private def nestedCore : Core.Expr := .ifE (.var 1) simpleCore (.var 3)

theorem unselected_nested_conditionals_add_no_execution_fuel (store : Core.Store) :
    elaborateLocalExpression? names context (withSkipped nested) =
      some (.ifE (.var 1) (.var 2) nestedCore, .bool) ∧
    Core.runStateful 3 (Core.State.initial (.ifE (.var 1) (.var 2) nestedCore)
      (Resolved.LocalScope.values (environment true)) store) =
      .outOfFuel (Core.State.initial (.var 2) (Resolved.LocalScope.values (environment true)) store) ∧
    ∀ extra, Core.runStateful (extra + 4)
      (Core.State.initial (.ifE (.var 1) (.var 2) nestedCore)
        (Resolved.LocalScope.values (environment true)) store) = .done (.bool false) store := by
  refine ⟨?_, rfl, ?_⟩
  · simp [elaborateLocalExpression?, resolveLocalExpression?, LocalNameTable.lookup?, names, context,
      withSkipped, nested, nestedCore, simple, simpleCore, group, branch, ref, Resolved.Expr.lower?,
      Resolved.LocalScope.ids, Resolved.LocalScope.values, Resolved.LocalScope.index?, localId]
    have inferred : Core.infer? [.unit, .bool, .bool, .bool, .word]
        (.ifE (.var 1) (.var 2) (.ifE (.var 1) simpleCore (.var 3))) = some .bool :=
      Core.infer_complete (.ifE (.var rfl) (.var rfl)
        (.ifE (.var rfl) (.ifE (.var rfl) (.var rfl) (.var rfl)) (.var rfl)))
    simp only [simpleCore] at inferred
    simp only [inferred, Option.bind_some]
  · intro extra
    simp [Core.runStateful, Core.State.initial, Core.advance, Resolved.LocalScope.values, environment]

end Tests.FrontendLocalExpression
