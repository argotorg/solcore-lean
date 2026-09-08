import Solcore.Frontend.LocalReference
import Solcore.Frontend.LocalReferenceElaborationProperties
import Solcore.Frontend.LocalReferenceEvaluation
import Solcore.Resolved.ExecutionProperties

/-! Canonical-AST consumers for the narrow local-reference adapter. Names are
caller-bound exact strings, not Boolean literals or normalized spellings.
Arbitrary independent source ranges do not participate in identity selection. -/

set_option autoImplicit false

namespace Tests.FrontendLocalReference

open Solcore Solcore.Frontend

private def modulePath : Workspace.ModulePath := ⟨[⟨"References", by decide⟩], by decide⟩
private def selectedId : Resolved.LocalId := ⟨⟨⟨.main, modulePath⟩, 0⟩, 0⟩
private def otherId : Resolved.LocalId := { selectedId with binderIndex := 1 }

private def reference (spelling : String) (expressionSpan nameSpan : Syntax.SourceSpan) : Syntax.Expr :=
  { span := expressionSpan, value := .identifier { span := nameSpan, value := spelling } }

private def grouped (outer inner expressionSpan nameSpan : Syntax.SourceSpan) : Syntax.Expr :=
  { span := outer, value := .group
      { span := inner, value := .group (reference "true" expressionSpan nameSpan) } }

private def booleanNames : LocalNameTable := [("true", selectedId), ("false", otherId)]

theorem occurrence_spans_do_not_select_ids (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? [("local", selectedId)] (reference "local" expressionSpan nameSpan) =
      some (.var selectedId) := by
  simp [resolveLocalReference?, LocalNameTable.lookup?, reference]

theorem true_and_false_remain_references (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? booleanNames (reference "true" expressionSpan nameSpan) = some (.var selectedId) ∧
    resolveLocalReference? booleanNames (reference "false" expressionSpan nameSpan) = some (.var otherId) := by
  simp [resolveLocalReference?, LocalNameTable.lookup?, reference, booleanNames]

theorem unbound_boolean_spellings_are_not_implicit_values (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? [] (reference "true" expressionSpan nameSpan) = none ∧
    resolveLocalReference? [] (reference "false" expressionSpan nameSpan) = none := by
  simp [resolveLocalReference?, LocalNameTable.lookup?, reference]

theorem spelling_is_case_and_space_sensitive (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? [("local", selectedId)] (reference "Local" expressionSpan nameSpan) = none ∧
    resolveLocalReference? [("local", selectedId)] (reference "local " expressionSpan nameSpan) = none := by
  simp [resolveLocalReference?, LocalNameTable.lookup?, reference]

/-- The second spelling uses a separate combining acute accent. -/
theorem spelling_is_not_unicode_normalized (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? [("é", selectedId)] (reference "é" expressionSpan nameSpan) = some (.var selectedId) ∧
    resolveLocalReference? [("é", selectedId)] (reference "é" expressionSpan nameSpan) = none := by
  simp [resolveLocalReference?, LocalNameTable.lookup?, reference]

theorem repeated_names_select_the_first_id (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? [("local", selectedId), ("local", otherId)]
      (reference "local" expressionSpan nameSpan) = some (.var selectedId) ∧
    ResolvesLocalReference [("local", selectedId), ("local", otherId)]
      (reference "local" expressionSpan nameSpan) selectedId := by
  exact ⟨by simp [resolveLocalReference?, LocalNameTable.lookup?, reference], .identifier .head⟩

theorem missing_names_are_unmapped (expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? booleanNames (reference "missing" expressionSpan nameSpan) = none := by
  simp [resolveLocalReference?, LocalNameTable.lookup?, reference, booleanNames]

theorem recovered_and_literal_nodes_are_unsupported (span literalSpan : Syntax.SourceSpan) :
    resolveLocalReference? booleanNames { span, value := .error } = none ∧
    resolveLocalReference? booleanNames
      { span, value := .literal { span := literalSpan, value := .decimal "7" } } = none ∧
    resolveLocalReference? booleanNames
      { span, value := .literal { span := literalSpan, value := .string "true" } } = none := by
  simp [resolveLocalReference?]

theorem calls_and_fields_are_not_reference_groups (span nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? booleanNames
      { span, value := .call (reference "true" span nameSpan) { span, elements := [] } } = none ∧
    resolveLocalReference? booleanNames
      { span, value := .field (reference "true" span nameSpan) span { span := nameSpan, value := "false" } } = none := by
  simp [resolveLocalReference?]

theorem nested_groups_preserve_the_selected_identity
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) :
    resolveLocalReference? booleanNames (grouped outer inner expressionSpan nameSpan) = some (.var selectedId) ∧
    ResolvesLocalReference booleanNames (grouped outer inner expressionSpan nameSpan) selectedId := by
  exact ⟨by simp [resolveLocalReference?, LocalNameTable.lookup?, grouped, reference, booleanNames],
    .group (.group (.identifier .head))⟩

private def context : Resolved.Context := [(otherId, .bool), (selectedId, .bool)]
private def environment : Resolved.Environment := [(otherId, .bool true), (selectedId, .bool false)]

private theorem selected_typed : Resolved.HasType context (.var selectedId) .bool :=
  .var (.tail (by decide) .head)

private theorem selected_lowered :
    Resolved.Lowers (Resolved.LocalScope.ids environment) (.var selectedId) (.var 1) :=
  .var (.tail (by decide) .head)

private theorem selected_evaluates (store : Core.Store) :
    Resolved.Evaluates environment store (.var selectedId) (.bool false) store :=
  .var (.tail (by decide) .head)

/-- The source spelling `true` denotes the caller's local Boolean value false.
The leading unrelated ID also checks that lowering selects position 1, not 0. -/
theorem caller_controls_the_referenced_value
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) (store : Core.Store) :
    ∃ resolved, resolveLocalReference? booleanNames (grouped outer inner expressionSpan nameSpan) = some resolved ∧
      Resolved.HasType context resolved .bool ∧
      resolved.lower? (Resolved.LocalScope.ids environment) = some (.var 1) ∧
      Resolved.Evaluates environment store resolved (.bool false) store ∧
      Core.Evaluates (Resolved.LocalScope.values environment) store (.var 1) (.bool false) store := by
  exact ⟨.var selectedId, (nested_groups_preserve_the_selected_identity _ _ _ _).1,
    selected_typed, selected_lowered.complete, selected_evaluates store,
    (selected_evaluates store).toCore selected_lowered⟩

theorem caller_reference_runs_at_sufficient_fuel
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) (store : Core.Store) :
    ∃ resolved required,
      resolveLocalReference? booleanNames (grouped outer inner expressionSpan nameSpan) = some resolved ∧
      resolved.lower? (Resolved.LocalScope.ids environment) = some (.var 1) ∧
      ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (Core.State.initial (.var 1) (Resolved.LocalScope.values environment) store) =
          .done (.bool false) store := by
  obtain ⟨required, enough⟩ := (selected_evaluates store).run_has_sufficient_fuel selected_lowered
  exact ⟨.var selectedId, required, (nested_groups_preserve_the_selected_identity _ _ _ _).1,
    selected_lowered.complete, enough⟩

theorem grouped_reference_elaborates_at_exact_position
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) :
    elaborateLocalReference? booleanNames context (grouped outer inner expressionSpan nameSpan) =
      some (.var 1, .bool) ∧
    LocalReferenceHasType booleanNames context (grouped outer inner expressionSpan nameSpan) .bool := by
  have resolved := (nested_groups_preserve_the_selected_identity outer inner expressionSpan nameSpan).2
  have found : Resolved.LocalScope.Lookup context selectedId .bool := .tail (by decide) .head
  exact ⟨elaborateLocalReference?_complete resolved (.tail (by decide) .head) found,
    .resolved resolved found⟩

theorem mapped_name_with_absent_typed_id_has_no_default
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) :
    elaborateLocalReference? booleanNames [(otherId, .bool)]
      (grouped outer inner expressionSpan nameSpan) = none :=
  elaborateLocalReference?_eq_none_of_missing_id
    (nested_groups_preserve_the_selected_identity outer inner expressionSpan nameSpan).2 (by decide)

theorem grouped_reference_evaluates_independently
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) :
    LocalReferenceEvaluates booleanNames environment
      (grouped outer inner expressionSpan nameSpan) (.bool false) :=
  .reference (nested_groups_preserve_the_selected_identity outer inner expressionSpan nameSpan).2
    (.tail (by decide) .head)

/-- Grouping costs no Core transition: zero fuel retains the input, and every
positive fuel executes the same selected positional variable in one step. -/
theorem grouped_reference_exact_machine_boundary
    (outer inner expressionSpan nameSpan : Syntax.SourceSpan) (store : Core.Store) :
    Core.runStateful 0 (Core.State.initial (.var 1) (Resolved.LocalScope.values environment) store) =
      .outOfFuel (Core.State.initial (.var 1) (Resolved.LocalScope.values environment) store) ∧
    ∀ fuel, Core.runStateful (fuel + 1)
      (Core.State.initial (.var 1) (Resolved.LocalScope.values environment) store) = .done (.bool false) store := by
  obtain ⟨id, index, resolved, indexed, zero, enough⟩ :=
    (grouped_reference_evaluates_independently outer inner expressionSpan nameSpan).exact_run store
  have idEq := resolved.id_unique
    (nested_groups_preserve_the_selected_identity outer inner expressionSpan nameSpan).2
  subst id
  have indexEq := indexed.index_unique
    (show Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) selectedId 1 from
      .tail (by decide) .head)
  subst index
  exact ⟨zero, enough⟩

end Tests.FrontendLocalReference
