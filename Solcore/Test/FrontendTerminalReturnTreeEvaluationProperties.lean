import Solcore.Frontend.TerminalReturnTreeExecutionProperties
import Solcore.Frontend.TerminalReturnTreeEvaluationEmbeddingProperties
import Solcore.Frontend.TerminalReturnTreeProperties

/-! Recursive selected paths retain actual values, stores and pending frames.
Identity alignment is separate from value typing; no tree runner is introduced. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalReturnTreeEvaluation

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeEvaluation", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "tree-evaluation.sol"⟩, 71, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (value : Option Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt value⟩]⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block :=
  ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def names : LocalNameTable := [("y", id 2), ("x", id 1), ("c", id 0)]
private def context (type : Core.Ty) : Resolved.Context := [(id 2, type), (id 1, type), (id 0, .bool)]
private def environment (choice : Bool) (left right : Core.Value) : Resolved.Environment :=
  [(id 2, right), (id 1, left), (id 0, .bool choice)]
private def x := returned (some (ref "x"))
private def y := returned (some (ref "y"))
private def bare := returned none
private def spine : Nat → Syntax.Block
  | 0 => x
  | depth + 1 => branch (ref "c") (spine depth) y
private def core : Nat → Core.Expr
  | 0 => .var 1
  | depth + 1 => .ifE (.var 2) (core depth) (.var 0)
private theorem xElab (type : Core.Ty) : ReturnBodyElaborates names (context type) x (.var 1) type :=
  .expression (.identifier (.tail (by decide) .head))
    (.var (.tail (by change id 2 ≠ id 1; decide) .head)) (.var (.tail (by decide) .head))
private theorem yElab (type : Core.Ty) : ReturnBodyElaborates names (context type) y (.var 0) type :=
  .expression (.identifier .head) (.var .head) (.var .head)
private theorem elaborated (depth : Nat) (type : Core.Ty) :
    TerminalReturnTreeElaborates names (context type) (spine depth) (core depth) type := by
  induction depth with
  | zero => exact .single (xElab type)
  | succ depth ih =>
    exact .conditional (.identifier (.tail (by decide) (.tail (by decide) .head)))
      (.var (.tail (by change id 2 ≠ id 0; decide) (.tail (by change id 1 ≠ id 0; decide) .head)))
      (.var (.tail (by decide) (.tail (by decide) .head))) ih (.single (yElab type))
private theorem conditionCost (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store (ref "c") (.bool choice) store 1 :=
  .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
private theorem xCost (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store (ref "x") left store 1 :=
  .identifier (.tail (by decide) .head) (.tail (by decide) .head)
private theorem yCost (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store (ref "y") right store 1 := .identifier .head .head
private theorem trueCost (depth : Nat) (left right : Core.Value) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost names (environment true left right) store (spine depth) left store (3 * depth + 1) := by
  induction depth with
  | zero => exact .single (.expression (xCost true left right store))
  | succ depth ih =>
    have arithmetic : 1 + (3 * depth + 1) + 2 = 3 * (depth + 1) + 1 := by omega
    simpa only [arithmetic, spine, branch] using TerminalReturnTreeEvaluatesWithCost.ifTrue (conditionCost true left right store) ih
private theorem falseCost (depth : Nat) (left right : Core.Value) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost names (environment false left right) store (spine (depth + 1)) right store 4 :=
  .ifFalse (conditionCost false left right store) (.single (.expression (yCost false left right store)))

theorem every_true_level_costs_three_while_false_stops_at_the_first_node
    (depth : Nat) (type : Core.Ty) (left right : Core.Value) (store : Core.Store) (continuation : List Core.Frame) :
    TerminalReturnTreeEvaluatesWithCost names (environment true left right) store (spine depth) left store (3 * depth + 1) ∧
    TerminalReturnTreeEvaluatesWithCost names (environment false left right) store (spine (depth + 1)) right store 4 ∧
    Core.Steps (3 * depth + 1) ⟨.eval (core depth) [right, left, .bool true], continuation, store⟩ ⟨.ret left, continuation, store⟩ ∧
    Core.Steps 4 (Core.State.initial (core (depth + 1)) [right, left, .bool false] store) (Core.State.final right store) :=
  ⟨trueCost depth left right store, falseCost depth left right store,
    (trueCost depth left right store).checked_toStepsWithContinuation (elaborated depth type).complete rfl continuation,
    (falseCost depth left right store).checked_toSteps (elaborated (depth + 1) type).complete rfl⟩

theorem a_leaf_has_one_step_even_when_the_unused_condition_is_false (left right : Core.Value) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost names (environment false left right) store (spine 0) left store 1 :=
  .single (.expression (xCost false left right store))

theorem raw_and_counted_derivations_determine_values_stores_and_the_exact_positive_cost
    (depth : Nat) (left right rawValue countedValue : Core.Value) (store rawStore countedStore : Core.Store) (cost : Nat)
    (raw : TerminalReturnTreeEvaluates names (environment true left right) store (spine depth) rawValue rawStore)
    (counted : TerminalReturnTreeEvaluatesWithCost names (environment true left right) store (spine depth) countedValue countedStore cost) :
    rawValue = left ∧ rawStore = store ∧ countedValue = left ∧ countedStore = store ∧ cost = 3 * depth + 1 ∧ 0 < cost ∧
    (∃ witness, TerminalReturnTreeEvaluatesWithCost names (environment true left right) store (spine depth) rawValue rawStore witness) ∧
    (TerminalReturnTreeEvaluates names (environment true left right) store (spine depth) left store ↔
      ∃ witness, TerminalReturnTreeEvaluatesWithCost names (environment true left right) store (spine depth) left store witness) := by
  have original := trueCost depth left right store
  have same := counted.deterministic original
  exact ⟨(raw.deterministic original.erase).1, raw.store_eq, same.1, counted.store_eq, same.2.2,
    counted.cost_pos, raw.exists_cost, terminalReturnTreeEvaluates_iff_exists_cost⟩

theorem typed_existence_and_preservation_use_the_actual_supplied_value_proofs
    (depth : Nat) (choice : Bool) (type : Core.Ty) (left right value : Core.Value)
    (leftTyped : Core.ValueHasType left type) (rightTyped : Core.ValueHasType right type)
    (store finalStore : Core.Store)
    (raw : TerminalReturnTreeEvaluates names (environment choice left right) store (spine depth) value finalStore) :
    (∃ result, TerminalReturnTreeEvaluates names (environment choice left right) store (spine depth) result store ∧
      Core.ValueHasType result type) ∧ Core.ValueHasType value type ∧ finalStore = store := by
  have typing := (elaborated depth type).hasType
  have supplied : Core.EnvironmentHasTypes (environment choice left right).values (context type).values :=
    .cons rightTyped (.cons leftTyped (.cons .bool .nil))
  exact ⟨typing.evaluates rfl supplied store, raw.preserves_type typing rfl supplied⟩

theorem opaque_existing_cells_and_closures_leave_even_incompatible_outer_frames_pending
    (depth : Nat) (location : Core.Location) (body : Core.Expr) (captured : Core.Environment)
    (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps (3 * depth + 1)
      ⟨.eval (core depth) [.unit, .cellRef .word location, .bool true], .unaryApply .boolNot :: continuation, store⟩
      ⟨.ret (.cellRef .word location), .unaryApply .boolNot :: continuation, store⟩ ∧
    Core.Steps (3 * depth + 1)
      ⟨.eval (core depth) [.unit, .closure .bool .word body captured, .bool true], continuation, store⟩
      ⟨.ret (.closure .bool .word body captured), continuation, store⟩ :=
  ⟨(trueCost depth (.cellRef .word location) .unit store).checked_toStepsWithContinuation
      (elaborated depth (.cell .word)).complete rfl _,
    (trueCost depth (.closure .bool .word body captured) .unit store).checked_toStepsWithContinuation
      (elaborated depth (.function .bool .word)).complete rfl continuation⟩

theorem aligned_untyped_payloads_still_have_raw_core_correspondence_without_type_safety
    (depth : Nat) (store finalStore : Core.Store) (value : Core.Value) :
    elaborateTerminalReturnTree? names (context .word) (spine depth) = some (core depth, .word) ∧
    (TerminalReturnTreeEvaluates names (environment true (.bool true) (.bool false)) store (spine depth) value finalStore ↔
      Core.Evaluates [.bool false, .bool true, .bool true] store (core depth) value finalStore) ∧
    Core.Evaluates [.bool false, .bool true, .bool true] store (core depth) (.bool true) store ∧
    ¬ Core.ValueHasType (.bool true) .word := by
  have accepted := (elaborated depth .word).complete
  exact ⟨accepted, elaborateTerminalReturnTree?_evaluates_iff accepted rfl,
    (elaborateTerminalReturnTree?_evaluates_iff accepted rfl).mp (trueCost depth (.bool true) (.bool false) store).erase,
    by intro impossible; cases impossible⟩

theorem typed_values_do_not_replace_the_missing_identity_alignment (store : Core.Store) :
    let table : LocalNameTable := [("x", id 0), ("y", id 1)]
    let scope : Resolved.Context := [(id 0, .bool), (id 1, .bool)]
    let swapped : Resolved.Environment := [(id 1, .bool false), (id 0, .bool true)]
    elaborateTerminalReturnTree? table scope x = some (.var 0, .bool) ∧
    swapped.ids ≠ scope.ids ∧ Core.EnvironmentHasTypes swapped.values scope.values ∧
    TerminalReturnTreeEvaluates table swapped store x (.bool true) store ∧
    Core.Evaluates swapped.values store (.var 0) (.bool false) store ∧
    ¬ Core.Evaluates swapped.values store (.var 0) (.bool true) store := by
  intro table scope swapped
  have exact : TerminalReturnTreeElaborates table scope x (.var 0) .bool :=
    .single (.expression (.identifier .head) (.var .head) (.var .head))
  exact ⟨exact.complete, by decide, .cons .bool (.cons .bool .nil),
    .single (.expression (.identifier .head (.tail (by decide) .head))), .var rfl,
    by intro impossible; cases impossible with | var found => cases found⟩

private def twoNames : LocalNameTable := ("d", id 3) :: names
private def twoEnvironment (outer inner : Bool) (word : Core.Word) : Resolved.Environment :=
  (id 3, .bool inner) :: environment outer (.word word) (.word .zero)
private def asymmetric := branch (ref "c")
  (branch (ref "d") (returned (some ⟨span, .unary ⟨span, .bitNot⟩ (ref "x")⟩)) x) y
private def asymmetricCost (outer inner : Bool) : Nat := if outer then if inner then 9 else 7 else 4
private def asymmetricValue (outer inner : Bool) (word : Core.Word) : Core.Value :=
  .word (if outer then if inner then word.bitNot else word else .zero)
theorem asymmetric_paths_count_only_the_selected_conditions_and_word_operation
    (outer inner : Bool) (word : Core.Word) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost twoNames (twoEnvironment outer inner word) store asymmetric
      (asymmetricValue outer inner word) store (asymmetricCost outer inner) := by
  have c : LocalExpressionEvaluatesWithCost twoNames (twoEnvironment outer inner word) store (ref "c") (.bool outer) store 1 :=
    .identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
  have d : LocalExpressionEvaluatesWithCost twoNames (twoEnvironment outer inner word) store (ref "d") (.bool inner) store 1 := .identifier .head .head
  have selectedX : LocalExpressionEvaluatesWithCost twoNames (twoEnvironment outer inner word) store (ref "x") (.word word) store 1 :=
    .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
  have selectedY : LocalExpressionEvaluatesWithCost twoNames (twoEnvironment outer inner word) store (ref "y") (.word .zero) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  cases outer
  · exact .ifFalse c (.single (.expression selectedY))
  · cases inner
    · exact .ifTrue c (.ifFalse d (.single (.expression selectedX)))
    · exact .ifTrue c (.ifTrue d (.single (.expression (.bitNot selectedX))))

private def bad : Nat → Syntax.Block
  | 0 => returned (some (ref "missing"))
  | depth + 1 => branch (ref "c") bare (bad depth)
private theorem badUntyped (depth : Nat) : ¬ ∃ type, TerminalReturnTreeHasType names (context .word) (bad depth) type := by
  induction depth with
  | zero =>
    rintro ⟨type, typing⟩
    cases typing with
    | single leaf =>
      cases leaf with
      | expression typed =>
        obtain ⟨resolved, resolution, _⟩ := typed.resolves
        have accepted := resolution.complete
        simp [resolveLocalExpression?, ref, names, LocalNameTable.lookup?] at accepted
  | succ depth ih =>
    rintro ⟨type, typing⟩
    cases typing with
    | single leaf => cases leaf
    | conditional _ _ no => exact ih ⟨type, no⟩
theorem a_skipped_arbitrarily_deep_invalid_arm_has_raw_cost_four_but_no_whole_acceptance
    (depth : Nat) (store : Core.Store) :
    TerminalReturnTreeEvaluates names (environment false .unit .unit) store (branch (ref "c") (bad depth) bare) .unit store ∧
    TerminalReturnTreeEvaluatesWithCost names (environment false .unit .unit) store (branch (ref "c") (bad depth) bare) .unit store 4 ∧
    elaborateTerminalReturnTree? names (context .word) (branch (ref "c") (bad depth) bare) = none := by
  refine ⟨.ifFalse (conditionCost false .unit .unit store).erase (.single .bare),
    .ifFalse (conditionCost false .unit .unit store) (.single .bare), ?_⟩
  apply elaborateTerminalReturnTree?_eq_none_iff.mpr
  rintro ⟨type, typing⟩
  cases typing with
  | single leaf => cases leaf
  | conditional _ yes _ => exact badUntyped depth ⟨type, yes⟩

theorem all_old_raw_and_cost_profiles_embed_with_no_extra_steps_or_acceptance_premise
    (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    TerminalReturnTreeEvaluates names (environment choice left right) store x left store ∧
    TerminalReturnTreeEvaluatesWithCost names (environment choice left right) store x left store 1 ∧
    TerminalReturnTreeEvaluates names (environment choice left right) store (spine 1) (if choice then left else right) store ∧
    TerminalReturnTreeEvaluatesWithCost names (environment choice left right) store (spine 1) (if choice then left else right) store 4 ∧
    TerminalReturnTreeEvaluates names (environment choice left right) store bare .unit store ∧
    TerminalReturnTreeEvaluatesWithCost names (environment choice left right) store bare .unit store 1 := by
  have leaf : ReturnBodyEvaluatesWithCost names (environment choice left right) store x left store 1 :=
    .expression (xCost choice left right store)
  have conditional : ConditionalReturnBodyEvaluatesWithCost names (environment choice left right) store (spine 1)
      (if choice then left else right) store 4 := by
    cases choice
    · exact .ifFalse (conditionCost false left right store) (.expression (yCost false left right store))
    · exact .ifTrue (conditionCost true left right store) (.expression (xCost true left right store))
  have terminal : TerminalReturnBodyEvaluatesWithCost names (environment choice left right) store bare .unit store 1 := .single .bare
  have terminalRaw : TerminalReturnBodyEvaluates names (environment choice left right) store bare .unit store := .single .bare
  exact ⟨leaf.erase.returnTree, leaf.returnTree, conditional.erase.returnTree, conditional.returnTree,
    terminalRaw.returnTree, terminal.returnTree⟩

end Tests.FrontendTerminalReturnTreeEvaluation
