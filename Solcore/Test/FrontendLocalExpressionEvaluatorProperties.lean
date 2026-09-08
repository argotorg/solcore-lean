import Solcore.Frontend.LocalExpressionEvaluatorExecutionProperties
import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Core.UnsignedDivision

/-! Independent original-syntax paths fix values and costs before direct execution.
Raw lookup/selected control flow need no typing, and checked paths keep their
separate whole-expression, identity-order and actual-value premises. -/
set_option autoImplicit false
namespace Tests.FrontendLocalExpressionEvaluator
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Direct", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "direct.sol"⟩, 223, 8⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def binary (op : Syntax.BinaryOp) (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, op⟩ right⟩
private def unary (op : Syntax.UnaryOp) (source : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, op⟩ source⟩
private def choose (c t f : Syntax.Expr) : Syntax.Expr := ⟨span, .conditional c span t span f⟩
private def table : LocalNameTable := [("l", id 7), ("r", id 42)]
private def env (left right : Core.Value) : Resolved.Environment := [(id 7, left), (id 42, right)]
private theorem leftRaw (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (env left right) store (ref "l") left store 1 := .identifier .head .head
private theorem rightRaw (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (env left right) store (ref "r") right store 1 :=
  .identifier (.tail (by decide) .head) (.tail (by decide) .head)
private def nest : Nat → Syntax.Expr
  | 0 => ref "r"
  | n + 1 => choose (ref "l") ⟨span, .group (nest n)⟩ (ref "missing")
private theorem nestRaw (n : Nat) {names : LocalNameTable} {values : Resolved.Environment}
    (value : Core.Value) (store : Core.Store)
    (condition : LocalExpressionEvaluatesWithCost names values store (ref "l") (.bool true) store 1)
    (leaf : LocalExpressionEvaluatesWithCost names values store (ref "r") value store 1) :
    LocalExpressionEvaluatesWithCost names values store (nest n) value store (3 * n + 1) := by
  induction n with
  | zero => exact leaf
  | succ n ih =>
      have count : 3 * (n + 1) + 1 = 1 + (3 * n + 1) + 2 := by omega
      rw [count]
      exact .ifTrue condition (.group ih)

theorem arbitrary_depth_selected_paths_keep_original_rows_values_and_exact_cost
    (n : Nat) {names : LocalNameTable} {values : Resolved.Environment} (value : Core.Value) (store : Core.Store)
    (condition : LocalExpressionEvaluatesWithCost names values store (ref "l") (.bool true) store 1)
    (leaf : LocalExpressionEvaluatesWithCost names values store (ref "r") value store 1) :
    evaluateLocalExpressionWithCost? names values (nest n) = some (value, 3 * n + 1) ∧
    ∀ replacement, LocalExpressionEvaluatesWithCost names values replacement (nest n) value replacement (3 * n + 1) := by
  have evaluated := evaluateLocalExpressionWithCost?_complete (nestRaw n value store condition leaf)
  exact ⟨evaluated, fun replacement => evaluateLocalExpressionWithCost?_sound evaluated replacement⟩

theorem duplicate_names_and_ids_keep_first_matches_without_alignment (value hidden : Core.Value) (store final : Core.Store) :
    let names := [("r", id 42), ("r", id 7), ("l", id 7)]
    let values := [(id 42, value), (id 42, hidden), (id 7, .bool true)]
    evaluateLocalExpressionWithCost? names values (ref "r") = some (value, 1) ∧
    (evaluateLocalExpressionWithCost? names values (ref "r")).map Prod.fst = some value ∧
    (LocalExpressionEvaluatesWithCost names values store (ref "r") value final 1 ↔ final = store) := by
  dsimp
  have raw : LocalExpressionEvaluatesWithCost [("r", id 42), ("r", id 7), ("l", id 7)]
      [(id 42, value), (id 42, hidden), (id 7, .bool true)] store (ref "r") value store 1 := .identifier .head .head
  have evaluated := (evaluateLocalExpressionWithCost?_iff store).mpr raw
  exact ⟨evaluated, (evaluateLocalExpressionWithCost?_value_iff store).mpr raw.erase, by
    rw [localExpressionEvaluatesWithCost_iff_evaluate, evaluated]; simp⟩

private inductive Strict where | add | sub | mul | div | mod | band | bor | bxor | gt | lt | eq | ne | le | ge
private def op : Strict → Syntax.BinaryOp
  | .add => .add | .sub => .subtract | .mul => .multiply | .div => .divide | .mod => .modulo
  | .band => .bitAnd | .bor => .bitOr | .bxor => .bitXor | .gt => .greater | .lt => .less
  | .eq => .equal | .ne => .notEqual | .le => .lessEqual | .ge => .greaterEqual
private def answer (kind : Strict) (left right : Core.Word) : Core.Value :=
  match kind with
  | .add => .word (left.add right) | .sub => .word (left.sub right) | .mul => .word (left.mul right)
  | .div => .word (left.udiv right) | .mod => .word (left.umod right)
  | .band => .word (left.bitAnd right) | .bor => .word (left.bitOr right) | .bxor => .word (left.bitXor right)
  | .gt => .bool (decide (left > right)) | .lt => .bool (decide (left < right)) | .eq => .bool (left == right)
  | .ne => .bool (!(left == right)) | .le => .bool (!(decide (left > right))) | .ge => .bool (!(decide (left < right)))
private def overhead : Strict → Nat | .ne | .le => 5 | .lt => 9 | .ge => 11 | _ => 3
private theorem strictRaw (kind : Strict) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (env (.word left) (.word right)) store
      (binary (op kind) (ref "l") (ref "r")) (answer kind left right) store (2 + overhead kind) := by
  have l := leftRaw (.word left) (.word right) store
  have r := rightRaw (.word left) (.word right) store
  cases kind
  · exact .add l r
  · exact .subtract l r
  · exact .multiply l r
  · exact .divide l r
  · exact .modulo l r
  · exact .bitAnd l r
  · exact .bitOr l r
  · exact .bitXor l r
  · exact .greater l r
  · exact .less l r
  · exact .equal l r
  · exact .notEqual l r
  · exact .lessEqual l r
  · exact .greaterEqual l r

theorem all_fourteen_strict_word_operators_have_independent_values_and_overheads
    (kind : Strict) (left right : Core.Word) (store : Core.Store) :
    evaluateLocalWordBinaryWithCost? (op kind) left right = some (answer kind left right, overhead kind) ∧
    LocalExpressionEvaluatesWithCost table (env (.word left) (.word right)) store
      (binary (op kind) (ref "l") (ref "r")) (answer kind left right) store (2 + overhead kind) ∧
    evaluateLocalExpressionWithCost? table (env (.word left) (.word right))
      (binary (op kind) (ref "l") (ref "r")) = some (answer kind left right, 2 + overhead kind) :=
  ⟨by cases kind <;> rfl, strictRaw kind left right store, evaluateLocalExpressionWithCost?_complete (strictRaw kind left right store)⟩

theorem unary_shapes_and_selected_short_circuits_forward_actual_opaque_values
    (flag : Bool) (word : Core.Word) (value : Core.Value) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env (.bool flag) (.word word)) (unary .logicalNot (ref "l")) = some (.bool (!flag), 3) ∧
    evaluateLocalExpressionWithCost? table (env (.bool flag) (.word word)) (unary .bitNot (ref "r")) = some (.word word.bitNot, 3) ∧
    evaluateLocalExpressionWithCost? table (env (.bool true) value) (binary .logicalAnd (ref "l") (ref "r")) = some (value, 4) ∧
    evaluateLocalExpressionWithCost? table (env (.bool false) value) (binary .logicalOr (ref "l") (ref "r")) = some (value, 4) ∧
    elaborateLocalExpression? table [(id 7, .bool), (id 42, .unit)] (binary .logicalAnd (ref "l") (ref "r")) = none ∧
    elaborateLocalExpression? table [(id 7, .bool), (id 42, .unit)] (binary .logicalOr (ref "l") (ref "r")) = none :=
  ⟨evaluateLocalExpressionWithCost?_complete (.logicalNot (leftRaw _ _ store)),
    evaluateLocalExpressionWithCost?_complete (.bitNot (rightRaw _ _ store)),
    evaluateLocalExpressionWithCost?_complete (.andTrue (leftRaw _ _ store) (rightRaw _ _ store)),
    evaluateLocalExpressionWithCost?_complete (.orFalse (leftRaw _ _ store) (rightRaw _ _ store)),
    by simp only [elaborateLocalExpression?, binary, ref, resolveLocalExpression?]; rfl,
    by simp only [elaborateLocalExpression?, binary, ref, resolveLocalExpression?]; rfl⟩

theorem skipped_children_need_no_meaning_but_whole_checking_still_does
    (value : Core.Value) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env (.bool false) value) (binary .logicalAnd (ref "l") (ref "missing")) = some (.bool false, 4) ∧
    evaluateLocalExpressionWithCost? table (env (.bool true) value) (binary .logicalOr (ref "l") (ref "missing")) = some (.bool true, 4) ∧
    evaluateLocalExpressionWithCost? table (env (.bool false) value) (choose (ref "l") (ref "missing") (ref "r")) = some (value, 4) ∧
    resolveLocalExpression? table (choose (ref "l") (ref "missing") (ref "r")) = none :=
  ⟨evaluateLocalExpressionWithCost?_complete (.andFalse (leftRaw _ _ store)),
    evaluateLocalExpressionWithCost?_complete (.orTrue (leftRaw _ _ store)),
    evaluateLocalExpressionWithCost?_complete (.ifFalse (leftRaw _ _ store) (rightRaw _ _ store)),
    by simp [resolveLocalExpression?, choose, ref, table, LocalNameTable.lookup?]⟩

theorem strict_missing_or_wrong_shaped_operands_do_not_gain_a_raw_path
    (kind : Strict) (word : Core.Word) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env .unit (.word word)) (binary (op kind) (ref "l") (ref "r")) = none ∧
    evaluateLocalExpressionWithCost? table (env (.word word) .unit) (binary (op kind) (ref "l") (ref "r")) = none ∧
    ¬ ∃ value cost, LocalExpressionEvaluatesWithCost table (env (.word .zero) (.word .zero)) store
      (binary .divide (ref "missing") (ref "r")) value store cost := by
  refine ⟨?_, ?_, (evaluateLocalExpressionWithCost?_eq_none_iff store).mp (by
    simp [evaluateLocalExpressionWithCost?, binary, ref, table, LocalNameTable.lookup?])⟩
  all_goals cases kind <;> simp [evaluateLocalExpressionWithCost?, binary, op, ref, table, env, id, LocalNameTable.lookup?, Resolved.LocalScope.lookup?]

private def literal (value : Syntax.CoreLiteralValue) : Syntax.Expr := ⟨span, .literal ⟨span, value⟩⟩
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
theorem strict_literal_payloads_and_zero_divisors_do_not_change_source_cost
    (word : Core.Word) (store : Core.Store) :
    evaluateLocalExpressionWithCost? [] [] (literal (.decimal "0")) = some (.word .zero, 1) ∧
    evaluateLocalExpressionWithCost? [] [] (literal (.decimal "12x")) = none ∧
    evaluateLocalExpressionWithCost? [] [] (literal (.hexadecimal "0Xff")) = none ∧
    evaluateLocalExpressionWithCost? [] [] (literal (.string "0")) = none ∧
    evaluateLocalExpressionWithCost? table (env (.word word) (.word .zero)) (binary .divide (ref "l") (ref "r")) = some (.word .zero, 5) ∧
    evaluateLocalExpressionWithCost? table (env (.word word) (.word .zero)) (binary .modulo (ref "l") (ref "r")) = some (.word .zero, 5) := by
  refine ⟨evaluateLocalExpressionWithCost?_complete (.wordLiteral (store := store) zeroMeaning),
    by simp only [evaluateLocalExpressionWithCost?, literal]; decide,
    by simp only [evaluateLocalExpressionWithCost?, literal]; decide,
    by simp only [evaluateLocalExpressionWithCost?, literal]; decide, ?_, ?_⟩
  · simpa [answer, overhead, op, Core.Word.udiv_zero] using evaluateLocalExpressionWithCost?_complete (strictRaw .div word .zero store)
  · simpa [answer, overhead, op, Core.Word.umod_zero] using evaluateLocalExpressionWithCost?_complete (strictRaw .mod word .zero store)

private def context : Resolved.Context := [(id 7, .word), (id 42, .word)]
private def subtraction := binary .subtract (ref "l") (ref "r")
private def subtractionCore : Core.Expr := .binary .wordSub (.var 0) (.var 1)
private theorem checked : elaborateLocalExpression? table context subtraction = some (subtractionCore, .word) :=
  elaborateLocalExpression?_complete (.subtract (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.binary (.var .head) (.var (.tail (by decide) .head))) (.binary (.var .head) (.var (.tail (by decide) .head)))
private theorem subOutput (left right : Core.Word) :
    evaluateLocalExpressionWithCost? table (env (.word left) (.word right)) subtraction = some (.word (left.sub right), 5) :=
  evaluateLocalExpressionWithCost?_complete (strictRaw .sub left right [])

theorem independently_checked_subtraction_retains_continuations_and_all_fuel
    (left right : Core.Word) (store final : Core.Store) (fuel : Nat) (continuation : List Core.Frame) :
    Core.Steps 5 ⟨.eval subtractionCore [.word left, .word right], continuation, store⟩
      ⟨.ret (.word (left.sub right)), continuation, store⟩ ∧
    (Core.runStateful fuel (Core.State.initial subtractionCore [.word left, .word right] store) =
      .done (.word (left.sub right)) store ↔ 5 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (Core.State.initial subtractionCore [.word left, .word right] store) =
      .outOfFuel checkpoint) ↔ fuel < 5) ∧
    (Core.runStateful fuel (Core.State.initial subtractionCore [.word left, .word right] store) =
      .done (.word (left.sub right)) final ↔ final = store ∧ 5 ≤ fuel) := by
  refine ⟨evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation (subOutput left right) checked rfl continuation,
    evaluateLocalExpressionWithCost?_checked_runStateful_done_iff (subOutput left right) checked rfl,
    evaluateLocalExpressionWithCost?_checked_runStateful_outOfFuel_iff (subOutput left right) checked rfl, ?_⟩
  have reflected := elaborateLocalExpression?_run_done_iff_evaluator (environment := env (.word left) (.word right))
      (initialStore := store) (finalStore := final) (value := .word (left.sub right)) (fuel := fuel) checked rfl
  rw [subOutput] at reflected
  simpa [env, Resolved.LocalScope.values] using reflected

private def inputs (left right : Core.Word) : LocalInputs :=
  ⟨[⟨"l", id 7, .word, .word left, .word⟩, ⟨"r", id 42, .word, .word right, .word⟩], by change [id 7, id 42].Nodup; decide⟩
private theorem inputTyped (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context subtraction .word :=
  .subtract (.identifier .head .head) (.identifier (.tail (by change "l" ≠ "r"; decide) .head)
    (.tail (by change id 7 ≠ id 42; decide) .head))

theorem actual_typed_input_wrappers_recover_the_independent_exact_cost
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 5 subtraction store = some (.word, .done (.word (left.sub right)) store) ∧
    (∃ checkpoint, (inputs left right).run? 4 subtraction store = some (.word, .outOfFuel checkpoint)) ∧
    ∀ fuel, ((inputs left right).run? fuel subtraction store = some (.word, .done (.word (left.sub right)) store) ↔ 5 ≤ fuel) ∧
      ((∃ checkpoint, (inputs left right).run? fuel subtraction store = some (.word, .outOfFuel checkpoint)) ↔ fuel < 5) := by
  refine ⟨LocalInputs.run?_done_iff_evaluator.mpr ⟨inputTyped left right, rfl, 5, subOutput left right, by decide⟩,
    LocalInputs.run?_outOfFuel_iff_evaluator.mpr ⟨inputTyped left right, .word (left.sub right), 5, subOutput left right, by decide⟩, ?_⟩
  obtain ⟨value, cost, output, _, thresholds⟩ := LocalInputs.typed_evaluator_execution (inputTyped left right) store
  have exactPair := (subOutput left right).symm.trans output
  cases Option.some.inj exactPair
  exact thresholds

theorem typed_existence_needs_actual_values_and_raw_projection_preserves_them
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) (store : Core.Store) :
    (∃ actual cost, evaluateLocalExpressionWithCost? table (env value .unit) (ref "l") = some (actual, cost) ∧
      Core.ValueHasType actual type) ∧
    (∃ cost, evaluateLocalExpressionWithCost? table (env value .unit) (ref "l") = some (value, cost)) := by
  have accepted : elaborateLocalExpression? table [(id 7, type), (id 42, .unit)] (ref "l") = some (.var 0, type) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  exact ⟨elaborateLocalExpression?_typed_evaluator_exists accepted rfl (.cons typed (.cons .unit .nil)),
    (evaluateLocalExpressionWithCost?_exists_cost_iff store).mpr (leftRaw value .unit store).erase⟩

theorem aligned_untyped_values_are_not_typed_results_and_misalignment_changes_lookup (store : Core.Store) :
    elaborateLocalExpression? table context (ref "l") = some (.var 0, .word) ∧
    evaluateLocalExpressionWithCost? table (env (.bool true) (.word .zero)) (ref "l") = some (.bool true, 1) ∧
    Core.Steps 1 (Core.State.initial (.var 0) [.bool true, .word .zero] store) (Core.State.final (.bool true) store) ∧
    (¬ Core.ValueHasType (.bool true) .word) ∧
    evaluateLocalExpressionWithCost? table [(id 42, .word .zero), (id 7, .word .maximum)] (ref "l") = some (.word .maximum, 1) ∧
    Core.runStateful 1 (Core.State.initial (.var 0) [.word .zero, .word .maximum] store) = .done (.word .zero) store := by
  have accepted : elaborateLocalExpression? table context (ref "l") = some (.var 0, .word) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  have output := evaluateLocalExpressionWithCost?_complete (leftRaw (.bool true) (.word .zero) store)
  exact ⟨accepted, output, evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation output accepted rfl [],
    (by intro bad; cases bad), evaluateLocalExpressionWithCost?_complete
      (.identifier (store := store) .head (.tail (by decide) .head)), rfl⟩

private def pending (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word right), [.binaryApply .wordSub (.word left)], store⟩
theorem actual_ordered_checkpoint_resumes_but_cannot_drop_its_pending_operation
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    Core.runStateful 4 (Core.State.initial subtractionCore [.word left, .word right] store) = .outOfFuel (pending left right store) ∧
    Core.Steps 1 (pending left right store) (Core.State.final (.word (left.sub right)) store) ∧
    Core.runStateful additional (pending left right store) =
      Core.runStateful (4 + additional) (Core.State.initial subtractionCore [.word left, .word right] store) ∧
    Core.runStateful 0 (pending left right store) = .outOfFuel (pending left right store) ∧
    Core.runStateful 0 (Core.State.final (.word right) store) = .done (.word right) store ∧
    Core.HasType [.word, .word] (.binary .wordSub (.var 1) (.var 0)) .word ∧
    elaborateLocalExpression? table context subtraction ≠ some (.binary .wordSub (.var 1) (.var 0), .word) := by
  have exhausted : Core.runStateful 4 (Core.State.initial subtractionCore [.word left, .word right] store) =
      .outOfFuel (pending left right store) := rfl
  refine ⟨exhausted, ((strictRaw .sub left right store).checked_residual_of_outOfFuel checked rfl exhausted).2,
    Core.runStateful_resume exhausted additional, rfl, rfl, .binary (.var rfl) (.var rfl), ?_⟩
  rw [checked]
  intro bad
  cases bad

theorem selected_unsupported_forms_and_wrong_boolean_guards_remain_absent (word : Core.Word) :
    evaluateLocalExpressionWithCost? table (env (.word word) .unit) ⟨span, .call (ref "r") ⟨span, []⟩⟩ = none ∧
    evaluateLocalExpressionWithCost? table (env .unit (.word word)) (choose (ref "l") (ref "r") (ref "r")) = none ∧
    evaluateLocalExpressionWithCost? table (env (.bool true) .unit) (binary .logicalAnd (ref "l") (ref "missing")) = none ∧
    evaluateLocalExpressionWithCost? table (env (.word word) .unit) (unary .logicalNot (ref "l")) = none ∧
    evaluateLocalExpressionWithCost? table (env (.bool true) .unit) (unary .bitNot (ref "l")) = none ∧
    evaluateLocalWordBinaryWithCost? .logicalAnd word word = none ∧
    evaluateLocalWordBinaryWithCost? .logicalOr word word = none := by
  simp [evaluateLocalExpressionWithCost?, evaluateLocalWordBinaryWithCost?, unary, binary, choose, ref, table, env, LocalNameTable.lookup?, Resolved.LocalScope.lookup?]

theorem arbitrary_depth_has_actual_opaque_instances_despite_unselected_rejection
    (depth location : Nat) (captured : Core.Word) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env (.bool true) (.cellRef .word location)) (nest depth) =
      some (.cellRef .word location, 3 * depth + 1) ∧
    evaluateLocalExpressionWithCost? table (env (.bool true) (.closure .bool .word (.var 1) [.word captured])) (nest depth) =
      some (.closure .bool .word (.var 1) [.word captured], 3 * depth + 1) ∧
    resolveLocalExpression? table (nest (depth + 1)) = none := by
  refine ⟨evaluateLocalExpressionWithCost?_complete (nestRaw depth _ store (leftRaw _ _ store) (rightRaw _ _ store)),
    evaluateLocalExpressionWithCost?_complete (nestRaw depth _ store (leftRaw _ _ store) (rightRaw _ _ store)), ?_⟩
  apply resolveLocalExpression?_eq_none_iff.mpr
  rintro ⟨resolved, resolution⟩
  cases resolution with
  | conditional _ _ missing =>
      have impossible := missing.complete
      simp [resolveLocalExpression?, ref, table, LocalNameTable.lookup?] at impossible

end Tests.FrontendLocalExpressionEvaluator
