import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Frontend.LocalExpressionLookupProperties
import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Frontend.LocalExpressionFuelBound
import Solcore.Frontend.LocalExpressionStoreProperties
import Solcore.Frontend.TypeName

/-! Original two-element syntax, independent expected products and exact paths.
Static types never manufacture actual values; raw short circuits keep their boundary. -/
set_option autoImplicit false
namespace Tests.FrontendBinaryTuple
open Solcore Solcore.Frontend
private def ref (span nameSpan : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨span, .identifier ⟨nameSpan, name⟩⟩
private def pair (span tupleSpan : Syntax.SourceSpan) (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .tuple ⟨tupleSpan, [left, right]⟩⟩
private def source (span tupleSpan nameSpan : Syntax.SourceSpan) (name : String) : Nat → Syntax.Expr
  | 0 => ref span nameSpan name
  | n + 1 => pair span tupleSpan (ref span nameSpan name) (source span tupleSpan nameSpan name n)
private def resolved (id : Resolved.LocalId) : Nat → Resolved.Expr
  | 0 => .var id
  | n + 1 => .pair (.var id) (resolved id n)
private def core : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .pair (.var 0) (core n)
private def product (type : Core.Ty) : Nat → Core.Ty
  | 0 => type
  | n + 1 => .product type (product type n)
private def value (actual : Core.Value) : Nat → Core.Value
  | 0 => actual
  | n + 1 => .pair actual (value actual n)
private theorem resolution {s t p : Syntax.SourceSpan} {name : String} (id : Resolved.LocalId) (table : LocalNameTable) (n : Nat) :
    ResolvesLocalExpression ((name, id) :: table) (source s t p name n) (resolved id n) := by
  induction n with
  | zero => exact .identifier .head
  | succ n ih => exact .pair (.identifier .head) ih
private theorem typed {s t p : Syntax.SourceSpan} {name : String} (id : Resolved.LocalId) (table : LocalNameTable)
    (context : Resolved.Context) (type : Core.Ty) (n : Nat) :
    LocalExpressionHasType ((name, id) :: table) ((id, type) :: context) (source s t p name n) (product type n) := by
  induction n with
  | zero => exact .identifier .head .head
  | succ n ih => exact .pair (.identifier .head .head) ih
private theorem lowered (id : Resolved.LocalId) (scope : List Resolved.LocalId) (n : Nat) :
    Resolved.Lowers (id :: scope) (resolved id n) (core n) := by
  induction n with
  | zero => exact .var .head
  | succ n ih => exact .pair (.var .head) ih
private theorem resolvedTyped (id : Resolved.LocalId) (context : Resolved.Context) (type : Core.Ty) (n : Nat) :
    Resolved.HasType ((id, type) :: context) (resolved id n) (product type n) := by
  induction n with
  | zero => exact .var .head
  | succ n ih => exact .pair (.var .head) ih
private theorem checked {s t p : Syntax.SourceSpan} {name : String} (id : Resolved.LocalId) (table : LocalNameTable)
    (context : Resolved.Context) (type : Core.Ty) (n : Nat) :
    elaborateLocalExpression? ((name, id) :: table) ((id, type) :: context) (source s t p name n) = some (core n, product type n) :=
  elaborateLocalExpression?_complete (resolution id table n) (lowered id _ n) (resolvedTyped id context type n)
private theorem costed {s t p : Syntax.SourceSpan} {name : String} (id : Resolved.LocalId) (table : LocalNameTable)
    (environment : Resolved.Environment) (actual : Core.Value) (store : Core.Store) (n : Nat) :
    LocalExpressionEvaluatesWithCost ((name, id) :: table) ((id, actual) :: environment) store (source s t p name n) (value actual n) store (4 * n + 1) := by
  induction n with
  | zero => exact .identifier .head .head
  | succ n ih =>
      have count : 4 * (n + 1) + 1 = 1 + (4 * n + 1) + 3 := by omega
      rw [count]
      exact .pair (.identifier .head .head) ih
private theorem bound (s t p : Syntax.SourceSpan) (name : String) (n : Nat) :
    localExpressionFuelBound (source s t p name n) = 4 * n + 1 := by
  induction n with
  | zero => simp [source, ref, localExpressionFuelBound]
  | succ n ih => simp [source, pair, ref, localExpressionFuelBound, ih, Nat.mul_add] <;> omega
private theorem path (actual : Core.Value) (environment : Core.Environment) (store : Core.Store) (n : Nat) :
    ∀ k, Core.Steps (4 * n + 1) ⟨.eval (core n) (actual :: environment), k, store⟩ ⟨.ret (value actual n), k, store⟩ := by
  induction n with
  | zero => intro k; exact .cons (.var rfl) .refl
  | succ n ih =>
      intro k
      have steps := Core.Steps.cons .enterPair (.cons (.var (index := 0) rfl) (.cons .enterPairRight
        ((ih (.pairApply actual :: k)).trans (.cons .applyPair .refl))))
      simpa [core, value, Nat.mul_add, Nat.add_assoc] using steps

theorem arbitrary_spans_names_and_types_have_independent_whole_provenance
    (s t p : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (table : LocalNameTable)
    (context : Resolved.Context) (type : Core.Ty) (n : Nat) :
    ResolvesLocalExpression ((name, id) :: table) (source s t p name n) (resolved id n) ∧
    LocalExpressionHasType ((name, id) :: table) ((id, type) :: context) (source s t p name n) (product type n) ∧
    elaborateLocalExpression? ((name, id) :: table) ((id, type) :: context) (source s t p name n) = some (core n, product type n) ∧
    localExpressionFuelBound (source s t p name n) = 4 * n + 1 :=
  ⟨resolution id table n, typed id table context type n, checked id table context type n, bound s t p name n⟩

theorem arbitrary_actual_values_have_exact_direct_results_and_store_replay
    (s t p : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (table : LocalNameTable)
    (environment : Resolved.Environment) (actual : Core.Value) (store final replacement : Core.Store) (n : Nat) :
    evaluateLocalExpressionWithCost? ((name, id) :: table) ((id, actual) :: environment) (source s t p name n) = some (value actual n, 4 * n + 1) ∧
    LocalExpressionEvaluatesWithCost ((name, id) :: table) ((id, actual) :: environment) replacement (source s t p name n) (value actual n) replacement (4 * n + 1) ∧
    4 * n + 1 ≤ localExpressionFuelBound (source s t p name n) ∧
    (LocalExpressionEvaluatesWithCost ((name, id) :: table) ((id, actual) :: environment) store (source s t p name n) (value actual n) final (4 * n + 1) ↔ final = store) := by
  have raw := costed (s := s) (t := t) (p := p) (name := name) id table environment actual store n
  have direct := evaluateLocalExpressionWithCost?_complete raw
  refine ⟨direct, raw.change_store replacement, raw.cost_le_fuelBound, ?_⟩
  rw [localExpressionEvaluatesWithCost_iff_evaluate, direct]
  simp

theorem independently_counted_paths_keep_outer_frames_and_every_fuel_threshold
    (s t p : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (actual : Core.Value)
    (store : Core.Store) (n fuel : Nat) (k : List Core.Frame) :
    Core.Steps (4 * n + 1) ⟨.eval (core n) [actual], k, store⟩ ⟨.ret (value actual n), k, store⟩ ∧
    (Core.runStateful fuel (.initial (core n) [actual] store) = .done (value actual n) store ↔ 4 * n + 1 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (.initial (core n) [actual] store) = .outOfFuel checkpoint) ↔ fuel < 4 * n + 1) := by
  have direct := evaluateLocalExpressionWithCost?_complete (costed (s := s) (t := t) (p := p) (name := name) id [] [] actual store n)
  have accepted := checked (s := s) (t := t) (p := p) (name := name) id [] [] .word n
  exact ⟨path actual [] store n k,
    evaluateLocalExpressionWithCost?_checked_runStateful_done_iff direct accepted rfl,
    evaluateLocalExpressionWithCost?_checked_runStateful_outOfFuel_iff direct accepted rfl⟩

theorem first_match_duplicates_and_injective_ids_keep_the_same_raw_product
    (s t p : Syntax.SourceSpan) (name : String) (id other : Resolved.LocalId) (actual hidden : Core.Value) (n : Nat)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    evaluateLocalExpressionWithCost? [(name, id), (name, other)] [(id, actual), (id, hidden)] (source s t p name n) = some (value actual n, 4 * n + 1) ∧
    LocalExpressionEvaluates (LocalNameTable.mapIds mapping [(name, id)]) (Resolved.LocalScope.mapIds mapping [(id, actual)]) []
      (source s t p name n) (value actual n) [] := by
  have same : ∀ key, (LocalNameTable.lookup? [(name, id)] key).bind (Resolved.LocalScope.lookup? [(id, actual)]) =
      (LocalNameTable.lookup? [(name, id), (name, other)] key).bind (Resolved.LocalScope.lookup? [(id, actual), (id, hidden)]) := by
    intro key
    by_cases equal : name = key
    · subst key; simp [LocalNameTable.lookup?, Resolved.LocalScope.lookup?]
    · simp [LocalNameTable.lookup?, equal]
  have direct := evaluateLocalExpressionWithCost?_complete (costed (s := s) (t := t) (p := p) (name := name) id [] [] actual [] n)
  exact ⟨(evaluateLocalExpressionWithCost?_congr_lookup _ _ _ _ same _).symm.trans direct,
    (localExpressionEvaluates_mapIds_iff mapping injective).mpr (costed id [] [] actual [] n).erase⟩

private def inputs (name : String) (id : Resolved.LocalId) (type : Core.Ty) (actual : Core.Value) (evidence : Core.ValueHasType actual type) : LocalInputs :=
  ⟨[⟨name, id, type, actual, evidence⟩], by simp⟩
theorem unused_fresh_inputs_preserve_typed_pair_results_at_the_same_fuel
    (s t p : Syntax.SourceSpan) (name extra : String) (different : extra ≠ name) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (type : Core.Ty) (actual : Core.Value) (evidence : Core.ValueHasType actual type)
    (store : Core.Store) (n fuel : Nat) :
    let original := inputs name id type actual evidence
    original.run? (4 * n + 1) (source s t p name n) store = some (product type n, .done (value actual n) store) ∧
    ((original.bindFresh owner extra .unit .unit .unit).run? fuel (source s t p name n) store = some (product type n, .done (value actual n) store) ↔
      original.run? fuel (source s t p name n) store = some (product type n, .done (value actual n) store)) := by
  dsimp
  have avoids : AvoidsLocalName extra (source s t p name n) := by
    induction n with
    | zero => exact .identifier different
    | succ n ih => exact .pair (.identifier different) ih
  exact ⟨LocalInputs.run?_done_iff_evaluator.mpr ⟨typed id [] [] type n, rfl, 4 * n + 1,
      evaluateLocalExpressionWithCost?_complete (costed id [] [] actual store n), Nat.le_refl _⟩,
    avoids.bindFresh_run_done_at_fuel_iff _ owner .unit .unit .unit⟩

theorem nominal_types_do_not_supply_actual_values_and_opaque_values_need_no_typing
    (s t p : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (nominal : Core.DataTypeId)
    (location : Core.Location) (captured : Core.Value) (n : Nat) :
    elaborateLocalExpression? [(name, id)] [(id, .namedData nominal)] (source s t p name (n + 1)) = some (core (n + 1), product (.namedData nominal) (n + 1)) ∧
    (¬ ∃ actual, Core.ValueHasType actual (.namedData nominal)) ∧
    evaluateLocalExpressionWithCost? [(name, id)] [(id, .pair (.cellRef .word location) (.closure .word .bool (.var 80) [captured]))]
      (source s t p name n) = some (value (.pair (.cellRef .word location) (.closure .word .bool (.var 80) [captured])) n, 4 * n + 1) := by
  refine ⟨checked id [] [] _ _, ?_, evaluateLocalExpressionWithCost?_complete (costed id [] [] _ [] n)⟩
  rintro ⟨actual, typedValue⟩
  cases typedValue with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def span : Syntax.SourceSpan := ⟨⟨.main, "tuple.sol"⟩, 230, 7⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"BinaryTuple", by decide⟩], by decide⟩⟩, 0⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def atom (name : String) := ref span span name
private def table : LocalNameTable := [("x", id 0), ("y", id 1), ("c", id 2)]
private def env (left right : Core.Value) : Resolved.Environment := [(id 0, left), (id 1, right)]
private def two := pair span span (atom "x") (atom "y")
private def twoCore : Core.Expr := .pair (.var 0) (.var 1)
private theorem twoRaw (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (env left right) store two (.pair left right) store 5 := by
  apply LocalExpressionEvaluatesWithCost.pair (leftCost := 1) (rightCost := 1)
  · exact .identifier .head .head
  · exact .identifier (.tail (by decide) .head) (.tail (by decide) .head)
private theorem twoChecked (type : Core.Ty) :
    elaborateLocalExpression? table [(id 0, type), (id 1, type)] two = some (twoCore, .product type type) :=
  elaborateLocalExpression?_complete (.pair (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.pair (.var .head) (.var (.tail (by change id 0 ≠ id 1; decide) .head)))
    (.pair (.var .head) (.var (.tail (by change id 0 ≠ id 1; decide) .head)))
private def binary (operator : Syntax.BinaryOp) (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, operator⟩ right⟩
private def choose (condition yes no : Syntax.Expr) : Syntax.Expr := ⟨span, .conditional condition span yes span no⟩
private def guardEnvironment (choice : Bool) (left right : Core.Value) := env left right ++ [(id 2, .bool choice)]
private theorem guardRaw (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (guardEnvironment choice left right) store (atom "c") (.bool choice) store 1 :=
  .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
private theorem guardedPair (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (guardEnvironment choice left right) store two (.pair left right) store 5 := by
  apply LocalExpressionEvaluatesWithCost.pair (leftCost := 1) (rightCost := 1)
  · exact .identifier .head .head
  · exact .identifier (.tail (by decide) .head) (.tail (by decide) .head)

theorem true_and_false_or_forward_arbitrary_actual_pairs_but_whole_boolean_checking_rejects
    (left right : Core.Value) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (guardEnvironment true left right) (binary .logicalAnd (atom "c") two) = some (.pair left right, 8) ∧
    evaluateLocalExpressionWithCost? table (guardEnvironment false left right) (binary .logicalOr (atom "c") two) = some (.pair left right, 8) ∧
    elaborateLocalExpression? table [(id 0, .unit), (id 1, .unit), (id 2, .bool)] (binary .logicalAnd (atom "c") two) = none ∧
    elaborateLocalExpression? table [(id 0, .unit), (id 1, .unit), (id 2, .bool)] (binary .logicalOr (atom "c") two) = none :=
  ⟨evaluateLocalExpressionWithCost?_complete (.andTrue (guardRaw true left right store) (guardedPair true left right store)),
    evaluateLocalExpressionWithCost?_complete (.orFalse (guardRaw false left right store) (guardedPair false left right store)),
    by simp only [elaborateLocalExpression?, resolveLocalExpression?, binary, two, pair, atom, ref]; rfl,
    by simp only [elaborateLocalExpression?, resolveLocalExpression?, binary, two, pair, atom, ref]; rfl⟩

theorem unselected_missing_children_are_skipped_but_tuple_children_are_strict
    (left right : Core.Value) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (guardEnvironment true left right) (choose (atom "c") two (atom "missing")) = some (.pair left right, 8) ∧
    resolveLocalExpression? table (choose (atom "c") two (atom "missing")) = none ∧
    evaluateLocalExpressionWithCost? table (env left right) (pair span span (atom "x") (atom "missing")) = none ∧
    ¬ ∃ result cost, LocalExpressionEvaluatesWithCost table (env left right) store (pair span span (atom "missing") (atom "y")) result store cost := by
  refine ⟨evaluateLocalExpressionWithCost?_complete (.ifTrue (guardRaw true left right store) (guardedPair true left right store)), ?_, ?_, ?_⟩
  · simp [resolveLocalExpression?, choose, atom, ref, two, pair, table, LocalNameTable.lookup?]
  · simp [evaluateLocalExpressionWithCost?, pair, atom, ref, table, env, LocalNameTable.lookup?, Resolved.LocalScope.lookup?]
  · apply (evaluateLocalExpressionWithCost?_eq_none_iff store).mp
    simp [evaluateLocalExpressionWithCost?, pair, atom, ref, table, LocalNameTable.lookup?]

theorem real_pair_checkpoint_keeps_left_value_and_resumes_the_last_step
    (left right : Core.Value) (store : Core.Store) (additional : Nat) (type : Core.Ty) :
    Core.runStateful 4 (.initial twoCore [left, right] store) = .outOfFuel ⟨.ret right, [.pairApply left], store⟩ ∧
    Core.Steps 1 ⟨.ret right, [.pairApply left], store⟩ (.final (.pair left right) store) ∧
    Core.runStateful additional ⟨.ret right, [.pairApply left], store⟩ = Core.runStateful (4 + additional) (.initial twoCore [left, right] store) ∧
    Core.HasType [type, type] (.pair (.var 1) (.var 0)) (.product type type) ∧
    elaborateLocalExpression? table [(id 0, type), (id 1, type)] two ≠ some (.pair (.var 1) (.var 0), .product type type) := by
  have exhausted : Core.runStateful 4 (.initial twoCore [left, right] store) = .outOfFuel ⟨.ret right, [.pairApply left], store⟩ := rfl
  refine ⟨exhausted, ((twoRaw left right store).checked_residual_of_outOfFuel (twoChecked type) rfl exhausted).2,
    Core.runStateful_resume exhausted additional, .pair (.var rfl) (.var rfl), ?_⟩
  rw [twoChecked]
  intro wrong
  cases wrong

theorem manual_singleton_tuples_and_old_named_type_tuple_gates_remain_rejections
    (s t : Syntax.SourceSpan) (elements : List Syntax.Expr) (singleton : elements.length = 1)
    (types : TypeNameTable) (typeElements : List Syntax.TypeExpr) :
    resolveLocalExpression? table ⟨s, .tuple ⟨t, elements⟩⟩ = none ∧
    evaluateLocalExpressionWithCost? table [] ⟨s, .tuple ⟨t, elements⟩⟩ = none ∧
    interpretTypeName? types ⟨s, .tuple typeElements⟩ = none := by
  rcases elements with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  all_goals simp_all [resolveLocalExpression?, evaluateLocalExpressionWithCost?, interpretTypeName?]

theorem a_successful_pair_does_not_enable_projection_index_or_array_syntax
    (left right : Core.Value) :
    evaluateLocalExpressionWithCost? table (env left right) two = some (.pair left right, 5) ∧
    resolveLocalExpression? table ⟨span, .field two span ⟨span, "first"⟩⟩ = none ∧
    evaluateLocalExpressionWithCost? table (env left right) ⟨span, .field two span ⟨span, "first"⟩⟩ = none ∧
    resolveLocalExpression? table ⟨span, .index two span (atom "x")⟩ = none ∧
    evaluateLocalExpressionWithCost? table (env left right) ⟨span, .array ⟨span, [atom "x", atom "y"]⟩⟩ = none := by
  exact ⟨evaluateLocalExpressionWithCost?_complete (twoRaw left right []), by simp only [resolveLocalExpression?],
    by simp only [evaluateLocalExpressionWithCost?], by simp only [resolveLocalExpression?],
    by simp only [evaluateLocalExpressionWithCost?]⟩

end Tests.FrontendBinaryTuple
