import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Frontend.LocalExpressionLookupProperties
import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Frontend.LocalExpressionFuelBound
import Solcore.Frontend.LocalExpressionStoreProperties
import Solcore.Frontend.LocalExpressionRenaming
import Solcore.Frontend.TypeName

/-! Empty original tuples are constant Unit leaves. Independent constructors and
paths separate arbitrary raw callers from whole typing and retained continuations. -/
set_option autoImplicit false
namespace Tests.FrontendUnit
open Solcore Solcore.Frontend
private def unit (span tupleSpan : Syntax.SourceSpan) : Syntax.Expr := ⟨span, .tuple ⟨tupleSpan, []⟩⟩
private def pair (span tupleSpan : Syntax.SourceSpan) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .tuple ⟨tupleSpan, [left, right]⟩⟩
private theorem accepted (span tupleSpan : Syntax.SourceSpan) (table : LocalNameTable) (context : Resolved.Context) :
    elaborateLocalExpression? table context (unit span tupleSpan) = some (.unit, .unit) :=
  elaborateLocalExpression?_complete .unit .unit .unit
private theorem costed (span tupleSpan : Syntax.SourceSpan) (table : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table environment store (unit span tupleSpan) .unit store 1 := .unit
private theorem path (environment : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 1 ⟨.eval .unit environment, k, store⟩ ⟨.ret .unit, k, store⟩ := .cons .unit .refl

theorem independent_five_constructors_need_no_caller_or_span_validity
    (span tupleSpan : Syntax.SourceSpan) (table : LocalNameTable) (context : Resolved.Context)
    (environment : Resolved.Environment) (store : Core.Store) (name : String) :
    ResolvesLocalExpression table (unit span tupleSpan) .unit ∧
    LocalExpressionHasType table context (unit span tupleSpan) .unit ∧
    AvoidsLocalName name (unit span tupleSpan) ∧
    LocalExpressionEvaluates table environment store (unit span tupleSpan) .unit store ∧
    LocalExpressionEvaluatesWithCost table environment store (unit span tupleSpan) .unit store 1 ∧
    elaborateLocalExpression? table context (unit span tupleSpan) = some (.unit, .unit) :=
  ⟨.unit, .unit, .unit, .unit, .unit, accepted span tupleSpan table context⟩

theorem direct_unit_replays_arbitrary_stores_and_retains_the_final_store_constraint
    (span tupleSpan : Syntax.SourceSpan) (table : LocalNameTable) (environment : Resolved.Environment)
    (initial final replacement : Core.Store) :
    evaluateLocalExpressionWithCost? table environment (unit span tupleSpan) = some (.unit, 1) ∧
    LocalExpressionEvaluatesWithCost table environment replacement (unit span tupleSpan) .unit replacement 1 ∧
    (LocalExpressionEvaluatesWithCost table environment initial (unit span tupleSpan) .unit final 1 ↔ final = initial) ∧
    localExpressionFuelBound (unit span tupleSpan) = 1 := by
  have raw := costed span tupleSpan table environment initial
  have direct := evaluateLocalExpressionWithCost?_complete raw
  refine ⟨direct, raw.change_store replacement, ?_, ?_⟩
  · rw [localExpressionEvaluatesWithCost_iff_evaluate, direct]; simp
  · simp [unit, localExpressionFuelBound]

theorem unit_has_one_step_even_for_unaligned_untyped_environments
    (span tupleSpan : Syntax.SourceSpan) (table : LocalNameTable) (context : Resolved.Context)
    (environment : Resolved.Environment) (store : Core.Store) (k : List Core.Frame) (fuel : Nat) :
    elaborateLocalExpression? table context (unit span tupleSpan) = some (.unit, .unit) ∧
    Core.Steps 1 ⟨.eval .unit environment.values, k, store⟩ ⟨.ret .unit, k, store⟩ ∧
    (Core.runStateful fuel (.initial .unit environment.values store) = .done .unit store ↔ 1 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (.initial .unit environment.values store) = .outOfFuel checkpoint) ↔ fuel < 1) :=
  ⟨accepted span tupleSpan table context, path _ store k,
    (path environment.values store []).runStateful_done_iff,
    (path environment.values store []).runStateful_outOfFuel_iff⟩

theorem retained_continuations_are_endpoints_not_completed_programs
    (environment : Core.Environment) (store : Core.Store) :
    Core.Steps 1 ⟨.eval .unit environment, [.unaryApply .boolNot], store⟩
      ⟨.ret .unit, [.unaryApply .boolNot], store⟩ ∧
    Core.runStateful 1 ⟨.eval .unit environment, [.unaryApply .boolNot], store⟩ =
      .fault (.invalidUnaryOperand .boolNot .unit) ⟨.ret .unit, [.unaryApply .boolNot], store⟩ ∧
    Core.runStateful 0 ⟨.ret .unit, [.unaryApply .boolNot], store⟩ =
      .fault (.invalidUnaryOperand .boolNot .unit) ⟨.ret .unit, [.unaryApply .boolNot], store⟩ := ⟨path _ _ _, rfl, rfl⟩

private def source (s t : Syntax.SourceSpan) : Nat → Syntax.Expr
  | 0 => unit s t
  | n + 1 => pair s t (unit s t) (source s t n)
private def resolved : Nat → Resolved.Expr
  | 0 => .unit
  | n + 1 => .pair .unit (resolved n)
private def core : Nat → Core.Expr
  | 0 => .unit
  | n + 1 => .pair .unit (core n)
private def type : Nat → Core.Ty
  | 0 => .unit
  | n + 1 => .product .unit (type n)
private def value : Nat → Core.Value
  | 0 => .unit
  | n + 1 => .pair .unit (value n)
private theorem nestedStatic (s t : Syntax.SourceSpan) (table : LocalNameTable) (context : Resolved.Context) (n : Nat) :
    ResolvesLocalExpression table (source s t n) (resolved n) ∧
    Resolved.Lowers context.ids (resolved n) (core n) ∧ Resolved.HasType context (resolved n) (type n) := by
  induction n with
  | zero => exact ⟨.unit, .unit, .unit⟩
  | succ n ih => exact ⟨.pair .unit ih.1, .pair .unit ih.2.1, .pair .unit ih.2.2⟩
private theorem nestedCost (s t : Syntax.SourceSpan) (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (n : Nat) :
    LocalExpressionEvaluatesWithCost table environment store (source s t n) (value n) store (4 * n + 1) := by
  induction n with
  | zero => exact .unit
  | succ n ih =>
      have count : 4 * (n + 1) + 1 = 1 + (4 * n + 1) + 3 := by omega
      rw [count]; exact .pair .unit ih
private theorem nestedPath (environment : Core.Environment) (store : Core.Store) (n : Nat) :
    ∀ k, Core.Steps (4 * n + 1) ⟨.eval (core n) environment, k, store⟩ ⟨.ret (value n), k, store⟩ := by
  induction n with
  | zero => exact path environment store
  | succ n ih =>
      intro k
      have steps := Core.Steps.cons .enterPair (.cons .unit (.cons .enterPairRight
        ((ih (.pairApply .unit :: k)).trans (.cons .applyPair .refl))))
      simpa [core, value, Nat.mul_add, Nat.add_assoc] using steps

theorem independent_nested_paths_determine_exact_bounds_and_every_threshold
    (s t : Syntax.SourceSpan) (environment : Core.Environment) (store : Core.Store) (n fuel : Nat) (k : List Core.Frame) :
    Core.Steps (4 * n + 1) ⟨.eval (core n) environment, k, store⟩ ⟨.ret (value n), k, store⟩ ∧
    localExpressionFuelBound (source s t n) = 4 * n + 1 ∧
    (Core.runStateful fuel (.initial (core n) environment store) = .done (value n) store ↔ 4 * n + 1 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (.initial (core n) environment store) = .outOfFuel checkpoint) ↔ fuel < 4 * n + 1) := by
  refine ⟨nestedPath environment store n k, ?_, (nestedPath environment store n []).runStateful_done_iff,
    (nestedPath environment store n []).runStateful_outOfFuel_iff⟩
  induction n with
  | zero => simp [source, unit, localExpressionFuelBound]
  | succ n ih => simp [source, pair, unit, localExpressionFuelBound, ih, Nat.mul_add] <;> omega

theorem nested_pairs_are_not_erased_and_groups_do_not_add_cost
    (s t groupSpan : Syntax.SourceSpan) (table : LocalNameTable) (context : Resolved.Context)
    (environment : Resolved.Environment) (store : Core.Store) (n : Nat) :
    elaborateLocalExpression? table context ⟨groupSpan, .group (source s t n)⟩ = some (core n, type n) ∧
    evaluateLocalExpressionWithCost? table environment ⟨groupSpan, .group (source s t n)⟩ = some (value n, 4 * n + 1) ∧
    core 1 = .pair .unit .unit ∧ value 2 = .pair .unit (.pair .unit .unit) := by
  obtain ⟨resolution, lowered, typing⟩ := nestedStatic s t table context n
  exact ⟨elaborateLocalExpression?_complete (.group resolution) lowered typing,
    evaluateLocalExpressionWithCost?_complete (.group (nestedCost s t table environment store n)), rfl, rfl⟩

theorem generic_identity_and_lookup_laws_preserve_the_constant
    (s t : Syntax.SourceSpan) (leftTable rightTable : LocalNameTable)
    (leftEnvironment rightEnvironment : Resolved.Environment) (context : Resolved.Context)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (sameLookup : ∀ name, (leftTable.lookup? name).bind leftEnvironment.lookup? =
      (rightTable.lookup? name).bind rightEnvironment.lookup?) (store : Core.Store) :
    elaborateLocalExpression? (LocalNameTable.mapIds mapping leftTable) (Resolved.LocalScope.mapIds mapping context)
      (unit s t) = some (.unit, .unit) ∧
    LocalExpressionEvaluates (LocalNameTable.mapIds mapping leftTable) (Resolved.LocalScope.mapIds mapping leftEnvironment)
      store (unit s t) .unit store ∧
    evaluateLocalExpressionWithCost? rightTable rightEnvironment (unit s t) = some (.unit, 1) := by
  refine ⟨(elaborateLocalExpression?_mapIds mapping injective _ _ _).trans (accepted s t _ _),
    (localExpressionEvaluates_mapIds_iff mapping injective).mpr .unit, ?_⟩
  exact (evaluateLocalExpressionWithCost?_congr_lookup _ _ _ _ sameLookup _).symm.trans
    (evaluateLocalExpressionWithCost?_complete (costed s t leftTable leftEnvironment store))

theorem actual_typed_inputs_and_unused_fresh_values_preserve_all_fuel_observations
    (s t : Syntax.SourceSpan) (inputs : LocalInputs) (owner : Resolved.DeclarationId) (name : String)
    (newType : Core.Ty) (actual : Core.Value) (typedActual : Core.ValueHasType actual newType)
    (store : Core.Store) (fuel : Nat) :
    (inputs.run? fuel (unit s t) store = some (.unit, .done .unit store) ↔ 1 ≤ fuel) ∧
    ((inputs.bindFresh owner name newType actual typedActual).run? fuel (unit s t) store = some (.unit, .done .unit store) ↔
      inputs.run? fuel (unit s t) store = some (.unit, .done .unit store)) := by
  refine ⟨?_, (AvoidsLocalName.unit (name := name) (span := s) (tupleSpan := t)).bindFresh_run_done_at_fuel_iff
    inputs owner newType actual typedActual⟩
  rw [LocalInputs.run?_done_iff_evaluator]
  have direct := evaluateLocalExpressionWithCost?_complete (costed s t inputs.names inputs.environment store)
  constructor
  · rintro ⟨_, _, cost, evaluated, enough⟩; rw [direct] at evaluated; cases evaluated; exact enough
  · intro enough; exact ⟨.unit, rfl, 1, direct, enough⟩

private def span : Syntax.SourceSpan := ⟨⟨.main, "unit.sol"⟩, 231, 3⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"UnitConsumer", by decide⟩], by decide⟩⟩, 0⟩
private def id : Resolved.LocalId := ⟨owner, 17⟩
private def atom (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def binary (op : Syntax.BinaryOp) (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, op⟩ right⟩
private theorem guard (choice : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost [("c", id)] [(id, .bool choice)] store (atom "c") (.bool choice) store 1 := .identifier .head .head

theorem short_circuits_can_forward_unit_without_boolean_whole_typing
    (store : Core.Store) :
    evaluateLocalExpressionWithCost? [("c", id)] [(id, .bool true)] (binary .logicalAnd (atom "c") (unit span span)) = some (.unit, 4) ∧
    evaluateLocalExpressionWithCost? [("c", id)] [(id, .bool false)] (binary .logicalOr (atom "c") (unit span span)) = some (.unit, 4) ∧
    evaluateLocalExpressionWithCost? [("c", id)] [(id, .bool false)] (binary .logicalAnd (atom "c") (unit span span)) = some (.bool false, 4) ∧
    evaluateLocalExpressionWithCost? [("c", id)] [(id, .bool true)] (binary .logicalOr (atom "c") (unit span span)) = some (.bool true, 4) ∧
    elaborateLocalExpression? [("c", id)] [(id, .bool)] (binary .logicalAnd (atom "c") (unit span span)) = none ∧
    elaborateLocalExpression? [("c", id)] [(id, .bool)] (binary .logicalOr (atom "c") (unit span span)) = none :=
  ⟨evaluateLocalExpressionWithCost?_complete (.andTrue (guard true store) .unit),
    evaluateLocalExpressionWithCost?_complete (.orFalse (guard false store) .unit),
    evaluateLocalExpressionWithCost?_complete (.andFalse (guard false store)),
    evaluateLocalExpressionWithCost?_complete (.orTrue (guard true store)),
    by simp only [elaborateLocalExpression?, resolveLocalExpression?, binary, atom, unit]; rfl,
    by simp only [elaborateLocalExpression?, resolveLocalExpression?, binary, atom, unit]; rfl⟩

theorem genuine_unit_pair_checkpoints_retain_the_pair_and_resume
    (environment : Core.Environment) (store : Core.Store) (additional : Nat) :
    Core.runStateful 2 (.initial (core 1) environment store) = .outOfFuel ⟨.ret .unit, [.pairRight .unit environment], store⟩ ∧
    Core.runStateful 4 (.initial (core 1) environment store) = .outOfFuel ⟨.ret .unit, [.pairApply .unit], store⟩ ∧
    Core.Steps 1 ⟨.ret .unit, [.pairApply .unit], store⟩ (.final (.pair .unit .unit) store) ∧
    Core.runStateful additional ⟨.ret .unit, [.pairApply .unit], store⟩ =
      Core.runStateful (4 + additional) (.initial (core 1) environment store) ∧
    Core.runStateful 0 (.final .unit store) = .done .unit store := by
  have exhausted : Core.runStateful 4 (.initial (core 1) environment store) = .outOfFuel ⟨.ret .unit, [.pairApply .unit], store⟩ := rfl
  exact ⟨rfl, exhausted, .cons .applyPair .refl, Core.runStateful_resume exhausted additional, rfl⟩

private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
theorem unit_spelling_is_not_reserved_and_type_aliases_remain_caller_supplied
    (actual : Core.Value) (callerType : Core.Ty) (types : TypeNameTable) :
    evaluateLocalExpressionWithCost? [("Unit", id)] [(id, actual)] (atom "Unit") = some (actual, 1) ∧
    evaluateLocalExpressionWithCost? [] [] (atom "Unit") = none ∧
    interpretTypeName? [(["Unit"], callerType)] (named "Unit") = some callerType ∧
    interpretTypeName? [(["Alias"], .unit)] (named "Alias") = some .unit ∧
    interpretTypeName? types ⟨span, .tuple []⟩ = none :=
  ⟨evaluateLocalExpressionWithCost?_complete (LocalExpressionEvaluatesWithCost.identifier (store := []) .head .head),
    by simp [evaluateLocalExpressionWithCost?, atom, LocalNameTable.lookup?], rfl, rfl, rfl⟩

theorem a_unit_left_child_does_not_hide_a_missing_right_or_wrong_result_type
    (table : LocalNameTable) (context : Resolved.Context) (store : Core.Store) :
    evaluateLocalExpressionWithCost? [] [] (pair span span (unit span span) (atom "missing")) = none ∧
    (¬ ∃ result cost, LocalExpressionEvaluatesWithCost [] [] store
      (pair span span (unit span span) (atom "missing")) result store cost) ∧
    Core.HasType context.values (.pair .unit .unit) (.product .unit .unit) ∧
    elaborateLocalExpression? table context (unit span span) ≠ some (.pair .unit .unit, .product .unit .unit) := by
  have rejected : evaluateLocalExpressionWithCost? [] [] (pair span span (unit span span) (atom "missing")) = none := by
    simp [evaluateLocalExpressionWithCost?, pair, unit, atom, LocalNameTable.lookup?]
  refine ⟨rejected, (evaluateLocalExpressionWithCost?_eq_none_iff store).mp rejected, .pair .unit .unit, ?_⟩
  rw [accepted]; intro wrong; cases wrong

theorem a_same_typed_variable_is_not_the_core_of_an_empty_tuple
    (s t : Syntax.SourceSpan) (table : LocalNameTable) (context : Resolved.Context)
    (inputId : Resolved.LocalId) (definitions : Core.DataEnvironment) (nominal : Core.DataTypeId) :
    Core.HasType (.unit :: context.values) (.var 0) .unit definitions ∧
    elaborateLocalExpression? table ((inputId, .unit) :: context) (unit s t) ≠ some (.var 0, .unit) ∧
    elaborateLocalExpression? table ((inputId, .namedData nominal) :: context) (unit s t) = some (.unit, .unit) ∧
    (¬ ∃ actual, Core.ValueHasType actual (.namedData nominal)) := by
  refine ⟨.var rfl, ?_, accepted s t _ _, ?_⟩
  · rw [accepted]; intro wrong; cases wrong
  · rintro ⟨actual, typedActual⟩
    cases typedActual with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

end Tests.FrontendUnit
