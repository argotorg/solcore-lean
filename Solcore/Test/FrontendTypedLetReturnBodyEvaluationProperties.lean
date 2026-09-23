import Solcore.Frontend.TypedLetReturnBody

/-! Independent let paths use actual values and count even unused initializers.
Static typing, positional alignment and pending-continuation safety are separate. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetReturnBodyEvaluation

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetEvaluation", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-evaluation.sol"⟩, 141, 5⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def binding (name : String) (value : Syntax.Expr) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some value)⟩
private def returned (value : Syntax.Expr) : Syntax.Statement := ⟨span, .returnStmt (some value)⟩
private def statements : List String → String → List Syntax.Statement
  | [], previous => [returned (ref previous)]
  | name :: rest, previous => binding name (ref previous) :: statements rest name
private def chain (names : List String) (previous : String) : Syntax.Block := ⟨span, statements names previous⟩
private def inputs (type : Core.Ty) : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "seed" type
private def table : LocalNameTable := [("seed", id 0)]
private def environment (value : Core.Value) : Resolved.Environment := [(id 0, value)]
private def one := chain ["x"] "seed"
private def oneCore : Core.Expr := .letE (.var 0) (.var 0)

private theorem chainRaw (names : List String) (previous : String) (namesTable : LocalNameTable)
    (values : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluates namesTable values store (ref previous) value store) :
    TypedLetReturnBodyEvaluates owner namesTable values store (chain names previous) value store := by
  induction names generalizing previous namesTable values with
  | nil => exact .terminal (.single (.expression head))
  | cons name rest ih => exact .binding head (ih name _ _ (.identifier .head .head))
private theorem chainCost (names : List String) (previous : String) (namesTable : LocalNameTable)
    (values : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost namesTable values store (ref previous) value store 1) :
    TypedLetReturnBodyEvaluatesWithCost owner namesTable values store (chain names previous) value store (3 * names.length + 1) := by
  induction names generalizing previous namesTable values with
  | nil => exact .terminal (.single (.expression head))
  | cons name rest ih =>
      have arithmetic : 1 + (3 * rest.length + 1) + 2 = 3 * (name :: rest).length + 1 := by simp; omega
      simpa only [arithmetic, chain, statements, binding] using
        TypedLetReturnBodyEvaluatesWithCost.binding (name := ⟨span, name⟩) (annotation := annotation)
          head (ih name _ _ (.identifier .head .head))
private theorem counted (value : Core.Value) (store : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store one value store 4 :=
  chainCost ["x"] "seed" table (environment value) value store (.identifier .head .head)
private theorem elaborated (type : Core.Ty) :
    TypedLetReturnBodyElaborates (types type) owner (inputs type) one oneCore type :=
  .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
    (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head))))

theorem independent_static_provenance_requires_neither_a_value_nor_a_store (type : Core.Ty) :
    TypedLetReturnBodyElaborates (types type) owner (inputs type) one oneCore type ∧
    elaborateTypedLetReturnBody? (types type) owner (inputs type) one = some (oneCore, type) :=
  ⟨elaborated type, (elaborated type).complete⟩

theorem arbitrary_lists_need_no_name_freshness_or_runtime_type_to_have_independent_raw_cost
    (names : List String) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnBodyEvaluates owner table (environment value) store (chain names "seed") value store ∧
    TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store (chain names "seed") value store (3 * names.length + 1) :=
  ⟨chainRaw names "seed" table (environment value) value store (.identifier .head .head),
    chainCost names "seed" table (environment value) value store (.identifier .head .head)⟩

theorem independent_paths_determine_exact_positive_cost_and_keep_each_store
    (names : List String) (value rawValue countedValue : Core.Value) (store rawStore countedStore : Core.Store) (cost : Nat)
    (raw : TypedLetReturnBodyEvaluates owner table (environment value) store (chain names "seed") rawValue rawStore)
    (costed : TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store (chain names "seed") countedValue countedStore cost) :
    rawValue = value ∧ rawStore = store ∧ countedValue = value ∧ countedStore = store ∧ cost = 3 * names.length + 1 ∧ 0 < cost ∧
    (∃ witness, TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store (chain names "seed") rawValue rawStore witness) ∧
    (TypedLetReturnBodyEvaluates owner table (environment value) store (chain names "seed") value store ↔
      ∃ witness, TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store (chain names "seed") value store witness) := by
  have original := chainCost names "seed" table (environment value) value store (.identifier .head .head)
  have same := costed.deterministic original
  exact ⟨(raw.deterministic original.erase).1, raw.store_eq, same.1, costed.store_eq, same.2.2, costed.cost_pos,
    raw.exists_cost, typedLetReturnBodyEvaluates_iff_exists_cost⟩

theorem arbitrary_static_types_do_not_supply_values_but_actual_typed_values_supply_existence
    (type : Core.Ty) (actual result : Core.Value) (typed : Core.ValueHasType actual type) (store finalStore : Core.Store)
    (raw : TypedLetReturnBodyEvaluates owner table (environment actual) store one result finalStore) :
    elaborateTypedLetReturnBody? (types type) owner (inputs type) one = some (oneCore, type) ∧
    (inputs type).names.map Prod.snd = (inputs type).ids ∧
    (∃ value, TypedLetReturnBodyEvaluates owner table (environment actual) store one value store ∧ Core.ValueHasType value type) ∧
    Core.ValueHasType result type ∧ finalStore = store := by
  have sourceType := (elaborated type).hasType
  have actualTypes : Core.EnvironmentHasTypes (environment actual).values (inputs type).context.values := .cons typed .nil
  exact ⟨(elaborated type).complete, (inputs type).names_ids, sourceType.evaluates rfl actualTypes store,
    raw.preserves_type sourceType rfl actualTypes⟩

theorem exact_checked_paths_keep_arbitrary_continuations_without_executing_them
    (type : Core.Ty) (value : Core.Value) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 4 ⟨.eval oneCore [value], continuation, store⟩ ⟨.ret value, continuation, store⟩ ∧
    Core.Steps 4 (Core.State.initial oneCore [value] store) (Core.State.final value store) :=
  ⟨(counted value store).checked_toStepsWithContinuation (elaborated type).complete rfl continuation,
    (counted value store).checked_toSteps (elaborated type).complete rfl⟩

theorem aligned_untyped_payloads_preserve_raw_core_meaning_but_not_the_declared_value_type
    (store finalStore : Core.Store) (value : Core.Value) :
    elaborateTypedLetReturnBody? (types .word) owner (inputs .word) one = some (oneCore, .word) ∧
    (TypedLetReturnBodyEvaluates owner table (environment (.bool true)) store one value finalStore ↔
      Core.Evaluates [.bool true] store oneCore value finalStore) ∧
    Core.Evaluates [.bool true] store oneCore (.bool true) store ∧ ¬ Core.ValueHasType (.bool true) .word :=
  ⟨(elaborated .word).complete, elaborateTypedLetReturnBody?_evaluates_iff (elaborated .word).complete rfl,
    (elaborateTypedLetReturnBody?_evaluates_iff (elaborated .word).complete rfl).mp (counted (.bool true) store).erase,
    by intro impossible; cases impossible⟩

theorem existing_typed_cells_and_captured_closures_are_neither_allocated_nor_invoked
    (location : Core.Location) (word : Core.Word) (store : Core.Store) (continuation : List Core.Frame) :
    Core.ValueHasType (.cellRef .word location) (.cell .word) ∧
    Core.ValueHasType (.closure .bool .word (.var 1) [.word word]) (.function .bool .word) ∧
    Core.Steps 4 ⟨.eval oneCore [.cellRef .word location], continuation, store⟩ ⟨.ret (.cellRef .word location), continuation, store⟩ ∧
    Core.Steps 4 ⟨.eval oneCore [.closure .bool .word (.var 1) [.word word]], continuation, store⟩
      ⟨.ret (.closure .bool .word (.var 1) [.word word]), continuation, store⟩ :=
  ⟨.cellRef, .closure (.cons .word .nil) (.var rfl),
    (counted (.cellRef .word location) store).checked_toStepsWithContinuation (elaborated (.cell .word)).complete rfl continuation,
    (counted (.closure .bool .word (.var 1) [.word word]) store).checked_toStepsWithContinuation
      (elaborated (.function .bool .word)).complete rfl continuation⟩

theorem a_safe_pending_frame_exhausts_but_an_incompatible_endpoint_faults_at_zero_fuel (store : Core.Store) :
    Core.runStateful 4 ⟨.eval oneCore [.bool true], [.unaryApply .boolNot], store⟩ =
      .outOfFuel ⟨.ret (.bool true), [.unaryApply .boolNot], store⟩ ∧
    Core.runStateful 0 ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot (.bool true)) ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ ∧
    Core.runStateful 4 ⟨.eval oneCore [.bool true], [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot (.bool true)) ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ := ⟨rfl, rfl, rfl⟩

private def subtract (left right : String) : Syntax.Expr := ⟨span, .binary (ref left) ⟨span, .subtract⟩ (ref right)⟩
private def pairInputs : LocalTypeInputs := ⟨[⟨"left", id 0, .word⟩, ⟨"right", id 1, .word⟩], by decide⟩
private def pairEnv (left right : Core.Word) : Resolved.Environment := [(id 0, .word left), (id 1, .word right)]
private def unused : Syntax.Block := ⟨span, [binding "unused" (subtract "left" "right"), returned (subtract "right" "left")]⟩
private def unusedCore : Core.Expr := .letE (.binary .wordSub (.var 0) (.var 1)) (.binary .wordSub (.var 2) (.var 1))
private theorem unusedElab : TypedLetReturnBodyElaborates (types .word) owner pairInputs unused unusedCore .word :=
  .binding (.named .head) (by decide)
    (.subtract (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.binary (.var .head) (.var (.tail (by decide) .head)))
    (.binary (.var .head) (.var (.tail (by decide) .head)))
    (.terminal (.single (.expression
      (.subtract (.identifier (.tail (by decide) (.tail (by decide) .head))) (.identifier (.tail (by decide) .head)))
      (.binary (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) .head)))
      (.binary (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) .head))))))
private theorem unusedCost (left right : Core.Word) (store : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner pairInputs.names (pairEnv left right) store unused (.word (right.sub left)) store 12 := by
  have lhs : LocalExpressionEvaluatesWithCost pairInputs.names (pairEnv left right) store (ref "left") (.word left) store 1 := .identifier .head .head
  have rhs : LocalExpressionEvaluatesWithCost pairInputs.names (pairEnv left right) store (ref "right") (.word right) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have initial : LocalExpressionEvaluatesWithCost pairInputs.names (pairEnv left right) store
      (subtract "left" "right") (.word (left.sub right)) store 5 := .subtract lhs rhs
  apply TypedLetReturnBodyEvaluatesWithCost.binding (owner := owner) (name := ⟨span, "unused"⟩)
    (annotation := annotation) (tailCost := 5) initial
  change TypedLetReturnBodyEvaluatesWithCost owner (("unused", id 2) :: pairInputs.names)
    ((id 2, .word (left.sub right)) :: pairEnv left right) store ⟨span, [returned (subtract "right" "left")]⟩ (.word (right.sub left)) store 5
  have nextRight : LocalExpressionEvaluatesWithCost (("unused", id 2) :: pairInputs.names)
      ((id 2, .word (left.sub right)) :: pairEnv left right) store (ref "right") (.word right) store 1 :=
    .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
  have nextLeft : LocalExpressionEvaluatesWithCost (("unused", id 2) :: pairInputs.names)
      ((id 2, .word (left.sub right)) :: pairEnv left right) store (ref "left") (.word left) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  exact .terminal (.single (.expression (.subtract nextRight nextLeft)))

theorem unused_noncommutative_initializers_are_evaluated_in_old_scope_and_still_cost_five
    (left right : Core.Word) (store : Core.Store) (continuation : List Core.Frame) :
    elaborateTypedLetReturnBody? (types .word) owner pairInputs unused = some (unusedCore, .word) ∧
    TypedLetReturnBodyEvaluatesWithCost owner pairInputs.names (pairEnv left right) store unused (.word (right.sub left)) store 12 ∧
    Core.Steps 12 ⟨.eval unusedCore [.word left, .word right], continuation, store⟩
      ⟨.ret (.word (right.sub left)), continuation, store⟩ ∧
    ¬ TypedLetReturnBodyEvaluatesWithCost owner pairInputs.names (pairEnv left right) store unused (.word (right.sub left)) store 7 := by
  refine ⟨unusedElab.complete, unusedCost left right store,
    (unusedCost left right store).checked_toStepsWithContinuation unusedElab.complete rfl continuation, ?_⟩
  intro skipped
  have impossible := (skipped.deterministic (unusedCost left right store)).2.2
  cases impossible

private def badConditional : Syntax.Expr := ⟨span, .conditional (ref "seed") span (ref "seed") span (ref "missing")⟩
private def bad (inInitializer : Bool) : Syntax.Block := if inInitializer then
  ⟨span, [binding "x" badConditional, returned (ref "seed")]⟩ else
  ⟨span, [binding "x" (ref "seed"), ⟨span, .ifThen (ref "seed") ⟨span, [returned (ref "seed")]⟩
    (some ⟨span, [returned (ref "missing")]⟩)⟩]⟩
private theorem badCost (inInitializer : Bool) (store : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment (.bool true)) store (bad inInitializer) (.bool true) store 7 := by
  have seed : LocalExpressionEvaluatesWithCost table (environment (.bool true)) store (ref "seed") (.bool true) store 1 := .identifier .head .head
  have tailSeed : LocalExpressionEvaluatesWithCost (("x", id 1) :: table) ((id 1, .bool true) :: environment (.bool true))
      store (ref "seed") (.bool true) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  cases inInitializer
  · apply TypedLetReturnBodyEvaluatesWithCost.binding (owner := owner) (name := ⟨span, "x"⟩)
      (annotation := annotation) (tailCost := 4) seed
    exact .terminal (.ifTrue tailSeed (.single (.expression tailSeed)))
  · have initializer : LocalExpressionEvaluatesWithCost table (environment (.bool true)) store badConditional (.bool true) store 4 := .ifTrue seed seed
    apply TypedLetReturnBodyEvaluatesWithCost.binding (owner := owner) (name := ⟨span, "x"⟩)
      (annotation := annotation) (tailCost := 1) initializer
    exact .terminal (.single (.expression tailSeed))

theorem skipped_bad_initializer_subexpressions_and_terminal_arms_still_fail_whole_checking
    (inInitializer : Bool) (store : Core.Store) :
    TypedLetReturnBodyEvaluates owner table (environment (.bool true)) store (bad inInitializer) (.bool true) store ∧
    TypedLetReturnBodyEvaluatesWithCost owner table (environment (.bool true)) store (bad inInitializer) (.bool true) store 7 ∧
    elaborateTypedLetReturnBody? (types .bool) owner (inputs .bool) (bad inInitializer) = none := by
  refine ⟨(badCost inInitializer store).erase, badCost inInitializer store, ?_⟩
  cases inInitializer <;> simp [bad, badConditional, binding, returned, elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?,
    elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?, ref, inputs, types, annotation,
    LocalTypeInputs.bindFresh, LocalTypeInputs.names, LocalTypeInputs.empty, LocalNameTable.lookup?]

theorem an_evaluated_missing_initializer_cannot_be_skipped_even_when_its_name_is_unused
    (store finalStore : Core.Store) (value : Core.Value) :
    ¬ TypedLetReturnBodyEvaluates owner table (environment (.bool true)) store
      ⟨span, [binding "x" (ref "missing"), returned (ref "seed")]⟩ value finalStore := by
  intro raw
  cases raw with
  | terminal tree => cases tree with | single leaf => cases leaf
  | binding initializer _ =>
      cases initializer with
      | identifier named _ =>
          have found := LocalNameTable.lookup?_iff.mpr named
          simp [table, LocalNameTable.lookup?] at found

theorem typed_values_cannot_replace_the_missing_identity_alignment (store : Core.Store) :
    let initial : LocalTypeInputs := ⟨[⟨"seed", id 0, .bool⟩, ⟨"other", id 9, .bool⟩], by decide⟩
    let swapped : Resolved.Environment := [(id 9, .bool false), (id 0, .bool true)]
    elaborateTypedLetReturnBody? (types .bool) owner initial one = some (oneCore, .bool) ∧
    swapped.ids ≠ initial.context.ids ∧ Core.EnvironmentHasTypes swapped.values initial.context.values ∧
    TypedLetReturnBodyEvaluates owner initial.names swapped store one (.bool true) store ∧
    Core.Evaluates swapped.values store oneCore (.bool false) store ∧ ¬ Core.Evaluates swapped.values store oneCore (.bool true) store := by
  intro initial swapped
  have exact : TypedLetReturnBodyElaborates (types .bool) owner initial one oneCore .bool :=
    .binding (.named .head) (by decide) (.identifier .head) (.var .head) (.var .head)
      (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head))))
  have wrong : Core.Evaluates swapped.values store oneCore (.bool false) store := .letE (.var rfl) (.var rfl)
  refine ⟨exact.complete, by decide, .cons .bool (.cons .bool .nil),
    chainRaw ["x"] "seed" initial.names swapped (.bool true) store (.identifier .head (.tail (by decide) .head)), wrong, ?_⟩
  intro impossible
  cases (Core.evaluation_deterministic impossible wrong).1

theorem original_raw_and_counted_tree_paths_embed_without_checking_or_extra_cost
    (names : LocalNameTable) (values : Resolved.Environment) (store finalStore : Core.Store) (body : Syntax.Block)
    (value : Core.Value) (cost : Nat) (raw : TerminalReturnTreeEvaluates names values store body value finalStore)
    (counted : TerminalReturnTreeEvaluatesWithCost names values store body value finalStore cost) :
    TypedLetReturnBodyEvaluates owner names values store body value finalStore ∧
    TypedLetReturnBodyEvaluatesWithCost owner names values store body value finalStore cost :=
  ⟨raw.typedLetReturnBody owner, counted.typedLetReturnBody owner⟩

end Tests.FrontendTypedLetReturnBodyEvaluation
