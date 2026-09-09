import Solcore.Frontend.TypedLetReturnTreeEvaluatorExecutionProperties
import Solcore.Frontend.TypedLetReturnTreeResumptionProperties
import Solcore.Frontend.TypedLetReturnTreeProperties

/-! Independent original bodies fix raw values, lexical scopes and costs before
direct evaluation. Whole checking, aligned identities and actual typing remain
separate premises; retained continuations are not executed by path endpoints. -/
set_option autoImplicit false
namespace Tests.FrontendTypedLetReturnTreeEvaluator
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"DirectTree", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "direct-tree.sol"⟩, 224, 7⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation (name : String := "Payload") : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def returned (value : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some value)⟩]⟩
private def binding (name : String) (value : Syntax.Expr) (tail : Syntax.Block) (typeName : String := "Payload") : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some (annotation typeName)) (some value)⟩ :: tail.value⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def zero : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span, .binary zero ⟨span, .equal⟩ zero⟩
private def guardCore : Core.Expr := .binary .wordEq (.word .zero) (.word .zero)
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree : List String → String → Syntax.Block
  | [], previous => returned (ref previous)
  | name :: rest, previous => binding name (ref previous) (branch guard (tree rest name) (returned (ref name)))
private def core : Nat → Core.Expr
  | 0 => .var 0
  | depth + 1 => .letE (.var 0) (.ifE guardCore (core depth) (.var 0))
private def initial (type : Core.Ty) : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "seed" type
private def table : LocalNameTable := [("seed", id 0)]
private def env (value : Core.Value) : Resolved.Environment := [(id 0, value)]
private theorem counted (names : List String) (previous : String) (namesTable : LocalNameTable)
    (values : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost namesTable values store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost owner namesTable values store (tree names previous) value store (10 * names.length + 1) := by
  induction names generalizing previous namesTable values with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
    have count : 1 + (5 + (10 * rest.length + 1) + 2) + 2 = 10 * (name :: rest).length + 1 := by simp; omega
    simpa only [count, tree, binding, branch, guard, zero] using TypedLetReturnTreeEvaluatesWithCost.binding
      (name := ⟨span, name⟩) (annotation := annotation) head
      (.ifTrue (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)) (ih name _ _ (.identifier .head .head)))
private theorem seedCost (names : List String) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (tree names "seed") value store (10 * names.length + 1) :=
  counted names "seed" table (env value) value store (.identifier .head .head)
private theorem output (names : List String) (value : Core.Value) :
    evaluateTypedLetReturnTreeWithCost? owner table (env value) (tree names "seed") = some (value, 10 * names.length + 1) :=
  evaluateTypedLetReturnTreeWithCost?_complete (seedCost names value [])
private theorem elaborated (names : List String) (previous : String) (type : Core.Ty)
    (inputs : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ inputs.names.map Prod.fst)
    (resolution : ResolvesLocalExpression inputs.names (ref previous) resolved)
    (lowered : Resolved.Lowers inputs.ids resolved (.var 0)) (typed : Resolved.HasType inputs.context resolved type) :
    TypedLetReturnTreeElaborates (types type) owner inputs (tree names previous) (core names.length) type := by
  induction names generalizing previous inputs resolved with
  | nil =>
    simp only [tree, List.length_nil, core]
    exact .single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typed)
  | cons name rest ih =>
    have parts := List.nodup_cons.mp distinct
    simp only [tree, List.length_cons, core, binding]
    apply TypedLetReturnTreeElaborates.binding (name := ⟨span, name⟩) (annotation := annotation)
      (.named .head) (fresh name (by simp)) resolution lowered typed
    apply TypedLetReturnTreeElaborates.conditional (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning))
      (.binary .word .word) (.binary .word .word)
    · apply ih name (inputs.bindFresh owner name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head
    · exact .single (.expression (.identifier .head) (.var .head) (.var .head))
private theorem accepted (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    elaborateTypedLetReturnTree? (types type) owner (initial type) (tree names "seed") = some (core names.length, type) := by
  apply TypedLetReturnTreeElaborates.complete
  apply elaborated names "seed" type (initial type) _ distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head

theorem arbitrary_raw_lists_execute_at_their_independently_counted_cost
    (names : List String) (value : Core.Value) (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? owner table (env value) (tree names "seed") = some (value, 10 * names.length + 1) ∧
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (tree names "seed") value store (10 * names.length + 1) ∧
    (evaluateTypedLetReturnTreeWithCost? owner table (env value) (tree names "seed")).map Prod.fst = some value :=
  ⟨output names value, evaluateTypedLetReturnTreeWithCost?_sound (output names value) store,
    (evaluateTypedLetReturnTreeWithCost?_value_iff store).mpr (seedCost names value store).erase⟩

theorem the_store_free_result_does_not_erase_final_store_equality
    (names : List String) (value : Core.Value) (store final : Core.Store) :
    (TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (tree names "seed") value final (10 * names.length + 1) ↔ final = store) ∧
    (∃ cost, evaluateTypedLetReturnTreeWithCost? owner table (env value) (tree names "seed") = some (value, cost)) ∧
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (tree names "seed") value store (10 * names.length + 1) := by
  refine ⟨?_, (evaluateTypedLetReturnTreeWithCost?_exists_cost_iff store).mpr (seedCost names value store).erase,
    (evaluateTypedLetReturnTreeWithCost?_iff store).mp (output names value)⟩
  rw [typedLetReturnTreeEvaluatesWithCost_iff_evaluate, output]; simp

theorem checked_arbitrary_depth_keeps_exact_core_all_fuel_and_unconsumed_frames
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (value : Core.Value) (store final : Core.Store) (fuel : Nat) (continuation : List Core.Frame) :
    Core.Steps (10 * names.length + 1) ⟨.eval (core names.length) [value], continuation, store⟩ ⟨.ret value, continuation, store⟩ ∧
    (Core.runStateful fuel (Core.State.initial (core names.length) [value] store) = .done value store ↔ 10 * names.length + 1 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (Core.State.initial (core names.length) [value] store) = .outOfFuel checkpoint) ↔ fuel < 10 * names.length + 1) ∧
    (Core.runStateful fuel (Core.State.initial (core names.length) [value] store) = .done value final ↔ final = store ∧ 10 * names.length + 1 ≤ fuel) := by
  have checked := accepted names type distinct fresh
  refine ⟨evaluateTypedLetReturnTreeWithCost?_checked_toStepsWithContinuation (output names value) checked rfl continuation,
    evaluateTypedLetReturnTreeWithCost?_checked_runStateful_done_iff (output names value) checked rfl,
    evaluateTypedLetReturnTreeWithCost?_checked_runStateful_outOfFuel_iff (output names value) checked rfl, ?_⟩
  have reflected := elaborateTypedLetReturnTree?_run_done_iff_evaluator (environment := env value)
    (initialStore := store) (finalStore := final) (value := value) (fuel := fuel) checked rfl
  rw [show (initial type).names = table from rfl, output] at reflected
  simpa [env, Resolved.LocalScope.values] using reflected

private def actualInputs (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "seed" type value typed
theorem typed_actual_inputs_supply_results_but_nominal_static_types_supply_no_values
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) (store : Core.Store) (nominal : Core.DataTypeId) :
    (∃ result cost, evaluateTypedLetReturnTreeWithCost? owner table (env value) (tree ["x"] "seed") = some (result, cost) ∧ Core.ValueHasType result type) ∧
    (∀ fuel, ((actualInputs type value typed).runTypedLetReturnTree? (types type) owner fuel (tree ["x"] "seed") store = some (type, .done value store) ↔ 11 ≤ fuel) ∧
      ((∃ checkpoint, (actualInputs type value typed).runTypedLetReturnTree? (types type) owner fuel (tree ["x"] "seed") store = some (type, .outOfFuel checkpoint)) ↔ fuel < 11)) ∧
    elaborateTypedLetReturnTree? (types (.namedData nominal)) owner (initial (.namedData nominal)) (tree ["x"] "seed") = some (core 1, .namedData nominal) ∧
    ¬ ∃ result, Core.ValueHasType result (.namedData nominal) := by
  have checked := accepted ["x"] type (by decide) (by decide)
  have typing : TypedLetReturnTreeHasType (types type) owner (actualInputs type value typed).toTypeInputs (tree ["x"] "seed") type :=
    elaborateTypedLetReturnTree?_sound checked
  obtain ⟨result, cost, evaluated, _, thresholds⟩ := LocalInputs.typedLetReturnTree_evaluator_execution typing store
  have same := (output ["x"] value).symm.trans evaluated
  cases Option.some.inj same
  refine ⟨elaborateTypedLetReturnTree?_typed_evaluator_exists checked rfl (.cons typed .nil), thresholds,
    accepted ["x"] _ (by decide) (by decide), ?_⟩
  rintro ⟨result, impossible⟩
  cases impossible with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def pairInputs : LocalTypeInputs := ⟨[⟨"c", id 0, .bool⟩, ⟨"x", id 3, .word⟩, ⟨"y", id 8, .word⟩], by decide⟩
private def pairEnv (choice : Bool) (left right : Core.Word) : Resolved.Environment := [(id 0, .bool choice), (id 3, .word left), (id 8, .word right)]
private def sub (left right : String) : Syntax.Expr := ⟨span, .binary (ref left) ⟨span, .subtract⟩ (ref right)⟩
private def bitNot (value : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .bitNot⟩ value⟩
private def siblings := branch (ref "c") (binding "z" (sub "x" "y") (returned (ref "z")))
  (binding "z" (bitNot (sub "y" "x")) (returned (ref "x")))
private def siblingsCore : Core.Expr := .ifE (.var 0) (.letE (.binary .wordSub (.var 1) (.var 2)) (.var 0))
  (.letE (.unary .wordNot (.binary .wordSub (.var 2) (.var 1))) (.var 2))
private theorem siblingsElab : TypedLetReturnTreeElaborates (types .word) owner pairInputs siblings siblingsCore .word :=
  .conditional (.identifier .head) (.var .head) (.var .head)
    (.binding (.named .head) (by decide)
      (.subtract (.identifier (.tail (by decide) .head)) (.identifier (.tail (by decide) (.tail (by decide) .head))))
      (.binary (.var (.tail (by decide) .head)) (.var (.tail (by decide) (.tail (by decide) .head))))
      (.binary (.var (.tail (by decide) .head)) (.var (.tail (by decide) (.tail (by decide) .head))))
      (.single (.expression (.identifier .head) (.var .head) (.var .head))))
    (.binding (.named .head) (by decide)
      (.bitNot (.subtract (.identifier (.tail (by decide) (.tail (by decide) .head))) (.identifier (.tail (by decide) .head))))
      (.unary (.binary (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) .head))))
      (.unary (.binary (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) .head))))
      (.single (.expression (.identifier (.tail (by decide) (.tail (by decide) .head)))
        (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) (.tail (by decide) .head))))))
private theorem siblingsCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner pairInputs.names (pairEnv choice left right) store siblings
      (.word (if choice then left.sub right else left)) store (if choice then 11 else 13) := by
  have c : LocalExpressionEvaluatesWithCost pairInputs.names (pairEnv choice left right) store (ref "c") (.bool choice) store 1 := .identifier .head .head
  have x : LocalExpressionEvaluatesWithCost pairInputs.names (pairEnv choice left right) store (ref "x") (.word left) store 1 := .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have y : LocalExpressionEvaluatesWithCost pairInputs.names (pairEnv choice left right) store (ref "y") (.word right) store 1 := .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
  cases choice
  · exact .ifFalse c (.binding (name := ⟨span, "z"⟩) (annotation := annotation) (initializerCost := 7) (tailCost := 1)
      (.bitNot (.subtract y x)) (.single (.expression (.identifier (name := ⟨span, "x"⟩) (id := id 3)
      (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))))))
  · exact .ifTrue c (.binding (.subtract x y) (.single (.expression (.identifier .head .head))))

theorem scope_local_siblings_keep_noncommutative_and_unused_initializers
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    Resolved.freshLocalId owner pairInputs.ids = id 9 ∧
    elaborateTypedLetReturnTree? (types .word) owner pairInputs siblings = some (siblingsCore, .word) ∧
    evaluateTypedLetReturnTreeWithCost? owner pairInputs.names (pairEnv choice left right) siblings =
      some (.word (if choice then left.sub right else left), if choice then 11 else 13) ∧
    ∀ fuel, (Core.runStateful fuel (Core.State.initial siblingsCore [.bool choice, .word left, .word right] store) =
      .done (.word (if choice then left.sub right else left)) store ↔ (if choice then 11 else 13) ≤ fuel) := by
  have evaluated := evaluateTypedLetReturnTreeWithCost?_complete (siblingsCost choice left right store)
  exact ⟨rfl, siblingsElab.complete, evaluated, fun _ =>
    evaluateTypedLetReturnTreeWithCost?_checked_runStateful_done_iff evaluated siblingsElab.complete rfl⟩

private def pending (value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody (.ifE guardCore (.var 0) (.var 0)) [value]], store⟩
theorem actual_initializer_checkpoints_keep_the_obtained_value_and_resume_at_any_fuel
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) (store : Core.Store) (additional : Nat) :
    (actualInputs type value typed).runTypedLetReturnTree? (types type) owner 2 (tree ["x"] "seed") store =
      some (type, .outOfFuel (pending value store)) ∧
    Core.Steps 9 (pending value store) (Core.State.final value store) ∧
    (actualInputs type value typed).runTypedLetReturnTree? (types type) owner (2 + additional) (tree ["x"] "seed") store =
      some (type, Core.runStateful additional (pending value store)) := by
  have checked := accepted ["x"] type (by decide) (by decide)
  have exhausted : Core.runStateful 2 (Core.State.initial (core 1) [value] store) = .outOfFuel (pending value store) := rfl
  have actualOut : (actualInputs type value typed).runTypedLetReturnTree? (types type) owner 2 (tree ["x"] "seed") store =
      some (type, .outOfFuel (pending value store)) := by
    simp only [LocalInputs.runTypedLetReturnTree?, LocalInputs.checkTypedLetReturnTree?, show (actualInputs type value typed).toTypeInputs = initial type from rfl, checked]
    exact congrArg (some ∘ Prod.mk type) exhausted
  exact ⟨actualOut, ((seedCost ["x"] value store).checked_residual_of_outOfFuel checked rfl exhausted).2,
    LocalInputs.runTypedLetReturnTree?_resume actualOut additional⟩

theorem bundled_done_and_exhaustion_need_whole_typing_in_addition_to_raw_success
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) (store : Core.Store) :
    (actualInputs type value typed).runTypedLetReturnTree? (types type) owner 11 (tree ["x"] "seed") store = some (type, .done value store) ∧
    ∃ checkpoint, (actualInputs type value typed).runTypedLetReturnTree? (types type) owner 10 (tree ["x"] "seed") store = some (type, .outOfFuel checkpoint) := by
  have typing : TypedLetReturnTreeHasType (types type) owner (actualInputs type value typed).toTypeInputs (tree ["x"] "seed") type :=
    elaborateTypedLetReturnTree?_sound (accepted ["x"] type (by decide) (by decide))
  exact ⟨LocalInputs.runTypedLetReturnTree?_done_iff_evaluator.mpr ⟨typing, rfl, 11, output ["x"] value, by decide⟩,
    LocalInputs.runTypedLetReturnTree?_outOfFuel_iff_evaluator.mpr ⟨typing, value, 11, output ["x"] value, by decide⟩⟩

private def unknown := binding "unused" (ref "seed") (returned (ref "seed")) "Unknown"
theorem an_unknown_unused_annotation_has_a_strict_raw_path_but_no_whole_acceptance
    (value : Core.Value) (type : Core.Ty) (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? owner table (env value) unknown = some (value, 4) ∧
    elaborateTypedLetReturnTree? (types type) owner (initial type) unknown = none := by
  have raw : TypedLetReturnTreeEvaluatesWithCost owner table (env value) store unknown value store 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (name := ⟨span, "unused"⟩)
      (annotation := annotation "Unknown") (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head .head
    · exact .single (.expression (.identifier (.tail (by decide) .head) (.tail (by decide) .head)))
  refine ⟨evaluateTypedLetReturnTreeWithCost?_complete raw, ?_⟩
  have unused : "unused" ∉ (initial type).names.map Prod.fst := by change "unused" ∉ ["seed"]; decide
  have missing : interpretStructuralType? (types type) (annotation "Unknown") = none := by simp only [annotation, interpretStructuralType?_named_eq_typeName]; rfl
  simp only [unknown, binding, elaborateTypedLetReturnTree?, if_pos unused, missing]; rfl

private def other : Resolved.DeclarationId := { owner with declarationIndex := 9 }
private def collidingInputs : LocalTypeInputs :=
  ⟨[⟨"seed", id 7, .word⟩, ⟨"seed", ⟨other, 50⟩, .bool⟩], by decide⟩
theorem name_table_freshness_does_not_require_freshness_for_extra_environment_rows
    (value hidden : Core.Value) (store : Core.Store) :
    let values : Resolved.Environment := [(id 8, hidden), (id 7, value), (⟨other, 50⟩, .bool true)]
    let body := binding "seed" (ref "seed") (returned (ref "seed"))
    Resolved.freshLocalId owner (collidingInputs.names.map Prod.snd) = id 8 ∧
    id 8 ∈ values.ids ∧
    evaluateTypedLetReturnTreeWithCost? owner collidingInputs.names values body = some (value, 4) ∧
    elaborateTypedLetReturnTree? (types .word) owner collidingInputs body = none := by
  intro values body
  have raw : TypedLetReturnTreeEvaluatesWithCost owner collidingInputs.names values store body value store 4 :=
    .binding (name := ⟨span, "seed"⟩) (annotation := annotation) (initializerCost := 1) (tailCost := 1)
      (.identifier .head (.tail (by decide) .head)) (.single (.expression (.identifier .head .head)))
  refine ⟨rfl, by simp [values, Resolved.LocalScope.ids], evaluateTypedLetReturnTreeWithCost?_complete raw, ?_⟩
  simp [body, binding, elaborateTypedLetReturnTree?, collidingInputs, LocalTypeInputs.names]

theorem selected_initializers_cannot_invent_missing_values_even_when_the_tail_ignores_them
    (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? owner table [] unknown = none ∧
    ¬ ∃ value cost, TypedLetReturnTreeEvaluatesWithCost owner table [] store unknown value store cost := by
  have absent : ¬ ∃ value cost, TypedLetReturnTreeEvaluatesWithCost owner table [] store unknown value store cost := by
    rintro ⟨value, cost, path⟩
    cases path with
    | single child => cases child
    | binding initializer _ => cases initializer with | identifier _ found => cases found
  exact ⟨(evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mpr absent, absent⟩

theorem bare_return_and_unsupported_body_shapes_are_not_silently_rewritten
    (names : LocalNameTable) (values : Resolved.Environment) :
    evaluateTypedLetReturnTreeWithCost? owner names values ⟨span, [⟨span, .returnStmt none⟩]⟩ = some (.unit, 1) ∧
    evaluateTypedLetReturnTreeWithCost? owner names values ⟨span, []⟩ = none ∧
    evaluateTypedLetReturnTreeWithCost? owner names values ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ none (some zero)⟩]⟩ = none ∧
    evaluateTypedLetReturnTreeWithCost? owner names values ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ (some annotation) none⟩]⟩ = none ∧
    evaluateTypedLetReturnTreeWithCost? owner names values ⟨span, [⟨span, .ifThen guard (returned zero) none⟩]⟩ = none ∧
    evaluateTypedLetReturnTreeWithCost? owner names values ⟨span, [⟨span, .returnStmt none⟩, ⟨span, .returnStmt none⟩]⟩ = none := by
  simp [evaluateTypedLetReturnTreeWithCost?]

theorem actual_opaque_values_remain_raw_values_while_a_retained_frame_can_fault
    (names : List String) (location : Core.Location) (captured : Core.Word) (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? owner table (env (.cellRef .word location)) (tree names "seed") =
      some (.cellRef .word location, 10 * names.length + 1) ∧
    evaluateTypedLetReturnTreeWithCost? owner table (env (.closure .bool .word (.var 1) [.word captured])) (tree names "seed") =
      some (.closure .bool .word (.var 1) [.word captured], 10 * names.length + 1) ∧
    Core.ValueHasType (.cellRef .word location) (.cell .word) ∧
    Core.ValueHasType (.closure .bool .word (.var 1) [.word captured]) (.function .bool .word) ∧
    Core.runStateful 11 ⟨.eval (core 1) [.bool true], [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot (.bool true)) ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ :=
  ⟨output names _, output names _, .cellRef, .closure (.cons .word .nil) (.var rfl), rfl⟩

theorem an_unselected_unknown_annotation_is_skipped_only_by_raw_evaluation
    (value : Core.Value) (type : Core.Ty) (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? owner table (env value) (branch guard (returned (ref "seed")) unknown) = some (value, 8) ∧
    elaborateTypedLetReturnTree? (types type) owner (initial type) (branch guard (returned (ref "seed")) unknown) = none := by
  refine ⟨evaluateTypedLetReturnTreeWithCost?_complete (TypedLetReturnTreeEvaluatesWithCost.ifTrue (owner := owner) (table := table) (environment := env value)
    (blockSpan := span) (statementSpan := span) (condition := guard) (thenBody := returned (ref "seed")) (elseBody := unknown)
    (.equal (.wordLiteral (store := store) zeroMeaning) (.wordLiteral zeroMeaning)) (.single (.expression (.identifier .head .head)))), ?_⟩
  apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
  rintro ⟨_, typing⟩
  cases typing with
  | single child => cases child
  | conditional _ _ skipped =>
    cases skipped with
    | single child => cases child
    | binding meaning _ _ _ =>
      have impossible := meaning.complete
      have absent : interpretStructuralType? (types type) (annotation "Unknown") = none := by simp only [annotation, interpretStructuralType?_named_eq_typeName]; rfl
      rw [absent] at impossible; cases impossible
end Tests.FrontendTypedLetReturnTreeEvaluator
