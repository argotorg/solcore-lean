import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Syntax.Parser.Internal.TermBasics

/-!
# Typed let tree evaluator tests

The evaluator on typed let return trees.
-/

section
-- leanmerge: from Solcore.Test.FrontendTypedLetReturnTreeEvaluatorProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetReturnTreeEvaluator
/-! Completely parsed original blocks, independent raw certificates and separate
Core/value/cost expectations. Direct evaluation neither checks nor changes entry policy. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"DirectTree", by decide⟩], by decide⟩⟩, 17⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .word .word)]
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def inputs (l r : Nat) (c d : Bool) : LocalInputs := ⟨[
  ⟨"c", ⟨owner, 2⟩, .bool, .bool c, .bool⟩, ⟨"d", ⟨other, 999⟩, .bool, .bool d, .bool⟩,
  ⟨"r", ⟨owner, 5⟩, .word, w r, .word⟩, ⟨"l", ⟨owner, 7⟩, .word, w l, .word⟩], by
    change ([⟨owner, 2⟩, ⟨other, 999⟩, ⟨owner, 5⟩, ⟨owner, 7⟩] : List Resolved.LocalId).Nodup
    decide⟩
private def parsed? (content : String) : IO (Option Syntax.Block) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "direct-tree.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed) with
  | .ok body next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (body.span.source = file.id ∧ body.span.startByte = 0 ∧ body.span.endByte = content.utf8ByteSize))
        "original block range changed"
      return some body
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")
private def parsed (content : String) : IO Syntax.Block := do
  let some body ← parsed? content | throw (IO.userError s!"incomplete block: {content}")
  return body
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def reference (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "certificate name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "certificate actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "certificate expected original reference")
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ => reference table env store source
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← reference table env store operand
      match atValue : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (atValue ▸ child.costed)⟩
      | _ => throw (IO.userError "certificate expected Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table env store left
      let second ← reference table env store right
      match atLeft : first.value, atRight : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]; exact .subtract (atLeft ▸ first.costed) (atRight ▸ second.costed)⟩
      | _, _ => throw (IO.userError "certificate subtraction expected Words")
  | _ => throw (IO.userError "expression outside independent certificate script")
private structure Certificate (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store body value store cost
private def certify (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (body : Syntax.Block) (choices : List Bool) : IO (Certificate table env store body) := do
  match atBody : body with
  | ⟨span, ⟨_, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      let child ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, child.value) :: env) store ⟨span, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by
        rw [atBody]
        cases annotation with
        | none => exact .inferred child.costed tail.costed
        | some _ => exact .binding child.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "independent branch script missing")
      let guard ← reference table env store condition
      if agrees : guard.value = .bool choice then
        match atChoice : choice with
        | true =>
            let child ← certify table env store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifTrue (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
        | false =>
            let child ← certify table env store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifFalse (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
      else throw (IO.userError "independent branch script disagrees with actual guard")
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ =>
      assertTrue choices.isEmpty "script continued past bare return"
      return ⟨.unit, 1, by rw [atBody]; exact .single .bare⟩
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      assertTrue choices.isEmpty "script continued past return"
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [atBody]; exact .single (.expression child.costed)⟩
  | _ => throw (IO.userError "body outside independent certificate script")
termination_by sizeOf body
private def raw (table : LocalNameTable) (env : Resolved.Environment) (body : Syntax.Block)
    (expected : Option (Core.Value × Nat)) (choices : List Bool := []) : IO Unit := do
  assertTrue (decide (evaluateTypedLetReturnTreeWithCost? owner table env body = expected)) "independent raw value/cost disagreed"
  for store in stores do
    match evaluated : evaluateTypedLetReturnTreeWithCost? owner table env body with
    | none => have _ := (evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mp evaluated; pure ()
    | some (_, cost) =>
        let certificate ← certify table env store body choices
        assertTrue (decide (some (certificate.value, certificate.cost) = expected)) "independent original-source certificate disagreed"
        have _ := evaluateTypedLetReturnTreeWithCost?_sound evaluated store
        have _ := evaluateTypedLetReturnTreeWithCost?_complete certificate.costed
        have _ := (evaluateTypedLetReturnTreeWithCost?_iff store).mpr certificate.costed
        have _ := typedLetReturnTreeEvaluatesWithCost_iff_evaluate.mp certificate.costed
        have _ := (evaluateTypedLetReturnTreeWithCost?_exists_cost_iff store).mp ⟨cost, evaluated⟩
        have _ := (evaluateTypedLetReturnTreeWithCost?_value_iff store).mpr certificate.costed.erase
        pure ()
private def checked (content : String) (actual : LocalInputs) (choices : List Bool)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let body ← parsed content
  raw actual.names actual.environment body (some (value, cost)) choices
  assertTrue (decide (actual.checkTypedLetReturnTree? types owner body = some (core, type) ∧
    Core.infer? actual.context.values core = some type)) "independent checked Core/type changed"
  have aligned : actual.environment.ids = actual.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using actual.sameIds
  have envTyped : Core.EnvironmentHasTypes actual.environment.values actual.toTypeInputs.context.values := by
    simpa only [LocalInputs.toTypeInputs_context] using actual.environmentTyped
  match accepted : actual.checkTypedLetReturnTree? types owner body,
      evaluated : evaluateTypedLetReturnTreeWithCost? owner actual.toTypeInputs.names actual.environment body with
  | some (_, actualType), some (found, _) =>
      let typing := elaborateTypedLetReturnTree?_sound accepted
      have _ := elaborateTypedLetReturnTree?_typed_evaluator_exists accepted aligned envTyped
      for store in stores do
        let costed := evaluateTypedLetReturnTreeWithCost?_sound evaluated store
        have _ := costed.cost_le_fuelBound
        have _ := LocalInputs.typedLetReturnTree_evaluator_execution (inputs := actual) typing store
        for continuation in [[], [.letBody (.var 0) [w 17]], [.unaryApply .wordNot]] do
          have _ := evaluateTypedLetReturnTreeWithCost?_checked_toStepsWithContinuation (store := store) evaluated accepted aligned continuation
          pure () -- Retained endpoints do not guarantee that the pending frames succeed.
        let run := fun fuel => actual.runTypedLetReturnTree? types owner fuel body store
        for fuel in List.range (typedLetReturnTreeFuelBound body + 3) do
          have _ := evaluateTypedLetReturnTreeWithCost?_checked_runStateful_done_iff (fuel := fuel) (store := store) evaluated accepted aligned
          have _ := evaluateTypedLetReturnTreeWithCost?_checked_runStateful_outOfFuel_iff (fuel := fuel) (store := store) evaluated accepted aligned
          have _ := elaborateTypedLetReturnTree?_run_done_iff_evaluator (value := found) (fuel := fuel)
            (initialStore := store) (finalStore := store) accepted aligned
          have _ := LocalInputs.runTypedLetReturnTree?_done_iff_evaluator (inputs := actual) (types := types) (owner := owner)
            (body := body) (type := actualType) (value := found) (fuel := fuel) (initialStore := store) (finalStore := store)
          have _ := LocalInputs.runTypedLetReturnTree?_outOfFuel_iff_evaluator (inputs := actual) (types := types) (owner := owner)
            (body := body) (type := actualType) (fuel := fuel) (store := store)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel (.initial core actual.environment.values store)))) "full actual Core result changed"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel state) => decide (fuel < cost ∧ t = type ∧ state.store = store)
            | _ => false) "exact threshold/value/own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              have _ : spent < _ ∧ Core.Steps (_ - spent) checkpoint (.final found store) := by
                obtain ⟨_, checkedAt, pathAt⟩ := LocalInputs.runTypedLetReturnTree?_eq_some_iff.mp exhausted
                exact costed.checked_residual_of_outOfFuel checkedAt aligned pathAt
              for remaining in List.range (cost - spent + 3) do
                have _ := LocalInputs.runTypedLetReturnTree?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "genuine resumption changed full result"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "independent residual cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart impersonated actual checkpoint"
          | _ => throw (IO.userError "genuine checkpoint missing")
  | _, _ => throw (IO.userError "positive whole/raw evidence disappeared")
private def contrast (content : String) (actual : LocalInputs) (expected : Option (Core.Value × Nat))
    (choices : List Bool := []) : IO Unit := do
  let body ← parsed content
  raw actual.names actual.environment body expected choices
  assertTrue (actual.checkTypedLetReturnTree? types owner body).isNone "raw success bypassed whole checking"
  for store in stores do
    for fuel in [0, 30] do assertTrue (actual.runTypedLetReturnTree? types owner fuel body store).isNone "whole rejection exposed a result"
private def spine (remaining level : Nat) : String × Core.Expr :=
  match remaining with
  | 0 => ("return " ++ (if level = 0 then "l" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 3 else 0))
  | count + 1 =>
      let (tail, core) := spine count (level + 1)
      ("if(c){" ++ s!"let z{level}: Word=" ++ (if level = 0 then "l" else s!"z{level - 1}") ++ ";" ++ tail ++
        "}else{" ++ s!"let z{level}: Word=r;return z{level};" ++ "}",
        .ifE (.var level) (.letE (.var (if level = 0 then 3 else 0)) core) (.letE (.var (level + 2)) (.var 0)))
private def checkOpaque (annotation : String) (type : Core.Ty) (x y : Core.Value)
    (typedX : Core.ValueHasType x type) (typedY : Core.ValueHasType y type) : IO Unit := do
  for c in [false, true] do
    let supplied := ((LocalInputs.empty.bindFresh owner "y" type y typedY).bindFresh owner "x" type x typedX).bindFresh other "c" .bool (.bool c) .bool
    let core : Core.Expr := .ifE (.var 0) (.letE (.var 1) (.letE (.var 3) (.var 1))) (.letE (.var 2) (.var 0))
    let value := if c then x else y
    let cost := if c then 10 else 7
    checked ("{if(c){let z: " ++ annotation ++ "=x;let q: " ++ annotation ++ "=y;return z;}else{let z: " ++ annotation ++ "=y;return z;}}")
      supplied [c] core type value cost
    for store in stores do
      let continuation : List Core.Frame := [.unaryApply .wordNot]
      assertTrue (decide (Core.runStateful cost ⟨.eval core supplied.environment.values, continuation, store⟩ =
        .fault (.invalidUnaryOperand .wordNot value) ⟨.ret value, continuation, store⟩))
        "retained endpoint promised success or exhaustion after incompatible pending frames"

def frontendParsedTypedLetReturnTreeEvaluatorTests : IO Unit := do
  for depth in [0, 1, 2, 5, 12] do
    let (content, core) := spine depth 0
    for c in [false, true] do
      checked ("{" ++ content ++ "}") (inputs 9 2 c false) (if depth = 0 then [] else if c then List.replicate depth true else [false])
        core .word (w (if depth = 0 || c then 9 else 2)) (if depth = 0 then 1 else if c then 6 * depth + 1 else 7)
  for (l, r) in [(9, 2), (2, 9), (0, Core.wordModulus - 1), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        checked "{if(c){let z: Word=l - r;if(d){let q: Word=z;return ~q;}else{let q: Word=r - z;return q;}}else{let z: Word=r - l;return r;}}"
          (inputs l r c d) (if c then [true, d] else [false]) (.ifE (.var 0)
            (.letE (.binary .wordSub (.var 3) (.var 2)) (.ifE (.var 2) (.letE (.var 0) (.unary .wordNot (.var 0)))
              (.letE (.binary .wordSub (.var 3) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 2) (.var 3)) (.var 3)))
          .word (if c then if d then w (Core.wordModulus - 1 - (l + Core.wordModulus - r) % Core.wordModulus)
            else w (r + Core.wordModulus - (l + Core.wordModulus - r) % Core.wordModulus) else w r) (if c then if d then 19 else 21 else 11)
  let actual := inputs 9 2 true false
  checked "{return;}" actual [] .unit .unit .unit 1
  checked "{let z: Word=l;return;}" actual [] (.letE (.var 3) .unit) .unit .unit 4
  checked "{let z=l;return z;}" actual [] (.letE (.var 3) (.var 0)) .word (w 9) 4
  checked "{let unused: Word=l - r;return r;}" actual [] (.letE (.binary .wordSub (.var 3) (.var 2)) (.var 3)) .word (w 2) 8
  checkOpaque "Cell" (.cell .word) (.cellRef .word 999) (.cellRef .word 40) .cellRef .cellRef
  checkOpaque "Fn" (.function .word .word) (.closure .word .word (.var 0) []) (.closure .word .word (.var 1) [w 7])
    (.closure .nil (.var rfl)) (.closure (.cons .word .nil) (.var rfl))
  checkOpaque "Unit" .unit .unit .unit .unit .unit
  for (content, value, cost, choices) in [("{let z: Unknown=l;return z;}", w 9, 4, []),
      ("{let z: Bool=l;return z;}", w 9, 4, []), ("{let l: Word=r;return l;}", w 2, 4, []),
      ("{let l: Word=l - r;return l;}", w 7, 8, []),
      ("{if(c){let z: Word=l;return z;}else{let z: Unknown=missing;return z;}}", w 9, 7, [true]),
      ("{if(c){return l;}else{return c;}}", w 9, 4, [true])] do contrast content actual (some (value, cost)) choices
  for content in ["{}", "{let z: Word;return l;}", "{let z: Word=l;}",
      "{return l;return r;}", "{if(c){return l;}}", "{if(c){return l;}else{return r;}return l;}",
      "{let z: Word=missing;return r;}", "{let z: Word=z;return l;}", "{let z: Word=f(l);return r;}",
      "{if(l){return l;}else{return r;}}", "{if(c && l){return l;}else{return r;}}"] do contrast content actual none
  let id : Resolved.LocalId := ⟨other, 999⟩
  let fresh : Resolved.LocalId := ⟨owner, 8⟩
  let body ← parsed "{let z: Word=l;return z;}"
  let collision : Resolved.Environment := (fresh, w 99) :: actual.environment
  assertTrue (decide (Resolved.freshLocalId owner (actual.names.map Prod.snd) = fresh ∧
    Resolved.freshLocalId owner collision.ids = ⟨owner, 9⟩ ∧
    Resolved.LocalScope.lookup? ((fresh, w 9) :: collision) fresh = some (w 9))) "allocator used the wrong table or lost its new head"
  raw actual.names collision body (some (w 9, 4))
  assertTrue (decide (collision.ids ≠ actual.context.ids ∧ Core.runStateful 4
    (.initial (.letE (.var 3) (.var 0)) collision.values []) = .done (w 2) [])) "unaligned raw lookup became positional execution"
  raw (("l", id) :: actual.names) ((id, w 4) :: (id, w 9) :: actual.environment) body (some (w 4, 4))
  raw actual.names [] body none
  for store in stores do
    let run := fun fuel => actual.runTypedLetReturnTree? types owner fuel body store
    assertTrue (decide (run 2 = some (.word, .outOfFuel
      ⟨.ret (w 9), [.letBody (.var 0) actual.environment.values], store⟩) ∧
      run 3 = some (.word, .outOfFuel ⟨.eval (.var 0) (w 9 :: actual.environment.values), [], store⟩)))
      "old-scope initializer checkpoint or actual extended tail environment changed"
  let untyped : Resolved.Environment := actual.environment.map fun row => (row.1, Core.Value.bool true)
  have aligned : untyped.ids = actual.toTypeInputs.context.ids := by
    simpa only [untyped, Resolved.LocalScope.ids, List.map_map, Function.comp_def, LocalInputs.toTypeInputs_context] using actual.sameIds
  raw actual.names untyped body (some (.bool true, 4))
  match accepted : actual.checkTypedLetReturnTree? types owner body,
      evaluated : evaluateTypedLetReturnTreeWithCost? owner actual.toTypeInputs.names untyped body with
  | some (core, type), some (_, _) =>
      have _ := evaluateTypedLetReturnTreeWithCost?_checked_runStateful_done_iff (fuel := 4) (store := []) evaluated accepted aligned
      assertTrue (decide (core = .letE (.var 3) (.var 0) ∧ type = .word ∧
        Core.runStateful 4 (.initial core untyped.values []) = .done (.bool true) [])) "aligned raw bridge acquired a runtime typing premise"
  | _, _ => throw (IO.userError "aligned untyped contrast lost whole or raw acceptance")
  let missing ← parsed "{let z: Word=missing;return r;}"
  match missing with
  | ⟨span, _ :: rest⟩ => raw actual.names actual.environment ⟨span, rest⟩ (some (w 2, 1))
  | _ => throw (IO.userError "strict unused initializer contrast lost its successful tail")
  for content in ["{", "{return l;", "{let z: Word=;return z;}", "{if(c){return l;}else", "{return;} trailing"] do
    assertTrue (← parsed? content).isNone "incomplete source acquired raw tree meaning"

end Tests
end
