import Solcore.Frontend.TypedLetReturnTreeExecutionProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluationProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluationEmbeddingProperties
import Solcore.Frontend.TypedLetReturnTreeProperties
import Solcore.Frontend.TypedLetReturnBodyEvaluationProperties
import Solcore.Core.Safety

/-! Independent selected paths distinguish raw scope, whole checking, actual
typing and pending-frame safety. No new runner or entry is assumed. -/
set_option autoImplicit false
namespace Tests.FrontendTypedLetReturnTreeEvaluation
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetTreeEvaluation", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-tree-evaluation.sol"⟩, 21, 5⟩
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
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree : List String → String → Syntax.Block
  | [], previous => returned (ref previous)
  | name :: rest, previous => binding name (ref previous) (branch guard (tree rest name) (returned (ref name)))
private def core : Nat → Core.Expr
  | 0 => .var 0
  | depth + 1 => .letE (.var 0) (.ifE guardCore (core depth) (.var 0))
private def inputs (type : Core.Ty) : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "seed" type
private def table : LocalNameTable := [("seed", id 0)]
private def env (value : Core.Value) : Resolved.Environment := [(id 0, value)]
private theorem guardCost (names : LocalNameTable) (values : Resolved.Environment) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names values store guard (.bool true) store 5 :=
  .equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)
private theorem rawPath (names : List String) (previous : String) (namesTable : LocalNameTable)
    (values : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluates namesTable values store (ref previous) value store) :
    TypedLetReturnTreeEvaluates owner namesTable values store (tree names previous) value store := by
  induction names generalizing previous namesTable values with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
    exact .binding head
      (.ifTrue (guardCost _ _ store).erase (ih name _ _ (.identifier .head .head)))
private theorem counted (names : List String) (previous : String) (namesTable : LocalNameTable)
    (values : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost namesTable values store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost owner namesTable values store (tree names previous) value store (10 * names.length + 1) := by
  induction names generalizing previous namesTable values with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
    have arithmetic : 1 + (5 + (10 * rest.length + 1) + 2) + 2 = 10 * (name :: rest).length + 1 := by simp; omega
    simpa only [arithmetic, tree, binding, branch] using TypedLetReturnTreeEvaluatesWithCost.binding
      (name := ⟨span, name⟩) (annotation := annotation) head
      (.ifTrue (guardCost _ _ store) (ih name _ _ (.identifier .head .head)))
private theorem elaborated (names : List String) (previous : String) (type : Core.Ty)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var 0)) (typed : Resolved.HasType initial.context resolved type) :
    TypedLetReturnTreeElaborates (types type) owner initial (tree names previous) (core names.length) type := by
  induction names generalizing previous initial resolved with
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
    · apply ih name (initial.bindFresh owner name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head
    · exact .single (.expression (.identifier .head) (.var .head) (.var .head))
private theorem seedElab (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (inputs type) (tree names "seed") (core names.length) type := by
  apply elaborated names "seed" type (inputs type) _ distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head
private theorem seedCost (names : List String) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (tree names "seed") value store (10 * names.length + 1) :=
  counted names "seed" table (env value) value store (.identifier .head .head)

theorem arbitrary_raw_lists_have_independent_counted_paths (names : List String) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluates owner table (env value) store (tree names "seed") value store ∧
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (tree names "seed") value store (10 * names.length + 1) :=
  ⟨rawPath names "seed" table (env value) value store (.identifier .head .head), seedCost names value store⟩
theorem raw_lists_need_no_freshness_and_determine_their_positive_exact_cost
    (names : List String) (value rawValue countedValue : Core.Value) (store rawStore countedStore : Core.Store) (cost : Nat)
    (raw : TypedLetReturnTreeEvaluates owner table (env value) store (tree names "seed") rawValue rawStore)
    (costed : TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (tree names "seed") countedValue countedStore cost) :
    TypedLetReturnTreeEvaluates owner table (env value) store (tree names "seed") value store ∧
    rawValue = value ∧ rawStore = store ∧ countedValue = value ∧ countedStore = store ∧ cost = 10 * names.length + 1 ∧ 0 < cost ∧
    (∃ amount, TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (tree names "seed") rawValue rawStore amount) ∧
    (TypedLetReturnTreeEvaluates owner table (env value) store (tree names "seed") value store ↔
      ∃ amount, TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (tree names "seed") value store amount) := by
  have original := seedCost names value store
  have same := costed.deterministic original
  exact ⟨original.erase, (raw.deterministic original.erase).1, raw.store_eq, same.1, costed.store_eq, same.2.2,
    costed.cost_pos, raw.exists_cost, typedLetReturnTreeEvaluates_iff_exists_cost⟩

theorem independent_whole_provenance_gives_exact_core_paths_without_runtime_typing
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (value result : Core.Value) (store finalStore : Core.Store) (continuation : List Core.Frame) :
    TypedLetReturnTreeElaborates (types type) owner (inputs type) (tree names "seed") (core names.length) type ∧
    (TypedLetReturnTreeEvaluates owner table (env value) store (tree names "seed") result finalStore ↔
      Core.Evaluates [value] store (core names.length) result finalStore) ∧
    Core.Steps (10 * names.length + 1) ⟨.eval (core names.length) [value], continuation, store⟩ ⟨.ret value, continuation, store⟩ ∧
    Core.Steps (10 * names.length + 1) (Core.State.initial (core names.length) [value] store) (Core.State.final value store) :=
  ⟨seedElab names type distinct fresh, elaborateTypedLetReturnTree?_evaluates_iff (seedElab names type distinct fresh).complete rfl,
    (seedCost names value store).checked_toStepsWithContinuation (seedElab names type distinct fresh).complete rfl continuation,
    (seedCost names value store).checked_toSteps (seedElab names type distinct fresh).complete rfl⟩

theorem actual_typing_supplies_existence_and_preservation_but_static_nominal_types_do_not
    (type : Core.Ty) (actual value : Core.Value) (typed : Core.ValueHasType actual type) (store finalStore : Core.Store)
    (nominal : Core.DataTypeId)
    (raw : TypedLetReturnTreeEvaluates owner table (env actual) store (tree ["x"] "seed") value finalStore) :
    (∃ result, TypedLetReturnTreeEvaluates owner table (env actual) store (tree ["x"] "seed") result store ∧ Core.ValueHasType result type) ∧
    Core.ValueHasType value type ∧ finalStore = store ∧
    elaborateTypedLetReturnTree? (types (.namedData nominal)) owner (inputs (.namedData nominal)) (tree ["x"] "seed") =
      some (core 1, .namedData nominal) ∧ ¬ ∃ result, Core.ValueHasType result (.namedData nominal) := by
  have typing := (seedElab ["x"] type (by decide) (by decide)).hasType
  have supplied : Core.EnvironmentHasTypes (env actual).values (inputs type).context.values := .cons typed .nil
  refine ⟨typing.evaluates rfl supplied store, (raw.preserves_type typing rfl supplied).1,
    (raw.preserves_type typing rfl supplied).2, (seedElab ["x"] _ (by decide) (by decide)).complete, ?_⟩
  rintro ⟨result, impossible⟩
  cases impossible with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem existing_typed_cells_and_closures_are_returned_without_access_or_invocation
    (location : Core.Location) (word : Core.Word) (store : Core.Store) (continuation : List Core.Frame) :
    Core.ValueHasType (.cellRef .word location) (.cell .word) ∧
    Core.ValueHasType (.closure .bool .word (.var 1) [.word word]) (.function .bool .word) ∧
    Core.Steps 11 ⟨.eval (core 1) [.cellRef .word location], continuation, store⟩ ⟨.ret (.cellRef .word location), continuation, store⟩ ∧
    Core.Steps 11 ⟨.eval (core 1) [.closure .bool .word (.var 1) [.word word]], continuation, store⟩
      ⟨.ret (.closure .bool .word (.var 1) [.word word]), continuation, store⟩ :=
  ⟨.cellRef, .closure (.cons .word .nil) (.var rfl),
    (seedCost ["x"] _ store).checked_toStepsWithContinuation (seedElab ["x"] (.cell .word) (by decide) (by decide)).complete rfl _,
    (seedCost ["x"] _ store).checked_toStepsWithContinuation (seedElab ["x"] (.function .bool .word) (by decide) (by decide)).complete rfl _⟩

private def pairInputs : LocalTypeInputs := ⟨[⟨"c", id 0, .bool⟩, ⟨"x", id 3, .word⟩, ⟨"y", id 8, .word⟩], by decide⟩
private def pairEnv (choice : Bool) (left right : Core.Word) : Resolved.Environment := [(id 0, .bool choice), (id 3, .word left), (id 8, .word right)]
private def sub (left right : String) : Syntax.Expr := ⟨span, .binary (ref left) ⟨span, .subtract⟩ (ref right)⟩
private def bitNot (value : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, .bitNot⟩ value⟩
private def siblings := branch (ref "c") (binding "z" (sub "x" "y") (returned (ref "z")))
  (binding "z" (sub "y" "x") (returned (bitNot (ref "z"))))
private def siblingsCore : Core.Expr := .ifE (.var 0) (.letE (.binary .wordSub (.var 1) (.var 2)) (.var 0))
  (.letE (.binary .wordSub (.var 2) (.var 1)) (.unary .wordNot (.var 0)))
private theorem siblingsElab : TypedLetReturnTreeElaborates (types .word) owner pairInputs siblings siblingsCore .word :=
  .conditional (.identifier .head) (.var .head) (.var .head)
    (.binding (.named .head) (by decide)
      (.subtract (.identifier (.tail (by decide) .head)) (.identifier (.tail (by decide) (.tail (by decide) .head))))
      (.binary (.var (.tail (by decide) .head)) (.var (.tail (by decide) (.tail (by decide) .head))))
      (.binary (.var (.tail (by decide) .head)) (.var (.tail (by decide) (.tail (by decide) .head))))
      (.single (.expression (.identifier .head) (.var .head) (.var .head))))
    (.binding (.named .head) (by decide)
      (.subtract (.identifier (.tail (by decide) (.tail (by decide) .head))) (.identifier (.tail (by decide) .head)))
      (.binary (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) .head)))
      (.binary (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) .head)))
      (.single (.expression (.bitNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))))
private theorem siblingsCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner pairInputs.names (pairEnv choice left right) store siblings
      (.word (if choice then left.sub right else (right.sub left).bitNot)) store (if choice then 11 else 13) := by
  have c : LocalExpressionEvaluatesWithCost pairInputs.names (pairEnv choice left right) store (ref "c") (.bool choice) store 1 := .identifier .head .head
  have x : LocalExpressionEvaluatesWithCost pairInputs.names (pairEnv choice left right) store (ref "x") (.word left) store 1 := .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have y : LocalExpressionEvaluatesWithCost pairInputs.names (pairEnv choice left right) store (ref "y") (.word right) store 1 := .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
  cases choice
  · exact .ifFalse c (.binding (.subtract y x) (.single (.expression (.bitNot (.identifier .head .head)))))
  · exact .ifTrue c (.binding (.subtract x y) (.single (.expression (.identifier .head .head))))
theorem same_id_siblings_use_original_scopes_and_different_selected_costs
    (choice : Bool) (left right : Core.Word) (store : Core.Store) (continuation : List Core.Frame) :
    Resolved.freshLocalId owner pairInputs.ids = id 9 ∧
    (pairInputs.bindFresh owner "z" .word).ids = (pairInputs.bindFresh owner "other" .bool).ids ∧
    elaborateTypedLetReturnTree? (types .word) owner pairInputs siblings = some (siblingsCore, .word) ∧
    TypedLetReturnTreeEvaluatesWithCost owner pairInputs.names (pairEnv choice left right) store siblings
      (.word (if choice then left.sub right else (right.sub left).bitNot)) store (if choice then 11 else 13) ∧
    Core.Steps (if choice then 11 else 13) ⟨.eval siblingsCore [.bool choice, .word left, .word right], continuation, store⟩
      ⟨.ret (.word (if choice then left.sub right else (right.sub left).bitNot)), continuation, store⟩ :=
  ⟨rfl, rfl, siblingsElab.complete, siblingsCost choice left right store,
    (siblingsCost choice left right store).checked_toStepsWithContinuation siblingsElab.complete rfl continuation⟩

private def unknown := binding "unused" (ref "seed") (returned (ref "seed")) "Missing"
private theorem unknownCost (value : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store unknown value store 4 := by
  apply TypedLetReturnTreeEvaluatesWithCost.binding (name := ⟨span, "unused"⟩) (annotation := annotation "Missing") (initializerCost := 1) (tailCost := 1)
  · exact .identifier .head .head
  · exact .single (.expression (.identifier (.tail (by decide) .head) (.tail (by decide) .head)))
private theorem unknownNone (type : Core.Ty) : elaborateTypedLetReturnTree? (types type) owner (inputs type) unknown = none := by
  have unused : "unused" ∉ (inputs type).names.map Prod.fst := by change "unused" ∉ ["seed"]; decide
  have missing : interpretStructuralType? (types type) (annotation "Missing") = none := by simp only [annotation, interpretStructuralType?_named_eq_typeName]; rfl
  simp only [unknown, binding, elaborateTypedLetReturnTree?, if_pos unused, missing]
  rfl
private def buried : Nat → Syntax.Block
  | 0 => unknown
  | depth + 1 => branch guard (returned (ref "seed")) (buried depth)
private theorem buriedNone (depth : Nat) (type : Core.Ty) :
    elaborateTypedLetReturnTree? (types type) owner (inputs type) (buried depth) = none := by
  induction depth with
  | zero => exact unknownNone type
  | succ depth ih =>
    apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
    rintro ⟨_, typed⟩
    cases typed with
    | single child => cases child
    | conditional _ _ other => exact elaborateTypedLetReturnTree?_eq_none_iff.mp ih ⟨_, other⟩
theorem unused_initializers_are_strict_while_unselected_invalid_depths_need_no_raw_path
    (depth : Nat) (value : Core.Value) (type : Core.Ty) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store unknown value store 4 ∧
    ¬ TypedLetReturnTreeEvaluatesWithCost owner table (env value) store unknown value store 1 ∧
    elaborateTypedLetReturnTree? (types type) owner (inputs type) unknown = none ∧
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (buried (depth + 1)) value store 8 ∧
    elaborateTypedLetReturnTree? (types type) owner (inputs type) (buried (depth + 1)) = none := by
  have leaf : ReturnBodyEvaluatesWithCost table (env value) store (returned (ref "seed")) value store 1 :=
    .expression (.identifier .head .head)
  refine ⟨unknownCost value store, ?_, unknownNone type,
    .ifTrue (guardCost table (env value) store) (.single leaf), buriedNone _ type⟩
  intro skipped
  cases (skipped.deterministic (unknownCost value store)).2.2

theorem a_valid_initializer_cannot_invent_a_missing_runtime_value (store finalStore : Core.Store) (value : Core.Value) :
    elaborateTypedLetReturnTree? (types .word) owner (inputs .word) (tree ["x"] "seed") = some (core 1, .word) ∧
    ¬ TypedLetReturnTreeEvaluates owner table [] store (tree ["x"] "seed") value finalStore := by
  refine ⟨(seedElab ["x"] .word (by decide) (by decide)).complete, ?_⟩
  intro raw
  cases raw with
  | single child => cases child
  | binding initializer _ => cases initializer with | identifier _ found => cases found

theorem aligned_untyped_values_have_exact_correspondence_without_the_declared_result_type (store : Core.Store) :
    elaborateTypedLetReturnTree? (types .word) owner (inputs .word) (tree ["x"] "seed") = some (core 1, .word) ∧
    Core.Evaluates [.bool true] store (core 1) (.bool true) store ∧ ¬ Core.ValueHasType (.bool true) .word :=
  ⟨(seedElab ["x"] .word (by decide) (by decide)).complete,
    (elaborateTypedLetReturnTree?_evaluates_iff (seedElab ["x"] .word (by decide) (by decide)).complete rfl).mp
      (seedCost ["x"] (.bool true) store).erase, by intro impossible; cases impossible⟩

theorem correctly_typed_values_do_not_repair_swapped_identity_order (store : Core.Store) :
    let initial : LocalTypeInputs := ⟨[⟨"seed", id 0, .bool⟩, ⟨"other", id 9, .bool⟩], by decide⟩
    let swapped : Resolved.Environment := [(id 9, .bool false), (id 0, .bool true)]
    elaborateTypedLetReturnTree? (types .bool) owner initial (tree ["x"] "seed") = some (core 1, .bool) ∧
    swapped.ids ≠ initial.context.ids ∧ Core.EnvironmentHasTypes swapped.values initial.context.values ∧
    TypedLetReturnTreeEvaluates owner initial.names swapped store (tree ["x"] "seed") (.bool true) store ∧
    Core.Evaluates swapped.values store (core 1) (.bool false) store ∧ ¬ Core.Evaluates swapped.values store (core 1) (.bool true) store := by
  intro initial swapped
  have exact := elaborated ["x"] "seed" .bool initial (.var (id 0)) (by decide)
    (by intro name member; simp only [List.mem_singleton] at member; subst name; decide)
    (.identifier .head) (.var .head) (.var .head)
  have wrong : Core.Evaluates swapped.values store (core 1) (.bool false) store :=
    .letE (.var rfl) (.ifTrue (.binary .word .word rfl) (.var rfl))
  refine ⟨exact.complete, by decide, .cons .bool (.cons .bool .nil),
    (counted ["x"] "seed" initial.names swapped (.bool true) store (.identifier .head (.tail (by decide) .head))).erase, wrong, ?_⟩
  intro impossible
  cases (Core.evaluation_deterministic impossible wrong).1

theorem exact_pending_endpoints_can_exhaust_or_fault_without_unwinding (store : Core.Store) :
    Core.runStateful 11 ⟨.eval (core 1) [.bool true], [.unaryApply .boolNot], store⟩ =
      .outOfFuel ⟨.ret (.bool true), [.unaryApply .boolNot], store⟩ ∧
    Core.runStateful 0 ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot (.bool true)) ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ ∧
    Core.runStateful 11 ⟨.eval (core 1) [.bool true], [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot (.bool true)) ⟨.ret (.bool true), [.unaryApply .wordNot], store⟩ := ⟨rfl, rfl, rfl⟩

theorem old_raw_and_counted_profiles_embed_without_checking_or_extra_cost (value : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluates owner table (env value) store (returned (ref "seed")) value store ∧
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (returned (ref "seed")) value store 1 ∧
    TypedLetReturnTreeEvaluates owner table (env value) store unknown value store ∧
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store unknown value store 4 := by
  have leaf : TerminalReturnTreeEvaluatesWithCost table (env value) store (returned (ref "seed")) value store 1 :=
    .single (.expression (.identifier .head .head))
  have oldCost : TypedLetReturnBodyEvaluatesWithCost owner table (env value) store unknown value store 4 := by
    apply TypedLetReturnBodyEvaluatesWithCost.binding (name := ⟨span, "unused"⟩) (annotation := annotation "Missing") (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head .head
    · exact .terminal (.single (.expression (.identifier (.tail (by decide) .head) (.tail (by decide) .head))))
  exact ⟨leaf.erase.typedLetReturnTree owner, leaf.typedLetReturnTree owner, oldCost.erase.returnTree, oldCost.returnTree⟩

end Tests.FrontendTypedLetReturnTreeEvaluation
