import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.TypedLetReturnBody
import Solcore.Core.Safety
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.RuntimeFunction

/-!
# Typed let tree evaluation tests

Evaluation of typed let return trees.
-/

section
-- leanmerge: from Solcore.Test.FrontendTypedLetReturnTreeEvaluationProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetReturnTreeEvaluation
/-! Actual source-path scripts certify strict old-scope initializers and selected
recursive arms. Independent expected Core, values and costs are not runner output.
Recursive entries preserve the same actual Core path; old body adapters stay narrow. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetTreeEvaluation", by decide⟩], by decide⟩⟩, 9⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def stores : List Core.Store := [[.word (word 101), .cellRef .word 31],
  [.closure .bool .bool (.var 0) [], .bool false, .word Core.Word.maximum]]
private def actual (content : String) (arguments : List TypedRuntimeArgument) : IO (Syntax.FunctionDecl × LocalInputs × List TypedRuntimeArgument) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-let-tree-evaluation.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"function did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "function was diagnosed or incompletely consumed"
  match bound : bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "actual typed arguments did not bind")
  | some inputs =>
      have declared := (bindRuntimeParameters?_sound bound).erase_values
      have _ := declared.complete
      let names := source.value.signature.parameters.elements.filterMap fun parameter => match parameter.value with
        | .typed none name _ => some name.value | _ => none
      assertTrue (decide (inputs.environment.values = arguments.reverse.map (·.value) ∧
        inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
        (declareRuntimeParameters? types owner source.value.signature.parameters.elements).map (fun i => (i.names, i.context.values)) =
          some (inputs.names, inputs.context.values))) "actual source positions, original IDs, values or static factorization changed"
      return (source, inputs, arguments)
private structure Expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table environment store source value store cost
private def reference (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "script expected an existing name")
      | some id =>
          match found : environment.lookup? id with
          | none => throw (IO.userError "script expected an actual value")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "script expected a reference")
private def expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ => reference table environment store source
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← reference table environment store operand
      match valueAt : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (by simpa only [valueAt] using child.costed)⟩
      | _ => throw (IO.userError "word-not script received a non-Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table environment store left
      let second ← reference table environment store right
      match leftAt : first.value, rightAt : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]
          exact .subtract (by simpa only [leftAt] using first.costed) (by simpa only [rightAt] using second.costed)⟩
      | _, _ => throw (IO.userError "subtraction script received a non-Word")
  | _ => throw (IO.userError "expression is outside the fixture script")
private structure Certificate (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  raw : TypedLetReturnTreeEvaluates owner table environment store source value store
  costed : TypedLetReturnTreeEvaluatesWithCost owner table environment store source value store cost
private structure Leaf (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : ReturnBodyEvaluatesWithCost table environment store source value store cost
private def certify (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) (choices : List Bool) : IO (Certificate table environment store source) := do
  match sourceAt : source with
  | ⟨blockSpan, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let child ← expression table environment store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, child.value) :: environment) store ⟨blockSpan, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by rw [sourceAt]; exact .binding child.costed.erase tail.raw,
        by rw [sourceAt]; exact .binding child.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "missing selected-branch script")
      let guard ← reference table environment store condition
      if agrees : guard.value = .bool choice then
        match choiceAt : choice with
        | true =>
            let child ← certify table environment store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]
              exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed.erase) child.raw,
              by rw [sourceAt]; exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
        | false =>
            let child ← certify table environment store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]
              exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed.erase) child.raw,
              by rw [sourceAt]; exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
      else throw (IO.userError "script disagrees with actual guard")
  | ⟨_, [⟨_, .returnStmt returned⟩]⟩ =>
      assertTrue choices.isEmpty "script continued after return"
      let leaf : Leaf table environment store source ←
        match returnedAt : returned with
        | none => pure ⟨.unit, 1, by rw [sourceAt, returnedAt]; exact .bare⟩
        | some operand => do
            let child ← expression table environment store operand
            pure ⟨child.value, child.cost, by rw [sourceAt, returnedAt]; exact .expression child.costed⟩
      let oldTree := TerminalReturnTreeEvaluatesWithCost.single leaf.costed
      let oldPrefix := TypedLetReturnBodyEvaluatesWithCost.terminal (owner := owner) oldTree
      let oldRaw := TerminalReturnTreeEvaluates.single leaf.costed.erase
      have _ := oldRaw.typedLetReturnTree owner
      have _ := oldTree.typedLetReturnTree owner
      have _ := (TypedLetReturnBodyEvaluates.terminal (owner := owner) oldRaw).returnTree
      have _ := oldPrefix.returnTree
      return ⟨leaf.value, leaf.cost, .single leaf.costed.erase, .single leaf.costed⟩
  | _ => throw (IO.userError "script cannot describe this original body")
termination_by sizeOf source
private theorem arbitraryContinuation {inputs : LocalTypeInputs} {environment : Resolved.Environment}
    {store : Core.Store} {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (certificate : Certificate inputs.names environment store source)
    (accepted : elaborateTypedLetReturnTree? types owner inputs source = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) (continuation : List Core.Frame) :
    Core.Steps certificate.cost ⟨.eval core environment.values, continuation, store⟩ ⟨.ret certificate.value, continuation, store⟩ :=
  certificate.costed.checked_toStepsWithContinuation accepted sameIds continuation
private def checked (source : Syntax.FunctionDecl) (inputs : LocalInputs) (arguments : List TypedRuntimeArgument) (choices : List Bool)
    (expectedCore : Core.Expr) (expected : TypedRuntimeArgument) (cost : Nat) (branchBindings : Bool := true) : IO Unit := do
  have aligned : inputs.environment.ids = inputs.toTypeInputs.context.ids := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
  have environmentTyped : Core.EnvironmentHasTypes inputs.environment.values inputs.toTypeInputs.context.values := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.environmentTyped
  for store in stores do
    let certificate ← certify inputs.toTypeInputs.names inputs.environment store source.value.body choices
    assertTrue (decide (certificate.value = expected.value ∧ certificate.cost = cost)) "independent selected source value/cost changed"
    match accepted : elaborateTypedLetReturnTree? types owner inputs.toTypeInputs source.value.body with
    | none => throw (IO.userError "whole tree rejected")
    | some (core, type) =>
        let typing := elaborateTypedLetReturnTree?_sound accepted
        have _ := typing.evaluates aligned environmentTyped store
        have _ := certificate.raw.preserves_type typing aligned environmentTyped
        have _ := certificate.raw.store_eq
        have _ := certificate.raw.exists_cost
        have _ := typedLetReturnTreeEvaluates_iff_exists_cost.mp certificate.raw
        have _ := certificate.raw.deterministic certificate.costed.erase
        have _ := certificate.costed.store_eq
        have _ := certificate.costed.cost_pos
        have _ := certificate.costed.deterministic certificate.costed
        let bridge := elaborateTypedLetReturnTree?_evaluates_iff accepted aligned
        have _ := bridge.mpr (bridge.mp certificate.raw)
        have _ := certificate.costed.checked_toSteps accepted aligned
        have _ := arbitraryContinuation certificate accepted aligned
        assertTrue (decide (core = expectedCore ∧ type = expected.type ∧ Core.infer? inputs.context.values core = some type ∧
          interpretRuntimeFunctionHeader? types source.value.signature = some type)) "actual accepted Core/type/header changed"
        assertTrue (decide ((compileRuntimeFunction? types owner source).map (fun c => (c.core, c.returnType, c.inputs.names, c.inputs.context.values)) =
          some (expectedCore, expected.type, inputs.names, inputs.context.values)) && (prepareRuntimeFunction? types owner source arguments).any (fun p =>
            decide (p.core = expectedCore ∧ p.returnType = expected.type ∧ p.inputs.names = inputs.names ∧ p.inputs.context.values = inputs.context.values ∧
              p.inputs.environment.values = arguments.reverse.map (·.value)))) "entry changed Core or original actual parameter rows"
        if branchBindings then assertTrue (inputs.checkTypedLetReturnBody? types owner source.value.body).isNone "old prefix adapter broadened"
        for fuel in List.range (cost + 3) do
          assertTrue (decide (runRuntimeFunction? types owner source arguments fuel store =
            some (expected.type, Core.runStateful fuel (.initial expectedCore inputs.environment.values store)))) "entry changed the full same-fuel machine result"
          assertTrue (match Core.runStateful fuel (.initial core inputs.environment.values store) with
            | .done value finalStore => decide (cost ≤ fuel ∧ value = expected.value ∧ finalStore = store)
            | .outOfFuel checkpoint => decide (fuel < cost ∧ checkpoint.store = store)
            | .fault _ _ => false) "exact independent cost threshold, value or own store changed"
        let safe : List Core.Frame := [.letBody (.var 0) [.word (word 17)], .unaryApply .wordNot]
        have _ := arbitraryContinuation certificate accepted aligned safe
        assertTrue (decide (Core.runStateful cost ⟨.eval core inputs.environment.values, safe, store⟩ =
          .outOfFuel ⟨.ret expected.value, safe, store⟩)) "pending continuation was executed or discarded"
        if (Core.UnaryOp.wordNot.apply expected.value).isNone then
          let bad : List Core.Frame := [.unaryApply .wordNot]
          have _ := arbitraryContinuation certificate accepted aligned bad
          assertTrue (decide (Core.runStateful cost ⟨.eval core inputs.environment.values, bad, store⟩ =
            .fault (.invalidUnaryOperand .wordNot expected.value) ⟨.ret expected.value, bad, store⟩)) "zero remaining fuel concealed the incompatible frame"
private def alternating (remaining level : Nat) : String × Core.Expr :=
  match remaining with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 1 else 0))
  | count + 1 =>
      let (tail, core) := alternating count (level + 1)
      let recursiveText := s!"let z{level}: Word=" ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail
      let leafText := s!"let z{level}: Word=y;return z{level};"
      let recCore := Core.Expr.letE (.var (if level = 0 then 1 else 0)) core
      let leafCore := Core.Expr.letE (.var level) (.var 0)
      if level % 2 = 0 then ("if(c){" ++ recursiveText ++ "}else{" ++ leafText ++ "}", .ifE (.var (level + 3)) recCore leafCore)
      else ("if(d){" ++ leafText ++ "}else{" ++ recursiveText ++ "}", .ifE (.var (level + 2)) leafCore recCore)
private theorem initializerRequired {table : LocalNameTable} {environment : Resolved.Environment} {store : Core.Store}
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier} {annotation : Syntax.TypeExpr}
    {initializer : Syntax.Expr} {rest : List Syntax.Statement}
    (absent : ¬ ∃ value finalStore, LocalExpressionEvaluates table environment store initializer value finalStore) :
    ¬ ∃ value finalStore, TypedLetReturnTreeEvaluates owner table environment store
      ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore := by
  rintro ⟨value, finalStore, evaluation⟩
  cases evaluation with
  | single child => cases child
  | binding child _ => exact absent ⟨_, _, child⟩
private def boundaries : IO Unit := do
  let (source, inputs, _) ← actual "function alignment(x: Word,y: Word) returns (Word){let z: Word=x;return y;}" [wordArg 9, wordArg 2]
  let untyped : Resolved.Environment := inputs.environment.map fun row => (row.1, Core.Value.bool true)
  have aligned : untyped.ids = inputs.toTypeInputs.context.ids := by
    simpa only [untyped, Resolved.LocalScope.ids, List.map_map, Function.comp_def, LocalInputs.toTypeInputs_context] using inputs.sameIds
  for store in stores do
    let certificate ← certify inputs.toTypeInputs.names untyped store source.value.body []
    match accepted : elaborateTypedLetReturnTree? types owner inputs.toTypeInputs source.value.body with
    | none => throw (IO.userError "alignment contrast lost static acceptance")
    | some (core, type) =>
        let bridge := elaborateTypedLetReturnTree?_evaluates_iff accepted aligned
        have _ := bridge.mpr (bridge.mp certificate.raw)
        have _ := certificate.costed.checked_toSteps accepted aligned
        assertTrue (decide (core = .letE (.var 1) (.var 1) ∧ type = .word ∧ certificate.value = .bool true ∧ certificate.cost = 4 ∧
          Core.runStateful 4 (.initial core untyped.values store) = .done (.bool true) store)) "aligned raw correspondence demanded runtime typing"
        let reordered : Resolved.Environment := inputs.environment.reverse
        let raw ← certify inputs.names reordered store source.value.body []
        assertTrue (decide (reordered.ids ≠ inputs.context.ids ∧ raw.value = .word (word 2) ∧ raw.cost = 4 ∧
          Core.runStateful 4 (.initial core reordered.values store) = .done (.word (word 9)) store)) "misaligned name lookup became positional lookup"
    match source.value.body with
    | ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some ⟨span, .identifier referenceName⟩)⟩ :: rest⟩ =>
        match named : inputs.names.lookup? referenceName.value with
        | none => throw (IO.userError "strict initializer name disappeared")
        | some id =>
            let missing : Resolved.Environment := inputs.environment.filter (fun row => row.1 != id)
            if absent : missing.lookup? id = none then
              have impossible : ¬ ∃ value finalStore, LocalExpressionEvaluates inputs.names missing store ⟨span, .identifier referenceName⟩ value finalStore := by
                rintro ⟨value, finalStore, evaluated⟩
                cases evaluated with
                | identifier other found =>
                    cases (LocalNameTable.lookup?_iff.mp named).id_unique other
                    have present := Resolved.LocalScope.lookup?_iff.mpr found
                    rw [absent] at present
                    cases present
              have _ := initializerRequired (blockSpan := blockSpan) (letSpan := letSpan) (name := name) (annotation := annotation) (rest := rest) impossible
              let tail ← certify inputs.names missing store ⟨blockSpan, rest⟩ []
              assertTrue (decide (tail.value = .word (word 2) ∧ tail.cost = 1)) "unused initializer strictness contrast lost its successful tail"
            else throw (IO.userError "removed runtime value was still available")
    | _ => throw (IO.userError "strictness contrast lost original initializer syntax")

def frontendParsedTypedLetReturnTreeEvaluationTests : IO Unit := do
  boundaries
  for depth in [0, 1, 2, 5, 12] do
    let (body, core) := alternating depth 0
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs, arguments) ← actual ("function alternating(c: Bool,d: Bool,x: Word,y: Word) returns (Word){" ++ body ++ "}")
          [boolArg c, boolArg d, wordArg 9, wordArg 2]
        let choices := if depth = 0 then [] else if !c then [false] else if depth = 1 then [true]
          else if d then [true, true] else (List.range depth).map fun level => level % 2 == 0
        checked source inputs arguments choices core (if depth == 0 || (c && (depth == 1 || !d)) then wordArg 9 else wordArg 2)
          (if depth = 0 then 1 else if !c || depth == 1 then 7 else if d then 13 else 6 * depth + 1) (depth != 0)
  for (x, y) in [(9, 2), (2, 9), (0, Core.Word.maximum.val), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs, arguments) ← actual "function asymmetric(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x - y;if(d){let w: Word=z;return ~w;}else{let w: Word=y - z;return w;}}else{let z: Word=y - x;return y;}}"
          [boolArg c, boolArg d, wordArg x, wordArg y]
        checked source inputs arguments (if c then [true, d] else [false]) (.ifE (.var 3)
          (.letE (.binary .wordSub (.var 1) (.var 0)) (.ifE (.var 3) (.letE (.var 0) (.unary .wordNot (.var 0)))
            (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 1)))
          ⟨.word, .word (if c then if d then ((word x).sub (word y)).bitNot else (word y).sub ((word x).sub (word y)) else word y), .word⟩
          (if c then if d then 19 else 21 else 11)
  let left : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let right : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, x, y) in [("Fn", left, right), ("Cell", ⟨.cell .word, .cellRef .word 17, .cellRef⟩, ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
      ("Unit", ⟨.unit, .unit, .unit⟩, ⟨.unit, .unit, .unit⟩)] do
    for c in [false, true] do
      let (source, inputs, arguments) ← actual (s!"function opaque(c: Bool,x: {name},y: {name}) returns ({name})" ++ "{if(c){let z: " ++ name ++
        "=x;if(c){let w: " ++ name ++ "=y;return z;}else{return z;}}else{let z: " ++ name ++ "=y;return z;}}") [boolArg c, x, y]
      checked source inputs arguments (if c then [true, true] else [false]) (.ifE (.var 2)
        (.letE (.var 1) (.ifE (.var 3) (.letE (.var 1) (.var 1)) (.var 0))) (.letE (.var 0) (.var 0))) (if c then x else y) (if c then 13 else 7)
  let (bare, bareInputs, bareArguments) ← actual "function bare(c: Bool,x: Word){if(c){let z: Word=x;return;}else{return;}}" [boolArg true, wordArg 9]
  checked bare bareInputs bareArguments [true] (.ifE (.var 1) (.letE (.var 0) .unit) .unit) ⟨.unit, .unit, .unit⟩ 7
  for (body, expected) in [("{if(c){let z: Unknown=x;return z;}else{return y;}}", 9), ("{if(c){let z: Bool=x;return z;}else{return y;}}", 9),
      ("{if(c){let x: Word=y;return x;}else{return y;}}", 2), ("{if(c){let z: Word=x;return z;}else{let z: Word=missing;return y;}}", 9),
      ("{if(c){let z: Word=x;return z;}else{return c;}}", 9), ("{if(c){let z: Word=x;return z;}else{if(c){return y;}else{return missing;}}}", 9)] do
    let (source, inputs, _) ← actual ("function raw(c: Bool,x: Word,y: Word) returns (Word)" ++ body) [boolArg true, wordArg 9, wordArg 2]
    for store in stores do
      let certificate ← certify inputs.names inputs.environment store source.value.body [true]
      assertTrue (decide (certificate.cost = 7 ∧ certificate.value = .word (word expected)) &&
        (elaborateTypedLetReturnTree? types owner inputs.toTypeInputs source.value.body).isNone) "raw selected success was mistaken for whole acceptance"

end Tests
end
