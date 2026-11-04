import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Frontend.LocalExpressionLookupProperties
import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Frontend.LocalExpressionFuelBound
import Solcore.Frontend.LocalExpressionStoreProperties
import Solcore.Frontend.TypeName
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.TypedLetReturnBody
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.LocalOwnerRenaming
import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.StructuralType
import Solcore.Core.Safety
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RuntimeFunction
import Solcore.Syntax.Parser.Internal.ParameterSoundness
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.LocalExpressionRenaming

/-!
# Structural form tests

Structural lets, parameters, returns and types, inferred lets, units, tuples, and many-valued
expressions and types.
-/

section
-- leanmerge: from Solcore.Test.FrontendBinaryTupleProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendInferredLetProperties
/-! Original optional annotations, independent paths and exact old-scope
initializers distinguish monomorphic inference from runtime inhabitants. -/
set_option autoImplicit false
namespace Tests.FrontendInferredLet
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"InferredLet", by decide⟩], by decide⟩⟩, 0⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 1 }
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "inferred-let.sol"⟩, 17, 9⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def bind (name : String) (ann : Option Syntax.TypeExpr) (init : Syntax.Expr) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ ann (some init)⟩ :: tail.value⟩
private def chain : Bool → List String → String → Syntax.Block
  | _, [], previous => returned previous
  | annotated, name :: rest, previous =>
      bind name (if annotated then some annotation else none) (ref previous) (chain (!annotated) rest name)
private def core : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .letE (.var 0) (core n)
private def seed (type : Core.Ty) := LocalTypeInputs.empty.bindFresh owner "seed" type
private def table : LocalNameTable := [("seed", id 0)]
private def env (value : Core.Value) : Resolved.Environment := [(id 0, value)]
private theorem chain_eta (flag : Bool) (names : List String) (previous : String) :
    (⟨span, (chain flag names previous).value⟩ : Syntax.Block) = chain flag names previous := by cases names <;> rfl
private theorem elaborated (flag : Bool) (names : List String) (previous : String) (type : Core.Ty)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var 0)) (typed : Resolved.HasType initial.context resolved type) :
    TypedLetReturnTreeElaborates (types type) owner initial (chain flag names previous) (core names.length) type := by
  induction names generalizing flag previous initial resolved with
  | nil =>
      simp only [chain, List.length_nil, core]
      exact .single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typed)
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      have tail := ih (!flag) name (initial.bindFresh owner name type) _ parts.2 (by
        intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩)
        (.identifier .head) (.var .head) (.var .head)
      cases flag
      · exact .inferred (fresh name (by simp)) resolution lowered typed (by simpa only [chain_eta] using tail)
      · exact .binding (.named .head) (fresh name (by simp)) resolution lowered typed (by simpa only [chain_eta] using tail)
private theorem seedElab (flag : Bool) (names : List String) (type : Core.Ty)
    (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed type) (chain flag names "seed") (core names.length) type := by
  apply elaborated flag names "seed" type (seed type) _ distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head
private theorem counted (flag : Bool) (names : List String) (previous : String)
    (namesTable : LocalNameTable) (values : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost namesTable values store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost owner namesTable values store (chain flag names previous) value store (3 * names.length + 1) := by
  induction names generalizing flag previous namesTable values with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
      let fresh := Resolved.freshLocalId owner (namesTable.map Prod.snd)
      have tail := ih (!flag) name ((name, fresh) :: namesTable) ((fresh, value) :: values) (.identifier .head .head)
      have arithmetic : 1 + (3 * rest.length + 1) + 2 = 3 * (name :: rest).length + 1 := by simp; omega
      rw [← arithmetic]
      cases flag
      · exact .inferred head (by simpa only [chain_eta] using tail)
      · exact .binding head (by simpa only [chain_eta] using tail)
private theorem cost (flag : Bool) (names : List String) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (chain flag names "seed") value store (3 * names.length + 1) :=
  counted flag names "seed" table (env value) value store (.identifier .head .head)
private theorem rawPath (flag : Bool) (names : List String) (previous : String)
    (namesTable : LocalNameTable) (values : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluates namesTable values store (ref previous) value store) :
    TypedLetReturnTreeEvaluates owner namesTable values store (chain flag names previous) value store := by
  induction names generalizing flag previous namesTable values with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
      let fresh := Resolved.freshLocalId owner (namesTable.map Prod.snd)
      have tail := ih (!flag) name ((name, fresh) :: namesTable) ((fresh, value) :: values) (.identifier .head .head)
      cases flag
      · exact .inferred head (by simpa only [chain_eta] using tail)
      · exact .binding head (by simpa only [chain_eta] using tail)
private theorem path (n : Nat) (value : Core.Value) (values : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*n+1) ⟨.eval (core n) (value :: values), k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing values k with
  | zero => exact .cons (.var rfl) .refl
  | succ n ih =>
      have steps := Core.Steps.cons .enterLet (.cons (.var (index := 0) rfl) (.cons .bindLet (ih (value :: values) k)))
      simpa [core, Nat.mul_add, Nat.add_assoc] using steps

theorem arbitrary_original_mixed_lists_have_value_free_provenance
    (flag : Bool) (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed type) (chain flag names "seed") (core names.length) type ∧
    TypedLetReturnTreeHasType (types type) owner (seed type) (chain flag names "seed") type ∧
    elaborateTypedLetReturnTree? (types type) owner (seed type) (chain flag names "seed") = some (core names.length, type) :=
  ⟨seedElab flag names type distinct fresh, (seedElab flag names type distinct fresh).hasType,
    (seedElab flag names type distinct fresh).complete⟩

theorem raw_duplicate_names_need_no_static_freshness
    (flag : Bool) (names : List String) (value : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    TypedLetReturnTreeEvaluates owner table (env value) store (chain flag names "seed") value store ∧
    evaluateTypedLetReturnTreeWithCost? owner table (env value) (chain flag names "seed") = some (value, 3 * names.length + 1) ∧
    Core.Steps (3 * names.length + 1) ⟨.eval (core names.length) [value], k, store⟩ ⟨.ret value, k, store⟩ :=
  ⟨rawPath flag names "seed" table (env value) value store (.identifier .head .head),
    evaluateTypedLetReturnTreeWithCost?_complete (cost flag names value store), path _ value [] store k⟩

theorem inferred_type_and_core_are_unique_without_synthetic_annotations
    (type otherType : Core.Ty) (candidate : Core.Expr)
    (competing : TypedLetReturnTreeElaborates (types type) owner (seed type) (chain false ["x"] "seed") candidate otherType) :
    candidate = core 1 ∧ otherType = type ∧
    ∃ initializerType initializerCore tailCore, "x" ∉ (seed type).names.map Prod.fst ∧
      elaborateLocalExpression? (seed type).names (seed type).context (ref "seed") = some (initializerCore, initializerType) ∧
      elaborateTypedLetReturnTree? (types type) owner ((seed type).bindFresh owner "x" initializerType)
        (returned "x") = some (tailCore, type) ∧ core 1 = .letE initializerCore tailCore := by
  have original := seedElab false ["x"] type (by decide) (by decide)
  exact ⟨(competing.result_unique original).1, competing.hasType.type_unique original.hasType,
    elaborateTypedLetReturnTree?_inferred_children original.complete⟩

theorem nominal_inference_does_not_supply_an_inhabitant (nominal : Core.DataTypeId) :
    elaborateTypedLetReturnTree? (types (.namedData nominal)) owner (seed (.namedData nominal))
      (chain false ["x", "y"] "seed") = some (core 2, .namedData nominal) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(seedElab false ["x", "y"] _ (by decide) (by decide)).complete, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem existing_cells_and_closures_are_opaque_actual_values
    (location : Core.Location) (word : Core.Word) (store : Core.Store) (k : List Core.Frame) :
    Core.ValueHasType (.cellRef .word location) (.cell .word) ∧
    Core.ValueHasType (.closure .bool .word (.var 1) [.word word]) (.function .bool .word) ∧
    Core.Steps 7 ⟨.eval (core 2) [.cellRef .word location], k, store⟩ ⟨.ret (.cellRef .word location), k, store⟩ ∧
    evaluateTypedLetReturnTreeWithCost? owner table (env (.closure .bool .word (.var 1) [.word word]))
      (chain false ["x", "y"] "seed") = some (.closure .bool .word (.var 1) [.word word], 7) :=
  ⟨.cellRef, .closure (.cons .word .nil) (.var rfl), path 2 _ [] store k,
    evaluateTypedLetReturnTreeWithCost?_complete (cost false ["x", "y"] _ store)⟩

private def sparse : LocalTypeInputs := ⟨[⟨"x", id 7, .word⟩, ⟨"y", ⟨other, 99⟩, .bool⟩, ⟨"x", id 2, .word⟩], by decide⟩
private def actual (left right : Core.Word) (choice : Bool) : LocalInputs :=
  ⟨[⟨"x", id 7, .word, .word left, .word⟩, ⟨"y", ⟨other, 99⟩, .bool, .bool choice, .bool⟩,
    ⟨"x", id 2, .word, .word right, .word⟩], by change [id 7, ⟨other, 99⟩, id 2].Nodup; decide⟩
private def pair : Syntax.Expr := ⟨span, .tuple ⟨span, [ref "x", ref "y"]⟩⟩
private def strict := bind "unused" none pair (returned "x")
private def strictCore : Core.Expr := .letE (.pair (.var 0) (.var 1)) (.var 1)
private theorem strictElab : TypedLetReturnTreeElaborates [] owner sparse strict strictCore .word :=
  .inferred (by decide) (.pair (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.pair (.var .head) (.var (.tail (by decide) .head))) (.pair (.var .head) (.var (.tail (by decide) .head)))
    (.single (.expression (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head))))
private theorem strictCost (left right : Core.Word) (choice : Bool) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (actual left right choice).names (actual left right choice).environment
      store strict (.word left) store 8 := by
  have x : LocalExpressionEvaluatesWithCost (actual left right choice).names (actual left right choice).environment store (ref "x") (.word left) store 1 := .identifier .head .head
  have y : LocalExpressionEvaluatesWithCost (actual left right choice).names (actual left right choice).environment store (ref "y") (.bool choice) store 1 :=
    .identifier (.tail (by change "x" ≠ "y"; decide) .head) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head)
  refine TypedLetReturnTreeEvaluatesWithCost.inferred (name := ⟨span, "unused"⟩)
    (blockSpan := span) (letSpan := span) (initializer := pair) (initializerCost := 5) (tailCost := 1)
    (rest := (returned "x").value) (.pair x y) ?_
  exact .single (.expression (.identifier (.tail (by change "unused" ≠ "x"; decide) .head)
    (.tail (by change id 8 ≠ id 7; decide) .head)))
private def checkpoint (left right : Core.Word) (choice : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.pair (.word left) (.bool choice)), [.letBody (.var 1) [.word left, .bool choice, .word right]], store⟩

theorem sparse_original_inputs_keep_order_and_strict_unused_cost
    (left right : Core.Word) (choice : Bool) (store : Core.Store) (fuel : Nat) :
    Resolved.freshLocalId owner sparse.ids = id 8 ∧ ¬ (sparse.names.map Prod.fst).Nodup ∧
    elaborateTypedLetReturnTree? [] owner sparse strict = some (strictCore, .word) ∧
    TypedLetReturnTreeEvaluatesWithCost owner sparse.names (actual left right choice).environment store strict (.word left) store 8 ∧
    (Core.runStateful fuel (Core.State.initial strictCore [.word left, .bool choice, .word right] store) = .done (.word left) store ↔ 8 ≤ fuel) :=
  ⟨rfl, by decide, strictElab.complete, strictCost left right choice store,
    (strictCost left right choice store).checked_runStateful_done_iff strictElab.complete rfl⟩

theorem same_typed_shortcut_is_not_exact_source_core :
    Core.HasType [.word, .bool, .word] (.var 0) .word ∧
    ¬ TypedLetReturnTreeElaborates [] owner sparse strict (.var 0) .word ∧
    typedLetReturnTreeFuelBound strict = 8 := by
  refine ⟨.var rfl, ?_, by simp [strict, bind, pair, returned, ref, typedLetReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]⟩
  intro wrong
  cases (wrong.result_unique strictElab).1

theorem genuine_initializer_checkpoint_retains_the_original_environment
    (left right : Core.Word) (choice : Bool) (store : Core.Store) (additional : Nat) :
    (actual left right choice).runTypedLetReturnTree? [] owner 6 strict store = some (.word, .outOfFuel (checkpoint left right choice store)) ∧
    Core.Steps 2 (checkpoint left right choice store) (Core.State.final (.word left) store) ∧
    (actual left right choice).runTypedLetReturnTree? [] owner (6 + additional) strict store =
      some (.word, Core.runStateful additional (checkpoint left right choice store)) ∧
    Core.runStateful 0 ⟨(checkpoint left right choice store).control, [], store⟩ = .done (.pair (.word left) (.bool choice)) store := by
  have exhausted : (actual left right choice).runTypedLetReturnTree? [] owner 6 strict store =
      some (.word, .outOfFuel (checkpoint left right choice store)) :=
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨strictCore, strictElab.complete, rfl⟩
  exact ⟨exhausted, ((strictCost left right choice store).checked_residual_of_outOfFuel
    (spent := 6) (checkpoint := checkpoint left right choice store) strictElab.complete rfl rfl).2,
    LocalInputs.runTypedLetReturnTree?_resume exhausted additional, rfl⟩

theorem owner_results_and_own_store_observations_are_separate
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (left right : Core.Word) (choice : Bool) (store replacement : Core.Store) (fuel : Nat) :
    ((actual left right choice).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).runTypedLetReturnTree?
      [] (mapping owner) fuel strict store = (actual left right choice).runTypedLetReturnTree? [] owner fuel strict store ∧
    TypedLetReturnTreeEvaluatesWithCost owner sparse.names (actual left right choice).environment replacement strict (.word left) replacement 8 :=
  ⟨LocalInputs.runTypedLetReturnTree?_mapOwner _ mapping injective [] owner fuel strict store,
    (strictCost left right choice store).change_store replacement⟩

theorem raw_lookup_transport_does_not_require_checked_identity_alignment
    (rightOwner : Resolved.DeclarationId) (rightTable : LocalNameTable) (rightEnvironment : Resolved.Environment)
    (left right : Core.Word) (choice : Bool)
    (agreement : ∀ name, (sparse.names.lookup? name).bind (actual left right choice).environment.lookup? =
      (rightTable.lookup? name).bind rightEnvironment.lookup?) :
    evaluateTypedLetReturnTreeWithCost? rightOwner rightTable rightEnvironment strict = some (.word left, 8) := by
  rw [← evaluateTypedLetReturnTreeWithCost?_congr_lookup owner rightOwner sparse.names rightTable _ rightEnvironment agreement strict]
  exact evaluateTypedLetReturnTreeWithCost?_complete (strictCost left right choice [])

theorem inferred_annotations_are_absent_while_written_annotations_still_mean_something (type : Core.Ty) :
    elaborateTypedLetReturnTree? [] owner (seed type) (bind "x" none (ref "seed") (returned "x")) = some (core 1, type) ∧
    elaborateTypedLetReturnBody? [] owner (seed type) (bind "x" none (ref "seed") (returned "x")) = none ∧
    elaborateTypedLetReturnTree? [] owner (seed type) (bind "x" (some annotation) (ref "seed") (returned "x")) = none := by
  have original : TypedLetReturnTreeElaborates [] owner (seed type) (bind "x" none (ref "seed") (returned "x")) (core 1) type :=
    .inferred (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))
  have unused : "x" ∉ (seed type).names.map Prod.fst := by change "x" ∉ ["seed"]; decide
  have missing : interpretStructuralType? [] annotation = none := by simp only [annotation, interpretStructuralType?_named_eq_typeName]; rfl
  exact ⟨original.complete, by simp [bind, returned, elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?],
    by simp only [bind, elaborateTypedLetReturnTree?, if_pos unused, missing]; rfl⟩

private def bad := bind "unused" (some annotation) (ref "x") (returned "x")
private def skipped : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "y") strict (some bad)⟩]⟩
theorem unselected_invalid_annotation_stays_whole_rejected (left right : Core.Word) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner sparse.names (actual left right true).environment store skipped (.word left) store 11 ∧
    elaborateTypedLetReturnTree? [] owner sparse skipped = none := by
  have raw : TypedLetReturnTreeEvaluatesWithCost owner sparse.names (actual left right true).environment store skipped (.word left) store 11 :=
    TypedLetReturnTreeEvaluatesWithCost.ifTrue
    (show LocalExpressionEvaluatesWithCost sparse.names (actual left right true).environment store (ref "y") (.bool true) store 1 from
      .identifier (.tail (by decide) .head) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head)) (strictCost left right true store)
  refine ⟨raw, elaborateTypedLetReturnTree?_eq_none_iff.mpr ?_⟩
  rintro ⟨_, typed⟩
  cases typed with
  | single child => cases child
  | conditional _ _ invalid =>
      cases invalid with
      | single child => cases child
      | binding meaning _ _ _ =>
          have impossible := meaning.complete
          simp only [annotation, interpretStructuralType?_named_eq_typeName] at impossible
          cases impossible

theorem initializer_and_lexical_scope_failures_are_not_inferred_away
    (value : Core.Value) (store finalStore : Core.Store) :
    elaborateTypedLetReturnTree? [] owner sparse (bind "z" none (ref "z") (returned "x")) = none ∧
    elaborateTypedLetReturnTree? [] owner sparse
      (bind "z" none (ref "later") (bind "later" none (ref "x") (returned "later"))) = none ∧
    elaborateTypedLetReturnTree? [] owner sparse (bind "x" none (ref "y") (returned "x")) = none ∧
    elaborateTypedLetReturnTree? [] owner sparse
      ⟨span, ⟨span, .letDecl ⟨span, "z"⟩ none none⟩ :: (returned "x").value⟩ = none ∧
    ¬ TypedLetReturnTreeEvaluates owner sparse.names [] store (bind "z" none (ref "z") (returned "x")) value finalStore := by
  have missing (name : String) (absent : name ∉ sparse.names.map Prod.fst) :
      elaborateLocalExpression? sparse.names sparse.context (ref name) = none := by
    have lookup := LocalNameTable.lookup?_eq_none_iff.mpr absent
    simp [elaborateLocalExpression?, resolveLocalExpression?, ref, lookup]
  have noZ := missing "z" (by decide)
  have noLater := missing "later" (by decide)
  have names : sparse.names.map Prod.fst = ["x", "y", "x"] := rfl
  refine ⟨by simp [bind, elaborateTypedLetReturnTree?, names, noZ],
    by simp [bind, elaborateTypedLetReturnTree?, names, noLater],
    by simp [bind, elaborateTypedLetReturnTree?, names], by simp only [elaborateTypedLetReturnTree?], ?_⟩
  intro evaluation
  cases evaluation with
  | single child => cases child
  | inferred initializer _ =>
      cases initializer with
      | identifier named _ =>
          have impossible := LocalNameTable.lookup?_iff.mpr named
          change none = some _ at impossible
          cases impossible

end Tests.FrontendInferredLet
end

section
-- leanmerge: from Solcore.Test.FrontendManyExpressionProperties
/-! Flat original lists of n+2 references, not generated nested source syntax.
Independent relations and manual Core paths fix products and costs before checking. -/
set_option autoImplicit false
namespace Tests.FrontendManyExpression
open Solcore Solcore.Frontend
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s,.identifier ⟨s,name⟩⟩
private def tuple (s t : Syntax.SourceSpan) (children : List Syntax.Expr) : Syntax.Expr := ⟨s,.tuple ⟨t,children⟩⟩
private def source (s t : Syntax.SourceSpan) (name : String) (n : Nat) := tuple s t (List.replicate (n+2) (ref s name))
private def resolved (id : Resolved.LocalId) : Nat → Resolved.Expr
  | 0 => .pair (.var id) (.var id)
  | n+1 => .pair (.var id) (resolved id n)
private def core : Nat → Core.Expr
  | 0 => .pair (.var 0) (.var 0)
  | n+1 => .pair (.var 0) (core n)
private def product (type : Core.Ty) : Nat → Core.Ty
  | 0 => .product type type
  | n+1 => .product type (product type n)
private def value (actual : Core.Value) : Nat → Core.Value
  | 0 => .pair actual actual
  | n+1 => .pair actual (value actual n)
private theorem static (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId)
    (table : LocalNameTable) (context : Resolved.Context) (type : Core.Ty) (n : Nat) :
    ResolvesLocalExpression ((name,id)::table) (source s t name n) (resolved id n) ∧
    LocalExpressionHasType ((name,id)::table) ((id,type)::context) (source s t name n) (product type n) ∧
    Resolved.Lowers (id::context.ids) (resolved id n) (core n) ∧
    Resolved.HasType ((id,type)::context) (resolved id n) (product type n) := by
  induction n with
  | zero => exact ⟨.pair (.identifier .head) (.identifier .head),
      .pair (.identifier .head .head) (.identifier .head .head), .pair (.var .head) (.var .head), .pair (.var .head) (.var .head)⟩
  | succ n ih => exact ⟨.many (.identifier .head) ih.1, .many (.identifier .head .head) ih.2.1,
      .pair (.var .head) ih.2.2.1, .pair (.var .head) ih.2.2.2⟩
private theorem checked (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId)
    (table : LocalNameTable) (context : Resolved.Context) (type : Core.Ty) (n : Nat) :
    elaborateLocalExpression? ((name,id)::table) ((id,type)::context) (source s t name n) = some (core n,product type n) :=
  let evidence := static s t name id table context type n
  elaborateLocalExpression?_complete evidence.1 evidence.2.2.1 evidence.2.2.2
private theorem costed (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId)
    (table : LocalNameTable) (env : Resolved.Environment) (actual : Core.Value) (store : Core.Store) (n : Nat) :
    LocalExpressionEvaluatesWithCost ((name,id)::table) ((id,actual)::env) store
      (source s t name n) (value actual n) store (4*n+5) := by
  induction n with
  | zero =>
      apply LocalExpressionEvaluatesWithCost.pair (leftCost := 1) (rightCost := 1) <;> exact .identifier .head .head
  | succ n ih =>
      have count : 4*(n+1)+5 = 1+(4*n+5)+3 := by omega
      rw [count]; exact .many (.identifier .head .head) ih
private theorem bound (s t : Syntax.SourceSpan) (name : String) (n : Nat) :
    localExpressionFuelBound (source s t name n) = 4*n+5 := by
  induction n with
  | zero => simp [source,tuple,ref,localExpressionFuelBound]
  | succ n ih =>
      change localExpressionFuelBound (tuple s t (ref s name :: ref s name :: ref s name :: List.replicate n (ref s name))) = _
      rw [tuple,localExpressionFuelBound]
      rw [show localExpressionFuelBound (ref s name) = 1 from by simp only [ref,localExpressionFuelBound]]
      change 1 + localExpressionFuelBound (source s t name n) + 3 = _
      rw [ih]; omega
private theorem path (actual : Core.Value) (env : Core.Environment) (store : Core.Store) (n : Nat) :
    ∀ k, Core.Steps (4*n+5) ⟨.eval (core n) (actual::env),k,store⟩ ⟨.ret (value actual n),k,store⟩ := by
  induction n with
  | zero => intro k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl))))
  | succ n ih =>
      intro k
      have steps := Core.Steps.cons .enterPair (.cons (.var (index := 0) rfl) (.cons .enterPairRight
        ((ih (.pairApply actual::k)).trans (.cons .applyPair .refl))))
      simpa [core,value,Nat.mul_add,Nat.add_assoc] using steps

theorem old_empty_and_binary_shapes_keep_their_distinct_costs
    (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (actual : Core.Value)
    (table : LocalNameTable) (context : Resolved.Context) (env : Resolved.Environment) (store : Core.Store) :
    elaborateLocalExpression? table context (tuple s t []) = some (.unit,.unit) ∧
    evaluateLocalExpressionWithCost? table env (tuple s t []) = some (.unit,1) ∧
    evaluateLocalExpressionWithCost? ((name,id)::table) ((id,actual)::env) (source s t name 0) = some (.pair actual actual,5) :=
  ⟨elaborateLocalExpression?_complete .unit .unit .unit,evaluateLocalExpressionWithCost?_complete (LocalExpressionEvaluatesWithCost.unit (store := store)),
    evaluateLocalExpressionWithCost?_complete (costed s t name id table env actual store 0)⟩

theorem arbitrary_n_plus_two_original_elements_have_independent_static_provenance
    (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (table : LocalNameTable)
    (context : Resolved.Context) (type : Core.Ty) (n : Nat) :
    source s t name n = tuple s t (List.replicate (n+2) (ref s name)) ∧
    ResolvesLocalExpression ((name,id)::table) (source s t name n) (resolved id n) ∧
    LocalExpressionHasType ((name,id)::table) ((id,type)::context) (source s t name n) (product type n) ∧
    elaborateLocalExpression? ((name,id)::table) ((id,type)::context) (source s t name n) = some (core n,product type n) ∧
    localExpressionFuelBound (source s t name n) = 4*n+5 :=
  ⟨rfl,(static s t name id table context type n).1,(static s t name id table context type n).2.1,
    checked s t name id table context type n,bound s t name n⟩

theorem actual_values_and_both_store_endpoints_keep_the_independently_counted_cost
    (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (table : LocalNameTable)
    (env : Resolved.Environment) (actual : Core.Value) (initial final replacement : Core.Store) (n : Nat) :
    evaluateLocalExpressionWithCost? ((name,id)::table) ((id,actual)::env) (source s t name n) = some (value actual n,4*n+5) ∧
    LocalExpressionEvaluatesWithCost ((name,id)::table) ((id,actual)::env) replacement (source s t name n) (value actual n) replacement (4*n+5) ∧
    (LocalExpressionEvaluatesWithCost ((name,id)::table) ((id,actual)::env) initial (source s t name n) (value actual n) final (4*n+5) ↔ final = initial) := by
  have raw := costed s t name id table env actual initial n
  have direct := evaluateLocalExpressionWithCost?_complete raw
  refine ⟨direct,raw.change_store replacement,?_⟩
  rw [localExpressionEvaluatesWithCost_iff_evaluate,direct]; simp

theorem original_scopes_and_manual_paths_determine_all_closed_fuel_thresholds
    (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (actual : Core.Value)
    (store : Core.Store) (n fuel : Nat) (k : List Core.Frame) :
    Core.Steps (4*n+5) ⟨.eval (core n) [actual],k,store⟩ ⟨.ret (value actual n),k,store⟩ ∧
    (Core.runStateful fuel (.initial (core n) [actual] store) = .done (value actual n) store ↔ 4*n+5 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (.initial (core n) [actual] store) = .outOfFuel checkpoint) ↔ fuel < 4*n+5) := by
  have raw := costed s t name id [] [] actual store n
  have direct := evaluateLocalExpressionWithCost?_complete raw
  have accepted := checked s t name id [] [] .word n
  have _ := raw.cost_le_fuelBound
  have _ := raw.checked_toSteps accepted rfl
  exact ⟨path actual [] store n k,
    evaluateLocalExpressionWithCost?_checked_runStateful_done_iff direct accepted rfl,
    evaluateLocalExpressionWithCost?_checked_runStateful_outOfFuel_iff direct accepted rfl⟩

theorem arbitrary_data_environments_do_not_require_a_nominal_actual
    (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (nominal : Core.DataTypeId)
    (definitions : Core.DataEnvironment) (n : Nat) :
    elaborateLocalExpression? [(name,id)] [(id,.namedData nominal)] (source s t name n) = some (core n,product (.namedData nominal) n) ∧
    Core.HasType [.namedData nominal] (core n) (product (.namedData nominal) n) definitions ∧
    (¬ ∃ actual, Core.ValueHasType actual (.namedData nominal)) := by
  refine ⟨checked s t name id [] [] _ n,?_,?_⟩
  · induction n with
    | zero => exact .pair (.var rfl) (.var rfl)
    | succ n ih => exact .pair (.var rfl) ih
  · rintro ⟨actual,typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?,Core.DataEnvironment.lookupDataType?] at found

private def inputs (name : String) (id : Resolved.LocalId) (actual : TypedRuntimeArgument) : LocalInputs :=
  ⟨[⟨name,id,actual.type,actual.value,actual.valueTyped⟩],by simp⟩
theorem typed_actuals_keep_owner_covariance_and_unused_input_observations
    (s t : Syntax.SourceSpan) (name extra : String) (different : extra ≠ name) (id : Resolved.LocalId)
    (actual : TypedRuntimeArgument) (owner : Resolved.DeclarationId) (store : Core.Store) (n fuel : Nat)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    let original := inputs name id actual
    original.run? (4*n+5) (source s t name n) store = some (product actual.type n,.done (value actual.value n) store) ∧
    (original.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).run? fuel (source s t name n) store = original.run? fuel (source s t name n) store ∧
    ((original.bindFresh owner extra .unit .unit .unit).run? fuel (source s t name n) store = some (product actual.type n,.done (value actual.value n) store) ↔
      original.run? fuel (source s t name n) store = some (product actual.type n,.done (value actual.value n) store)) := by
  dsimp
  have avoids : AvoidsLocalName extra (source s t name n) := by
    induction n with
    | zero => exact .pair (.identifier different) (.identifier different)
    | succ n ih => exact .many (.identifier different) ih
  exact ⟨LocalInputs.run?_done_iff_evaluator.mpr ⟨(static s t name id [] [] actual.type n).2.1,rfl,4*n+5,
    evaluateLocalExpressionWithCost?_complete (costed s t name id [] [] actual.value store n),Nat.le_refl _⟩,
    LocalInputs.run?_mapIds _ _ _ _ _ _,avoids.bindFresh_run_done_at_fuel_iff _ owner .unit .unit .unit⟩

theorem duplicate_rows_and_equal_optional_lookups_preserve_raw_many_results
    (s t : Syntax.SourceSpan) (name : String) (id : Resolved.LocalId) (actual hidden : Core.Value) (n : Nat)
    (rightTable : LocalNameTable) (rightEnv : Resolved.Environment)
    (same : ∀ key, (LocalNameTable.lookup? [(name,id),(name,id)] key).bind
      (Resolved.LocalScope.lookup? [(id,actual),(id,hidden)]) = (rightTable.lookup? key).bind rightEnv.lookup?) :
    evaluateLocalExpressionWithCost? rightTable rightEnv (source s t name n) = some (value actual n,4*n+5) :=
  (evaluateLocalExpressionWithCost?_congr_lookup _ _ _ _ same _).symm.trans
    (evaluateLocalExpressionWithCost?_complete (costed s t name id [(name,id)] [(id,hidden)] actual [] n))

private def s : Syntax.SourceSpan := ⟨⟨.main,"many.sol"⟩,237,2⟩
private def t : Syntax.SourceSpan := ⟨⟨.main,"different.sol"⟩,91,3⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Many",by decide⟩],by decide⟩⟩,7⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def atom := ref s
private def table : LocalNameTable := [("x",id 0),("y",id 1),("z",id 2),("c",id 3)]
private def env (x y z : Core.Value) (flag : Bool) : Resolved.Environment := [(id 0,x),(id 1,y),(id 2,z),(id 3,.bool flag)]
private def three := tuple s t [atom "x",atom "y",atom "z"]
private def threeCore : Core.Expr := .pair (.var 0) (.pair (.var 1) (.var 2))
private def context (type : Core.Ty) : Resolved.Context := [(id 0,type),(id 1,type),(id 2,type),(id 3,.bool)]
private theorem threeCost (x y z : Core.Value) (flag : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (env x y z flag) store three (.pair x (.pair y z)) store 9 := by
  apply LocalExpressionEvaluatesWithCost.many (headCost := 1) (tailCost := 5)
  · exact .identifier .head .head
  · apply LocalExpressionEvaluatesWithCost.pair (leftCost := 1) (rightCost := 1)
    · exact .identifier (.tail (by decide) .head) (.tail (by decide) .head)
    · exact .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
private theorem threeChecked (type : Core.Ty) :
    elaborateLocalExpression? table (context type) three = some (threeCore,.product type (.product type type)) :=
  elaborateLocalExpression?_complete (.many (.identifier .head) (.pair
    (.identifier (.tail (by decide) .head)) (.identifier (.tail (by decide) (.tail (by decide) .head)))))
    (.pair (.var .head) (.pair (.var (.tail (by change id 0 ≠ id 1; decide) .head))
      (.var (.tail (by change id 0 ≠ id 2; decide) (.tail (by change id 1 ≠ id 2; decide) .head)))))
    (.pair (.var .head) (.pair (.var (.tail (by change id 0 ≠ id 1; decide) .head))
      (.var (.tail (by change id 0 ≠ id 2; decide) (.tail (by change id 1 ≠ id 2; decide) .head)))))

theorem original_order_and_explicit_association_are_not_coerced (x y z : Core.Value) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env x y z true) three = some (.pair x (.pair y z),9) ∧
    evaluateLocalExpressionWithCost? table (env x y z true) (tuple s t [tuple s t [atom "x",atom "y"],atom "z"]) = some (.pair (.pair x y) z,9) ∧
    Core.HasType [.word,.word,.word,.bool] (.pair (.var 2) (.pair (.var 1) (.var 0))) (.product .word (.product .word .word)) ∧
    elaborateLocalExpression? table (context .word) three ≠ some (.pair (.var 2) (.pair (.var 1) (.var 0)),.product .word (.product .word .word)) := by
  refine ⟨evaluateLocalExpressionWithCost?_complete (threeCost x y z true store),?_,.pair (.var rfl) (.pair (.var rfl) (.var rfl)),?_⟩
  · apply evaluateLocalExpressionWithCost?_complete (initialStore := store) (finalStore := store)
    apply LocalExpressionEvaluatesWithCost.pair (leftCost := 5) (rightCost := 1)
    · apply LocalExpressionEvaluatesWithCost.pair (leftCost := 1) (rightCost := 1)
      · exact .identifier .head .head
      · exact .identifier (.tail (by decide) .head) (.tail (by decide) .head)
    · exact .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
  · rw [threeChecked]; intro wrong; cases wrong

private def binary (op : Syntax.BinaryOp) (left right : Syntax.Expr) : Syntax.Expr := ⟨s,.binary left ⟨t,op⟩ right⟩
private def choose (yes no : Syntax.Expr) : Syntax.Expr := ⟨s,.conditional (atom "c") s yes t no⟩
private theorem guard (x y z : Core.Value) (flag : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost table (env x y z flag) store (atom "c") (.bool flag) store 1 :=
  .identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
theorem selected_raw_many_values_do_not_weaken_whole_boolean_or_branch_checks
    (x y z : Core.Value) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env x y z true) (binary .logicalAnd (atom "c") three) = some (.pair x (.pair y z),12) ∧
    evaluateLocalExpressionWithCost? table (env x y z false) (binary .logicalOr (atom "c") three) = some (.pair x (.pair y z),12) ∧
    elaborateLocalExpression? table (context .word) (binary .logicalAnd (atom "c") three) = none ∧
    evaluateLocalExpressionWithCost? table (env x y z true) (choose three (atom "missing")) = some (.pair x (.pair y z),12) ∧
    resolveLocalExpression? table (choose three (atom "missing")) = none := by
  refine ⟨evaluateLocalExpressionWithCost?_complete (.andTrue (guard x y z true store) (threeCost x y z true store)),
    evaluateLocalExpressionWithCost?_complete (.orFalse (guard x y z false store) (threeCost x y z false store)),?_,
    evaluateLocalExpressionWithCost?_complete (.ifTrue (guard x y z true store) (threeCost x y z true store)),?_⟩
  · apply elaborateLocalExpression?_eq_none_iff.mpr
    rintro ⟨type,typing⟩
    cases typing with
    | logicalAnd _ rightTyped => cases rightTyped
  · simp [resolveLocalExpression?,choose,three,tuple,atom,ref,table,LocalNameTable.lookup?]

theorem missing_tail_elements_are_strict_even_when_the_head_has_a_value (x y z : Core.Value) (store : Core.Store) :
    evaluateLocalExpressionWithCost? table (env x y z true) (tuple s t [atom "x",atom "y",atom "missing"]) = none ∧
    ¬ ∃ result cost, LocalExpressionEvaluatesWithCost table (env x y z true) store
      (tuple s t [atom "x",atom "missing",atom "z"]) result store cost := by
  constructor
  · simp [evaluateLocalExpressionWithCost?,tuple,atom,ref,table,env,LocalNameTable.lookup?,Resolved.LocalScope.lookup?]
  · apply (evaluateLocalExpressionWithCost?_eq_none_iff store).mp
    simp [evaluateLocalExpressionWithCost?,tuple,atom,ref,table,env,LocalNameTable.lookup?,Resolved.LocalScope.lookup?]

theorem two_pending_pairs_are_genuine_checkpoints_with_exact_residuals
    (x y z : Core.Value) (store : Core.Store) (additional : Nat) :
    Core.runStateful 7 (.initial threeCore [x,y,z,.bool true] store) = .outOfFuel ⟨.ret z,[.pairApply y,.pairApply x],store⟩ ∧
    Core.Steps 2 ⟨.ret z,[.pairApply y,.pairApply x],store⟩ (.final (.pair x (.pair y z)) store) ∧
    Core.runStateful additional ⟨.ret z,[.pairApply y,.pairApply x],store⟩ = Core.runStateful (7+additional) (.initial threeCore [x,y,z,.bool true] store) ∧
    Core.runStateful 0 ⟨.ret z,[],store⟩ = .done z store ∧
    Core.runStateful 0 ⟨.ret z,[.pairApply y,.pairApply x],store⟩ = .outOfFuel ⟨.ret z,[.pairApply y,.pairApply x],store⟩ := by
  have exhausted : Core.runStateful 7 (.initial threeCore [x,y,z,.bool true] store) = .outOfFuel ⟨.ret z,[.pairApply y,.pairApply x],store⟩ := rfl
  exact ⟨exhausted,((threeCost x y z true store).checked_residual_of_outOfFuel (threeChecked .word) rfl exhausted).2,
    Core.runStateful_resume exhausted additional,rfl,rfl⟩

theorem typed_opaque_components_and_grouping_keep_products_without_new_store_claims
    (location : Core.Location) (captured : Core.Word) (store : Core.Store) :
    let actual : TypedRuntimeArgument := ⟨.product (.cell .word) (.function .word .word),
      .pair (.cellRef .word location) (.closure .word .word (.var 1) [.word captured]),.pair .cellRef (.closure (.cons .word .nil) (.var rfl))⟩
    (inputs "x" (id 0) actual).run? 9 (source s t "x" 1) store = some (product actual.type 1,.done (value actual.value 1) store) ∧
    evaluateLocalExpressionWithCost? [("x",id 0)] [(id 0,actual.value)] ⟨t,.group (source s t "x" 1)⟩ = some (value actual.value 1,9) := by
  dsimp
  exact ⟨LocalInputs.run?_done_iff_evaluator.mpr ⟨(static s t "x" (id 0) [] [] _ 1).2.1,rfl,9,
    evaluateLocalExpressionWithCost?_complete (costed s t "x" (id 0) [] [] _ store 1),by decide⟩,
    evaluateLocalExpressionWithCost?_complete (.group (costed s t "x" (id 0) [] [] _ store 1))⟩
end Tests.FrontendManyExpression
end

section
-- leanmerge: from Solcore.Test.FrontendManyTypeProperties
/-! Original finite type lists have an independent source-order meaning.
The final written type is not followed by an implicit Unit, and explicit
nested products remain distinct. Static meanings do not create runtime values. -/
set_option autoImplicit false
namespace Tests.FrontendManyType
open Solcore Solcore.Frontend

private def folded : List Core.Ty → Core.Ty
  | [] => .unit
  | [type] => type
  | type :: next :: rest => .product type (folded (next :: rest))
private def tuple (span : Syntax.SourceSpan) (elements : List Syntax.TypeExpr) : Syntax.TypeExpr :=
  ⟨span, .tuple elements⟩
private def named (span : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private inductive ChildMeanings (table : TypeNameTable) : List Syntax.TypeExpr → List Core.Ty → Prop where
  | nil : ChildMeanings table [] []
  | cons {child : Syntax.TypeExpr} {type : Core.Ty} {rest : List Syntax.TypeExpr} {types : List Core.Ty}
      (head : StructuralTypeDenotes table child type) (tail : ChildMeanings table rest types) :
      ChildMeanings table (child :: rest) (type :: types)
private theorem listMeaning {table : TypeNameTable} {elements : List Syntax.TypeExpr} {types : List Core.Ty}
    (children : ChildMeanings table elements types) (span : Syntax.SourceSpan) :
    StructuralTypeDenotes table (tuple span elements) (folded types) := by
  induction children with
  | nil => exact .unit
  | @cons first firstType rest restTypes head tail ih =>
      cases tail with
      | nil => exact .single head
      | @cons second secondType remaining remainingTypes secondMeaning others =>
          cases others with
          | nil => exact .pair head secondMeaning
          | cons thirdMeaning final => exact .many head ih

private theorem everyChild {table : TypeNameTable} {source : Syntax.TypeExpr} {type : Core.Ty}
    (meaning : StructuralTypeDenotes table source type) :
    ∀ span elements, source = tuple span elements →
      ∀ child ∈ elements, ∃ childType, StructuralTypeDenotes table child childType := by
  induction meaning with
  | named found => intro span elements same; cases same
  | unit => intro span elements same child member; cases same; cases member
  | single meaning _ =>
      intro span elements same child member
      cases same
      simp only [List.mem_singleton] at member
      subst child
      exact ⟨_, meaning⟩
  | pair left right _ _ =>
      intro span elements same child member
      cases same
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨_, left⟩
      · exact ⟨_, right⟩
  | many head tail _ tailIH =>
      intro span elements same child member
      cases same
      rcases List.mem_cons.mp member with rfl | remaining
      · exact ⟨_, head⟩
      · exact tailIH _ _ rfl child remaining
  | functionDefault _ _ => intro span elements same; cases same
  | functionReturns _ _ _ _ => intro span elements same; cases same

theorem arbitrary_finite_lists_have_independent_right_associated_meaning
    (table : TypeNameTable) (span : Syntax.SourceSpan) (elements : List Syntax.TypeExpr) (types : List Core.Ty)
    (children : ChildMeanings table elements types) :
    StructuralTypeDenotes table (tuple span elements) (folded types) ∧
    interpretStructuralType? table (tuple span elements) = some (folded types) ∧
    elements.length = types.length ∧ (tuple span elements).value = .tuple elements := by
  have lengths : elements.length = types.length := by
    induction children with
    | nil => rfl
    | cons _ _ ih => exact congrArg Nat.succ ih
  exact ⟨listMeaning children span, (listMeaning children span).complete, lengths, rfl⟩

theorem three_original_children_use_many_without_an_extra_terminal_unit
    (table : TypeNameTable) (span : Syntax.SourceSpan) (a b c : Syntax.TypeExpr) (x y z : Core.Ty)
    (first : StructuralTypeDenotes table a x) (second : StructuralTypeDenotes table b y)
    (third : StructuralTypeDenotes table c z) :
    StructuralTypeDenotes table (tuple span [a,b,c]) (.product x (.product y z)) ∧
    interpretStructuralType? table (tuple span [a,b,c]) = some (.product x (.product y z)) ∧
    interpretTypeName? table (tuple span [a,b,c]) = none := by
  have meaning : StructuralTypeDenotes table (tuple span [a,b,c]) (.product x (.product y z)) :=
    .many first (.pair second third)
  exact ⟨meaning, interpretStructuralType?_iff.mpr meaning, rfl⟩

theorem one_missing_original_child_rejects_every_prefix_and_suffix
    (table : TypeNameTable) (span : Syntax.SourceSpan) (before after : List Syntax.TypeExpr) (missing : Syntax.TypeExpr)
    (absent : ¬ ∃ type, StructuralTypeDenotes table missing type) :
    interpretStructuralType? table (tuple span (before ++ missing :: after)) = none ∧
    ¬ ∃ type, StructuralTypeDenotes table (tuple span (before ++ missing :: after)) type := by
  have rejected : ¬ ∃ type, StructuralTypeDenotes table (tuple span (before ++ missing :: after)) type := by
    rintro ⟨type, meaning⟩
    exact absent (everyChild meaning span _ rfl missing (by simp))
  exact ⟨interpretStructuralType?_eq_none_iff.mpr rejected, rejected⟩

private def table : TypeNameTable := [(["A"], .word), (["B"], .bool), (["C"], .unit)]
private theorem three (s : Syntax.SourceSpan) : StructuralTypeDenotes table
    (tuple s [named s "A", named s "B", named s "C"]) (.product .word (.product .bool .unit)) :=
  .many (.named .head) (.pair (.named (.tail (by change ["A"] ≠ ["B"]; decide) .head))
    (.named (.tail (by change ["A"] ≠ ["C"]; decide) (.tail (by change ["B"] ≠ ["C"]; decide) .head))))

theorem explicit_nested_association_is_not_flattened_or_completed_with_unit (span : Syntax.SourceSpan) :
    interpretStructuralType? table (tuple span [named span "A",named span "B",named span "C"]) =
      some (.product .word (.product .bool .unit)) ∧
    interpretStructuralType? table (tuple span [tuple span [named span "A",named span "B"],named span "C"]) =
      some (.product (.product .word .bool) .unit) ∧
    (.product .word (.product .bool .unit) : Core.Ty) ≠ .product (.product .word .bool) .unit ∧
    (.product .word (.product .bool .unit) : Core.Ty) ≠ .product .word (.product .bool (.product .unit .unit)) := by
  have nested : StructuralTypeDenotes table
      (tuple span [tuple span [named span "A",named span "B"],named span "C"]) (.product (.product .word .bool) .unit) :=
    .pair (.pair (.named .head) (.named (.tail (by change ["A"] ≠ ["B"]; decide) .head)))
      (.named (.tail (by change ["A"] ≠ ["C"]; decide) (.tail (by change ["B"] ≠ ["C"]; decide) .head)))
  exact ⟨(three span).complete, nested.complete, by decide, by decide⟩

theorem meaningful_children_do_not_allow_a_wrong_result_for_the_same_flat_source (span : Syntax.SourceSpan) :
    ¬ StructuralTypeDenotes table (tuple span [named span "A",named span "B",named span "C"])
      (.product (.product .word .bool) .unit) := by
  intro wrong
  cases wrong.type_unique (three span)

private def qualified (s : Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s, .named ⟨s, ⟨⟨⟨s,"Pkg"⟩,[⟨s,"A"⟩]⟩⟩⟩ none⟩
private def aliases (x y hidden : Core.Ty) : TypeNameTable :=
  [(["A"],x), (["Pkg","A"],y), (["A"],hidden), (["Pkg.A"],.unit)]
private theorem aliasMeaning (span : Syntax.SourceSpan) (x y hidden : Core.Ty) :
    StructuralTypeDenotes (aliases x y hidden) (tuple span [named span "A",qualified span,named span "A"])
      (.product x (.product y x)) :=
  .many (.named .head) (.pair (.named (.tail (by change ["A"] ≠ ["Pkg","A"]; decide) .head)) (.named .head))

theorem every_original_leaf_uses_the_same_first_match_table_and_qualified_components
    (span : Syntax.SourceSpan) (x y hidden : Core.Ty) :
    interpretStructuralType? (aliases x y hidden) (tuple span [named span "A",qualified span,named span "A"]) =
      some (.product x (.product y x)) ∧
    (aliases x y hidden).lookup? ["A"] = some x ∧
    (aliases x y hidden).lookup? ["Pkg","A"] = some y ∧
    (aliases x y hidden).lookup? ["Pkg.A"] = some .unit :=
  ⟨(aliasMeaning span x y hidden).complete, rfl, rfl, rfl⟩

theorem arbitrary_ranges_and_lookup_equality_preserve_the_full_optional_result
    (left right : TypeNameTable) (same : ∀ key, left.lookup? key = right.lookup? key)
    (original replacement : Syntax.SourceSpan) (a b c : Syntax.TypeExpr) (rest : List Syntax.TypeExpr) :
    interpretStructuralType? left (tuple replacement (a :: b :: c :: rest)) =
      interpretStructuralType? right (tuple original (a :: b :: c :: rest)) ∧
    (tuple replacement (a :: b :: c :: rest)).value = (tuple original (a :: b :: c :: rest)).value := by
  exact ⟨(interpretStructuralType?_span left (tuple original (a :: b :: c :: rest)) replacement).trans
    (interpretStructuralType?_congr_lookup left right same _), rfl⟩

theorem successful_extension_and_mutual_full_options_keep_right_association
    (old next : TypeNameTable) (extension : TypeNameTable.Extends old next) (span : Syntax.SourceSpan)
    (elements : List Syntax.TypeExpr) (types : List Core.Ty)
    (children : ChildMeanings old elements types) :
    StructuralTypeDenotes next (tuple span elements) (folded types) ∧
    interpretStructuralType? next (tuple span elements) = some (folded types) ∧
    (TypeNameTable.Extends next old → ∀ source,
      interpretStructuralType? old source = interpretStructuralType? next source) :=
  ⟨(listMeaning children span).extend_types extension,
    interpretStructuralType?_some_of_extends extension (listMeaning children span).complete,
    fun back source => interpretStructuralType?_eq_of_mutual_extends extension back source⟩

theorem one_way_extension_can_repair_an_original_middle_leaf (span : Syntax.SourceSpan) (type : Core.Ty) :
    TypeNameTable.Extends [] [(["N"],type)] ∧
    interpretStructuralType? [] (tuple span [tuple span [],named span "N",tuple span []]) = none ∧
    interpretStructuralType? [(["N"],type)] (tuple span [tuple span [],named span "N",tuple span []]) =
      some (.product .unit (.product type .unit)) := by
  have absent : ¬ ∃ type, StructuralTypeDenotes [] (named span "N") type := by
    rintro ⟨type, meaning⟩
    cases meaning with | named found => cases found
  have repaired : StructuralTypeDenotes [(["N"],type)]
      (tuple span [tuple span [],named span "N",tuple span []]) (.product .unit (.product type .unit)) :=
    .many .unit (.pair (.named .head) .unit)
  exact ⟨TypeNameTable.Extends.append_right [] _,
    (one_missing_original_child_rejects_every_prefix_and_suffix [] span [tuple span []] [tuple span []] _ absent).1,
    repaired.complete⟩

theorem empty_table_products_need_no_whole_result_membership (span : Syntax.SourceSpan) :
    interpretStructuralType? [] (tuple span [tuple span [],tuple span [],tuple span []]) =
      some (.product .unit (.product .unit .unit)) ∧
    (¬ ∃ key, (key, Core.Ty.product .unit (.product .unit .unit)) ∈ ([] : TypeNameTable)) ∧
    interpretTypeName? [] (tuple span [tuple span [],tuple span [],tuple span []]) = none := by
  have meaning : StructuralTypeDenotes [] (tuple span [tuple span [],tuple span [],tuple span []])
      (.product .unit (.product .unit .unit)) := .many .unit (.pair .unit .unit)
  exact ⟨meaning.complete, by simp, rfl⟩

private theorem repeatedMeaning (nominal : Core.DataTypeId) (span : Syntax.SourceSpan) (n : Nat) :
    ChildMeanings [(["N"], .namedData nominal)]
      (List.replicate n (named span "N")) (List.replicate n (.namedData nominal)) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons (.named .head) ih
private theorem repeatedUninhabited (nominal : Core.DataTypeId) (n : Nat) :
    ¬ ∃ value, Core.ValueHasType value (folded (List.replicate (n + 1) (.namedData nominal))) := by
  induction n with
  | zero =>
      rintro ⟨value, typed⟩
      cases typed with
      | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  | succ n ih => rintro ⟨value, typed⟩; cases typed with | pair _ right => exact ih ⟨_,right⟩

theorem arbitrarily_long_nominal_types_remain_static_without_runtime_inhabitants
    (nominal : Core.DataTypeId) (span : Syntax.SourceSpan) (n : Nat) (definitions : Core.DataEnvironment) :
    StructuralTypeDenotes [(["N"], .namedData nominal)] (tuple span (List.replicate (n + 1) (named span "N")))
      (folded (List.replicate (n + 1) (.namedData nominal))) ∧
    Core.HasType [folded (List.replicate (n + 1) (.namedData nominal))] (.var 0)
      (folded (List.replicate (n + 1) (.namedData nominal))) definitions ∧
    ¬ ∃ value, Core.ValueHasType value (folded (List.replicate (n + 1) (.namedData nominal))) :=
  ⟨listMeaning (repeatedMeaning nominal span (n + 1)) span, .var rfl, repeatedUninhabited nominal n⟩

end Tests.FrontendManyType
end

section
-- leanmerge: from Solcore.Test.FrontendParsedBinaryTupleEntries
/-! Complete declarations use named aliases and one structural return annotation,
not multiple returns. Raw source and fixed Core certificates are separate. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace BinaryTupleEntries
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TupleEntry", by decide⟩], by decide⟩⟩, 17⟩
private def pairType : Core.Ty := .product .word .bool
private def nestedType : Core.Ty := .product pairType .word
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Pair"], pairType),
  (["Nested"], nestedType), (["Cell"], .cell .word), (["Fn"], .function .word .word),
  (["OpaquePair"], .product (.cell .word) (.function .word .word)),
  (["Nominal"], .namedData ⟨91⟩), (["NominalPair"], .product (.namedData ⟨91⟩) .bool)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "tuple-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "unexpected lexing diagnostic"
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide (source.span.source = file.id ∧
    source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) && source.span.contains source.value.body.span)
    "original declaration range or completion changed"
  return source
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .group inner⟩ =>
      let child ← expression table env store inner
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .group child.costed⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← expression table env store left
      let second ← expression table env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | _ => throw (IO.userError "expression outside independent tuple script")
termination_by sizeOf source
private structure Body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store source value store cost
private def body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) : IO (Body table env store source) := do
  match sourceAt : source with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let first ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let second ← body ((name.value, id) :: table) ((id, first.value) :: env) store ⟨span, rest⟩
      return ⟨second.value, first.cost + second.cost + 2, by rw [sourceAt]; exact .binding first.costed second.costed⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← body table env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← body table env store no
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent guard not Boolean")
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | _ => throw (IO.userError "body outside independent tuple script")
termination_by sizeOf source
private structure Path (env : Core.Environment) (store : Core.Store) (core : Core.Expr) where
  value : Core.Value
  cost : Nat
  steps : ∀ k, Core.Steps cost ⟨.eval core env, k, store⟩ ⟨.ret value, k, store⟩
private def path (env : Core.Environment) (store : Core.Store) (core : Core.Expr) : IO (Path env store core) := do
  match coreAt : core with
  | .var index =>
      match found : env[index]? with
      | none => throw (IO.userError "independent Core position missing")
      | some value => return ⟨value, 1, by intro k; rw [coreAt]; exact .cons (.var found) .refl⟩
  | .pair left right =>
      let first ← path env store left
      let second ← path env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        intro k; rw [coreAt]
        have steps := Core.Steps.cons .enterPair ((first.steps (.pairRight right env :: k)).trans
          (.cons .enterPairRight ((second.steps (.pairApply first.value :: k)).trans (.cons .applyPair .refl))))
        simpa only [Nat.add_assoc] using steps⟩
  | .letE initializer tail =>
      let first ← path env store initializer
      let second ← path (first.value :: env) store tail
      return ⟨second.value, first.cost + second.cost + 2, by
        intro k; rw [coreAt]
        have steps := Core.Steps.cons .enterLet ((first.steps _).trans (.cons .bindLet (second.steps k)))
        simpa only [Nat.add_assoc] using steps⟩
  | .ifE condition yes no =>
      let guard ← path env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← path env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by
            intro k; rw [coreAt]
            have before := guard.steps (.ifBranches yes no env :: k)
            rw [selected] at before
            have steps := Core.Steps.cons .enterIf (before.trans (.cons .chooseTrue (child.steps k)))
            simpa only [Nat.add_assoc] using steps⟩
      | .bool false =>
          let child ← path env store no
          return ⟨child.value, guard.cost + child.cost + 2, by
            intro k; rw [coreAt]
            have before := guard.steps (.ifBranches yes no env :: k)
            rw [selected] at before
            have steps := Core.Steps.cons .enterIf (before.trans (.cons .chooseFalse (child.steps k)))
            simpa only [Nat.add_assoc] using steps⟩
      | _ => throw (IO.userError "independent Core guard not Boolean")
  | _ => throw (IO.userError "Core outside fixed tuple script")
termination_by sizeOf core
private def check (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Syntax.FunctionDecl := do
  let source ← parsed content
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError "tuple entry did not compile")
  let names ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name annotation := parameter.value | throw (IO.userError "original parameter shape changed")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains annotation.span)
      "original parameter range changed"
    pure name.value
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
    compiled.inputs.context.values = (arguments.map (·.type)).reverse ∧ compiled.inputs.bindings.length = arguments.length))
    "fixed ordered Core/type or original parameter-only layout changed"
  match preparedAt : prepareRuntimeFunction? types owner source arguments with
  | none => throw (IO.userError "tuple arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "tuple flattened arguments or leaked local bindings into parameter records"
      for store in stores do
        let raw ← body prepared.inputs.names prepared.inputs.environment store source.value.body
        let fixed ← path (arguments.reverse.map (·.value)) store core
        assertTrue (decide (raw.value = value ∧ raw.cost = cost ∧ fixed.value = value ∧ fixed.cost = cost))
          "separate source/Core certificates disagreed with independent fixture"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation raw.costed
        have direct := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, direct⟩
        have _ := independent.cost_le_fuelBound
        have _ := (fixed.steps []).runStateful_done_iff (fuel := cost)
        assertTrue (decide (evaluateRuntimeFunctionWithCost? types owner source arguments = some (type, value, cost))) "entry triple changed"
        let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
        let start := Core.State.initial core (arguments.reverse.map (·.value)) store
        for fuel in List.range (cost + 3) do
          have _ := independent.run_done_iff (fuel := fuel)
          have _ := independent.run_outOfFuel_iff (fuel := fuel)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel start))) "entry changed fixed Core or full checkpoint"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "entry threshold, ordered value or own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "entry residual path changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "actual remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart pretended to resume"
          | _ => throw (IO.userError "below-cost entry checkpoint missing")
  return source
private def rejected (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid tuple gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid tuple gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid tuple gate exposed a checkpoint"
end BinaryTupleEntries
open BinaryTupleEntries

def frontendParsedBinaryTupleEntryTests : IO Unit := do
  for n in [2, 9, Core.wordModulus - 1] do
    for choice in [false, true] do
      let arguments := [wordArg n, boolArg choice]
      let value := Core.Value.pair (w n) (.bool choice)
      let simple ← check "function pair(x: Word,c: Bool) returns(Pair){return (x,c);}" arguments
        (.pair (.var 1) (.var 0)) pairType value 5
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner simple arguments 2 store = some (pairType,
          .outOfFuel ⟨.ret (w n), [.pairRight (.var 0) [.bool choice, w n]], store⟩)))
          "entry pair checkpoint lost source parameter positions or actual saved environment"
      for wrong in [[], [wordArg n], [boolArg choice, wordArg n], [wordArg n, boolArg choice, wordArg 0]] do rejected simple wrong
      let _ ← check "function grouped(x: Word,c: Bool) returns(Pair){return (((x,),c,));}" arguments
        (.pair (.var 1) (.var 0)) pairType value 5
      let _ ← check "function tupleType(x: Word,c: Bool) returns((Word,Bool)){return (x,c);}" arguments
        (.pair (.var 1) (.var 0)) pairType value 5
      let _ ← check "function nested(x: Word,c: Bool) returns(Nested){return ((x,c),x);}" arguments
        (.pair (.pair (.var 1) (.var 0)) (.var 1)) nestedType (.pair value (w n)) 9
      let bound ← check "function bound(x: Word,c: Bool) returns(Nested){let p: Pair=(x,c);return (p,x);}" arguments
        (.letE (.pair (.var 1) (.var 0)) (.pair (.var 0) (.var 2))) nestedType (.pair value (w n)) 12
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner bound arguments 6 store = some (nestedType,
          .outOfFuel ⟨.ret value, [.letBody (.pair (.var 0) (.var 2)) [.bool choice, w n]], store⟩) ∧
          runRuntimeFunction? types owner bound arguments 7 store = some (nestedType,
          .outOfFuel ⟨.eval (.pair (.var 0) (.var 2)) [value, .bool choice, w n], [], store⟩)))
          "tuple initializer bound the tail early or changed the actual local product"
      let _ ← check "function branches(x: Word,c: Bool) returns(Pair){if(c){let p: Pair=(x,c);return p;}else{return (x,c);}}" arguments
        (.ifE (.var 0) (.letE (.pair (.var 1) (.var 0)) (.var 0)) (.pair (.var 1) (.var 0))) pairType value (if choice then 11 else 8)
      let pairArgument : TypedRuntimeArgument := ⟨pairType, value, .pair .word .bool⟩
      let _ ← check "function reuse(p: Pair) returns(Pair){return p;}" [pairArgument] (.var 0) pairType value 1
      for declaration in ["function wrong(x: Word,c: Bool) returns(Bool){return (x,c);}",
          "function unknown(x: Word,c: Bool) returns(Unknown){return (x,c);}",
          "function many(x: Word,c: Bool) returns(Word,Bool){return (x,c);}",
          "function unused(x: Word,c: Bool) returns(Pair){if(c){return (x,c);}else{return (missing,c);}}"] do
        let source ← parsed declaration
        let some actual := bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments
          | throw (IO.userError "raw gate contrast lost original actual arguments")
        if choice || !declaration.startsWith "function unused" then
          for store in stores do
            let raw ← body actual.names actual.environment store source.value.body
            assertTrue (decide (raw.value = value ∧ raw.cost = if declaration.startsWith "function unused" then 8 else 5))
              "whole rejection lost independently successful raw tuple"
        rejected source arguments
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 999, .cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩
  let _ ← check "function opaque(x: Cell,f: Fn) returns(OpaquePair){return (x,f);}" [cell, closure]
    (.pair (.var 1) (.var 0)) (.product cell.type closure.type) (.pair cell.value closure.value) 5
  let nominal ← parsed "function nominal(x: Nominal,c: Bool) returns(NominalPair){return (x,c);}"
  assertTrue (decide ((compileRuntimeFunction? types owner nominal).map (fun c => (c.core, c.returnType)) =
    some (.pair (.var 1) (.var 0), .product (.namedData ⟨91⟩) .bool))) "nominal product static compilation required an inhabitant"
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨_, typed⟩; cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  rejected nominal [wordArg 9, boolArg true]
  for operand in ["()", "(x,c,x)", "[x,c]", "(x,c).first", "(x,c)[0]"] do
    let source ← parsed ("function unsupported(x: Word,c: Bool) returns(Pair){return " ++ operand ++ ";}")
    rejected source [wordArg 9, boolArg true]

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedBinaryTuples
/-! Original parsed binary tuples with independently constructed source evidence
and Core transition paths. Static types never manufacture or constrain raw values. -/
set_option autoImplicit false
namespace Tests
namespace BinaryTuples
open Solcore Solcore.Frontend
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"BinaryTuple", by decide⟩], by decide⟩⟩, 17⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def table : LocalNameTable := [("l", id 7), ("r", id 2), ("c", id 99)]
private def context (a b : Core.Ty) : Resolved.Context := [(id 7, a), (id 2, b), (id 99, .bool)]
private def env (a b : Core.Value) (c : Bool) : Resolved.Environment := [(id 7, a), (id 2, b), (id 99, .bool c)]
private def stores : List Core.Store := [[], [w 40, .cellRef .word 999, .bool false]]
private def file (content : String) : Syntax.SourceFile := ⟨⟨.main, "binary-tuples.sol"⟩, content⟩
private def parsed (content : String) : IO Syntax.Expr := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "lexer diagnostics"
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial (file content) lexed)
    | throw (IO.userError "complete expression did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide
    (source.span = ⟨(file content).id, 0, content.utf8ByteSize⟩)) "original complete byte range changed"
  return source
private structure Certificate (ctx : Resolved.Context) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  resolution : ResolvesLocalExpression table source resolved
  lowered : Resolved.Lowers ctx.ids resolved core
  typing : LocalExpressionHasType table ctx source type
  raw : LocalExpressionEvaluatesWithCost table environment store source value store cost
  paths : ∀ continuation, Core.Steps cost ⟨.eval core environment.values, continuation, store⟩
    ⟨.ret value, continuation, store⟩
private def certify (ctx : Resolved.Context) (environment : Resolved.Environment)
    (aligned : environment.ids = ctx.ids) (store : Core.Store) (source : Syntax.Expr) :
    IO (Certificate ctx environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      let some identity := table.lookup? name.value | throw (IO.userError "certificate spelling missing")
      match named : table.lookup? name.value, typed : ctx.lookup? identity,
          found : environment.lookup? identity, indexed : Resolved.LocalScope.index? ctx.ids identity with
      | some actualId, some type, some value, some index =>
          if same : actualId = identity then
            let namedProof := LocalNameTable.lookup?_iff.mp (same ▸ named)
            let indexProof := Resolved.LocalScope.index?_iff.mp indexed
            return ⟨.var identity, .var index, type, value, 1,
              by rw [sourceAt]; exact .identifier namedProof, .var indexProof,
              by rw [sourceAt]; exact .identifier namedProof (Resolved.LocalScope.lookup?_iff.mp typed),
              by rw [sourceAt]; exact .identifier namedProof (Resolved.LocalScope.lookup?_iff.mp found),
              fun _ => .cons (.var ((Resolved.LocalScope.lookup_iff_getElem?
                (aligned.symm ▸ indexProof)).mp (Resolved.LocalScope.lookup?_iff.mp found))) .refl⟩
          else throw (IO.userError "certificate name changed")
      | _, _, _, _ => throw (IO.userError "certificate row missing")
  | ⟨_, .group inner⟩ =>
      let child ← certify ctx environment aligned store inner
      return { child with resolution := by rw [sourceAt]; exact .group child.resolution
                          typing := by rw [sourceAt]; exact .group child.typing
                          raw := by rw [sourceAt]; exact .group child.raw }
  | ⟨_, .tuple ⟨_, []⟩⟩ =>
      return ⟨.unit, .unit, .unit, .unit, 1,
        by rw [sourceAt]; exact .unit, .unit,
        by rw [sourceAt]; exact .unit, by rw [sourceAt]; exact .unit,
        fun _ => .cons .unit .refl⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← certify ctx environment aligned store left; let b ← certify ctx environment aligned store right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        .pair a.value b.value, a.cost + b.cost + 3,
        by rw [sourceAt]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered,
        by rw [sourceAt]; exact .pair a.typing b.typing,
        by rw [sourceAt]; exact .pair a.raw b.raw, fun continuation => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core environment.values :: continuation)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ =>
      let a ← certify ctx environment aligned store first
      let b ← certify ctx environment aligned store ⟨span,.tuple ⟨tupleSpan,second :: third :: rest⟩⟩
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type, .pair a.value b.value, a.cost + b.cost + 3,
        by rw [sourceAt]; exact .many a.resolution b.resolution, .pair a.lowered b.lowered,
        by rw [sourceAt]; exact .many a.typing b.typing, by rw [sourceAt]; exact .many a.raw b.raw, fun k => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core environment.values :: k)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨_, .conditional guard _ left _ right⟩ =>
      let c ← certify ctx environment aligned store guard
      let a ← certify ctx environment aligned store left; let b ← certify ctx environment aligned store right
      if guardType : c.type = .bool then
        if armType : b.type = a.type then
          let common := fun value cost raw paths =>
            (⟨.ifE c.resolved a.resolved b.resolved, .ifE c.core a.core b.core, a.type, value, cost,
              by rw [sourceAt]; exact .conditional c.resolution a.resolution b.resolution,
              .ifE c.lowered a.lowered b.lowered,
              by rw [sourceAt]; exact .conditional (guardType ▸ c.typing) a.typing (armType ▸ b.typing),
              raw, paths⟩ : Certificate ctx environment store source)
          match guardValue : c.value with
          | .bool true => return (common a.value (c.cost + a.cost + 2)
              (by rw [sourceAt]; exact .ifTrue (guardValue ▸ c.raw) a.raw) (fun continuation => by
                have path := Core.Steps.cons .enterIf ((guardValue ▸ c.paths
                  (.ifBranches a.core b.core environment.values :: continuation)).trans (.cons .chooseTrue (a.paths _)))
                simpa only [Nat.add_assoc] using path))
          | .bool false => return (common b.value (c.cost + b.cost + 2)
              (by rw [sourceAt]; exact .ifFalse (guardValue ▸ c.raw) b.raw) (fun continuation => by
                have path := Core.Steps.cons .enterIf ((guardValue ▸ c.paths
                  (.ifBranches a.core b.core environment.values :: continuation)).trans (.cons .chooseFalse (b.paths _)))
                simpa only [Nat.add_assoc] using path))
          | _ => throw (IO.userError "certificate actual guard not Bool")
        else throw (IO.userError "certificate arm types differ")
      else throw (IO.userError "certificate guard type not Bool")
  | _ => throw (IO.userError "outside independent certificate grammar")
termination_by sizeOf source
private def checked (content : String) (a b : Core.Value) (c : Bool) (aType bType : Core.Ty)
    (expectedCore : Core.Expr) (expectedType : Core.Ty) (expectedValue : Core.Value) (expectedCost : Nat) : IO Unit := do
  let source ← parsed content
  for store in stores do
    let certificate ← certify (context aType bType) (env a b c) rfl store source
    assertTrue (decide (certificate.core = expectedCore ∧ certificate.type = expectedType ∧
      certificate.value = expectedValue ∧ certificate.cost = expectedCost)) "independent source certificate differs"
    let accepted := elaborateLocalExpression?_complete certificate.resolution certificate.lowered
      (certificate.resolution.preserves_type certificate.typing)
    let direct := evaluateLocalExpressionWithCost?_complete certificate.raw
    have _ := evaluateLocalExpressionWithCost?_sound direct store
    assertTrue (decide (elaborateLocalExpression? table (context aType bType) source = some (expectedCore, expectedType) ∧
      evaluateLocalExpressionWithCost? table (env a b c) source = some (expectedValue, expectedCost) ∧
      Core.infer? (context aType bType).values expectedCore = some expectedType ∧
      expectedCost ≤ localExpressionFuelBound source)) "fixed lowering/type/value/cost changed"
    for continuation in [[], [.letBody (.var 0) []], [.unaryApply .wordNot]] do
      have _ := certificate.paths continuation
      have _ := certificate.raw.toStepsWithContinuation certificate.resolution certificate.lowered continuation
      have _ := evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation (store := store) direct accepted rfl continuation
      pure ()
    let start := Core.State.initial certificate.core (env a b c).values store
    for fuel in List.range (expectedCost + 3) do
      have _ := evaluateLocalExpressionWithCost?_checked_runStateful_done_iff (store := store) (fuel := fuel) direct accepted rfl
      assertTrue (match Core.runStateful fuel start with
        | .done value finalStore => decide (expectedCost ≤ fuel ∧ value = expectedValue ∧ finalStore = store)
        | .outOfFuel checkpoint => decide (fuel < expectedCost ∧ checkpoint.store = store)
        | _ => false) "independent threshold or own store changed"
    for spent in List.range expectedCost do
      match exhausted : Core.runStateful spent start with
      | .outOfFuel checkpoint =>
          have _ := (certificate.paths []).residual_of_outOfFuel exhausted
          have _ := certificate.raw.checked_residual_of_outOfFuel accepted rfl exhausted
          for additional in List.range (expectedCost - spent + 3) do
            have _ := Core.runStateful_resume exhausted additional
            assertTrue (decide (Core.runStateful additional checkpoint = Core.runStateful (spent + additional) start)) "resumption changed full state"
            assertTrue (match Core.runStateful additional checkpoint with
              | .done value finalStore => decide (expectedCost - spent ≤ additional ∧ value = expectedValue ∧ finalStore = store)
              | .outOfFuel next => decide (additional < expectedCost - spent ∧ next.store = store)
              | _ => false) "independent residual threshold changed"
          if spent > 0 then
            assertTrue (Core.runStateful (expectedCost - spent) start != .done expectedValue store) "restart paid no consumed prefix"
          if expectedCost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 checkpoint | throw (IO.userError "second chunk missing")
            assertTrue (decide (Core.runStateful (expectedCost - spent - 1) next = .done expectedValue store)) "third chunk did not finish"
      | _ => throw (IO.userError "genuine checkpoint absent")
    if expectedValue matches .pair _ _ then
      assertTrue (match Core.runStateful expectedCost ⟨.eval expectedCore (env a b c).values, [.unaryApply .wordNot], store⟩ with
        | .fault _ checkpoint => decide (checkpoint = ⟨.ret expectedValue, [.unaryApply .wordNot], store⟩)
        | _ => false) "arbitrary continuation endpoint was confused with exhaustion"
private def rejected (content : String) (expected : Option (Core.Value × Nat) := none) : IO Unit := do
  let source ← parsed content
  assertTrue ((elaborateLocalExpression? table (context .word .word) source).isNone &&
    decide (evaluateLocalExpressionWithCost? table (env (w 9) (w 2) true) source = expected)) "unsupported boundary changed"
  for store in stores do
    match outcome : evaluateLocalExpressionWithCost? table (env (w 9) (w 2) true) source with
    | none => have _ := (evaluateLocalExpressionWithCost?_eq_none_iff store).mp outcome; pure ()
    | some _ => have _ := evaluateLocalExpressionWithCost?_sound outcome store; pure ()
private def rawLogical (source : Syntax.Expr) (c : Bool) (store : Core.Store) : IO Unit := do
  match sourceAt : source with
  | ⟨span, .binary left ⟨operatorSpan, op⟩ right⟩ =>
      let a ← certify (context .word .word) (env (w 9) (w 2) c) rfl store left
      let b ← certify (context .word .word) (env (w 9) (w 2) c) rfl store right
      match opAt : op, guardValue : a.value with
      | .logicalAnd, .bool true =>
          let evidence := LocalExpressionEvaluatesWithCost.andTrue (span := span) (operatorSpan := operatorSpan) (guardValue ▸ a.raw) b.raw
          have _ : evaluateLocalExpressionWithCost? table (env (w 9) (w 2) c) source = some (b.value, a.cost + b.cost + 2) := by
            simpa only [sourceAt, opAt] using evaluateLocalExpressionWithCost?_complete evidence
          assertTrue (decide (a.cost + b.cost + 2 = 8 ∧ b.value = .pair (w 9) (w 2))) "independent and-forward certificate changed"
      | .logicalOr, .bool false =>
          let evidence := LocalExpressionEvaluatesWithCost.orFalse (span := span) (operatorSpan := operatorSpan) (guardValue ▸ a.raw) b.raw
          have _ : evaluateLocalExpressionWithCost? table (env (w 9) (w 2) c) source = some (b.value, a.cost + b.cost + 2) := by
            simpa only [sourceAt, opAt] using evaluateLocalExpressionWithCost?_complete evidence
          assertTrue (decide (a.cost + b.cost + 2 = 8 ∧ b.value = .pair (w 9) (w 2))) "independent or-forward certificate changed"
      | .logicalAnd, .bool false =>
          have _ := evaluateLocalExpressionWithCost?_complete (LocalExpressionEvaluatesWithCost.andFalse
            (span := span) (operatorSpan := operatorSpan) (right := right) (guardValue ▸ a.raw))
          assertTrue (a.cost + 3 == 4) "independent skipped and cost changed"
      | .logicalOr, .bool true =>
          have _ := evaluateLocalExpressionWithCost?_complete (LocalExpressionEvaluatesWithCost.orTrue
            (span := span) (operatorSpan := operatorSpan) (right := right) (guardValue ▸ a.raw))
          assertTrue (a.cost + 3 == 4) "independent skipped or cost changed"
      | _, _ => throw (IO.userError "logical certificate shape changed")
  | _ => throw (IO.userError "original binary shape changed")
end BinaryTuples
open BinaryTuples Solcore Solcore.Frontend
def frontendParsedBinaryTupleTests : IO Unit := do
  let pair : Core.Expr := .pair (.var 0) (.var 1); let product : Core.Ty := .product .word .word
  for (left, right) in [(w 9, w 2), (.cellRef .word 999, .closure .word .bool (.var 999) [w 12]),
      (.constructed ⟨⟨81⟩, 4⟩ (.pair .unit (w 8)), .unit)] do
    for text in ["(l,r)", "(l, r,)", "((l),(r))", "(((l,r)))"] do
      checked text left right true .word .word pair product (.pair left right) 5
    checked "(l,(r,l))" left right false .word .word (.pair (.var 0) (.pair (.var 1) (.var 0)))
      (.product .word product) (.pair left (.pair right left)) 9
    checked "((l,r),r)" left right false .word .word (.pair pair (.var 1))
      (.product product .word) (.pair (.pair left right) right) 9
    for c in [false, true] do
      checked "c ? (l,r) : (r,l)" left right c .word .word (.ifE (.var 2) pair (.pair (.var 1) (.var 0)))
        product (if c then .pair left right else .pair right left) 8
      checked "c ? (l,r) : (r,(c ? l : r))" left right c .word .word
        (.ifE (.var 2) pair (.pair (.var 1) (.ifE (.var 2) (.var 0) (.var 1))))
        product (if c then .pair left right else .pair right right) (if c then 8 else 11)
  for depth in [0, 1, 3, 6] do
    let content := (List.range depth).foldl (fun inner _ => "(l," ++ inner ++ ")") "r"
    let core := (List.range depth).foldl (fun inner _ => Core.Expr.pair (.var 0) inner) (.var 1)
    let type := (List.range depth).foldl (fun inner _ => Core.Ty.product .word inner) .word
    let value := (List.range depth).foldl (fun inner _ => Core.Value.pair (w 9) inner) (w 2)
    checked content (w 9) (w 2) true .word .word core type value (4 * depth + 1)
  checked "(l,c)" (w 9) (w 2) false .word .word (.pair (.var 0) (.var 2)) (.product .word .bool) (.pair (w 9) (.bool false)) 5
  checked "(c,r)" (w 9) (w 2) true .word .word (.pair (.var 2) (.var 1)) (.product .bool .word) (.pair (.bool true) (w 2)) 5
  for text in ["(l)", "(l,)"] do checked text (w 9) (w 2) true .word .word (.var 0) .word (w 9) 1
  checked "()" (w 9) (w 2) true .word .word .unit .unit .unit 1
  checked "(l,r)" (.cellRef .word 999) (.closure .word .word (.var 0) []) true (.cell .word) (.function .word .word)
    pair (.product (.cell .word) (.function .word .word)) (.pair (.cellRef .word 999) (.closure .word .word (.var 0) [])) 5
  let source ← parsed "(l,r,)"
  assertTrue (match source.value with
    | .tuple ⟨span, [⟨_, .identifier l⟩, ⟨_, .identifier r⟩]⟩ =>
        l.value == "l" && r.value == "r" && decide (span = source.span ∧ l.span.endByte < r.span.startByte)
    | _ => false) "parser changed binary arity, ranges or written order"
  for store in stores do
    let environment := (env (w 9) (w 2) true).values
    assertTrue (decide (Core.runStateful 2 (Core.State.initial pair environment store) = .outOfFuel
      ⟨.ret (w 9), [.pairRight (.var 1) environment], store⟩ ∧
      Core.runStateful 4 (Core.State.initial pair environment store) = .outOfFuel
      ⟨.ret (w 2), [.pairApply (w 9)], store⟩)) "actual ordered pair frames or captured environment changed"
    let duplicateContext : Resolved.Context := [(id 7, .word), (id 7, .bool), (id 2, .word), (id 99, .bool)]
    let duplicateEnvironment : Resolved.Environment := [(id 7, w 9), (id 7, .bool false), (id 2, w 2), (id 99, .bool true)]
    let duplicate ← certify duplicateContext duplicateEnvironment rfl store source
    have _ := evaluateLocalExpressionWithCost?_complete duplicate.raw
    assertTrue (decide (duplicate.core = .pair (.var 0) (.var 2) ∧ duplicate.type = product ∧
      duplicate.value = .pair (w 9) (w 2) ∧ duplicate.cost = 5 ∧
      Core.runStateful 5 (Core.State.initial (.pair (.var 0) (.var 2)) duplicateEnvironment.values store) = .done (.pair (w 9) (w 2)) store))
      "duplicate first-match identity changed ordered values or positions"
  for c in [false, true] do
    for op in [Syntax.BinaryOp.logicalAnd, .logicalOr] do
      let text := if op == .logicalAnd then "c && (l,r)" else "c || (l,r)"
      let expression ← parsed text
      let forwarded := if op == .logicalAnd then c else !c
      let value := if forwarded then Core.Value.pair (w 9) (w 2) else .bool c
      assertTrue (decide (evaluateLocalExpressionWithCost? table (env (w 9) (w 2) c) expression =
        some (value, if forwarded then 8 else 4)) && (elaborateLocalExpression? table (context .word .word) expression).isNone)
        "raw pair forwarding became a whole Bool rule"
      for store in stores do rawLogical expression c store
  checked "(l,r,c)" (w 9) (w 2) true .word .word (.pair (.var 0) (.pair (.var 1) (.var 2)))
    (.product .word (.product .word .bool)) (.pair (w 9) (.pair (w 2) (.bool true))) 9
  checked "(l,r,c,l)" (w 9) (w 2) true .word .word (.pair (.var 0) (.pair (.var 1) (.pair (.var 2) (.var 0))))
    (.product .word (.product .word (.product .bool .word))) (.pair (w 9) (.pair (w 2) (.pair (.bool true) (w 9)))) 13
  for text in ["[l,r]", "(l,r).x", "(l,r)[0]", "(missing,r)", "(l,missing)", "(l,f(r))", "(l,~c)"] do rejected text
  rejected "c ? (l,r) : (l,missing)" (some (.pair (w 9) (w 2), 8))
  rejected "c ? (l,r) : l" (some (.pair (w 9) (w 2), 8))
  let singleton : Syntax.Expr := ⟨source.span, .tuple ⟨source.span, [← parsed "l"]⟩⟩
  assertTrue ((resolveLocalExpression? table singleton).isNone &&
    (evaluateLocalExpressionWithCost? table (env (w 9) (w 2) true) singleton).isNone) "manual singleton tuple acquired grouping meaning"
  let .ok lexed := Syntax.Lexer.lex (file "(Word, Word)") | throw (IO.userError "type lexer invariant")
  let .ok tupleType next := Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file "(Word, Word)") lexed)
    | throw (IO.userError "tuple type did not parse")
  assertTrue (next.atEnd && (interpretTypeName? [(["Word"], .word)] tupleType).isNone) "expression pairs enabled tuple type syntax"
  match sourceAt : source with
  | ⟨_, .tuple ⟨_, [⟨_, .identifier left⟩, ⟨_, .identifier right⟩]⟩⟩ =>
      if leftAt : left.value = "l" then
        if rightAt : right.value = "r" then
          let nominal : Core.Ty := .namedData ⟨83⟩
          have typing : LocalExpressionHasType table (context nominal .unit) source (.product nominal .unit) := by
            rw [sourceAt]
            exact .pair (.identifier (by rw [leftAt]; exact .head) .head)
              (.identifier (by rw [rightAt]; exact .tail (by decide) .head) (.tail (by decide) .head))
          have _ := localExpressionHasType_iff_elaborates.mp typing
          have noInhabitant : ∀ nominal : Core.DataTypeId, ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
            intro nominal
            rintro ⟨_, typed⟩
            cases typed with
            | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
          have _ := noInhabitant ⟨83⟩
          assertTrue (decide (elaborateLocalExpression? table (context nominal .unit) source =
            some (pair, .product nominal .unit))) "static nominal pair required actual values"
        else throw (IO.userError "nominal right spelling changed")
      else throw (IO.userError "nominal left spelling changed")
  | _ => throw (IO.userError "nominal original binary tuple changed")
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedInferredLetEntries
/-! Original missing annotations remain missing through checked recursive entries.
Independent annotation/raw-body evidence and fixed Core paths determine all expectations. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace InferredLetEntries
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"InferredLetEntry", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool),
  (["Unit"], .unit), (["Pair"], .product .word .bool), (["Pkg", "Flag"], .bool),
  (["Cell"], .cell .word), (["Fn"], .function .word .word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def unitArg : TypedRuntimeArgument := ⟨.unit,.unit,.unit⟩
private def pairArg (left right : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.product left.type right.type,.pair left.value right.value,.pair left.valueTyped right.valueTyped⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "inferred-let-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "unexpected lexing diagnostic"
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide (source.span.source = file.id ∧
    source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) && source.span.contains source.value.body.span)
    "original declaration range or completion changed"
  return source
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .group inner⟩ =>
      let child ← expression table env store inner
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .group child.costed⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← expression table env store left
      let second ← expression table env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ =>
      let head ← expression table env store first
      let tail ← expression table env store ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩
      return ⟨.pair head.value tail.value, head.cost + tail.cost + 3, by rw [sourceAt]; exact .many head.costed tail.costed⟩
  | ⟨_, .conditional condition _ yes _ no⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← expression table env store yes
          return ⟨child.value,guard.cost + child.cost + 2,by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← expression table env store no
          return ⟨child.value,guard.cost + child.cost + 2,by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent conditional guard not Boolean")
  | _ => throw (IO.userError "expression outside independent tuple script")
termination_by sizeOf source
private structure Body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store source value store cost
private def body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) : IO (Body table env store source) := do
  match sourceAt : source with
  | ⟨span, ⟨_, .letDecl name optionalType (some initializer)⟩ :: rest⟩ =>
      let first ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let second ← body ((name.value, id) :: table) ((id, first.value) :: env) store ⟨span, rest⟩
      return ⟨second.value, first.cost + second.cost + 2, by
        rw [sourceAt]; cases optionalType with
        | none => exact .inferred first.costed second.costed
        | some _ => exact .binding first.costed second.costed⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← body table env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← body table env store no
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent guard not Boolean")
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | _ => throw (IO.userError "body outside independent unit script")
termination_by sizeOf source
private structure Annotation (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes types source type
private def annotation (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Annotation types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | none => throw (IO.userError "independent return leaf missing")
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [atSource]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← annotation types child
      return ⟨inner.type, by rw [atSource]; exact .single inner.meaning⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let first ← annotation types left
      let second ← annotation types right
      return ⟨.product first.type second.type, by rw [atSource]; exact .pair first.meaning second.meaning⟩
  | ⟨span, .tuple (first :: second :: third :: rest)⟩ =>
      let head ← annotation types first
      let tail ← annotation types ⟨span, .tuple (second :: third :: rest)⟩
      return ⟨.product head.type tail.type, by rw [atSource]; exact .many head.meaning tail.meaning⟩
  | _ => throw (IO.userError "return annotation outside independent script")
termination_by sizeOf source
private structure Return (types : TypeNameTable) (clause : Option Syntax.ReturnClause) where
  type : Core.Ty
  meaning : RuntimeReturnTypeDenotes types clause type
private def returns (types : TypeNameTable) (clause : Option Syntax.ReturnClause) : IO (Return types clause) := do
  match atClause : clause with
  | none => return ⟨.unit, by rw [atClause]; exact .absent⟩
  | some ⟨_, ⟨_, [source]⟩⟩ =>
      let child ← annotation types source
      return ⟨child.type, by rw [atClause]; exact .single child.meaning⟩
  | _ => throw (IO.userError "independent return clause is not singleton")
private def bindingTypes (types : TypeNameTable) (source : Syntax.Block) : IO (List (Option Core.Ty)) := do
  match source with
  | ⟨span, ⟨letSpan, .letDecl name optionalType (some initializer)⟩ :: rest⟩ =>
      assertTrue (span.contains letSpan && letSpan.contains name.span && letSpan.contains initializer.span &&
        decide (name.span.endByte ≤ initializer.span.startByte)) "original inferred binding ranges/order changed"
      let written : Option Core.Ty ← match optionalType with
        | none => pure none
        | some sourceType => do
            assertTrue (letSpan.contains sourceType.span) "original written annotation range changed"
            let meaning ← annotation types sourceType
            pure (some meaning.type)
      return written :: (← bindingTypes types ⟨span, rest⟩)
  | ⟨_, [⟨_, .ifThen _ yes (some no)⟩]⟩ =>
      return (← bindingTypes types yes) ++ (← bindingTypes types no)
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => return []
  | _ => throw (IO.userError "original annotated body shape changed")
termination_by sizeOf source
private def check (types : TypeNameTable) (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (steps : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) (written : List (Option Core.Ty)) : IO Syntax.FunctionDecl := do
  let source ← parsed content
  assertTrue (decide ((← bindingTypes types source.value.body) = written)) "independent written let annotation order/types changed"
  let declared ← returns types source.value.signature.returnsClause
  assertTrue (decide (declared.type = type)) "independent structural return type differs from fixture"
  if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
      source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
    have header : RuntimeFunctionHeader types source.value.signature declared.type :=
      ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, declared.meaning⟩
    have _ := interpretRuntimeFunctionHeader?_iff.mpr header
    pure ()
  else throw (IO.userError "independent header policy rejected")
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError ("structural parameter entry did not compile: " ++ content))
  let original ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name sourceType := parameter.value | throw (IO.userError "original parameter shape changed")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains sourceType.span)
      "original parameter range changed"
    let meaning ← annotation types sourceType
    pure (name.value, meaning.type)
  let names := original.map Prod.fst
  assertTrue (decide (original.map Prod.snd = arguments.map (·.type))) "independent original parameter types changed"
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
    compiled.inputs.context.values = (original.map Prod.snd).reverse ∧ compiled.inputs.bindings.length = arguments.length))
    "fixed ordered Core/type or original parameter-only layout changed"
  match preparedAt : prepareRuntimeFunction? types owner source arguments with
  | none => throw (IO.userError "structural arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "adapter flattened arguments or leaked local bindings into parameter records"
      for store in stores do
        let raw ← body prepared.inputs.names prepared.inputs.environment store source.value.body
        assertTrue (decide (raw.value = value ∧ raw.cost = cost))
          "separate source/Core certificates disagreed with independent fixture"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation raw.costed
        have direct := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, direct⟩
        have _ := independent.cost_le_fuelBound
        have _ := (steps store []).runStateful_done_iff (fuel := cost)
        assertTrue (decide (evaluateRuntimeFunctionWithCost? types owner source arguments = some (type, value, cost))) "entry triple changed"
        let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
        let start := Core.State.initial core (arguments.reverse.map (·.value)) store
        for fuel in List.range (cost + 3) do
          have _ := independent.run_done_iff (fuel := fuel)
          have _ := independent.run_outOfFuel_iff (fuel := fuel)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel start))) "entry changed fixed Core or full checkpoint"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "entry threshold, ordered value or own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "entry residual path changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "actual remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart pretended to resume"
          | _ => throw (IO.userError "below-cost entry checkpoint missing")
  return source
private def rejected (types : TypeNameTable) (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid structural parameter gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid structural parameter gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid structural parameter gate exposed a checkpoint"
end InferredLetEntries
open InferredLetEntries
def frontendParsedInferredLetEntryTests : IO Unit := do
  let _ ← check [] "function unit(){let u=();return u;}" [] (.letE .unit (.var 0)) .unit .unit 4
    (by intro store k; exact .cons .enterLet (.cons .unit (.cons .bindLet (.cons (.var rfl) (.refl))))) [none]
  let _ ← check [(["Word"],.bool)] "function alias(x: Word) returns(Word){let z=x;return z;}" [boolArg true]
    (.letE (.var 0) (.var 0)) .bool (.bool true) 4 (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) (.refl))))) [none]
  for n in [0,9,Core.Word.maximum.val] do
    for choice in [false,true] do
      let args := [wordArg n,boolArg choice,wordArg 17]
      let _ ← check types "function mixed(x: Word,c: Bool,y: Word) returns(Word){let a=x;let b: Word=a;let d=b;return d;}"
        args (.letE (.var 2) (.letE (.var 0) (.letE (.var 0) (.var 0)))) .word (w n) 10
        (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) (.refl))))))))))) [none,some .word,none]
      let strict ← check types "function strict(x: Word,c: Bool,y: Word) returns(Word){let p=(x,y);return x;}"
        args (.letE (.pair (.var 2) (.var 0)) (.var 3)) .word (w n) 8
        (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons (.var rfl) (.refl))))))))) [none]
      for store in stores do
        let saved : Core.State := ⟨.ret (.pair (w n) (w 17)),[.letBody (.var 3) [w 17,.bool choice,w n]],store⟩
        assertTrue (decide (runRuntimeFunction? types owner strict args 6 store = some (.word,.outOfFuel saved) ∧
          Core.runStateful 2 saved = .done (w n) store)) "unused initializer or actual residual let work disappeared"
      let _ ← check types "function product(x: Word,c: Bool,y: Word) returns((Word,Bool,Word)){let p=(x,c,y);return p;}"
        args (.letE (.pair (.var 2) (.pair (.var 1) (.var 0))) (.var 0))
        (.product .word (.product .bool .word)) (.pair (w n) (.pair (.bool choice) (w 17))) 12
        (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .applyPair (.cons .bindLet (.cons (.var rfl) (.refl))))))))))))) [none]
      let _ ← check types "function branch(x: Word,c: Bool,y: Word) returns(Word){if(c){let z=x;return z;}else{return y;}}"
        args (.ifE (.var 1) (.letE (.var 2) (.var 0)) (.var 0)) .word (if choice then w n else w 17)
        (if choice then 7 else 4) (by
          intro store k; cases choice
          · exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons (.var rfl) (.refl))))
          · exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) (.refl)))))))) [none]
      for content in ["function bad(x: Word,c: Bool,y: Word) returns(Word){let p=missing;return x;}",
          "function bad(x: Word,c: Bool,y: Word) returns(Word){let p=p;return x;}",
          "function bad(x: Word,c: Bool,y: Word) returns(Word){let x=x;return x;}",
          "function bad(x: Word,c: Bool,y: Word) returns(Word){let p;return x;}",
          "function bad(x: Word,c: Bool,y: Word) returns(Word){let p=(x,missing);return x;}",
          "function bad(x: Word,c: Bool,y: Word) returns(Word){let p: (Word,Bool)=(x,y);return x;}",
          "function bad(x: Word,c: Bool,y: Word) returns(Word){if(c){let p=x;return p;}else{let p=missing;return p;}}"] do
        rejected types (← parsed content) args
  let captured : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w 7],
    .closure (.cons .word .nil) (.var rfl)⟩
  let packedOpaque := pairArg (pairArg ⟨.cell .word,.cellRef .word 999,.cellRef⟩ captured) unitArg
  let _ ← check types "function opaque(p:((Cell,Fn),())) returns(((Cell,Fn),())){let q=p;return q;}"
    [packedOpaque] (.letE (.var 0) (.var 0)) packedOpaque.type packedOpaque.value 4 (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) (.refl))))) [none]
  let nominalTypes : TypeNameTable := [(["N"],.namedData ⟨91⟩)]
  let nominal ← parsed "function nominal(x:N) returns(N){let z=x;return z;}"
  assertTrue (decide ((compileRuntimeFunction? nominalTypes owner nominal).map (fun c => (c.core,c.returnType)) =
    some (.letE (.var 0) (.var 0),.namedData ⟨91⟩))) "nominal static inference required an actual inhabitant"
  rejected nominalTypes nominal [wordArg 9]
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedManyExpressions
/-! Original parsed many-element tuples with independently constructed source evidence
and Core transition paths. Static types never manufacture or constrain raw values. -/
set_option autoImplicit false
namespace Tests
namespace ManyExpressions
open Solcore Solcore.Frontend
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"BinaryTuple", by decide⟩], by decide⟩⟩, 17⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def table : LocalNameTable := [("l", id 7), ("l", id 501), ("r", id 2), ("c", id 99)]
private def context (a b : Core.Ty) : Resolved.Context := [(id 7, a), (id 2, b), (id 99, .bool)]
private def env (a b : Core.Value) (c : Bool) : Resolved.Environment := [(id 7, a), (id 2, b), (id 99, .bool c)]
private def stores : List Core.Store := [[], [w 40, .cellRef .word 999, .bool false]]
private def file (content : String) : Syntax.SourceFile := ⟨⟨.main, "many-expressions.sol"⟩, content⟩
private def parsed (content : String) : IO Syntax.Expr := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "lexer diagnostics"
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial (file content) lexed)
    | throw (IO.userError "complete expression did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide
    (source.span = ⟨(file content).id, 0, content.utf8ByteSize⟩)) s!"original complete byte range changed: {content}"
  return source
private structure Certificate (ctx : Resolved.Context) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  resolution : ResolvesLocalExpression table source resolved
  lowered : Resolved.Lowers ctx.ids resolved core
  typing : LocalExpressionHasType table ctx source type
  raw : LocalExpressionEvaluatesWithCost table environment store source value store cost
  paths : ∀ continuation, Core.Steps cost ⟨.eval core environment.values, continuation, store⟩
    ⟨.ret value, continuation, store⟩
private def certify (ctx : Resolved.Context) (environment : Resolved.Environment)
    (aligned : environment.ids = ctx.ids) (store : Core.Store) (source : Syntax.Expr) :
    IO (Certificate ctx environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      let some identity := table.lookup? name.value | throw (IO.userError "certificate spelling missing")
      match named : table.lookup? name.value, typed : ctx.lookup? identity,
          found : environment.lookup? identity, indexed : Resolved.LocalScope.index? ctx.ids identity with
      | some actualId, some type, some value, some index =>
          if same : actualId = identity then
            let namedProof := LocalNameTable.lookup?_iff.mp (same ▸ named)
            let indexProof := Resolved.LocalScope.index?_iff.mp indexed
            return ⟨.var identity, .var index, type, value, 1,
              by rw [sourceAt]; exact .identifier namedProof, .var indexProof,
              by rw [sourceAt]; exact .identifier namedProof (Resolved.LocalScope.lookup?_iff.mp typed),
              by rw [sourceAt]; exact .identifier namedProof (Resolved.LocalScope.lookup?_iff.mp found),
              fun _ => .cons (.var ((Resolved.LocalScope.lookup_iff_getElem?
                (aligned.symm ▸ indexProof)).mp (Resolved.LocalScope.lookup?_iff.mp found))) .refl⟩
          else throw (IO.userError "certificate name changed")
      | _, _, _, _ => throw (IO.userError "certificate row missing")
  | ⟨_, .group inner⟩ =>
      let child ← certify ctx environment aligned store inner
      return { child with resolution := by rw [sourceAt]; exact .group child.resolution
                          typing := by rw [sourceAt]; exact .group child.typing
                          raw := by rw [sourceAt]; exact .group child.raw }
  | ⟨_, .tuple ⟨_, []⟩⟩ =>
      return ⟨.unit, .unit, .unit, .unit, 1,
        by rw [sourceAt]; exact .unit, .unit,
        by rw [sourceAt]; exact .unit, by rw [sourceAt]; exact .unit,
        fun _ => .cons .unit .refl⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← certify ctx environment aligned store left; let b ← certify ctx environment aligned store right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        .pair a.value b.value, a.cost + b.cost + 3,
        by rw [sourceAt]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered,
        by rw [sourceAt]; exact .pair a.typing b.typing,
        by rw [sourceAt]; exact .pair a.raw b.raw, fun continuation => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core environment.values :: continuation)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ =>
      let a ← certify ctx environment aligned store first
      let b ← certify ctx environment aligned store ⟨span,.tuple ⟨tupleSpan,second :: third :: rest⟩⟩
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type, .pair a.value b.value, a.cost + b.cost + 3,
        by rw [sourceAt]; exact .many a.resolution b.resolution, .pair a.lowered b.lowered,
        by rw [sourceAt]; exact .many a.typing b.typing, by rw [sourceAt]; exact .many a.raw b.raw, fun k => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core environment.values :: k)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← certify ctx environment aligned store left; let b ← certify ctx environment aligned store right
      if aType : a.type = .word then
        if bt : b.type = .word then
          match av : a.value, bv : b.value with
          | .word x, .word y => return ⟨.binary .wordSub a.resolved b.resolved, .binary .wordSub a.core b.core, .word,
              .word (x.sub y), a.cost + b.cost + 3, by rw [sourceAt]; exact .subtract a.resolution b.resolution,
              .binary a.lowered b.lowered, by rw [sourceAt]; exact .subtract (aType ▸ a.typing) (bt ▸ b.typing),
              by rw [sourceAt]; exact .subtract (av ▸ a.raw) (bv ▸ b.raw), fun k => by
                have path := Core.Steps.cons .enterBinary
                  ((av ▸ a.paths (.binaryRight .wordSub b.core environment.values :: k)).trans
                    (.cons .enterBinaryRight ((bv ▸ b.paths _).trans (.cons (.applyBinary rfl) .refl))))
                simpa only [Nat.add_assoc] using path⟩
          | _,_ => throw (IO.userError "actual subtraction operands are not Words")
        else throw (IO.userError "right subtraction type is not Word")
      else throw (IO.userError "left subtraction type is not Word")
  | ⟨_, .conditional guard _ left _ right⟩ =>
      let c ← certify ctx environment aligned store guard
      let a ← certify ctx environment aligned store left; let b ← certify ctx environment aligned store right
      if guardType : c.type = .bool then
        if armType : b.type = a.type then
          let common := fun value cost raw paths =>
            (⟨.ifE c.resolved a.resolved b.resolved, .ifE c.core a.core b.core, a.type, value, cost,
              by rw [sourceAt]; exact .conditional c.resolution a.resolution b.resolution,
              .ifE c.lowered a.lowered b.lowered,
              by rw [sourceAt]; exact .conditional (guardType ▸ c.typing) a.typing (armType ▸ b.typing),
              raw, paths⟩ : Certificate ctx environment store source)
          match guardValue : c.value with
          | .bool true => return (common a.value (c.cost + a.cost + 2)
              (by rw [sourceAt]; exact .ifTrue (guardValue ▸ c.raw) a.raw) (fun continuation => by
                have path := Core.Steps.cons .enterIf ((guardValue ▸ c.paths
                  (.ifBranches a.core b.core environment.values :: continuation)).trans (.cons .chooseTrue (a.paths _)))
                simpa only [Nat.add_assoc] using path))
          | .bool false => return (common b.value (c.cost + b.cost + 2)
              (by rw [sourceAt]; exact .ifFalse (guardValue ▸ c.raw) b.raw) (fun continuation => by
                have path := Core.Steps.cons .enterIf ((guardValue ▸ c.paths
                  (.ifBranches a.core b.core environment.values :: continuation)).trans (.cons .chooseFalse (b.paths _)))
                simpa only [Nat.add_assoc] using path))
          | _ => throw (IO.userError "certificate actual guard not Bool")
        else throw (IO.userError "certificate arm types differ")
      else throw (IO.userError "certificate guard type not Bool")
  | _ => throw (IO.userError "outside independent certificate grammar")
termination_by sizeOf source
private def checked (text : String) (left right : Core.Value) (choice : Bool)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let source ← parsed text
  for store in stores do
    let proof ← certify (context .word .word) (env left right choice) rfl store source
    assertTrue (decide (proof.core = core ∧ proof.type = type ∧ proof.value = value ∧ proof.cost = cost))
      "original source certificate differs from the external fixture"
    have accepted := elaborateLocalExpression?_complete proof.resolution proof.lowered (proof.resolution.preserves_type proof.typing)
    have evaluated := evaluateLocalExpressionWithCost?_complete proof.raw
    assertTrue (decide (resolveLocalExpression? table source = some proof.resolved ∧
      elaborateLocalExpression? table (context .word .word) source = some (core,type) ∧
      evaluateLocalExpressionWithCost? table (env left right choice) source = some (value,cost) ∧
      Core.infer? [.word,.word,.bool] core = some type ∧ cost ≤ localExpressionFuelBound source))
      "exact lowering, static type, raw value or cost changed"
    for k in [[],[.letBody (.var 0) []],[.unaryApply .wordNot]] do
      have _ := proof.paths k
      have _ := proof.raw.toStepsWithContinuation proof.resolution proof.lowered k
      have _ := evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation (store := store) evaluated accepted rfl k
      pure ()
    let start := Core.State.initial proof.core (env left right choice).values store
    for fuel in List.range (cost + 3) do
      have _ := (proof.paths []).runStateful_done_iff (fuel := fuel)
      assertTrue (match Core.runStateful fuel start with
        | .done result final => decide (cost ≤ fuel ∧ result = value ∧ final = store)
        | .outOfFuel saved => decide (fuel < cost ∧ saved.store = store)
        | _ => false) "whole exact fuel or own-store observation changed"
    for spent in List.range cost do
      match exhausted : Core.runStateful spent start with
      | .outOfFuel saved =>
          have _ := (proof.paths []).residual_of_outOfFuel exhausted
          have _ := proof.raw.checked_residual_of_outOfFuel accepted rfl exhausted
          for additional in List.range (cost - spent + 3) do
            have _ := Core.runStateful_resume exhausted additional
            assertTrue (decide (Core.runStateful additional saved = Core.runStateful (spent + additional) start))
              "actual checkpoint replay changed the full result"
            assertTrue (match Core.runStateful additional saved with
              | .done result final => decide (cost - spent ≤ additional ∧ result = value ∧ final = store)
              | .outOfFuel next => decide (additional < cost - spent ∧ next.store = store)
              | _ => false) "independent remaining-cost threshold changed"
          if spent > 0 then assertTrue (Core.runStateful (cost - spent) start != .done value store) "restart discarded consumed work"
          if cost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 saved | throw (IO.userError "second chunk absent")
            assertTrue (decide (Core.runStateful (cost - spent - 1) next = .done value store)) "third chunk failed"
      | _ => throw (IO.userError "genuine partial execution absent")
    assertTrue (match Core.runStateful cost ⟨.eval core (env left right choice).values,[.unaryApply .wordNot],store⟩ with
      | .fault _ endpoint => decide (endpoint = ⟨.ret value,[.unaryApply .wordNot],store⟩)
      | _ => false) "arbitrary continuation endpoint implied unconditional exhaustion"
private def skipped (source : Syntax.Expr) (store : Core.Store) : IO Unit := do
  match original : source with
  | ⟨span,.tuple ⟨tupleSpan,[head,⟨cs,.conditional guard question yes colon no⟩,⟨us,.tuple ⟨uts,[]⟩⟩]⟩⟩ =>
      let a ← certify (context .word .word) (env (w 9) (w 2) true) rfl store head
      let c ← certify (context .word .word) (env (w 9) (w 2) true) rfl store guard
      let b ← certify (context .word .word) (env (w 9) (w 2) true) rfl store yes
      if selected : c.value = .bool true then
        have costed : LocalExpressionEvaluatesWithCost table (env (w 9) (w 2) true) store source
            (.pair a.value (.pair b.value .unit)) store (a.cost + (c.cost + b.cost + 2 + 1 + 3) + 3) := by
          rw [original]
          exact .many (headCost := a.cost) (tailCost := c.cost + b.cost + 2 + 1 + 3) a.raw
            (.pair (leftCost := c.cost + b.cost + 2) (rightCost := 1)
              (.ifTrue (conditionCost := c.cost) (branchCost := b.cost) (selected ▸ c.raw) b.raw) .unit)
        have _ := evaluateLocalExpressionWithCost?_complete costed
        assertTrue (decide (a.value = w 9 ∧ b.value = w 2 ∧ a.cost = 1 ∧ b.cost = 1 ∧ c.cost = 1))
          "selected-only independent component certificate changed"
      else throw (IO.userError "raw chosen condition changed")
  | _ => throw (IO.userError "original flat tuple/conditional shape changed")
end ManyExpressions
open ManyExpressions Solcore Solcore.Frontend
def frontendParsedManyExpressionTests : IO Unit := do
  let triple : Core.Expr := .pair (.var 0) (.pair (.var 1) (.var 2))
  let tripleType : Core.Ty := .product .word (.product .word .bool)
  for (left,right) in [(w 9,w 2),(.cellRef .word 999,.closure .word .word (.var 999) [w 7])] do
    for c in [false,true] do
      for text in ["(l,r,c)","(l,r,c,)","((l),(r),(c))","(((l,r,c)))"] do
        checked text left right c triple tripleType (.pair left (.pair right (.bool c))) 9
      checked "(l,r,c,l)" left right c (.pair (.var 0) (.pair (.var 1) (.pair (.var 2) (.var 0))))
        (.product .word (.product .word (.product .bool .word))) (.pair left (.pair right (.pair (.bool c) left))) 13
      checked "((l,r),c,l)" left right c (.pair (.pair (.var 0) (.var 1)) (.pair (.var 2) (.var 0)))
        (.product (.product .word .word) (.product .bool .word)) (.pair (.pair left right) (.pair (.bool c) left)) 13
      checked "(l,(c ? r : l),())" left right c (.pair (.var 0) (.pair (.ifE (.var 2) (.var 1) (.var 0)) .unit))
        (.product .word (.product .word .unit)) (.pair left (.pair (if c then right else left) .unit)) 12
  for c in [false,true] do
    checked "(l - r,c ? l : r,r)" (w 9) (w 2) c
      (.pair (.binary .wordSub (.var 0) (.var 1)) (.pair (.ifE (.var 2) (.var 0) (.var 1)) (.var 1)))
      (.product .word (.product .word .word)) (.pair (w 7) (.pair (if c then w 9 else w 2) (w 2))) 16
  for length in [3,4,6,9] do
    let text := "(" ++ String.intercalate "," (List.replicate length "l") ++ ")"
    let core := (List.range (length - 1)).foldl (fun inner _ => Core.Expr.pair (.var 0) inner) (.var 0)
    let type := (List.range (length - 1)).foldl (fun inner _ => Core.Ty.product .word inner) .word
    let value := (List.range (length - 1)).foldl (fun inner _ => Core.Value.pair (w 9) inner) (w 9)
    checked text (w 9) (w 2) true core type value (4 * length - 3)
  let source ← parsed "(l,r,c,)"
  assertTrue (match source.value with
    | .tuple ⟨s,[⟨a,.identifier x⟩,⟨b,.identifier y⟩,⟨c,.identifier z⟩]⟩ =>
        decide (s = source.span ∧ (x.value,y.value,z.value) = ("l","r","c") ∧
          (a.startByte,a.endByte,b.startByte,b.endByte,c.startByte,c.endByte) = (1,2,3,4,5,6))
    | _ => false) "flat original arity, written names or byte ranges were rewritten"
  for store in stores do
    let environment := (env (w 9) (w 2) true).values
    assertTrue (decide (Core.runStateful 2 (.initial triple environment store) = .outOfFuel
      ⟨.ret (w 9),[.pairRight (.pair (.var 1) (.var 2)) environment],store⟩ ∧
      Core.runStateful 5 (.initial triple environment store) = .outOfFuel
      ⟨.ret (w 2),[.pairRight (.var 2) environment,.pairApply (w 9)],store⟩ ∧
      Core.runStateful 8 (.initial triple environment store) = .outOfFuel
      ⟨.ret (.pair (w 2) (.bool true)),[.pairApply (w 9)],store⟩)) "actual nested pair frames or saved environment changed"
    let duplicateContext : Resolved.Context := [(id 7,.word),(id 7,.bool),(id 2,.word),(id 99,.bool)]
    let duplicateEnv : Resolved.Environment := [(id 7,w 9),(id 7,.bool false),(id 2,w 2),(id 99,.bool true)]
    let duplicate ← certify duplicateContext duplicateEnv rfl store source
    assertTrue (decide (duplicate.core = .pair (.var 0) (.pair (.var 2) (.var 3)) ∧
      duplicate.value = .pair (w 9) (.pair (w 2) (.bool true)) ∧ duplicate.cost = 9)) "first duplicate ID ceased to determine lookup/index"
    let rawSource ← parsed "(l,c ? r : missing,())"
    skipped rawSource store
    assertTrue ((elaborateLocalExpression? table (context .word .word) rawSource).isNone &&
      decide (evaluateLocalExpressionWithCost? table (env (w 9) (w 2) true) rawSource =
        some (.pair (w 9) (.pair (w 2) .unit),12))) "selected raw component bypassed whole written-arm checking"
  for text in ["(missing,l,r)","(l,missing,r)","(l,r,missing)","(l,r,c,missing)",
      "(l,r,~c)","(l,r,f(l))","(l,r,[c])","(l,r,c).x","(l,r,c)[0]"] do
    let invalid ← parsed text
    assertTrue ((elaborateLocalExpression? table (context .word .word) invalid).isNone &&
      (evaluateLocalExpressionWithCost? table (env (w 9) (w 2) true) invalid).isNone) "strict unsupported written component was skipped"
  let original ← parsed "(l,r,())"
  let unaligned : Resolved.Environment := [(id 2,w 2),(id 7,w 9),(id 99,.bool true)]
  match shape : original with
  | ⟨_,.tuple ⟨_,[⟨_,.identifier ln⟩,⟨_,.identifier rn⟩,⟨_,.tuple ⟨_,[]⟩⟩]⟩⟩ =>
      if l : ln.value = "l" then
        if r : rn.value = "r" then
          for store in stores do
            have raw : LocalExpressionEvaluatesWithCost table unaligned store original (.pair (w 9) (.pair (w 2) .unit)) store 9 := by
              rw [shape]; exact .many (.identifier (by rw [l]; exact .head) (.tail (by decide) .head))
                (.pair (.identifier (by rw [r]; exact .tail (by decide) (.tail (by decide) .head)) .head) .unit)
            have _ := evaluateLocalExpressionWithCost?_complete raw
            assertTrue (decide (unaligned.ids ≠ (context .word .word).ids ∧
              Core.runStateful 9 (.initial (.pair (.var 0) (.pair (.var 1) .unit)) unaligned.values store) =
                .done (.pair (w 2) (.pair (w 9) .unit)) store)) "raw named lookup was confused with unaligned positional Core execution"
        else throw (IO.userError "right original spelling changed")
      else throw (IO.userError "left original spelling changed")
  | _ => throw (IO.userError "original unaligned flat fixture changed")
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedManyTupleEntries
/-! Original flat tuple expressions keep exact ordered values and existing pair steps.
Independent annotation/raw-body evidence and fixed Core paths determine all expectations. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ManyTupleEntries
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ManyTupleEntry", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool),
  (["Unit"], .unit), (["Pair"], .product .word .bool), (["Pkg", "Flag"], .bool),
  (["Cell"], .cell .word), (["Fn"], .function .word .word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def unitArg : TypedRuntimeArgument := ⟨.unit,.unit,.unit⟩
private def pairArg (left right : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.product left.type right.type,.pair left.value right.value,.pair left.valueTyped right.valueTyped⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "many-tuple-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "unexpected lexing diagnostic"
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide (source.span.source = file.id ∧
    source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) && source.span.contains source.value.body.span)
    "original declaration range or completion changed"
  return source
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .group inner⟩ =>
      let child ← expression table env store inner
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .group child.costed⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← expression table env store left
      let second ← expression table env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ =>
      let head ← expression table env store first
      let tail ← expression table env store ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩
      return ⟨.pair head.value tail.value, head.cost + tail.cost + 3, by rw [sourceAt]; exact .many head.costed tail.costed⟩
  | ⟨_, .conditional condition _ yes _ no⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← expression table env store yes
          return ⟨child.value,guard.cost + child.cost + 2,by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← expression table env store no
          return ⟨child.value,guard.cost + child.cost + 2,by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent conditional guard not Boolean")
  | _ => throw (IO.userError "expression outside independent tuple script")
termination_by sizeOf source
private structure Body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store source value store cost
private def body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) : IO (Body table env store source) := do
  match sourceAt : source with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let first ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let second ← body ((name.value, id) :: table) ((id, first.value) :: env) store ⟨span, rest⟩
      return ⟨second.value, first.cost + second.cost + 2, by rw [sourceAt]; exact .binding first.costed second.costed⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← body table env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← body table env store no
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent guard not Boolean")
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | _ => throw (IO.userError "body outside independent unit script")
termination_by sizeOf source
private structure Annotation (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes types source type
private def annotation (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Annotation types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | none => throw (IO.userError "independent return leaf missing")
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [atSource]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← annotation types child
      return ⟨inner.type, by rw [atSource]; exact .single inner.meaning⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let first ← annotation types left
      let second ← annotation types right
      return ⟨.product first.type second.type, by rw [atSource]; exact .pair first.meaning second.meaning⟩
  | ⟨span, .tuple (first :: second :: third :: rest)⟩ =>
      let head ← annotation types first
      let tail ← annotation types ⟨span, .tuple (second :: third :: rest)⟩
      return ⟨.product head.type tail.type, by rw [atSource]; exact .many head.meaning tail.meaning⟩
  | _ => throw (IO.userError "return annotation outside independent script")
termination_by sizeOf source
private structure Return (types : TypeNameTable) (clause : Option Syntax.ReturnClause) where
  type : Core.Ty
  meaning : RuntimeReturnTypeDenotes types clause type
private def returns (types : TypeNameTable) (clause : Option Syntax.ReturnClause) : IO (Return types clause) := do
  match atClause : clause with
  | none => return ⟨.unit, by rw [atClause]; exact .absent⟩
  | some ⟨_, ⟨_, [source]⟩⟩ =>
      let child ← annotation types source
      return ⟨child.type, by rw [atClause]; exact .single child.meaning⟩
  | _ => throw (IO.userError "independent return clause is not singleton")
private def bindingTypes (types : TypeNameTable) (source : Syntax.Block) : IO (List Core.Ty) := do
  match source with
  | ⟨span, ⟨_, .letDecl _ (some sourceType) (some _)⟩ :: rest⟩ =>
      let meaning ← annotation types sourceType
      let tail ← bindingTypes types ⟨span, rest⟩
      return meaning.type :: tail
  | ⟨_, [⟨_, .ifThen _ yes (some no)⟩]⟩ =>
      return (← bindingTypes types yes) ++ (← bindingTypes types no)
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => return []
  | _ => throw (IO.userError "original annotated body shape changed")
termination_by sizeOf source
private def check (types : TypeNameTable) (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (steps : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) (written : List Core.Ty) : IO Syntax.FunctionDecl := do
  let source ← parsed content
  assertTrue (decide ((← bindingTypes types source.value.body) = written)) "independent written let annotation order/types changed"
  let declared ← returns types source.value.signature.returnsClause
  assertTrue (decide (declared.type = type)) "independent structural return type differs from fixture"
  if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
      source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
    have header : RuntimeFunctionHeader types source.value.signature declared.type :=
      ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, declared.meaning⟩
    have _ := interpretRuntimeFunctionHeader?_iff.mpr header
    pure ()
  else throw (IO.userError "independent header policy rejected")
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError ("structural parameter entry did not compile: " ++ content))
  let original ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name sourceType := parameter.value | throw (IO.userError "original parameter shape changed")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains sourceType.span)
      "original parameter range changed"
    let meaning ← annotation types sourceType
    pure (name.value, meaning.type)
  let names := original.map Prod.fst
  assertTrue (decide (original.map Prod.snd = arguments.map (·.type))) "independent original parameter types changed"
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
    compiled.inputs.context.values = (original.map Prod.snd).reverse ∧ compiled.inputs.bindings.length = arguments.length))
    "fixed ordered Core/type or original parameter-only layout changed"
  match preparedAt : prepareRuntimeFunction? types owner source arguments with
  | none => throw (IO.userError "structural arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "adapter flattened arguments or leaked local bindings into parameter records"
      for store in stores do
        let raw ← body prepared.inputs.names prepared.inputs.environment store source.value.body
        assertTrue (decide (raw.value = value ∧ raw.cost = cost))
          "separate source/Core certificates disagreed with independent fixture"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation raw.costed
        have direct := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, direct⟩
        have _ := independent.cost_le_fuelBound
        have _ := (steps store []).runStateful_done_iff (fuel := cost)
        assertTrue (decide (evaluateRuntimeFunctionWithCost? types owner source arguments = some (type, value, cost))) "entry triple changed"
        let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
        let start := Core.State.initial core (arguments.reverse.map (·.value)) store
        for fuel in List.range (cost + 3) do
          have _ := independent.run_done_iff (fuel := fuel)
          have _ := independent.run_outOfFuel_iff (fuel := fuel)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel start))) "entry changed fixed Core or full checkpoint"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "entry threshold, ordered value or own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "entry residual path changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "actual remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart pretended to resume"
          | _ => throw (IO.userError "below-cost entry checkpoint missing")
  return source
private def rejected (types : TypeNameTable) (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid structural parameter gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid structural parameter gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid structural parameter gate exposed a checkpoint"
end ManyTupleEntries
open ManyTupleEntries

def frontendParsedManyTupleEntryTests : IO Unit := do
  let _ ← check [] "function units() returns(((),(),())){return ((),(),());}" []
    (.pair .unit (.pair .unit .unit)) (.product .unit (.product .unit .unit)) (.pair .unit (.pair .unit .unit)) 9
    (by intro store k; exact .cons .enterPair (.cons .unit (.cons .enterPairRight (.cons .enterPair (.cons .unit (.cons .enterPairRight (.cons .unit (.cons .applyPair (.cons .applyPair (.refl)))))))))) []
  let _ ← check [] "function fourUnits() returns(((),(),(),())){return ((),(),(),());}" []
    (.pair .unit (.pair .unit (.pair .unit .unit))) (.product .unit (.product .unit (.product .unit .unit)))
    (.pair .unit (.pair .unit (.pair .unit .unit))) 13 (by intro store k; exact .cons .enterPair (.cons .unit (.cons .enterPairRight (.cons .enterPair (.cons .unit (.cons .enterPairRight (.cons .enterPair (.cons .unit (.cons .enterPairRight (.cons .unit (.cons .applyPair (.cons .applyPair (.cons .applyPair (.refl)))))))))))))) []
  for n in [0,9,Core.wordModulus - 1] do
    for choice in [false,true] do
      let args := [wordArg n,boolArg choice,wordArg 17]
      let type := Core.Ty.product .word (.product .bool .word)
      let value := Core.Value.pair (w n) (.pair (.bool choice) (w 17))
      let core := Core.Expr.pair (.var 2) (.pair (.var 1) (.var 0))
      for written in ["(x,c,y)", "(x,c,y,)", "((x),c,y)"] do
        let source ← check types ("function flat(x: Word,c: Bool,y: Word) returns((Word,Bool,Word)){return " ++ written ++ ";}")
          args core type value 9 (by intro store k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .applyPair (.refl)))))))))) []
        assertTrue (match source.value.body.value with
          | [⟨_,.returnStmt (some ⟨span,.tuple ⟨tupleSpan,[a,b,c]⟩⟩)⟩] =>
              decide (span = tupleSpan ∧ a.span.endByte < b.span.startByte ∧ b.span.endByte < c.span.startByte) &&
                span.contains a.span && span.contains b.span && span.contains c.span
          | _ => false) "original flat expression children or ranges were rewritten"
        for store in stores do
          assertTrue (decide (runRuntimeFunction? types owner source args 2 store =
            some (type,.outOfFuel ⟨.ret (w n),[.pairRight (.pair (.var 1) (.var 0)) [w 17,.bool choice,w n]],store⟩)))
            "first tuple component or saved original tail environment changed"
      let four := Core.Expr.pair (.var 2) (.pair (.var 1) (.pair (.var 0) .unit))
      let fourType := Core.Ty.product .word (.product .bool (.product .word .unit))
      let fourValue := Core.Value.pair (w n) (.pair (.bool choice) (.pair (w 17) .unit))
      let unused ← check types "function strict(x: Word,c: Bool,y: Word) returns(Word){let unused: (Word,Bool,Word,())=(x,c,y,());return x;}"
        args (.letE four (.var 3)) .word (w n) 16 (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .unit (.cons .applyPair (.cons .applyPair (.cons .applyPair (.cons .bindLet (.cons (.var rfl) (.refl))))))))))))))))) [fourType]
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner unused args 14 store =
          some (.word,.outOfFuel ⟨.ret fourValue,[.letBody (.var 3) [w 17,.bool choice,w n]],store⟩))) "unused flat initializer was skipped"
      let _ ← check types "function nested(x: Word,c: Bool,y: Word) returns(((Word,Word),Bool,())){return ((x,y),c,());}"
        args (.pair (.pair (.var 2) (.var 0)) (.pair (.var 1) .unit)) (.product (.product .word .word) (.product .bool .unit))
        (.pair (.pair (w n) (w 17)) (.pair (.bool choice) .unit)) 13 (by intro store k; exact .cons .enterPair (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .enterPairRight (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .unit (.cons .applyPair (.cons .applyPair (.refl)))))))))))))) []
      let _ ← check types "function selected(x: Word,c: Bool,y: Word) returns((Word,Word,Word)){return (x,c ? x : y,y);}"
        args (.pair (.var 2) (.pair (.ifE (.var 1) (.var 2) (.var 0)) (.var 0)))
        (.product .word (.product .word .word)) (.pair (w n) (.pair (if choice then w n else w 17) (w 17))) 12
        (by
          intro store k
          cases choice
          · exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .applyPair (.refl))))))))))))
          · exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .applyPair (.refl))))))))))))) []
      for text in ["function wrong(x: Word,c: Bool,y: Word) returns(((Word,Bool),Word)){return (x,c,y);}",
          "function unitTail(x: Word,c: Bool,y: Word) returns((Word,Bool,Word,())){return (x,c,y);}",
          "function first(x: Word,c: Bool,y: Word) returns((Word,Bool,Word)){return (missing,c,y);}",
          "function middle(x: Word,c: Bool,y: Word) returns((Word,Bool,Word)){return (x,missing,y);}",
          "function last(x: Word,c: Bool,y: Word) returns((Word,Bool,Word)){return (x,c,missing);}",
          "function calls(x: Word,c: Bool,y: Word) returns((Word,Bool,Word)){return (x,c,f(y));}"] do rejected types (← parsed text) args
  let cell : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 999,.cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w 7],.closure (.cons .word .nil) (.var rfl)⟩
  let opaqueArg := pairArg cell (pairArg closure unitArg)
  let _ ← check types "function opaque(p: (Cell,Fn,())) returns(((Cell,Fn,()),(),())){return (p,(),());}"
    [opaqueArg] (.pair (.var 0) (.pair .unit .unit)) (.product opaqueArg.type (.product .unit .unit))
    (.pair opaqueArg.value (.pair .unit .unit)) 9
    (by intro store k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons .unit (.cons .enterPairRight (.cons .unit (.cons .applyPair (.cons .applyPair (.refl)))))))))) []
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedManyTypeEntries
/-! Original many-element annotations keep exact right-associated types and existing steps.
Independent annotation/raw-body evidence and fixed Core paths determine all expectations. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ManyTypeEntries
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ManyTypeEntry", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool),
  (["Unit"], .unit), (["Pair"], .product .word .bool), (["Pkg", "Flag"], .bool),
  (["Cell"], .cell .word), (["Fn"], .function .word .word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def unitArg : TypedRuntimeArgument := ⟨.unit,.unit,.unit⟩
private def pairArg (left right : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.product left.type right.type,.pair left.value right.value,.pair left.valueTyped right.valueTyped⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "many-type-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "unexpected lexing diagnostic"
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide (source.span.source = file.id ∧
    source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) && source.span.contains source.value.body.span)
    "original declaration range or completion changed"
  return source
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .group inner⟩ =>
      let child ← expression table env store inner
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .group child.costed⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← expression table env store left
      let second ← expression table env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ =>
      let head ← expression table env store first
      let tail ← expression table env store ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩
      return ⟨.pair head.value tail.value, head.cost + tail.cost + 3, by rw [sourceAt]; exact .many head.costed tail.costed⟩
  | _ => throw (IO.userError "expression outside independent unit script")
termination_by sizeOf source
private structure Body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store source value store cost
private def body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) : IO (Body table env store source) := do
  match sourceAt : source with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let first ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let second ← body ((name.value, id) :: table) ((id, first.value) :: env) store ⟨span, rest⟩
      return ⟨second.value, first.cost + second.cost + 2, by rw [sourceAt]; exact .binding first.costed second.costed⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← body table env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← body table env store no
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent guard not Boolean")
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | _ => throw (IO.userError "body outside independent unit script")
termination_by sizeOf source
private structure Annotation (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes types source type
private def annotation (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Annotation types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | none => throw (IO.userError "independent return leaf missing")
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [atSource]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← annotation types child
      return ⟨inner.type, by rw [atSource]; exact .single inner.meaning⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let first ← annotation types left
      let second ← annotation types right
      return ⟨.product first.type second.type, by rw [atSource]; exact .pair first.meaning second.meaning⟩
  | ⟨span, .tuple (first :: second :: third :: rest)⟩ =>
      let head ← annotation types first
      let tail ← annotation types ⟨span, .tuple (second :: third :: rest)⟩
      return ⟨.product head.type tail.type, by rw [atSource]; exact .many head.meaning tail.meaning⟩
  | _ => throw (IO.userError "return annotation outside independent script")
termination_by sizeOf source
private structure Return (types : TypeNameTable) (clause : Option Syntax.ReturnClause) where
  type : Core.Ty
  meaning : RuntimeReturnTypeDenotes types clause type
private def returns (types : TypeNameTable) (clause : Option Syntax.ReturnClause) : IO (Return types clause) := do
  match atClause : clause with
  | none => return ⟨.unit, by rw [atClause]; exact .absent⟩
  | some ⟨_, ⟨_, [source]⟩⟩ =>
      let child ← annotation types source
      return ⟨child.type, by rw [atClause]; exact .single child.meaning⟩
  | _ => throw (IO.userError "independent return clause is not singleton")
private def bindingTypes (types : TypeNameTable) (source : Syntax.Block) : IO (List Core.Ty) := do
  match source with
  | ⟨span, ⟨_, .letDecl _ (some sourceType) (some _)⟩ :: rest⟩ =>
      let meaning ← annotation types sourceType
      let tail ← bindingTypes types ⟨span, rest⟩
      return meaning.type :: tail
  | ⟨_, [⟨_, .ifThen _ yes (some no)⟩]⟩ =>
      return (← bindingTypes types yes) ++ (← bindingTypes types no)
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => return []
  | _ => throw (IO.userError "original annotated body shape changed")
termination_by sizeOf source
private def check (types : TypeNameTable) (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (steps : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) (written : List Core.Ty) : IO Syntax.FunctionDecl := do
  let source ← parsed content
  assertTrue (decide ((← bindingTypes types source.value.body) = written)) "independent written let annotation order/types changed"
  let declared ← returns types source.value.signature.returnsClause
  assertTrue (decide (declared.type = type)) "independent structural return type differs from fixture"
  if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
      source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
    have header : RuntimeFunctionHeader types source.value.signature declared.type :=
      ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, declared.meaning⟩
    have _ := interpretRuntimeFunctionHeader?_iff.mpr header
    pure ()
  else throw (IO.userError "independent header policy rejected")
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError ("structural parameter entry did not compile: " ++ content))
  let original ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name sourceType := parameter.value | throw (IO.userError "original parameter shape changed")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains sourceType.span)
      "original parameter range changed"
    let meaning ← annotation types sourceType
    pure (name.value, meaning.type)
  let names := original.map Prod.fst
  assertTrue (decide (original.map Prod.snd = arguments.map (·.type))) "independent original parameter types changed"
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
    compiled.inputs.context.values = (original.map Prod.snd).reverse ∧ compiled.inputs.bindings.length = arguments.length))
    "fixed ordered Core/type or original parameter-only layout changed"
  match preparedAt : prepareRuntimeFunction? types owner source arguments with
  | none => throw (IO.userError "structural arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "adapter flattened arguments or leaked local bindings into parameter records"
      for store in stores do
        let raw ← body prepared.inputs.names prepared.inputs.environment store source.value.body
        assertTrue (decide (raw.value = value ∧ raw.cost = cost))
          "separate source/Core certificates disagreed with independent fixture"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation raw.costed
        have direct := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, direct⟩
        have _ := independent.cost_le_fuelBound
        have _ := (steps store []).runStateful_done_iff (fuel := cost)
        assertTrue (decide (evaluateRuntimeFunctionWithCost? types owner source arguments = some (type, value, cost))) "entry triple changed"
        let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
        let start := Core.State.initial core (arguments.reverse.map (·.value)) store
        for fuel in List.range (cost + 3) do
          have _ := independent.run_done_iff (fuel := fuel)
          have _ := independent.run_outOfFuel_iff (fuel := fuel)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel start))) "entry changed fixed Core or full checkpoint"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "entry threshold, ordered value or own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "entry residual path changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "actual remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart pretended to resume"
          | _ => throw (IO.userError "below-cost entry checkpoint missing")
  return source
private def rejected (types : TypeNameTable) (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid structural parameter gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid structural parameter gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid structural parameter gate exposed a checkpoint"
end ManyTypeEntries
open ManyTypeEntries

def frontendParsedManyTypeEntryTests : IO Unit := do
  let _ ← check [] "function units() returns(((),(),())){return ((),((),()));}" []
    (.pair .unit (.pair .unit .unit)) (.product .unit (.product .unit .unit)) (.pair .unit (.pair .unit .unit)) 9
    (by intro store k; exact .cons .enterPair (.cons .unit (.cons .enterPairRight (.cons .enterPair (.cons .unit (.cons .enterPairRight (.cons .unit (.cons .applyPair (.cons .applyPair (.refl)))))))))) []
  for n in [0,9,Core.wordModulus - 1] do
    for choice in [false,true] do
      let args := [wordArg n,boolArg choice,wordArg 17]
      let value := Core.Value.pair (w n) (.pair (.bool choice) (w 17))
      let type := Core.Ty.product .word (.product .bool .word)
      let core := Core.Expr.pair (.var 2) (.pair (.var 1) (.var 0))
      let actual := pairArg (wordArg n) (pairArg (boolArg choice) (wordArg 17))
      for written in ["(Word,Bool,Word)", "(Word,Bool,Word,)", "((Word,),(Bool,),Word)"] do
        let _ ← check types ("function returned(x: Word,c: Bool,z: Word) returns(" ++ written ++ "){return (x,(c,z));}")
          args core type value 9 (by intro store k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .applyPair (.refl)))))))))) []
        let parameter ← check types ("function parameter(p: " ++ written ++ ") returns((Word,(Bool,Word))){return p;}")
          [actual] (.var 0) type value 1 (by intro store k; exact .cons (.var rfl) .refl) []
        assertTrue (match parameter.value.signature.parameters.elements with
          | [⟨_,.typed none _ ⟨span,.tuple [first,second,third]⟩⟩] =>
              span.contains first.span && span.contains second.span && span.contains third.span &&
                decide (first.span.endByte < second.span.startByte ∧ second.span.endByte < third.span.startByte)
          | _ => false) "flat annotation was rewritten into generated nested source"
      let unused ← check types "function strict(x: Word,c: Bool,z: Word) returns(Word){let unused: (Word,Bool,Word)=(x,(c,z));return x;}"
        args (.letE core (.var 3)) .word (w n) 12 (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .applyPair (.cons .bindLet (.cons (.var rfl) (.refl))))))))))))) [type]
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner unused args 10 store =
          some (.word,.outOfFuel ⟨.ret value,[.letBody (.var 3) [w 17,.bool choice,w n]],store⟩)))
          "strict many-type initializer or saved original environment changed"
      let _ ← check types "function branches(x: Word,c: Bool,z: Word) returns((Word,Bool,Word)){if(c){return (x,(c,z));}else{let p: (Word,Bool,Word)=(x,(c,z));return p;}}"
        args (.ifE (.var 1) core (.letE core (.var 0))) type value (if choice then 12 else 15)
        (by
          intro store k
          cases choice
          · exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .applyPair (.cons .bindLet (.cons (.var rfl) (.refl)))))))))))))))
          · exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .applyPair (.refl))))))))))))) [type]
      let four := pairArg (wordArg n) (pairArg (boolArg choice) (pairArg (wordArg 17) unitArg))
      let _ ← check types "function four(p: (Word,Bool,Word,())) returns((Word,(Bool,(Word,())))){let q: (Word,Bool,Word,())=p;return q;}"
        [four] (.letE (.var 0) (.var 0)) four.type four.value 4
        (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) (.refl))))) [four.type]
      let left := pairArg (pairArg (wordArg n) (boolArg choice)) (wordArg 17)
      let _ ← check types "function nested(p: ((Word,Bool),Word)) returns(((Word,Bool),Word)){return p;}"
        [left] (.var 0) left.type left.value 1 (by intro store k; exact .cons (.var rfl) .refl) []
      let _ ← check types "function expression(x: Word,c: Bool,z: Word) returns((Word,Bool,Word)){return (x,c,z);}"
        args core type value 9 (by intro store k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .applyPair .refl))))))))) []
      for content in ["function wrong(x: Word,c: Bool,z: Word) returns((Word,Bool,Word)){return ((x,c),z);}",
          "function clauses(x: Word,c: Bool,z: Word) returns(Word,Bool,Word){return (x,(c,z));}",
          "function first(x: Word,c: Bool,z: Word){let p: (Missing,Bool,Word)=(x,(c,z));return ();}",
          "function middle(x: Word,c: Bool,z: Word){let p: (Word,Missing,Word)=(x,(c,z));return ();}",
          "function last(x: Word,c: Bool,z: Word){let p: (Word,Bool,Missing)=(x,(c,z));return ();}"] do
        rejected types (← parsed content) args
      let acceptsOne ← parsed "function one(p: (Word,Bool,Word)) returns((Word,Bool,Word)){return p;}"
      for wrong in [args,[left],[pairArg actual unitArg]] do rejected types acceptsOne wrong
  let cell : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 999,.cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w 7],.closure (.cons .word .nil) (.var rfl)⟩
  let opaqueArg := pairArg cell (pairArg closure unitArg)
  let _ ← check types "function opaque(p: (Cell,Fn,())) returns((Cell,Fn,())){let q: (Cell,Fn,())=p;return q;}"
    [opaqueArg] (.letE (.var 0) (.var 0)) opaqueArg.type opaqueArg.value 4
    (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) (.refl))))) [opaqueArg.type]
  let nominal ← parsed "function nominal(p: (N,(),Word)) returns((N,(),Word)){let q: (N,(),Word)=p;return q;}"
  let nominalTypes := (["N"],Core.Ty.namedData ⟨91⟩) :: types
  assertTrue (decide ((compileRuntimeFunction? nominalTypes owner nominal).map (fun c => (c.core,c.returnType)) =
    some (.letE (.var 0) (.var 0),.product (.namedData ⟨91⟩) (.product .unit .word)))) "static many type required a nominal actual"
  rejected nominalTypes nominal [pairArg (wordArg 9) (pairArg unitArg (wordArg 17))]
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedManyTypes
/-! Original flat lists retain every child and range. Independent structural and
parameter certificates are compared with external ordered types and supplied values. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedManyTypes
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Many", by decide⟩], by decide⟩⟩, 36⟩
private def table : TypeNameTable := [(["W"], .word), (["W"], .unit), (["B"], .bool),
  (["Unit"], .word), (["Pkg", "Flag"], .bool), (["Pkg.Flag"], .word),
  (["Cell"], .cell .word), (["Fn"], .function .word .word), (["N"], .namedData ⟨91⟩)]
private def file (text : String) : Syntax.SourceFile := ⟨⟨.main, "many-types.sol"⟩, text⟩
private def parsed? (text : String) : IO (Option Syntax.TypeExpr) := do
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file text) lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span = ⟨(file text).id,0,text.utf8ByteSize⟩)) "complete original type range lost"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "type parser invariant")
private def parsed (text : String) : IO Syntax.TypeExpr := do
  let some source ← parsed? text | throw (IO.userError s!"complete type rejected: {text}")
  return source
private def ranges (source : Syntax.TypeExpr) : IO Unit := do
  match source with
  | ⟨span, .tuple elements⟩ =>
      for child in elements do
        assertTrue (span.contains child.span) "original inner type range escaped its parent"
      for (left,right) in elements.zip elements.tail do
        assertTrue (decide (left.span.endByte < right.span.startByte)) "written child order changed"
      for child in elements do ranges child
  | _ => pure ()
termination_by sizeOf source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match original : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [original]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent named leaf missing")
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [original]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← meaning types child
      return ⟨inner.type, by rw [original]; exact .single inner.evidence⟩
  | ⟨_, .tuple [left,right]⟩ =>
      let l ← meaning types left; let r ← meaning types right
      return ⟨.product l.type r.type, by rw [original]; exact .pair l.evidence r.evidence⟩
  | ⟨span, .tuple (first :: second :: third :: rest)⟩ =>
      let head ← meaning types first; let tail ← meaning types ⟨span, .tuple (second :: third :: rest)⟩
      return ⟨.product head.type tail.type, by rw [original]; exact .many head.evidence tail.evidence⟩
  | _ => throw (IO.userError "outside independent type profile")
termination_by sizeOf source
private def checked (types : TypeNameTable) (text : String) (arity : Nat) (expected : Core.Ty) : IO Syntax.TypeExpr := do
  let source ← parsed text
  assertTrue (match source.value with | .tuple elements => decide (elements.length = arity) | _ => false)
    "original flat element count was normalized or rewritten"
  ranges source
  let independent ← meaning types source
  assertTrue (decide (independent.type = expected ∧ interpretStructuralType? types source = some expected))
    "ordered right-associated fixture type changed"
  have _ := interpretStructuralType?_iff.mpr independent.evidence
  have _ := independent.evidence.type_unique (interpretStructuralType?_sound independent.evidence.complete)
  assertTrue (interpretTypeName? types source).isNone "old named-only adapter accepted a product list"
  let replacement : Syntax.SourceSpan := ⟨⟨.external "other", "raw"⟩,99,1⟩
  have _ := interpretStructuralType?_span types source replacement
  assertTrue (decide (interpretStructuralType? types { source with span := replacement } = some expected))
    "outer-span transport changed original nested meanings"
  have extension : TypeNameTable.Extends types (types ++ [(["W"],.bool)]) :=
    TypeNameTable.Extends.append_right types _
  have _ := independent.evidence.extend_types extension
  have _ := interpretStructuralType?_some_of_extends extension independent.evidence.complete
  assertTrue (decide (interpretStructuralType? (types ++ [(["W"],.bool)]) source = some expected))
    "later conflicting duplicate changed a written leaf"
  return source
private def parameters (text : String) : IO (Syntax.DelimitedList Syntax.FunctionParameter) := do
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "parameter lexer invariant")
  let .ok source next := Syntax.Parser.functionParameters (Syntax.Parser.State.initial (file text) lexed)
    | throw (IO.userError "complete original parameters rejected")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨(file text).id,0,text.utf8ByteSize⟩)) "parameter list was partial or reranged"
  return source
private structure Declaration (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types owner initial params inputs
private def declaration (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) :
    IO (Declaration types initial params) := do
  match original : params with
  | [] => return ⟨initial, by rw [original]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest =>
      let head ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declaration types (initial.bindFresh owner name.value head.type) rest
        return ⟨tail.inputs, by rw [original]; exact .cons head.evidence unused tail.evidence⟩
      else throw (IO.userError "original names repeat")
  | _ => throw (IO.userError "unsupported original parameter shape")
private structure Binding (types : TypeNameTable) (initial : LocalInputs)
    (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial params args inputs
private def binding (types : TypeNameTable) (initial : LocalInputs) (params : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Binding types initial params args) := do
  match original : params, actual : args with
  | [], [] => return ⟨initial, by rw [original,actual]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest, argument :: tailArgs =>
      let head ← meaning types annotation
      if same : head.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← binding types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest tailArgs
          return ⟨tail.inputs, by rw [original,actual]; exact .cons (same ▸ head.evidence) unused tail.evidence⟩
        else throw (IO.userError "duplicate parameter spelling")
      else throw (IO.userError "supplied actual differs from the independent annotation type")
  | _,_ => throw (IO.userError "one original parameter requires one actual argument")
private def rows (inputs : LocalTypeInputs) := inputs.bindings.map fun row => (row.name,row.id,row.type)
private def checkParameters (types : TypeNameTable) (text : String) (expected : List (String × Core.Ty))
    (arguments : Option (List TypedRuntimeArgument) := none) : IO Unit := do
  let source ← parameters text
  let independent ← declaration types .empty source.elements
  let expectedRows := expected.zipIdx.map fun (row,index) => (row.1,(⟨owner,index⟩ : Resolved.LocalId),row.2)
  assertTrue (decide (rows independent.inputs = expectedRows.reverse ∧ source.elements.length = expected.length ∧
    (declareRuntimeParameters? types owner source.elements).map rows = some expectedRows.reverse)) "exact original row/order changed"
  have _ := RuntimeParametersDeclare.complete independent.evidence
  for index in List.range source.elements.length do
    match original : source.elements[index]? with
    | some ⟨span,.typed none name annotation⟩ =>
        ranges annotation
        have _ := RuntimeParametersDeclare.position independent.evidence original
        assertTrue (source.span.contains span && span.contains name.span && span.contains annotation.span &&
          decide (Resolved.LocalScope.index? independent.inputs.ids ⟨owner,index⟩ = some (expected.length - 1 - index)))
          "original parameter ranges or reversed Core index changed"
    | _ => throw (IO.userError "original declared position disappeared")
  match arguments with
  | none => pure ()
  | some args =>
      let actual ← binding types .empty source.elements args
      have _ := independent.evidence.result_unique actual.evidence.erase_values
      if matching : args.map (·.type) = independent.inputs.context.values.reverse then
        have _ := RuntimeParametersDeclare.bind_typed_arguments independent.evidence args matching
      else throw (IO.userError "static restoration lost supplied actual types")
      have _ := RuntimeParametersBind.complete actual.evidence
      assertTrue (decide (rows actual.inputs.toTypeInputs = expectedRows.reverse ∧
        actual.inputs.environment.values = args.reverse.map (·.value) ∧ args.length = expected.length ∧
        (bindRuntimeParameters? types owner source.elements args).map (fun i => (i.names,i.context,i.environment)) =
          some (actual.inputs.names,actual.inputs.context,actual.inputs.environment))) "products were flattened or values reordered"
private def w : TypedRuntimeArgument := ⟨.word,.word (Core.Word.ofNatModulo 9),.word⟩
private def b : TypedRuntimeArgument := ⟨.bool,.bool true,.bool⟩
private def u : TypedRuntimeArgument := ⟨.unit,.unit,.unit⟩
private def pair (l r : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.product l.type r.type,.pair l.value r.value,.pair l.valueTyped r.valueTyped⟩
end ParsedManyTypes
open ParsedManyTypes

def frontendParsedManyTypeTests : IO Unit := do
  for (text,arity,expected) in [("()",0,Core.Ty.unit),("(W,)",1,.word),("(W,B)",2,.product .word .bool),
      ("(W,B,())",3,.product .word (.product .bool .unit)), ("(W,B,(),W,)",4,.product .word (.product .bool (.product .unit .word))),
      ("((W,B),(),W)",3,.product (.product .word .bool) (.product .unit .word)),
      ("(W,(B,()),W)",3,.product .word (.product (.product .bool .unit) .word)),
      ("((),(),(),())",4,.product .unit (.product .unit (.product .unit .unit)))] do
    let _ ← checked table text arity expected
  let flat ← checked table "(W,B,())" 3 (.product .word (.product .bool .unit))
  assertTrue (match flat.value with
    | .tuple [⟨a,.named _ none⟩,⟨b,.named _ none⟩,⟨c,.tuple []⟩] =>
        decide ((a.startByte,a.endByte,b.startByte,b.endByte,c.startByte,c.endByte) = (1,2,3,4,5,7))
    | _ => false) "flat source list or exact child byte ranges changed"
  assertTrue (decide (interpretStructuralType? table flat ≠ some (.product (.product .word .bool) .unit) ∧
    interpretStructuralType? table flat ≠ some (.product .word (.product .bool (.product .unit .unit)))))
    "left association or an extra terminal Unit was introduced"
  let qualified ← checked table "(Pkg /* kept */ . Flag,W,())" 3 (.product .bool (.product .word .unit))
  assertTrue (match qualified.value with
    | .tuple (⟨_,.named name none⟩ :: _) => decide (qualifiedTypeNameKey name = ["Pkg","Flag"])
    | _ => false) "qualified component boundaries collapsed into a raw dotted key"
  let _ ← checked table "(Unit,(),Unit)" 3 (.product .word (.product .unit .word))
  for type in [Core.Ty.namedData ⟨91⟩,.cell .bool,.function .unit (.namedData ⟨7⟩)] do
    for depth in [0,1,3,7] do
      let text := (List.range depth).foldl (fun inner _ => "(()," ++ inner ++ ",B,)") "(N,)"
      let expected := (List.range depth).foldl (fun inner _ => Core.Ty.product .unit (.product inner .bool)) type
      let types := [(["N"],type),(["B"],.bool)]
      let _ ← checked types text (if depth = 0 then 1 else 3) expected
      checkParameters types ("(packed: " ++ text ++ ")") [("packed",expected)]
  let triple := pair w (pair b u)
  checkParameters table "(packed: (W,B,()))" [("packed",triple.type)] (some [triple])
  checkParameters table "(first: (), packed: (W,B,(),W,), last: W)"
    [("first",.unit),("packed",(pair w (pair b (pair u w))).type),("last",.word)] (some [u,pair w (pair b (pair u w)),w])
  let cell : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 999,.cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w.value],
    .closure (.cons .word .nil) (.var rfl)⟩
  let opaqueArgument := pair cell (pair closure u)
  checkParameters table "(opaque: (Cell,Fn,()))" [("opaque",opaqueArgument.type)] (some [opaqueArgument])
  for args in [[u],[w,b,u],[pair (pair w b) u],[pair w (pair u b)],[],[triple,u]] do
    let source ← parameters "(packed: (W,B,()))"
    assertTrue (declareRuntimeParameters? table owner source.elements).isSome "valid static triple depended on actual inhabitants"
    assertTrue (bindRuntimeParameters? table owner source.elements args).isNone "wrong count, flattening, association or order accepted"
  for text in ["(Missing,W,B)","(W,Missing,B)","(W,B,Missing)","(W,B,(),Missing)","(W,(B,Missing,()),())",
      "(W,@B,())","(W,B<W>,())","(W,mapping(W => B),())","(W,function() returns(B),())"] do
    let source ← parsed text
    have _ := interpretStructuralType?_eq_none_iff (table := table) (source := source)
    assertTrue (interpretStructuralType? table source).isNone "a written unknown or unsupported child was skipped"
  let missing ← parsed "(W,New,B)"
  assertTrue (interpretStructuralType? table missing).isNone "one-way extension's old failure disappeared"
  let _ ← checked (table ++ [(["New"],.unit)]) "(W,New,B)" 3 (.product .word (.product .unit .bool))
  have sameLookup (key : List String) : table.lookup? key = (table ++ table).lookup? key := by
    cases result : table.lookup? key with
    | none =>
        symm
        apply TypeNameTable.lookup?_eq_none_iff.mpr
        simpa only [List.map_append, List.mem_append, not_or] using
          And.intro (TypeNameTable.lookup?_eq_none_iff.mp result)
            (TypeNameTable.lookup?_eq_none_iff.mp result)
    | some type =>
        exact (TypeNameTable.lookup?_iff.mpr
          (TypeNameTable.Extends.append_right table table
            (TypeNameTable.lookup?_iff.mp result))).symm
  have backward : TypeNameTable.Extends (table ++ table) table := by
    intro key type found
    apply TypeNameTable.lookup?_iff.mp
    rw [sameLookup]
    exact TypeNameTable.lookup?_iff.mpr found
  for text in ["(W,B,())","(W,New,B)","(W,@B,())"] do
    let source ← parsed text
    have _ := interpretStructuralType?_congr_lookup table (table ++ table) sameLookup source
    have _ := interpretStructuralType?_eq_of_mutual_extends (TypeNameTable.Extends.append_right table table) backward source
    assertTrue (decide (interpretStructuralType? table source = interpretStructuralType? (table ++ table) source))
      "unequal lookup-equivalent tables changed the entire optional result"
    let params ← parameters ("(x: " ++ text ++ ")")
    have _ := declareRuntimeParameters?_eq_of_mutual_extends (TypeNameTable.Extends.append_right table table) backward owner params.elements
    assertTrue (decide ((declareRuntimeParameters? table owner params.elements).map rows =
      (declareRuntimeParameters? (table ++ table) owner params.elements).map rows)) "full optional declaration was not preserved"
  assertTrue (decide (interpretStructuralType? ((["W"],.unit) :: table) flat = some (.product .unit (.product .bool .unit))))
    "first-match conflicting prefix was treated as semantic extension"
  for text in ["(W,B,,())","(W,B,()) trailing","(W,B,()","(,W,B)"] do
    assertTrue (← parsed? text).isNone "malformed source manufactured a structural type"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedStructuralLetEntries
/-! Original structural let annotations reach existing entries without new steps.
Independent annotation/raw-body evidence and fixed Core paths determine all expectations. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace StructuralLetEntries
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"StructuralLetEntry", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool),
  (["Unit"], .unit), (["Pair"], .product .word .bool), (["Pkg", "Flag"], .bool),
  (["Cell"], .cell .word), (["Fn"], .function .word .word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "structural-let-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "unexpected lexing diagnostic"
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide (source.span.source = file.id ∧
    source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) && source.span.contains source.value.body.span)
    "original declaration range or completion changed"
  return source
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .group inner⟩ =>
      let child ← expression table env store inner
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .group child.costed⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← expression table env store left
      let second ← expression table env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | _ => throw (IO.userError "expression outside independent unit script")
termination_by sizeOf source
private structure Body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store source value store cost
private def body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) : IO (Body table env store source) := do
  match sourceAt : source with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let first ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let second ← body ((name.value, id) :: table) ((id, first.value) :: env) store ⟨span, rest⟩
      return ⟨second.value, first.cost + second.cost + 2, by rw [sourceAt]; exact .binding first.costed second.costed⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← body table env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← body table env store no
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent guard not Boolean")
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | _ => throw (IO.userError "body outside independent unit script")
termination_by sizeOf source
private structure Annotation (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes types source type
private def annotation (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Annotation types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | none => throw (IO.userError "independent return leaf missing")
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [atSource]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← annotation types child
      return ⟨inner.type, by rw [atSource]; exact .single inner.meaning⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let first ← annotation types left
      let second ← annotation types right
      return ⟨.product first.type second.type, by rw [atSource]; exact .pair first.meaning second.meaning⟩
  | _ => throw (IO.userError "return annotation outside independent script")
termination_by sizeOf source
private structure Return (types : TypeNameTable) (clause : Option Syntax.ReturnClause) where
  type : Core.Ty
  meaning : RuntimeReturnTypeDenotes types clause type
private def returns (types : TypeNameTable) (clause : Option Syntax.ReturnClause) : IO (Return types clause) := do
  match atClause : clause with
  | none => return ⟨.unit, by rw [atClause]; exact .absent⟩
  | some ⟨_, ⟨_, [source]⟩⟩ =>
      let child ← annotation types source
      return ⟨child.type, by rw [atClause]; exact .single child.meaning⟩
  | _ => throw (IO.userError "independent return clause is not singleton")
private def bindingTypes (types : TypeNameTable) (source : Syntax.Block) : IO (List Core.Ty) := do
  match source with
  | ⟨span, ⟨_, .letDecl _ (some sourceType) (some _)⟩ :: rest⟩ =>
      let meaning ← annotation types sourceType
      let tail ← bindingTypes types ⟨span, rest⟩
      return meaning.type :: tail
  | ⟨_, [⟨_, .ifThen _ yes (some no)⟩]⟩ =>
      return (← bindingTypes types yes) ++ (← bindingTypes types no)
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => return []
  | _ => throw (IO.userError "original annotated body shape changed")
termination_by sizeOf source
private def check (types : TypeNameTable) (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (steps : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) (written : List Core.Ty) : IO Syntax.FunctionDecl := do
  let source ← parsed content
  assertTrue (decide ((← bindingTypes types source.value.body) = written)) "independent written let annotation order/types changed"
  let declared ← returns types source.value.signature.returnsClause
  assertTrue (decide (declared.type = type)) "independent structural return type differs from fixture"
  if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
      source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
    have header : RuntimeFunctionHeader types source.value.signature declared.type :=
      ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, declared.meaning⟩
    have _ := interpretRuntimeFunctionHeader?_iff.mpr header
    pure ()
  else throw (IO.userError "independent header policy rejected")
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError ("structural parameter entry did not compile: " ++ content))
  let original ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name sourceType := parameter.value | throw (IO.userError "original parameter shape changed")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains sourceType.span)
      "original parameter range changed"
    let meaning ← annotation types sourceType
    pure (name.value, meaning.type)
  let names := original.map Prod.fst
  assertTrue (decide (original.map Prod.snd = arguments.map (·.type))) "independent original parameter types changed"
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
    compiled.inputs.context.values = (original.map Prod.snd).reverse ∧ compiled.inputs.bindings.length = arguments.length))
    "fixed ordered Core/type or original parameter-only layout changed"
  match preparedAt : prepareRuntimeFunction? types owner source arguments with
  | none => throw (IO.userError "structural arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "adapter flattened arguments or leaked local bindings into parameter records"
      for store in stores do
        let raw ← body prepared.inputs.names prepared.inputs.environment store source.value.body
        assertTrue (decide (raw.value = value ∧ raw.cost = cost))
          "separate source/Core certificates disagreed with independent fixture"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation raw.costed
        have direct := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, direct⟩
        have _ := independent.cost_le_fuelBound
        have _ := (steps store []).runStateful_done_iff (fuel := cost)
        assertTrue (decide (evaluateRuntimeFunctionWithCost? types owner source arguments = some (type, value, cost))) "entry triple changed"
        let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
        let start := Core.State.initial core (arguments.reverse.map (·.value)) store
        for fuel in List.range (cost + 3) do
          have _ := independent.run_done_iff (fuel := fuel)
          have _ := independent.run_outOfFuel_iff (fuel := fuel)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel start))) "entry changed fixed Core or full checkpoint"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "entry threshold, ordered value or own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "entry residual path changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "actual remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart pretended to resume"
          | _ => throw (IO.userError "below-cost entry checkpoint missing")
  return source
private def rejected (types : TypeNameTable) (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid structural parameter gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid structural parameter gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid structural parameter gate exposed a checkpoint"
end StructuralLetEntries
open StructuralLetEntries

def frontendParsedStructuralLetEntryTests : IO Unit := do
  for annotation in ["()", "(())", "((),)"] do
    let source ← check [] ("function unit() returns(()){let u: " ++ annotation ++ "=();return u;}") []
      (.letE .unit (.var 0)) .unit .unit 4
      (by intro store k; exact .cons .enterLet (.cons .unit (.cons .bindLet (.cons (.var rfl) .refl)))) [.unit]
    for store in stores do
      assertTrue (decide (runRuntimeFunction? [] owner source [] 2 store =
        some (.unit, .outOfFuel ⟨.ret .unit, [.letBody (.var 0) []], store⟩))) "Unit binding checkpoint lost its tail"
  let _ ← check [(["Unit"],.word)] "function notReserved() returns(()){let u: ()=();return u;}" []
    (.letE .unit (.var 0)) .unit .unit 4
    (by intro store k; exact .cons .enterLet (.cons .unit (.cons .bindLet (.cons (.var rfl) .refl)))) [.unit]
  for n in [0,9,Core.wordModulus - 1] do
    for choice in [false,true] do
      let args := [wordArg n,boolArg choice]
      let ptype := Core.Ty.product .word .bool
      let pvalue := Core.Value.pair (w n) (.bool choice)
      let _ ← check types "function single(x: Word,c: Bool) returns(Word){let y: ((Word,))=x;return y;}" args
        (.letE (.var 1) (.var 0)) .word (w n) 4
        (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))) [.word]
      for annotation in ["(Word,Bool)", "((Word,),(Bool,))", "(Word,Bool,)"] do
        let _ ← check types ("function pair(x: Word,c: Bool) returns((Word,Bool)){let p: " ++ annotation ++ "=(x,c);return p;}") args
          (.letE (.pair (.var 1) (.var 0)) (.var 0)) ptype pvalue 8
          (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
            (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons (.var rfl) .refl)))))))) [ptype]
      let unused ← check types "function strict(x: Word,c: Bool) returns(Word){let unused: (Word,Bool)=(x,c);return x;}" args
        (.letE (.pair (.var 1) (.var 0)) (.var 2)) .word (w n) 8
        (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
          (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons (.var rfl) .refl)))))))) [ptype]
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner unused args 6 store =
          some (.word, .outOfFuel ⟨.ret pvalue, [.letBody (.var 2) [.bool choice,w n]], store⟩)))
          "unused structural initializer stopped executing strictly"
      let _ ← check types "function nested(x: Word,c: Bool) returns(((Word,Bool),())){let p: (Word,Bool)=(x,c);let q: ((Word,Bool),())=(p,());return q;}" args
        (.letE (.pair (.var 1) (.var 0)) (.letE (.pair (.var 0) .unit) (.var 0))) (.product ptype .unit) (.pair pvalue .unit) 15
        (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl)
          (.cons .applyPair (.cons .bindLet (.cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
            (.cons .unit (.cons .applyPair (.cons .bindLet (.cons (.var rfl) .refl))))))))))))))) [ptype,.product ptype .unit]
      let _ ← check types "function arms(x: Word,c: Bool) returns((Word,Bool)){if(c){let p: (Word,Bool)=(x,c);return p;}else{let u: ()=();let p: (Word,Bool)=(x,c);return p;}}" args
        (.ifE (.var 0) (.letE (.pair (.var 1) (.var 0)) (.var 0)) (.letE .unit (.letE (.pair (.var 2) (.var 1)) (.var 0))))
        ptype pvalue (if choice then 11 else 14)
        (by
          intro store k
          cases choice
          · exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons .enterLet (.cons .unit (.cons .bindLet (.cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons (.var rfl) (.refl))))))))))))))
          · exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons (.var rfl) (.refl)))))))))))) [ptype,.unit,ptype]
      for declaration in ["function mismatch(x: Word,c: Bool){let p: (Word,Bool)=();return ();}",
          "function order(x: Word,c: Bool){let p: (Bool,Word)=(x,c);return ();}",
          "function association(x: Word,c: Bool){let p: (Word,(Bool,()))=((x,c),());return ();}",
          "function unknown(x: Word,c: Bool){let p: (Word,Missing)=(x,c);return ();}",
          "function many(x: Word,c: Bool){let p: (Word,Bool,Word)=(x,c);return ();}",
          "function self(x: Word,c: Bool){let p: (Word,Bool)=p;return ();}",
          "function forward(x: Word,c: Bool){let p: (Word,Bool)=q;let q: (Word,Bool)=(x,c);return ();}",
          "function shadow(x: Word,c: Bool){let x: (Word)=x;return ();}",
          "function sibling(x: Word,c: Bool) returns((Word,Bool)){if(c){let p: (Word,Bool)=(x,c);return p;}else{return p;}}"] do
        rejected types (← parsed declaration) args
  let selected ← parsed "function skipped(x: Word,c: Bool) returns(Word){if(c){return x;}else{let bad: (Missing,())=(x,());return x;}}"
  let names : LocalNameTable := [("c",⟨owner,1⟩),("x",⟨owner,0⟩)]
  let env : Resolved.Environment := [(⟨owner,1⟩,.bool true),(⟨owner,0⟩,w 9)]
  for store in stores do
    let original ← body names env store selected.value.body
    assertTrue (decide (original.value = w 9 ∧ original.cost = 4 ∧
      evaluateTypedLetReturnTreeWithCost? owner names env selected.value.body = some (w 9,4))) "raw selected path changed"
  rejected types selected [wordArg 9,boolArg true]
  let cell : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 999,.cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w 7],.closure (.cons .word .nil) (.var rfl)⟩
  let opaqueArg : TypedRuntimeArgument := ⟨.product cell.type closure.type,.pair cell.value closure.value,.pair cell.valueTyped closure.valueTyped⟩
  let _ ← check types "function opaque(p: (Cell,Fn)) returns((Cell,Fn)){let q: (Cell,Fn)=p;return q;}" [opaqueArg]
    (.letE (.var 0) (.var 0)) opaqueArg.type opaqueArg.value 4
    (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))) [opaqueArg.type]
  let nominal ← parsed "function nominal(p: (N,())) returns((N,())){let q: (N,())=p;return q;}"
  let nominalTypes := (["N"],Core.Ty.namedData ⟨91⟩) :: types
  assertTrue (decide ((compileRuntimeFunction? nominalTypes owner nominal).map (fun c => (c.core,c.returnType)) =
    some (.letE (.var 0) (.var 0),.product (.namedData ⟨91⟩) .unit))) "static let required a nominal inhabitant"
  rejected nominalTypes nominal [wordArg 9]
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedStructuralParameterEntries
/-! Structural parameters enter the unchanged whole-function runtime. Original
annotation/raw-body evidence and hand-written Core paths fix each expectation. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace StructuralParameterEntries
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"StructuralParameterEntry", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool),
  (["Unit"], .unit), (["Pair"], .product .word .bool), (["Pkg", "Flag"], .bool),
  (["Cell"], .cell .word), (["Fn"], .function .word .word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "structural-parameter-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "unexpected lexing diagnostic"
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide (source.span.source = file.id ∧
    source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) && source.span.contains source.value.body.span)
    "original declaration range or completion changed"
  return source
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .group inner⟩ =>
      let child ← expression table env store inner
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .group child.costed⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← expression table env store left
      let second ← expression table env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | _ => throw (IO.userError "expression outside independent unit script")
termination_by sizeOf source
private structure Body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store source value store cost
private def body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) : IO (Body table env store source) := do
  match sourceAt : source with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let first ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let second ← body ((name.value, id) :: table) ((id, first.value) :: env) store ⟨span, rest⟩
      return ⟨second.value, first.cost + second.cost + 2, by rw [sourceAt]; exact .binding first.costed second.costed⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← body table env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← body table env store no
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent guard not Boolean")
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | _ => throw (IO.userError "body outside independent unit script")
termination_by sizeOf source
private structure Annotation (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes types source type
private def annotation (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Annotation types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | none => throw (IO.userError "independent return leaf missing")
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [atSource]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← annotation types child
      return ⟨inner.type, by rw [atSource]; exact .single inner.meaning⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let first ← annotation types left
      let second ← annotation types right
      return ⟨.product first.type second.type, by rw [atSource]; exact .pair first.meaning second.meaning⟩
  | _ => throw (IO.userError "return annotation outside independent script")
termination_by sizeOf source
private structure Return (types : TypeNameTable) (clause : Option Syntax.ReturnClause) where
  type : Core.Ty
  meaning : RuntimeReturnTypeDenotes types clause type
private def returns (types : TypeNameTable) (clause : Option Syntax.ReturnClause) : IO (Return types clause) := do
  match atClause : clause with
  | none => return ⟨.unit, by rw [atClause]; exact .absent⟩
  | some ⟨_, ⟨_, [source]⟩⟩ =>
      let child ← annotation types source
      return ⟨child.type, by rw [atClause]; exact .single child.meaning⟩
  | _ => throw (IO.userError "independent return clause is not singleton")
private def check (types : TypeNameTable) (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (steps : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) : IO Syntax.FunctionDecl := do
  let source ← parsed content
  let declared ← returns types source.value.signature.returnsClause
  assertTrue (decide (declared.type = type)) "independent structural return type differs from fixture"
  if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
      source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
    have header : RuntimeFunctionHeader types source.value.signature declared.type :=
      ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, declared.meaning⟩
    have _ := interpretRuntimeFunctionHeader?_iff.mpr header
    pure ()
  else throw (IO.userError "independent header policy rejected")
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError ("structural parameter entry did not compile: " ++ content))
  let original ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name sourceType := parameter.value | throw (IO.userError "original parameter shape changed")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains sourceType.span)
      "original parameter range changed"
    let meaning ← annotation types sourceType
    pure (name.value, meaning.type)
  let names := original.map Prod.fst
  assertTrue (decide (original.map Prod.snd = arguments.map (·.type))) "independent original parameter types changed"
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
    compiled.inputs.context.values = (original.map Prod.snd).reverse ∧ compiled.inputs.bindings.length = arguments.length))
    "fixed ordered Core/type or original parameter-only layout changed"
  match preparedAt : prepareRuntimeFunction? types owner source arguments with
  | none => throw (IO.userError "structural arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "adapter flattened arguments or leaked local bindings into parameter records"
      for store in stores do
        let raw ← body prepared.inputs.names prepared.inputs.environment store source.value.body
        assertTrue (decide (raw.value = value ∧ raw.cost = cost))
          "separate source/Core certificates disagreed with independent fixture"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation raw.costed
        have direct := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, direct⟩
        have _ := independent.cost_le_fuelBound
        have _ := (steps store []).runStateful_done_iff (fuel := cost)
        assertTrue (decide (evaluateRuntimeFunctionWithCost? types owner source arguments = some (type, value, cost))) "entry triple changed"
        let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
        let start := Core.State.initial core (arguments.reverse.map (·.value)) store
        for fuel in List.range (cost + 3) do
          have _ := independent.run_done_iff (fuel := fuel)
          have _ := independent.run_outOfFuel_iff (fuel := fuel)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel start))) "entry changed fixed Core or full checkpoint"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "entry threshold, ordered value or own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "entry residual path changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "actual remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart pretended to resume"
          | _ => throw (IO.userError "below-cost entry checkpoint missing")
  return source
private def rejected (types : TypeNameTable) (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid structural parameter gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid structural parameter gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid structural parameter gate exposed a checkpoint"
end StructuralParameterEntries
open StructuralParameterEntries

def frontendParsedStructuralParameterEntryTests : IO Unit := do
  let unitArg : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  for annotation in ["()", "(())", "((()))"] do
    let source ← check [] ("function unit(u: " ++ annotation ++ ") returns(()){return u;}") [unitArg]
      (.var 0) .unit .unit 1 (by intro store k; exact .cons (.var rfl) .refl)
    rejected [] source []
    rejected [] source [wordArg 0]
  let _ ← check [(["Unit"], .word)] "function spelling(u: (),x: Unit) returns(Unit){return x;}" [unitArg, wordArg 5]
    (.var 0) .word (w 5) 1 (by intro store k; exact .cons (.var rfl) .refl)
  for n in [0, 9, Core.wordModulus - 1] do
    for choice in [false, true] do
      let pair : TypedRuntimeArgument :=
        ⟨.product .word .bool, .pair (w n) (.bool choice), .pair .word .bool⟩
      for annotation in ["(Word,Bool)", "((Word),(Bool,))", "((Word,Bool),)"] do
        let source ← check types ("function retain(p: " ++ annotation ++ ",u: ()) returns((Word,Bool)){return p;}")
          [pair, unitArg] (.var 1) pair.type pair.value 1 (by intro store k; exact .cons (.var rfl) .refl)
        for wrong in [[pair], [wordArg n, boolArg choice, unitArg], [unitArg, pair],
            [pair, wordArg 0], [pair, unitArg, unitArg]] do rejected types source wrong
      let _ ← check types "function unused(p: (Word,Bool),u: ()){return ();}" [pair, unitArg]
        .unit .unit .unit 1 (by intro store k; exact .cons .unit .refl)
      let _ ← check types "function single(x: ((Word,)),u: ()) returns((Word)){return x;}" [wordArg n, unitArg]
        (.var 1) .word (w n) 1 (by intro store k; exact .cons (.var rfl) .refl)
      let second : TypedRuntimeArgument :=
        ⟨.product .word .bool, .pair (w (n + 1)) (.bool (!choice)), .pair .word .bool⟩
      let output := Core.Value.pair pair.value second.value
      let outputType := Core.Ty.product pair.type second.type
      let ordered ← check types "function ordered(p: (Word,Bool),q: (Word,Bool),u: ()) returns(((Word,Bool),(Word,Bool))){return (p,q);}"
        [pair, second, unitArg] (.pair (.var 2) (.var 1)) outputType output 5
        (by intro store k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner ordered [pair, second, unitArg] 2 store =
          some (outputType, .outOfFuel ⟨.ret pair.value, [.pairRight (.var 1) [.unit, second.value, pair.value]], store⟩)))
          "same-typed product parameters lost their original identities or order"
      let nested : TypedRuntimeArgument := ⟨.product pair.type .unit, .pair pair.value .unit, .pair pair.valueTyped .unit⟩
      let _ ← check types "function nested(p: ((Word,Bool),())) returns(((Word,Bool),())){return p;}" [nested]
        (.var 0) nested.type nested.value 1 (by intro store k; exact .cons (.var rfl) .refl)
      let bound ← check types "function bound(p: (Word,Bool),u: ()) returns(((Word,Bool),())){let copied: Pair=p;return (copied,u);}"
        [pair, unitArg] (.letE (.var 1) (.pair (.var 0) (.var 1))) nested.type nested.value 8
        (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet
          (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl))))))))
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner bound [pair, unitArg] 2 store = some (nested.type,
          .outOfFuel ⟨.ret pair.value, [.letBody (.pair (.var 0) (.var 1)) [.unit, pair.value]], store⟩)))
          "strict initializer no longer used the original structural parameter"
      let _ ← check types "function branches(p: (Word,Bool),c: (Bool)) returns((Word,Bool)){if(c){return p;}else{let x: Pair=p;return x;}}"
        [pair, boolArg choice] (.ifE (.var 0) (.var 1) (.letE (.var 1) (.var 0))) pair.type pair.value (if choice then 4 else 7)
        (by intro store k; cases choice <;> first
          | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) .refl)))
          | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons .enterLet
              (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))))))
      let migrated ← check types "function stillLet(p: (Word,Bool),c: (Bool)){let x: (Word,Bool)=p;return ();}"
        [pair, boolArg choice] (.letE (.var 1) .unit) .unit .unit 4
        (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .unit .refl))))
      match migrated.value.body.value with
      | ⟨_, .letDecl _ (some original) (some _)⟩ :: _ =>
          let independent ← annotation types original
          assertTrue (decide (independent.type = pair.type)) "migrated original let annotation changed meaning"
          assertTrue (interpretTypeName? types original).isNone "old named-only annotation boundary changed"
      | _ => throw (IO.userError "migrated original structural let disappeared")
      for declaration in ["function unselected(p: (Word,Bool),c: (Bool)) returns((Word,Bool)){if(c){return p;}else{return missing;}}",
          "function unknown(p: (Word,Unknown),c: (Bool)){return ();}",
          "function unsupported(p: (Word,Bool,Word),c: (Bool)){return ();}",
          "function wrongOrder(p: (Bool,Word),c: (Bool)){return ();}",
          "function shadow(p: (Word,Bool),c: (Bool)){let p: Pair=p;return ();}",
          "function multiple(p: (Word,Bool),c: (Bool)) returns(Word,Bool){return p;}"] do
        rejected types (← parsed declaration) [pair, boolArg choice]
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 999, .cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩
  let opaqueArg : TypedRuntimeArgument := ⟨.product cell.type closure.type, .pair cell.value closure.value, .pair cell.valueTyped closure.valueTyped⟩
  let _ ← check types "function opaque(p: (Cell,Fn)) returns((Cell,Fn)){return p;}" [opaqueArg]
    (.var 0) opaqueArg.type opaqueArg.value 1 (by intro store k; exact .cons (.var rfl) .refl)
  let nominal ← parsed "function nominal(p: (N,()),u: ()) returns((N,())){return p;}"
  let nominalTypes := (["N"], Core.Ty.namedData ⟨91⟩) :: types
  assertTrue (decide ((compileRuntimeFunction? nominalTypes owner nominal).map (fun c => (c.core,c.returnType)) =
    some (.var 1, .product (.namedData ⟨91⟩) .unit))) "structural parameter required a nominal inhabitant to compile"
  rejected nominalTypes nominal [wordArg 9, unitArg]
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedStructuralParameters
/-! Complete original parameter lists have independent structural/declaration/binding
certificates. Expected rows and actual values are separate; products are never flattened. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedStructuralParameters
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Parameters", by decide⟩], by decide⟩⟩, 34⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 99 }
private def table : TypeNameTable := [(["Word"], .word), (["Word"], .bool), (["Bool"], .bool),
  (["Unit"], .word), (["Pkg", "Flag"], .bool), (["Pkg.Flag"], .word),
  (["Cell"], .cell .word), (["Fn"], .function .word .word), (["N"], .namedData ⟨91⟩)]
private def w (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (Core.Word.ofNatModulo n), .word⟩
private def b (v : Bool) : TypedRuntimeArgument := ⟨.bool, .bool v, .bool⟩
private def u : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
private def pair (left right : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.product left.type right.type, .pair left.value right.value, .pair left.valueTyped right.valueTyped⟩
private def parsed? (content : String) : IO (Option (Syntax.DelimitedList Syntax.FunctionParameter)) := do
  let file : Syntax.SourceFile := ⟨⟨.main, "structural-parameters.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionParameters (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span = ⟨file.id, 0, content.utf8ByteSize⟩)) "whole parameter range changed"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "parameter parser invariant")
private def parsed (content : String) : IO (Syntax.DelimitedList Syntax.FunctionParameter) := do
  let some source ← parsed? content | throw (IO.userError s!"complete parameters rejected: {content}")
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent named leaf missing")
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [atSource]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← meaning types child
      return ⟨inner.type, by rw [atSource]; exact .single inner.evidence⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let l ← meaning types left; let r ← meaning types right
      return ⟨.product l.type r.type, by rw [atSource]; exact .pair l.evidence r.evidence⟩
  | ⟨span, .tuple (first :: second :: third :: rest)⟩ =>
      let head ← meaning types first; let tail ← meaning types ⟨span, .tuple (second :: third :: rest)⟩
      return ⟨.product head.type tail.type, by rw [atSource]; exact .many head.evidence tail.evidence⟩
  | _ => throw (IO.userError "unsupported independent annotation")
termination_by sizeOf source
private structure Declaration (types : TypeNameTable) (initial : LocalTypeInputs)
    (parameters : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types owner initial parameters inputs
private def declaration (types : TypeNameTable) (initial : LocalTypeInputs)
    (parameters : List Syntax.FunctionParameter) : IO (Declaration types initial parameters) := do
  match atParams : parameters with
  | [] => return ⟨initial, by rw [atParams]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest =>
      let head ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declaration types (initial.bindFresh owner name.value head.type) rest
        return ⟨tail.inputs, by rw [atParams]; exact .cons head.evidence unused tail.evidence⟩
      else throw (IO.userError "independent declaration repeats a name")
  | _ => throw (IO.userError "unsupported independent parameter")
private structure Binding (types : TypeNameTable) (initial : LocalInputs)
    (parameters : List Syntax.FunctionParameter) (arguments : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial parameters arguments inputs
private def binding (types : TypeNameTable) (initial : LocalInputs) (parameters : List Syntax.FunctionParameter)
    (arguments : List TypedRuntimeArgument) : IO (Binding types initial parameters arguments) := do
  match atParams : parameters, atArgs : arguments with
  | [], [] => return ⟨initial, by rw [atParams, atArgs]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest, argument :: args =>
      let head ← meaning types annotation
      if same : head.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← binding types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest args
          return ⟨tail.inputs, by rw [atParams, atArgs]; exact .cons (same ▸ head.evidence) unused tail.evidence⟩
        else throw (IO.userError "independent binding repeats a name")
      else throw (IO.userError "independent actual type mismatch")
  | _, _ => throw (IO.userError "independent shape/arity mismatch")
private def rows (inputs : LocalTypeInputs) : List (String × Resolved.LocalId × Core.Ty) :=
  inputs.bindings.map fun row => (row.name,row.id,row.type)
private def shifted (id : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { id with declarationIndex := id.declarationIndex + 11 }
private theorem injective : Function.Injective shifted := by
  intro a b same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases a; cases b; simp_all [shifted]
private def check (types : TypeNameTable) (content : String) (expected : List (String × Core.Ty))
    (arguments : Option (List TypedRuntimeArgument) := none) : IO Unit := do
  let source ← parsed content
  let original ← declaration types .empty source.elements
  let expectedRows := expected.zipIdx.map fun (row,index) => (row.1,(⟨owner,index⟩ : Resolved.LocalId),row.2)
  assertTrue (decide (rows original.inputs = expectedRows.reverse ∧ source.elements.length = expected.length ∧
    original.inputs.context.values = (expected.map Prod.snd).reverse)) "independent exact declaration/layout mismatch"
  have accepted := RuntimeParametersDeclare.complete original.evidence
  have _ := declareRuntimeParameters?_iff.mpr original.evidence
  assertTrue (decide ((declareRuntimeParameters? types owner source.elements).map rows = some expectedRows.reverse))
    "executable declaration differs from original certificate"
  have _ := (RuntimeParametersDeclare.rows original.evidence).arity
  have _ := original.evidence.generated_ids
  let mapped := RuntimeParametersDeclare.map_owner original.evidence shifted injective
  have _ := mapped.complete
  let extension : TypeNameTable.Extends types (types ++ [(["Word"], .unit)]) :=
    TypeNameTable.Extends.append_right types _
  have _ := declareRuntimeParameters?_some_of_extends extension accepted
  assertTrue (decide ((declareRuntimeParameters? (types ++ [(["Word"], .unit)]) owner source.elements).map rows =
    some expectedRows.reverse)) "later conflicting leaf changed original rows"
  for index in List.range source.elements.length do
    match atParameter : source.elements[index]? with
    | some ⟨span, .typed none name annotation⟩ =>
        have _ := RuntimeParametersDeclare.position original.evidence atParameter
        have _ := (RuntimeParametersDeclare.rows original.evidence).row_at atParameter
        let independent ← meaning types annotation
        have row : RuntimeParameterDeclarationRow types ⟨span, .typed none name annotation⟩
            { name := name.value, id := ⟨owner,index⟩, type := independent.type } := .typed independent.evidence
        have _ := row
        assertTrue (source.span.contains span && span.contains name.span && span.contains annotation.span &&
          decide (original.inputs.context.lookup? ⟨owner,index⟩ = some independent.type ∧
            Resolved.LocalScope.index? original.inputs.ids ⟨owner,index⟩ = some (source.elements.length - 1 - index)))
          "original span, type lookup or reversed Core index changed"
    | _ => throw (IO.userError "accepted original position missing")
  match arguments with
  | none => pure ()
  | some args =>
      let bound ← binding types .empty source.elements args
      have erased := bound.evidence.erase_values
      have _ := original.evidence.result_unique erased
      have _ := RuntimeParametersBind.complete bound.evidence
      if matching : args.map (·.type) = original.inputs.context.values.reverse then
        have _ := RuntimeParametersDeclare.bind_typed_arguments original.evidence args matching
      else throw (IO.userError "typed restoration requires all original argument types")
      assertTrue (decide (rows bound.inputs.toTypeInputs = expectedRows.reverse ∧
        bound.inputs.environment.values = args.reverse.map (·.value) ∧ args.length = expected.length ∧
        (bindRuntimeParameters? types owner source.elements args).map (fun i => (i.names,i.context,i.environment)) =
          some (bound.inputs.names,bound.inputs.context,bound.inputs.environment))) "erasure/order or actual binding changed"
      for index in List.range args.length do
        match atParameter : source.elements[index]?, atArgument : args[index]? with
        | some ⟨span, .typed none name annotation⟩, some argument =>
            have _ := RuntimeParametersBind.position bound.evidence atParameter atArgument
            let independent ← meaning types annotation
            if same : independent.type = argument.type then
              have row : RuntimeParameterRow types ⟨span, .typed none name annotation⟩ argument
                  ⟨name.value,⟨owner,index⟩,argument.type,argument.value,argument.valueTyped⟩ := .typed (same ▸ independent.evidence)
              have _ := row
            else throw (IO.userError "original paired annotation differs from actual value type")
        | _, _ => throw (IO.userError "paired position disappeared")
private def sparse : LocalInputs := ⟨[
  ⟨"old",⟨owner,7⟩,.word,(w 9).value,.word⟩, ⟨"old",⟨owner,2⟩,.bool,.bool false,.bool⟩,
  ⟨"foreign",⟨other,999⟩,.unit,.unit,.unit⟩], by decide⟩
private def checkSparse : IO Unit := do
  let source ← parsed "(p: (Word,Bool), unit: ())"
  let args := [pair (w 9) (b true),u]
  let declared ← declaration table sparse.toTypeInputs source.elements
  let bound ← binding table sparse source.elements args
  have _ := declared.evidence.rows
  have _ := declared.evidence.generated_ids
  have _ := declared.evidence.bindings_length
  have _ := bound.evidence.erase_values
  have _ := declared.evidence.result_unique bound.evidence.erase_values
  have _ := declared.evidence.extend_types (TypeNameTable.Extends.append_right table [(["Word"],.unit)])
  if matching : sparse.context.values.reverse ++ args.map (·.type) = declared.inputs.context.values.reverse then
    have _ := declared.evidence.bind_typed_arguments sparse rfl args matching
  else throw (IO.userError "general retained-prefix restoration type equation failed")
  assertTrue (decide (declared.inputs.ids = [⟨owner,9⟩,⟨owner,8⟩,⟨owner,7⟩,⟨owner,2⟩,⟨other,999⟩] ∧
    declared.inputs.names.map Prod.fst = ["unit","p","old","old","foreign"] ∧
    rows bound.inputs.toTypeInputs = rows declared.inputs ∧
    bound.inputs.environment.values = args.reverse.map (·.value) ++ sparse.environment.values))
    "mixed sparse allocation, duplicate initial names or untouched actual tail changed"
end ParsedStructuralParameters
open ParsedStructuralParameters

def frontendParsedStructuralParameterTests : IO Unit := do
  check table "()" [] (some [])
  for text in ["(x: ())", "(x: (()))", "(x: ((),))"] do check table text [("x",.unit)] (some [u])
  for text in ["(x: (Word))", "(x: (Word,))", "(x: ((Word,),))"] do check table text [("x",.word)] (some [w 9])
  for c in [false,true] do
    let p := pair (w 9) (b c)
    for text in ["(x: (Word,Bool))", "(x: (Word,Bool,),)", "(x: ((Word,),(Bool,)))"] do
      check table text [("x",p.type)] (some [p])
    check table "(a: (), p: (Word,Bool), z: Word)" [("a",.unit),("p",p.type),("z",.word)] (some [u,p,w 2])
    check table "(x: ((Word,Bool),()), y: (Word,(Bool,())))"
      [("x",(pair p u).type),("y",(pair (w 2) (pair (b c) u)).type)] (some [pair p u,pair (w 2) (pair (b c) u)])
  check table "(Unit: Unit, empty: ())" [("Unit",.word),("empty",.unit)] (some [w 9,u])
  check table "(flag: (Pkg /* qualified */ . Flag,Word))" [("flag",.product .bool .word)] (some [pair (b true) (w 2)])
  let cell : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 999,.cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [(w 7).value],
    .closure (.cons .word .nil) (.var rfl)⟩
  check table "(opaque: (Cell,Fn))" [("opaque",(pair cell closure).type)] (some [pair cell closure])
  for type in [Core.Ty.namedData ⟨91⟩, .product (.namedData ⟨73⟩) (.cell .bool), .function .unit (.namedData ⟨4⟩)] do
    for depth in [0,1,3,6] do
      let annotation := (List.range depth).foldl (fun text _ => "((),(" ++ text ++ "))") "N"
      let expected := (List.range depth).foldl (fun inner _ => Core.Ty.product .unit inner) type
      check [(["N"],type)] ("(x: " ++ annotation ++ ")") [("x",expected)]
  checkSparse
  check table "(x: (Word,Bool,Word))" [("x",.product .word (.product .bool .word))]
    (some [pair (w 9) (pair (b true) (w 2))])
  for (text,args) in [("(x: ())",[]), ("(x: ())",[w 9]), ("()",[u]),
      ("(x: (Word,Bool,Word))",[u]),
      ("(x: function(Word) returns(Bool))",[u]),
      ("(x: (Word,Bool))",[w 9,b true]), ("(x: (Word,Bool))",[pair (b true) (w 9)]),
      ("(x: (Word,Bool))",[b true]), ("(x: ((Word,Bool),()))",[pair (w 9) (pair (b true) u)]),
      ("(u: (), w: Word)",[w 9,u]), ("(unused: (N,()))",[pair (w 9) u])] do
    let source ← parsed text
    assertTrue (declareRuntimeParameters? table owner source.elements).isSome "valid static annotation requires no actual value"
    have _ := bindRuntimeParameters?_eq_none_iff (types := table) (owner := owner) (params := source.elements) (args := args)
    assertTrue (bindRuntimeParameters? table owner source.elements args).isNone "missing, flattened or wrongly typed argument accepted"
  for text in ["(x: (), x: ())", "(x: ((),Unknown))", "(x: (Unknown,()))",
      "(x: Word<Bool>)", "(x: (Word,@Bool))", "(x: mapping(Word => Bool))",
      "(comptime x: ())"] do
    let source ← parsed text
    have _ := declareRuntimeParameters?_eq_none_iff (types := table) (owner := owner) (params := source.elements)
    assertTrue (declareRuntimeParameters? table owner source.elements).isNone "unsupported written parameter gained a row"
    assertTrue (bindRuntimeParameters? table owner source.elements [u]).isNone "unsupported actual parameter accepted"
  let missing ← parsed "(x: (Word,New))"
  assertTrue (declareRuntimeParameters? table owner missing.elements).isNone "unknown leaf was already accepted"
  check (table ++ [(["New"],.bool)]) "(x: (Word,New))" [("x",.product .word .bool)] (some [pair (w 9) (b true)])
  let known ← parsed "(x: (Word,Bool))"
  assertTrue (decide ((declareRuntimeParameters? ((["Word"],.unit) :: table) owner known.elements).map
    (fun i => i.context.values) = some [.product .unit .bool])) "first-match override was treated as extension"
  have sameLookup (key : List String) : table.lookup? key = (table ++ table).lookup? key := by
    cases result : table.lookup? key with
    | none =>
        symm
        apply TypeNameTable.lookup?_eq_none_iff.mpr
        simpa only [List.map_append, List.mem_append, not_or] using
          And.intro (TypeNameTable.lookup?_eq_none_iff.mp result)
            (TypeNameTable.lookup?_eq_none_iff.mp result)
    | some type =>
        exact (TypeNameTable.lookup?_iff.mpr
          (TypeNameTable.Extends.append_right table table
            (TypeNameTable.lookup?_iff.mp result))).symm
  have backward : TypeNameTable.Extends (table ++ table) table := by
    intro key type found
    apply TypeNameTable.lookup?_iff.mp
    rw [sameLookup]
    exact TypeNameTable.lookup?_iff.mpr found
  for text in ["(x: (Word,Bool))", "(x: ())", "(x: (Word,Unknown))", "(x: (Word,Bool,Word))"] do
    let source ← parsed text
    have same := declareRuntimeParameters?_eq_of_mutual_extends
      (TypeNameTable.Extends.append_right table table) backward owner source.elements
    have _ := congrArg (Option.map rows) same
    assertTrue (decide ((declareRuntimeParameters? table owner source.elements).map rows =
      (declareRuntimeParameters? (table ++ table) owner source.elements).map rows)) "mutual meaning equivalence lost Some or None"
  for text in ["", "(x)", "(x:)", "(x: ()) trailing", "(x: (Word,,Bool))", "(x: comptime<Word>)"] do
    assertTrue (← parsed? text).isNone "malformed/incomplete source fabricated an annotation"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedStructuralReturns
/-! Complete entries consume original structural return annotations. Independent
annotation/raw-body evidence and fixed Core transition scripts fix all expectations. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace StructuralReturns
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"StructuralReturn", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool),
  (["Unit"], .unit), (["Pair"], .product .word .bool), (["Pkg", "Flag"], .bool),
  (["Cell"], .cell .word), (["Fn"], .function .word .word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "structural-return.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "unexpected lexing diagnostic"
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide (source.span.source = file.id ∧
    source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) && source.span.contains source.value.body.span)
    "original declaration range or completion changed"
  return source
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .group inner⟩ =>
      let child ← expression table env store inner
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .group child.costed⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← expression table env store left
      let second ← expression table env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | _ => throw (IO.userError "expression outside independent unit script")
termination_by sizeOf source
private structure Body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store source value store cost
private def body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) : IO (Body table env store source) := do
  match sourceAt : source with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let first ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let second ← body ((name.value, id) :: table) ((id, first.value) :: env) store ⟨span, rest⟩
      return ⟨second.value, first.cost + second.cost + 2, by rw [sourceAt]; exact .binding first.costed second.costed⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← body table env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← body table env store no
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent guard not Boolean")
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | _ => throw (IO.userError "body outside independent unit script")
termination_by sizeOf source
private structure Annotation (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes types source type
private def annotation (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Annotation types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | none => throw (IO.userError "independent return leaf missing")
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [atSource]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← annotation types child
      return ⟨inner.type, by rw [atSource]; exact .single inner.meaning⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let first ← annotation types left
      let second ← annotation types right
      return ⟨.product first.type second.type, by rw [atSource]; exact .pair first.meaning second.meaning⟩
  | _ => throw (IO.userError "return annotation outside independent script")
termination_by sizeOf source
private structure Return (types : TypeNameTable) (clause : Option Syntax.ReturnClause) where
  type : Core.Ty
  meaning : RuntimeReturnTypeDenotes types clause type
private def returns (types : TypeNameTable) (clause : Option Syntax.ReturnClause) : IO (Return types clause) := do
  match atClause : clause with
  | none => return ⟨.unit, by rw [atClause]; exact .absent⟩
  | some ⟨_, ⟨_, [source]⟩⟩ =>
      let child ← annotation types source
      return ⟨child.type, by rw [atClause]; exact .single child.meaning⟩
  | _ => throw (IO.userError "independent return clause is not singleton")
private def check (types : TypeNameTable) (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (steps : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) : IO Syntax.FunctionDecl := do
  let source ← parsed content
  let declared ← returns types source.value.signature.returnsClause
  assertTrue (decide (declared.type = type)) "independent structural return type differs from fixture"
  have _ := (interpretRuntimeReturnType?_iff).mpr declared.meaning
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError "unit entry did not compile")
  let names ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name annotation := parameter.value | throw (IO.userError "original parameter shape changed")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains annotation.span)
      "original parameter range changed"
    pure name.value
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
    compiled.inputs.context.values = (arguments.map (·.type)).reverse ∧ compiled.inputs.bindings.length = arguments.length))
    "fixed ordered Core/type or original parameter-only layout changed"
  match preparedAt : prepareRuntimeFunction? types owner source arguments with
  | none => throw (IO.userError "unit arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "unit flattened arguments or leaked local bindings into parameter records"
      for store in stores do
        let raw ← body prepared.inputs.names prepared.inputs.environment store source.value.body
        assertTrue (decide (raw.value = value ∧ raw.cost = cost))
          "separate source/Core certificates disagreed with independent fixture"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation raw.costed
        have direct := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, direct⟩
        have _ := independent.cost_le_fuelBound
        have _ := (steps store []).runStateful_done_iff (fuel := cost)
        assertTrue (decide (evaluateRuntimeFunctionWithCost? types owner source arguments = some (type, value, cost))) "entry triple changed"
        let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
        let start := Core.State.initial core (arguments.reverse.map (·.value)) store
        for fuel in List.range (cost + 3) do
          have _ := independent.run_done_iff (fuel := fuel)
          have _ := independent.run_outOfFuel_iff (fuel := fuel)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel start))) "entry changed fixed Core or full checkpoint"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "entry threshold, ordered value or own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "entry residual path changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "actual remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart pretended to resume"
          | _ => throw (IO.userError "below-cost entry checkpoint missing")
  return source
private def rejected (types : TypeNameTable) (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid unit gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid unit gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid unit gate exposed a checkpoint"
end StructuralReturns
open StructuralReturns

def frontendParsedStructuralReturnTests : IO Unit := do
  for declaration in ["function unit() returns(()){return ();}",
      "function groupUnit() returns((())){return ();}", "function bare() returns(()){return;}"] do
    let _ ← check [] declaration [] .unit .unit .unit 1 (by intro store k; exact .cons .unit .refl)
  let _ ← check [(["Unit"], .word)] "function notReserved() returns(()){return ();}" [] .unit .unit .unit 1
    (by intro store k; exact .cons .unit .refl)
  for n in [0, 9, Core.wordModulus - 1] do
    for choice in [false, true] do
      let arguments := [wordArg n, boolArg choice]
      let pairType := Core.Ty.product .word .bool
      let value := Core.Value.pair (w n) (.bool choice)
      for annotation in ["(Word,Bool)", "((Word),(Bool,))", "(Word,Bool,)"] do
        let source ← check types ("function pair(x: Word,c: Bool) returns(" ++ annotation ++ "){return (x,c);}")
          arguments (.pair (.var 1) (.var 0)) pairType value 5
          (by intro store k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
            (.cons (.var rfl) (.cons .applyPair .refl)))))
        for store in stores do
          assertTrue (decide (runRuntimeFunction? types owner source arguments 2 store = some (pairType,
            .outOfFuel ⟨.ret (w n), [.pairRight (.var 0) [.bool choice, w n]], store⟩)))
            "structural annotation changed the original parameter environment checkpoint"
        for wrong in [[], [wordArg n], [boolArg choice, wordArg n], [wordArg n, boolArg choice, wordArg 0]] do
          rejected types source wrong
      let _ ← check types "function reversed(x: Word,c: Bool) returns((Bool,Word)){return (c,x);}" arguments
        (.pair (.var 0) (.var 1)) (.product .bool .word) (.pair (.bool choice) (w n)) 5
        (by intro store k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
          (.cons (.var rfl) (.cons .applyPair .refl)))))
      for annotation in ["(Word)", "((Word,))"] do
        let _ ← check types ("function single(x: Word,c: Bool) returns(" ++ annotation ++ "){return x;}") arguments
          (.var 1) .word (w n) 1 (by intro store k; exact .cons (.var rfl) .refl)
      let _ ← check types "function qualified(x: Word,c: Bool) returns((Pkg.Flag)){return c;}" arguments
        (.var 0) .bool (.bool choice) 1 (by intro store k; exact .cons (.var rfl) .refl)
      let _ ← check types "function nested(x: Word,c: Bool) returns(((Word,Bool),Word)){return ((x,c),x);}" arguments
        (.pair (.pair (.var 1) (.var 0)) (.var 1)) (.product pairType .word) (.pair value (w n)) 9
        (by intro store k; exact .cons .enterPair (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
          (.cons (.var rfl) (.cons .applyPair (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))))))
      let bound ← check types "function bound(x: Word,c: Bool) returns(((Word,Bool),Word)){let p: Pair=(x,c);return (p,x);}" arguments
        (.letE (.pair (.var 1) (.var 0)) (.pair (.var 0) (.var 2))) (.product pairType .word) (.pair value (w n)) 12
        (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
          (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons .enterPair (.cons (.var rfl)
            (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl))))))))))))
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner bound arguments 6 store = some (.product pairType .word,
          .outOfFuel ⟨.ret value, [.letBody (.pair (.var 0) (.var 2)) [.bool choice, w n]], store⟩)))
          "named strict let stopped retaining its two binding steps"
      let _ ← check types "function branches(x: Word,c: Bool) returns((Word,Bool)){if(c){return (x,c);}else{let p: Pair=(x,c);return p;}}" arguments
        (.ifE (.var 0) (.pair (.var 1) (.var 0)) (.letE (.pair (.var 1) (.var 0)) (.var 0))) pairType value (if choice then 8 else 11)
        (by intro store k; cases choice <;> first
          | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .enterPair (.cons (.var rfl)
              (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))))
          | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons .enterLet (.cons .enterPair
              (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair
                (.cons .bindLet (.cons (.var rfl) .refl)))))))))))
      for declaration in ["function empty(x: Word,c: Bool) returns(){return (x,c);}",
          "function multiple(x: Word,c: Bool) returns(Word,Bool){return (x,c);}",
          "function wrongOrder(x: Word,c: Bool) returns((Bool,Word)){return (x,c);}",
          "function wrongAssociation(x: Word,c: Bool) returns((Word,(Bool,Word))){return ((x,c),x);}",
          "function unknown(x: Word,c: Bool) returns((Word,Unknown)){return (x,c);}",
          "function many(x: Word,c: Bool) returns((Word,Bool,Word)){return ((x,c),x);}",
          "function unselected(x: Word,c: Bool) returns((Word,Bool)){if(c){return (x,c);}else{return (missing,c);}}"] do
        let source ← parsed declaration
        rejected types source arguments
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 999, .cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩
  let _ ← check types "function opaque(x: Cell,f: Fn) returns((Cell,Fn)){return (x,f);}" [cell, closure]
    (.pair (.var 1) (.var 0)) (.product cell.type closure.type) (.pair cell.value closure.value) 5
    (by intro store k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))
  let nominal ← parsed "function nominal(x: N,c: Bool) returns((N,Bool)){return (x,c);}"
  let nominalTypes := (["N"], Core.Ty.namedData ⟨91⟩) :: types
  assertTrue (decide ((compileRuntimeFunction? nominalTypes owner nominal).map (fun c => (c.core,c.returnType)) =
    some (.pair (.var 1) (.var 0), .product (.namedData ⟨91⟩) .bool))) "static structural result required a nominal inhabitant"
  rejected nominalTypes nominal [wordArg 9, boolArg true]
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedStructuralTypes
/-! Complete types carry independent meaning. One structural return annotation
parameters and recursive lets execute; old named-only and prefix adapters remain unchanged. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedStructuralTypes
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def file (content : String) : Syntax.SourceFile := ⟨⟨.main, "structural-type.sol"⟩, content⟩
private def parsed? (content : String) : IO (Option Syntax.TypeExpr) := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file content) lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span = ⟨(file content).id, 0, content.utf8ByteSize⟩)) "complete original type range changed"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "type parser invariant")
private def parsed (content : String) : IO Syntax.TypeExpr := do
  let some source ← parsed? content | throw (IO.userError s!"incomplete type: {content}")
  return source
private structure Certificate (table : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes table source type
private def certify (table : TypeNameTable) (source : Syntax.TypeExpr) : IO (Certificate table source) := do
  match sourceAt : source with
  | ⟨_, .named name none⟩ =>
      match found : table.lookup? (qualifiedTypeNameKey name) with
      | none => throw (IO.userError "independent name missing")
      | some type => return ⟨type, by rw [sourceAt]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← certify table child
      return ⟨inner.type, by rw [sourceAt]; exact .single inner.meaning⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let first ← certify table left; let second ← certify table right
      return ⟨.product first.type second.type, by rw [sourceAt]; exact .pair first.meaning second.meaning⟩
  | ⟨span, .tuple (first :: second :: third :: rest)⟩ =>
      let head ← certify table first; let tail ← certify table ⟨span, .tuple (second :: third :: rest)⟩
      return ⟨.product head.type tail.type, by rw [sourceAt]; exact .many head.meaning tail.meaning⟩
  | _ => throw (IO.userError "outside independent structural certificate")
termination_by sizeOf source
private def checked (content : String) (table : TypeNameTable) (expected : Core.Ty) : IO Syntax.TypeExpr := do
  let source ← parsed content
  let independent ← certify table source
  assertTrue (decide (independent.type = expected)) "independent ordered type differs from fixture"
  have accepted := independent.meaning.complete
  have _ := interpretStructuralType?_sound accepted
  have _ := interpretStructuralType?_iff.mpr independent.meaning
  have _ := independent.meaning.type_unique (interpretStructuralType?_sound accepted)
  assertTrue (decide (interpretStructuralType? table source = some expected)) "structural interpretation differs from fixture"
  match source.value with
  | .named _ none =>
      assertTrue (decide (interpretTypeName? table source = some expected)) "named-only compatibility changed"
  | _ => assertTrue (interpretTypeName? table source).isNone "old named-only scope silently broadened"
  let otherSpan : Syntax.SourceSpan := ⟨⟨.external "unrelated", "raw"⟩, 92, 1⟩
  have _ := interpretStructuralType?_span table source otherSpan
  assertTrue (decide (interpretStructuralType? table { source with span := otherSpan } = some expected)) "meaning required outer range validity"
  let extras : TypeNameTable := [(["Word"], .unit), (["Unknown"], .bool)]
  have extended := independent.meaning.extend_types (TypeNameTable.Extends.append_right table extras)
  have _ := interpretStructuralType?_some_of_extends (TypeNameTable.Extends.append_right table extras) accepted
  assertTrue (decide (interpretStructuralType? (table ++ extras) source = some expected)) "later duplicates overrode an accepted nested leaf"
  have _ := extended.complete; return source
private def table : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["PairAlias"], .product .word .bool), (["Pkg", "Flag"], .bool), (["Pkg.Flag"], .word)]
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TypeGate", by decide⟩], by decide⟩⟩, 23⟩
private def w : TypedRuntimeArgument := ⟨.word, .word (Core.Word.ofNatModulo 9), .word⟩
private def b : TypedRuntimeArgument := ⟨.bool, .bool true, .bool⟩
private def u : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
private def p : TypedRuntimeArgument := ⟨.product .word .bool, .pair w.value b.value, .pair .word .bool⟩
private def declaration (content : String) : IO Syntax.FunctionDecl := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "entry lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial (file content) lexed)
    | throw (IO.userError "complete gate declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && lexed.diagnostics.isEmpty &&
    decide (source.span = ⟨(file content).id, 0, content.utf8ByteSize⟩)) "gate source lost original completion or range"
  return source
private structure Raw (inputs : LocalInputs) (store : Core.Store) (source : Syntax.Expr) where
  type : Core.Ty
  value : Core.Value
  cost : Nat
  typing : LocalExpressionHasType inputs.names inputs.context source type
  costed : LocalExpressionEvaluatesWithCost inputs.names inputs.environment store source value store cost
private def raw (inputs : LocalInputs) (store : Core.Store) (source : Syntax.Expr) : IO (Raw inputs store source) := do
  match sourceAt : source with
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, .unit, 1, by rw [sourceAt]; exact .unit, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | none => throw (IO.userError "independent source name missing")
      | some id =>
          match found : inputs.environment.lookup? id, typed : inputs.context.lookup? id with
          | some value, some type => return ⟨type, value, 1,
              by rw [sourceAt]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp typed),
              by rw [sourceAt]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _, _ => throw (IO.userError "independent actual value/type missing")
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← raw inputs store left; let second ← raw inputs store right
      return ⟨.product first.type second.type, .pair first.value second.value, first.cost + second.cost + 3,
        by rw [sourceAt]; exact .pair first.typing second.typing,
        by rw [sourceAt]; exact .pair first.costed second.costed⟩
  | _ => throw (IO.userError "outside independent migrated expression script")
termination_by sizeOf source
private structure Script (inputs : LocalInputs) (store : Core.Store) (body : Syntax.Block) where
  type : Core.Ty
  value : Core.Value
  cost : Nat
  typing : TypedLetReturnTreeHasType table owner inputs.toTypeInputs body type
  costed : TypedLetReturnTreeEvaluatesWithCost owner inputs.names inputs.environment store body value store cost
private def script (inputs : LocalInputs) (store : Core.Store) (body : Syntax.Block) : IO (Script inputs store body) := do
  match bodyAt : body with
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← raw inputs store operand
      return ⟨child.type, child.value, child.cost, by rw [bodyAt]; exact .single (.expression (by simpa only [LocalInputs.toTypeInputs_names, LocalInputs.toTypeInputs_context] using child.typing)),
        by rw [bodyAt]; exact .single (.expression child.costed)⟩
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ =>
      let declared ← certify table annotation
      assertTrue (interpretTypeName? table annotation).isNone "old named-only let annotation gained meaning"
      let child ← raw inputs store initializer
      if same : child.type = declared.type then
        if unused : name.value ∉ inputs.names.map Prod.fst then
          let valueTyped := (child.costed.erase.preserves_type child.typing inputs.sameIds inputs.environmentTyped).1
          let tail ← script (inputs.bindFresh owner name.value child.type child.value valueTyped) store ⟨blockSpan, rest⟩
          return ⟨tail.type, tail.value, child.cost + tail.cost + 2, by
            rw [bodyAt]; exact .binding (same.symm ▸ declared.meaning) (by simpa only [LocalInputs.toTypeInputs_names] using unused) (by simpa only [LocalInputs.toTypeInputs_names, LocalInputs.toTypeInputs_context] using child.typing)
              (by simpa only [LocalInputs.toTypeInputs_bindFresh] using tail.typing), by
            rw [bodyAt]; apply TypedLetReturnTreeEvaluatesWithCost.binding child.costed
            simpa only [LocalInputs.bindFresh_names, LocalInputs.bindFresh_environment,
              LocalInputs.names, LocalInputs.ids, LocalInputs.bindFresh_bindings, List.map_cons, List.map_map, Function.comp_def] using tail.costed⟩
        else throw (IO.userError "independent let reused an existing spelling")
      else throw (IO.userError "independent initializer type disagrees with its written annotation")
  | _ => throw (IO.userError "outside independent migrated body script")
termination_by sizeOf body
private structure Declared (initial : LocalTypeInputs) (parameters : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom table owner initial parameters inputs
private def declared (initial : LocalTypeInputs) (parameters : List Syntax.FunctionParameter) : IO (Declared initial parameters) := do
  match parametersAt : parameters with
  | [] => return ⟨initial, by rw [parametersAt]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest =>
      let certificate ← certify table annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declared (initial.bindFresh owner name.value certificate.type) rest
        return ⟨tail.inputs, by rw [parametersAt]; exact .cons certificate.meaning unused tail.evidence⟩
      else throw (IO.userError "original parameter spelling repeated")
  | _ => throw (IO.userError "unsupported original parameter shape")
private def checkedReturn (content : String) (arguments : List TypedRuntimeArgument)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (path : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) (structuralReturn : Bool := true) (structuralLet : Bool := false) : IO Unit := do
  let source ← declaration content
  let returnsMeaning : PLift (RuntimeReturnTypeDenotes table source.value.signature.returnsClause type) ←
    match returnsAt : source.value.signature.returnsClause with
    | none =>
        if same : type = .unit then pure ⟨by rw [returnsAt, same]; exact .absent⟩
        else throw (IO.userError "absent return must have Unit type")
    | some ⟨_, ⟨_, [annotation]⟩⟩ =>
        let independent ← certify table annotation
        if same : independent.type = type then
          if structuralReturn then
            assertTrue (interpretTypeName? table annotation).isNone "old named-only type adapter broadened"
          pure ⟨by rw [returnsAt]; exact .single (same ▸ independent.meaning)⟩
        else throw (IO.userError "independent structural return type differs from fixture")
    | _ => throw (IO.userError "expected exactly one return annotation")
  if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
      source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
    have header : RuntimeFunctionHeader table source.value.signature type :=
      ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, returnsMeaning.down⟩
    have _ := interpretRuntimeFunctionHeader?_iff.mpr header
  else throw (IO.userError "independent header policy not satisfied")
  let independent ← declared .empty source.value.signature.parameters.elements
  have _ := RuntimeParametersDeclare.complete independent.evidence
  if !structuralReturn && !structuralLet then
    for parameter in source.value.signature.parameters.elements do
      let .typed none _ annotation := parameter.value | throw (IO.userError "parameter shape changed")
      assertTrue (interpretTypeName? table annotation).isNone "old named-only parameter meaning broadened"
  let expectedNames ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name _ := parameter.value | throw (IO.userError "parameter shape changed")
    pure name.value
  let expected := (expectedNames.zip arguments).zipIdx.map fun (entry, index) =>
    (entry.1, (⟨owner, index⟩ : Resolved.LocalId), entry.2.type)
  assertTrue (decide (independent.inputs.bindings.map (fun row => (row.name,row.id,row.type)) = expected.reverse ∧
    expectedNames.length = arguments.length)) "one original parameter no longer has one exact row/argument"
  let some compiled := compileRuntimeFunction? table owner source | throw (IO.userError "structural return did not compile")
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = independent.inputs.names ∧ compiled.inputs.context = independent.inputs.context)) "migrated return changed fixed Core/type"
  match preparedAt : prepareRuntimeFunction? table owner source arguments with
  | none => throw (IO.userError "original actual arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧
        prepared.inputs.names = compiled.inputs.names ∧ prepared.inputs.context = compiled.inputs.context ∧
        prepared.inputs.bindings.length = source.value.signature.parameters.elements.length ∧
        prepared.inputs.environment.values = arguments.reverse.map (·.value))) "original argument layout changed"
      if structuralLet then
        assertTrue (prepared.inputs.checkTypedLetReturnBody? table owner source.value.body).isNone "old prefix adapter gained structural lets"
      for store in [[], [w.value, .cellRef .word 99]] do
        let original ← script prepared.inputs store source.value.body
        assertTrue (decide (original.type = type ∧ original.value = value ∧ original.cost = cost)) "independent source type/value/cost changed"
        let costed := RuntimeFunctionEvaluatesWithCost.intro preparation original.costed
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp costed).2
        have _ := (path store []).runStateful_done_iff (fuel := cost)
        assertTrue (decide (evaluateRuntimeFunctionWithCost? table owner source arguments = some (type, value, cost)))
          "whole direct return differs from independent fixture"
        for fuel in List.range (cost + 3) do
          if structuralLet then assertTrue (prepared.inputs.runTypedLetReturnBody? table owner fuel source.value.body store).isNone "old prefix runner gained structural lets"
          have _ := costed.run_done_iff (fuel := fuel)
          assertTrue (match runRuntimeFunction? table owner source arguments fuel store with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "migrated return changed threshold or own store"
        for spent in List.range cost do
          match exhausted : runRuntimeFunction? table owner source arguments spent store with
          | some (t, .outOfFuel checkpoint) =>
              have _ := runRuntimeFunction?_resume exhausted (cost - spent)
              assertTrue (decide (t = type ∧ Core.runStateful (cost - spent) checkpoint = .done value store))
                "migrated return lost its genuine remaining path"
          | _ => throw (IO.userError "migrated return checkpoint missing")
end ParsedStructuralTypes
open ParsedStructuralTypes
def frontendParsedStructuralTypeTests : IO Unit := do
  for (left, right) in [(Core.Ty.word, Core.Ty.bool), (.namedData ⟨83⟩, .cell .word),
      (.function .word .bool, .product .unit .bool)] do
    let caller : TypeNameTable := [(["Word"], left), (["Word"], .unit), (["Bool"], right)]
    for text in ["Word", "(Word)", "(Word,)", "((Word,),)"] do let _ ← checked text caller left
    for text in ["()", "(())", "((),)"] do let _ ← checked text caller .unit
    for text in ["(Word,Bool)", "(Word,Bool,)", "((Word,),(Bool,),)"] do let _ ← checked text caller (.product left right)
    let _ ← checked "(Bool,Word)" caller (.product right left)
    let _ ← checked "((Word,Bool),())" caller (.product (.product left right) .unit)
    let _ ← checked "(Word,(Bool,()))" caller (.product left (.product right .unit))
    for depth in [0, 1, 3, 6] do
      let text := (List.range depth).foldl (fun inner _ => "((),(" ++ inner ++ "),)") "Word"
      let expected := (List.range depth).foldl (fun inner _ => Core.Ty.product .unit inner) left
      let _ ← checked text caller expected
    for text in ["Unknown", "(Word,Unknown)", "(Unknown,())", "((Unknown),)", "((),(Word,Unknown))"] do
      let source ← parsed text
      assertTrue (interpretStructuralType? caller source).isNone "missing written leaf received a fallback or was skipped"
  let _ ← checked "(Pkg /* first */ . Flag, Word)" table (.product .bool .word)
  let _ ← checked "(PairAlias,())" table (.product (.product .word .bool) .unit)
  let _ ← checked "((),())" [] (.product .unit .unit)
  let singleton ← parsed "(Word,)"
  assertTrue (match singleton.value with
    | .tuple [⟨span, .named name none⟩] => decide (span.startByte = 1 ∧ span.endByte = 5 ∧ qualifiedTypeNameKey name = ["Word"])
    | _ => false) "type singleton was rewritten into expression grouping"
  let nested ← parsed "((Word,Bool),())"
  assertTrue (match nested.value with
    | .tuple [⟨leftSpan, .tuple [left, right]⟩, ⟨unitSpan, .tuple []⟩] =>
        nested.span.contains leftSpan && leftSpan.contains left.span && leftSpan.contains right.span &&
        nested.span.contains unitSpan && decide (left.span.endByte < right.span.startByte ∧ leftSpan.endByte < unitSpan.startByte)
    | _ => false) "original nested associations or child ranges changed"
  let _ ← checked "(Word,Bool,Word)" table (.product .word (.product .bool .word))
  let _ ← checked "((),(),(),())" table (.product .unit (.product .unit (.product .unit .unit)))
  for text in ["Word<Bool>", "(Word<Bool>)",
      "mapping(Word => Bool)", "@Word", "comptime<Word>",
      "((),@Word)", "(function() returns(),Word)"] do
    let source ← parsed text
    assertTrue (interpretStructuralType? table source).isNone "unsupported written constructor gained meaning"
  let missing ← parsed "(Word,New)"
  assertTrue (interpretStructuralType? table missing).isNone "unknown structural child already accepted"
  let _ ← checked "(Word,New)" (table ++ [(["New"], .bool)]) (.product .word .bool)
  let known ← parsed "(Word,Bool)"
  assertTrue (decide (interpretStructuralType? ((["Word"], .unit) :: table) known = some (.product .unit .bool)))
    "first-match meaning-changing shadowing was ignored"
  have sameLookup (key : List String) : table.lookup? key = (table ++ table).lookup? key := by
    cases result : table.lookup? key with
    | none =>
        symm
        apply TypeNameTable.lookup?_eq_none_iff.mpr
        simpa only [List.map_append, List.mem_append, not_or] using
          And.intro (TypeNameTable.lookup?_eq_none_iff.mp result)
            (TypeNameTable.lookup?_eq_none_iff.mp result)
    | some type =>
        exact (TypeNameTable.lookup?_iff.mpr
          (TypeNameTable.Extends.append_right table table
            (TypeNameTable.lookup?_iff.mp result))).symm
  for text in ["(Word,Bool)", "(Word,Unknown)", "()", "(Word,Bool,Word)"] do
    let source ← parsed text
    have _ := interpretStructuralType?_congr_lookup table (table ++ table) sameLookup source
    assertTrue (decide (interpretStructuralType? table source = interpretStructuralType? (table ++ table) source))
      "duplicate-suffix lookup-equivalent tables changed the full optional result"
  checkedReturn "function unitParam(x: ()){return ();}" [u] .unit .unit .unit 1
    (by intro store k; exact .cons .unit .refl) false
  checkedReturn "function pairParam(x: (Word,Bool)){return ();}" [p] .unit .unit .unit 1
    (by intro store k; exact .cons .unit .refl) false
  checkedReturn "function singleParam(x: (Word)) returns(Word){return x;}" [w] (.var 0) .word w.value 1
    (by intro store k; exact .cons (.var rfl) .refl) false
  checkedReturn "function unitReturn() returns(()){return ();}" [] .unit .unit .unit 1
    (by intro store k; exact .cons .unit .refl)
  checkedReturn "function pairReturn(x: Word,c: Bool) returns((Word,Bool)){return (x,c);}" [w,b]
    (.pair (.var 1) (.var 0)) (.product .word .bool) (.pair w.value b.value) 5
    (by intro store k; exact .cons .enterPair (.cons (.var rfl)
      (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))
  checkedReturn "function singleReturn(x: Word) returns((Word)){return x;}" [w] (.var 0) .word w.value 1
    (by intro store k; exact .cons (.var rfl) .refl)
  checkedReturn "function unitLet(){let x: ()=();return x;}" [] (.letE .unit (.var 0)) .unit .unit 4
    (by intro store k; exact .cons .enterLet (.cons .unit (.cons .bindLet (.cons (.var rfl) .refl)))) false true
  checkedReturn "function pairLet(x: Word,c: Bool) returns(PairAlias){let p: (Word,Bool)=(x,c);return p;}" [w,b]
    (.letE (.pair (.var 1) (.var 0)) (.var 0)) (.product .word .bool) (.pair w.value b.value) 8
    (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
      (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons (.var rfl) .refl)))))))) false true
  for text in ["", "(", "Word Bool", "(Word,,Bool)", "(Word,Bool))", "(,)", "Word<>"] do
    assertTrue (← parsed? text).isNone s!"incomplete or malformed type accepted: {text}"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedUnitEntries
/-! Complete original Unit entries keep header/argument gates and strict bindings.
Original-source certificates and explicitly written Core paths are independent. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace UnitEntries
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"UnitEntry", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool),
  (["Unit"], .unit), (["UnitAlias"], .unit), (["UnitPair"], .product .unit .unit)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "unit-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "unexpected lexing diagnostic"
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide (source.span.source = file.id ∧
    source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) && source.span.contains source.value.body.span)
    "original declaration range or completion changed"
  return source
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .group inner⟩ =>
      let child ← expression table env store inner
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .group child.costed⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← expression table env store left
      let second ← expression table env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | _ => throw (IO.userError "expression outside independent unit script")
termination_by sizeOf source
private structure Body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store source value store cost
private def body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) : IO (Body table env store source) := do
  match sourceAt : source with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let first ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let second ← body ((name.value, id) :: table) ((id, first.value) :: env) store ⟨span, rest⟩
      return ⟨second.value, first.cost + second.cost + 2, by rw [sourceAt]; exact .binding first.costed second.costed⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← body table env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← body table env store no
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent guard not Boolean")
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | _ => throw (IO.userError "body outside independent unit script")
termination_by sizeOf source
private def check (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (steps : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) : IO Syntax.FunctionDecl := do
  let source ← parsed content
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError "unit entry did not compile")
  let names ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name annotation := parameter.value | throw (IO.userError "original parameter shape changed")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains annotation.span)
      "original parameter range changed"
    pure name.value
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
    compiled.inputs.context.values = (arguments.map (·.type)).reverse ∧ compiled.inputs.bindings.length = arguments.length))
    "fixed ordered Core/type or original parameter-only layout changed"
  match preparedAt : prepareRuntimeFunction? types owner source arguments with
  | none => throw (IO.userError "unit arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "unit flattened arguments or leaked local bindings into parameter records"
      for store in stores do
        let raw ← body prepared.inputs.names prepared.inputs.environment store source.value.body
        assertTrue (decide (raw.value = value ∧ raw.cost = cost))
          "separate source/Core certificates disagreed with independent fixture"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation raw.costed
        have direct := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, direct⟩
        have _ := independent.cost_le_fuelBound
        have _ := (steps store []).runStateful_done_iff (fuel := cost)
        assertTrue (decide (evaluateRuntimeFunctionWithCost? types owner source arguments = some (type, value, cost))) "entry triple changed"
        let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
        let start := Core.State.initial core (arguments.reverse.map (·.value)) store
        for fuel in List.range (cost + 3) do
          have _ := independent.run_done_iff (fuel := fuel)
          have _ := independent.run_outOfFuel_iff (fuel := fuel)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel start))) "entry changed fixed Core or full checkpoint"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "entry threshold, ordered value or own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "entry residual path changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "actual remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart pretended to resume"
          | _ => throw (IO.userError "below-cost entry checkpoint missing")
  return source
private def rejected (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid unit gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid unit gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid unit gate exposed a checkpoint"
end UnitEntries
open UnitEntries

def frontendParsedUnitEntryTests : IO Unit := do
  for declaration in ["function empty(){return ();}",
      "function alias() returns(UnitAlias){return ();}",
      "function emptyType() returns(()){return ();}",
      "function grouped(){return (());}", "function trailing(){return ((),);}"] do
    let source ← check declaration [] .unit .unit .unit 1 (by intro store k; exact .cons .unit .refl)
    for store in stores do
      assertTrue (decide (runRuntimeFunction? types owner source [] 0 store = some (.unit,
        .outOfFuel (Core.State.initial .unit [] store)) ∧
        runRuntimeFunction? types owner source [] 1 store = some (.unit, .done .unit store)))
        "constant entry did not use exactly one Core step"
  let bare ← check "function bare(){return;}" [] .unit .unit .unit 1 (by intro store k; exact .cons .unit .refl)
  let explicit ← parsed "function explicit(){return ();}"
  assertTrue (match bare.value.body.value, explicit.value.body.value with
    | [⟨_, .returnStmt none⟩], [⟨_, .returnStmt (some ⟨_, .tuple ⟨_, []⟩⟩)⟩] => true
    | _, _ => false)
    "bare return and explicit original tuple syntax were identified"
  let boundCore : Core.Expr := .letE .unit (.var 0)
  let bound ← check "function bound() returns(Unit){let u: Unit=();return u;}" [] boundCore .unit .unit 4
    (by intro store k; exact .cons .enterLet (.cons .unit (.cons .bindLet (.cons (.var rfl) .refl))))
  for store in stores do
    assertTrue (decide (runRuntimeFunction? types owner bound [] 2 store = some (.unit,
      .outOfFuel ⟨.ret .unit, [.letBody (.var 0) []], store⟩) ∧
      runRuntimeFunction? types owner bound [] 3 store = some (.unit,
      .outOfFuel ⟨.eval (.var 0) [.unit], [], store⟩))) "strict Unit binding skipped a transition"
  let unitPair : Core.Ty := .product .unit .unit
  let pairValue : Core.Value := .pair .unit .unit
  let pair ← check "function pair() returns(UnitPair){return ((),());}" [] (.pair .unit .unit) unitPair pairValue 5
    (by intro store k; exact .cons .enterPair (.cons .unit (.cons .enterPairRight (.cons .unit (.cons .applyPair .refl)))))
  for store in stores do
    assertTrue (decide (runRuntimeFunction? types owner pair [] 2 store = some (unitPair,
      .outOfFuel ⟨.ret .unit, [.pairRight .unit []], store⟩) ∧
      runRuntimeFunction? types owner pair [] 4 store = some (unitPair,
      .outOfFuel ⟨.ret .unit, [.pairApply .unit], store⟩))) "pair of units was flattened or lost its continuation"
  let _ ← check "function boundPair() returns(UnitPair){let u: Unit=();return (u,());}" []
    (.letE .unit (.pair (.var 0) .unit)) unitPair pairValue 8
    (by intro store k; exact .cons .enterLet (.cons .unit (.cons .bindLet (.cons .enterPair
      (.cons (.var rfl) (.cons .enterPairRight (.cons .unit (.cons .applyPair .refl))))))))
  for n in [0, 9, Core.wordModulus - 1] do
    for choice in [false, true] do
      let arguments := [wordArg n, boolArg choice]
      let unused ← check "function unused(x: Word,c: Bool) returns(UnitAlias){return ();}" arguments .unit .unit .unit 1
        (by intro store k; exact .cons .unit .refl)
      for wrong in [[], [wordArg n], [boolArg choice, wordArg n], [wordArg n, boolArg choice, wordArg 0]] do rejected unused wrong
      let _ ← check "function named(Unit: Word) returns(Word){return Unit;}" [wordArg n] (.var 0) .word (w n) 1
        (by intro store k; exact .cons (.var rfl) .refl)
      let _ ← check "function branches(c: Bool) returns(Unit){if(c){return ();}else{let u: Unit=();return u;}}"
        [boolArg choice] (.ifE (.var 0) .unit boundCore) .unit .unit (if choice then 4 else 7)
        (by intro store k; cases choice <;>
            first
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .unit .refl)))
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse
                (.cons .enterLet (.cons .unit (.cons .bindLet (.cons (.var rfl) .refl)))))))
  for declaration in ["function wrong() returns(Word){return ();}",
      "function unknown() returns(Unknown){return ();}", "function emptyHeader() returns(){return ();}",
      "function many() returns(Unit,Unit){return ();}",
      "function unknownUnused(x: Unknown){return ();}",
      "function unselected(c: Bool){if(c){return ();}else{return missing;}}"] do
    let source ← parsed declaration
    let arguments := if declaration.startsWith "function unselected" then [boolArg true] else []
    let table := if arguments.isEmpty then [] else [("c", (⟨owner, 0⟩ : Resolved.LocalId))]
    let env := if arguments.isEmpty then [] else [(⟨owner, 0⟩, Core.Value.bool true)]
    for store in stores do
      let raw ← body table env store source.value.body
      assertTrue (decide (raw.value = .unit ∧ raw.cost = if arguments.isEmpty then 1 else 4))
        "entry gate rejection lost independently successful raw Unit"
    if declaration.startsWith "function unknownUnused" then rejected source [wordArg 0]
    else rejected source arguments
  let overridden ← parsed "function overridden() returns(Unit){return ();}"
  let overrideTypes : TypeNameTable := [(["Unit"], .word)]
  assertTrue (compileRuntimeFunction? overrideTypes owner overridden).isNone "Unit alias was silently reserved"
  assertTrue (evaluateRuntimeFunctionWithCost? overrideTypes owner overridden []).isNone "Unit alias bypassed return typing"
  for declaration in ["function noFlatten() returns(Unit){return ((),());}",
      "function inferred(){return ((),());}", "function noAlias() returns(MissingUnit){return ();}"] do
    let source ← parsed declaration
    rejected source []
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedUnits
/-! Completely parsed empty tuples, separate nullary/binary products, and
independent transition certificates. Constant leaves need no runtime alignment. -/
set_option autoImplicit false
namespace Tests
namespace ParsedUnits
open Solcore Solcore.Frontend
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedUnit", by decide⟩], by decide⟩⟩, 23⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def stores : List Core.Store := [[], [w 42, .cellRef .word 999, .bool false]]
private def file (content : String) : Syntax.SourceFile := ⟨⟨.main, "empty-tuples.sol"⟩, content⟩
private def parsed? (content : String) : IO (Option Syntax.Expr) := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.expression (Syntax.Parser.State.initial (file content) lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span = ⟨(file content).id, 0, content.utf8ByteSize⟩)) "original complete byte range changed"
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")
private def parsed (content : String) : IO Syntax.Expr := do
  let some source ← parsed? content | throw (IO.userError s!"incomplete expression: {content}")
  return source
private structure Certificate (table : LocalNameTable) (context : Resolved.Context)
    (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  resolution : ResolvesLocalExpression table source resolved
  lowered : Resolved.Lowers context.ids resolved core
  typing : LocalExpressionHasType table context source type
  raw : LocalExpressionEvaluatesWithCost table environment store source value store cost
  paths : ∀ k, Core.Steps cost ⟨.eval core environment.values, k, store⟩ ⟨.ret value, k, store⟩
private def certify (table : LocalNameTable) (context : Resolved.Context) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) : IO (Certificate table context environment store source) := do
  match sourceAt : source with
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, .unit, .unit, .unit, 1,
      by rw [sourceAt]; exact .unit, .unit,
      by rw [sourceAt]; exact .unit, by rw [sourceAt]; exact .unit, fun _ => .cons .unit .refl⟩
  | ⟨_, .group inner⟩ =>
      let child ← certify table context environment store inner
      return { child with resolution := by rw [sourceAt]; exact .group child.resolution
                          typing := by rw [sourceAt]; exact .group child.typing
                          raw := by rw [sourceAt]; exact .group child.raw }
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← certify table context environment store left
      let b ← certify table context environment store right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        .pair a.value b.value, a.cost + b.cost + 3,
        by rw [sourceAt]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered,
        by rw [sourceAt]; exact .pair a.typing b.typing,
        by rw [sourceAt]; exact .pair a.raw b.raw, fun k => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core environment.values :: k)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ =>
      let a ← certify table context environment store first
      let b ← certify table context environment store ⟨span,.tuple ⟨tupleSpan,second :: third :: rest⟩⟩
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type, .pair a.value b.value, a.cost + b.cost + 3,
        by rw [sourceAt]; exact .many a.resolution b.resolution, .pair a.lowered b.lowered,
        by rw [sourceAt]; exact .many a.typing b.typing, by rw [sourceAt]; exact .many a.raw b.raw, fun k => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core environment.values :: k)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | _ => throw (IO.userError "outside independent constant certificate grammar")
termination_by sizeOf source
private def checked (content : String) (table : LocalNameTable) (context : Resolved.Context)
    (environment : Resolved.Environment) (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let source ← parsed content
  for store in stores do
    let evidence ← certify table context environment store source
    assertTrue (decide (evidence.core = core ∧ evidence.type = type ∧ evidence.value = value ∧ evidence.cost = cost)) "independent constant certificate changed"
    have accepted := elaborateLocalExpression?_complete evidence.resolution evidence.lowered
      (evidence.resolution.preserves_type evidence.typing)
    have _ := elaborateLocalExpression?_core_hasType accepted
    have direct := evaluateLocalExpressionWithCost?_complete evidence.raw
    have _ := evaluateLocalExpressionWithCost?_sound direct store
    have _ := (evaluateLocalExpressionWithCost?_iff store).mpr evidence.raw
    have _ := localExpressionEvaluatesWithCost_iff_evaluate.mp evidence.raw
    have _ := (evaluateLocalExpressionWithCost?_exists_cost_iff store).mp ⟨evidence.cost, direct⟩
    have _ := (evaluateLocalExpressionWithCost?_value_iff store).mpr evidence.raw.erase
    assertTrue (decide (elaborateLocalExpression? table context source = some (core, type) ∧
      evaluateLocalExpressionWithCost? table environment source = some (value, cost) ∧
      Core.infer? context.values core = some type ∧ localExpressionFuelBound source = cost)) "independent Core/type/value/cost/bound changed"
    for k in [[], [.letBody (.var 0) [w 17]], [.unaryApply .wordNot]] do
      have _ := evidence.paths k
      pure () -- No sameIds premise: these independently constructed paths contain no references.
    let start := Core.State.initial evidence.core environment.values store
    for fuel in List.range (cost + 3) do
      have _ := (evidence.paths []).runStateful_done_iff (fuel := fuel)
      assertTrue (match Core.runStateful fuel start with
        | .done result finalStore => decide (cost ≤ fuel ∧ result = value ∧ finalStore = store)
        | .outOfFuel checkpoint => decide (fuel < cost ∧ checkpoint.store = store)
        | _ => false) "constant fuel threshold or own store changed"
    for spent in List.range cost do
      match exhausted : Core.runStateful spent start with
      | .outOfFuel checkpoint =>
          have _ := (evidence.paths []).residual_of_outOfFuel exhausted
          for additional in List.range (cost - spent + 3) do
            have _ := Core.runStateful_resume exhausted additional
            have _ := (evidence.paths []).resumed_done_iff (additional := additional) exhausted
            assertTrue (decide (Core.runStateful additional checkpoint = Core.runStateful (spent + additional) start)) "actual continuation replay changed"
            assertTrue (match Core.runStateful additional checkpoint with
              | .done result finalStore => decide (cost - spent ≤ additional ∧ result = value ∧ finalStore = store)
              | .outOfFuel next => decide (additional < cost - spent ∧ next.store = store)
              | _ => false) "independent remaining cost changed"
          if spent > 0 then assertTrue (Core.runStateful (cost - spent) start != .done value store) "restart discarded consumed cost"
          if cost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 checkpoint | throw (IO.userError "second actual chunk absent")
            assertTrue (decide (Core.runStateful (cost - spent - 1) next = .done value store)) "third chunk failed"
      | _ => throw (IO.userError "genuine checkpoint absent")
    assertTrue (match Core.runStateful cost ⟨.eval core environment.values, [.unaryApply .wordNot], store⟩ with
      | .fault _ endpoint => decide (endpoint = ⟨.ret value, [.unaryApply .wordNot], store⟩)
      | _ => false) "unit/product endpoint incorrectly guaranteed arbitrary-continuation exhaustion"
    assertTrue (decide (Core.runStateful cost ⟨.eval core environment.values, [.letBody (.var 0) []], store⟩ =
      .outOfFuel ⟨.ret value, [.letBody (.var 0) []], store⟩ ∧
      Core.runStateful (cost + 2) ⟨.eval core environment.values, [.letBody (.var 0) []], store⟩ = .done value store))
      "pending strict binding lost its two transitions"
private def shortCircuit (choice : Bool) (isAnd : Bool) : IO Unit := do
  let inputs := LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool
  let source ← parsed (if isAnd then "c && ()" else "c || ()")
  let expected := if (if isAnd then choice else !choice) then Core.Value.unit else .bool choice
  assertTrue (decide (evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (expected, 4)) &&
    (inputs.check? source).isNone) "raw Unit forwarding became whole Bool typing"
  for store in stores do
    for fuel in [0, 4, 8] do assertTrue (inputs.run? fuel source store).isNone "whole rejection exposed execution"
    match sourceAt : source with
    | ⟨_, .binary ⟨guardSpan, .identifier name⟩ ⟨_, op⟩ ⟨_, .tuple ⟨_, []⟩⟩⟩ =>
        if nameAt : name.value = "c" then
          have guard : LocalExpressionEvaluatesWithCost inputs.names inputs.environment store
              ⟨guardSpan, .identifier name⟩ (.bool choice) store 1 := .identifier (by rw [nameAt]; exact .head) .head
          match opAt : op, atChoice : choice with
          | .logicalAnd, true =>
              have _ : evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (.unit, 4) := by
                rw [sourceAt, opAt]
                exact evaluateLocalExpressionWithCost?_complete (.andTrue (atChoice ▸ guard) .unit)
              pure ()
          | .logicalOr, false =>
              have _ : evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (.unit, 4) := by
                rw [sourceAt, opAt]
                exact evaluateLocalExpressionWithCost?_complete (.orFalse (atChoice ▸ guard) .unit)
              pure ()
          | .logicalAnd, false =>
              have _ : evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (.bool false, 4) := by
                rw [sourceAt, opAt]
                exact evaluateLocalExpressionWithCost?_complete (.andFalse (atChoice ▸ guard))
              pure ()
          | .logicalOr, true =>
              have _ : evaluateLocalExpressionWithCost? inputs.names inputs.environment source = some (.bool true, 4) := by
                rw [sourceAt, opAt]
                exact evaluateLocalExpressionWithCost?_complete (.orTrue (atChoice ▸ guard))
              pure ()
          | _, _ => throw (IO.userError "logical operator changed")
        else throw (IO.userError "guard spelling changed")
    | _ => throw (IO.userError "original Unit child disappeared")
private def conditional (choice : Bool) : IO Unit := do
  let inputs := LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool
  let source ← parsed "c ? () : ()"
  for store in stores do
    match sourceAt : source with
    | ⟨_, .conditional ⟨guardSpan, .identifier name⟩ _ ⟨_, .tuple ⟨_, []⟩⟩ _ ⟨_, .tuple ⟨_, []⟩⟩⟩ =>
        if nameAt : name.value = "c" then
          have guard : LocalExpressionEvaluatesWithCost inputs.names inputs.environment store
              ⟨guardSpan, .identifier name⟩ (.bool choice) store 1 := .identifier (by rw [nameAt]; exact .head) .head
          have raw : LocalExpressionEvaluatesWithCost inputs.names inputs.environment store source .unit store 4 := by
            rw [sourceAt]
            cases choice
            · exact .ifFalse guard .unit
            · exact .ifTrue guard .unit
          have resolved : ResolvesLocalExpression inputs.names source (.ifE (.var (Resolved.freshLocalId owner [])) .unit .unit) := by
            rw [sourceAt]; exact .conditional (.identifier (by rw [nameAt]; exact .head)) .unit .unit
          have accepted := elaborateLocalExpression?_complete (context := inputs.context) resolved (.ifE (.var .head) .unit .unit)
            (Resolved.HasType.ifE (.var .head) .unit .unit)
          have _ := evaluateLocalExpressionWithCost?_complete raw
          have _ := raw.checked_toSteps accepted inputs.sameIds
          assertTrue (decide (inputs.check? source = some (.ifE (.var 0) .unit .unit, .unit))) "conditional unit Core changed"
          for fuel in List.range 7 do
            assertTrue (match inputs.run? fuel source store with
              | some (type, .done value finalStore) => decide (4 ≤ fuel ∧ type = .unit ∧ value = .unit ∧ finalStore = store)
              | some (type, .outOfFuel checkpoint) => decide (fuel < 4 ∧ type = .unit ∧ checkpoint.store = store)
              | _ => false) "selected unit conditional cost changed"
          assertTrue (decide (inputs.run? 3 source store = some (.unit, .outOfFuel (.initial .unit inputs.environment.values store))))
            "selected arm checkpoint was not the original unit expression"
        else throw (IO.userError "conditional guard spelling changed")
    | _ => throw (IO.userError "original conditional Unit children changed")
  let skipped ← parsed "c ? () : missing"
  assertTrue ((inputs.check? skipped).isNone && decide (evaluateLocalExpressionWithCost? inputs.names inputs.environment skipped =
    if choice then some (.unit, 4) else none)) "raw skipped missing arm bypassed whole checking"
end ParsedUnits
open ParsedUnits Solcore Solcore.Frontend
def frontendParsedUnitTests : IO Unit := do
  let hostileNames : LocalNameTable := [("Unit", id 7), ("Unit", id 99), ("missing", id 2)]
  let hostileContext : Resolved.Context := [(id 2, .namedData ⟨83⟩), (id 99, .word)]
  let hostileEnvironment : Resolved.Environment := [(id 7, .cellRef .word 999), (id 7, .closure .word .bool (.var 999) [w 12])]
  let actual := LocalInputs.empty.bindFresh owner "Unit" .word (w 9) .word
  for (table, context, environment) in [([], [], []), (hostileNames, hostileContext, hostileEnvironment),
      (actual.names, actual.context, actual.environment)] do
    for text in ["()", "(())", "((),)", "((()),)"] do checked text table context environment .unit .unit .unit 1
    checked "((), ())" table context environment (.pair .unit .unit) (.product .unit .unit) (.pair .unit .unit) 5
    checked "((),((),()))" table context environment (.pair .unit (.pair .unit .unit))
      (.product .unit (.product .unit .unit)) (.pair .unit (.pair .unit .unit)) 9
    checked "(((),()),())" table context environment (.pair (.pair .unit .unit) .unit)
      (.product (.product .unit .unit) .unit) (.pair (.pair .unit .unit) .unit) 9
    for depth in [0, 1, 3, 6] do
      let text := (List.range depth).foldl (fun inner _ => "(()," ++ inner ++ ")") "()"
      let core := (List.range depth).foldl (fun inner _ => Core.Expr.pair .unit inner) .unit
      let type := (List.range depth).foldl (fun inner _ => Core.Ty.product .unit inner) .unit
      let value := (List.range depth).foldl (fun inner _ => Core.Value.pair .unit inner) .unit
      checked text table context environment core type value (4 * depth + 1)
  let source ← parsed "()"
  assertTrue (match source.value with | .tuple ⟨span, []⟩ => decide (span = source.span) | _ => false) "empty delimited range changed"
  let named ← parsed "Unit"
  assertTrue (decide (actual.check? named = some (.var 0, .word) ∧ actual.check? source = some (.unit, .unit) ∧
    evaluateLocalExpressionWithCost? hostileNames hostileEnvironment named = some (.cellRef .word 999, 1) ∧
    evaluateLocalExpressionWithCost? hostileNames [] source = some (.unit, 1))) "Unit spelling became reserved or empty constant looked up a name"
  for store in stores do
    assertTrue (decide (actual.run? 0 source store = some (.unit, .outOfFuel (.initial .unit actual.environment.values store)) ∧
      actual.run? 1 source store = some (.unit, .done .unit store))) "genuine zero/one Unit boundary changed"
    match exhausted : actual.run? 0 source store with
    | some (_, .outOfFuel _) => have _ := LocalInputs.run?_resume exhausted 1; pure ()
    | _ => throw (IO.userError "Unit checkpoint absent")
    let initial := Core.State.initial (.pair .unit .unit) hostileEnvironment.values store
    assertTrue (decide (Core.runStateful 2 initial = .outOfFuel
      ⟨.ret .unit, [.pairRight .unit hostileEnvironment.values], store⟩ ∧
      Core.runStateful 4 initial = .outOfFuel ⟨.ret .unit, [.pairApply .unit], store⟩)) "unit pair frames were collapsed"
    let certificate ← certify actual.names actual.context actual.environment store source
    let accepted := elaborateLocalExpression?_complete certificate.resolution certificate.lowered
      (certificate.resolution.preserves_type certificate.typing)
    have _ := certificate.raw.checked_toSteps accepted actual.sameIds
    have _ := actual.typed_evaluator_execution certificate.typing store
    pure ()
  for choice in [false, true] do
    for isAnd in [false, true] do shortCircuit choice isAnd
    conditional choice
  checked "((),(),())" hostileNames hostileContext hostileEnvironment (.pair .unit (.pair .unit .unit))
    (.product .unit (.product .unit .unit)) (.pair .unit (.pair .unit .unit)) 9
  checked "((),(),(),())" hostileNames hostileContext hostileEnvironment (.pair .unit (.pair .unit (.pair .unit .unit)))
    (.product .unit (.product .unit (.product .unit .unit))) (.pair .unit (.pair .unit (.pair .unit .unit))) 13
  for text in ["().x", "()[0]", "[()]", "() ()", "() && ()", "!()", "~()"] do
    let invalid ← parsed text
    assertTrue ((resolveLocalExpression? [] invalid).isNone || (elaborateLocalExpression? [] [] invalid).isNone) "unsupported syntax became checked"
    assertTrue (evaluateLocalExpressionWithCost? [] [] invalid).isNone "unsupported/ill-shaped raw syntax succeeded"
  let singleton : Syntax.Expr := ⟨source.span, .tuple ⟨source.span, [source]⟩⟩
  assertTrue ((resolveLocalExpression? [] singleton).isNone && (evaluateLocalExpressionWithCost? [] [] singleton).isNone) "manual singleton acquired grouping meaning"
  for text in ["()", "(Word, Word)"] do
    let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "type lexer invariant")
    let .ok type next := Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file text) lexed) | throw (IO.userError "type parser failed")
    assertTrue (next.atEnd && (interpretTypeName? [(["Word"], .word)] type).isNone) "expression Unit enabled tuple type syntax"
  for (text, expected) in [("Unit", Core.Ty.word), ("Nothing", .unit)] do
    let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "alias lexer invariant")
    let .ok type next := Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file text) lexed) | throw (IO.userError "alias parser failed")
    assertTrue (next.atEnd && decide (interpretTypeName? [(["Unit"], .word), (["Nothing"], .unit)] type = some expected))
      "Unit spelling acquired a reserved type-name meaning"
  let malformedSpan : Syntax.SourceSpan := ⟨⟨.main, "not-parsed.sol"⟩, 99, 2⟩
  let manual : Syntax.Expr := ⟨malformedSpan, .tuple ⟨⟨(file "").id, 7, 1⟩, []⟩⟩
  for store in stores do
    let evidence ← certify hostileNames hostileContext hostileEnvironment store manual
    have _ := evaluateLocalExpressionWithCost?_complete evidence.raw
    assertTrue (decide (evidence.core = .unit ∧ evidence.type = .unit ∧ evidence.value = .unit ∧ evidence.cost = 1))
      "raw/static Unit unexpectedly required valid occurrence ranges"
  for text in ["(", "())", "(,)", "(),"] do assertTrue (← parsed? text).isNone s!"incomplete source accepted: {text}"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendStructuralLetProperties
/-! Independent structural annotations and lexical bodies fix the original Core.
Static nominal inputs never manufacture the values needed for actual execution. -/
set_option autoImplicit false
namespace Tests.FrontendStructuralLet
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"StructuralLet", by decide⟩], by decide⟩⟩, 35⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"structural-let.sol"⟩,235,1⟩
private def named : Syntax.TypeExpr := ⟨span,.named ⟨span,⟨⟨⟨span,"Payload"⟩,[]⟩⟩⟩ none⟩
private def unitType : Syntax.TypeExpr := ⟨span,.tuple []⟩
private def shape : Nat → Syntax.TypeExpr
  | 0 => ⟨span,.tuple [named]⟩
  | n+1 => ⟨span,.tuple [unitType,shape n]⟩
private def nested (type : Core.Ty) : Nat → Core.Ty
  | 0 => type
  | n+1 => .product .unit (nested type n)
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"],type)]
private theorem meaning (type : Core.Ty) (n : Nat) : StructuralTypeDenotes (types type) (shape n) (nested type n) := by
  induction n with
  | zero => exact .single (.named .head)
  | succ n ih => exact .pair .unit ih
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def unit : Syntax.Expr := ⟨span,.tuple ⟨span,[]⟩⟩
private def returned (name : String) : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (ref name))⟩]⟩
private def bind (annotation : Syntax.TypeExpr) (name : String) (initializer : Syntax.Expr) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span,⟨span,.letDecl ⟨span,name⟩ (some annotation) (some initializer)⟩ :: tail.value⟩
private def seed (type : Core.Ty) : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "seed" type
private def zero : Syntax.Expr := ⟨span,.literal ⟨span,.decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span,.binary zero ⟨span,.equal⟩ zero⟩
private def guardCore : Core.Expr := .binary .wordEq (.word .zero) (.word .zero)
private theorem zeroMeaning : WordLiteralDenotes ⟨span,.decimal "0"⟩ Core.Word.zero :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def branch (left right : Syntax.Block) : Syntax.Block := ⟨span,[⟨span,.ifThen guard left (some right)⟩]⟩
private def tree (annotation : Syntax.TypeExpr) : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => bind annotation name (ref previous) (branch (tree annotation rest name) (returned name))
private def core : Nat → Core.Expr
  | 0 => .var 0
  | n+1 => .letE (.var 0) (.ifE guardCore (core n) (.var 0))
private theorem treeElab (names : List String) (previous : String) (type : Core.Ty) (depth : Nat)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var 0))
    (typed : Resolved.HasType initial.context resolved (nested type depth)) :
    TypedLetReturnTreeElaborates (types type) owner initial (tree (shape depth) names previous)
      (core names.length) (nested type depth) := by
  induction names generalizing previous initial resolved with
  | nil => exact .single (.expression resolution (by simpa only [LocalTypeInputs.context_ids, List.length_nil, core] using lowered) typed)
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      apply TypedLetReturnTreeElaborates.binding (meaning type depth) (fresh name (by simp)) resolution lowered typed
      apply TypedLetReturnTreeElaborates.conditional (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning))
        (.binary .word .word) (.binary .word .word)
      · apply ih name (initial.bindFresh owner name (nested type depth)) _ parts.2
        · intro next member
          simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
          exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
        · exact .identifier .head
        · exact .var .head
        · exact .var .head
      · exact .single (.expression (.identifier .head) (.var .head) (.var .head))
private theorem seeded (names : List String) (type : Core.Ty) (depth : Nat)
    (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed (nested type depth))
      (tree (shape depth) names "seed") (core names.length) (nested type depth) := by
  apply treeElab names "seed" type depth _ _ distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head
private theorem coreTyped (n : Nat) (type : Core.Ty) (tail : Core.Context) (definitions : Core.DataEnvironment) :
    Core.HasType (type :: tail) (core n) type definitions := by
  induction n generalizing tail with
  | zero => exact .var rfl
  | succ n ih => exact .letE (.var rfl) (.ifE (.binary .word .word) (ih (type :: tail)) (.var rfl))

theorem arbitrary_type_and_let_depth_have_independent_exact_provenance
    (names : List String) (type : Core.Ty) (depth : Nat) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (definitions : Core.DataEnvironment) :
    StructuralTypeDenotes (types type) (shape depth) (nested type depth) ∧
    TypedLetReturnTreeElaborates (types type) owner (seed (nested type depth))
      (tree (shape depth) names "seed") (core names.length) (nested type depth) ∧
    TypedLetReturnTreeHasType (types type) owner (seed (nested type depth)) (tree (shape depth) names "seed") (nested type depth) ∧
    elaborateTypedLetReturnTree? (types type) owner (seed (nested type depth)) (tree (shape depth) names "seed") =
      some (core names.length,nested type depth) ∧ Core.HasType [nested type depth] (core names.length) (nested type depth) definitions :=
  ⟨meaning type depth, seeded names type depth distinct fresh, (seeded names type depth distinct fresh).hasType,
    (seeded names type depth distinct fresh).complete, coreTyped _ _ [] definitions⟩

theorem structural_success_does_not_make_the_old_prefix_checker_equivalent
    (type : Core.Ty) (depth : Nat) :
    elaborateTypedLetReturnTree? (types type) owner (seed (nested type depth)) (tree (shape depth) ["local"] "seed") =
      some (core 1,nested type depth) ∧
    elaborateTypedLetReturnBody? (types type) owner (seed (nested type depth)) (tree (shape depth) ["local"] "seed") = none := by
  refine ⟨(seeded ["local"] type depth (by decide) (by decide)).complete, ?_⟩
  apply elaborateTypedLetReturnBody?_eq_none_iff.mpr
  rintro ⟨result, typing⟩
  cases typing with
  | terminal child => cases child with | single child => cases child
  | binding oldMeaning _ _ _ => cases depth <;> cases oldMeaning

theorem first_binding_keeps_old_scope_and_exact_fresh_tail (type : Core.Ty) (depth : Nat) :
    ∃ declared initializer tail,
      interpretStructuralType? (types type) (shape depth) = some declared ∧
      elaborateLocalExpression? (seed (nested type depth)).names (seed (nested type depth)).context (ref "seed") = some (initializer,declared) ∧
      elaborateTypedLetReturnTree? (types type) owner ((seed (nested type depth)).bindFresh owner "local" declared)
        (branch (returned "local") (returned "local")) = some (tail,nested type depth) ∧ core 1 = .letE initializer tail := by
  obtain ⟨declared, initializer, tail, _, interpreted, initial, rest, same⟩ :=
    elaborateTypedLetReturnTree?_binding_children (seeded ["local"] type depth (by decide) (by decide)).complete
  exact ⟨declared,initializer,tail,interpreted,initial,rest,same⟩

theorem old_named_typing_and_exact_prefix_successes_still_embed (type : Core.Ty) :
    TypedLetReturnTreeHasType (types type) owner (seed type) (bind named "local" (ref "seed") (returned "local")) type ∧
    elaborateTypedLetReturnTree? (types type) owner (seed type) (bind named "local" (ref "seed") (returned "local")) =
      some (.letE (.var 0) (.var 0),type) := by
  have old : TypedLetReturnBodyElaborates (types type) owner (seed type)
      (bind named "local" (ref "seed") (returned "local")) (.letE (.var 0) (.var 0)) type :=
    .binding (.named .head) (by change "local" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head))))
  exact ⟨old.hasType.returnTree, elaborateTypedLetReturnTree?_some_of_typedLetReturnBody old.complete⟩

private def unitBody (annotation : Syntax.TypeExpr) : Syntax.Block := bind annotation "local" unit (returned "local")
theorem unit_initializer_accepts_unit_but_not_an_arbitrary_product (table : TypeNameTable) (left right : Syntax.TypeExpr) :
    elaborateTypedLetReturnTree? table owner .empty (unitBody unitType) = some (.letE .unit (.var 0),.unit) ∧
    elaborateTypedLetReturnTree? table owner .empty (unitBody ⟨span,.tuple [left,right]⟩) = none := by
  have good : TypedLetReturnTreeElaborates table owner .empty (unitBody unitType) (.letE .unit (.var 0)) .unit :=
    .binding .unit (by simp) .unit .unit .unit (.single (.expression (.identifier .head) (.var .head) (.var .head)))
  refine ⟨good.complete, elaborateTypedLetReturnTree?_eq_none_iff.mpr ?_⟩
  rintro ⟨type, typing⟩
  cases typing with
  | single child => cases child
  | binding declared _ initializer _ => cases declared; cases initializer

private def strict : Syntax.Block := bind ⟨span,.tuple [named,unitType]⟩ "unused"
  ⟨span,.tuple ⟨span,[ref "seed",unit]⟩⟩ (returned "seed")
private def strictCore : Core.Expr := .letE (.pair (.var 0) .unit) (.var 1)
private theorem strictElab (type : Core.Ty) : TypedLetReturnTreeElaborates (types type) owner (seed type) strict strictCore type :=
  .binding (.pair (.named .head) .unit) (by change "unused" ∉ ["seed"]; decide)
    (.pair (.identifier .head) .unit) (.pair (.var .head) .unit) (.pair (.var .head) .unit)
    (.single (.expression (.identifier (.tail (by change "unused" ≠ "seed"; decide) .head))
      (.var (.tail (by change id 1 ≠ id 0; decide) .head)) (.var (.tail (by change id 1 ≠ id 0; decide) .head))))
private abbrev Actual (type : Core.Ty) := {value : Core.Value // Core.ValueHasType value type}
private def actualInputs {type : Core.Ty} (actual : Actual type) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "seed" type actual.val actual.property
private theorem strictCost {type : Core.Ty} (actual : Actual type) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (actualInputs actual).names (actualInputs actual).environment store strict actual.val store 8 := by
  apply TypedLetReturnTreeEvaluatesWithCost.binding (boundValue := .pair actual.val .unit)
    (middleStore := store) (initializerCost := 5) (tailCost := 1)
  · exact .pair (leftCost := 1) (rightCost := 1) (.identifier .head .head) .unit
  · exact .single (.expression (.identifier (.tail (by change "unused" ≠ "seed"; decide) .head)
      (.tail (by change id 1 ≠ id 0; decide) .head)))

theorem an_unused_structural_product_initializer_keeps_its_strict_eight_steps
    {type : Core.Ty} (actual : Actual type) (store : Core.Store) (continuation : List Core.Frame) :
    elaborateTypedLetReturnTree? (types type) owner (actualInputs actual).toTypeInputs strict = some (strictCore,type) ∧
    TypedLetReturnTreeEvaluatesWithCost owner (actualInputs actual).names (actualInputs actual).environment store strict actual.val store 8 ∧
    Core.Steps 8 ⟨.eval strictCore [actual.val],continuation,store⟩ ⟨.ret actual.val,continuation,store⟩ :=
  ⟨(strictElab type).complete, strictCost actual store,
    (strictCost actual store).checked_toStepsWithContinuation (strictElab type).complete rfl continuation⟩

theorem equal_result_types_do_not_identify_a_different_core (type : Core.Ty) (definitions : Core.DataEnvironment) :
    Core.HasType [type] (.var 0) type definitions ∧
    ¬ TypedLetReturnTreeElaborates (types type) owner (seed type) strict (.var 0) type := by
  refine ⟨.var rfl, ?_⟩
  intro wrong
  cases (wrong.result_unique (strictElab type)).1

theorem nominal_nested_static_types_do_not_supply_actual_inputs (nominal : Core.DataTypeId) (depth : Nat) :
    elaborateTypedLetReturnTree? (types (.namedData nominal)) owner (seed (nested (.namedData nominal) depth))
      (tree (shape depth) ["local"] "seed") = some (core 1,nested (.namedData nominal) depth) ∧
    ¬ ∃ value, Core.ValueHasType value (nested (.namedData nominal) depth) := by
  refine ⟨(seeded ["local"] _ depth (by decide) (by decide)).complete, ?_⟩
  induction depth with
  | zero =>
      rintro ⟨value, typed⟩
      cases typed with
      | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  | succ depth ih => rintro ⟨value, typed⟩; cases typed with | pair _ right => exact ih ⟨_,right⟩

theorem opaque_cells_and_captured_closures_are_returned_without_unpacking (location : Core.Location) (word : Core.Word) (store : Core.Store) :
    Core.Steps 8 (Core.State.initial strictCore [.cellRef .word location] store) (Core.State.final (.cellRef .word location) store) ∧
    Core.Steps 8 (Core.State.initial strictCore [.closure .word .word (.var 1) [.word word]] store)
      (Core.State.final (.closure .word .word (.var 1) [.word word]) store) :=
  ⟨(an_unused_structural_product_initializer_keeps_its_strict_eight_steps ⟨_,.cellRef⟩ store []).2.2,
    (an_unused_structural_product_initializer_keeps_its_strict_eight_steps ⟨_,.closure (.cons .word .nil) (.var rfl)⟩ store []).2.2⟩

theorem semantic_extension_and_owner_relabeling_retain_the_original_tree
    (type : Core.Ty) (depth : Nat) (next : TypeNameTable) (extension : TypeNameTable.Extends (types type) next)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    elaborateTypedLetReturnTree? next owner (seed (nested type depth)) (tree (shape depth) ["local"] "seed") =
      some (core 1,nested type depth) ∧
    elaborateTypedLetReturnTree? (types type) (mapping owner)
      ((seed (nested type depth)).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
      (tree (shape depth) ["local"] "seed") = some (core 1,nested type depth) :=
  ⟨((seeded ["local"] type depth (by decide) (by decide)).extend_types extension).complete,
    ((seeded ["local"] type depth (by decide) (by decide)).mapOwner mapping injective).complete⟩

end Tests.FrontendStructuralLet
end

section
-- leanmerge: from Solcore.Test.FrontendStructuralParameterProperties
/-! Structural annotations keep each original parameter and supplied value whole.
Independent constructor evidence fixes static and runtime bundles before checking. -/
set_option autoImplicit false
namespace Tests.FrontendStructuralParameter
open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "structural-parameter.sol"⟩, 234, 1⟩
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Parameters", by decide⟩], by decide⟩⟩, n⟩
private def named : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def unit : Syntax.TypeExpr := ⟨span, .tuple []⟩
private def single (child : Syntax.TypeExpr) : Syntax.TypeExpr := ⟨span, .tuple [child]⟩
private def shape : Nat → Syntax.TypeExpr
  | 0 => unit
  | n + 1 => ⟨span, .tuple [named, single (shape n)]⟩
private def product (type : Core.Ty) : Nat → Core.Ty
  | 0 => .unit
  | n + 1 => .product type (product type n)
private def packed (value : Core.Value) : Nat → Core.Value
  | 0 => .unit
  | n + 1 => .pair value (packed value n)
private def table (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private theorem meaning (type : Core.Ty) (n : Nat) : StructuralTypeDenotes (table type) (shape n) (product type n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.named .head) (.single ih)
private def parameter (name : String) (annotation : Syntax.TypeExpr) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ annotation⟩
private def parameters (n : Nat) := [parameter "packed" (shape n), parameter "ignored" unit, parameter "leaf" (single named)]
private def static (type : Core.Ty) (n : Nat) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh (owner 0) "packed" (product type n)).bindFresh (owner 0) "ignored" .unit).bindFresh (owner 0) "leaf" type
private theorem declared (type : Core.Ty) (n : Nat) : RuntimeParametersDeclare (table type) (owner 0) (parameters n) (static type n) :=
  .cons (meaning type n) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons .unit (by change "ignored" ∉ ["packed"]; decide)
      (.cons (.single (.named .head)) (by change "leaf" ∉ ["ignored", "packed"]; decide) .nil))
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private theorem packedTyped {type : Core.Ty} (actual : Actual type) (n : Nat) :
    Core.ValueHasType (packed actual.val n) (product type n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair actual.property ih
private def packArgument {type : Core.Ty} (actual : Actual type) (n : Nat) : TypedRuntimeArgument :=
  ⟨product type n, packed actual.val n, packedTyped actual n⟩
private def unitArgument : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
private def leafArgument {type : Core.Ty} (actual : Actual type) : TypedRuntimeArgument := ⟨type, actual.val, actual.property⟩
private def arguments {type : Core.Ty} (actual : Actual type) (n : Nat) := [packArgument actual n, unitArgument, leafArgument actual]
private def runtime {type : Core.Ty} (actual : Actual type) (n : Nat) : LocalInputs :=
  ((LocalInputs.empty.bindFresh (owner 0) "packed" (product type n) (packed actual.val n) (packedTyped actual n)).bindFresh
    (owner 0) "ignored" .unit .unit .unit).bindFresh (owner 0) "leaf" type actual.val actual.property
private theorem bound {type : Core.Ty} (actual : Actual type) (n : Nat) :
    RuntimeParametersBind (table type) (owner 0) (parameters n) (arguments actual n) (runtime actual n) :=
  .cons (meaning type n) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons .unit (by change "ignored" ∉ ["packed"]; decide)
      (.cons (.single (.named .head)) (by change "leaf" ∉ ["ignored", "packed"]; decide) .nil))

theorem arbitrary_structural_depth_declares_three_original_rows (type : Core.Ty) (n : Nat) :
    RuntimeParametersDeclare (table type) (owner 0) (parameters n) (static type n) ∧
    declareRuntimeParameters? (table type) (owner 0) (parameters n) = some (static type n) ∧
    (static type n).bindings = [⟨"leaf", ⟨owner 0, 2⟩, type⟩, ⟨"ignored", ⟨owner 0, 1⟩, .unit⟩,
      ⟨"packed", ⟨owner 0, 0⟩, product type n⟩] ∧
    interpretTypeName? (table type) (shape n) = none :=
  ⟨declared type n, (declared type n).complete, rfl, by cases n <;> rfl⟩

theorem paired_constructor_rows_do_not_flatten_products_or_omit_unit {type : Core.Ty} (actual : Actual type) (n : Nat) :
    RuntimeParameterDeclarationRows (table type) (parameters n) (static type n).bindings.reverse ∧
    RuntimeParameterRows (table type) (parameters n) (arguments actual n) (runtime actual n).bindings.reverse ∧
    bindRuntimeParameters? (table type) (owner 0) (parameters n) (arguments actual n) = some (runtime actual n) ∧
    (runtime actual n).environment = [(⟨owner 0, 2⟩, actual.val), (⟨owner 0, 1⟩, .unit), (⟨owner 0, 0⟩, packed actual.val n)] :=
  ⟨.cons (.typed (meaning type n)) (.cons (.typed .unit) (.cons (.typed (.single (.named .head))) .nil)),
    .cons (.typed (meaning type n)) (.cons (.typed .unit) (.cons (.typed (.single (.named .head))) .nil)),
    (bound actual n).complete, rfl⟩

theorem exact_static_bundles_erase_and_restore_only_supplied_values {type : Core.Ty} (actual : Actual type) (n : Nat) :
    (runtime actual n).toTypeInputs = static type n ∧
    RuntimeParametersDeclare (table type) (owner 0) (parameters n) (runtime actual n).toTypeInputs ∧
    ∃ restored, RuntimeParametersBind (table type) (owner 0) (parameters n) (arguments actual n) restored ∧
      restored.toTypeInputs = static type n ∧ restored = runtime actual n := by
  obtain ⟨restored, binding, erased⟩ := (declared type n).bind_typed_arguments (arguments actual n) rfl
  exact ⟨rfl, (bound actual n).erase_values, restored, binding, erased, binding.result_unique (bound actual n)⟩

theorem every_actual_source_position_keeps_its_exact_structural_meaning {type : Core.Ty}
    (actual : Actual type) (n : Nat) {index : Nat} {parameterSpan : Syntax.SourceSpan}
    {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {argument : TypedRuntimeArgument}
    (parameterAt : (parameters n)[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : (arguments actual n)[index]? = some argument) :
    index < 3 ∧ StructuralTypeDenotes (table type) annotation argument.type ∧
    (runtime actual n).bindings[2 - index]? = some
      ⟨name.value, ⟨owner 0, index⟩, argument.type, argument.value, argument.valueTyped⟩ ∧
    LocalNameTable.Lookup (runtime actual n).names name.value ⟨owner 0, index⟩ ∧
    Resolved.LocalScope.Lookup (runtime actual n).context ⟨owner 0, index⟩ argument.type ∧
    Resolved.LocalScope.Lookup (runtime actual n).environment ⟨owner 0, index⟩ argument.value ∧
    Resolved.LocalScope.IndexOf (runtime actual n).context.ids ⟨owner 0, index⟩ (2 - index) :=
  (bound actual n).position parameterAt argumentAt

theorem static_position_needs_no_value_and_cannot_exchange_equal_outer_types (type : Core.Ty) (n : Nat) :
    StructuralTypeDenotes (table type) (shape n) (product type n) ∧
    Resolved.LocalScope.Lookup (static type n).context ⟨owner 0, 0⟩ (product type n) ∧
    Resolved.LocalScope.IndexOf (static type n).context.ids ⟨owner 0, 0⟩ 2 ∧
    elaborateLocalExpression? (static type n).names (static type n).context
      ⟨span, .identifier ⟨span, "packed"⟩⟩ = some (.var 2, product type n) := by
  obtain ⟨_, actualType, actualMeaning, _, named, found, indexed⟩ := (declared type n).position (index := 0) rfl
  cases actualMeaning.type_unique (meaning type n)
  exact ⟨meaning type n, found, indexed, elaborateLocalExpression?_complete (.identifier named) (.var indexed) (.var found)⟩

private def sparse : LocalInputs := ⟨[⟨"old", ⟨owner 0, 7⟩, .unit, .unit, .unit⟩,
  ⟨"foreign", ⟨owner 1, 999⟩, .unit, .unit, .unit⟩, ⟨"old", ⟨owner 0, 2⟩, .unit, .unit, .unit⟩], by decide⟩
private def extended {type : Core.Ty} (actual : Actual type) (n : Nat) :=
  ((sparse.bindFresh (owner 0) "packed" (product type n) (packed actual.val n) (packedTyped actual n)).bindFresh
    (owner 0) "ignored" .unit .unit .unit).bindFresh (owner 0) "leaf" type actual.val actual.property
private theorem extension {type : Core.Ty} (actual : Actual type) (n : Nat) :
    RuntimeParametersBindFrom (table type) (owner 0) sparse (parameters n) (arguments actual n) (extended actual n) :=
  .cons (meaning type n) (by change "packed" ∉ ["old", "foreign", "old"]; decide)
    (.cons .unit (by change "ignored" ∉ ["packed", "old", "foreign", "old"]; decide)
      (.cons (.single (.named .head)) (by change "leaf" ∉ ["ignored", "packed", "old", "foreign", "old"]; decide) .nil))

theorem sparse_mixed_owners_and_repeated_initial_names_keep_all_rows {type : Core.Ty} (actual : Actual type) (n : Nat) :
    RuntimeParametersBindFrom (table type) (owner 0) sparse (parameters n) (arguments actual n) (extended actual n) ∧
    RuntimeParametersDeclareFrom (table type) (owner 0) sparse.toTypeInputs (parameters n) (extended actual n).toTypeInputs ∧
    (extended actual n).ids = [⟨owner 0, 10⟩, ⟨owner 0, 9⟩, ⟨owner 0, 8⟩] ++ sparse.ids ∧
    (extended actual n).bindings.length = 3 + sparse.bindings.length ∧
    (extended actual n).environment.values = (arguments actual n).reverse.map (·.value) ++ sparse.environment.values :=
  ⟨extension actual n, (extension actual n).erase_values, rfl, (extension actual n).bindings_length,
    (extension actual n).argument_values⟩

theorem semantic_table_extension_keeps_the_exact_static_bundle (type : Core.Ty) (n : Nat)
    (next : TypeNameTable) (preserves : TypeNameTable.Extends (table type) next) :
    RuntimeParametersDeclare next (owner 0) (parameters n) (static type n) ∧
    declareRuntimeParameters? next (owner 0) (parameters n) = some (static type n) :=
  ⟨(declared type n).extend_types preserves,
    declareRuntimeParameters?_some_of_extends preserves (declared type n).complete⟩

theorem owner_relabeling_keeps_structural_types_and_source_order (type : Core.Ty) (n : Nat)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    RuntimeParametersDeclare (table type) (mapping (owner 0)) (parameters n)
      ((static type n).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) :=
  (declared type n).map_owner mapping injective

theorem nominal_packed_and_unused_leaf_types_never_supply_runtime_inhabitants (nominal : Core.DataTypeId) (n : Nat) :
    declareRuntimeParameters? (table (.namedData nominal)) (owner 0) (parameters n) = some (static (.namedData nominal) n) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  refine ⟨(declared _ _).complete, ?_⟩
  rintro ⟨⟨type, value, typed⟩, same⟩; cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem opaque_cells_and_captured_functions_are_whole_arguments (location : Core.Location) (word : Core.Word) :
    bindRuntimeParameters? (table (.cell .word)) (owner 0) (parameters 1)
      (arguments ⟨.cellRef .word location, .cellRef⟩ 1) = some (runtime ⟨.cellRef .word location, .cellRef⟩ 1) ∧
    bindRuntimeParameters? (table (.function .bool .word)) (owner 0) (parameters 1)
      (arguments ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ 1) =
      some (runtime ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ 1) :=
  ⟨(bound _ _).complete, (bound _ _).complete⟩

private def declaration (n : Nat) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "packed"⟩, none, ⟨span, parameters n⟩, ⟨none, none⟩,
      some ⟨span, ⟨span, [shape n]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some ⟨span, .identifier ⟨span, "packed"⟩⟩)⟩]⟩⟩⟩
private def compiled (type : Core.Ty) (n : Nat) : CompiledRuntimeFunction := ⟨static type n, .var 2, product type n⟩
private theorem compilation (type : Core.Ty) (n : Nat) : RuntimeFunctionCompiles (table type) (owner 0) (declaration n) (compiled type n) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (meaning type n)⟩, declared type n,
    .single (.expression (.identifier (.tail (by change "leaf" ≠ "packed"; decide)
        (.tail (by change "ignored" ≠ "packed"; decide) .head)))
      (.var (.tail (by change (⟨owner 0, 2⟩ : Resolved.LocalId) ≠ ⟨owner 0, 0⟩; decide)
        (.tail (by change (⟨owner 0, 1⟩ : Resolved.LocalId) ≠ ⟨owner 0, 0⟩; decide) .head)))
      (.var (.tail (by change (⟨owner 0, 2⟩ : Resolved.LocalId) ≠ ⟨owner 0, 0⟩; decide)
        (.tail (by change (⟨owner 0, 1⟩ : Resolved.LocalId) ≠ ⟨owner 0, 0⟩; decide) .head))))⟩

theorem parameter_only_record_reconstruction_keeps_the_original_core {type : Core.Ty} (actual : Actual type) (n : Nat) :
    compileRuntimeFunction? (table type) (owner 0) (declaration n) = some (compiled type n) ∧
    ∃ prepared, RuntimeFunctionPrepares (table type) (owner 0) (declaration n) (arguments actual n) prepared ∧
      prepared.toCompiled = compiled type n :=
  ⟨(compilation type n).complete, (compilation type n).prepare_arguments (arguments actual n) rfl⟩

theorem equally_typed_unit_positions_do_not_justify_a_wrong_compiled_variable :
    Core.HasType [.unit, .unit, .unit] (.var 1) .unit ∧
    ¬ RuntimeFunctionCompiles (table .unit) (owner 0) (declaration 0) { compiled .unit 0 with core := .var 1 } := by
  refine ⟨.var rfl, ?_⟩
  intro wrong
  have incompatible := congrArg CompiledRuntimeFunction.core (wrong.result_unique (compilation .unit 0))
  cases incompatible

end Tests.FrontendStructuralParameter
end

section
-- leanmerge: from Solcore.Test.FrontendStructuralReturnProperties
/-! Independent structural return contracts meet the existing entry only through
original parameter/body provenance. Static types do not supply runtime arguments. -/
set_option autoImplicit false
namespace Tests.FrontendStructuralReturn
open Solcore Solcore.Frontend
private def clause (s t : Syntax.SourceSpan) (annotations : List Syntax.TypeExpr) : Option Syntax.ReturnClause :=
  some ⟨s, ⟨t, annotations⟩⟩
private def signature (s : Syntax.SourceSpan) (returns : Option Syntax.ReturnClause)
    (parameters : List Syntax.FunctionParameter := []) : Syntax.FunctionSignature :=
  ⟨s, ⟨s, "structural"⟩, none, ⟨s, parameters⟩, ⟨none, none⟩, returns, none⟩

theorem independent_structural_headers_keep_arbitrary_ranges_and_unique_results
    (s t : Syntax.SourceSpan) (table : TypeNameTable) (annotation : Syntax.TypeExpr) (type : Core.Ty)
    (meaning : StructuralTypeDenotes table annotation type) :
    RuntimeReturnTypeDenotes table (clause s t [annotation]) type ∧
    RuntimeFunctionHeader table (signature s (clause s t [annotation])) type ∧
    interpretRuntimeFunctionHeader? table (signature s (clause s t [annotation])) = some type ∧
    (∀ other, RuntimeFunctionHeader table (signature s (clause s t [annotation])) other → other = type) := by
  have header : RuntimeFunctionHeader table (signature s (clause s t [annotation])) type :=
    ⟨rfl, rfl, rfl, rfl, .single meaning⟩
  exact ⟨.single meaning, header, interpretRuntimeFunctionHeader?_iff.mpr header, fun _ other => other.type_unique header⟩

theorem absent_and_single_empty_tuple_are_unit_but_multiple_return_annotations_stay_rejected
    (s t : Syntax.SourceSpan) (table : TypeNameTable) (left right third : Syntax.TypeExpr) :
    RuntimeReturnTypeDenotes table none .unit ∧
    RuntimeReturnTypeDenotes table (clause s t [⟨s, .tuple []⟩]) .unit ∧
    interpretRuntimeReturnType? table none = some .unit ∧
    interpretRuntimeReturnType? table (clause s t [⟨s, .tuple []⟩]) = some .unit ∧
    interpretRuntimeReturnType? table (clause s t []) = none ∧
    interpretRuntimeReturnType? table (clause s t [left, right]) = none ∧
    interpretRuntimeReturnType? table (clause s t [left, right, third]) = none := by
  refine ⟨.absent, .single .unit, rfl, ?_, rfl, rfl, ?_⟩ <;>
    simp [interpretRuntimeReturnType?, interpretStructuralType?, clause]

theorem old_named_return_evidence_still_enters_through_its_explicit_embedding
    (s t : Syntax.SourceSpan) (table : TypeNameTable) (annotation : Syntax.TypeExpr) (type : Core.Ty)
    (old : TypeNameDenotes table annotation type) :
    (∃ key, (key, type) ∈ table) ∧
    RuntimeReturnTypeDenotes table (clause s t [annotation]) type ∧
    RuntimeReturnTypeDenotes table (clause s t [⟨s, .tuple [annotation]⟩]) type :=
  ⟨old.mem, .single old.structural, .single (.single old.structural)⟩

private def span : Syntax.SourceSpan := ⟨⟨.main, "structural-return.sol"⟩, 233, 4⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"StructuralReturn", by decide⟩], by decide⟩⟩, 0⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def table (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def annotation : Nat → Syntax.TypeExpr
  | 0 => ⟨span, .tuple []⟩
  | n + 1 => ⟨span, .tuple [⟨span, .tuple [named "Payload"]⟩, annotation n]⟩
private def product (type : Core.Ty) : Nat → Core.Ty
  | 0 => .unit
  | n + 1 => .product type (product type n)
private def source : Nat → Syntax.Expr
  | 0 => ⟨span, .tuple ⟨span, []⟩⟩
  | n + 1 => ⟨span, .tuple ⟨span, [⟨span, .identifier ⟨span, "seed"⟩⟩, source n]⟩⟩
private def resolved (id : Resolved.LocalId) : Nat → Resolved.Expr
  | 0 => .unit
  | n + 1 => .pair (.var id) (resolved id n)
private def core : Nat → Core.Expr
  | 0 => .unit
  | n + 1 => .pair (.var 0) (core n)
private def value (actual : Core.Value) : Nat → Core.Value
  | 0 => .unit
  | n + 1 => .pair actual (value actual n)
private def parameter (type : Syntax.TypeExpr) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, "seed"⟩ type⟩
private def body (n : Nat) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (source n))⟩]⟩
private def entry (returnClause : Option Syntax.ReturnClause) (parameters : List Syntax.FunctionParameter) (body : Syntax.Block) : Syntax.FunctionDecl :=
  ⟨span, ⟨signature span returnClause parameters, body⟩⟩
private def declaration (n : Nat) := entry (clause span span [annotation n]) [parameter (named "Payload")] (body n)
private def initial (type : Core.Ty) := LocalTypeInputs.empty.bindFresh owner "seed" type
private def compiled (type : Core.Ty) (n : Nat) : CompiledRuntimeFunction := ⟨initial type, core n, product type n⟩
private theorem meaning (type : Core.Ty) (n : Nat) : StructuralTypeDenotes (table type) (annotation n) (product type n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.single (.named .head)) ih
private theorem header (type : Core.Ty) (n : Nat) : RuntimeFunctionHeader (table type) (declaration n).value.signature (product type n) :=
  ⟨rfl, rfl, rfl, rfl, .single (meaning type n)⟩
private theorem expression (type : Core.Ty) (n : Nat) :
    ResolvesLocalExpression (initial type).names (source n) (resolved (Resolved.freshLocalId owner []) n) ∧
    Resolved.Lowers (initial type).ids (resolved (Resolved.freshLocalId owner []) n) (core n) ∧
    Resolved.HasType (initial type).context (resolved (Resolved.freshLocalId owner []) n) (product type n) := by
  induction n with
  | zero => exact ⟨.unit, .unit, .unit⟩
  | succ n ih => exact ⟨.pair (.identifier .head) ih.1, .pair (.var .head) ih.2.1, .pair (.var .head) ih.2.2⟩
private theorem compilation (type : Core.Ty) (n : Nat) : RuntimeFunctionCompiles (table type) owner (declaration n) (compiled type n) :=
  ⟨header type n, .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
    .single (.expression (expression type n).1 (expression type n).2.1 (expression type n).2.2)⟩
private abbrev Actual (type : Core.Ty) := { actual : Core.Value // Core.ValueHasType actual type }
private def arguments {type : Core.Ty} (actual : Actual type) : List TypedRuntimeArgument := [⟨type, actual.val, actual.property⟩]
private def inputs {type : Core.Ty} (actual : Actual type) := LocalInputs.empty.bindFresh owner "seed" type actual.val actual.property
private theorem preparation {type : Core.Ty} (actual : Actual type) (n : Nat) :
    RuntimeFunctionPrepares (table type) owner (declaration n) (arguments actual) ⟨inputs actual, core n, product type n⟩ :=
  ⟨header type n, .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil, (compilation type n).body⟩
private theorem raw (table : LocalNameTable) (environment : Resolved.Environment) (id : Resolved.LocalId)
    (actual : Core.Value) (store : Core.Store) (n : Nat) :
    LocalExpressionEvaluatesWithCost (("seed", id) :: table) ((id, actual) :: environment) store (source n) (value actual n) store (4 * n + 1) := by
  induction n with
  | zero => exact .unit
  | succ n ih =>
      have count : 4 * (n + 1) + 1 = 1 + (4 * n + 1) + 3 := by omega
      rw [count]; exact .pair (.identifier .head .head) ih
private theorem costed {type : Core.Ty} (actual : Actual type) (n : Nat) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table type) owner (declaration n) (arguments actual) store
      (product type n) (value actual.val n) store (4 * n + 1) :=
  .intro (preparation actual n) (.single (.expression (raw [] [] _ actual.val store n)))
private theorem path (actual : Core.Value) (store : Core.Store) (n : Nat) :
    ∀ k, Core.Steps (4 * n + 1) ⟨.eval (core n) [actual], k, store⟩ ⟨.ret (value actual n), k, store⟩ := by
  induction n with
  | zero => intro k; exact .cons .unit .refl
  | succ n ih =>
      intro k
      have steps := Core.Steps.cons .enterPair (.cons (.var (index := 0) rfl) (.cons .enterPairRight
        ((ih (.pairApply actual :: k)).trans (.cons .applyPair .refl))))
      simpa [core, value, Nat.mul_add, Nat.add_assoc] using steps

theorem arbitrary_nested_returns_compile_without_supplied_values (type : Core.Ty) (n : Nat) :
    RuntimeFunctionCompiles (table type) owner (declaration n) (compiled type n) ∧
    compileRuntimeFunction? (table type) owner (declaration n) = some (compiled type n) ∧
    (compiled type n).inputs.bindings.length = 1 ∧
    interpretTypeName? (table type) (annotation n) = none :=
  ⟨compilation type n, (compilation type n).complete, rfl, by cases n <;> rfl⟩

theorem actual_arguments_execute_the_original_body_at_its_independent_cost
    {type : Core.Ty} (actual : Actual type) (n fuel : Nat) (store : Core.Store) (k : List Core.Frame) :
    prepareRuntimeFunction? (table type) owner (declaration n) (arguments actual) = some ⟨inputs actual, core n, product type n⟩ ∧
    (inputs actual).environment.values = (arguments actual).reverse.map (·.value) ∧
    Core.Steps (4 * n + 1) ⟨.eval (core n) [actual.val], k, store⟩ ⟨.ret (value actual.val n), k, store⟩ ∧
    (runRuntimeFunction? (table type) owner (declaration n) (arguments actual) fuel store =
      some (product type n, .done (value actual.val n) store) ↔ 4 * n + 1 ≤ fuel) ∧
    ((∃ checkpoint, runRuntimeFunction? (table type) owner (declaration n) (arguments actual) fuel store =
      some (product type n, .outOfFuel checkpoint)) ↔ fuel < 4 * n + 1) :=
  ⟨(preparation actual n).complete, rfl, path actual.val store n k, (costed actual n store).run_done_iff, (costed actual n store).run_outOfFuel_iff⟩

theorem typed_products_preserve_the_entire_compiled_record_under_semantic_extension
    (type : Core.Ty) (n : Nat) (next : TypeNameTable) (extension : TypeNameTable.Extends (table type) next) :
    RuntimeFunctionCompiles next owner (declaration n) (compiled type n) ∧
    compileRuntimeFunction? next owner (declaration n) = some (compiled type n) :=
  ⟨(compilation type n).extend_types extension, compileRuntimeFunction?_some_of_extends extension (compilation type n).complete⟩

theorem nominal_returns_and_even_unused_nominal_parameters_do_not_supply_actual_values (nominal : Core.DataTypeId) :
    compileRuntimeFunction? (table (.namedData nominal)) owner (declaration 2) = some (compiled (.namedData nominal) 2) ∧
    compileRuntimeFunction? (table (.namedData nominal)) owner (declaration 0) = some (compiled (.namedData nominal) 0) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  refine ⟨(compilation _ _).complete, (compilation _ _).complete, ?_⟩
  rintro ⟨⟨type, actual, typed⟩, same⟩; cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem opaque_actual_values_form_products_without_allocation_or_invocation (location : Core.Location) (word : Core.Word) :
    evaluateRuntimeFunctionWithCost? (table (.cell .word)) owner (declaration 1)
      (arguments ⟨.cellRef .word location, .cellRef⟩) = some (.product (.cell .word) .unit, .pair (.cellRef .word location) .unit, 5) ∧
    evaluateRuntimeFunctionWithCost? (table (.function .bool .word)) owner (declaration 1)
      (arguments ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩) =
      some (.product (.function .bool .word) .unit, .pair (.closure .bool .word (.var 1) [.word word]) .unit, 5) :=
  ⟨(runtimeFunctionEvaluatesWithCost_iff_evaluate.mp (costed _ 1 [])).2,
    (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp (costed _ 1 [])).2⟩

theorem store_replay_preserves_results_but_not_a_different_final_store
    {type : Core.Ty} (actual : Actual type) (n : Nat) (initial final : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table type) owner (declaration n) (arguments actual) initial
      (product type n) (value actual.val n) final (4 * n + 1) ↔ final = initial := by
  have computed := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp (costed actual n initial)).2
  rw [runtimeFunctionEvaluatesWithCost_iff_evaluate, computed]; simp

theorem genuine_pair_checkpoint_keeps_the_unit_tail_and_original_actual_argument
    {type : Core.Ty} (actual : Actual type) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? (table type) owner (declaration 1) (arguments actual) 4 store =
      some (.product type .unit, .outOfFuel ⟨.ret .unit, [.pairApply actual.val], store⟩) ∧
    Core.Steps 1 ⟨.ret .unit, [.pairApply actual.val], store⟩ (.final (.pair actual.val .unit) store) ∧
    runRuntimeFunction? (table type) owner (declaration 1) (arguments actual) (4 + additional) store =
      some (.product type .unit, Core.runStateful additional ⟨.ret .unit, [.pairApply actual.val], store⟩) ∧
    Core.runStateful 0 (.final .unit store) = .done .unit store := by
  have exhausted : runRuntimeFunction? (table type) owner (declaration 1) (arguments actual) 4 store =
      some (.product type .unit, .outOfFuel ⟨.ret .unit, [.pairApply actual.val], store⟩) := by
    rw [(compilation type 1).run_eq (arguments actual) rfl]; rfl
  exact ⟨exhausted, ((costed actual 1 store).residual_of_outOfFuel exhausted).2, runRuntimeFunction?_resume exhausted additional, rfl⟩

theorem same_typed_swapped_core_is_not_compilation :
    Core.HasType [.unit] (.pair .unit (.var 0)) (.product .unit .unit) ∧
    ¬ RuntimeFunctionCompiles (table .unit) owner (declaration 1) { compiled .unit 1 with core := .pair .unit (.var 0) } := by
  refine ⟨.pair .unit (.var rfl), ?_⟩
  intro forged
  have wrong := congrArg CompiledRuntimeFunction.core (forged.result_unique (compilation .unit 1))
  cases wrong

private def strictBody : Syntax.Block := ⟨span,
  [⟨span, .letDecl ⟨span, "unused"⟩ (some (named "Payload")) (some ⟨span, .identifier ⟨span, "seed"⟩⟩)⟩,
   ⟨span, .returnStmt (some (source 1))⟩]⟩
private def strictDeclaration := entry (clause span span [annotation 1]) [parameter (named "Payload")] strictBody
private def strictCore : Core.Expr := .letE (.var 0) (.pair (.var 1) .unit)
private theorem strictCompilation (type : Core.Ty) :
    RuntimeFunctionCompiles (table type) owner strictDeclaration ⟨initial type, strictCore, .product type .unit⟩ :=
  ⟨header type 1, (compilation type 1).parameters,
    .binding (.named .head) (by change "unused" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.single (.expression (.pair (.identifier (.tail (by change "unused" ≠ "seed"; decide) .head)) .unit)
        (.pair (.var (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)) .unit)
        (.pair (.var (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)) .unit)))⟩

theorem named_unused_initializers_remain_strict_before_a_structural_product_return
    {type : Core.Ty} (actual : Actual type) (store : Core.Store) (fuel : Nat) :
    RuntimeFunctionCompiles (table type) owner strictDeclaration ⟨initial type, strictCore, .product type .unit⟩ ∧
    RuntimeFunctionEvaluatesWithCost (table type) owner strictDeclaration (arguments actual) store
      (.product type .unit) (.pair actual.val .unit) store 8 ∧
    (runRuntimeFunction? (table type) owner strictDeclaration (arguments actual) fuel store =
      some (.product type .unit, .done (.pair actual.val .unit) store) ↔ 8 ≤ fuel) := by
  have cost : RuntimeFunctionEvaluatesWithCost (table type) owner strictDeclaration (arguments actual) store
      (.product type .unit) (.pair actual.val .unit) store 8 := by
    apply RuntimeFunctionEvaluatesWithCost.intro (declaration := strictDeclaration) (prepared := ⟨inputs actual, strictCore, .product type .unit⟩)
      ⟨header type 1, (preparation actual 1).parameters, (strictCompilation type).body⟩
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 5)
    · exact .identifier .head .head
    · apply TypedLetReturnTreeEvaluatesWithCost.single
      apply ReturnBodyEvaluatesWithCost.expression
      apply LocalExpressionEvaluatesWithCost.pair (leftCost := 1) (rightCost := 1)
      · exact .identifier (.tail (by change "unused" ≠ "seed"; decide) .head) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
      · exact .unit
  exact ⟨strictCompilation type, cost, cost.run_done_iff⟩

private def letBody (annotation : Syntax.TypeExpr) : Syntax.Block :=
  ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ (some annotation) (some (source 0))⟩, ⟨span, .returnStmt (some (source 0))⟩]⟩
theorem structural_annotations_remain_outside_the_old_named_only_and_prefix_adapters
    (types : TypeNameTable) (elements : List Syntax.TypeExpr) :
    interpretTypeName? types ⟨span, .tuple elements⟩ = none ∧
    elaborateTypedLetReturnBody? types owner .empty (letBody ⟨span, .tuple elements⟩) = none := by
  constructor
  · rfl
  · apply elaborateTypedLetReturnBody?_eq_none_iff.mpr
    rintro ⟨type, typing⟩
    cases typing with
    | terminal child => cases child with | single child => cases child
    | binding meaning _ _ _ => cases meaning

theorem raw_unit_success_does_not_bypass_a_missing_child_in_the_return_annotation :
    evaluateTypedLetReturnTreeWithCost? owner [] [] (body 0) = some (.unit, 1) ∧
    compileRuntimeFunction? [] owner
      (entry (clause span span [⟨span, .tuple [annotation 0, named "Missing"]⟩]) [] (body 0)) = none ∧
    evaluateRuntimeFunctionWithCost? [] owner
      (entry (clause span span [⟨span, .tuple [annotation 0, named "Missing"]⟩]) [] (body 0)) [] = none := by
  refine ⟨evaluateTypedLetReturnTreeWithCost?_complete
    (TypedLetReturnTreeEvaluatesWithCost.single (owner := owner) (initialStore := []) (.expression .unit)), ?_, ?_⟩
  · simp [compileRuntimeFunction?, entry, signature, clause, interpretRuntimeFunctionHeader?, interpretRuntimeReturnType?,
      interpretStructuralType?, annotation, named, TypeNameTable.lookup?]
  · apply evaluateRuntimeFunctionWithCost?_eq_none_iff.mpr
    simp [prepareRuntimeFunction?, entry, signature, clause, interpretRuntimeFunctionHeader?, interpretRuntimeReturnType?,
      interpretStructuralType?, annotation, named, TypeNameTable.lookup?]

end Tests.FrontendStructuralReturn
end

section
-- leanmerge: from Solcore.Test.FrontendStructuralTypeProperties
/-! Independent original-syntax meanings, not interpreter-generated expectations.
Structural results need no whole-type table row or runtime inhabitant. -/
set_option autoImplicit false
namespace Tests.FrontendStructuralType
open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "structural-type.sol"⟩, 0, 1⟩
private def qualified (s : Syntax.SourceSpan) (head : String) (tail : List String := []) : Syntax.QualifiedName :=
  ⟨s, ⟨⟨⟨s, head⟩, tail.map (fun text => ⟨s, text⟩)⟩⟩⟩
private def named (s : Syntax.SourceSpan) (head : String) (tail : List String := []) : Syntax.TypeExpr :=
  ⟨s, .named (qualified s head tail) none⟩
private def unit (s : Syntax.SourceSpan) : Syntax.TypeExpr := ⟨s, .tuple []⟩
private def single (s : Syntax.SourceSpan) (child : Syntax.TypeExpr) : Syntax.TypeExpr := ⟨s, .tuple [child]⟩
private def pair (s : Syntax.SourceSpan) (left right : Syntax.TypeExpr) : Syntax.TypeExpr := ⟨s, .tuple [left, right]⟩
private theorem key (s : Syntax.SourceSpan) (head : String) (tail : List String) :
    qualifiedTypeNameKey (qualified s head tail) = head :: tail := by
  simp [qualifiedTypeNameKey, qualified, Syntax.NonemptyList.toList, List.map_map, Function.comp_def]

theorem four_independent_rules_keep_arbitrary_ranges_tables_and_leaf_types
    (outer childSpan : Syntax.SourceSpan) (table : TypeNameTable) (head : String) (tail : List String)
    (type : Core.Ty) (found : TypeNameTable.Lookup table (head :: tail) type) :
    StructuralTypeDenotes table (named childSpan head tail) type ∧
    StructuralTypeDenotes table (unit outer) .unit ∧
    StructuralTypeDenotes table (single outer (named childSpan head tail)) type ∧
    StructuralTypeDenotes table (pair outer (named childSpan head tail) (unit childSpan)) (.product type .unit) ∧
    interpretStructuralType? table (pair outer (named childSpan head tail) (unit childSpan)) = some (.product type .unit) := by
  have leaf : StructuralTypeDenotes table (named childSpan head tail) type := by
    apply StructuralTypeDenotes.named; simpa only [key] using found
  exact ⟨leaf, .unit, .single leaf, .pair leaf .unit, (StructuralTypeDenotes.pair leaf .unit).complete⟩

private def nested (s : Syntax.SourceSpan) (leaf : Syntax.TypeExpr) : Nat → Syntax.TypeExpr
  | 0 => single s (unit s)
  | n + 1 => pair s (single s leaf) (single s (nested s leaf n))
private def nestedType (leaf : Core.Ty) : Nat → Core.Ty
  | 0 => .unit
  | n + 1 => .product leaf (nestedType leaf n)
private theorem nestedMeaning (s : Syntax.SourceSpan) (table : TypeNameTable)
    (leaf : Syntax.TypeExpr) (type : Core.Ty) (meaning : StructuralTypeDenotes table leaf type) (n : Nat) :
    StructuralTypeDenotes table (nested s leaf n) (nestedType type n) := by
  induction n with
  | zero => exact .single .unit
  | succ n ih => exact .pair (.single meaning) (.single ih)

theorem every_depth_has_the_independently_nested_type_and_unique_meaning
    (s : Syntax.SourceSpan) (table : TypeNameTable) (leaf : Syntax.TypeExpr) (type : Core.Ty)
    (meaning : StructuralTypeDenotes table leaf type) (n : Nat) :
    interpretStructuralType? table (nested s leaf n) = some (nestedType type n) ∧
    StructuralTypeDenotes table (nested s leaf n) (nestedType type n) ∧
    (∀ other, StructuralTypeDenotes table (nested s leaf n) other → other = nestedType type n) := by
  have independent := nestedMeaning s table leaf type meaning n
  have accepted := independent.complete
  exact ⟨accepted, interpretStructuralType?_sound accepted,
    fun _ other => other.type_unique independent⟩

private def aliases : TypeNameTable := [(["L"], .word), (["R"], .bool)]
private theorem leftMeaning : StructuralTypeDenotes aliases (named span "L") .word := .named .head
private theorem rightMeaning : StructuralTypeDenotes aliases (named span "R") .bool :=
  .named (.tail (by decide) .head)

theorem equal_product_shape_does_not_justify_swapping_or_reassociating_types :
    interpretStructuralType? aliases (pair span (named span "L") (named span "R")) = some (.product .word .bool) ∧
    interpretStructuralType? aliases (pair span (named span "R") (named span "L")) = some (.product .bool .word) ∧
    (¬ StructuralTypeDenotes aliases (pair span (named span "L") (named span "R")) (.product .bool .word)) ∧
    interpretStructuralType? aliases (pair span (pair span (named span "L") (named span "R")) (unit span)) =
      some (.product (.product .word .bool) .unit) ∧
    interpretStructuralType? aliases (pair span (pair span (named span "L") (named span "R")) (unit span)) ≠
      some (.product .word (.product .bool .unit)) := by
  have binary := StructuralTypeDenotes.pair (span := span) leftMeaning rightMeaning
  have nested := (StructuralTypeDenotes.pair (span := span) binary (StructuralTypeDenotes.unit (span := span))).complete
  refine ⟨binary.complete, (StructuralTypeDenotes.pair rightMeaning leftMeaning).complete, ?_, nested, ?_⟩
  · intro wrong; cases wrong.type_unique binary
  · intro wrong; cases nested.symm.trans wrong

theorem old_named_provenance_survives_but_whole_structural_membership_is_unnecessary
    (table : TypeNameTable) (source : Syntax.TypeExpr) (type : Core.Ty)
    (old : TypeNameDenotes table source type) :
    (∃ key, (key, type) ∈ table) ∧ StructuralTypeDenotes table source type ∧
    interpretStructuralType? table source = some type ∧
    StructuralTypeDenotes [] (pair span (unit span) (unit span)) (.product .unit .unit) ∧
    (¬ ∃ key, (key, Core.Ty.product .unit .unit) ∈ ([] : TypeNameTable)) ∧
    interpretTypeName? [] (pair span (unit span) (unit span)) = none := by
  exact ⟨old.mem, old.structural, interpretStructuralType?_of_typeName old.complete,
    .pair .unit .unit, by simp, rfl⟩

theorem first_duplicate_wins_inside_a_product_without_builtin_spellings :
    interpretStructuralType? [(["Unit"], .bool), (["Unit"], .word)]
      (pair span (named span "Unit") (unit span)) = some (.product .bool .unit) ∧
    (["Unit"], Core.Ty.word) ∈ [(["Unit"], .bool), (["Unit"], .word)] ∧
    ¬ StructuralTypeDenotes [(["Unit"], .bool), (["Unit"], .word)]
      (pair span (named span "Unit") (unit span)) (.product .word .unit) := by
  have meaning : StructuralTypeDenotes [(["Unit"], .bool), (["Unit"], .word)]
      (pair span (named span "Unit") (unit span)) (.product .bool .unit) := .pair (.named .head) .unit
  refine ⟨meaning.complete, by simp, ?_⟩
  intro wrong; cases wrong.type_unique meaning

theorem qualified_components_raw_dots_and_empty_components_remain_distinct :
    interpretStructuralType? [(["A", "B"], .word), (["A.B"], .bool)]
      (pair span (named span "A" ["B"]) (named span "A.B")) = some (.product .word .bool) ∧
    interpretStructuralType? [(["A", "B"], .word)] (named span "A.B") = none ∧
    interpretStructuralType? [(["A", "", "B"], .unit)] (single span (named span "A" ["", "B"])) = some .unit ∧
    interpretStructuralType? [([], .word)] (named span "") = none ∧
    StructuralTypeDenotes [([""], .bool)] (named span "") .bool := by
  have dotted : StructuralTypeDenotes [(["A", "B"], .word), (["A.B"], .bool)]
      (pair span (named span "A" ["B"]) (named span "A.B")) (.product .word .bool) :=
    .pair (.named .head) (.named (.tail (by decide) .head))
  have emptyComponent : StructuralTypeDenotes [(["A", "", "B"], .unit)]
      (single span (named span "A" ["", "B"])) .unit := .single (.named .head)
  refine ⟨dotted.complete, ?_, emptyComponent.complete, ?_, .named .head⟩ <;>
    simp [interpretStructuralType?, named, key, TypeNameTable.lookup?]

private def reversed : Syntax.SourceSpan := ⟨⟨.external "raw", "invalid"⟩, 99, 2⟩
theorem invalid_ranges_and_outer_range_changes_do_not_change_whole_options
    (file : Syntax.SourceFile) (table : TypeNameTable) (source : Syntax.TypeExpr) :
    (¬ reversed.ValidFor file) ∧
    StructuralTypeDenotes table (pair reversed (single reversed (unit reversed)) (unit reversed)) (.product .unit .unit) ∧
    interpretStructuralType? table { source with span := reversed } = interpretStructuralType? table source := by
  exact ⟨by simp [Syntax.SourceSpan.ValidFor, reversed], .pair (.single .unit) .unit,
    interpretStructuralType?_span table source reversed⟩

theorem nominal_structural_types_need_neither_well_formed_data_nor_runtime_inhabitants
    (nominal : Core.DataTypeId) (definitions : Core.DataEnvironment) :
    StructuralTypeDenotes [(["N"], .namedData nominal)]
      (pair span (named span "N") (unit span)) (.product (.namedData nominal) .unit) ∧
    Core.HasType [.namedData nominal] (.pair (.var 0) .unit) (.product (.namedData nominal) .unit) definitions ∧
    (¬ ∃ actual, Core.ValueHasType actual (.namedData nominal)) := by
  refine ⟨.pair (.named .head) .unit, .pair (.var rfl) .unit, ?_⟩
  rintro ⟨actual, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def unsupported (child : Syntax.TypeExpr) : List Syntax.TypeExprValue :=
  [.named (qualified span "Known") (some ⟨span, ⟨child, []⟩⟩), .mapping span span child child,
   .proxy span child, .comptime span span child, .error]
theorem unsupported_constructors_cannot_be_rescued_by_meaningful_children
    (table : TypeNameTable) (child : Syntax.TypeExpr) (type : Core.Ty)
    (meaning : StructuralTypeDenotes table child type) (payload : Syntax.TypeExprValue)
    (present : payload ∈ unsupported child) (outer : Syntax.SourceSpan) :
    interpretStructuralType? table child = some type ∧ interpretStructuralType? table ⟨outer, payload⟩ = none ∧
    ¬ ∃ result, StructuralTypeDenotes table ⟨outer, payload⟩ result := by
  refine ⟨meaning.complete, ?_⟩
  simp only [unsupported, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp only [interpretStructuralType?], by rintro ⟨result, denoted⟩; cases denoted⟩

theorem larger_tuples_remain_named_only_rejections_and_missing_children_stay_strict
    (table : TypeNameTable) (a b c : Syntax.TypeExpr) (rest : List Syntax.TypeExpr) :
    interpretTypeName? table ⟨span, .tuple (a :: b :: c :: rest)⟩ = none ∧
    interpretStructuralType? [] (pair span (unit span) (named span "Missing")) = none ∧
    interpretStructuralType? [] (pair span (named span "Missing") (unit span)) = none ∧
    (¬ ∃ type, StructuralTypeDenotes [] (pair span (unit span) (named span "Missing")) type) ∧
    interpretTypeName? aliases (single span (named span "L")) = none ∧
    interpretStructuralType? aliases (single span (named span "L")) = some .word := by
  have absent : interpretStructuralType? [] (pair span (unit span) (named span "Missing")) = none := by
    simp [interpretStructuralType?, pair, unit, named, TypeNameTable.lookup?]
  refine ⟨rfl, absent, ?_, interpretStructuralType?_eq_none_iff.mp absent, rfl,
    (StructuralTypeDenotes.single leftMeaning).complete⟩ <;>
    simp [interpretStructuralType?, pair, unit, named, TypeNameTable.lookup?]

theorem arbitrary_nested_success_survives_append_and_fresh_prepend
    (table extras : TypeNameTable) (leaf : Syntax.TypeExpr) (type : Core.Ty)
    (meaning : StructuralTypeDenotes table leaf type) (n : Nat) (key : List String) (newType : Core.Ty)
    (fresh : key ∉ table.map Prod.fst) :
    StructuralTypeDenotes (table ++ extras) (nested span leaf n) (nestedType type n) ∧
    interpretStructuralType? ((key, newType) :: table) (nested span leaf n) = some (nestedType type n) := by
  have independent := nestedMeaning span table leaf type meaning n
  exact ⟨independent.extend_types (TypeNameTable.Extends.append_right table extras),
    interpretStructuralType?_some_of_extends (TypeNameTable.Extends.cons_fresh table key newType fresh) independent.complete⟩

private def one : TypeNameTable := [(["T"], .word)]
private def hiddenConflict : TypeNameTable := [(["T"], .word), (["T"], .bool)]
private theorem forward : TypeNameTable.Extends one hiddenConflict := TypeNameTable.Extends.append_right one [(["T"], .bool)]
private theorem backward : TypeNameTable.Extends hiddenConflict one := by
  intro key type found
  cases found with
  | head => exact .head
  | tail different found =>
      cases found with
      | head => exact False.elim (different rfl)
      | tail _ impossible => cases impossible

theorem unequal_tables_with_hidden_conflicts_preserve_every_optional_result (source : Syntax.TypeExpr) :
    one ≠ hiddenConflict ∧ TypeNameTable.Extends one hiddenConflict ∧ TypeNameTable.Extends hiddenConflict one ∧
    interpretStructuralType? one source = interpretStructuralType? hiddenConflict source ∧
    interpretStructuralType? hiddenConflict source = interpretStructuralType? one source ∧
    interpretStructuralType? hiddenConflict (pair span (unit span) (named span "Missing")) = none := by
  exact ⟨by decide, forward, backward,
    interpretStructuralType?_eq_of_mutual_extends forward backward source,
    interpretStructuralType?_congr_lookup hiddenConflict one
      (TypeNameTable.lookup?_eq_of_mutual_extends backward forward) source,
    by simp [interpretStructuralType?, pair, unit, named, key, hiddenConflict, TypeNameTable.lookup?]⟩

theorem one_way_extension_can_repair_an_unknown_child_but_head_override_is_not_extension :
    TypeNameTable.Extends [] [(["Missing"], .word)] ∧
    interpretStructuralType? [] (pair span (unit span) (named span "Missing")) = none ∧
    interpretStructuralType? [(["Missing"], .word)] (pair span (unit span) (named span "Missing")) =
      some (.product .unit .word) ∧
    (¬ TypeNameTable.Extends one ((["T"], .bool) :: one)) ∧
    (["T"], Core.Ty.word) ∈ ((["T"], .bool) :: one) := by
  have repaired : StructuralTypeDenotes [(["Missing"], .word)]
      (pair span (unit span) (named span "Missing")) (.product .unit .word) := .pair .unit (.named .head)
  refine ⟨TypeNameTable.Extends.cons_fresh [] ["Missing"] .word (by simp),
    by simp [interpretStructuralType?, pair, unit, named, TypeNameTable.lookup?],
    repaired.complete, ?_, by simp [one]⟩
  intro extension
  have wrong : TypeNameTable.Lookup ((["T"], .bool) :: one) ["T"] .word := extension .head
  have first : TypeNameTable.Lookup ((["T"], .bool) :: one) ["T"] .bool := .head
  cases wrong.type_unique first

theorem exact_executable_acceptance_is_the_independent_original_syntax_relation
    (table : TypeNameTable) (source : Syntax.TypeExpr) (type : Core.Ty)
    (name : Syntax.QualifiedName) (outer : Syntax.SourceSpan) :
    (interpretStructuralType? table source = some type ↔ StructuralTypeDenotes table source type) ∧
    (interpretStructuralType? table source = none ↔ ¬ ∃ result, StructuralTypeDenotes table source result) ∧
    interpretStructuralType? table ⟨outer, .named name none⟩ = interpretTypeName? table ⟨outer, .named name none⟩ :=
  ⟨interpretStructuralType?_iff, interpretStructuralType?_eq_none_iff,
    interpretStructuralType?_named_eq_typeName table name outer⟩

end Tests.FrontendStructuralType
end

section
-- leanmerge: from Solcore.Test.FrontendUnitProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedInferredLets
/-! Original optional annotations, independent source evidence and hand-composed
Core paths. Static input types are independent of the actual values returned. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace InferredLets
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Inferred", by decide⟩], by decide⟩⟩, 17⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def inputs (type : Core.Ty) : LocalTypeInputs := ⟨[
  ⟨"c", ⟨other, 999⟩, .bool⟩, ⟨"r", id 2, .word⟩, ⟨"x", id 7, type⟩, ⟨"x", id 3, .bool⟩], by
    change ([⟨other, 999⟩, id 2, id 7, id 3] : List Resolved.LocalId).Nodup; decide⟩
private def env (value : Core.Value) (choice : Bool) : Resolved.Environment :=
  [(⟨other, 999⟩, .bool choice), (id 2, w 2), (id 7, value), (id 3, .bool false)]
private def stores : List Core.Store := [[], [w 91, .cellRef .word 40, .bool false]]
private def parsed (content : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main, "inferred.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok body next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"complete block rejected: {content}")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (body.span = ⟨file.id, 0, content.utf8ByteSize⟩)) "original block/range changed"
  return body
private structure Expression (s : LocalTypeInputs) (e : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.ids resolved core
  typing : Resolved.HasType s.context resolved type
  raw : LocalExpressionEvaluatesWithCost s.names e store source value store cost
  paths : ∀ k, Core.Steps cost ⟨.eval core e.values, k, store⟩ ⟨.ret value, k, store⟩
private def expression (s : LocalTypeInputs) (e : Resolved.Environment) (aligned : e.ids = s.ids)
    (store : Core.Store) (source : Syntax.Expr) : IO (Expression s e store source) := do
  match atSource : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | none => throw (IO.userError "independent name absent")
      | some binder =>
          match typed : s.context.lookup? binder, found : e.lookup? binder, indexed : Resolved.LocalScope.index? s.ids binder with
          | some type, some value, some index =>
              let position := Resolved.LocalScope.index?_iff.mp indexed
              return ⟨.var binder, .var index, type, value, 1,
                by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named), .var position,
                .var (Resolved.LocalScope.lookup?_iff.mp typed),
                by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found),
                fun _ => .cons (.var ((Resolved.LocalScope.lookup_iff_getElem? (aligned.symm ▸ position)).mp
                  (Resolved.LocalScope.lookup?_iff.mp found))) .refl⟩
          | _, _, _ => throw (IO.userError "independent row absent")
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, .unit, .unit, .unit, 1,
      by rw [atSource]; exact .unit, .unit, .unit, by rw [atSource]; exact .unit, fun _ => .cons .unit .refl⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← expression s e aligned store left; let b ← expression s e aligned store right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type, .pair a.value b.value, a.cost + b.cost + 3,
        by rw [atSource]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing,
        by rw [atSource]; exact .pair a.raw b.raw, fun k => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core e.values :: k)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← expression s e aligned store left; let b ← expression s e aligned store right
      match av : a.value, bv : b.value with
      | .word x, .word y =>
          if leftType : a.type = .word then
            if rightType : b.type = .word then
            return ⟨.binary .wordSub a.resolved b.resolved, .binary .wordSub a.core b.core, .word, .word (x.sub y), a.cost + b.cost + 3,
              by rw [atSource]; exact .subtract a.resolution b.resolution, .binary a.lowered b.lowered,
              .binary (show Resolved.HasType s.context a.resolved .word from leftType ▸ a.typing)
                (show Resolved.HasType s.context b.resolved .word from rightType ▸ b.typing),
              by rw [atSource]; exact .subtract (av ▸ a.raw) (bv ▸ b.raw), fun k => by
                have path := Core.Steps.cons .enterBinary ((av ▸ a.paths (.binaryRight .wordSub b.core e.values :: k)).trans
                  (.cons .enterBinaryRight ((bv ▸ b.paths _).trans (.cons (.applyBinary rfl) .refl))))
                simpa only [Nat.add_assoc] using path⟩
            else throw (IO.userError "right is not Word")
          else throw (IO.userError "left is not Word")
      | _, _ => throw (IO.userError "actual operand not Word")
  | _ => throw (IO.userError "outside independent expression script")
termination_by sizeOf source
private structure Certificate (s : LocalTypeInputs) (e : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  elaboration : TypedLetReturnTreeElaborates types owner s body core type
  raw : TypedLetReturnTreeEvaluatesWithCost owner s.names e store body value store cost
  paths : ∀ k, Core.Steps cost ⟨.eval core e.values, k, store⟩ ⟨.ret value, k, store⟩
private def certify (s : LocalTypeInputs) (e : Resolved.Environment) (aligned : e.ids = s.ids)
    (store : Core.Store) (body : Syntax.Block) : IO (Certificate s e store body) := do
  match atBody : body with
  | ⟨_, [⟨_, .returnStmt (some source)⟩]⟩ =>
      let a ← expression s e aligned store source
      return ⟨a.core, a.type, a.value, a.cost,
        by rw [atBody]; exact .single (.expression a.resolution (by simpa only [LocalTypeInputs.context_ids] using a.lowered) a.typing),
        by rw [atBody]; exact .single (.expression a.raw), a.paths⟩
  | ⟨span, ⟨_, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      if unused : name.value ∉ s.names.map Prod.fst then
        let a ← expression s e aligned store initializer
        let next := s.bindFresh owner name.value a.type
        let b ← certify next ((Resolved.freshLocalId owner s.ids, a.value) :: e)
          (by simpa only [next, LocalTypeInputs.bindFresh_ids, Resolved.LocalScope.ids, List.map_cons]
            using congrArg (List.cons _) aligned) store ⟨span, rest⟩
        let rawTail := by simpa only [next, LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using b.raw
        let common := fun elaboration raw => (⟨.letE a.core b.core, b.type, b.value, a.cost + b.cost + 2, elaboration, raw, fun k => by
          have path := Core.Steps.cons .enterLet ((a.paths (.letBody b.core e.values :: k)).trans (.cons .bindLet (b.paths k)))
          simpa only [Resolved.LocalScope.values, List.map_cons, Nat.add_assoc] using path⟩ : Certificate s e store body)
        match atAnnotation : annotation with
        | none => return (common (by rw [atBody, atAnnotation]; exact .inferred unused a.resolution a.lowered a.typing b.elaboration)
            (by rw [atBody, atAnnotation]; exact .inferred a.raw (by simpa only [LocalTypeInputs.names_ids] using rawTail)))
        | some written =>
            match atWritten : written with
            | ⟨_, .named name none⟩ =>
                if meaning : types.lookup? (qualifiedTypeNameKey name) = some a.type then
                  return (common (by rw [atBody, atAnnotation, atWritten]; exact .binding (.named (TypeNameTable.lookup?_iff.mp meaning)) unused a.resolution a.lowered a.typing b.elaboration)
                    (by rw [atBody, atAnnotation]; exact .binding a.raw (by simpa only [LocalTypeInputs.names_ids] using rawTail)))
                else throw (IO.userError "written annotation disagrees")
            | _ => throw (IO.userError "outside independent annotation script")
      else throw (IO.userError "written name is already used")
  | ⟨_, [⟨_, .ifThen guard yes (some no)⟩]⟩ =>
      let c ← expression s e aligned store guard
      let a ← certify s e aligned store yes; let b ← certify s e aligned store no
      if ct : c.type = .bool then
        if bt : b.type = a.type then
        have elaboration : TypedLetReturnTreeElaborates types owner s body (.ifE c.core a.core b.core) a.type := by
          rw [atBody]; exact .conditional c.resolution c.lowered (ct ▸ c.typing) a.elaboration (bt ▸ b.elaboration)
        match cv : c.value with
        | .bool true => return ⟨.ifE c.core a.core b.core, a.type, a.value, c.cost + a.cost + 2, elaboration,
            by rw [atBody]; exact .ifTrue (cv ▸ c.raw) a.raw, fun k => by
              have path := Core.Steps.cons .enterIf ((cv ▸ c.paths (.ifBranches a.core b.core e.values :: k)).trans (.cons .chooseTrue (a.paths k)))
              simpa only [Nat.add_assoc] using path⟩
        | .bool false => return ⟨.ifE c.core a.core b.core, a.type, b.value, c.cost + b.cost + 2, elaboration,
            by rw [atBody]; exact .ifFalse (cv ▸ c.raw) b.raw, fun k => by
              have path := Core.Steps.cons .enterIf ((cv ▸ c.paths (.ifBranches a.core b.core e.values :: k)).trans (.cons .chooseFalse (b.paths k)))
              simpa only [Nat.add_assoc] using path⟩
        | _ => throw (IO.userError "actual guard not Bool")
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "guard type not Bool")
  | _ => throw (IO.userError "outside independent body script")
termination_by sizeOf body
private def checked (content : String) (inputType : Core.Ty) (actual : Core.Value) (choice : Bool)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let body ← parsed content; let s := inputs inputType; let e := env actual choice
  for store in stores do
    let cert ← certify s e rfl store body
    check (decide (cert.core = core ∧ cert.type = type ∧ cert.value = value ∧ cert.cost = cost)) "independent certificate disagreed"
    let accepted := cert.elaboration.complete
    have _ := cert.elaboration.hasType
    match atShape : body with
    | ⟨_, ⟨_, .letDecl _ none (some _)⟩ :: _⟩ =>
        have _ := elaborateTypedLetReturnTree?_inferred_children (by rw [← atShape]; exact accepted)
        pure ()
    | _ => pure ()
    check (decide (elaborateTypedLetReturnTree? types owner s body = some (core, type) ∧
      evaluateTypedLetReturnTreeWithCost? owner s.names e body = some (value, cost) ∧
      Core.infer? s.context.values core = some type ∧ cost ≤ typedLetReturnTreeFuelBound body)) "fixed static/raw expectations changed"
    let start := Core.State.initial cert.core e.values store
    for k in [[], [.letBody (.var 0) [w 17]], [.unaryApply .wordNot]] do
      have _ := cert.paths k
      have _ := cert.raw.checked_toStepsWithContinuation accepted rfl k
      pure ()
    for fuel in List.range (typedLetReturnTreeFuelBound body + 3) do
      check (match Core.runStateful fuel start with
        | .done v st => decide (cost ≤ fuel ∧ v = value ∧ st = store)
        | .outOfFuel cp => decide (fuel < cost ∧ cp.store = store)
        | _ => false) "exact fuel/store boundary changed"
    for spent in List.range cost do
      match exhausted : Core.runStateful spent start with
      | .outOfFuel cp =>
          have _ := (cert.paths []).residual_of_outOfFuel exhausted
          have _ := cert.raw.checked_residual_of_outOfFuel accepted rfl exhausted
          for remaining in [0, 1, cost - spent, cost - spent + 2] do
            have _ := Core.runStateful_resume exhausted remaining
            check (decide (Core.runStateful remaining cp = Core.runStateful (spent + remaining) start)) "genuine checkpoint replay changed"
          check (decide (Core.runStateful (cost - spent) cp = .done value store)) "independent residual budget changed"
          if cost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 cp | throw (IO.userError "second chunk missing")
            check (decide (Core.runStateful (cost - spent - 1) next = .done value store)) "third chunk lost the captured continuation"
          if spent > 0 then check (Core.runStateful (cost - spent) start != .done value store) "restart impersonated resume"
      | _ => throw (IO.userError "checkpoint missing")
private def spine (n level : Nat) : String × Core.Expr :=
  match n with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 2 else 0))
  | n + 1 =>
      let (tail, core) := spine n (level + 1)
      (s!"let z{level}" ++ (if level % 2 = 0 then "" else ": Word") ++ "=" ++
        (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail, .letE (.var (if level = 0 then 2 else 0)) core)
private def originalOne (bs ls ns is rs us : Syntax.SourceSpan) : Syntax.Block :=
  ⟨bs, [⟨ls, .letDecl ⟨ns, "z"⟩ none (some ⟨is, .identifier ⟨is, "x"⟩⟩)⟩,
    ⟨rs, .returnStmt (some ⟨us, .identifier ⟨us, "z"⟩⟩)⟩]⟩
private theorem oneElaboration (type : Core.Ty) (bs ls ns is rs us : Syntax.SourceSpan) :
    TypedLetReturnTreeElaborates types owner (inputs type) (originalOne bs ls ns is rs us)
      (.letE (.var 2) (.var 0)) type := by
  apply TypedLetReturnTreeElaborates.inferred (inferredType := type) (initializerResolved := .var (id 7))
  · change "z" ∉ (["c", "r", "x", "x"] : List String); decide
  · exact .identifier (.tail (by change "c" ≠ "x"; decide) (.tail (by change "r" ≠ "x"; decide) .head))
  · exact .var (.tail (by decide) (.tail (by decide) .head))
  · exact .var (.tail (by decide) (.tail (by decide) .head))
  · exact .single (.expression (.identifier .head) (.var .head) (.var .head))
private theorem oneCoreType (type : Core.Ty) (definitions : Core.DataEnvironment) :
    Core.HasType (inputs type).context.values (.letE (.var 2) (.var 0)) type definitions :=
  .letE (.var rfl) (.var rfl)
private def checkedOpaque (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : IO Unit := do
  have _ : Core.EnvironmentHasTypes (env value true).values (inputs type).context.values :=
    .cons .bool (.cons .word (.cons typed (.cons .bool .nil)))
  checked "{let z=x;let q=z;return q;}" type value true (.letE (.var 2) (.letE (.var 0) (.var 0))) type value 7
end InferredLets
open InferredLets

def frontendParsedInferredLetTests : IO Unit := do
  for depth in [3, 4, 9, 20, 40] do
    let (content, core) := spine depth 0
    checked ("{" ++ content ++ "}") .word (w 9) true core .word (w 9) (3 * depth + 1)
  checked "{let z=x - r;return r;}" .word (w 9) true (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 2)) .word (w 2) 8
  checked "{let z=x - r;return z;}" .word (w 9) true (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 0)) .word (w 7) 8
  checked "{let z=(x,r);return z;}" .word (w 9) true (.letE (.pair (.var 2) (.var 1)) (.var 0)) (.product .word .word) (.pair (w 9) (w 2)) 8
  checked "{let z=();return z;}" .word (w 9) true (.letE .unit (.var 0)) .unit .unit 4
  checked "{let z=c;return z;}" .word (w 9) false (.letE (.var 0) (.var 0)) .bool (.bool false) 4
  checkedOpaque (.cell .word) (.cellRef .word 999) .cellRef
  checkedOpaque (.function .word .word) (.closure .word .word (.var 1) [w 7]) (.closure (.cons .word .nil) (.var rfl))
  checkedOpaque (.product .unit (.cell .word)) (.pair .unit (.cellRef .word 19)) (.pair .unit .cellRef)
  checkedOpaque .unit .unit .unit
  for c in [false, true] do
    checked "{if(c){let z=x;return z;}else{return r;}}" .word (w 9) c
      (.ifE (.var 0) (.letE (.var 2) (.var 0)) (.var 1)) .word (if c then w 9 else w 2) (if c then 7 else 4)
  let body ← parsed "{let z=x;return z;}"
  match body.value with
  | [⟨span, .letDecl name none (some initializer)⟩, ⟨returnSpan, .returnStmt (some result)⟩] =>
      check (decide (span.startByte = 1 ∧ span.endByte = 9 ∧ name.value = "z" ∧
        initializer.span.startByte = 7 ∧ initializer.span.endByte = 8)) "original none annotation or byte ranges changed"
      let source := originalOne body.span span name.span initializer.span returnSpan result.span
      check (body == source) "independent original source reconstruction disagreed"
      for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨99⟩) (.cell (.namedData ⟨13⟩)),
          .function (.namedData ⟨99⟩) (.namedData ⟨13⟩)] do
        let evidence := oneElaboration type body.span span name.span initializer.span returnSpan result.span
        have _ : ∀ definitions, Core.HasType (inputs type).context.values (.letE (.var 2) (.var 0)) type definitions := oneCoreType type
        have _ : ¬ TypedLetReturnTreeElaborates types owner (inputs type) source (.var 2) type := by
          intro wrong
          have impossible := evidence.result_unique wrong
          cases impossible.1
        check (decide (elaborateTypedLetReturnTree? types owner (inputs type) body = some (.letE (.var 2) (.var 0), type) ∧
          elaborateTypedLetReturnTree? [] owner (inputs type) body = some (.letE (.var 2) (.var 0), type) ∧
          Core.infer? (inputs type).context.values (.var 2) = some type)) "value-free nominal or same-typed wrong-Core boundary changed"
  | _ => throw (IO.userError "inferred original syntax was rewritten")
  check (decide (Resolved.freshLocalId owner (inputs .word).ids = InferredLets.id 8 ∧
    ((inputs .word).bindFresh owner "z" .word).context = (InferredLets.id 8, .word) :: (inputs .word).context)) "sparse owner-relative scope changed"
  check ((elaborateTypedLetReturnBody? types owner (inputs .word) body).isNone) "old annotated-only prefix unexpectedly widened"
  for store in stores do
    let e := env (w 9) true
    check (decide (Core.runStateful 2 (.initial (.letE (.var 2) (.var 0)) e.values store) =
      .outOfFuel ⟨.ret (w 9), [.letBody (.var 0) e.values], store⟩)) "old-scope initializer frame changed"
  for content in ["{let z;return x;}", "{let z: Word;return x;}", "{let z=missing;return x;}",
      "{let z=z;return x;}", "{let z=q;let q=x;return z;}", "{let z=~c;return x;}", "{let z=f(x);return x;}"] do
    check ((evaluateTypedLetReturnTreeWithCost? owner (inputs .word).names (env (w 9) true) (← parsed content)).isNone)
      "invalid or missing initializer acquired raw evaluation"
  for content in ["{let z;return x;}", "{let z: Word;return x;}", "{let z=missing;return x;}", "{let z=z;return x;}",
      "{let z=q;let q=x;return z;}", "{let x=r;return x;}", "{let z=x;let z=r;return z;}",
      "{if(c){let z=x;return z;}else{return z;}}", "{let z=~c;return x;}", "{let z=f(x);return x;}"] do
    check ((elaborateTypedLetReturnTree? types owner (inputs .word) (← parsed content)).isNone) "invalid scope/strict initializer accepted"
  let skipped ← parsed "{if(c){let z=x;return z;}else{let q=missing;return q;}}"
  check (decide (evaluateTypedLetReturnTreeWithCost? owner (inputs .word).names (env (w 9) true) skipped = some (w 9, 7) ∧
    elaborateTypedLetReturnTree? types owner (inputs .word) skipped = none)) "raw selection bypassed whole arm checking"

end Tests
end
