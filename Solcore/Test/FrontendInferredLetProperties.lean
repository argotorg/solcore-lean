import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.TypedLetReturnBody

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
