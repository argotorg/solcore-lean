import Solcore.Frontend.TypedLetReturnTreeResumptionProperties
import Solcore.Frontend.TypedLetReturnTreeStoreProperties
import Solcore.Frontend.TypedLetReturnTreeRunnerOwnerProperties
import Solcore.Frontend.TypedLetReturnTreeLookupProperties
import Solcore.Frontend.TypedLetReturnTreeFuelBoundProperties
import Solcore.Frontend.TypedLetReturnBody

/-! Original discard statements retain source scopes. Hidden Core binders
retain strict work without introducing source names or runtime parameters. -/
set_option autoImplicit false
namespace Tests.FrontendDiscardStatement
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Discard", by decide⟩], by decide⟩⟩, 0⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "discard.sol"⟩, 17, 9⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def discard (expression : Syntax.Expr) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span, ⟨span, .expression expression true⟩ :: tail.value⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def mixed : Bool → List String → String → Syntax.Block
  | _, [], previous => returned previous
  | flag, name :: rest, previous => discard (ref previous)
      ⟨span, ⟨span, .letDecl ⟨span, name⟩ (if flag then some annotation else none)
        (some (ref previous))⟩ :: (mixed (!flag) rest name).value⟩
private def core : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .letE (.var 0) (.letE (.var 1) (core n))
private def seed (type : Core.Ty) := LocalTypeInputs.empty.bindFresh owner "seed" type
private theorem stable (n cutoff : Nat) (positive : 0 < cutoff) : (core n).weakenAt cutoff = core n := by
  induction n generalizing cutoff with
  | zero => simp [core, Core.Expr.weakenAt, Nat.not_le.mpr positive]
  | succ n ih =>
      simp only [core, Core.Expr.weakenAt]
      rw [if_neg (by omega), if_neg (by omega), ih (cutoff + 1 + 1) (by omega)]
private theorem eta (flag : Bool) (names : List String) (previous : String) :
    (⟨span, (mixed flag names previous).value⟩ : Syntax.Block) = mixed flag names previous := by cases names <;> rfl
private theorem elaborated (flag : Bool) (names : List String) (previous : String) (type : Core.Ty)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var 0)) (typed : Resolved.HasType initial.context resolved type) :
    TypedLetReturnTreeElaborates (types type) owner initial (mixed flag names previous) (core names.length) type := by
  induction names generalizing flag previous initial resolved with
  | nil =>
      simp only [mixed, List.length_nil, core]
      exact .single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typed)
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      have tail := ih (!flag) name (initial.bindFresh owner name type) _ parts.2 (by
        intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩)
        (.identifier .head) (.var .head) (.var .head)
      have bound : TypedLetReturnTreeElaborates (types type) owner initial
          ⟨span, ⟨span, .letDecl ⟨span, name⟩ (if flag then some annotation else none) (some (ref previous))⟩ ::
            (mixed (!flag) rest name).value⟩ (.letE (.var 0) (core rest.length)) type := by
        cases flag
        · exact .inferred (fresh name (by simp)) resolution lowered typed (by simpa only [eta] using tail)
        · exact .binding (.named .head) (fresh name (by simp)) resolution lowered typed (by simpa only [eta] using tail)
      have full : TypedLetReturnTreeElaborates (types type) owner initial (mixed flag (name :: rest) previous)
          (.letE (.var 0) ((Core.Expr.letE (.var 0) (core rest.length)).weakenAt 0)) type :=
        .discard resolution lowered typed bound
      simpa [core, Core.Expr.weakenAt, stable] using full
private theorem seedElab (flag : Bool) (names : List String) (type : Core.Ty)
    (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed type) (mixed flag names "seed") (core names.length) type := by
  apply elaborated flag names "seed" type (seed type) _ distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head
private theorem counted (flag : Bool) (names : List String) (previous : String)
    (table : LocalNameTable) (environment : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost table environment store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment store (mixed flag names previous) value store (6*names.length+1) := by
  induction names generalizing flag previous table environment with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
      let fresh := Resolved.freshLocalId owner (table.map Prod.snd)
      have tail := ih (!flag) name ((name, fresh) :: table) ((fresh, value) :: environment) (.identifier .head .head)
      have arithmetic : 1 + (1 + (6*rest.length+1) + 2) + 2 = 6*(name :: rest).length+1 := by simp; omega
      rw [← arithmetic]
      cases flag
      · exact .discard head (.inferred head (by simpa only [eta] using tail))
      · exact .discard head (.binding head (by simpa only [eta] using tail))
private theorem path (n : Nat) (value : Core.Value) (tail : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (6*n+1) ⟨.eval (core n) (value :: tail), k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing tail k with
  | zero => exact .cons (.var rfl) .refl
  | succ n ih =>
      have steps := Core.Steps.cons .enterLet (.cons (.var (index := 0) rfl) (.cons .bindLet
        (.cons .enterLet (.cons (.var (index := 1) rfl) (.cons .bindLet (ih (value :: value :: tail) k))))))
      simpa [core, Nat.mul_add, Nat.add_assoc] using steps

theorem arbitrary_mixed_prefixes_keep_original_annotations_and_exact_core
    (flag : Bool) (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed type) (mixed flag names "seed") (core names.length) type ∧
    TypedLetReturnTreeHasType (types type) owner (seed type) (mixed flag names "seed") type ∧
    elaborateTypedLetReturnTree? (types type) owner (seed type) (mixed flag names "seed") = some (core names.length, type) :=
  ⟨seedElab flag names type distinct fresh, (seedElab flag names type distinct fresh).hasType,
    (seedElab flag names type distinct fresh).complete⟩

theorem raw_duplicate_names_still_evaluate_every_discard
    (flag : Bool) (names : List String) (value : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    TypedLetReturnTreeEvaluatesWithCost owner [("seed", id 0)] [(id 0, value)] store (mixed flag names "seed") value store (6*names.length+1) ∧
    evaluateTypedLetReturnTreeWithCost? owner [("seed", id 0)] [(id 0, value)] (mixed flag names "seed") = some (value, 6*names.length+1) ∧
    Core.Steps (6*names.length+1) ⟨.eval (core names.length) [value], k, store⟩ ⟨.ret value, k, store⟩ := by
  have evaluation := counted flag names "seed" [("seed", id 0)] [(id 0, value)] value store (.identifier .head .head)
  exact ⟨evaluation, evaluateTypedLetReturnTreeWithCost?_complete evaluation, path _ value [] store k⟩

theorem nominal_static_types_need_no_discardable_runtime_inhabitant (nominal : Core.DataTypeId) :
    elaborateTypedLetReturnTree? (types (.namedData nominal)) owner (seed (.namedData nominal))
      (mixed false ["x", "y"] "seed") = some (core 2, .namedData nominal) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(seedElab false ["x", "y"] _ (by decide) (by decide)).complete, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem actual_cells_and_closures_are_discarded_without_inspection
    (location : Core.Location) (word : Core.Word) (store : Core.Store) (k : List Core.Frame) :
    Core.ValueHasType (.cellRef .word location) (.cell .word) ∧
    Core.ValueHasType (.closure .bool .word (.var 1) [.word word]) (.function .bool .word) ∧
    Core.Steps 7 ⟨.eval (core 1) [.cellRef .word location], k, store⟩ ⟨.ret (.cellRef .word location), k, store⟩ ∧
    Core.Steps 7 ⟨.eval (core 1) [.closure .bool .word (.var 1) [.word word]], k, store⟩
      ⟨.ret (.closure .bool .word (.var 1) [.word word]), k, store⟩ :=
  ⟨.cellRef, .closure (.cons .word .nil) (.var rfl), path 1 _ [] store k, path 1 _ [] store k⟩

private def sparse : LocalTypeInputs := ⟨[⟨"x", id 7, .word⟩, ⟨"y", ⟨other, 99⟩, .word⟩, ⟨"x", id 2, .word⟩], by decide⟩
private def actual (left right shadow : Core.Word) : LocalInputs :=
  ⟨[⟨"x", id 7, .word, .word left, .word⟩, ⟨"y", ⟨other, 99⟩, .word, .word right, .word⟩,
    ⟨"x", id 2, .word, .word shadow, .word⟩], by change [id 7, ⟨other, 99⟩, id 2].Nodup; decide⟩
private def subtraction : Syntax.Expr := ⟨span, .binary (ref "x") ⟨span, .subtract⟩ (ref "y")⟩
private def strict := discard subtraction (returned "x")
private def strictCore : Core.Expr := .letE (.binary .wordSub (.var 0) (.var 1)) (.var 1)
private theorem strictElab : TypedLetReturnTreeElaborates [] owner sparse strict strictCore .word := by
  simpa [strict, discard, strictCore, Core.Expr.weakenAt] using
    (TypedLetReturnTreeElaborates.discard (types := []) (owner := owner) (blockSpan := span) (statementSpan := span)
    (inputs := sparse) (expression := subtraction) (rest := (returned "x").value) (tailCore := .var 0)
    (.subtract (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.binary (.var .head) (.var (.tail (by decide) .head))) (.binary (.var .head) (.var (.tail (by decide) .head)))
    (.single (.expression (.identifier .head) (.var .head) (.var .head))))
private theorem strictCost (left right shadow : Core.Word) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner sparse.names (actual left right shadow).environment store strict (.word left) store 8 :=
  .discard (expression := subtraction) (discardedValue := .word (left.sub right)) (expressionCost := 5) (tailCost := 1)
    (.subtract (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
      (.identifier .head .head) (.identifier (.tail (by decide) .head) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head)))
    (.single (.expression (.identifier .head .head)))
private theorem strictPath (left right shadow : Core.Word) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 8 ⟨.eval strictCore [.word left, .word right, .word shadow], k, store⟩ ⟨.ret (.word left), k, store⟩ :=
  CostStepComposition.letE (CostStepComposition.binary (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) rfl)
    (.cons (.var rfl) .refl)

theorem strict_noncommutative_work_keeps_first_matches_and_all_fuel
    (left right shadow : Core.Word) (store : Core.Store) (fuel : Nat) :
    ¬ (sparse.names.map Prod.fst).Nodup ∧
    elaborateTypedLetReturnTree? [] owner sparse strict = some (strictCore, .word) ∧
    TypedLetReturnTreeEvaluatesWithCost owner sparse.names (actual left right shadow).environment store strict (.word left) store 8 ∧
    (Core.runStateful fuel (Core.State.initial strictCore [.word left, .word right, .word shadow] store) = .done (.word left) store ↔ 8 ≤ fuel) :=
  ⟨by decide, strictElab.complete, strictCost left right shadow store, (strictPath left right shadow store []).runStateful_done_iff⟩

theorem discarded_type_and_tail_keep_the_same_source_inputs :
    ∃ expressionType expressionCore tailCore,
      elaborateLocalExpression? sparse.names sparse.context subtraction = some (expressionCore, expressionType) ∧
      elaborateTypedLetReturnTree? [] owner sparse (returned "x") = some (tailCore, .word) ∧
      strictCore = .letE expressionCore (tailCore.weakenAt 0) :=
  elaborateTypedLetReturnTree?_discard_children strictElab.complete

theorem a_hidden_binder_is_not_a_source_binding_or_an_unweakened_tail :
    Resolved.freshLocalId owner sparse.ids = id 8 ∧
    ¬ TypedLetReturnTreeElaborates [] owner sparse strict (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0)) .word ∧
    Core.runStateful 8 (Core.State.initial (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0))
      [.word (Core.Word.ofNatModulo 5), .word (Core.Word.ofNatModulo 2)]) = .done (.word (Core.Word.ofNatModulo 3)) [] := by
  refine ⟨rfl, ?_, rfl⟩
  intro wrong
  cases (wrong.result_unique strictElab).1

private def checkpoint (left right shadow : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word (left.sub right)), [.letBody (.var 1) [.word left, .word right, .word shadow]], store⟩
theorem genuine_discard_checkpoints_resume_the_original_tail
    (left right shadow : Core.Word) (store : Core.Store) (additional : Nat) :
    (actual left right shadow).runTypedLetReturnTree? [] owner 6 strict store = some (.word, .outOfFuel (checkpoint left right shadow store)) ∧
    Core.Steps 2 (checkpoint left right shadow store) (Core.State.final (.word left) store) ∧
    (actual left right shadow).runTypedLetReturnTree? [] owner (6 + additional) strict store =
      some (.word, Core.runStateful additional (checkpoint left right shadow store)) ∧
    Core.runStateful 0 ⟨(checkpoint left right shadow store).control, [], store⟩ = .done (.word (left.sub right)) store := by
  have exhausted : (actual left right shadow).runTypedLetReturnTree? [] owner 6 strict store =
      some (.word, .outOfFuel (checkpoint left right shadow store)) :=
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨strictCore, strictElab.complete, rfl⟩
  exact ⟨exhausted, .cons .bindLet (.cons (.var rfl) .refl), LocalInputs.runTypedLetReturnTree?_resume exhausted additional, rfl⟩

theorem product_results_need_not_be_unit_to_be_discarded (left right shadow : Core.Word) (store : Core.Store) :
    TypedLetReturnTreeElaborates [] owner sparse
      (discard ⟨span, .tuple ⟨span, [ref "x", ref "y"]⟩⟩ (returned "x")) (.letE (.pair (.var 0) (.var 1)) (.var 1)) .word ∧
    TypedLetReturnTreeEvaluates owner sparse.names (actual left right shadow).environment store
      (discard ⟨span, .tuple ⟨span, [ref "x", ref "y"]⟩⟩ (returned "x")) (.word left) store := by
  refine ⟨?_, .discard (.pair (.identifier .head .head)
    (.identifier (.tail (by decide) .head) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head)))
    (.single (.expression (.identifier .head .head)))⟩
  simpa [discard, Core.Expr.weakenAt] using
    (TypedLetReturnTreeElaborates.discard (types := []) (owner := owner) (blockSpan := span) (statementSpan := span)
    (inputs := sparse) (tailCore := .var 0) (discardedType := .product .word .word)
    (expression := ⟨span, .tuple ⟨span, [ref "x", ref "y"]⟩⟩) (rest := (returned "x").value)
    (.pair (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.pair (.var .head) (.var (.tail (by decide) .head))) (.pair (.var .head) (.var (.tail (by decide) .head)))
    (.single (.expression (.identifier .head) (.var .head) (.var .head))))

theorem owner_store_and_raw_lookup_transport_have_distinct_premises
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (left right shadow : Core.Word) (store replacement : Core.Store) (fuel : Nat)
    (rightOwner : Resolved.DeclarationId) (table : LocalNameTable) (environment : Resolved.Environment)
    (agreement : ∀ name, (sparse.names.lookup? name).bind (actual left right shadow).environment.lookup? = (table.lookup? name).bind environment.lookup?) :
    ((actual left right shadow).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).runTypedLetReturnTree?
      [] (mapping owner) fuel strict store = (actual left right shadow).runTypedLetReturnTree? [] owner fuel strict store ∧
    TypedLetReturnTreeEvaluatesWithCost owner sparse.names (actual left right shadow).environment replacement strict (.word left) replacement 8 ∧
    evaluateTypedLetReturnTreeWithCost? rightOwner table environment strict = some (.word left, 8) := by
  refine ⟨LocalInputs.runTypedLetReturnTree?_mapOwner _ mapping injective [] owner fuel strict store,
    (strictCost left right shadow store).change_store replacement, ?_⟩
  rw [← evaluateTypedLetReturnTreeWithCost?_congr_lookup owner rightOwner sparse.names table _ environment agreement strict]
  exact evaluateTypedLetReturnTreeWithCost?_complete (strictCost left right shadow store)

theorem missing_expression_or_required_shape_is_not_silently_discarded
    (value : Core.Value) (store finalStore : Core.Store) :
    elaborateTypedLetReturnTree? [] owner sparse (discard (ref "missing") (returned "x")) = none ∧
    ¬ TypedLetReturnTreeEvaluates owner sparse.names [] store (discard (ref "missing") (returned "x")) value finalStore ∧
    elaborateTypedLetReturnTree? [] owner sparse ⟨span, ⟨span, .expression subtraction false⟩ :: (returned "x").value⟩ = none ∧
    elaborateTypedLetReturnTree? [] owner sparse ⟨span, [⟨span, .expression subtraction true⟩]⟩ = none ∧
    elaborateTypedLetReturnBody? [] owner sparse strict = none := by
  have missingLookup : sparse.names.lookup? "missing" = none := rfl
  have missing : elaborateLocalExpression? sparse.names sparse.context (ref "missing") = none := by
    simp [elaborateLocalExpression?, resolveLocalExpression?, ref, missingLookup]
  have noTail : elaborateTypedLetReturnTree? [] owner sparse ⟨span, [⟨span, .expression subtraction true⟩]⟩ = none := by
    apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
    rintro ⟨_, typing⟩
    cases typing with
    | single child => cases child
    | discard _ tail => cases tail with
      | single child => cases child
  refine ⟨by simp [discard, elaborateTypedLetReturnTree?, missing], ?_, by simp only [elaborateTypedLetReturnTree?],
    noTail,
    by simp [strict, discard, elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?]⟩
  intro evaluation
  cases evaluation with
  | single child => cases child
  | discard expression _ =>
      cases expression with
      | identifier named _ =>
          have impossible := LocalNameTable.lookup?_iff.mpr named
          change none = some _ at impossible
          cases impossible

private def one := discard (ref "seed") (returned "seed")
private def branch (otherwise : Syntax.Block) : Syntax.Block :=
  ⟨span, [⟨span, .ifThen (ref "seed") one (some otherwise)⟩]⟩
theorem branch_costs_are_selected_but_whole_checking_keeps_both_arms (choice : Bool) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (seed .bool).names [(id 0, .bool choice)] store
      (branch (returned "seed")) (.bool choice) store (if choice then 7 else 4) ∧
    elaborateTypedLetReturnTree? [] owner (seed .bool) (branch (returned "seed")) =
      some (.ifE (.var 0) (.letE (.var 0) (.var 1)) (.var 0), .bool) ∧
    TypedLetReturnTreeEvaluates owner (seed .bool).names [(id 0, .bool true)] store
      (branch (discard (ref "missing") (returned "seed"))) (.bool true) store ∧
    elaborateTypedLetReturnTree? [] owner (seed .bool) (branch (discard (ref "missing") (returned "seed"))) = none := by
  have leaf : ReturnBodyElaborates (seed .bool).names (seed .bool).context (returned "seed") (.var 0) .bool :=
    .expression (.identifier .head) (.var .head) (.var .head)
  have first : TypedLetReturnTreeElaborates [] owner (seed .bool) one (.letE (.var 0) ((Core.Expr.var 0).weakenAt 0)) .bool :=
    .discard (inputs := seed .bool) (expression := ref "seed") (rest := (returned "seed").value) (tailCore := .var 0)
      (.identifier .head) (.var .head) (.var .head) (.single leaf)
  have original : TypedLetReturnTreeElaborates [] owner (seed .bool) (branch (returned "seed"))
      (.ifE (.var 0) (.letE (.var 0) ((Core.Expr.var 0).weakenAt 0)) (.var 0)) .bool :=
    .conditional (.identifier .head) (.var .head) (.var .head) first (.single leaf)
  refine ⟨?_, by simpa [Core.Expr.weakenAt] using original.complete,
    .ifTrue (.identifier .head .head) (.discard (.identifier .head .head) (.single (.expression (.identifier .head .head)))), ?_⟩
  · cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact .ifFalse (condition := ref "seed") (thenBody := one) (conditionCost := 1) (branchCost := 1)
        (.identifier .head .head) (.single (.expression (.identifier .head .head)))
    · exact .ifTrue (condition := ref "seed") (elseBody := returned "seed") (conditionCost := 1) (branchCost := 4)
        (.identifier .head .head) (.discard (expression := ref "seed") (expressionCost := 1) (tailCost := 1)
          (.identifier .head .head) (.single (.expression (.identifier .head .head))))
  · apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
    rintro ⟨_, typing⟩
    cases typing with
    | single child => cases child
    | conditional _ _ other =>
        cases other with
        | single child => cases child
        | discard expression _ =>
            cases expression with
            | identifier named _ =>
                have impossible := LocalNameTable.lookup?_iff.mpr named
                change none = some _ at impossible
                cases impossible

end Tests.FrontendDiscardStatement
