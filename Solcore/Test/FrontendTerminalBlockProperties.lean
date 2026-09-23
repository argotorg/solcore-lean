import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.TypedLetReturnBody

/-! Original terminal wrappers have no hidden binder or machine transition.
Independent mixed bodies separate static types, raw values and genuine states. -/
set_option autoImplicit false
namespace Tests.FrontendTerminalBlock
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TerminalBlock", by decide⟩], by decide⟩⟩, 0⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 9 }
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "terminal-block.sol"⟩, 23, 4⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def wrap (outer : Syntax.SourceSpan) (body : Syntax.Block) : Syntax.Block :=
  ⟨outer, [⟨body.span, .block body.value⟩]⟩
private def nested : List Syntax.SourceSpan → Syntax.Block → Syntax.Block
  | [], body => body
  | outer :: rest, body => wrap outer (nested rest body)
private theorem wrapped {types : TypeNameTable} {own : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (evidence : TypedLetReturnTreeElaborates types own inputs body core type) (spans : List Syntax.SourceSpan) :
    TypedLetReturnTreeElaborates types own inputs (nested spans body) core type := by
  induction spans with
  | nil => exact evidence
  | cons outer rest ih => exact .block ih
private theorem replay {own : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initial final : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evidence : TypedLetReturnTreeEvaluatesWithCost own table environment initial body value final cost)
    (spans : List Syntax.SourceSpan) :
    TypedLetReturnTreeEvaluatesWithCost own table environment initial (nested spans body) value final cost := by
  induction spans with
  | nil => exact evidence
  | cons outer rest ih => exact .block ih
private theorem checked (types : TypeNameTable) (own : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (spans : List Syntax.SourceSpan) (body : Syntax.Block) :
    elaborateTypedLetReturnTree? types own inputs (nested spans body) = elaborateTypedLetReturnTree? types own inputs body := by
  induction spans with
  | nil => rfl
  | cons outer rest ih => exact (elaborateTypedLetReturnTree?_block types own inputs outer _ _).trans ih
private theorem runs (inputs : LocalInputs) (types : TypeNameTable) (own : Resolved.DeclarationId)
    (spans : List Syntax.SourceSpan) (body : Syntax.Block) (fuel : Nat) (store : Core.Store) :
    inputs.runTypedLetReturnTree? types own fuel (nested spans body) store = inputs.runTypedLetReturnTree? types own fuel body store := by
  simp only [LocalInputs.runTypedLetReturnTree?, LocalInputs.checkTypedLetReturnTree?, checked]
private def static (type : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"seed", id 7, type⟩, ⟨"c", ⟨other, 99⟩, .bool⟩, ⟨"seed", id 2, type⟩], by change [id 7, ⟨other, 99⟩, id 2].Nodup; decide⟩
private def values (value shadow : Core.Value) (choice : Bool) : Resolved.Environment :=
  [(id 7, value), (⟨other, 99⟩, .bool choice), (id 2, shadow)]
private def actual (type : Core.Ty) (value shadow : Core.Value) (choice : Bool)
    (typed : Core.ValueHasType value type) (shadowTyped : Core.ValueHasType shadow type) : LocalInputs :=
  ⟨[⟨"seed", id 7, type, value, typed⟩, ⟨"c", ⟨other, 99⟩, .bool, .bool choice, .bool⟩,
    ⟨"seed", id 2, type, shadow, shadowTyped⟩], by change [id 7, ⟨other, 99⟩, id 2].Nodup; decide⟩
private def branch : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") (returned "x") (some (returned "x"))⟩]⟩
private def mixed : Syntax.Block := ⟨span,
  ⟨span, .letDecl ⟨span, "x"⟩ none (some (ref "seed"))⟩ :: ⟨span, .expression (ref "x") true⟩ :: branch.value⟩
private def branchCore : Core.Expr := .ifE (.var 3) (.var 1) (.var 1)
private def core : Core.Expr := .letE (.var 0) (.letE (.var 0) branchCore)
private theorem elaborated (types : TypeNameTable) (type : Core.Ty) :
    TypedLetReturnTreeElaborates types owner (static type) mixed core type := by
  have leaf : ReturnBodyElaborates ((static type).bindFresh owner "x" type).names
      ((static type).bindFresh owner "x" type).context (returned "x") (.var 0) type :=
    .expression (.identifier .head) (.var .head) (.var .head)
  have conditional : TypedLetReturnTreeElaborates types owner ((static type).bindFresh owner "x" type)
      branch (.ifE (.var 2) (.var 0) (.var 0)) type :=
    .conditional (.identifier (.tail (by change "x" ≠ "c"; decide) (.tail (by change "seed" ≠ "c"; decide) .head)))
      (.var (.tail (by change id 8 ≠ ⟨other, 99⟩; decide) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head)))
      (.var (.tail (by change id 8 ≠ ⟨other, 99⟩; decide) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head)))
      (.single leaf) (.single leaf)
  have tail := TypedLetReturnTreeElaborates.discard (inputs := (static type).bindFresh owner "x" type)
    (blockSpan := span) (statementSpan := span) (expression := ref "x") (rest := branch.value)
    (.identifier .head) (.var .head) (.var .head) conditional
  simpa [mixed, core, branchCore, Core.Expr.weakenAt] using
    (TypedLetReturnTreeElaborates.inferred (inputs := static type) (name := ⟨span, "x"⟩)
      (initializer := ref "seed") (letSpan := span) (by change "x" ∉ ["seed", "c", "seed"]; decide)
      (.identifier .head) (.var .head) (.var .head) tail)
private theorem counted (type : Core.Ty) (value shadow : Core.Value) (choice : Bool) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (static type).names (values value shadow choice) store mixed value store 10 := by
  apply TypedLetReturnTreeEvaluatesWithCost.inferred (owner := owner) (table := (static type).names)
    (environment := values value shadow choice) (initializer := ref "seed") (name := ⟨span, "x"⟩)
    (blockSpan := span) (letSpan := span) (initializerCost := 1) (tailCost := 7) (.identifier .head .head)
  apply TypedLetReturnTreeEvaluatesWithCost.discard (expression := ref "x") (expressionCost := 1) (tailCost := 4) (.identifier .head .head)
  have guard : LocalExpressionEvaluatesWithCost (("x", id 8) :: (static type).names)
      ((id 8, value) :: values value shadow choice) store (ref "c") (.bool choice) store 1 :=
    .identifier (.tail (by change "x" ≠ "c"; decide) (.tail (by change "seed" ≠ "c"; decide) .head))
      (.tail (by change id 8 ≠ ⟨other, 99⟩; decide) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head))
  cases choice
  · exact .ifFalse guard (.single (.expression (.identifier .head .head)))
  · exact .ifTrue guard (.single (.expression (.identifier .head .head)))
private theorem path (value shadow : Core.Value) (choice : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 10 ⟨.eval core [value, .bool choice, shadow], k, store⟩ ⟨.ret value, k, store⟩ := by
  apply CostStepComposition.letE (valueCost := 1) (bodyCost := 7) (.cons (.var rfl) .refl)
  apply CostStepComposition.letE (valueCost := 1) (bodyCost := 4) (.cons (.var rfl) .refl)
  cases choice
  · exact CostStepComposition.ifFalse (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
  · exact CostStepComposition.ifTrue (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)

theorem arbitrary_original_ranges_keep_value_free_mixed_provenance
    (spans : List Syntax.SourceSpan) (types : TypeNameTable) (type : Core.Ty) (definitions : Core.DataEnvironment) :
    TypedLetReturnTreeElaborates types owner (static type) (nested spans mixed) core type ∧
    TypedLetReturnTreeHasType types owner (static type) (nested spans mixed) type ∧
    Core.HasType [type, .bool, type] core type definitions ∧
    Resolved.freshLocalId owner (static type).ids = id 8 ∧ ¬ ((static type).names.map Prod.fst).Nodup :=
  ⟨wrapped (elaborated types type) spans, (wrapped (elaborated types type) spans).hasType,
    .letE (.var rfl) (.letE (.var rfl) (.ifE (.var rfl) (.var rfl) (.var rfl))), rfl,
    by change ¬ ["seed", "c", "seed"].Nodup; decide⟩

theorem raw_values_and_every_continuation_keep_exactly_ten_steps
    (spans : List Syntax.SourceSpan) (type : Core.Ty) (value shadow : Core.Value) (choice : Bool)
    (store : Core.Store) (k : List Core.Frame) :
    TypedLetReturnTreeEvaluatesWithCost owner (static type).names (values value shadow choice) store (nested spans mixed) value store 10 ∧
    evaluateTypedLetReturnTreeWithCost? owner (static type).names (values value shadow choice) (nested spans mixed) = some (value, 10) ∧
    Core.Steps 10 ⟨.eval core [value, .bool choice, shadow], k, store⟩ ⟨.ret value, k, store⟩ ∧
    Core.Evaluates [value, .bool choice, shadow] store core value store :=
  ⟨replay (counted type value shadow choice store) spans,
    evaluateTypedLetReturnTreeWithCost?_complete (replay (counted type value shadow choice store) spans), path value shadow choice store k,
    (elaborateTypedLetReturnTree?_evaluates_iff (wrapped (elaborated [] type) spans).complete rfl).mp
      (replay (counted type value shadow choice store) spans).erase⟩

theorem whole_option_and_actual_full_states_are_equal_not_just_values
    (spans : List Syntax.SourceSpan) (types : TypeNameTable) (own : Resolved.DeclarationId)
    (inputs : LocalInputs) (body : Syntax.Block) (fuel : Nat) (store : Core.Store) :
    elaborateTypedLetReturnTree? types own inputs.toTypeInputs (nested spans body) = elaborateTypedLetReturnTree? types own inputs.toTypeInputs body ∧
    inputs.runTypedLetReturnTree? types own fuel (nested spans body) store = inputs.runTypedLetReturnTree? types own fuel body store :=
  ⟨checked types own inputs.toTypeInputs spans body, runs inputs types own spans body fuel store⟩

theorem actual_typed_callers_have_exact_thresholds (spans : List Syntax.SourceSpan) (type : Core.Ty)
    (value shadow : Core.Value) (choice : Bool) (typed : Core.ValueHasType value type)
    (shadowTyped : Core.ValueHasType shadow type) (store : Core.Store) (fuel : Nat) :
    (actual type value shadow choice typed shadowTyped).runTypedLetReturnTree? [] owner fuel (nested spans mixed) store =
      some (type, Core.runStateful fuel (Core.State.initial core [value, .bool choice, shadow] store)) ∧
    (Core.runStateful fuel (Core.State.initial core [value, .bool choice, shadow] store) = .done value store ↔ 10 ≤ fuel) :=
  ⟨LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, (wrapped (elaborated [] type) spans).complete, rfl⟩,
    (path value shadow choice store []).runStateful_done_iff⟩

private def checkpoint (value shadow : Core.Value) (choice : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody branchCore [value, value, .bool choice, shadow]], store⟩
private def early (value shadow : Core.Value) (choice : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody (.letE (.var 0) branchCore) [value, .bool choice, shadow]], store⟩
theorem wrappers_preserve_the_actual_pre_binding_checkpoint (spans : List Syntax.SourceSpan)
    (word shadow : Core.Word) (choice : Bool) (store : Core.Store) :
    (actual .word (.word word) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner 2 mixed store =
      some (.word, .outOfFuel (early (.word word) (.word shadow) choice store)) ∧
    (actual .word (.word word) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner 2 (nested spans mixed) store =
      some (.word, .outOfFuel (early (.word word) (.word shadow) choice store)) := by
  have original : (actual .word (.word word) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner 2 mixed store =
      some (.word, .outOfFuel (early (.word word) (.word shadow) choice store)) :=
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, (elaborated [] .word).complete, rfl⟩
  exact ⟨original, (runs _ [] owner spans mixed 2 store).trans original⟩

theorem identical_saved_states_resume_without_restarting (spans : List Syntax.SourceSpan)
    (value shadow : Core.Word) (choice : Bool) (store : Core.Store) (additional : Nat) :
    (actual .word (.word value) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner 5 (nested spans mixed) store =
      some (.word, .outOfFuel (checkpoint (.word value) (.word shadow) choice store)) ∧
    Core.Steps 5 (checkpoint (.word value) (.word shadow) choice store) (Core.State.final (.word value) store) ∧
    (actual .word (.word value) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner (5 + additional) (nested spans mixed) store =
      some (.word, Core.runStateful additional (checkpoint (.word value) (.word shadow) choice store)) := by
  have stopped : (actual .word (.word value) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner 5 (nested spans mixed) store =
      some (.word, .outOfFuel (checkpoint (.word value) (.word shadow) choice store)) :=
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, (wrapped (elaborated [] .word) spans).complete, rfl⟩
  exact ⟨stopped, ((path (.word value) (.word shadow) choice store []).residual_of_outOfFuel (spent := 5) rfl).2,
    LocalInputs.runTypedLetReturnTree?_resume stopped additional⟩

theorem nominal_static_acceptance_is_not_actual_inhabitation (spans : List Syntax.SourceSpan) (nominal : Core.DataTypeId) :
    elaborateTypedLetReturnTree? [] owner (static (.namedData nominal)) (nested spans mixed) = some (core, .namedData nominal) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(wrapped (elaborated [] _) spans).complete, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem opaque_cells_and_closures_need_no_dereference (location : Core.Location) (word : Core.Word)
    (spans : List Syntax.SourceSpan) (store : Core.Store) :
    Core.ValueHasType (.cellRef .word location) (.cell .word) ∧
    Core.ValueHasType (.closure .bool .word (.var 1) [.word word]) (.function .bool .word) ∧
    TypedLetReturnTreeEvaluatesWithCost owner (static (.cell .word)).names (values (.cellRef .word location) .unit true)
      store (nested spans mixed) (.cellRef .word location) store 10 ∧
    Core.Steps 10 ⟨.eval core [.closure .bool .word (.var 1) [.word word], .bool false, .unit], [], store⟩
      (Core.State.final (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨.cellRef, .closure (.cons .word .nil) (.var rfl), replay (counted _ _ _ true store) spans, path _ _ false store []⟩

theorem opaque_actual_inputs_complete_without_accessing_stored_contents
    (location : Core.Location) (word : Core.Word) (spans : List Syntax.SourceSpan) (store : Core.Store) :
    (actual (.cell .word) (.cellRef .word location) (.cellRef .word location) true .cellRef .cellRef).runTypedLetReturnTree?
      [] owner 10 (nested spans mixed) store = some (.cell .word, .done (.cellRef .word location) store) ∧
    (actual (.function .bool .word) (.closure .bool .word (.var 1) [.word word]) (.closure .bool .word (.var 1) [.word word]) false
      (.closure (.cons .word .nil) (.var rfl)) (.closure (.cons .word .nil) (.var rfl))).runTypedLetReturnTree?
      [] owner 10 (nested spans mixed) store = some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, (wrapped (elaborated [] _) spans).complete, rfl⟩,
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, (wrapped (elaborated [] _) spans).complete, rfl⟩⟩

theorem same_typed_replacement_is_not_original_provenance (spans : List Syntax.SourceSpan) (type : Core.Ty) :
    Core.HasType [type, .bool, type] (.var 2) type ∧
    ¬ TypedLetReturnTreeElaborates [] owner (static type) (nested spans mixed) (.var 2) type := by
  refine ⟨.var rfl, ?_⟩
  intro competing
  cases (competing.result_unique (wrapped (elaborated [] type) spans)).1

theorem owner_type_store_and_raw_lookup_transport_remain_distinct
    (spans : List Syntax.SourceSpan) (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (word shadow : Core.Word) (choice : Bool) (store replacement : Core.Store) (fuel : Nat) (extras : TypeNameTable)
    (rightOwner : Resolved.DeclarationId) (table : LocalNameTable) (environment : Resolved.Environment)
    (agreement : ∀ name, ((static .word).names.lookup? name).bind (values (.word word) (.word shadow) choice).lookup? =
      (table.lookup? name).bind environment.lookup?) :
    ((actual .word (.word word) (.word shadow) choice .word .word).mapIds (ownerLocalIdMap mapping)
      (ownerLocalIdMap_injective mapping injective)).runTypedLetReturnTree? [] (mapping owner) fuel (nested spans mixed) store =
      (actual .word (.word word) (.word shadow) choice .word .word).runTypedLetReturnTree? [] owner fuel (nested spans mixed) store ∧
    elaborateTypedLetReturnTree? extras owner (static .word) (nested spans mixed) = some (core, .word) ∧
    TypedLetReturnTreeEvaluatesWithCost rightOwner table environment replacement (nested spans mixed) (.word word) replacement 10 := by
  exact ⟨LocalInputs.runTypedLetReturnTree?_mapOwner _ mapping injective [] owner fuel _ store,
    elaborateTypedLetReturnTree?_some_of_extends (TypeNameTable.Extends.append_right [] extras)
      (wrapped (elaborated [] .word) spans).complete,
    (typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff agreement).mp
      ((replay (counted .word (.word word) (.word shadow) choice store) spans).change_store replacement)⟩

theorem terminal_shape_does_not_enable_nonterminal_blocks_or_empty_returns
    (outer inner : Syntax.SourceSpan) (spans : List Syntax.SourceSpan) :
    elaborateTypedLetReturnTree? [] owner (static .word) (nested spans ⟨inner, []⟩) = none ∧
    elaborateTypedLetReturnTree? [] owner (static .word) ⟨outer, ⟨inner, .block mixed.value⟩ :: (returned "x").value⟩ = none ∧
    elaborateTypedLetReturnBody? [] owner (static .word) (wrap outer mixed) = none ∧
    (wrap outer ⟨inner, mixed.value⟩).value = [⟨inner, .block mixed.value⟩] := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [checked]; simp only [elaborateTypedLetReturnTree?]
  · simp only [returned, elaborateTypedLetReturnTree?]
  · simp only [wrap, mixed, elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?]

private def badBranch : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") (returned "seed") (some (returned "missing"))⟩]⟩
theorem unselected_missing_is_raw_success_but_not_whole_success (spans : List Syntax.SourceSpan)
    (value shadow : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluates owner (static .word).names (values value shadow true) store (nested spans badBranch) value store ∧
    elaborateTypedLetReturnTree? [] owner (static .word) (nested spans badBranch) = none := by
  have raw : TypedLetReturnTreeEvaluatesWithCost owner (static .word).names (values value shadow true) store badBranch value store 4 :=
    .ifTrue (condition := ref "c") (conditionCost := 1) (branchCost := 1)
      (.identifier (.tail (by change "seed" ≠ "c"; decide) .head) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head))
      (.single (.expression (.identifier .head .head)))
  refine ⟨(replay raw spans).erase, ?_⟩
  rw [checked]
  apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
  rintro ⟨_, typing⟩
  cases typing with
  | single child => cases child
  | conditional _ _ other =>
      cases other with
      | single child => cases child with
        | expression expression => cases expression with
          | identifier named _ =>
              have impossible := LocalNameTable.lookup?_iff.mpr named
              change none = some _ at impossible
              cases impossible

theorem wrapping_does_not_reset_scope_or_allow_shadowing (spans : List Syntax.SourceSpan) :
    elaborateTypedLetReturnTree? [] owner (static .word) (nested spans (returned "x")) = none ∧
    elaborateTypedLetReturnTree? [] owner (static .word)
      (nested spans ⟨span, ⟨span, .letDecl ⟨span, "seed"⟩ none (some (ref "seed"))⟩ :: (returned "seed").value⟩) = none := by
  constructor
  · rw [checked]
    simp [returned, ref, elaborateTypedLetReturnTree?, elaborateReturnBody?, elaborateLocalExpression?,
      resolveLocalExpression?, static, LocalTypeInputs.names, LocalNameTable.lookup?]
  · rw [checked]
    simp [elaborateTypedLetReturnTree?, static, LocalTypeInputs.names]

end Tests.FrontendTerminalBlock
