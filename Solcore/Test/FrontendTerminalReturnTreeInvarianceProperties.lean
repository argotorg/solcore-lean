import Solcore.Frontend.TerminalReturnTree

/-! Static relabeling needs no runtime inhabitants. Actual typed runners retain
whole checkpoints under ID maps, but replacement stores remain distinct. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalReturnTreeInvariance

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeInvariance", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "tree-invariance.sol"⟩, 91, 6⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (source : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some source)⟩]⟩
private def branch (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") yes (some no)⟩]⟩
private def names : LocalNameTable := [("y", id 2), ("x", id 1), ("c", id 0)]
private def context (type : Core.Ty) : Resolved.Context := [(id 2, type), (id 1, type), (id 0, .bool)]
private def environment (choice : Bool) (left right : Core.Value) : Resolved.Environment :=
  [(id 2, right), (id 1, left), (id 0, .bool choice)]
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def inputs {type : Core.Ty} (choice : Bool) (left right : Actual type) : LocalInputs :=
  ⟨[⟨"y", id 2, type, right.val, right.property⟩, ⟨"x", id 1, type, left.val, left.property⟩,
    ⟨"c", id 0, .bool, .bool choice, .bool⟩], by change [id 2, id 1, id 0].Nodup; decide⟩
private def x := returned (ref "x")
private def y := returned (ref "y")
private def spine : Nat → Syntax.Block
  | 0 => x
  | depth + 1 => branch (spine depth) y
private def core : Nat → Core.Expr
  | 0 => .var 1
  | depth + 1 => .ifE (.var 2) (core depth) (.var 0)
private theorem elaborated (depth : Nat) (type : Core.Ty) :
    TerminalReturnTreeElaborates names (context type) (spine depth) (core depth) type := by
  have xE : TerminalReturnTreeElaborates names (context type) x (.var 1) type :=
    .single (.expression (.identifier (.tail (by decide) .head))
      (.var (.tail (by change id 2 ≠ id 1; decide) .head)) (.var (.tail (by decide) .head)))
  have yE : TerminalReturnTreeElaborates names (context type) y (.var 0) type :=
    .single (.expression (.identifier .head) (.var .head) (.var .head))
  induction depth with
  | zero => exact xE
  | succ depth ih =>
    exact .conditional (.identifier (.tail (by decide) (.tail (by decide) .head)))
      (.var (.tail (by change id 2 ≠ id 0; decide) (.tail (by change id 1 ≠ id 0; decide) .head)))
      (.var (.tail (by decide) (.tail (by decide) .head))) ih yE
private theorem conditionCost (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store (ref "c") (.bool choice) store 1 :=
  .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
private theorem trueCost (depth : Nat) (left right : Core.Value) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost names (environment true left right) store (spine depth) left store (3 * depth + 1) := by
  induction depth with
  | zero => exact .single (.expression (.identifier (.tail (by decide) .head) (.tail (by decide) .head)))
  | succ depth ih =>
    have arithmetic : 1 + (3 * depth + 1) + 2 = 3 * (depth + 1) + 1 := by omega
    simpa only [arithmetic, spine, branch] using TerminalReturnTreeEvaluatesWithCost.ifTrue (conditionCost true left right store) ih
private theorem yCost (choice : Bool) (left right : Core.Value) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store (ref "y") right store 1 := .identifier .head .head
private theorem falseCost (depth : Nat) (left right : Core.Value) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost names (environment false left right) store (spine (depth + 1)) right store 4 :=
  .ifFalse (conditionCost false left right store) (.single (.expression (yCost false left right store)))

theorem arbitrary_depth_static_transport_retains_exact_core_without_runtime_values
    (depth : Nat) (type : Core.Ty) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    TerminalReturnTreeElaborates (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context type))
      (spine depth) (core depth) type ∧
    elaborateTerminalReturnTree? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context type)) (spine depth) =
      some (core depth, type) :=
  ⟨(elaborated depth type).mapIds mapping injective,
    (elaborateTerminalReturnTree?_mapIds mapping injective names (context type) (spine depth)).trans (elaborated depth type).complete⟩

theorem nominal_static_transport_does_not_provide_a_typed_runtime_inhabitant
    (depth : Nat) (nominal : Core.DataTypeId) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    elaborateTerminalReturnTree? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context (.namedData nominal)))
      (spine depth) = some (core depth, .namedData nominal) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(arbitrary_depth_static_transport_retains_exact_core_without_runtime_values depth _ mapping injective).2, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem actual_typed_inputs_keep_all_same_fuel_optional_results_under_injective_maps
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) :
    ((inputs choice left right).mapIds mapping injective).checkTerminalReturnTree? (spine depth) = some (core depth, type) ∧
    ((inputs choice left right).mapIds mapping injective).runTerminalReturnTree? fuel (spine depth) store =
      (inputs choice left right).runTerminalReturnTree? fuel (spine depth) store :=
  ⟨((inputs choice left right).checkTerminalReturnTree?_mapIds mapping injective (spine depth)).trans (elaborated depth type).complete,
    (inputs choice left right).runTerminalReturnTree?_mapIds mapping injective fuel (spine depth) store⟩

theorem raw_replay_needs_no_checking_alignment_or_value_typing
    (depth : Nat) (left right : Core.Value) (first replacement : Core.Store) :
    TerminalReturnTreeEvaluates names (environment true left right) replacement (spine depth) left replacement ∧
    TerminalReturnTreeEvaluatesWithCost names (environment true left right) replacement (spine depth) left replacement (3 * depth + 1) ∧
    TerminalReturnTreeEvaluates names (environment false left right) replacement (spine (depth + 1)) right replacement ∧
    TerminalReturnTreeEvaluatesWithCost names (environment false left right) replacement (spine (depth + 1)) right replacement 4 :=
  ⟨(trueCost depth left right first).erase.change_store replacement, (trueCost depth left right first).change_store replacement,
    (falseCost depth left right first).erase.change_store replacement, (falseCost depth left right first).change_store replacement⟩

theorem raw_and_cost_replay_equivalences_retain_both_original_stores
    (depth : Nat) (choice : Bool) (left right value : Core.Value) (initialStore finalStore replacement : Core.Store) (cost : Nat) :
    (TerminalReturnTreeEvaluates names (environment choice left right) initialStore (spine depth) value finalStore ↔
      finalStore = initialStore ∧ TerminalReturnTreeEvaluates names (environment choice left right) replacement (spine depth) value replacement) ∧
    (TerminalReturnTreeEvaluatesWithCost names (environment choice left right) initialStore (spine depth) value finalStore cost ↔
      finalStore = initialStore ∧ TerminalReturnTreeEvaluatesWithCost names (environment choice left right) replacement (spine depth) value replacement cost) :=
  ⟨terminalReturnTreeEvaluates_store_iff, terminalReturnTreeEvaluatesWithCost_store_iff⟩

theorem identity_transport_and_store_replay_compose_at_each_fuel_without_state_equality
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (value : Core.Value)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (fuel : Nat) (first replacement : Core.Store) :
    (((inputs choice left right).mapIds mapping injective).runTerminalReturnTree? fuel (spine depth) first = some (type, .done value first) ↔
      (inputs choice left right).runTerminalReturnTree? fuel (spine depth) replacement = some (type, .done value replacement)) ∧
    ((∃ checkpoint, ((inputs choice left right).mapIds mapping injective).runTerminalReturnTree? fuel (spine depth) first =
      some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, (inputs choice left right).runTerminalReturnTree? fuel (spine depth) replacement = some (type, .outOfFuel checkpoint)) := by
  rw [(inputs choice left right).runTerminalReturnTree?_mapIds mapping injective fuel (spine depth) first]
  exact ⟨(inputs choice left right).runTerminalReturnTree?_done_store_iff fuel (spine depth) first replacement type value,
    (inputs choice left right).runTerminalReturnTree?_outOfFuel_store_iff fuel (spine depth) first replacement type⟩

private def shifted (localId : Resolved.LocalId) : Resolved.LocalId := ⟨localId.owner, localId.binderIndex + 7⟩
private theorem shiftedInjective : Function.Injective shifted := by
  intro ⟨ownerA, indexA⟩ ⟨ownerB, indexB⟩ same
  simp only [shifted, Resolved.LocalId.mk.injEq] at same
  obtain ⟨rfl, indexes⟩ := same
  cases Nat.add_right_cancel indexes
  rfl
private def checkpoint (depth : Nat) (choice : Bool) (left right : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (core depth) (.var 0) [right, left, .bool choice]], store⟩
private theorem exhausted {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) :
    (inputs choice left right).runTerminalReturnTree? 2 (spine (depth + 1)) store =
      some (type, .outOfFuel (checkpoint depth choice left.val right.val store)) := by
  apply LocalInputs.runTerminalReturnTree?_eq_some_iff.mpr
  refine ⟨core (depth + 1), (elaborated (depth + 1) type).complete, ?_⟩
  cases choice <;> rfl
theorem genuine_identity_changes_preserve_the_whole_arbitrary_depth_checkpoint
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) :
    shifted (id 0) ≠ id 0 ∧
    ((inputs choice left right).mapIds shifted shiftedInjective).runTerminalReturnTree? 2 (spine (depth + 1)) store =
      some (type, .outOfFuel (checkpoint depth choice left.val right.val store)) :=
  ⟨by decide, ((inputs choice left right).runTerminalReturnTree?_mapIds shifted shiftedInjective 2 (spine (depth + 1)) store).trans
    (exhausted depth choice left right store)⟩

theorem different_nonempty_stores_produce_different_full_checkpoints
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (tail : Core.Store) :
    (inputs choice left right).runTerminalReturnTree? 2 (spine (depth + 1)) (.unit :: tail) =
      some (type, .outOfFuel (checkpoint depth choice left.val right.val (.unit :: tail))) ∧
    (inputs choice left right).runTerminalReturnTree? 2 (spine (depth + 1)) (.bool true :: tail) =
      some (type, .outOfFuel (checkpoint depth choice left.val right.val (.bool true :: tail))) ∧
    (inputs choice left right).runTerminalReturnTree? 2 (spine (depth + 1)) (.unit :: tail) ≠
      (inputs choice left right).runTerminalReturnTree? 2 (spine (depth + 1)) (.bool true :: tail) := by
  refine ⟨exhausted depth choice left right _, exhausted depth choice left right _, ?_⟩
  rw [exhausted, exhausted]
  intro same
  have stored := congrArg (fun state : Core.State => state.store)
    (Core.StatefulRunResult.outOfFuel.inj (Prod.mk.inj (Option.some.inj same)).2)
  cases stored

private theorem completed {type : Core.Ty} (depth : Nat) (left right : Actual type) (store : Core.Store) :
    (inputs true left right).runTerminalReturnTree? (3 * depth + 1) (spine depth) store = some (type, .done left.val store) :=
  LocalInputs.runTerminalReturnTree?_eq_some_iff.mpr ⟨core depth, (elaborated depth type).complete,
    ((trueCost depth left.val right.val store).checked_runStateful_done_iff (elaborated depth type).complete rfl).mpr (Nat.le_refl _)⟩
theorem existing_typed_cells_and_captured_closures_replay_without_store_access
    (depth : Nat) (location : Core.Location) (word : Core.Word) (first replacement : Core.Store) :
    (inputs true ⟨.cellRef .word location, .cellRef⟩ ⟨.cellRef .word location, .cellRef⟩).runTerminalReturnTree? (3 * depth + 1) (spine depth) first =
      some (.cell .word, .done (.cellRef .word location) first) ∧
    (inputs true ⟨.cellRef .word location, .cellRef⟩ ⟨.cellRef .word location, .cellRef⟩).runTerminalReturnTree? (3 * depth + 1) (spine depth) replacement =
      some (.cell .word, .done (.cellRef .word location) replacement) ∧
    (inputs true ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩
      ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩).runTerminalReturnTree? (3 * depth + 1) (spine depth) replacement =
      some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) replacement) := by
  refine ⟨completed depth _ _ first, ?_, ?_⟩
  · exact (LocalInputs.runTerminalReturnTree?_done_store_iff _ _ _ first replacement _ _).mp (completed depth _ _ first)
  · exact (LocalInputs.runTerminalReturnTree?_done_store_iff _ _ _ first replacement _ _).mp (completed depth _ _ first)

private def bad : Nat → Syntax.Block
  | 0 => returned (ref "missing")
  | depth + 1 => branch y (bad depth)
private theorem badUntyped (depth : Nat) (type : Core.Ty) : ¬ ∃ result, TerminalReturnTreeHasType names (context type) (bad depth) result := by
  induction depth with
  | zero =>
    rintro ⟨result, typing⟩
    cases typing with
    | single leaf =>
      cases leaf with
      | expression typed =>
        obtain ⟨resolved, resolution, _⟩ := typed.resolves
        have accepted := resolution.complete
        simp [resolveLocalExpression?, ref, names, LocalNameTable.lookup?] at accepted
  | succ depth ih =>
    rintro ⟨result, typing⟩
    cases typing with
    | single leaf => cases leaf
    | conditional _ _ no => exact ih ⟨result, no⟩
theorem skipped_deep_invalid_trees_replay_raw_but_remain_absent_after_both_changes
    {type : Core.Ty} (depth : Nat) (left right : Actual type) (first replacement : Core.Store) (fuel : Nat)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    TerminalReturnTreeEvaluatesWithCost names (environment false left.val right.val) first (branch (bad depth) y) right.val first 4 ∧
    TerminalReturnTreeEvaluatesWithCost names (environment false left.val right.val) replacement (branch (bad depth) y) right.val replacement 4 ∧
    elaborateTerminalReturnTree? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context type)) (branch (bad depth) y) = none ∧
    ((inputs false left right).mapIds mapping injective).runTerminalReturnTree? fuel (branch (bad depth) y) replacement = none := by
  have raw : TerminalReturnTreeEvaluatesWithCost names (environment false left.val right.val) first
      (branch (bad depth) y) right.val first 4 :=
    .ifFalse (conditionCost false left.val right.val first) (.single (.expression (yCost false left.val right.val first)))
  have rejected : elaborateTerminalReturnTree? names (context type) (branch (bad depth) y) = none := by
    apply elaborateTerminalReturnTree?_eq_none_iff.mpr
    rintro ⟨result, typing⟩
    cases typing with
    | single leaf => cases leaf
    | conditional _ yes _ => exact badUntyped depth type ⟨result, yes⟩
  exact ⟨raw, raw.change_store replacement,
    (elaborateTerminalReturnTree?_mapIds mapping injective names (context type) _).trans rejected,
    ((inputs false left right).runTerminalReturnTree?_mapIds mapping injective fuel _ replacement).trans
      (LocalInputs.runTerminalReturnTree?_eq_none_iff.mpr rejected)⟩

private def collapse (_ : Resolved.LocalId) : Resolved.LocalId := id 0
private def notY := returned ⟨span, .unary ⟨span, .logicalNot⟩ (ref "y")⟩
private def contrast := branch (branch x notY) notY
private def contrastCore : Core.Expr := .ifE (.var 2) (.ifE (.var 2) (.var 1) (.unary .boolNot (.var 0))) (.unary .boolNot (.var 0))
private def collapsedCore : Core.Expr := .ifE (.var 0) (.ifE (.var 0) (.var 0) (.unary .boolNot (.var 0))) (.unary .boolNot (.var 0))
theorem merging_ids_changes_first_lookup_value_exact_cost_and_accepted_core (store : Core.Store) :
    ¬ Function.Injective collapse ∧
    TerminalReturnTreeEvaluatesWithCost names (environment false (.bool false) (.bool true)) store contrast (.bool false) store 6 ∧
    TerminalReturnTreeEvaluatesWithCost (LocalNameTable.mapIds collapse names)
      (Resolved.LocalScope.mapIds collapse (environment false (.bool false) (.bool true))) store contrast (.bool true) store 7 ∧
    elaborateTerminalReturnTree? names (context .bool) contrast = some (contrastCore, .bool) ∧
    elaborateTerminalReturnTree? (LocalNameTable.mapIds collapse names) (Resolved.LocalScope.mapIds collapse (context .bool)) contrast =
      some (collapsedCore, .bool) ∧ collapsedCore ≠ contrastCore := by
  have selected : LocalExpressionEvaluatesWithCost names (environment false (.bool false) (.bool true)) store (ref "y") (.bool true) store 1 :=
    .identifier .head .head
  have mappedC : LocalExpressionEvaluatesWithCost (LocalNameTable.mapIds collapse names)
      (Resolved.LocalScope.mapIds collapse (environment false (.bool false) (.bool true))) store (ref "c") (.bool true) store 1 :=
    .identifier (.tail (by decide) (.tail (by decide) .head)) .head
  have mappedX : LocalExpressionEvaluatesWithCost (LocalNameTable.mapIds collapse names)
      (Resolved.LocalScope.mapIds collapse (environment false (.bool false) (.bool true))) store (ref "x") (.bool true) store 1 :=
    .identifier (.tail (by decide) .head) .head
  have cR : ResolvesLocalExpression (LocalNameTable.mapIds collapse names) (ref "c") (.var (id 0)) :=
    .identifier (.tail (by decide) (.tail (by decide) .head))
  have xE : TerminalReturnTreeElaborates (LocalNameTable.mapIds collapse names) (Resolved.LocalScope.mapIds collapse (context .bool)) x (.var 0) .bool :=
    .single (.expression (.identifier (.tail (by decide) .head)) (.var .head) (.var .head))
  have nE : TerminalReturnTreeElaborates (LocalNameTable.mapIds collapse names) (Resolved.LocalScope.mapIds collapse (context .bool)) notY (.unary .boolNot (.var 0)) .bool :=
    .single (.expression (.logicalNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))
  have mapped : TerminalReturnTreeElaborates (LocalNameTable.mapIds collapse names) (Resolved.LocalScope.mapIds collapse (context .bool)) contrast collapsedCore .bool :=
    .conditional cR (.var .head) (.var .head) (.conditional cR (.var .head) (.var .head) xE nE) nE
  have originalR : ResolvesLocalExpression names (ref "c") (.var (id 0)) :=
    .identifier (.tail (by decide) (.tail (by decide) .head))
  have originalL : Resolved.Lowers (context .bool).ids (.var (id 0)) (.var 2) :=
    .var (.tail (by decide) (.tail (by decide) .head))
  have originalT : Resolved.HasType (context .bool) (.var (id 0)) .bool :=
    .var (.tail (by decide) (.tail (by decide) .head))
  have originalX : TerminalReturnTreeElaborates names (context .bool) x (.var 1) .bool :=
    .single (.expression (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head)))
  have originalN : TerminalReturnTreeElaborates names (context .bool) notY (.unary .boolNot (.var 0)) .bool :=
    .single (.expression (.logicalNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))
  have original : TerminalReturnTreeElaborates names (context .bool) contrast contrastCore .bool :=
    .conditional originalR originalL originalT (.conditional originalR originalL originalT originalX originalN) originalN
  refine ⟨?_, .ifFalse (conditionCost false (.bool false) (.bool true) store) (.single (.expression (.logicalNot selected))),
    .ifTrue mappedC (.ifTrue mappedC (.single (.expression mappedX))), original.complete, mapped.complete, by decide⟩
  intro injective
  have distinct : id 2 ≠ id 0 := by decide
  exact distinct (injective (a₁ := id 2) (a₂ := id 0) rfl)

end Tests.FrontendTerminalReturnTreeInvariance
