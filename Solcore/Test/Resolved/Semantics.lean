import Solcore.Resolved.FreshIdentity
import Solcore.Resolved.Scope
import Solcore.Resolved.Renaming
import Solcore.Core.LocalFragment
import Solcore.Core.FuelResumptionProperties
import Solcore.Resolved.Typing
import Solcore.Resolved.Eval
import Solcore.Core.Machine
import Solcore.Core.ExactFuelProperties
import Solcore.Core.Safety
import Solcore.Resolved
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Resolved.WordLessWithIds

/-!
# Resolved syntax tests

Resolved local semantics, identities and scopes, ordered pairs, word comparisons, and the public
boundary of resolved programs.
-/

section
-- leanmerge: from Solcore.Test.ResolvedFreshBindingProperties
/-! Fresh allocation is local to the caller's scope. Extension must preserve
both free outer references and existing inner binders, even when they share the new ID. -/

set_option autoImplicit false

namespace Tests.ResolvedFreshBinding

open Solcore Solcore.Resolved

private def modulePath : Workspace.ModulePath := ⟨[⟨"Fresh", by decide⟩], by decide⟩
private def owner : DeclarationId := ⟨⟨.main, modulePath⟩, 0⟩
private def oldId : LocalId := ⟨owner, 0⟩
private def innerId : LocalId := ⟨owner, 3⟩
private def otherOwnerId : LocalId := ⟨{ owner with declarationIndex := 1 }, 999⟩
private def outsideId : LocalId := ⟨owner, 4⟩
private def scope : List LocalId := [oldId, innerId, oldId]
private def allocated : LocalId := freshLocalId owner scope

theorem allocation_respects_owner_and_supplied_scope :
    allocated = outsideId ∧ allocated.owner = owner ∧ allocated ∉ scope :=
  ⟨by decide, freshLocalId_owner owner scope, freshLocalId_not_mem owner scope⟩

theorem other_owners_and_permutations_do_not_change_allocation :
    freshLocalId owner (otherOwnerId :: scope) = allocated ∧
    freshLocalId owner [innerId, oldId, oldId] = allocated := by
  constructor
  · exact freshLocalId_cons_of_ne_owner owner scope otherOwnerId (by decide)
  · exact freshLocalId_eq_of_perm owner (List.Perm.swap oldId innerId [oldId])

theorem second_allocation_advances :
    (freshLocalId owner (allocated :: scope)).binderIndex = allocated.binderIndex + 1 ∧
    freshLocalId owner (allocated :: scope) ≠ allocated :=
  ⟨freshLocalId_cons_fresh_binderIndex owner scope, freshLocalId_cons_fresh_ne owner scope⟩

theorem scope_freshness_is_not_global_freshness :
    allocated ∉ scope ∧ allocated ∈ [outsideId] :=
  ⟨freshLocalId_not_mem owner scope, by decide⟩

private def environment : Environment :=
  [(oldId, .bool true), (innerId, .bool false), (oldId, .bool false)]
private def nested : Expr :=
  .letE allocated (.bool true) (.letE innerId (.bool false)
    (.ifE (.var allocated) (.var oldId) (.var innerId)))
private def originalCore : Core.Expr :=
  .letE (.bool true) (.letE (.bool false) (.ifE (.var 1) (.var 2) (.var 0)))
private def insertedCore : Core.Expr :=
  .letE (.bool true) (.letE (.bool false) (.ifE (.var 1) (.var 3) (.var 0)))

private theorem nested_lowered : Lowers scope nested originalCore :=
  .letE .bool (.letE .bool (.ifE
    (.var (.tail (by decide) .head))
    (.var (.tail (by decide) (.tail (by decide) .head))) (.var .head)))

private theorem nested_evaluates (store : Core.Store) :
    Evaluates environment store nested (.bool true) store :=
  .letE .bool (.letE .bool (.ifTrue
    (.var (.tail (by decide) .head))
    (.var (.tail (by decide) (.tail (by decide) .head)))))

/-- An existing inner binder equal to the inserted ID still wins lookup. The
outer oldId reference also retains its value, and the store is arbitrary. -/
theorem nested_binder_equal_to_inserted_id_keeps_value (store : Core.Store) :
    Evaluates environment store nested (.bool true) store ∧
    Evaluates ((allocated, .bool false) :: environment) store nested (.bool true) store :=
  ⟨nested_evaluates store, (nested_evaluates store).weaken_allocated owner (.bool false)⟩

/-- The bound positions 1 and 0 stay fixed; only the free outer position 2 shifts. -/
theorem nested_lowering_shifts_only_the_free_reference :
    nested.lower? scope = some originalCore ∧
    nested.lower? (allocated :: scope) = some insertedCore ∧
    nested.lower? (allocated :: scope) =
      (nested.lower? scope).map (fun core => core.weakenAt 0) := by
  have extended := (nested_lowered.weaken_fresh (freshLocalId_not_mem owner scope)).complete
  refine ⟨nested_lowered.complete, ?_,
    Expr.lower?_weaken_fresh nested_lowered.wellScoped (freshLocalId_not_mem owner scope)⟩
  simpa [allocated, originalCore, insertedCore, Core.Expr.weakenAt] using extended

/-- Without the absent-ID premise, an added outer entry captures the old reference. -/
theorem nonfresh_insertion_captures_reference (store : Core.Store) :
    Evaluates environment store (.var oldId) (.bool true) store ∧
    Evaluates ((oldId, .bool false) :: environment) store (.var oldId) (.bool false) store ∧
    ¬ Evaluates ((oldId, .bool false) :: environment) store (.var oldId) (.bool true) store := by
  refine ⟨.var .head, .var .head, ?_⟩
  intro evaluation
  have opposite : Evaluates ((oldId, .bool false) :: environment) store
      (.var oldId) (.bool false) store := .var .head
  have impossible := (evaluation_deterministic evaluation opposite).1
  cases impossible

private def skippedMissing : Expr := .ifE (.bool true) (.var oldId) (.var allocated)

/-- Evaluation preservation does not require the old, unselected branch to be scoped. -/
theorem skipped_unscoped_branch_keeps_evaluation (store : Core.Store) :
    skippedMissing.lower? scope = none ∧
    skippedMissing.lower? (allocated :: scope) = some (.ifE (.bool true) (.var 1) (.var 0)) ∧
    Evaluates ((allocated, .bool false) :: environment) store skippedMissing (.bool true) store := by
  have evaluation : Evaluates environment store skippedMissing (.bool true) store :=
    .ifTrue .bool (.var .head)
  exact ⟨by decide, by decide, evaluation.weaken_allocated owner (.bool false)⟩

end Tests.ResolvedFreshBinding
end

section
-- leanmerge: from Solcore.Test.ResolvedIdentityRenamingProperties
/-! Compile-time identity-renaming consumers. Injective index shifts preserve
meaning, while a constant map captures an outer reference under an inner let. -/

set_option autoImplicit false

namespace Tests.ResolvedIdentityRenaming

open Solcore Solcore.Resolved

private def modulePath : Workspace.ModulePath := ⟨[⟨"Rename", by decide⟩], by decide⟩
private def outerId : LocalId := ⟨⟨⟨.main, modulePath⟩, 0⟩, 0⟩
private def innerId : LocalId := { outerId with binderIndex := 1 }

private def shift (id : LocalId) : LocalId := { id with binderIndex := id.binderIndex + 1 }

private theorem shift_injective : Function.Injective shift := by
  intro first second same
  have owners := congrArg LocalId.owner same
  change first.owner = second.owner at owners
  have shifted := congrArg LocalId.binderIndex same
  change first.binderIndex + 1 = second.binderIndex + 1 at shifted
  have indices := Nat.add_right_cancel shifted
  cases first
  cases second
  cases owners
  cases indices
  rfl

private def expression : Expr :=
  .letE outerId (.bool false) (.letE innerId (.bool true) (.var outerId))

private def originalCore : Core.Expr := .letE (.bool false) (.letE (.bool true) (.var 1))
private def capturedCore : Core.Expr := .letE (.bool false) (.letE (.bool true) (.var 0))

private theorem original_lowered : Lowers [] expression originalCore :=
  .letE .bool (.letE .bool (.var (.tail (by decide) .head)))

private theorem original_typed : HasType [] expression .bool :=
  .letE .bool (.letE .bool (.var (.tail (by decide) .head)))

private theorem original_evaluates (store : Core.Store) :
    Evaluates [] store expression (.bool false) store :=
  .letE .bool (.letE .bool (.var (.tail (by decide) .head)))

theorem injective_shift_keeps_core :
    (expression.renameIds shift).lower? [] = some originalCore := by
  simpa only [List.map_nil] using
    (Expr.lower?_renameIds shift shift_injective expression []).trans original_lowered.complete

theorem injective_shift_keeps_type : HasType [] (expression.renameIds shift) .bool :=
  (typing_renameIds_iff shift shift_injective).mpr original_typed

theorem injective_shift_keeps_value_and_store (store : Core.Store) :
    Evaluates [] store (expression.renameIds shift) (.bool false) store :=
  (evaluates_renameIds_iff shift shift_injective).mpr (original_evaluates store)

private def collapse (_id : LocalId) : LocalId := outerId

private theorem collapsed_lowered : Lowers [] (expression.renameIds collapse) capturedCore :=
  .letE .bool (.letE .bool (.var .head))

theorem constant_map_changes_core :
    (expression.renameIds collapse).lower? [] ≠ expression.lower? [] := by
  rw [collapsed_lowered.complete, original_lowered.complete]
  intro same
  cases same

theorem constant_map_captures_outer_reference (store : Core.Store) :
    Evaluates [] store (expression.renameIds collapse) (.bool true) store :=
  .letE .bool (.letE .bool (.var .head))

theorem constant_map_does_not_preserve_result (store finalStore : Core.Store) :
    ¬ Evaluates [] store (expression.renameIds collapse) (.bool false) finalStore := by
  intro evaluation
  have impossible := (evaluation_deterministic evaluation (constant_map_captures_outer_reference store)).1
  cases impossible

theorem constant_map_not_injective : ¬ Function.Injective collapse := by
  intro injective
  have same : outerId = innerId := injective rfl
  have different : outerId ≠ innerId := by decide
  exact different same

end Tests.ResolvedIdentityRenaming
end

section
-- leanmerge: from Solcore.Test.ResolvedPairBoundary
/-! Independent resolved provenance and exact Core paths. Static component types
are separate from opaque raw values; ID and whole-scoping premises remain visible. -/
set_option autoImplicit false
namespace Tests
open Solcore
namespace ResolvedPairBoundary
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ResolvedPairs", by decide⟩], by decide⟩⟩, 17⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def env (x y : Core.Value) : Resolved.Environment := [(id 7, x), (id 2, y)]
private def context : Resolved.Context := [(id 7, .word), (id 2, .word)]
private def source : Resolved.Expr := .pair (.var (id 7)) (.var (id 2))
private def core : Core.Expr := .pair (.var 0) (.var 1)
private def product : Core.Ty := .product .word .word
private structure Certificate (x y : Core.Value) (store : Core.Store) where
  expr : Resolved.Expr
  output : Core.Expr
  value : Core.Value
  type : Core.Ty
  cost : Nat
  lowered : Resolved.Lowers [id 7, id 2] expr output
  typed : Resolved.HasType context expr type
  evaluated : Resolved.Evaluates (env x y) store expr value store
  paths : ∀ k, Core.Steps cost ⟨.eval output [x, y], k, store⟩ ⟨.ret value, k, store⟩
private def simple (x y : Core.Value) (store : Core.Store) : Certificate x y store :=
  ⟨source, core, .pair x y, product, 5, .pair (.var .head) (.var (.tail (by decide) .head)),
    .pair (.var .head) (.var (.tail (by decide) .head)), .pair (.var .head) (.var (.tail (by decide) .head)),
    fun _ => .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl))))⟩
private def nested (x y : Core.Value) (store : Core.Store) : Certificate x y store :=
  ⟨.pair (.var (id 7)) (.pair (.var (id 2)) (.var (id 7))), .pair (.var 0) (.pair (.var 1) (.var 0)),
    .pair x (.pair y x), .product .word product, 9,
    .pair (.var .head) (.pair (.var (.tail (by decide) .head)) (.var .head)),
    .pair (.var .head) (.pair (.var (.tail (by decide) .head)) (.var .head)),
    .pair (.var .head) (.pair (.var (.tail (by decide) .head)) (.var .head)),
    fun _ => .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .enterPair
      (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair (.cons .applyPair .refl))))))))⟩
private def shadowed (x y : Core.Value) (store : Core.Store) : Certificate x y store :=
  ⟨.pair (.letE (id 7) (.var (id 2)) (.var (id 7))) (.var (id 7)), .pair (.letE (.var 1) (.var 0)) (.var 0),
    .pair y x, product, 8,
    .pair (.letE (.var (.tail (by decide) .head)) (.var .head)) (.var .head),
    .pair (.letE (.var (.tail (by decide) .head)) (.var .head)) (.var .head),
    .pair (.letE (.var (.tail (by decide) .head)) (.var .head)) (.var .head),
    fun _ => .cons .enterPair (.cons .enterLet (.cons (.var rfl) (.cons .bindLet
      (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))))⟩
private def boundPair (x y : Core.Value) (store : Core.Store) : Certificate x y store :=
  ⟨.letE (id 7) source source, .letE core (.pair (.var 0) (.var 2)), .pair (.pair x y) y, .product product .word, 12,
    .letE (.pair (.var .head) (.var (.tail (by decide) .head)))
      (.pair (.var .head) (.var (.tail (by decide) (.tail (by decide) .head)))),
    .letE (.pair (.var .head) (.var (.tail (by decide) .head)))
      (.pair (.var .head) (.var (.tail (by decide) (.tail (by decide) .head)))),
    .letE (.pair (.var .head) (.var (.tail (by decide) .head)))
      (.pair (.var .head) (.var (.tail (by decide) (.tail (by decide) .head)))),
    fun _ => .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
      (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons .enterPair (.cons (.var rfl)
        (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))))))))⟩
private def shift (binder : Resolved.LocalId) : Resolved.LocalId := { binder with binderIndex := binder.binderIndex + 5 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases left; cases right; cases owners; cases indices; rfl
private def observe (result : Core.StatefulRunResult) (remaining fuel : Nat) (value : Core.Value) (store : Core.Store) : Bool :=
  match result with
  | .done actual final => decide (remaining ≤ fuel ∧ actual = value ∧ final = store)
  | .outOfFuel checkpoint => decide (fuel < remaining ∧ checkpoint.store = store)
  | .fault _ _ => false
private def execute (start : Core.State) (value : Core.Value) (store : Core.Store) (cost : Nat)
    (path : Core.Steps cost start (.final value store)) : IO Unit := do
  for fuel in List.range (cost + 3) do
    have _ := path.runStateful_done_iff (fuel := fuel)
    assertTrue (observe (Core.runStateful fuel start) cost fuel value store) "independent value/cost/own store changed"
  for spent in List.range cost do
    match exhausted : Core.runStateful spent start with
    | .outOfFuel checkpoint =>
        have _ := path.residual_of_outOfFuel exhausted
        for additional in List.range (cost - spent + 3) do
          have _ := Core.runStateful_resume exhausted additional
          assertTrue (observe (Core.runStateful additional checkpoint) (cost - spent) additional value store) "genuine residual threshold changed"
        if 1 < cost - spent then
          match again : Core.runStateful 1 checkpoint with
          | .outOfFuel next =>
              have _ := Core.runStateful_resume again (cost - spent - 1)
              assertTrue (decide (Core.runStateful (cost - spent - 1) next = .done value store)) "three chunks lost captured state"
          | _ => throw (IO.userError "second checkpoint missing")
        if 0 < spent then assertTrue (match Core.runStateful (cost - spent) start with | .outOfFuel _ => true | _ => false) "restart passed as resumption"
    | _ => throw (IO.userError "genuine checkpoint missing")
private def check {x y : Core.Value} {store : Core.Store} (proof : Certificate x y store)
    (expectedCore : Core.Expr) (expected : Core.Value) (expectedType : Core.Ty) (cost : Nat) : IO Unit := do
  assertTrue (decide (proof.output = expectedCore ∧ proof.value = expected ∧ proof.type = expectedType ∧ proof.cost = cost ∧
    proof.expr.lower? [id 7, id 2] = some expectedCore ∧ Resolved.infer? context proof.expr = some expectedType)) "independent ordered provenance changed"
  have _ := proof.lowered.complete
  have coreTyped := proof.lowered.preserves_type (context := context) proof.typed
  have _ := proof.lowered.reflects_type (context := context) coreTyped
  have coreEvaluation := proof.evaluated.toCore proof.lowered
  have _ := Resolved.Evaluates.ofCore (environment := env x y) proof.lowered coreEvaluation
  have _ := (proof.lowered.evaluates_iff (environment := env x y)).mp proof.evaluated
  have _ := (proof.lowered.evaluates_iff (environment := env x y)).mpr coreEvaluation
  have _ := proof.evaluated.store_eq
  have renamed := (Resolved.evaluates_renameIds_iff shift shiftInjective).mpr proof.evaluated
  have _ := (Resolved.evaluates_renameIds_iff shift shiftInjective).mp renamed
  have _ := Resolved.Expr.lower?_renameIds shift shiftInjective proof.expr [id 7, id 2]
  assertTrue (decide ((proof.expr.renameIds shift).lower? ([id 7, id 2].map shift) = some expectedCore)) "injective ID change altered ordered Core"
  have fresh : id 99 ∉ [id 7, id 2] := by decide
  have inserted := proof.evaluated.weaken_fresh (newId := id 99) (newValue := .cellRef .word 999) fresh
  have _ := inserted.reflect_insert_fresh (leading := []) proof.lowered.wellScoped fresh
  have _ := (proof.lowered.wellScoped.evaluates_weaken_fresh_iff (environment := env x y) fresh).mp inserted
  have shifted := (proof.paths []).weakenAt_zero_localFragment proof.lowered.localFragment (.cellRef .word 999) []
  execute (.initial proof.output [x, y] store) proof.value store proof.cost (proof.paths [])
  execute (.initial (proof.output.weakenAt 0) [.cellRef .word 999, x, y] store) proof.value store proof.cost shifted
  for k in [[Core.Frame.letBody (.var 0) []], [.unaryApply .wordNot]] do
    have _ := proof.lowered.localFragment.steps_insert [] [x, y] (.cellRef .word 999) (proof.paths []) k
    let start : Core.State := ⟨.eval proof.output [x, y], k, store⟩
    match k with
    | [.unaryApply .wordNot] => assertTrue (decide (Core.runStateful cost start =
        .fault (.invalidUnaryOperand .wordNot expected) ⟨.ret expected, k, store⟩)) "arbitrary continuation endpoint promised exhaustion"
    | _ => assertTrue (decide (Core.runStateful cost start = .outOfFuel ⟨.ret expected, k, store⟩)) "safe pending continuation was executed early"
private def checkpoints (x y : Core.Value) (store : Core.Store) : IO Unit := do
  for (input, indexX, indexY) in [([x, y], 0, 1), ([Core.Value.cellRef .word 999, x, y], 1, 2)] do
    let start := Core.State.initial (.pair (.var indexX) (.var indexY)) input store
    assertTrue (decide (Core.runStateful 2 start = .outOfFuel ⟨.ret x, [.pairRight (.var indexY) input], store⟩ ∧
      Core.runStateful 3 start = .outOfFuel ⟨.eval (.var indexY) input, [.pairApply x], store⟩ ∧
      Core.runStateful 4 start = .outOfFuel ⟨.ret y, [.pairApply x], store⟩)) "own pair frames or actual component order changed"
    let localLeft := Core.State.initial (.pair (.letE (.var indexY) (.var 0)) (.var indexX)) input store
    assertTrue (decide (Core.runStateful 4 localLeft = .outOfFuel ⟨.eval (.var 0) (y :: input), [.pairRight (.var indexX) input], store⟩ ∧
      Core.runStateful 6 localLeft = .outOfFuel ⟨.eval (.var indexX) input, [.pairApply y], store⟩)) "left local shadow escaped into the right operand"
  assertTrue (decide (Core.runStateful 2 (.initial core [x, y] store) ≠
    Core.runStateful 2 (.initial (core.weakenAt 0) [.cellRef .word 999, x, y] store))) "insertion equated captured environments"
private def nominal : IO Unit := do
  for left in [Core.Ty.namedData ⟨91⟩, .word] do
    for right in [Core.Ty.namedData ⟨92⟩, .function (.namedData ⟨999⟩) .unit] do
      let ctx : Resolved.Context := [(id 7, left), (id 2, right)]
      have typed : Resolved.HasType ctx source (.product left right) := .pair (.var .head) (.var (.tail (by decide) .head))
      have _ := typed.lowers
      have _ := Resolved.infer_complete typed
      assertTrue (decide (source.lower? ctx.ids = some core ∧ Resolved.infer? ctx source = some (.product left right) ∧
        Core.infer? [left, right] core [] = some (.product left right))) "nominal static pair required manufactured actual inhabitants"
private def boundaries (store : Core.Store) : IO Unit := do
  let old := simple (w 9) (w 2) store
  have _ : ¬ Resolved.Lowers [id 7, id 2] source (.pair (.var 1) (.var 0)) := by
    intro wrong
    have impossible := old.lowered.deterministic wrong
    cases impossible
  assertTrue (decide (Core.infer? [.word, .word] (.pair (.var 1) (.var 0)) = some product)) "wrong same-typed Core contrast disappeared"
  let duplicate : Resolved.Environment := [(id 7, w 9), (id 7, w 99), (id 2, w 2)]
  have duplicated : Resolved.Evaluates duplicate store source (.pair (w 9) (w 2)) store :=
    .pair (.var .head) (.var (.tail (by decide) (.tail (by decide) .head)))
  have exactDuplicate : Resolved.Lowers duplicate.ids source (.pair (.var 0) (.var 2)) :=
    .pair (.var .head) (.var (.tail (by decide) (.tail (by decide) .head)))
  have _ := duplicated.toCore exactDuplicate
  assertTrue (decide (source.lower? duplicate.ids = some (.pair (.var 0) (.var 2)) ∧
    Core.runStateful 5 (.initial (.pair (.var 0) (.var 2)) duplicate.values store) = .done (.pair (w 9) (w 2)) store)) "duplicate first-match ID changed value or position"
  let swapped : Resolved.Environment := [(id 2, w 2), (id 7, w 9)]
  have _ : Resolved.Evaluates swapped store source (.pair (w 9) (w 2)) store := .pair (.var (.tail (by decide) .head)) (.var .head)
  assertTrue (decide (swapped.ids ≠ [id 7, id 2] ∧ Core.runStateful 5 (.initial core swapped.values store) =
    .done (.pair (w 2) (w 9)) store)) "unaligned Core positions were confused with named evaluation"
  let collapse := fun _ : Resolved.LocalId => id 7
  have _ : ¬ Function.Injective collapse := by
    intro injective
    have impossible := injective (a₁ := id 7) (a₂ := id 2) rfl
    cases impossible
  have _ := source.renameIds_id
  have _ := source.renameIds_comp collapse shift
  have collapsed : Resolved.Evaluates (Resolved.LocalScope.mapIds collapse (env (w 9) (w 2))) store
      (source.renameIds collapse) (.pair (w 9) (w 9)) store := .pair (.var .head) (.var .head)
  have _ := collapsed.store_eq
  assertTrue (decide (source.renameIds collapse = .pair (.var (id 7)) (.var (id 7)) ∧
    (source.renameIds collapse).lower? ([id 7, id 2].map collapse) = some (.pair (.var 0) (.var 0)) ∧
    (.pair (w 9) (w 9) : Core.Value) ≠ .pair (w 9) (w 2))) "noninjective structural map acquired semantic invariance"
  let missing : Resolved.Expr := .pair (.var (id 7)) (.var (id 99))
  have enabled : Resolved.Evaluates [(id 99, w 2), (id 7, w 9)] store missing (.pair (w 9) (w 2)) store :=
    .pair (.var (.tail (by decide) .head)) (.var .head)
  have _ : ¬ Resolved.WellScoped [id 7] missing := by
    change ¬ Resolved.WellScoped [id 7] (.pair (.var (id 7)) (.var (id 99)))
    intro h; cases h with | pair _ h => cases h with | var member => simp [id] at member
  have _ : ¬ ∃ value final, Resolved.Evaluates [(id 7, w 9)] store missing value final := by
    rintro ⟨value, final, evaluation⟩
    change Resolved.Evaluates _ _ (.pair (.var (id 7)) (.var (id 99))) _ _ at evaluation
    cases evaluation with
    | pair _ right =>
      cases right with
      | var found =>
        have impossible := Resolved.LocalScope.lookup?_iff.mpr found
        change none = some _ at impossible
        cases impossible
  assertTrue (decide (id 99 ∉ [id 7] ∧ missing.lower? [id 7] = none ∧
    missing.lower? [id 99, id 7] = some (.pair (.var 1) (.var 0)))) "fresh insertion wrongly reflected a previously missing child"
  have _ := enabled.store_eq
  let captured : Resolved.Environment := (id 7, w 99) :: env (w 9) (w 2)
  have _ : Resolved.Evaluates captured store source (.pair (w 99) (w 2)) store :=
    .pair (.var .head) (.var (.tail (by decide) (.tail (by decide) .head)))
  assertTrue (decide (source.lower? captured.ids = some (.pair (.var 0) (.var 2)) ∧
    source.lower? captured.ids ≠ some (core.weakenAt 0))) "nonfresh suffix insertion acquired the fresh weakening law"
  let selected : Resolved.Expr := .ifE (.bool true) source missing
  have skipped : Resolved.Evaluates (env (w 9) (w 2)) store selected (.pair (w 9) (w 2)) store := .ifTrue .bool old.evaluated
  have _ := skipped.weaken_allocated owner (.cellRef .word 999)
  have _ := (Resolved.evaluates_renameIds_iff shift shiftInjective).mpr skipped
  assertTrue (decide (selected.lower? [id 7, id 2] = none ∧ Resolved.infer? context selected = none)) "selected raw success bypassed whole missing-child checking"
  let invalid : Resolved.Expr := .ifE (.bool true) source (.pair (.unary .wordNot (.bool true)) (.var (id 7)))
  have _ : Resolved.Evaluates (env (w 9) (w 2)) store invalid (.pair (w 9) (w 2)) store := .ifTrue .bool old.evaluated
  assertTrue ((invalid.lower? [id 7, id 2]).isSome && (Resolved.infer? context invalid).isNone) "whole type checking ignored the unselected wrong primitive"
  have fresh : id 7 ∉ [id 2] := by decide
  have kept := old.evaluated.insert_fresh (leading := [(id 7, w 9)]) (suffix := [(id 2, w 2)]) (newValue := w 99) fresh
  have _ := kept.reflect_insert_fresh old.lowered.wellScoped fresh
  have _ := old.lowered.insert_fresh (kept := [id 7]) (scope := [id 2]) fresh
  assertTrue (decide (source.lower? [id 7, id 7, id 2] = some (.pair (.var 0) (.var 2)))) "retained prefix was incorrectly required fresh"
end ResolvedPairBoundary

open ResolvedPairBoundary

def resolvedPairBoundaryTests : IO Unit := do
  nominal
  for store in stores do
    boundaries store
    for (x, y) in [(w 9, w 2),
        (Core.Value.cellRef .word 999, .closure .word .bool (.var 80) []),
        (.constructed ⟨⟨91⟩, 4⟩ (.pair .unit (w 7)), .unit)] do
      check (simple x y store) core (.pair x y) product 5
      check (nested x y store) (.pair (.var 0) (.pair (.var 1) (.var 0))) (.pair x (.pair y x)) (.product .word product) 9
      check (shadowed x y store) (.pair (.letE (.var 1) (.var 0)) (.var 0)) (.pair y x) product 8
      check (boundPair x y store) (.letE core (.pair (.var 0) (.var 2))) (.pair (.pair x y) y) (.product product .word) 12
      checkpoints x y store

end Tests
end

section
-- leanmerge: from Solcore.Test.ResolvedLocalSemantics
/-! Concrete resolved-local regressions. These test structured identities, not
source-name resolution; repeated identities intentionally exercise first match. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Resolved

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def pathA : Workspace.ModulePath := ⟨[⟨"A", by decide⟩], by decide⟩
private def pathB : Workspace.ModulePath := ⟨[⟨"B", by decide⟩], by decide⟩
private def outerId : LocalId := ⟨⟨⟨.main, pathA⟩, 0⟩, 0⟩
private def innerId : LocalId := { outerId with binderIndex := 1 }
private def otherDeclaration : LocalId :=
  { outerId with owner := { outerId.owner with declarationIndex := 1 } }
private def otherModule : LocalId := ⟨⟨⟨.main, pathB⟩, 0⟩, 0⟩
private def otherLibrary : LocalId := ⟨⟨⟨.standard, pathA⟩, 0⟩, 0⟩
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def environment : Environment := [(outerId, .bool true)]
private def context : Context := [(outerId, .bool)]
private def stored : Core.Store := [.word (w 19), .bool false]

example : outerId ≠ innerId ∧ outerId ≠ otherDeclaration ∧
    outerId ≠ otherModule ∧ outerId ≠ otherLibrary := by decide

example : LocalScope.index? [outerId] outerId = some 0 ∧
    LocalScope.index? [outerId] innerId = none := by decide

private def noCapture : Expr := .letE innerId (.bool false) (.var outerId)
private def noCaptureCore : Core.Expr := .letE (.bool false) (.var 1)

private theorem noCapture_lowered :
    Lowers (LocalScope.ids environment) noCapture noCaptureCore :=
  .letE .bool (.var (.tail (by decide) .head))

private theorem noCapture_typed : HasType context noCapture .bool :=
  .letE .bool (.var (.tail (by decide) .head))

private theorem noCapture_evaluates (store : Core.Store) :
    Evaluates environment store noCapture (.bool true) store :=
  .letE .bool (.var (.tail (by decide) .head))

example (store : Core.Store) :
    Core.Evaluates (LocalScope.values environment) store noCaptureCore (.bool true) store :=
  (noCapture_evaluates store).toCore noCapture_lowered

example : noCapture.lower? [outerId] = some noCaptureCore := noCapture_lowered.complete
example : infer? context noCapture = some .bool := infer_complete noCapture_typed

private def initializer : Expr := .letE innerId (.var outerId) (.var innerId)
private def initializerCore : Core.Expr := .letE (.var 0) (.var 0)

private theorem initializer_lowered :
    Lowers (LocalScope.ids environment) initializer initializerCore :=
  .letE (.var .head) (.var .head)

private theorem initializer_evaluates (store : Core.Store) :
    Evaluates environment store initializer (.bool true) store :=
  .letE (.var .head) (.var .head)

example (store : Core.Store) :
    Core.Evaluates (LocalScope.values environment) store initializerCore (.bool true) store :=
  (initializer_evaluates store).toCore initializer_lowered

-- A binder is unavailable in its own initializer when absent from the old scope.
private def selfInitializer : Expr := .letE innerId (.var innerId) .unit
example : selfInitializer.lower? [] = none := by decide
example {core : Core.Expr} : ¬ Lowers [] selfInitializer core := by
  intro lowered
  have impossible := lowered.complete
  change none = some core at impossible
  cases impossible
example {value : Core.Value} {store finalStore : Core.Store} :
    ¬ Evaluates [] store selfInitializer value finalStore := by
  intro evaluation
  cases evaluation with
  | letE initializer _ =>
      cases initializer with
      | var found => cases found

-- All expression constructors appear here or in the separate unit case.
private def combined : Expr :=
  .letE outerId (.binary .wordAdd (.word (w 2)) (.word (w 3)))
    (.ifE (.unary .boolNot (.bool false)) (.var outerId) (.word (w 0)))
private def combinedCore : Core.Expr :=
  .letE (.binary .wordAdd (.word (w 2)) (.word (w 3)))
    (.ifE (.unary .boolNot (.bool false)) (.var 0) (.word (w 0)))

private theorem combined_lowered : Lowers [] combined combinedCore :=
  .letE (.binary .word .word) (.ifE (.unary .bool) (.var .head) .word)

private theorem combined_typed : HasType [] combined .word :=
  .letE (.binary .word .word) (.ifE (.unary .bool) (.var .head) .word)

private theorem combined_evaluates (store : Core.Store) :
    Evaluates [] store combined (.word (w 5)) store :=
  .letE (.binary .word .word rfl)
    (.ifTrue (.unary .bool rfl) (.var .head))

example (store : Core.Store) : Core.Evaluates [] store combinedCore (.word (w 5)) store :=
  (combined_evaluates store).toCore combined_lowered
example (store : Core.Store) : Evaluates [] store combined (.word (w 5)) store :=
  Evaluates.ofCore combined_lowered ((combined_evaluates store).toCore combined_lowered)
example : infer? [] combined = some .word := infer_complete combined_typed
example (store : Core.Store) : Evaluates [] store .unit .unit store := .unit
example : Lowers [] .unit .unit := .unit
example : HasType [] .unit .unit := .unit

private def duplicates : Environment := [(outerId, .bool false), (outerId, .bool true)]
example : LocalScope.Lookup duplicates outerId (.bool false) := .head
example : LocalScope.IndexOf (LocalScope.ids duplicates) outerId 0 := .head
example : ¬ LocalScope.Lookup duplicates outerId (.bool true) := by
  intro found
  have impossible := found.value_unique (show LocalScope.Lookup duplicates outerId (.bool false) from .head)
  cases impossible
example (store : Core.Store) : Evaluates duplicates store (.var outerId) (.bool false) store :=
  .var .head

private def badUnary : Expr := .unary .boolNot (.word (w 0))
private def badBinary : Expr := .binary .wordAdd (.bool true) (.word (w 1))
private def badCondition : Expr := .ifE .unit (.bool true) (.bool false)

private theorem rejected_no_type {expr : Expr} (rejected : infer? [] expr = none)
    {type : Core.Ty} : ¬ HasType [] expr type := by
  intro typed
  have accepted := infer_complete typed
  rw [rejected] at accepted
  cases accepted

example {type : Core.Ty} : ¬ HasType [] badUnary type := rejected_no_type (by decide)
example {type : Core.Ty} : ¬ HasType [] badBinary type := rejected_no_type (by decide)
example {type : Core.Ty} : ¬ HasType [] badCondition type := rejected_no_type (by decide)

-- Evaluation selects one branch, but lowering and type checking inspect both.
private def skippedMissing : Expr := .ifE (.bool true) .unit (.var innerId)
private theorem skipped_evaluates (store : Core.Store) :
    Evaluates [] store skippedMissing .unit store := .ifTrue .bool .unit
example : skippedMissing.lower? [] = none := by decide
example {type : Core.Ty} : ¬ HasType [] skippedMissing type := rejected_no_type (by decide)
example {value : Core.Value} {store finalStore : Core.Store}
    (evaluation : Evaluates [] store skippedMissing value finalStore) :
    value = .unit ∧ finalStore = store :=
  evaluation_deterministic evaluation (skipped_evaluates store)
example (store : Core.Store) :
    Evaluates [] store (.ifE (.bool false) (.var innerId) .unit) .unit store :=
  .ifFalse .bool .unit

private def testIdentityAndScope : IO Unit := do
  for other in [innerId, otherDeclaration, otherModule, otherLibrary] do
    assertTrue (decide (outerId ≠ other)) "structured local identity components collided"
  assertTrue (decide (LocalScope.lookup? environment outerId = some (.bool true)))
    "head local lookup failed"
  assertTrue (decide (LocalScope.index? [outerId] outerId = some 0)) "head index was not zero"
  assertTrue (decide (LocalScope.lookup? environment innerId = none)) "absent local was found"
  assertTrue (decide (LocalScope.index? [outerId] innerId = none)) "absence became index zero"
  assertTrue (decide (LocalScope.lookup? duplicates outerId = some (.bool false)))
    "duplicate identity did not use first value"
  assertTrue (decide (LocalScope.index? (LocalScope.ids duplicates) outerId = some 0))
    "duplicate identity did not use first index"
  assertTrue (decide (infer? [(outerId, .bool), (outerId, .word)] (.var outerId) = some .bool))
    "duplicate identity did not use first type"

private def testLoweringAndExecution : IO Unit := do
  let cases : List (Environment × Expr × Core.Expr × Core.Value) := [
    ([], .unit, .unit, .unit),
    (environment, noCapture, noCaptureCore, .bool true),
    (environment, initializer, initializerCore, .bool true),
    ([], combined, combinedCore, .word (w 5)),
    (duplicates, .var outerId, .var 0, .bool false)]
  for (env, expr, core, expected) in cases do
    assertTrue (decide (expr.lower? (LocalScope.ids env) = some core))
      "resolved local lowering produced the wrong positional expression"
    assertTrue (Core.runStateful 40 (Core.State.initial core (LocalScope.values env) stored) ==
      .done expected stored) "lowered local execution changed the value or store"
  assertTrue (decide (selfInitializer.lower? [] = none)) "initializer saw its new binder"
  assertTrue (decide (infer? context noCapture = some .bool)) "outer variable type was captured"
  assertTrue (decide (infer? [] combined = some .word)) "combined local expression was rejected"
  assertTrue (decide (skippedMissing.lower? [] = none)) "lowering skipped an ill-scoped branch"
  assertTrue (decide (infer? [] skippedMissing = none)) "checking skipped an ill-scoped branch"

private def testRejections : IO Unit := do
  let cases : List (Expr × Core.Expr × Core.MachineFault) := [
    (badUnary, .unary .boolNot (.word (w 0)), .invalidUnaryOperand .boolNot (.word (w 0))),
    (badBinary, .binary .wordAdd (.bool true) (.word (w 1)),
      .invalidBinaryOperands .wordAdd (.bool true) (.word (w 1))),
    (badCondition, .ifE .unit (.bool true) (.bool false), .expectedBool .unit)]
  for (expr, core, fault) in cases do
    assertTrue (decide (expr.lower? [] = some core)) "well-scoped ill-typed expression failed lowering"
    assertTrue (decide (infer? [] expr = none)) "ill-typed resolved expression was accepted"
    assertTrue (Core.run 20 (Core.State.initial core) == .fault fault)
      "ill-typed primitive or condition produced the wrong Core fault"

/-- Structured lookup, all local constructors, exact execution, and semantic boundaries. -/
def resolvedLocalSemanticsTests : IO Unit := do
  testIdentityAndScope
  testLoweringAndExecution
  testRejections

end Tests
end

section
-- leanmerge: from Solcore.Test.ResolvedPairProperties
/-! Independent ordered products: duplicate identities, untyped actual values,
and arbitrary product types are separate from successful whole checking. -/
set_option autoImplicit false
namespace Tests.ResolvedPair
open Solcore Solcore.Resolved

private def owner : DeclarationId := ⟨⟨.main, ⟨[⟨"ResolvedPair", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : LocalId := ⟨owner, index⟩
private theorem different : ident 0 ≠ ident 1 := by decide
private def spine (id : LocalId) : Nat → Expr
  | 0 => .unit
  | n + 1 => .pair (.var id) (spine id n)
private def spineCore : Nat → Core.Expr
  | 0 => .unit
  | n + 1 => .pair (.var 0) (spineCore n)
private def spineType (type : Core.Ty) : Nat → Core.Ty
  | 0 => .unit
  | n + 1 => .product type (spineType type n)
private def spineValue (value : Core.Value) : Nat → Core.Value
  | 0 => .unit
  | n + 1 => .pair value (spineValue value n)
private theorem spineLower (id : LocalId) (scope : List LocalId) (n : Nat) :
    Lowers (id :: scope) (spine id n) (spineCore n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.var .head) ih
private theorem spineTyped (id : LocalId) (context : Context) (type : Core.Ty) (n : Nat) :
    HasType ((id, type) :: context) (spine id n) (spineType type n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.var .head) ih
private theorem spineScoped (id : LocalId) (scope : List LocalId) (n : Nat) :
    WellScoped (id :: scope) (spine id n) := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.var (by simp)) ih
private theorem spineEval (id : LocalId) (environment : Environment) (value : Core.Value) (store : Core.Store) (n : Nat) :
    Evaluates ((id, value) :: environment) store (spine id n) (spineValue value n) store := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.var .head) ih
private theorem spineCoreEval (environment : Core.Environment) (value : Core.Value) (store : Core.Store) (n : Nat) :
    Core.Evaluates (value :: environment) store (spineCore n) (spineValue value n) store := by
  induction n with
  | zero => exact .unit
  | succ n ih => exact .pair (.var rfl) ih
private theorem spinePath (environment : Core.Environment) (value : Core.Value) (store : Core.Store) (n : Nat) :
    ∀ continuation, Core.Steps (4 * n + 1) ⟨.eval (spineCore n) (value :: environment), continuation, store⟩
      ⟨.ret (spineValue value n), continuation, store⟩ := by
  induction n with
  | zero => intro continuation; exact .cons .unit .refl
  | succ n ih =>
      intro continuation
      have path := Core.Steps.cons .enterPair (.cons (.var (index := 0) rfl) (.cons .enterPairRight
        ((ih (.pairApply value :: continuation)).trans (.cons .applyPair .refl))))
      simpa [spineCore, spineValue, Nat.mul_add, Nat.add_assoc] using path

theorem arbitrary_depth_and_types_keep_duplicate_first_match_and_exact_core
    (id : LocalId) (type hiddenType : Core.Ty) (suffix : Context) (n : Nat) :
    WellScoped (id :: id :: LocalScope.ids suffix) (spine id n) ∧
    Lowers (id :: id :: LocalScope.ids suffix) (spine id n) (spineCore n) ∧
    (spine id n).lower? (id :: id :: LocalScope.ids suffix) = some (spineCore n) ∧
    HasType ((id, type) :: (id, hiddenType) :: suffix) (spine id n) (spineType type n) ∧
    infer? ((id, type) :: (id, hiddenType) :: suffix) (spine id n) = some (spineType type n) ∧
    (spineCore n).LocalFragment :=
  ⟨spineScoped id _ n, spineLower id _ n, (spineLower id _ n).complete,
    spineTyped id _ type n, infer_complete (spineTyped id _ type n), (spineLower id [] n).localFragment⟩

theorem exact_product_typing_reflects_without_requiring_actual_values
    (id : LocalId) (type : Core.Ty) (suffix : Context) (n : Nat) :
    Core.HasType (type :: LocalScope.values suffix) (spineCore n) (spineType type n) ∧
    (HasType ((id, type) :: suffix) (spine id n) (spineType type n) ↔
      Core.HasType (type :: LocalScope.values suffix) (spineCore n) (spineType type n)) ∧
    HasType ((id, type) :: suffix) (spine id n) (spineType type n) := by
  have independent : Core.HasType (type :: LocalScope.values suffix) (spineCore n) (spineType type n) := by
    induction n with
    | zero => exact .unit
    | succ n ih => exact .pair (.var rfl) ih
  have lowered := spineLower id (LocalScope.ids suffix) n
  exact ⟨lowered.preserves_type (context := (id, type) :: suffix) (spineTyped id suffix type n),
    lowered.typing_iff (context := (id, type) :: suffix),
    lowered.reflects_type (context := (id, type) :: suffix) independent⟩

theorem arbitrary_raw_values_retain_both_stores_and_bidirectional_core_correspondence
    (id : LocalId) (value hidden result : Core.Value) (suffix : Environment) (store final : Core.Store) (n : Nat) :
    Evaluates ((id, value) :: (id, hidden) :: suffix) store (spine id n) (spineValue value n) store ∧
    Core.Evaluates (value :: hidden :: LocalScope.values suffix) store (spineCore n) (spineValue value n) store ∧
    (Evaluates ((id, value) :: (id, hidden) :: suffix) store (spine id n) result final ↔
      Core.Evaluates (value :: hidden :: LocalScope.values suffix) store (spineCore n) result final) ∧
    (Evaluates ((id, value) :: (id, hidden) :: suffix) store (spine id n) result final →
      result = spineValue value n ∧ final = store) := by
  have lowered := spineLower id (id :: LocalScope.ids suffix) n
  have evaluation := spineEval id ((id, hidden) :: suffix) value store n
  refine ⟨Evaluates.ofCore lowered (spineCoreEval _ value store n), evaluation.toCore lowered,
    lowered.evaluates_iff (environment := (id, value) :: (id, hidden) :: suffix), ?_⟩
  intro other
  exact ⟨(evaluation_deterministic other evaluation).1, other.store_eq⟩

theorem independently_counted_pairs_cost_four_per_node_under_any_outer_frames
    (id : LocalId) (value hidden : Core.Value) (suffix : Environment) (store : Core.Store)
    (n fuel : Nat) (continuation : List Core.Frame) :
    Lowers (id :: id :: LocalScope.ids suffix) (spine id n) (spineCore n) ∧
    Core.Steps (4 * n + 1) ⟨.eval (spineCore n) (value :: hidden :: LocalScope.values suffix), continuation, store⟩
      ⟨.ret (spineValue value n), continuation, store⟩ ∧
    (Core.runStateful fuel (Core.State.initial (spineCore n) (value :: hidden :: LocalScope.values suffix) store) =
      .done (spineValue value n) store ↔ 4 * n + 1 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (Core.State.initial (spineCore n) (value :: hidden :: LocalScope.values suffix) store) =
      .outOfFuel checkpoint) ↔ fuel < 4 * n + 1) :=
  ⟨spineLower id _ n, spinePath _ value store n continuation,
    (spinePath _ value store n []).runStateful_done_iff, (spinePath _ value store n []).runStateful_outOfFuel_iff⟩

theorem nominal_products_can_check_without_any_runtime_inhabitant (nominal : Core.DataTypeId) (n : Nat) :
    infer? [(ident 0, .namedData nominal)] (spine (ident 0) (n + 1)) = some (spineType (.namedData nominal) (n + 1)) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨infer_complete (spineTyped (ident 0) [] (.namedData nominal) _), ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem opaque_cells_closures_and_constructor_payloads_are_not_executed
    (location : Core.Location) (constructor : Core.ConstructorId) (payload captured : Core.Value)
    (store : Core.Store) (n : Nat) :
    Evaluates [(ident 0, .pair (.cellRef .word location)
      (.pair (.closure .word .bool (.var 99) [captured]) (.constructed constructor payload))),
      (ident 0, captured)] store (spine (ident 0) n)
      (spineValue (.pair (.cellRef .word location)
        (.pair (.closure .word .bool (.var 99) [captured]) (.constructed constructor payload))) n) store :=
  spineEval _ _ _ _ _

private def source : Expr := .pair (.letE (ident 1) (.var (ident 0)) (.var (ident 1))) (.var (ident 1))
private def core : Core.Expr := .pair (.letE (.var 0) (.var 0)) (.var 1)
private def scope : List LocalId := [ident 0, ident 1]
private def environment (left right : Core.Value) : Environment := [(ident 0, left), (ident 1, right)]
private theorem lowered : Lowers scope source core := .pair (.letE (.var .head) (.var .head)) (.var (.tail different .head))
private theorem typed (left right : Core.Ty) : HasType [(ident 0, left), (ident 1, right)] source (.product left right) :=
  .pair (.letE (.var .head) (.var .head)) (.var (.tail different .head))
private theorem evaluated (left right : Core.Value) (store : Core.Store) :
    Evaluates (environment left right) store source (.pair left right) store :=
  .pair (.letE (.var .head) (.var .head)) (.var (.tail different .head))
private theorem nestedPath (left right : Core.Value) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 8 ⟨.eval core [left, right], continuation, store⟩ ⟨.ret (.pair left right), continuation, store⟩ :=
  .cons .enterPair (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl)
    (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))))

theorem a_left_local_shadow_never_changes_the_original_right_environment
    (left right : Core.Value) (leftType rightType : Core.Ty) (store : Core.Store) (continuation : List Core.Frame) :
    WellScoped scope source ∧ Lowers scope source core ∧ HasType [(ident 0, leftType), (ident 1, rightType)] source (.product leftType rightType) ∧
    Evaluates (environment left right) store source (.pair left right) store ∧
    Core.Steps 8 ⟨.eval core [left, right], continuation, store⟩ ⟨.ret (.pair left right), continuation, store⟩ :=
  ⟨lowered.wellScoped, lowered, typed _ _, evaluated _ _ _, nestedPath _ _ _ _⟩

theorem a_swapped_same_typed_core_is_not_an_exact_lowering (type : Core.Ty) :
    Core.HasType [type, type] (.pair (.var 1) (.letE (.var 0) (.var 0))) (.product type type) ∧
    ¬ Lowers scope source (.pair (.var 1) (.letE (.var 0) (.var 0))) := by
  refine ⟨.pair (.var rfl) (.letE (.var rfl) (.var rfl)), ?_⟩
  intro other
  have impossible := lowered.deterministic other
  cases impossible

theorem structural_maps_need_no_injectivity_but_semantic_transport_does
    (first second mapping : LocalId → LocalId) (injective : Function.Injective mapping)
    (left right : Core.Value) (leftType rightType : Core.Ty) (store : Core.Store) :
    (source.renameIds first).renameIds second = source.renameIds (second ∘ first) ∧
    source.renameIds id = source ∧
    (source.renameIds mapping).lower? (scope.map mapping) = some core ∧
    infer? (LocalScope.mapIds mapping [(ident 0, leftType), (ident 1, rightType)]) (source.renameIds mapping) = some (.product leftType rightType) ∧
    (Evaluates (LocalScope.mapIds mapping (environment left right)) store (source.renameIds mapping) (.pair left right) store ↔
      Evaluates (environment left right) store source (.pair left right) store) ∧
    Evaluates (LocalScope.mapIds mapping (environment left right)) store (source.renameIds mapping) (.pair left right) store :=
  ⟨source.renameIds_comp first second, source.renameIds_id,
    (Expr.lower?_renameIds mapping injective source scope).trans lowered.complete,
    (infer?_renameIds mapping injective _ source).trans (infer_complete (typed _ _)),
    evaluates_renameIds_iff mapping injective, (evaluates_renameIds_iff mapping injective).mpr (evaluated _ _ _)⟩

theorem collapsing_two_identities_really_changes_the_ordered_pair (store : Core.Store) :
    Evaluates (environment (.bool true) (.bool false)) store source (.pair (.bool true) (.bool false)) store ∧
    Evaluates (LocalScope.mapIds (fun _ => ident 0) (environment (.bool true) (.bool false))) store
      (source.renameIds (fun _ => ident 0)) (.pair (.bool true) (.bool true)) store ∧
    ¬ Evaluates (LocalScope.mapIds (fun _ => ident 0) (environment (.bool true) (.bool false))) store
      (source.renameIds (fun _ => ident 0)) (.pair (.bool true) (.bool false)) store := by
  have collapsed : Evaluates (LocalScope.mapIds (fun _ => ident 0) (environment (.bool true) (.bool false))) store
      (source.renameIds (fun _ => ident 0)) (.pair (.bool true) (.bool true)) store :=
    .pair (.letE (.var .head) (.var .head)) (.var .head)
  refine ⟨evaluated _ _ _, collapsed, ?_⟩
  intro other
  have impossible := (evaluation_deterministic other collapsed).1
  cases impossible

private def retained : Expr := .pair (.letE (ident 2) (.var (ident 0)) (.var (ident 2))) (.var (ident 2))
private def retainedCore : Core.Expr := .pair (.letE (.var 1) (.var 0)) (.var 0)
theorem suffix_freshness_allows_the_inserted_identity_in_the_prefix_and_inner_binder
    (kept bound inserted result : Core.Value) (store final : Core.Store) :
    Lowers [ident 2, ident 2, ident 0] retained (retainedCore.weakenAt 1) ∧
    Evaluates [(ident 2, kept), (ident 2, inserted), (ident 0, bound)] store retained (.pair bound kept) store ∧
    (Evaluates [(ident 2, kept), (ident 2, inserted), (ident 0, bound)] store retained result final ↔
      Evaluates [(ident 2, kept), (ident 0, bound)] store retained result final) := by
  have fresh : ident 2 ∉ [ident 0] := by decide
  have original : Lowers [ident 2, ident 0] retained retainedCore :=
    .pair (.letE (.var (.tail (by decide) .head)) (.var .head)) (.var .head)
  have evaluation : Evaluates [(ident 2, kept), (ident 0, bound)] store retained (.pair bound kept) store :=
    .pair (.letE (.var (.tail (by decide) .head)) (.var .head)) (.var .head)
  exact ⟨Lowers.insert_fresh (kept := [ident 2]) fresh original,
    evaluation.insert_fresh (leading := [(ident 2, kept)]) fresh,
    original.wellScoped.evaluates_insert_fresh_iff (leading := [(ident 2, kept)])
      (suffix := [(ident 0, bound)]) fresh⟩

theorem fresh_head_insertion_preserves_static_and_actual_profiles_separately
    (id newId : LocalId) (different : newId ≠ id) (type insertedType : Core.Ty)
    (value inserted : Core.Value) (store : Core.Store) (n : Nat) :
    HasType [(newId, insertedType), (id, type)] (spine id n) (spineType type n) ∧
    (spine id n).lower? [newId, id] = ((spine id n).lower? [id]).map (fun core => core.weakenAt 0) ∧
    Evaluates [(newId, inserted), (id, value)] store (spine id n) (spineValue value n) store ∧
    (Evaluates [(newId, inserted), (id, value)] store (spine id n) (spineValue value n) store ↔
      Evaluates [(id, value)] store (spine id n) (spineValue value n) store) := by
  have fresh : newId ∉ [id] := by simp [different]
  exact ⟨(spineTyped id [] type n).weaken_fresh fresh insertedType,
    (spine id n).lower?_weaken_fresh (spineScoped id [] n) fresh,
    (spineEval id [] value store n).weaken_fresh fresh,
    (spineScoped id [] n).evaluates_weaken_fresh_iff (environment := [(id, value)]) fresh⟩

private def skipped : Expr := .pair (.var (ident 0)) (.ifE (.bool true) .unit (.var (ident 9)))
theorem raw_selected_pairs_can_succeed_while_whole_lowering_and_typing_fail
    (value : Core.Value) (store : Core.Store) (type : Core.Ty) :
    Evaluates [(ident 0, value)] store skipped (.pair value .unit) store ∧
    skipped.lower? [ident 0] = none ∧ infer? [(ident 0, type)] skipped = none ∧
    ¬ WellScoped [ident 0] skipped := by
  have missing : skipped.lower? [ident 0] = none := by decide
  exact ⟨.pair (.var .head) (.ifTrue .bool .unit), missing,
    by simp [infer?, LocalScope.ids, missing], Expr.lower?_eq_none_iff_not_wellScoped.mp missing⟩

theorem original_scoping_is_necessary_to_reflect_a_newly_enabled_pair
    (value : Core.Value) (store : Core.Store) :
    Evaluates [(ident 2, value)] store (.pair .unit (.var (ident 2))) (.pair .unit value) store ∧
    ¬ ∃ result final, Evaluates [] store (.pair .unit (.var (ident 2))) result final := by
  refine ⟨.pair .unit (.var .head), ?_⟩
  rintro ⟨result, final, evaluation⟩
  cases evaluation with
  | pair _ right => cases right with | var found => cases found

end Tests.ResolvedPair
end

section
-- leanmerge: from Solcore.Test.ResolvedPublicBoundary
set_option autoImplicit false

namespace Tests

example := @Solcore.Resolved.DeclarationId
example := @Solcore.Resolved.LocalId
example := @Solcore.Resolved.LocalScope
example := @Solcore.Resolved.LocalScope.ids
example := @Solcore.Resolved.LocalScope.values
example := @Solcore.Resolved.LocalScope.lookup?
example := @Solcore.Resolved.LocalScope.index?
example := @Solcore.Resolved.LocalScope.Lookup
example := @Solcore.Resolved.LocalScope.IndexOf
example := @Solcore.Resolved.LocalScope.lookup?_iff
example := @Solcore.Resolved.LocalScope.index?_iff
example := @Solcore.Resolved.LocalScope.Lookup.indexed
example := @Solcore.Resolved.LocalScope.lookup_of_indexed
example := @Solcore.Resolved.LocalScope.index_lookup
example := @Solcore.Resolved.LocalScope.Lookup.value_unique
example := @Solcore.Resolved.LocalScope.IndexOf.index_unique
example := @Solcore.Resolved.LocalScope.lookup_iff_getElem?
example := @Solcore.Resolved.LocalScope.IndexOf.getElem?
example := @Solcore.Resolved.LocalScope.IndexOf.lt_length
example := @Solcore.Resolved.LocalScope.Lookup.mem
example := @Solcore.Resolved.LocalScope.Lookup.of_mem_of_ids_nodup
example := @Solcore.Resolved.LocalScope.index?_eq_none_iff
example := @Solcore.Resolved.LocalScope.lookup?_eq_none_iff
example := @Solcore.Resolved.LocalScope.ids_length
example := @Solcore.Resolved.LocalScope.values_length
example := @Solcore.Resolved.Expr
example := @Solcore.Resolved.Expr.lower?
example := @Solcore.Resolved.Lowers
example := @Solcore.Resolved.Lowers.complete
example := @Solcore.Resolved.Expr.lower?_sound
example := @Solcore.Resolved.Expr.lower?_iff
example := @Solcore.Resolved.Lowers.deterministic
example := @Solcore.Resolved.Expr.lower?_eq_none_iff
example := @Solcore.Resolved.Context
example := @Solcore.Resolved.HasType
example := @Solcore.Resolved.infer?
example := @Solcore.Resolved.HasType.lowers
example := @Solcore.Resolved.Lowers.reflects_type
example := @Solcore.Resolved.Lowers.preserves_type
example := @Solcore.Resolved.Lowers.typing_iff
example := @Solcore.Resolved.infer_sound
example := @Solcore.Resolved.infer_complete
example := @Solcore.Resolved.typing_iff_infer
example := @Solcore.Resolved.typing_deterministic
example := @Solcore.Resolved.Environment
example := @Solcore.Resolved.Evaluates
example := @Solcore.Resolved.Evaluates.toCore
example := @Solcore.Resolved.Evaluates.ofCore
example := @Solcore.Resolved.Lowers.evaluates_iff
example := @Solcore.Resolved.Evaluates.store_eq
example := @Solcore.Resolved.evaluation_deterministic
example := @Solcore.Resolved.Lowers.run_done_sound
example := @Solcore.Resolved.Evaluates.run_has_sufficient_fuel
example := @Solcore.Resolved.Lowers.evaluates_iff_run_done
example := @Solcore.Resolved.HasType.closed_evaluates
example := @Solcore.Resolved.HasType.closed_run_has_sufficient_fuel
example := @Solcore.Resolved.Lowers.closed_run_never_faults

example := @Solcore.Resolved.WellScoped
example := @Solcore.Resolved.Lowers.wellScoped
example := @Solcore.Resolved.WellScoped.lowers
example := @Solcore.Resolved.wellScoped_iff_lowers
example := @Solcore.Resolved.Expr.lower?_eq_none_iff_not_wellScoped
example := @Solcore.Resolved.Expr.lower?_isSome_iff_wellScoped
example := @Solcore.Resolved.HasType.wellScoped
example := @Solcore.Resolved.Expr.lower?_var_eq_none_iff
example := @Solcore.Resolved.LocalScope.mapIds
example := @Solcore.Resolved.Expr.renameIds
example := @Solcore.Resolved.LocalScope.ids_mapIds
example := @Solcore.Resolved.LocalScope.values_mapIds
example := @Solcore.Resolved.LocalScope.index?_map
example := @Solcore.Resolved.LocalScope.lookup?_mapIds
example := @Solcore.Resolved.LocalScope.lookup_mapIds_iff
example := @Solcore.Resolved.LocalScope.indexOf_map_iff
example := @Solcore.Resolved.Expr.renameIds_id
example := @Solcore.Resolved.Expr.renameIds_comp
example := @Solcore.Resolved.Expr.lower?_renameIds
example := @Solcore.Resolved.lowers_renameIds_iff
example := @Solcore.Resolved.infer?_renameIds
example := @Solcore.Resolved.typing_renameIds_iff
example := @Solcore.Resolved.evaluates_renameIds_iff

example := @Solcore.Resolved.freshLocalId
example := @Solcore.Resolved.freshLocalId_owner
example := @Solcore.Resolved.freshLocalId_empty
example := @Solcore.Resolved.lt_freshLocalId_binderIndex
example := @Solcore.Resolved.freshLocalId_not_mem
example := @Solcore.Resolved.freshLocalId_cons_fresh_binderIndex
example := @Solcore.Resolved.freshLocalId_cons_fresh_ne
example := @Solcore.Resolved.freshLocalId_cons_of_ne_owner
example := @Solcore.Resolved.freshLocalId_eq_of_perm
example := @Solcore.Resolved.freshLocalId_map_owner
example := @Solcore.Resolved.LocalScope.IndexOf.insert_fresh
example := @Solcore.Resolved.Lowers.insert_fresh
example := @Solcore.Resolved.Lowers.weaken_fresh
example := @Solcore.Resolved.WellScoped.weaken_fresh
example := @Solcore.Resolved.Expr.lower?_weaken_fresh
example := @Solcore.Resolved.HasType.weaken_fresh
example := @Solcore.Resolved.LocalScope.Lookup.insert_fresh
example := @Solcore.Resolved.Evaluates.insert_fresh
example := @Solcore.Resolved.Evaluates.weaken_fresh
example := @Solcore.Resolved.Evaluates.weaken_allocated
example := @Solcore.Resolved.LocalScope.lookup_insert_fresh_iff
example := @Solcore.Resolved.Evaluates.reflect_insert_fresh
example := @Solcore.Resolved.WellScoped.evaluates_insert_fresh_iff
example := @Solcore.Resolved.WellScoped.evaluates_weaken_fresh_iff
example := @Solcore.Resolved.WellScoped.evaluates_weaken_allocated_iff
example := @Solcore.Resolved.Expr.wordLtWithIds
example := @Solcore.Resolved.Expr.renameIds_wordLtWithIds
example := @Solcore.Resolved.Lowers.wordLtWithIds
example := @Solcore.Resolved.HasType.wordLtWithIds
example := @Solcore.Resolved.Expr.lower?_wordLtWithIds
example := @Solcore.Resolved.infer_wordLtWithIds
example := @Solcore.Resolved.Evaluates.wordLtWithIds
example := @Solcore.Resolved.Evaluates.wordLtWithIds_inv
example := @Solcore.Resolved.wordLtWithIds_evaluates_iff
example := @Solcore.Resolved.Lowers.localFragment
example := @Solcore.Resolved.Expr.wordLt
example := @Solcore.Resolved.Lowers.wordLt
example := @Solcore.Resolved.HasType.wordLt
example := @Solcore.Resolved.Evaluates.wordLt
example := @Solcore.Resolved.WellScoped.wordLt

example := @Solcore.Resolved.Expr.pair
example := @Solcore.Resolved.Lowers.pair
example := @Solcore.Resolved.HasType.pair
example := @Solcore.Resolved.Evaluates.pair
example := @Solcore.Resolved.WellScoped.pair

end Tests
end

section
-- leanmerge: from Solcore.Test.ResolvedScopeProperties
/-! Concrete consumers separate local scope, type checking, and selected-branch
evaluation without imposing a source-name or identity-freshness policy. -/

set_option autoImplicit false

namespace Tests.ResolvedScope

open Solcore Solcore.Resolved

private def modulePath : Workspace.ModulePath := ⟨[⟨"Scope", by decide⟩], by decide⟩
private def binder : LocalId := ⟨⟨⟨.main, modulePath⟩, 0⟩, 0⟩
private def badUnary : Expr := .unary .boolNot .unit
private def selfInitializer : Expr := .letE binder (.var binder) .unit
private def boundBody : Expr := .letE binder .unit (.var binder)
private def skippedElse : Expr := .ifE (.bool true) .unit (.var binder)
private def skippedThen : Expr := .ifE (.bool false) (.var binder) .unit

theorem wellScoped_unary_can_be_ill_typed :
    WellScoped [] badUnary ∧ badUnary.lower? [] = some (.unary .boolNot .unit) ∧
      ¬ ∃ type, HasType [] badUnary type := by
  refine ⟨.unary .unit, (Lowers.unary Lowers.unit).complete, ?_⟩
  rintro ⟨type, typing⟩
  cases typing with
  | unary operand => cases operand

theorem self_initializer_out_of_scope :
    ¬ WellScoped [] selfInitializer ∧ selfInitializer.lower? [] = none := by
  have missing : ¬ WellScoped [] selfInitializer := by
    intro valid
    cases valid with
    | letE initializer _ =>
        cases initializer with
        | var member => simp at member
  exact ⟨missing, Expr.lower?_eq_none_iff_not_wellScoped.mpr missing⟩

theorem binder_available_in_body :
    WellScoped [] boundBody ∧ boundBody.lower? [] = some (.letE .unit (.var 0)) :=
  ⟨.letE .unit (.var (by simp)), (Lowers.letE Lowers.unit (.var .head)).complete⟩

theorem skipped_else_still_requires_scope (store : Core.Store) :
    Evaluates [] store skippedElse .unit store ∧ ¬ WellScoped [] skippedElse ∧
      skippedElse.lower? [] = none := by
  have missing : ¬ WellScoped [] skippedElse := by
    intro valid
    cases valid with
    | ifE _ _ branch =>
        cases branch with
        | var member => simp at member
  exact ⟨.ifTrue .bool .unit, missing, Expr.lower?_eq_none_iff_not_wellScoped.mpr missing⟩

theorem skipped_then_still_requires_scope (store : Core.Store) :
    Evaluates [] store skippedThen .unit store ∧ ¬ WellScoped [] skippedThen ∧
      skippedThen.lower? [] = none := by
  have missing : ¬ WellScoped [] skippedThen := by
    intro valid
    cases valid with
    | ifE _ branch _ =>
        cases branch with
        | var member => simp at member
  exact ⟨.ifFalse .bool .unit, missing, Expr.lower?_eq_none_iff_not_wellScoped.mpr missing⟩

theorem duplicate_scope_keeps_first_index :
    WellScoped [binder, binder] (.var binder) ∧
      (Expr.var binder).lower? [binder, binder] = some (.var 0) :=
  ⟨.var (by simp), (Lowers.var .head).complete⟩

end Tests.ResolvedScope
end

section
-- leanmerge: from Solcore.Test.ResolvedScopeReflectionProperties
/-! Fresh insertion reflects already-scoped evaluations, including references
under an existing binder with the inserted ID. Freshness alone is insufficient. -/

set_option autoImplicit false

namespace Tests.ResolvedScopeReflection

open Solcore Solcore.Resolved

private def modulePath : Workspace.ModulePath := ⟨[⟨"Reflect", by decide⟩], by decide⟩
private def owner : DeclarationId := ⟨⟨.main, modulePath⟩, 0⟩
private def oldId : LocalId := ⟨owner, 0⟩
private def environment : Environment := [(oldId, .bool false)]
private def fresh : LocalId := freshLocalId owner (LocalScope.ids environment)
private def nested : Expr :=
  .letE fresh (.bool true) (.letE oldId (.bool false) (.var fresh))

private theorem nested_scoped : WellScoped (LocalScope.ids environment) nested :=
  .letE .bool (.letE .bool (.var (by simp)))

theorem prefix_can_already_bind_the_inserted_id
    (keptValue addedValue value : Core.Value) (initialStore finalStore : Core.Store) :
    Evaluates ([(fresh, keptValue)] ++ (fresh, addedValue) :: environment)
      initialStore (.var fresh) value finalStore ↔
    Evaluates ([(fresh, keptValue)] ++ environment)
      initialStore (.var fresh) value finalStore := by
  have scopeValid : WellScoped
      (LocalScope.ids ([(fresh, keptValue)] ++ environment)) (.var fresh) :=
    .var (by simp [LocalScope.ids])
  exact scopeValid.evaluates_insert_fresh_iff
    (freshLocalId_not_mem owner (LocalScope.ids environment))

theorem nested_same_id_binder_has_exact_evaluation_iff
    (addedValue value : Core.Value) (initialStore finalStore : Core.Store) :
    Evaluates ((fresh, addedValue) :: environment) initialStore nested value finalStore ↔
      Evaluates environment initialStore nested value finalStore :=
  nested_scoped.evaluates_weaken_fresh_iff
    (freshLocalId_not_mem owner (LocalScope.ids environment))

theorem allocated_head_has_exact_evaluation_iff
    (addedValue value : Core.Value) (initialStore finalStore : Core.Store) :
    Evaluates ((freshLocalId owner (LocalScope.ids environment), addedValue) :: environment)
      initialStore (.var oldId) value finalStore ↔
    Evaluates environment initialStore (.var oldId) value finalStore := by
  have scopeValid : WellScoped (LocalScope.ids environment) (.var oldId) :=
    .var (by simp [LocalScope.ids, environment])
  exact scopeValid.evaluates_weaken_allocated_iff owner addedValue

/-- Reverse the independent extended evaluation; the inserted value is arbitrary
and the inner `fresh` binder continues to return true. -/
theorem nested_extended_evaluation_reflects (addedValue : Core.Value) (store : Core.Store) :
    Evaluates ((fresh, addedValue) :: environment) store nested (.bool true) store ∧
      Evaluates environment store nested (.bool true) store := by
  have extended : Evaluates ((fresh, addedValue) :: environment)
      store nested (.bool true) store :=
    .letE .bool (.letE .bool (.var (.tail (by decide) .head)))
  exact ⟨extended, extended.reflect_insert_fresh (leading := []) nested_scoped
    (freshLocalId_not_mem owner (LocalScope.ids environment))⟩

private def emptyFresh : LocalId := freshLocalId owner []

/-- The absent-ID premise holds, but the old expression is unscoped and has no
evaluation. Insertion creates a new evaluation, so reverse preservation fails. -/
theorem freshness_alone_does_not_reflect (addedValue : Core.Value) (store : Core.Store) :
    emptyFresh ∉ ([] : List LocalId) ∧ ¬ WellScoped [] (.var emptyFresh) ∧
    (∀ value finalStore, ¬ Evaluates [] store (.var emptyFresh) value finalStore) ∧
    Evaluates [(emptyFresh, addedValue)] store (.var emptyFresh) addedValue store := by
  refine ⟨freshLocalId_not_mem owner [], ?_, ?_, .var .head⟩
  · intro scopeValid
    cases scopeValid with
    | var member => cases member
  · intro value finalStore evaluation
    cases evaluation with
    | var found => cases found

end Tests.ResolvedScopeReflection
end

section
-- leanmerge: from Solcore.Test.ResolvedWordLessBoundary
/-! Raw ordered comparison evaluates only selected conditional branches. Whole
scope and typing checks remain stricter, and positional Core temporaries cannot
repair a missing named reference. Semantic renaming still needs injectivity. -/

set_option autoImplicit false

namespace Tests.ResolvedWordLessBoundary

open Solcore Solcore.Resolved

private def owner : DeclarationId := ⟨⟨.main, ⟨[⟨"LessBoundary", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : LocalId := ⟨owner, index⟩
private def one : Core.Word := Core.Word.ofNatModulo 1
private def scope : List LocalId := [ident 0, ident 1]
private def context : Context := [(ident 0, .word), (ident 1, .word)]
private def environment : Environment := [(ident 0, .word .zero), (ident 1, .word one)]
private theorem different : ident 0 ≠ ident 1 := by decide
private theorem fresh : ident 2 ∉ scope := by decide
private theorem ordered : decide (Core.Word.zero < one) = true := by decide

private def skippedMissing : Expr := .wordLt (.word .zero)
  (.ifE (.bool true) (.word one) (.var (ident 2)))
private def skippedBad : Expr := .wordLt (.word .zero)
  (.ifE (.bool true) (.word one) (.bool false))
private def skippedBadCore : Core.Expr := (Core.Expr.word .zero).wordLt
  (.ifE (.bool true) (.word one) (.bool false))
private def missingRight : Expr := .wordLt (.word .zero) (.var (ident 2))

private theorem missingRejected : skippedMissing.lower? scope = none := by decide
private theorem missingNotScoped : ¬WellScoped scope skippedMissing :=
  Expr.lower?_eq_none_iff_not_wellScoped.mp missingRejected
private theorem missingNotTyped (type : Core.Ty) : ¬HasType context skippedMissing type :=
  fun typing => missingNotScoped typing.wellScoped
private theorem missingEvaluated (store : Core.Store) :
    Evaluates environment store skippedMissing (.bool true) store := by
  simpa only [skippedMissing, ordered] using (Evaluates.wordLt .word (.ifTrue .bool .word) :
    Evaluates environment store skippedMissing (.bool (decide (Core.Word.zero < one))) store)
private theorem badLowered : Lowers scope skippedBad skippedBadCore :=
  .wordLt .word (.ifE .bool .word .bool)
private theorem badNotTyped (type : Core.Ty) : ¬HasType context skippedBad type := by
  intro typing
  cases typing with
  | wordLt _ right => cases right with
    | ifE _ _ wrong => cases wrong
private theorem badEvaluated (store : Core.Store) :
    Evaluates environment store skippedBad (.bool true) store := by
  simpa only [skippedBad, ordered] using (Evaluates.wordLt .word (.ifTrue .bool .word) :
    Evaluates environment store skippedBad (.bool (decide (Core.Word.zero < one))) store)
private theorem inferNone {expr : Expr} (rejected : ∀ type, ¬HasType context expr type) :
    infer? context expr = none := by
  cases inferred : infer? context expr with
  | none => rfl
  | some type => exact False.elim (rejected type (infer_sound inferred))

theorem skipped_unresolved_branch_allows_raw_success_but_rejects_whole_lowering_and_typing
    (store : Core.Store) :
    Evaluates environment store skippedMissing (.bool true) store ∧
    skippedMissing.lower? scope = none ∧ ¬WellScoped scope skippedMissing ∧
    (∀ type, ¬HasType context skippedMissing type) ∧ infer? context skippedMissing = none :=
  ⟨missingEvaluated store, missingRejected, missingNotScoped, missingNotTyped,
    inferNone missingNotTyped⟩

theorem raw_success_without_whole_scope_still_has_unique_value_and_unchanged_store
    (store finalStore : Core.Store) (value : Core.Value)
    (evaluation : Evaluates environment store skippedMissing value finalStore) :
    value = .bool true ∧ finalStore = store :=
  ⟨(evaluation_deterministic evaluation (missingEvaluated store)).1, evaluation.store_eq⟩

theorem skipped_wrong_type_lowers_and_runs_but_has_no_resolved_type
    (store : Core.Store) :
    Lowers scope skippedBad skippedBadCore ∧ skippedBad.lower? scope = some skippedBadCore ∧
    WellScoped scope skippedBad ∧ Evaluates environment store skippedBad (.bool true) store ∧
    Core.Evaluates [.word .zero, .word one] store skippedBadCore (.bool true) store ∧
    (∀ type, ¬HasType context skippedBad type) ∧ infer? context skippedBad = none :=
  ⟨badLowered, badLowered.complete, badLowered.wellScoped, badEvaluated store,
    (badEvaluated store).toCore badLowered, badNotTyped, inferNone badNotTyped⟩

private theorem noMissingEvaluation (store : Core.Store) :
    ¬∃ value finalStore, Evaluates environment store missingRight value finalStore := by
  rintro ⟨value, finalStore, evaluation⟩
  cases evaluation with
  | wordLt _ right => cases right with
    | var found =>
        have lookup := LocalScope.lookup?_iff.mpr found
        have absent : LocalScope.lookup? environment (ident 2) = none := by decide
        rw [absent] at lookup
        cases lookup

theorem positional_temporaries_do_not_enable_an_originally_missing_right_reference
    (store : Core.Store) :
    missingRight.lower? scope = none ∧ ¬WellScoped scope missingRight ∧
    (¬∃ value finalStore, Evaluates environment store missingRight value finalStore) := by
  have absent : missingRight.lower? scope = none := by decide
  exact ⟨absent, Expr.lower?_eq_none_iff_not_wellScoped.mp absent, noMissingEvaluation store⟩

theorem explicitly_inserting_the_missing_identity_cannot_be_reflected_without_original_scope
    (store : Core.Store) :
    ident 2 ∉ LocalScope.ids environment ∧
    Lowers (ident 2 :: scope) missingRight ((Core.Expr.word .zero).wordLt (.var 0)) ∧
    Evaluates ((ident 2, .word one) :: environment) store missingRight (.bool true) store ∧
    (¬∃ value finalStore, Evaluates environment store missingRight value finalStore) := by
  refine ⟨fresh, .wordLt .word (.var .head), ?_, noMissingEvaluation store⟩
  simpa only [missingRight, ordered] using (Evaluates.wordLt .word (.var .head) :
    Evaluates ((ident 2, .word one) :: environment) store missingRight
      (.bool (decide (Core.Word.zero < one))) store)

private def source : Expr := .wordLt (.var (ident 0)) (.var (ident 1))
private def merge : LocalId → LocalId := fun _ => ident 0
private theorem sourceEvaluated (store : Core.Store) :
    Evaluates environment store source (.bool true) store := by
  simpa only [source, ordered] using (Evaluates.wordLt (.var .head) (.var (.tail different .head)) :
    Evaluates environment store source (.bool (decide (Core.Word.zero < one))) store)
private theorem mergedEvaluated (store : Core.Store) :
    Evaluates (LocalScope.mapIds merge environment) store (source.renameIds merge) (.bool false) store := by
  simpa [source, Expr.renameIds] using (Evaluates.wordLt (.var .head) (.var .head) :
    Evaluates (LocalScope.mapIds merge environment) store (source.renameIds merge)
      (.bool (decide (Core.Word.zero < Core.Word.zero))) store)

theorem noninjective_renaming_obeys_structural_composition_but_changes_nearest_lookup_semantics
    (after : LocalId → LocalId) (store : Core.Store) :
    ¬Function.Injective merge ∧
    (source.renameIds merge).renameIds after = source.renameIds (after ∘ merge) ∧
    LocalScope.mapIds merge environment = [(ident 0, .word .zero), (ident 0, .word one)] ∧
    Lowers scope source ((Core.Expr.var 0).wordLt (.var 1)) ∧
    Lowers (scope.map merge) (source.renameIds merge) ((Core.Expr.var 0).wordLt (.var 0)) ∧
    Evaluates environment store source (.bool true) store ∧
    Evaluates (LocalScope.mapIds merge environment) store (source.renameIds merge) (.bool false) store ∧
    ¬Evaluates (LocalScope.mapIds merge environment) store (source.renameIds merge) (.bool true) store := by
  refine ⟨fun injective => different (injective rfl), source.renameIds_comp merge after, rfl,
    .wordLt (.var .head) (.var (.tail different .head)), .wordLt (.var .head) (.var .head),
    sourceEvaluated store, mergedEvaluated store, ?_⟩
  intro wrong
  have impossible := (evaluation_deterministic wrong (mergedEvaluated store)).1
  cases impossible

theorem fresh_insertion_and_reflection_through_word_less_need_scope_but_not_typing
    (inserted : Core.Value) (store finalStore : Core.Store) (value : Core.Value) :
    (∀ type, ¬HasType context skippedBad type) ∧
    Lowers (ident 2 :: scope) skippedBad (skippedBadCore.weakenAt 0) ∧
    Evaluates ((ident 2, inserted) :: environment) store skippedBad (.bool true) store ∧
    (Evaluates ((ident 2, inserted) :: environment) store skippedBad value finalStore ↔
      Evaluates environment store skippedBad value finalStore) :=
  ⟨badNotTyped, badLowered.weaken_fresh fresh, (badEvaluated store).weaken_fresh fresh,
    badLowered.wellScoped.evaluates_weaken_fresh_iff (environment := environment) fresh⟩

theorem injective_renaming_preserves_raw_success_even_when_whole_lowering_fails
    (mapping : LocalId → LocalId) (injective : Function.Injective mapping) (store : Core.Store) :
    (skippedMissing.renameIds mapping).lower? (scope.map mapping) = none ∧
    Evaluates (LocalScope.mapIds mapping environment) store (skippedMissing.renameIds mapping)
      (.bool true) store :=
  ⟨(Expr.lower?_renameIds mapping injective skippedMissing scope).trans missingRejected,
    (evaluates_renameIds_iff mapping injective).mpr (missingEvaluated store)⟩

end Tests.ResolvedWordLessBoundary
end

section
-- leanmerge: from Solcore.Test.ResolvedWordLessProperties
/-! Independent consumers use only the two original named operands. Positional
Core bindings introduce no LocalIds, even with duplicate identities, nested
shadowing, or comparison of one named value with itself. -/

set_option autoImplicit false

namespace Tests.ResolvedWordLess

open Solcore Solcore.Resolved

private def owner : DeclarationId := ⟨⟨.main, ⟨[⟨"IdentityFreeLess", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : LocalId := ⟨owner, index⟩
private def scope : List LocalId := [ident 0, ident 1]
private def context : Context := [(ident 0, .word), (ident 1, .word)]
private def environment (left right : Core.Word) : Environment := [(ident 0, .word left), (ident 1, .word right)]
private def source : Expr := .wordLt (.var (ident 0)) (.var (ident 1))
private def core : Core.Expr := .letE (.var 0) (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1)))
private theorem different : ident 0 ≠ ident 1 := by decide
private theorem fresh : ident 2 ∉ scope := by decide
private theorem scopeValid : WellScoped scope source := .wordLt (.var (by decide)) (.var (by decide))
private theorem lowered : Lowers scope source core := by
  simpa [source, core, Core.Expr.wordLt_expansion, Core.Expr.weakenAt] using
    (Lowers.wordLt (Lowers.var .head) (Lowers.var (.tail different .head)) :
      Lowers scope source ((Core.Expr.var 0).wordLt (.var 1)))
private theorem typed : HasType context source .bool := .wordLt (.var .head) (.var (.tail different .head))
private theorem evaluated (left right : Core.Word) (store : Core.Store) :
    Evaluates (environment left right) store source (.bool (decide (left < right))) store :=
  .wordLt (.var .head) (.var (.tail different .head))
private theorem coreEvaluated (left right : Core.Word) (store : Core.Store) :
    Core.Evaluates [.word left, .word right] store core (.bool (decide (left < right))) store :=
  .letE (.var rfl) (.letE (.var rfl) (.binary (.var rfl) (.var rfl) rfl))

theorem exact_lowering_keeps_both_original_positions_without_named_temporaries :
    source = .wordLt (.var (ident 0)) (.var (ident 1)) ∧ WellScoped scope source ∧
    Lowers scope source core ∧ source.lower? scope = some core ∧ core.LocalFragment ∧
    HasType context source .bool ∧ infer? context source = some .bool :=
  ⟨rfl, scopeValid, lowered, lowered.complete, lowered.localFragment, typed, infer_complete typed⟩

theorem independent_type_correspondence_preserves_and_reflects_bool :
    Core.HasType [.word, .word] core .bool ∧
    (HasType context source .bool ↔ Core.HasType [.word, .word] core .bool) ∧
    HasType context source .bool := by
  have independent : Core.HasType [.word, .word] core .bool :=
    .letE (.var rfl) (.letE (.var rfl) (.binary (.var rfl) (.var rfl)))
  exact ⟨lowered.preserves_type (context := context) typed,
    lowered.typing_iff (context := context), lowered.reflects_type (context := context) independent⟩

theorem arbitrary_actual_words_and_nonempty_stores_have_bidirectional_core_correspondence
    (left right : Core.Word) (store : Core.Store) :
    Evaluates (environment left right) (.unit :: store) source (.bool (decide (left < right))) (.unit :: store) ∧
    Core.Evaluates [.word left, .word right] (.unit :: store) core
      (.bool (decide (left < right))) (.unit :: store) ∧
    (Evaluates (environment left right) (.unit :: store) source (.bool (decide (left < right))) (.unit :: store) ↔
      Core.Evaluates [.word left, .word right] (.unit :: store) core
        (.bool (decide (left < right))) (.unit :: store)) :=
  ⟨Evaluates.ofCore lowered (coreEvaluated left right (.unit :: store)),
    (evaluated left right (.unit :: store)).toCore lowered,
    lowered.evaluates_iff (environment := environment left right)⟩

theorem equal_strict_and_reversed_unsigned_words_use_boolean_results
    (left right : Core.Word) (ordered : left < right) (store : Core.Store) :
    Evaluates (environment left left) store source (.bool false) store ∧
    Evaluates (environment left right) store source (.bool true) store ∧
    Evaluates (environment right left) store source (.bool false) store := by
  have reversed : ¬right < left := Nat.not_lt.mpr (Nat.le_of_lt ordered)
  exact ⟨by simpa using evaluated left left store, by simpa [ordered] using evaluated left right store,
    by simpa [reversed] using evaluated right left store⟩

theorem every_evaluation_recovers_the_unique_value_and_original_store
    (left right : Core.Word) (store finalStore : Core.Store) (value : Core.Value)
    (evaluation : Evaluates (environment left right) store source value finalStore) :
    value = .bool (decide (left < right)) ∧ finalStore = store :=
  ⟨(evaluation_deterministic evaluation (evaluated left right store)).1, evaluation.store_eq⟩

private def nestedRight : Expr := .letE (ident 0) (.var (ident 1))
  (.letE (ident 0) (.var (ident 0)) (.var (ident 0)))
private def nestedSource : Expr := .wordLt (.var (ident 0)) nestedRight
private def nestedCore : Core.Expr := .letE (.var 0)
  (.letE (.letE (.var 2) (.letE (.var 0) (.var 0))) (.binary .wordGt (.var 0) (.var 1)))

theorem repeated_inner_binders_shadow_an_outer_operand_without_capturing_it
    (left right : Core.Word) (store : Core.Store) :
    WellScoped scope nestedSource ∧ Lowers scope nestedSource nestedCore ∧
    HasType context nestedSource .bool ∧
    Evaluates (environment left right) store nestedSource (.bool (decide (left < right))) store := by
  have rightLowered : Lowers scope nestedRight (.letE (.var 1) (.letE (.var 0) (.var 0))) :=
    .letE (.var (.tail different .head)) (.letE (.var .head) (.var .head))
  have rightTyped : HasType context nestedRight .word :=
    .letE (.var (.tail different .head)) (.letE (.var .head) (.var .head))
  have rightEvaluated : Evaluates (environment left right) store nestedRight (.word right) store :=
    .letE (.var (.tail different .head)) (.letE (.var .head) (.var .head))
  refine ⟨.wordLt (.var (by decide)) (.letE (.var (by decide))
    (.letE (.var (by simp)) (.var (by simp)))), ?_, .wordLt (.var .head) rightTyped,
    .wordLt (.var .head) rightEvaluated⟩
  simpa [scope, nestedSource, nestedCore, Core.Expr.wordLt_expansion, Core.Expr.weakenAt] using
    Lowers.wordLt (Lowers.var .head) rightLowered

theorem duplicate_scope_entries_keep_nearest_lookup_in_both_original_operands
    (left hidden right : Core.Word) (store : Core.Store) :
    Lowers [ident 0, ident 0, ident 1] source
      ((Core.Expr.var 0).wordLt (.var 2)) ∧
    HasType [(ident 0, .word), (ident 0, .bool), (ident 1, .word)] source .bool ∧
    Evaluates [(ident 0, .word left), (ident 0, .word hidden), (ident 1, .word right)] store
      source (.bool (decide (left < right))) store :=
  ⟨.wordLt (.var .head) (.var (.tail different (.tail different .head))),
    .wordLt (.var .head) (.var (.tail different (.tail different .head))),
    .wordLt (.var .head) (.var (.tail different (.tail different .head)))⟩

theorem comparison_of_one_identity_with_itself_needs_no_freshness_or_distinctness
    (word hidden : Core.Word) (store : Core.Store) :
    WellScoped [ident 0, ident 0] (.wordLt (.var (ident 0)) (.var (ident 0))) ∧
    Lowers [ident 0, ident 0] (.wordLt (.var (ident 0)) (.var (ident 0)))
      ((Core.Expr.var 0).wordLt (.var 0)) ∧
    Evaluates [(ident 0, .word word), (ident 0, .word hidden)] store
      (.wordLt (.var (ident 0)) (.var (ident 0))) (.bool false) store := by
  refine ⟨.wordLt (.var (by simp)) (.var (by simp)), .wordLt (.var .head) (.var .head), ?_⟩
  simpa using (Evaluates.wordLt (.var .head) (.var .head) :
    Evaluates [(ident 0, .word word), (ident 0, .word hidden)] store
      (.wordLt (.var (ident 0)) (.var (ident 0))) (.bool (decide (word < word))) store)

theorem structural_renaming_laws_allow_arbitrary_even_collapsing_maps
    (first second : LocalId → LocalId) :
    source.renameIds first = .wordLt (.var (first (ident 0))) (.var (first (ident 1))) ∧
    source.renameIds id = source ∧
    (source.renameIds first).renameIds second = source.renameIds (second ∘ first) ∧
    source.renameIds (fun _ => ident 0) = .wordLt (.var (ident 0)) (.var (ident 0)) :=
  ⟨rfl, source.renameIds_id, source.renameIds_comp first second, rfl⟩

theorem injective_semantic_renaming_keeps_exact_core_type_and_ordered_evaluation
    (mapping : LocalId → LocalId) (injective : Function.Injective mapping)
    (left right : Core.Word) (store : Core.Store) :
    (source.renameIds mapping).lower? (scope.map mapping) = some core ∧
    HasType (LocalScope.mapIds mapping context) (source.renameIds mapping) .bool ∧
    Evaluates (LocalScope.mapIds mapping (environment left right)) store (source.renameIds mapping)
      (.bool (decide (left < right))) store :=
  ⟨(Expr.lower?_renameIds mapping injective source scope).trans lowered.complete,
    (typing_renameIds_iff mapping injective).mpr typed,
    (evaluates_renameIds_iff mapping injective).mpr (evaluated left right store)⟩

theorem fresh_outer_insertion_preserves_lowering_typing_and_reflects_evaluation
    (inserted : Core.Value) (insertedType : Core.Ty) (left right : Core.Word)
    (store finalStore : Core.Store) (value : Core.Value) :
    Lowers (ident 2 :: scope) source (core.weakenAt 0) ∧
    HasType ((ident 2, insertedType) :: context) source .bool ∧
    Evaluates ((ident 2, inserted) :: environment left right) store source (.bool (decide (left < right))) store ∧
    (Evaluates ((ident 2, inserted) :: environment left right) store source value finalStore ↔
      Evaluates (environment left right) store source value finalStore) :=
  ⟨lowered.weaken_fresh fresh, typed.weaken_fresh fresh insertedType,
    (evaluated left right store).weaken_fresh fresh,
    scopeValid.evaluates_weaken_fresh_iff (environment := environment left right) fresh⟩

theorem actual_lowered_operand_paths_cost_eleven_with_the_outer_continuation_retained
    (left right : Core.Word) (store : Core.Store) (continuation : List Core.Frame) :
    Lowers scope source core ∧ Core.Steps 11
      ⟨.eval core [.word left, .word right], continuation, store⟩
      ⟨.ret (.bool (decide (left < right))), continuation, store⟩ := by
  have leftPath : ∀ frames, Core.Steps 1 ⟨.eval (.var 0) [.word left, .word right], frames, store⟩
      ⟨.ret (.word left), frames, store⟩ := fun _ => .cons (.var rfl) .refl
  have rightPath : ∀ frames, Core.Steps 1 ⟨.eval (.var 1) [.word left, .word right], frames, store⟩
      ⟨.ret (.word right), frames, store⟩ := fun _ => .cons (.var rfl) .refl
  refine ⟨lowered, ?_⟩
  simpa [core, Core.Expr.wordLt_expansion, Core.Expr.weakenAt] using
    Frontend.CostStepComposition.wordLt_of_local_right leftPath rightPath .var continuation

end Tests.ResolvedWordLess
end

section
-- leanmerge: from Solcore.Test.ResolvedWordLessWithIdsProperties
/-! Explicit comparison temporaries are hygienic under precise premises. These
consumers do not add canonical source operators or infer freshness from names. -/

set_option autoImplicit false

namespace Tests.ResolvedWordLessWithIds

open Solcore Solcore.Resolved

private def owner : DeclarationId := ⟨⟨.main, ⟨[⟨"ExplicitLess", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : LocalId := ⟨owner, index⟩
private def scope : List LocalId := [ident 0, ident 1]
private def context : Context := [(ident 0, .word), (ident 1, .word)]
private def environment (left right : Core.Word) : Environment := [(ident 0, .word left), (ident 1, .word right)]
private def source : Expr := .wordLtWithIds (ident 2) (ident 0) (.var (ident 0)) (.var (ident 1))
private def core : Core.Expr := .letE (.var 0) (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1)))
private theorem distinctOuter : ident 0 ≠ ident 1 := by decide
private theorem distinctTemps : ident 0 ≠ ident 2 := by decide
private theorem fresh : ident 2 ∉ scope := by decide
private theorem leftEvaluation (left right : Core.Word) (store : Core.Store) :
    Evaluates (environment left right) store (.var (ident 0)) (.word left) store := .var .head
private theorem rightEvaluation (left right : Core.Word) (store : Core.Store) :
    Evaluates (environment left right) store (.var (ident 1)) (.word right) store := .var (.tail distinctOuter .head)
private theorem lowered : Lowers scope source core := by
  simpa [scope, source, Core.Expr.wordLt_expansion, Core.Expr.weakenAt, core] using
    (Lowers.var .head).wordLtWithIds (Lowers.var (.tail distinctOuter .head)) fresh distinctTemps
private theorem typed : HasType context source .bool :=
  (HasType.var .head).wordLtWithIds (HasType.var (.tail distinctOuter .head)) fresh distinctTemps
private theorem evaluated (left right : Core.Word) (store : Core.Store) :
    Evaluates (environment left right) store source (.bool (decide (left < right))) store :=
  (leftEvaluation left right store).wordLtWithIds (rightEvaluation left right store) fresh distinctTemps
private theorem rightScoped : WellScoped scope (.var (ident 1)) := .var (by decide)

theorem second_temporary_may_reuse_an_outer_id_with_exact_nested_core
    (left right : Core.Word) (store : Core.Store) :
    ident 0 ∈ scope ∧ Lowers scope source core ∧ HasType context source .bool ∧
    source.lower? scope = some core ∧ infer? context source = some .bool ∧
    Evaluates (environment left right) (.unit :: store) source (.bool (decide (left < right))) (.unit :: store) ∧
    Core.Evaluates [.word left, .word right] (.unit :: store) core
      (.bool (decide (left < right))) (.unit :: store) := by
  refine ⟨by decide, lowered, typed, ?_,
    infer_wordLtWithIds (infer_complete (HasType.var .head))
      (infer_complete (HasType.var (.tail distinctOuter .head))) fresh distinctTemps,
    evaluated left right (.unit :: store), (evaluated left right (.unit :: store)).toCore lowered⟩
  simpa [scope, source, Core.Expr.wordLt_expansion, Core.Expr.weakenAt, core] using
    Expr.lower?_wordLtWithIds (Lowers.var .head).complete
      (Lowers.var (.tail distinctOuter .head)).complete fresh distinctTemps

theorem reflection_recovers_original_ordered_children_and_intermediate_store
    (left right : Core.Word) (initialStore finalStore : Core.Store) (value : Core.Value)
    (evaluation : Evaluates (environment left right) initialStore source value finalStore) :
    (∃ leftWord rightWord middleStore,
      Evaluates (environment left right) initialStore (.var (ident 0)) (.word leftWord) middleStore ∧
      Evaluates (environment left right) middleStore (.var (ident 1)) (.word rightWord) finalStore ∧
      value = .bool (decide (leftWord < rightWord))) ∧
    (Evaluates (environment left right) initialStore source value finalStore ↔
      ∃ leftWord rightWord middleStore,
        Evaluates (environment left right) initialStore (.var (ident 0)) (.word leftWord) middleStore ∧
        Evaluates (environment left right) middleStore (.var (ident 1)) (.word rightWord) finalStore ∧
        value = .bool (decide (leftWord < rightWord))) :=
  ⟨evaluation.wordLtWithIds_inv rightScoped fresh distinctTemps,
    wordLtWithIds_evaluates_iff rightScoped fresh distinctTemps⟩

theorem equality_and_both_unsigned_directions_use_the_original_values
    (left right : Core.Word) (strict : left < right) (store : Core.Store) :
    Evaluates (environment left left) store source (.bool false) store ∧
    Evaluates (environment left right) store source (.bool true) store ∧
    Evaluates (environment right left) store source (.bool false) store := by
  have reverse : ¬right < left := Nat.not_lt.mpr (Nat.le_of_lt strict)
  exact ⟨by simpa using evaluated left left store, by simpa [strict] using evaluated left right store,
    by simpa [reverse] using evaluated right left store⟩

theorem injective_explicit_identity_changes_keep_the_same_core_and_meaning
    (mapping : LocalId → LocalId) (injective : Function.Injective mapping)
    (left right : Core.Word) (store : Core.Store) :
    source.renameIds mapping = Expr.wordLtWithIds (mapping (ident 2)) (mapping (ident 0))
      (.var (mapping (ident 0))) (.var (mapping (ident 1))) ∧
    (Expr.wordLtWithIds (mapping (ident 2)) (mapping (ident 0))
      (.var (mapping (ident 0))) (.var (mapping (ident 1)))).lower? (scope.map mapping) = some core ∧
    Evaluates (LocalScope.mapIds mapping (environment left right)) store
      (Expr.wordLtWithIds (mapping (ident 2)) (mapping (ident 0))
        (.var (mapping (ident 0))) (.var (mapping (ident 1)))) (.bool (decide (left < right))) store := by
  refine ⟨Expr.renameIds_wordLtWithIds _ _ _ _ _, ?_, ?_⟩
  · simpa only [source, Expr.renameIds_wordLtWithIds, Expr.renameIds] using
      (Expr.lower?_renameIds mapping injective source scope).trans lowered.complete
  · simpa only [source, Expr.renameIds_wordLtWithIds, Expr.renameIds] using
      (evaluates_renameIds_iff mapping injective).mpr (evaluated left right store)

private def shadowedRight : Expr := .letE (ident 2) (.var (ident 1)) (.var (ident 2))
private def shadowedSource := Expr.wordLtWithIds (ident 2) (ident 0) (.var (ident 0)) shadowedRight
private def shadowedCore : Core.Expr :=
  .letE (.var 0) (.letE (.letE (.var 2) (.var 0)) (.binary .wordGt (.var 0) (.var 1)))

theorem inner_operand_binders_can_shadow_the_first_temporary
    (left right : Core.Word) (store : Core.Store) :
    WellScoped scope shadowedRight ∧ Lowers scope shadowedSource shadowedCore ∧
    HasType context shadowedSource .bool ∧
    Evaluates (environment left right) store shadowedSource (.bool (decide (left < right))) store := by
  have rightLowered : Lowers scope shadowedRight (.letE (.var 1) (.var 0)) :=
    .letE (.var (.tail distinctOuter .head)) (.var .head)
  have rightTyped : HasType context shadowedRight .word :=
    .letE (.var (.tail distinctOuter .head)) (.var .head)
  have rightEvaluated : Evaluates (environment left right) store shadowedRight (.word right) store :=
    .letE (rightEvaluation left right store) (.var .head)
  refine ⟨.letE rightScoped (.var (by simp)), ?_,
    (HasType.var .head).wordLtWithIds rightTyped fresh distinctTemps,
    (leftEvaluation left right store).wordLtWithIds rightEvaluated fresh distinctTemps⟩
  simpa [scope, shadowedSource, Core.Expr.wordLt_expansion, Core.Expr.weakenAt, shadowedCore] using
    (Lowers.var .head).wordLtWithIds rightLowered fresh distinctTemps

private def one : Core.Word := Core.Word.ofNatModulo 1
private def zeroOne : Environment := environment .zero one
private theorem zeroOneEvaluatesTrue (store : Core.Store) :
    Evaluates zeroOne store source (.bool true) store := by
  have ordered : decide (Core.Word.zero < one) = true := by decide
  simpa only [zeroOne, ordered] using evaluated .zero one store

theorem equal_temporary_ids_compare_the_right_value_with_itself
    (store : Core.Store) :
    Evaluates zeroOne store source (.bool true) store ∧
    Evaluates zeroOne store (Expr.wordLtWithIds (ident 2) (ident 2)
      (.var (ident 0)) (.var (ident 1))) (.bool false) store := by
  refine ⟨zeroOneEvaluatesTrue store, ?_⟩
  exact .letE (leftEvaluation .zero one store)
    (.letE (.var (.tail (by decide) (.tail distinctOuter .head)))
      (.binary (.var .head) (.var .head) rfl))

theorem a_capturing_first_temporary_changes_an_existing_right_reference
    (store : Core.Store) :
    Evaluates zeroOne store (.var (ident 1)) (.word one) store ∧
    Evaluates ((ident 1, .word .zero) :: zeroOne) store (.var (ident 1)) (.word .zero) store ∧
    Evaluates zeroOne store (Expr.wordLtWithIds (ident 1) (ident 2)
      (.var (ident 0)) (.var (ident 1))) (.bool false) store ∧
    Evaluates zeroOne store source (.bool true) store := by
  refine ⟨rightEvaluation .zero one store, .var .head, ?_, ?_⟩
  · exact .letE (leftEvaluation .zero one store)
      (.letE (.var .head) (.binary (.var .head) (.var (.tail (by decide) .head)) rfl))
  · exact zeroOneEvaluatesTrue store

theorem newly_enabled_missing_right_reference_explains_the_reflection_scope_premise
    (store : Core.Store) :
    ident 2 ∉ LocalScope.ids zeroOne ∧ ident 3 ≠ ident 2 ∧
    Evaluates zeroOne store (Expr.wordLtWithIds (ident 2) (ident 3)
      (.word .zero) (.var (ident 2))) (.bool false) store ∧
    ¬∃ value finalStore, Evaluates zeroOne store (.var (ident 2)) value finalStore := by
  refine ⟨fresh, by decide, ?_, ?_⟩
  · exact .letE .word (.letE (.var .head)
      (.binary (.var .head) (.var (.tail (by decide) .head)) rfl))
  · rintro ⟨value, finalStore, evaluation⟩
    cases evaluation with
    | var found =>
      have lookup := LocalScope.lookup?_iff.mpr found
      have absent : LocalScope.lookup? zeroOne (ident 2) = none := by decide
      rw [absent] at lookup
      cases lookup

end Tests.ResolvedWordLessWithIds
end
