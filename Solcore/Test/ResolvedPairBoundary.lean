import Solcore.Resolved.Renaming
import Solcore.Resolved.Scope
import Solcore.Core.LocalFragment
import Solcore.Core.FuelResumptionProperties

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
