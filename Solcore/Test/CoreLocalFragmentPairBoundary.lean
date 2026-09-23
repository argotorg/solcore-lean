import Solcore.Core.LocalFragment
import Solcore.Core.FuelResumptionProperties

/-! Independent ordered pair certificates, explicit checkpoints and mathematical
thresholds. Insertion preserves endpoints, not captured machine environments. -/
set_option autoImplicit false
namespace Tests
open Solcore.Core

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def w (n : Nat) : Value := .word (Word.ofNatModulo n)
private def stores : List Store := [[], [.cellRef .word 40, .bool true, w 91]]
private structure Certificate (environment : Environment) (store : Store) where
  expr : Expr
  value : Value
  cost : Nat
  fragment : expr.LocalFragment
  evaluation : Evaluates environment store expr value store
  paths : ∀ continuation, Steps cost ⟨.eval expr environment, continuation, store⟩ ⟨.ret value, continuation, store⟩
private def reference (environment : Environment) (store : Store) (index : Nat) (value : Value)
    (found : environment[index]? = some value) : Certificate environment store :=
  ⟨.var index, value, 1, .var, .var found, fun _ => .cons (.var found) .refl⟩
private def pair {environment : Environment} {store : Store}
    (left right : Certificate environment store) : Certificate environment store where
  expr := .pair left.expr right.expr
  value := .pair left.value right.value
  cost := left.cost + right.cost + 3
  fragment := .pair left.fragment right.fragment
  evaluation := .pair left.evaluation right.evaluation
  paths := by
    intro continuation
    have enter : Steps 1 ⟨.eval (.pair left.expr right.expr) environment, continuation, store⟩
        ⟨.eval left.expr environment, .pairRight right.expr environment :: continuation, store⟩ := .cons .enterPair .refl
    have next : Steps 1 ⟨.ret left.value, .pairRight right.expr environment :: continuation, store⟩
        ⟨.eval right.expr environment, .pairApply left.value :: continuation, store⟩ := .cons .enterPairRight .refl
    have finish : Steps 1 ⟨.ret right.value, .pairApply left.value :: continuation, store⟩
        ⟨.ret (.pair left.value right.value), continuation, store⟩ := .cons .applyPair .refl
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      enter.trans ((left.paths _).trans (next.trans ((right.paths _).trans finish)))
private def binding {environment : Environment} {store : Store} (initializer : Certificate environment store)
    (body : Certificate (initializer.value :: environment) store) : Certificate environment store where
  expr := .letE initializer.expr body.expr
  value := body.value
  cost := initializer.cost + body.cost + 2
  fragment := .letE initializer.fragment body.fragment
  evaluation := .letE initializer.evaluation body.evaluation
  paths := by
    intro continuation
    have enter : Steps 1 ⟨.eval (.letE initializer.expr body.expr) environment, continuation, store⟩
        ⟨.eval initializer.expr environment, .letBody body.expr environment :: continuation, store⟩ := .cons .enterLet .refl
    have next : Steps 1 ⟨.ret initializer.value, .letBody body.expr environment :: continuation, store⟩
        ⟨.eval body.expr (initializer.value :: environment), continuation, store⟩ := .cons .bindLet .refl
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      enter.trans ((initializer.paths _).trans (next.trans (body.paths _)))
private def observe (result : StatefulRunResult) (remaining budget : Nat) (value : Value) (store : Store) : Bool :=
  match result with
  | .done actual final => decide (remaining ≤ budget ∧ actual = value ∧ final = store)
  | .outOfFuel checkpoint => decide (budget < remaining ∧ checkpoint.store = store)
  | .fault _ _ => false
private def execute (start : State) (value : Value) (store : Store) (cost : Nat)
    (path : Steps cost start (.final value store)) : IO Unit := do
  for fuel in List.range (cost + 3) do
    have _ := path.runStateful_done_iff (fuel := fuel)
    have _ := path.runStateful_outOfFuel_iff (fuel := fuel)
    assertTrue (observe (runStateful fuel start) cost fuel value store) "independent exact threshold/value/own store changed"
  for spent in List.range cost do
    match exhausted : runStateful spent start with
    | .outOfFuel checkpoint =>
        have _ := path.residual_of_outOfFuel exhausted
        for additional in List.range (cost - spent + 3) do
          have _ := runStateful_resume exhausted additional
          have _ := path.resumed_done_iff (additional := additional) exhausted
          have _ := path.resumed_outOfFuel_iff (additional := additional) exhausted
          assertTrue (observe (runStateful additional checkpoint) (cost - spent) additional value store)
            "genuine residual cost or own-store result changed"
        if 1 < cost - spent then
          match second : runStateful 1 checkpoint with
          | .outOfFuel next =>
              have _ := runStateful_resume second (cost - spent - 1)
              assertTrue (decide (runStateful (cost - spent - 1) next = .done value store)) "three-chunk completion lost its actual state"
          | _ => throw (IO.userError "second genuine checkpoint missing")
        if 0 < spent then
          assertTrue (match runStateful (cost - spent) start with | .outOfFuel _ => true | _ => false)
            "restart impersonated exact checkpoint resumption"
    | _ => throw (IO.userError "known terminating path lost a genuine checkpoint")
private def exercise (leading suffix : Environment) (inserted : Value) (store : Store)
    (certificate : Certificate (leading ++ suffix) store) (expectedCore : Expr) (expected : Value) (cost : Nat) : IO Unit := do
  assertTrue (decide (certificate.value = expected ∧ certificate.cost = cost ∧
    certificate.expr.weakenAt leading.length = expectedCore)) "independent Core/value/cost certificate changed"
  have _ := certificate.fragment.weakenAt leading.length
  have shiftedEval := (certificate.fragment.evaluates_insert_iff leading suffix inserted).mpr certificate.evaluation
  have _ := (certificate.fragment.evaluates_insert_iff leading suffix inserted).mp shiftedEval
  have _ := certificate.fragment.insertion_paths leading suffix inserted certificate.evaluation
  have shifted := certificate.fragment.steps_insert leading suffix inserted (certificate.paths []) []
  have _ := (certificate.fragment.steps_insert_iff leading suffix inserted).mp shifted
  have _ := (certificate.fragment.steps_insert_iff leading suffix inserted).mpr (certificate.paths [])
  if agrees : certificate.value = expected ∧ certificate.cost = cost then
    execute (.initial certificate.expr (leading ++ suffix) store) expected store cost
      (by simpa only [State.initial, State.final, agrees.1, agrees.2] using certificate.paths [])
    execute (.initial (certificate.expr.weakenAt leading.length) (leading ++ inserted :: suffix) store)
      expected store cost (by simpa only [State.initial, State.final, agrees.1, agrees.2] using shifted)
  else throw (IO.userError "independent value/cost evidence missing")
  for continuation in [[], [.unaryApply .wordNot], [.letBody (.var 0) [w 99]], [.firstApply]] do
    have _ := certificate.fragment.steps_insert leading suffix inserted (certificate.paths []) continuation
    have _ := certificate.fragment.steps_reflect_insert leading suffix inserted shifted continuation
    for (expr, environment) in [(certificate.expr, leading ++ suffix),
        (certificate.expr.weakenAt leading.length, leading ++ inserted :: suffix)] do
      let state : State := ⟨.eval expr environment, continuation, store⟩
      match continuation with
      | [.unaryApply .wordNot] =>
          assertTrue (decide (runStateful cost state = .fault (.invalidUnaryOperand .wordNot expected)
            ⟨.ret expected, continuation, store⟩)) "retained endpoint promised completion or unconditional exhaustion"
      | [.letBody (.var 0) _] =>
          assertTrue (decide (runStateful cost state = .outOfFuel ⟨.ret expected, continuation, store⟩ ∧
            runStateful (cost + 2) state = .done expected store)) "pending safe let frame was silently executed"
      | _ => pure ()
private def pairCheckpoints (x y inserted : Value) (store : Store) : IO Unit := do
  let original := State.initial (.pair (.var 0) (.var 1)) [x, y] store
  let shifted := State.initial (.pair (.var 1) (.var 2)) [inserted, x, y] store
  for (start, environment, leftIndex, rightIndex) in [(original, [x, y], 0, 1), (shifted, [inserted, x, y], 1, 2)] do
    assertTrue (decide (runStateful 1 start = .outOfFuel ⟨.eval (.var leftIndex) environment,
      [.pairRight (.var rightIndex) environment], store⟩)) "pair left entry or saved original environment changed"
    assertTrue (decide (runStateful 2 start = .outOfFuel ⟨.ret x, [.pairRight (.var rightIndex) environment], store⟩ ∧
      runStateful 3 start = .outOfFuel ⟨.eval (.var rightIndex) environment, [.pairApply x], store⟩ ∧
      runStateful 4 start = .outOfFuel ⟨.ret y, [.pairApply x], store⟩ ∧
      runStateful 5 start = .done (.pair x y) store)) "left-to-right pair frames or actual components changed"
    let localLeft := State.initial (.pair (.letE (.var leftIndex) (.var 0)) (.var rightIndex)) environment store
    assertTrue (decide (runStateful 4 localLeft = .outOfFuel
      ⟨.eval (.var 0) (x :: environment), [.pairRight (.var rightIndex) environment], store⟩ ∧
      runStateful 6 localLeft = .outOfFuel ⟨.eval (.var rightIndex) environment, [.pairApply x], store⟩ ∧
      runStateful 8 localLeft = .done (.pair x y) store)) "left-local binding leaked into the right operand's saved environment"
  assertTrue (decide (runStateful 2 original ≠ runStateful 2 shifted)) "own pairRight frames were equated across insertion"
private theorem nominalTyping (left right inserted : Ty) (definitions : DataEnvironment) :
    HasType [left, inserted, right] (.pair (.var 0) (.var 2)) (.product left right) definitions := by
  have fragment : (Expr.pair (.var 0) (.var 1)).LocalFragment := .pair .var .var
  have original : HasType [left, right] (.pair (.var 0) (.var 1)) (.product left right) definitions := .pair (.var rfl) (.var rfl)
  simpa [Expr.weakenAt] using (fragment.hasType_insert_iff [left] [right] inserted).mpr original
private def typingCases : IO Unit := do
  let fragment : (Expr.pair (.var 0) (.var 1)).LocalFragment := .pair .var .var
  for left in [Ty.word, .namedData ⟨91⟩, .function (.namedData ⟨999⟩) .unit] do
    for right in [Ty.bool, .namedData ⟨92⟩] do
      for definitions in [([] : DataEnvironment), [⟨[.namedData ⟨999⟩]⟩]] do
        have typed := nominalTyping left right (.namedData ⟨1000⟩) definitions
        have _ := (fragment.hasType_insert_iff [left] [right] (.namedData ⟨1000⟩)).mp (by simpa [Expr.weakenAt] using typed)
        have _ := fragment.infer_insert [left] [right] (.namedData ⟨1000⟩) definitions
        have original : HasType [left, right] (.pair (.var 0) (.var 1)) (.product left right) definitions := .pair (.var rfl) (.var rfl)
        have zero := original.weakenAt_zero_localFragment fragment .unit
        have _ := zero.reflect_weakenAt_zero_localFragment fragment
        have _ := (fragment.hasType_weaken_zero_iff [left, right] .unit).mp zero
        have _ := fragment.infer_weaken_zero [left, right] .unit definitions
        assertTrue (decide (infer? [left, .namedData ⟨1000⟩, right] (.pair (.var 0) (.var 2)) definitions =
          some (.product left right))) "nominal open typing acquired an inhabitant or data-WF premise"
private def invalidCases (store : Store) : IO Unit := do
  have _ : ¬ (Expr.pair .unit (.lambda .word .word (.var 0))).LocalFragment := by intro h; cases h with | pair _ bad => cases bad
  have _ : ¬ (Expr.pair (.apply (.var 0) .unit) .unit).LocalFragment := by intro h; cases h with | pair bad _ => cases bad
  have _ : ¬ (Expr.pair .unit (.loadCell (.var 0))).LocalFragment := by intro h; cases h with | pair _ bad => cases bad
  have _ : ¬ (Expr.pair (.first (.pair .unit .unit)) .unit).LocalFragment := by intro h; cases h with | pair bad _ => cases bad
  have _ : ¬ (Expr.ifE (.bool true) (.pair .unit .unit) (.pair .unit (.second (.pair .unit .unit)))).LocalFragment := by
    intro h; cases h with | ifE _ _ bad => cases bad with | pair _ bad => cases bad
  let unselected : Expr := .ifE (.bool true) (.pair .unit .unit) (.pair .unit (.second (.pair .unit .unit)))
  have _ : HasType [] unselected (.product .unit .unit) := .ifE .bool (.pair .unit .unit) (.pair .unit (.second (.pair .unit .unit)))
  have _ : Evaluates [] store unselected (.pair .unit .unit) store := .ifTrue .bool (.pair .unit .unit)
  assertTrue (decide (runStateful 8 (.initial unselected [] store) = .done (.pair .unit .unit) store))
    "unselected nonlocal child was confused with failed actual execution"
  let missing : Expr := .pair (.word (Word.ofNatModulo 9)) (.var 0)
  let missingFragment : missing.LocalFragment := .pair .word .var
  have _ := missingFragment.evaluates_insert_iff (initialStore := store) (finalStore := store) (value := .pair (w 9) .unit) [] [] (.cellRef .word 999)
  have _ := missingFragment.infer_insert [] [] (.cell .word)
  assertTrue (decide (infer? [] missing = none ∧ infer? [.cell .word] (missing.weakenAt 0) = none)) "inserted value filled an original missing reference"
  for (expr, env, index) in [(missing, ([] : Environment), 0), (missing.weakenAt 0, [.cellRef .word 999], 1)] do
    assertTrue (decide (runStateful 3 (.initial expr env store) = .fault (.unboundVariable index)
      ⟨.eval (.var index) env, [.pairApply (w 9)], store⟩)) "missing right child lost actual index or left value"
  let wrong : Expr := .unary .wordNot (.bool true)
  let wrongFragment : (Expr.pair wrong (.var 99)).LocalFragment := .pair (.unary .bool) .var
  have _ := wrongFragment.infer_insert [] [] .unit
  for (env, index) in [(([] : Environment), 99), ([Value.unit], 100)] do
    assertTrue (decide (runStateful 3 (.initial (.pair wrong (.var index)) env store) =
      .fault (.invalidUnaryOperand .wordNot (.bool true))
        ⟨.ret (.bool true), [.unaryApply .wordNot, .pairRight (.var index) env], store⟩)) "right failure overtook the wrong left operand"
    assertTrue (decide (runStateful 5 (.initial (.pair (.word (Word.ofNatModulo 9)) wrong) env store) =
      .fault (.invalidUnaryOperand .wordNot (.bool true))
        ⟨.ret (.bool true), [.unaryApply .wordNot, .pairApply (w 9)], store⟩)) "wrong right operand lost its evaluated left component"
  for (env, index) in [(([] : Environment), 0), ([Value.unit], 1)] do
    assertTrue (decide (runStateful 1 (.initial (.pair (.var index) wrong) env store) =
      .fault (.unboundVariable index) ⟨.eval (.var index) env, [.pairRight wrong env], store⟩))
      "missing left reference evaluated the wrong right primitive first"

def coreLocalFragmentPairBoundaryTests : IO Unit := do
  typingCases
  for store in stores do
    invalidCases store
    for (x, y) in [(w 9, w 2), (.cellRef .word 999, .closure .word .bool (.var 80) []),
        (.constructed ⟨⟨91⟩, 4⟩ (.pair .unit (w 7)), .unit)] do
      for inserted in [Value.bool false, .cellRef (.namedData ⟨777⟩) 500] do
        let first := reference [x, y] store 0 x rfl
        let second := reference [x, y] store 1 y rfl
        let simple := pair first second
        exercise [] [x, y] inserted store simple (.pair (.var 1) (.var 2)) (.pair x y) 5
        exercise [x] [y] inserted store simple (.pair (.var 0) (.var 2)) (.pair x y) 5
        exercise [x, y] [] inserted store simple (.pair (.var 0) (.var 1)) (.pair x y) 5
        let nested := pair first (pair second first)
        exercise [] [x, y] inserted store nested (.pair (.var 1) (.pair (.var 2) (.var 1))) (.pair x (.pair y x)) 9
        let localLeft := binding first (reference [x, x, y] store 0 x rfl)
        exercise [] [x, y] inserted store (pair localLeft second)
          (.pair (.letE (.var 1) (.var 0)) (.var 2)) (.pair x y) 8
        let tail := pair (reference [simple.value, x, y] store 0 simple.value rfl) (reference [simple.value, x, y] store 2 y rfl)
        exercise [] [x, y] inserted store (binding simple tail)
          (.letE (.pair (.var 1) (.var 2)) (.pair (.var 0) (.var 3))) (.pair (.pair x y) y) 12
        let retained := pair (reference [.bool true, .unit, x, y] store 0 (.bool true) rfl)
          (pair (reference [.bool true, .unit, x, y] store 2 x rfl) (reference [.bool true, .unit, x, y] store 3 y rfl))
        exercise [.bool true, .unit] [x, y] inserted store retained
          (.pair (.var 0) (.pair (.var 3) (.var 4))) (.pair (.bool true) (.pair x y)) 9
        have shiftedEval := simple.evaluation.weakenAt_zero_localFragment simple.fragment inserted
        have _ := shiftedEval.reflect_weakenAt_zero_localFragment simple.fragment
        have _ := (simple.fragment.evaluates_weaken_zero_iff [x, y] inserted).mp shiftedEval
        have shiftedPath := (simple.paths []).weakenAt_zero_localFragment simple.fragment inserted []
        have _ := shiftedPath.reflect_weakenAt_zero_localFragment simple.fragment []
        pairCheckpoints x y inserted store

end Tests
