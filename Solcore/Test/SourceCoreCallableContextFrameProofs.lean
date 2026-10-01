import Solcore.SourceSemantics.CoreLowering.CallableContextFrames

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Finite frame-helper laws with real lexical selectors, arbitrary closure
captures, effectful frame preparation, body allocation, nested restoration,
language failures and suspension before restoration. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableContextFrameProofs
open Solcore Solcore.Core Solcore.Frontend.SourceCoreCallableContextFrames
open Solcore.SourceSemantics.CoreLowering.CallableContextFrames
open Solcore.SourceSemantics.CoreLowering.DataEquality (Selects)

private def w (value : Nat) : Word := Word.ofNatModulo value
private def layout : Layout := ⟨⟨0⟩⟩
private def definitions : DataEnvironment := [layout.definition]
private def cyclic : Value := .closure .unit .unit (.var 0) [.cellRef (.function .unit .unit) 0]
private def before : Store := [cyclic, encode layout .empty, .word (w 99)]
private def environment : Environment := [.pair .unit (.cellRef layout.type 1), .cellRef .word 2]
private def context : Context := [.product .unit (.cell layout.type), .cell .word]
private def reference : Expr := .second (.var 0)
private def next : Expr :=
  .letE (.storeCell reference (named layout (w 13))) (named layout (w 3))
private def body (failure : Bool) : Expr :=
  .letE (.newCell .word (.word (w 42)))
    (.letE (.storeCell (.var 2) (.word (w 7)))
      (.letE (.storeCell (.second (.var 2)) (named layout (w 88)))
        (if failure then LanguageResult.failure .word (.word (w 23))
         else LanguageResult.success (.loadCell (.var 2)))))
private def expected (failure : Bool) : Value :=
  if failure then .inLeft .word (.word (w 23)) else .inRight .word (.word (w 42))
private def after : Store := [cyclic, encode layout .empty, .word (w 7), .word (w 42)]

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private theorem selected : Selects environment reference (.cellRef layout.type 1) := .second (.var rfl)

example : RuntimeStoreHasTypes [.function .unit .unit, layout.type, .word] before definitions := by
  constructor
  · rfl
  · intro index type found
    cases index with
    | zero => cases found; exact ⟨cyclic, rfl, .closure (.cons (.cellRef rfl) .nil) (.var rfl)⟩
    | succ index =>
      cases index with
      | zero => cases found; exact ⟨_, rfl, encode_runtime_typed _ ⟨rfl⟩ .empty⟩
      | succ index =>
        cases index with
        | zero => cases found; exact ⟨_, rfl, .word⟩
        | succ index => cases found

/-- An arbitrary resulting closure really captures the administrative values.
No equality with an unshifted body evaluation is asserted. -/
example (outer : Environment) (saved : Value) (store : Store)
    (readable : store.read? 0 = some saved) :
    Evaluates (.cellRef .unit 0 :: outer) store
      (withFrame (.var 0) .unit (.lambda .unit .unit (.var 0)))
      (.closure .unit .unit (.var 0) (.unit :: saved :: .cellRef .unit 0 :: outer))
      ((store.set 0 .unit).set 0 saved) :=
  withFrame_evaluates (nextStore := store) (installedValue := .unit) (.var rfl) readable
    (by simpa [Expr.weakenAt] using (Evaluates.unit (environment := saved :: .cellRef .unit 0 :: outer) (store := store)))
    (by simpa [Expr.weakenAt] using (Evaluates.lambda (environment := .unit :: saved :: .cellRef .unit 0 :: outer)
      (store := store.set 0 .unit) (parameterType := .unit) (resultType := .unit) (body := .var 0)))

example {result : Value} {store : Store} {fuel : Nat}
    (done : runStateful fuel (.initial (withFrame reference next (body true)) environment before) = .done result store) :
    store.read? 1 = some (encode layout .empty) :=
  (withFrame_restores selected rfl (runStateful_evaluation_sound done)).1

example {result : Value} {store : Store}
    (done : ∃ fuel, runStateful fuel (.initial (withFrame reference next (body false)) environment before) = .done result store) :
    ∃ installed nextStore bodyStore,
      Evaluates (encode layout .empty :: environment) before (next.weakenAt 0) installed nextStore ∧
      Evaluates (.unit :: encode layout .empty :: environment) (nextStore.set 1 installed)
        (((body false).weakenAt 0).weakenAt 0) result bodyStore ∧
      store = bodyStore.set 1 (encode layout .empty) :=
  (withFrame_run_done_iff selected rfl).mp done

private def scopedCases : IO Unit := do
  for failure in [false, true] do
    let expression := withFrame reference next (body failure)
    assertTrue (infer? context expression definitions == some (LanguageResult.resultType .word))
      "actual selector/temporary environment failed Core checking"
    match runStateful 10000 (.initial expression environment before) with
    | .done result store =>
      assertTrue (result == expected failure && store == after) "finite restoration changed body effects/result"
    | result => throw (IO.userError s!"finite context helper did not finish: {reprStr result}")
    let mut state := State.initial expression environment before
    let mut sawPrepared := false
    let mut sawInstalled := false
    let mut sawBodyWrite := false
    let mut completed := false
    for _ in List.range 500 do
      match runStateful 1 state with
      | .outOfFuel checkpoint =>
        sawPrepared := sawPrepared || checkpoint.store.read? 1 == some (encode layout (.named (w 13)))
        sawInstalled := sawInstalled || checkpoint.store.read? 1 == some (encode layout (.named (w 3)))
        sawBodyWrite := sawBodyWrite || checkpoint.store.read? 1 == some (encode layout (.named (w 88)))
        state := checkpoint
      | .done result store =>
        assertTrue (result == expected failure && store == after) "single-step resume lost pending restoration"
        completed := true
        break
      | .fault fault _ => throw (IO.userError s!"typed frame helper faulted: {reprStr fault}")
    assertTrue (completed && sawPrepared && sawInstalled && sawBodyWrite)
      "checkpoints failed to retain actual non-restored context states"

private def nested : IO Unit := do
  let inner := withFrame reference (named layout (w 2)) (LanguageResult.failure .word (.word (w 8)))
  let middle := .letE inner (.pair (.var 0) (.loadCell (reference.weakenAt 0)))
  let expression := withFrame reference (named layout (w 1)) middle
  let expectedType := .product (LanguageResult.resultType .word) layout.type
  assertTrue (infer? context expression definitions == some expectedType) "nested restoration is not typed"
  match runStateful 10000 (.initial expression environment before) with
  | .done result store =>
    assertTrue (result == .pair (.inLeft .word (.word (w 8))) (encode layout (.named (w 1))))
      "inner failure restored the outer caller instead of its saved lexical frame"
    assertTrue (store == before) "outer restoration lost original frame or cyclic administrative cell"
  | result => throw (IO.userError s!"nested frame execution did not finish: {reprStr result}")

private def selectedCases : IO Unit := do
  let captured : ContextFrame := .view (w 41) (w 5) (.lambda (w 17) (.named (w 3)))
  for current in ([.empty, .named (w 99), .lambda (w 99) .empty,
      .view (w 7) (w 11) (.view (w 8) (w 11) .empty), .view (w 7) (w 12) .empty] : List ContextFrame) do
    let env := [Value.pair (encode layout captured) (encode layout current)]
    let expression := lambdaFrame layout (w 11) (.first (.var 0)) (.second (.var 0))
    assertTrue (infer? [.product layout.type layout.type] expression definitions == some layout.type)
      "recursive encoded frame selection was not typed"
    match runStateful 10000 (.initial expression env before) with
    | .done value store =>
      assertTrue (value == encode layout (selectedFrame (w 11) captured current) && store == before)
        "frame selection retained dynamic caller ancestry or changed the store"
    | result => throw (IO.userError s!"encoded frame selection did not finish: {reprStr result}")

example (captured current : ContextFrame) (store : Store) :
    Evaluates [Value.pair (encode layout captured) (encode layout current)] store
      (lambdaFrame layout (w 11) (.first (.var 0)) (.second (.var 0)))
      (encode layout (selectedFrame (w 11) captured current)) store :=
  lambdaFrame_evaluates _ (.first (.var rfl)) (.second (.var rfl)) _

def run : IO Unit := do
  scopedCases
  nested
  selectedCases
  IO.println "finite context restoration/reflection, cyclic stores, exact captures and pending resume GREEN"
end Tests.SourceCoreCallableContextFrameProofs
