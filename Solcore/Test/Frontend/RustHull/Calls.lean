import Solcore.Frontend.RustHull.Semantics.Layers
import Solcore.Frontend.RustHull.ContractCallTheorems
import Solcore.Frontend.RustHull.Effects
import Solcore.Core.Machine
import Solcore.Frontend.RustHull.Semantics.Frames
import Solcore.Frontend.RustHull.Correspondence
import Solcore.Frontend.RustHull.Internal.CallLayout
import Solcore.Frontend.RustHull.ContractCodeTheorems
import Solcore.Frontend.RustHull.Internal.TerminationLayers
import Solcore.Frontend.RustHull.ContractStateTheorems
import Solcore.Test.Frontend.RustHull.Effects

/-!
# Hull call tests

Calls through the actual dispatcher: call modes, root, child and nested child calls, return data, reverts,
faults and termination.
-/

section
-- leanmerge: from Solcore.Test.RustHullCallCorrespondence
/-! Empty-account calls use the actual dispatcher, including balance transfer,
rollback, static checks, memory expansion, and public resumption. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullCallCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | ordinary | staticCall | transfer | insufficient | incomplete | staticValue | stipend | inputOverflow | outputOverflow
  deriving DecidableEq, Repr
private abbrev w := Core.Word.ofNatModulo
private def maximum := "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def static (scenario : Scenario) : Bool := scenario = .staticValue
def context (scenario : Scenario) : Contract.Context :=
  {balance := w 10, completeWorld := scenario != .incomplete, isStatic := static scenario}
def operation (scenario : Scenario) : RuntimeCallEffectsSemantics.Operation :=
  if scenario = .staticCall then .staticCall else .ordinary
def valueText : Scenario → String
  | .transfer | .incomplete | .staticValue | .stipend => "3"
  | .insufficient => "11"
  | _ => "0"
def value (scenario : Scenario) : Core.Word := match scenario with
  | .transfer | .incomplete | .staticValue | .stipend => w 3
  | .insufficient => w 11
  | _ => w 0
def gas (scenario : Scenario) : Core.Word := if scenario = .stipend then Core.Word.maximum else w 100
def inputOffset (scenario : Scenario) : Core.Word := if scenario = .inputOverflow then Core.Word.maximum else w 1
def outputOffset (scenario : Scenario) : Core.Word := if scenario = .outputOverflow then Core.Word.maximum else w 31
def seed : Expr := call .unit "mstore8" [word "1", word "171"]
def storageWrite (scenario : Scenario) : Expr :=
  if static scenario then call .word "msize" [] else call .unit "sstore" [word "7", word "42"]
def event (scenario : Scenario) : Expr :=
  if static scenario then call .word "msize" [] else call .unit "log0" [word "1", word "1"]
def invoked (scenario : Scenario) : Expr :=
  let gas := word (if scenario = .stipend then maximum else "100")
  let tail := [word (if scenario = .inputOverflow then maximum else "1"), word "1",
    word (if scenario = .outputOverflow then maximum else "31"), word "2"]
  if scenario = .staticCall then call .word "staticcall" ([gas, word "100"] ++ tail)
  else call .word "call" ([gas, word "100", word (valueText scenario)] ++ tail)
def stored (scenario : Scenario) : Expr := call .unit "mstore8" [word "2", invoked scenario]
def returned : Expr := call .unit "return" [word "1", word "2"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression seed, expression (storageWrite scenario), expression (event scenario),
    expression (stored scenario), expression returned], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Calls" (code scenario) []]}
abbrev SourceState := Semantics.State RuntimeCallEffectsSemantics.State

def initial (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], ⟨⟨ContractCodeCorrespondence.contextInitialState none object (Contract.normalizeContext (context scenario)), []⟩, w 0⟩⟩
def withMemory (state : SourceState) (memory : MemorySemantics.State) : SourceState :=
  ⟨[], {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime
    {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory})}⟩
def seeded : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 1) (w 171)).2
def memoryWritten (object : Contract.CompiledObject) (scenario : Scenario) : SourceState := withMemory (initial object scenario) seeded

def storageWritten (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  if static scenario then memoryWritten object scenario else
    let state := (memoryWritten object scenario).external
    let runtime := state.runtime.runtime.runtime.runtime.runtime
    ⟨[], {state with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.runtime
      {runtime with storage := (StorageSemantics.store runtime.storage (w 7) (w 42) false).2})}⟩
def loggedWords : LogsSemantics.Words :=
  [(w 0, w 0), (w 1, w 0), (w 2, w 1), (w 3, LogsSemantics.paddedWord seeded.words (w 1) (w 1))]
def logged (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  if static scenario then storageWritten object scenario else
    let state := (storageWritten object scenario).external
    let old := RuntimeLogEffectsSemantics.logsState state.runtime.runtime.runtime
    ⟨[], {state with runtime := {state.runtime with runtime := {state.runtime.runtime with
      runtime := RuntimeLogEffectsSemantics.withLogs state.runtime.runtime.runtime {old with words := loggedWords, cursor := w 4}}}}⟩
def arguments (object : Contract.CompiledObject) (scenario : Scenario) : CallTransportSemantics.Arguments :=
  RuntimeCallEffectsSemantics.arguments (operation scenario) (logged object scenario).external
    (gas scenario) (w 100) (value scenario) (inputOffset scenario) (w 1) (outputOffset scenario) (w 2)
def input : MemorySemantics.State :=
  ⟨MemoryCopySemantics.written [] (w 0) (w 1) (MemoryCopySemantics.copiedWord seeded.words (w 1) (w 1)), w 32⟩
def sharedAfter (object : Contract.CompiledObject) (scenario : Scenario) : AccountCallSemantics.Shared :=
  let old := RuntimeCallEffectsSemantics.shared (logged object scenario).external
  if scenario = .transfer then {old with balances := [(w 0, w 7), (w 100, w 3)]} else old
def nextTransport : CallTransportSemantics.State := ⟨{seeded with size := w 64}, [], w 0⟩
def callResult : Scenario → Semantics.Result Semantics.Value
  | .incomplete => .fault (.language (w 7))
  | .staticValue => .fault (.language Core.Word.maximum)
  | .stipend => .fault (.language (w 13))
  | .inputOverflow | .outputOverflow => .fault (.language (w 6))
  | .insufficient => .value (.word (w 0))
  | _ => .value (.word (w 1))
def afterCall (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := (logged object scenario).external
  match scenario with
  | .staticValue => ⟨[], (RuntimeCallEffectsSemantics.invalid state).2⟩
  | .stipend => logged object scenario
  | .inputOverflow | .outputOverflow => ⟨[], RuntimeCallEffectsSemantics.withTransport state
      (RuntimeCallEffectsSemantics.transport state) (RuntimeCallEffectsSemantics.shared state)⟩
  | _ => ⟨[], RuntimeCallEffectsSemantics.withTransport state nextTransport (sharedAfter object scenario)⟩
def afterStore (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  match callResult scenario with
  | .fault _ => afterCall object scenario
  | .value (.word success) => withMemory (afterCall object scenario)
      (MemorySemantics.mstore8 nextTransport.memory (w 2) success).2
  | _ => afterCall object scenario
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  match callResult scenario with
  | .fault _ => afterStore object scenario
  | .value _ =>
      let state := (afterStore object scenario).external
      ⟨[], {state with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.runtime
        (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 1 (w 1) (w 2)).2)}⟩
def result (scenario : Scenario) : Semantics.Result Semantics.Value :=
  match callResult scenario with
  | .fault fault => .fault fault
  | .value _ => .fault (.language Core.Word.maximum)

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] seed
      (initial object scenario) (.value .unit) (memoryWritten object scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem storage_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] (storageWrite scenario)
      (memoryWritten object scenario) (if static scenario then .value (.word (w 32)) else .value .unit) (storageWritten object scenario) := by
  cases scenario
  all_goals first
    | apply Semantics.EvalExpr.call rfl .nil
      exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))
    | apply Semantics.EvalExpr.call rfl
      · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "42") rfl) .nil)
      · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem event_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] (event scenario)
      (storageWritten object scenario) (if static scenario then .value (.word (w 32)) else .value .unit) (logged object scenario) := by
  cases scenario
  all_goals first
    | apply Semantics.EvalExpr.call rfl .nil
      exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))
    | apply Semantics.EvalExpr.call rfl
      · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) .nil)
      · apply Semantics.EvalCall.external (by rfl) rfl
        apply RuntimeCallEffectsSemantics.Builtin.runtime
        apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
        apply RuntimeCodeEffectsSemantics.Builtin.runtime
        apply RuntimeAccountEffectsSemantics.Builtin.runtime
        apply RuntimeHashEffectsSemantics.Builtin.runtime
        apply RuntimeCopyEffectsSemantics.Builtin.runtime
        apply RuntimeFullEffectsSemantics.Builtin.runtime
        apply RuntimeLogEffectsSemantics.Builtin.logs
        apply LogsSemantics.Builtin.log .log0 .unit (w 1) (w 1) [] rfl
        apply LogsSemantics.Execute.writable rfl
        apply LogsSemantics.Append.done (size := w 32) (words := loggedWords)
        · decide +kernel
        · change ¬w 0 > LogsSemantics.nextCursor (w 0) (w 1) []
          decide +kernel
        · change MemorySemantics.touchSize? seeded.size (w 1) (w 1) = some (w 32)
          decide +kernel
        · apply LogsSemantics.Copy.step (by decide +kernel)
          exact .empty _ _ _

private theorem input_copied :
    MemoryCopySemantics.From seeded.words (w 0) (w 1) (w 1) {} (.value .unit) input := by
  apply MemoryCopySemantics.From.done (by decide +kernel)
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  change MemoryCopySemantics.Copy _ _ _ ((w 1).sub (w 1)) input.words input.words
  rw [show (w 1).sub (w 1) = Core.Word.zero from by decide +kernel]
  exact .empty _ _ _ _

private theorem transfer_balances :
    AccountCallSemantics.transfer (w 0) (w 100) (w 3) [(w 0, w 10)] = .ok [(w 0, w 7), (w 100, w 3)] := by
  have computed : (AccountCallSemantics.transfer (w 0) (w 100) (w 3) [(w 0, w 10)]).toOption =
      some [(w 0, w 7), (w 100, w 3)] := by decide +kernel
  cases found : AccountCallSemantics.transfer (w 0) (w 100) (w 3) [(w 0, w 10)] with
  | error error => simp [found, Except.toOption] at computed
  | ok entries => exact congrArg Except.ok (Option.some.inj (by simpa only [found, Except.toOption] using computed))

private theorem invoked_source (object : Contract.CompiledObject) (scenario : Scenario) :
    RuntimeCallEffectsSemantics.Call (fun _ => AccountCallSemantics.noChildren) (operation scenario)
      (gas scenario) (w 100) (value scenario) (inputOffset scenario) (w 1) (outputOffset scenario) (w 2)
      (logged object scenario).external (callResult scenario) (afterCall object scenario).external := by
  cases scenario
  case staticValue => exact .staticValue _ rfl rfl (by decide +kernel)
  case stipend => exact .gasOverflow _ rfl rfl (by decide +kernel) (by decide +kernel)
  case inputOverflow =>
    apply RuntimeCallEffectsSemantics.Call.invoked (by exact .inr (.inl rfl)) (by intros _ nonzero; exact False.elim (nonzero rfl))
    exact .inputOverflow _ _ (by change MemorySemantics.touchSize? seeded.size Core.Word.maximum (w 1) = none; decide +kernel)
  case outputOverflow =>
    apply RuntimeCallEffectsSemantics.Call.invoked (by exact .inr (.inl rfl)) (by intros _ nonzero; exact False.elim (nonzero rfl))
    apply CallTransportSemantics.Execute.outputOverflow (inputSize := w 32)
    · change MemorySemantics.touchSize? seeded.size (w 1) (w 1) = some (w 32)
      decide +kernel
    · change MemorySemantics.touchSize? (w 32) Core.Word.maximum (w 2) = none
      decide +kernel
  all_goals
    apply RuntimeCallEffectsSemantics.Call.invoked
    · first | exact .inl rfl | exact .inr (.inr rfl)
    · intros ordinary nonzero
      decide +kernel
    apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 64)
    · change MemorySemantics.touchSize? seeded.size (w 1) (w 1) = some (w 32)
      decide +kernel
    · change MemorySemantics.touchSize? (w 32) (w 31) (w 2) = some (w 64)
      decide +kernel
  case ordinary.executed.dispatched =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := AccountCallSemantics.emptyResponse true) (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · apply AccountCallSemantics.Dispatch.succeeded (transferred := RuntimeCallEffectsSemantics.shared (logged object .ordinary).external)
      · exact .inr (by change ¬w 0 > w 10; decide +kernel)
      · rfl
      · exact .empty (by change AccountCallSemantics.isPrecompile (w 100) = false; decide +kernel) rfl rfl
      · rfl
    · exact .done rfl (.empty _ _ _ _)
  case staticCall.executed.dispatched =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := AccountCallSemantics.emptyResponse true) (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · apply AccountCallSemantics.Dispatch.succeeded (transferred := RuntimeCallEffectsSemantics.shared (logged object .staticCall).external)
      · exact .inr (by change ¬w 0 > w 10; decide +kernel)
      · rfl
      · exact .empty (by change AccountCallSemantics.isPrecompile (w 100) = false; decide +kernel) rfl rfl
      · rfl
    · exact .done rfl (.empty _ _ _ _)
  case transfer.executed.dispatched =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := AccountCallSemantics.emptyResponse true) (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · apply AccountCallSemantics.Dispatch.succeeded (transferred := sharedAfter object .transfer)
      · exact .inr (by change ¬w 3 > w 10; decide +kernel)
      · dsimp only [AccountCallSemantics.transferFor]
        simp only [show (AccountCallSemantics.Mode.ordinary == .ordinary) = true from rfl, ↓reduceIte]
        have moved : AccountCallSemantics.transfer (w 0) ((w 100).bitAnd (w (2 ^ 160 - 1))) (w 3) [(w 0, w 10)] =
            .ok [(w 0, w 7), (w 100, w 3)] := by
          rw [show (w 100).bitAnd (w (2 ^ 160 - 1)) = w 100 from by decide +kernel]
          exact transfer_balances
        change Except.map _ (AccountCallSemantics.transfer (w 0) ((w 100).bitAnd (w (2 ^ 160 - 1))) (w 3) [(w 0, w 10)]) = _
        rw [moved]
        rfl
      · exact .empty (by change AccountCallSemantics.isPrecompile (w 100) = false; decide +kernel) rfl rfl
      · rfl
    · exact .done rfl (.empty _ _ _ _)
  case insufficient.executed.dispatched =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := AccountCallSemantics.emptyResponse false) (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · exact .insufficient (by decide +kernel) (by change w 11 > w 10; decide +kernel)
    · exact .done rfl (.empty _ _ _ _)
  case incomplete.executed.dispatched =>
    apply CallTransportSemantics.Dispatch.fault (input := input)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · apply AccountCallSemantics.Dispatch.fault
        (transferred := {RuntimeCallEffectsSemantics.shared (logged object .incomplete).external with balances := [(w 0, w 7), (w 100, w 3)]})
      · exact .inr (by change ¬w 3 > w 10; decide +kernel)
      · dsimp only [AccountCallSemantics.transferFor]
        simp only [show (AccountCallSemantics.Mode.ordinary == .ordinary) = true from rfl, ↓reduceIte]
        have moved : AccountCallSemantics.transfer (w 0) ((w 100).bitAnd (w (2 ^ 160 - 1))) (w 3) [(w 0, w 10)] =
            .ok [(w 0, w 7), (w 100, w 3)] := by
          rw [show (w 100).bitAnd (w (2 ^ 160 - 1)) = w 100 from by decide +kernel]
          exact transfer_balances
        change Except.map _ (AccountCallSemantics.transfer (w 0) ((w 100).bitAnd (w (2 ^ 160 - 1))) (w 3) [(w 0, w 10)]) = _
        rw [moved]
        rfl
      · exact .unavailable (by change AccountCallSemantics.isPrecompile (w 100) = false; decide +kernel) rfl rfl

private theorem call_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] (invoked scenario)
      (logged object scenario) (callResult scenario) (afterCall object scenario) := by
  cases scenario <;> apply Semantics.EvalExpr.call rfl
  all_goals first
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "31") rfl) (.cons (.word (text := "2") rfl) .nil)))))))
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "31") rfl) (.cons (.word (text := "2") rfl) .nil))))))
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "31") rfl) (.cons (.word (text := "2") rfl) .nil)))))))
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "11") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "31") rfl) (.cons (.word (text := "2") rfl) .nil)))))))
    | exact (.cons (.word (text := maximum) rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "31") rfl) (.cons (.word (text := "2") rfl) .nil)))))))
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := maximum) rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "31") rfl) (.cons (.word (text := "2") rfl) .nil)))))))
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := maximum) rfl) (.cons (.word (text := "2") rfl) .nil)))))))
    | exact .external (by rfl) rfl (.call (invoked_source object .ordinary))
    | exact .external (by rfl) rfl (.staticCall (invoked_source object .staticCall))
    | exact .external (by rfl) rfl (.call (invoked_source object .transfer))
    | exact .external (by rfl) rfl (.call (invoked_source object .insufficient))
    | exact .external (by rfl) rfl (.call (invoked_source object .incomplete))
    | exact .external (by rfl) rfl (.call (invoked_source object .staticValue))
    | exact .external (by rfl) rfl (.call (invoked_source object .stipend))
    | exact .external (by rfl) rfl (.call (invoked_source object .inputOverflow))
    | exact .external (by rfl) rfl (.call (invoked_source object .outputOverflow))

def storeResult (scenario : Scenario) : Semantics.Result Semantics.Value := (callResult scenario).map (fun _ => .unit)

private theorem store_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] (stored scenario)
      (logged object scenario) (storeResult scenario) (afterStore object scenario) := by
  cases scenario
  all_goals first
    | apply Semantics.EvalExpr.call rfl (.cons (.word (text := "2") rfl) (.cons (call_source object _) .nil))
      exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))
    | exact .callFault rfl (.cons (.word (text := "2") rfl) (.fault (call_source object _)))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario)
    (normal : ∃ value, callResult scenario = .value value) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] returned
      (afterStore object scenario) (result scenario) (finalState object scenario) := by
  cases scenario
  all_goals first
    | (obtain ⟨value, impossible⟩ := normal; cases impossible; done)
    | apply Semantics.EvalExpr.call rfl
      · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "2") rfl) .nil)
      · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none)
      (AccountRuntime.frameFunction (code scenario)) [] (initial object scenario) (result scenario) (finalState object scenario) := by
  cases scenario
  all_goals
    apply Semantics.EvalFunction.body (control := .fault _) rfl
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object _))
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (storage_source object _))
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (event_source object _))
    first
      | apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (store_source object _))
        exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object _ ⟨_, rfl⟩))
          (by intro impossible; cases impossible)
      | exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (store_source object _))
          (by intro impossible; cases impossible)

def usedNames : List String := ["mstore8", "sstore", "log0", "msize", "call", "staticcall", "return"]

private theorem atoms {supported : String → Prop} (functions : List Function) (type : Ty) (name : String)
    (arguments : List String) (available : supported name)
    (absent : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (call type name (arguments.map word)) := by
  apply ExecutableExpression.external (name := name) available absent
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported [AccountRuntime.frameFunction (code scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["1", "171"] (available _ (by simp [usedNames])) (by rfl)
  · cases scenario <;> first
      | exact atoms _ .unit "sstore" ["7", "42"] (available _ (by simp [usedNames])) (by rfl)
      | exact atoms _ .word "msize" [] (available _ (by simp [usedNames])) (by rfl)
  · cases scenario <;> first
      | exact atoms _ .unit "log0" ["1", "1"] (available _ (by simp [usedNames])) (by rfl)
      | exact atoms _ .word "msize" [] (available _ (by simp [usedNames])) (by rfl)
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases scenario <;> first
        | exact atoms _ .word "staticcall" ["100", "100", "1", "1", "31", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["100", "100", "0", "1", "1", "31", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["100", "100", "3", "1", "1", "31", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["100", "100", "11", "1", "1", "31", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" [maximum, "100", "3", "1", "1", "31", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["100", "100", "0", maximum, "1", "31", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["100", "100", "0", "1", "1", maximum, "2"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "return" ["1", "2"] (available _ (by simp [usedNames])) (by rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallCorrespondence.supported false name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store8, rfl⟩))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.store false, rfl⟩))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.log0, rfl⟩))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.size, rfl⟩))))))))
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)
  · exact .inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩)))))

theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Calls"] 64 none [] = .ok object) :
    ∃ value, ContractCallCorrespondence.PublicMessageRel (context scenario) (result scenario) (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate (context scenario)) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallCorrespondence.compileObject_resumes_exact (code := code scenario) (by rfl) accepted
    (eligible scenario names_supported) (context scenario) rfl (source object scenario)

theorem public_prepared (scenario : Scenario) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program scenario) ["Calls"] (context scenario) 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program scenario) ["Calls"] 64 none [] = .ok object ∧
      prepared = object.instantiate (context scenario) ∧
      ∃ value, ContractCallCorrespondence.PublicMessageRel (context scenario) (result scenario) (finalState object scenario).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractCallCorrespondence.prepare_resumes_exact
    (code := code scenario) (by rfl) accepted (eligible scenario names_supported) rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object scenario)⟩

private def expectedEvents (scenario : Scenario) : List Logs.Event :=
  if static scenario then [] else [⟨w 0, [], [171]⟩]
private def expectedStorage (scenario : Scenario) : Core.WordMapping.Entries :=
  if static scenario then [] else [(w 7, w 42)]
private def expectedBalances (scenario : Scenario) : Core.WordMapping.Entries :=
  if scenario = .transfer then [(w 0, w 7), (w 100, w 3)] else [(w 0, w 10)]

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Calls"] 64 none [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"call correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate (context scenario)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"call correspondence: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"call correspondence: short resume completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match callResult scenario with
    | .value _ =>
        match receipt.outcome with
        | .returned bytes storage =>
            let expected : List UInt8 := [171, if scenario = .insufficient then 0 else 1]
            unless bytes == expected && storage == expectedStorage scenario && receipt.logs == expectedEvents scenario &&
                receipt.balances == expectedBalances scenario do
              throw (IO.userError s!"call correspondence: wrong successful state for {reprStr scenario}: {reprStr receipt}")
        | outcome => throw (IO.userError s!"call correspondence: expected return for {reprStr scenario}: {reprStr outcome}")
    | .fault (.language reason) =>
        let expected := if scenario = .staticValue then
          match receipt.outcome with | .invalid => true | _ => false
        else match receipt.outcome with | .languageFailure (.word actual) => actual == reason | _ => false
        unless expected && receipt.world.isEmpty && receipt.logs.isEmpty && receipt.balances.isEmpty do
          throw (IO.userError s!"call correspondence: wrong failure or exported changes for {reprStr scenario}: {reprStr receipt}")
    | _ => throw (IO.userError "call correspondence: invalid fixture")
  match Core.runStateful 1000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair length (.pair memory (.pair storage (.pair logs (.pair cursor (.pair balances _))))))))) _ =>
      let expected := (finalState object scenario).external
      let runtime := expected.runtime.runtime.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words && storage == Core.WordMapping.encode (expectedStorage scenario) &&
          logs == Core.WordMapping.encode expected.runtime.runtime.runtime.words && cursor == .word expected.runtime.runtime.runtime.cursor &&
          balances == Core.WordMapping.encode (expectedBalances scenario) && exit == .word runtime.storage.exit &&
          offset == .word runtime.storage.returnOffset && length == .word runtime.storage.returnSize do
        throw (IO.userError s!"call correspondence: internal snapshot mismatch for {reprStr scenario}")
      match Logs.decodeValues logs cursor with
      | .ok events =>
          unless events == expectedEvents scenario do
            throw (IO.userError "call correspondence: callback changed the prior event snapshot")
      | .error error => throw (IO.userError s!"call correspondence: malformed internal logs: {error}")
  | outcome => throw (IO.userError s!"call correspondence: Core failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.ordinary, .staticCall, .transfer, .insufficient, .incomplete, .staticValue,
      .stipend, .inputOverflow, .outputOverflow] do
    check scenario

end Tests.RustHullCallCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullCalls
set_option autoImplicit false
namespace Tests.RustHullCalls
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def ok (value : Nat) : Value := .inRight .word (scalar value)

private structure Call where
  depth : Nat := 0
  source : Nat := 7
  length : Nat := 65
  destination : Nat := 8
  outputLength : Nat := 17
  static : Bool := false
  installed : Bool := true
  success : Bool := true
  fail : Bool := false
  mutate : Bool := false
  tick : Bool := false

private def callbackBody (call : Call) : Expr :=
  let request := Expr.var 0
  let reject := LanguageResult.failure Calls.responseType (number 99)
  let result := if call.fail then reject else
    LanguageResult.success (Calls.response (.bool call.success)
      (Calls.requestField 6 request) (Calls.requestField 7 request))
  let result := if call.mutate then LocalSequence.discard Calls.responseType
    (Memory.mstore8 (.var 6) (.var 5) (number 0) (number 0xee)) result else result
  let checks := [(0, 0xabc), (1, 0xdef), (2, 17), (4, call.depth + 1), (5, 88), (7, call.length)]
  let checked : Expr := checks.foldr (fun (index, expected) next =>
    .ifE (.binary .wordEq (Calls.requestField index request) (number expected)) next reject)
    (.ifE (Calls.requestField 3 request) (if call.static then result else reject)
      (if call.static then reject else result))
  .letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (number 1)))
    (checked.weakenAt 0)

/-- In the body: counter0, callback1, return size2, return map3, memory size4,
memory5. The callback captures these cells and receives its request at zero. -/
private def invoke (call : Call) : Expr :=
  let tick (value : Expr) := if call.tick then
    Expr.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (number 1)))
      (value.weakenAt 0) else value
  Calls.invoke (tick (.var 5)) (tick (.var 4)) (tick (.var 3)) (tick (.var 2)) (tick (.var 1))
    (tick (number (2 ^ 200 + 0xdef))) (tick (number call.depth)) (tick (.bool call.static))
    (tick (number 88)) (tick (number (2 ^ 200 + 0xabc))) (tick (number 17))
    (tick (number call.source)) (tick (number call.length))
    (tick (number call.destination)) (tick (number call.outputLength))

private def program (input : List UInt8) (call : Call) : Program :=
  let body := if call.installed then
    Expr.letE (.storeCell (.var 1) (.inRight .unit
      (.lambda Calls.requestType (LanguageResult.resultType Calls.responseType) (callbackBody call))))
      ((invoke call).weakenAt 0) else invoke call
  {resultType := LanguageResult.resultType .word, dataDefinitions := Memory.definitions,
   body := .letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes input)))
      (.letE (.newCell .word (number 0))
        (.letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes [0xaa, 0xbb])))
          (.letE (.newCell .word (number 2))
            (.letE (OptionalCell.allocate Calls.callbackType)
              (.letE (.newCell .word (number 0)) body)))))}

private def entries : Value → Except String WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor == WordMapping.nilConstructor then pure [] else .error "invalid empty map"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor == WordMapping.consConstructor do throw "invalid map constructor"
      pure ((key, value) :: (← entries tail))
  | _ => .error "invalid map value"

private def checkMap (label : String) (actual : Option Value) (expected : List UInt8) : IO Unit := do
  let some actual := actual | throw (IO.userError s!"{label}: missing cell")
  let actual ← match entries actual with
    | .ok actual => pure actual
    | .error error => throw (IO.userError s!"{label}: {error}")
  let expected := Memory.packBytes expected
  for (key, _) in actual ++ expected do
    require (WordMapping.lookupEntries key actual == WordMapping.lookupEntries key expected)
      s!"{label}: wrong packed word at {key.val}"

private def verify (label : String) (expected : Value) (memory returned : List UInt8)
    (size count : Nat) (actual : StatefulRunResult) : IO Unit :=
  match actual with
  | .done value store => do
      require (value == expected) s!"{label}: {reprStr value}"
      checkMap s!"{label} memory" store[0]? memory
      require (store[1]? == some (scalar size)) s!"{label}: memory extent"
      checkMap s!"{label} return data" store[2]? returned
      require (store[3]? == some (scalar returned.length)) s!"{label}: return data extent"
      require (store[5]? == some (scalar count)) s!"{label}: argument/callback count"
  | .outOfFuel _ => throw (IO.userError s!"{label}: exhausted test fuel")
  | .fault error _ => throw (IO.userError s!"{label}: {reprStr error}")

private def resumeChunks : Nat → State → IO StatefulRunResult
  | 0, _ => throw (IO.userError "call resume budget exhausted")
  | fuel + 1, state => match runStateful 500 state with
      | .outOfFuel state => resumeChunks fuel state
      | result => pure result

private def overwritten (input : List UInt8) (offset : Nat) (replacement : List UInt8) : List UInt8 :=
  let padded := input ++ List.replicate (offset + replacement.length - input.length) 0
  padded.take offset ++ replacement ++ padded.drop (offset + replacement.length)

private def check (label : String) (input : List UInt8) (call : Call) (expected : Value)
    (memory returned : List UInt8) (size count : Nat) (resume : Bool := false) : IO Unit := do
  let compiled := program input call
  require compiled.check s!"{label}: ill-typed Core"
  verify label expected memory returned size count (compiled.runStateful 2000000)
  if resume then
    match compiled.runStateful 100 with
    | .outOfFuel state => verify s!"{label} resumed" expected memory returned size count (← resumeChunks 10000 state)
    | _ => throw (IO.userError s!"{label}: fixture did not suspend")

def run : IO Unit := do
  let input := (List.range 160).map fun index => UInt8.ofNat (index * 7 + 3)
  let payload := (input.drop 7).take 65
  for succeeded in [true, false] do
    check s!"nested {(if succeeded then "return" else "revert")} bytes and clipped overlapping output"
      input {success := succeeded, tick := true} (ok (if succeeded then 1 else 0))
      (overwritten input 8 (payload.take 17)) payload 96 16 true
  check "input snapshot survives callback memory writes" input {mutate := true}
    (ok 1) (overwritten (overwritten input 0 [0xee]) 8 (payload.take 17)) payload 96 1
  check "static flag and child depth1024" input {depth := 1023, static := true}
    (ok 1) (overwritten input 8 (payload.take 17)) payload 96 1
  for depth in [1024, wordModulus - 1] do
    check s!"depth{depth} refuses child and clears return data" input {depth}
      (ok 0) input [] 96 0
  check "empty ranges ignore maximal offsets" input
    {source := wordModulus - 1, length := 0, destination := wordModulus - 1, outputLength := 0}
    (ok 1) input [] 0 1
  check "short return data leaves output suffix untouched" input {length := 3, outputLength := 65}
    (ok 1) (overwritten input 8 ((input.drop 7).take 3)) ((input.drop 7).take 3) 96 1
  check "no output keeps full return data" input {destination := wordModulus - 1, outputLength := 0}
    (ok 1) input payload 96 1
  check "callback unavailable" input {installed := false}
    (.inLeft .word (.word Calls.unavailableReason)) input [] 96 0
  check "callback language failure propagates" input {fail := true}
    (.inLeft .word (scalar 99)) input [] 96 1
  check "invalid input range does not start call" input
    {source := wordModulus - 16, length := 32}
    (.inLeft .word (.word Memory.overflowReason)) input [0xaa, 0xbb] 0 0
  check "invalid output range does not start call" input
    {source := 0, length := 1, destination := wordModulus - 16, outputLength := 32}
    (.inLeft .word (.word Memory.overflowReason)) input [0xaa, 0xbb] 32 0

end Tests.RustHullCalls
end

section
-- leanmerge: from Solcore.Test.RustHullChildCallCorrespondence
/-! A real catalog child runs in a fresh frame. Its shared writes commit only
on success, while revert data remains available to the parent. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullChildCallCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where | returned | reverted | invalid | staticCall
  deriving DecidableEq, Repr
private abbrev w := Core.Word.ofNatModulo
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def childBytes : List UInt8 := [0x60, 0x00]
def childAccount : AccountState.Account := {address := w 100, code := some childBytes, nonce := w 1}
def context : Contract.Context := {world := [childAccount], completeWorld := true}
def seed : Expr := call .unit "mstore8" [word "3", word "170"]
def priorStorage : Expr := call .unit "sstore" [word "7", word "42"]
def priorLog : Expr := call .unit "log0" [word "3", word "1"]
def invoke (scenario : Scenario) : Expr :=
  if scenario = .staticCall then call .word "staticcall" [word "100", word "100", word "0", word "0", word "2", word "1"]
  else call .word "call" [word "100", word "100", word "0", word "0", word "0", word "2", word "1"]
def storedStatus (scenario : Scenario) : Expr := call .unit "mstore8" [word "0", invoke scenario]
def storedSize : Expr := call .unit "mstore8" [word "1", call .word "returndatasize" []]
def returned : Expr := call .unit "return" [word "0", word "4"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression seed, expression priorStorage, expression priorLog,
    expression (storedStatus scenario), expression storedSize, expression returned], functions := []}
def childSeed : Expr := call .unit "mstore8" [word "0", word "187"]
def childStorage : Expr := call .unit "sstore" [word "8", word "99"]
def childTransient : Expr := call .unit "tstore" [word "9", word "77"]
def childLog : Expr := call .unit "log0" [word "0", word "1"]
def childFinish (scenario : Scenario) : Expr :=
  match scenario with
  | .invalid => call .unit "invalid" []
  | .reverted => call .unit "revert" [word "0", word "1"]
  | _ => call .unit "return" [word "0", word "1"]
def childCode (scenario : Scenario) : CodeBlock := {
  stmts := [expression childSeed, expression childStorage, expression childTransient,
    expression childLog, expression (childFinish scenario)], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Parent" (code scenario) [], .object "Child" (childCode scenario) []]}
def compiledCatalog (scenario : Scenario) : List AccountRuntime.CodeDefinition :=
  [{program := program scenario, path := ["Child"], bytes := childBytes}]
def sourceCode (scenario : Scenario) : ChildFrameSemantics.Code := ⟨program scenario, childCode scenario, childBytes⟩
def catalog (scenario : Scenario) : ChildFrameSemantics.Catalog := [(w 100, sourceCode scenario)]
def effects (scenario : Scenario) := ChildFrameSemantics.callFreeEffects (catalog scenario) none
abbrev SourceState := Semantics.State RuntimeCallEffectsSemantics.State
abbrev ChildState := Semantics.State RuntimeReturnDataEffectsSemantics.State

def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ⟨⟨ContractCodeCorrespondence.contextInitialState none object (Contract.normalizeContext context), []⟩, w 0⟩⟩
def withRuntime (state : SourceState) (runtime : RuntimeEffectsSemantics.State) : SourceState :=
  ⟨[], {state.external with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime runtime}⟩
def parentRuntime (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime

def seeded (object : Contract.CompiledObject) : SourceState := withRuntime (initial object)
  {parentRuntime (initial object) with memory := (MemorySemantics.mstore8 {} (w 3) (w 170)).2}
def stored (object : Contract.CompiledObject) : SourceState := withRuntime (seeded object)
  {parentRuntime (seeded object) with storage := (StorageSemantics.store (parentRuntime (seeded object)).storage (w 7) (w 42) false).2}
def logWords (state : LogsSemantics.State) (offset : Core.Word) : LogsSemantics.Words :=
  MemorySemantics.insert (state.cursor.add (w 3)) (LogsSemantics.paddedWord state.memory.words offset (w 1))
    (LogsSemantics.insertWords state.words state.cursor (LogsSemantics.headers state.address (w 1) []))
def addLog (state : RuntimeLogEffectsSemantics.State) (offset : Core.Word) : RuntimeLogEffectsSemantics.State :=
  let old := RuntimeLogEffectsSemantics.logsState state
  RuntimeLogEffectsSemantics.withLogs state {old with words := logWords old offset, cursor := LogsSemantics.nextCursor old.cursor (w 1) []}
def logged (object : Contract.CompiledObject) : SourceState :=
  let state := (stored object).external
  ⟨[], {state with runtime := {state.runtime with runtime := {state.runtime.runtime with runtime := addLog state.runtime.runtime.runtime (w 3)}}}⟩
def arguments (object : Contract.CompiledObject) (scenario : Scenario) : CallTransportSemantics.Arguments :=
  RuntimeCallEffectsSemantics.arguments (if scenario = .staticCall then .staticCall else .ordinary)
    (logged object).external (w 100) (w 100) (w 0) (w 0) (w 0) (w 2) (w 1)
def request (object : Contract.CompiledObject) (scenario : Scenario) : AccountCallSemantics.Request :=
  CallTransportSemantics.request (arguments object scenario) []
def childInitial (object : Contract.CompiledObject) (scenario : Scenario) : ChildState :=
  ⟨[], (ChildFrameSemantics.initial (logged object).external (request object scenario)
    (RuntimeCallEffectsSemantics.shared (logged object).external) childBytes).runtime⟩
def childRuntime (state : ChildState) := state.external.runtime.runtime.runtime.runtime
def childWithRuntime (state : ChildState) (runtime : RuntimeEffectsSemantics.State) : ChildState :=
  ⟨[], RuntimeReturnDataEffectsSemantics.withRuntime state.external runtime⟩
def childSeeded (object : Contract.CompiledObject) (scenario : Scenario) : ChildState := childWithRuntime (childInitial object scenario)
  {childRuntime (childInitial object scenario) with memory := (MemorySemantics.mstore8 {} (w 0) (w 187)).2}
def childStored (object : Contract.CompiledObject) (scenario : Scenario) : ChildState := childWithRuntime (childSeeded object scenario)
  {childRuntime (childSeeded object scenario) with storage := (StorageSemantics.store (childRuntime (childSeeded object scenario)).storage (w 8) (w 99) false).2}
def childTransientStored (object : Contract.CompiledObject) (scenario : Scenario) : ChildState := childWithRuntime (childStored object scenario)
  {childRuntime (childStored object scenario) with storage := (StorageSemantics.store (childRuntime (childStored object scenario)).storage (w 9) (w 77) true).2}
def childLogged (object : Contract.CompiledObject) (scenario : Scenario) : ChildState :=
  let state := (childTransientStored object scenario).external
  ⟨[], {state with runtime := {state.runtime with runtime := addLog state.runtime.runtime (w 0)}}⟩
def childFinal (object : Contract.CompiledObject) (scenario : Scenario) : ChildState :=
  if scenario = .staticCall then childStored object scenario else
    childWithRuntime (childLogged object scenario)
      (TerminationSemantics.terminate (childRuntime (childLogged object scenario))
        (if scenario = .invalid then 3 else if scenario = .reverted then 2 else 1)
        (w 0) (if scenario = .invalid then w 0 else w 1)).2

def childStatus : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)
def response (object : Contract.CompiledObject) (scenario : Scenario) : AccountCallSemantics.Response :=
  match scenario with
  | .invalid | .staticCall => AccountCallSemantics.emptyResponse false
  | _ => ⟨scenario = .returned, MemorySnapshotSemantics.aligned (childRuntime (childFinal object scenario)).memory.words (w 0) (w 1), w 1⟩

private theorem child_seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (sourceCode scenario).functions (RuntimeReturnDataEffectsSemantics.effects (some childBytes)) [] childSeed
      (childInitial object scenario) (.value .unit) (childSeeded object scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0") rfl) (.cons (.word (text := "187") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))))

private theorem child_storage_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (sourceCode scenario).functions (RuntimeReturnDataEffectsSemantics.effects (some childBytes)) [] childStorage
      (childSeeded object scenario) (if scenario = .staticCall then childStatus else .value .unit) (childStored object scenario) := by
  cases scenario <;> apply Semantics.EvalExpr.call rfl
  all_goals first
    | exact .cons (.word (text := "8") rfl) (.cons (.word (text := "99") rfl) .nil)
    | exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))))

private theorem child_transient_source (object : Contract.CompiledObject) (scenario : Scenario) (writable : scenario ≠ .staticCall) :
    Semantics.EvalExpr (sourceCode scenario).functions (RuntimeReturnDataEffectsSemantics.effects (some childBytes)) [] childTransient
      (childStored object scenario) (.value .unit) (childTransientStored object scenario) := by
  cases scenario <;> (try contradiction)
  all_goals
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "9") rfl) (.cons (.word (text := "77") rfl) .nil)
    · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))))

private theorem log_copied (state : LogsSemantics.State) (offset : Core.Word) :
    LogsSemantics.Copy state.memory.words offset (w 1)
      (LogsSemantics.insertWords state.words state.cursor (LogsSemantics.headers state.address (w 1) []))
      (state.cursor.add (w 3)) (logWords state offset) := by
  apply LogsSemantics.Copy.step (by decide +kernel)
  exact .empty _ _ _

private theorem child_log_source (object : Contract.CompiledObject) (scenario : Scenario) (writable : scenario ≠ .staticCall) :
    Semantics.EvalExpr (sourceCode scenario).functions (RuntimeReturnDataEffectsSemantics.effects (some childBytes)) [] childLog
      (childTransientStored object scenario) (.value .unit) (childLogged object scenario) := by
  cases scenario <;> (try contradiction)
  all_goals
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil)
    · apply Semantics.EvalCall.external (by rfl) rfl
      apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
      apply RuntimeCodeEffectsSemantics.Builtin.runtime
      apply RuntimeAccountEffectsSemantics.Builtin.runtime
      apply RuntimeHashEffectsSemantics.Builtin.runtime
      apply RuntimeCopyEffectsSemantics.Builtin.runtime
      apply RuntimeFullEffectsSemantics.Builtin.runtime
      apply RuntimeLogEffectsSemantics.Builtin.logs
      apply LogsSemantics.Builtin.log .log0 .unit (w 0) (w 1) [] rfl
      apply LogsSemantics.Execute.writable rfl
      apply LogsSemantics.Append.done (size := w 32)
      · decide +kernel
      · change ¬w 4 > LogsSemantics.nextCursor (w 4) (w 1) []
        decide +kernel
      · change MemorySemantics.touchSize? (w 32) (w 0) (w 1) = some (w 32)
        decide +kernel
      · exact log_copied _ _

private theorem child_finish_source (object : Contract.CompiledObject) (scenario : Scenario) (writable : scenario ≠ .staticCall) :
    Semantics.EvalExpr (sourceCode scenario).functions (RuntimeReturnDataEffectsSemantics.effects (some childBytes)) [] (childFinish scenario)
      (childLogged object scenario) childStatus (childFinal object scenario) := by
  cases scenario <;> (try contradiction)
  all_goals first
    | apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil))
      exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl))))))
    | apply Semantics.EvalExpr.call rfl .nil
      exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl))))))

theorem child_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (sourceCode scenario).functions (RuntimeReturnDataEffectsSemantics.effects (some childBytes))
      (sourceCode scenario).entry [] (childInitial object scenario) childStatus (childFinal object scenario) := by
  cases scenario
  all_goals
    apply Semantics.EvalFunction.body (control := .fault _) rfl
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_seed_source object _))
    first
      | exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (child_storage_source object .staticCall))
          (by intro impossible; cases impossible)
      | apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_storage_source object _))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_transient_source object _ (by decide)))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_log_source object _ (by decide)))
        exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (child_finish_source object _ (by decide)))
          (by intro impossible; cases impossible)

theorem child_response (object : Contract.CompiledObject) (scenario : Scenario) :
    ChildResultSemantics.Respond
      (ChildFrameSemantics.completedStatus childStatus (childRuntime (childFinal object scenario)))
      (childRuntime (childFinal object scenario)) (.value (response object scenario)) := by
  cases scenario
  case returned =>
    apply ChildResultSemantics.Respond.returned (data := .value (MemorySnapshotSemantics.aligned (childRuntime (childFinal object .returned)).memory.words (w 0) (w 1))) rfl
    apply MemorySnapshotSemantics.Extract.aligned (size := w 32)
    · change MemorySemantics.touchSize? (w 0) (w 0) (w 1) = some (w 32)
      decide +kernel
    · change w 1 ≠ w 0
      decide +kernel
    · change (w 0).umod (w 32) = w 0
      decide +kernel
  case reverted =>
    apply ChildResultSemantics.Respond.reverted (data := .value (MemorySnapshotSemantics.aligned (childRuntime (childFinal object .reverted)).memory.words (w 0) (w 1))) rfl
    apply MemorySnapshotSemantics.Extract.aligned (size := w 32)
    · change MemorySemantics.touchSize? (w 0) (w 0) (w 1) = some (w 32)
      decide +kernel
    · change w 1 ≠ w 0
      decide +kernel
    · change (w 0).umod (w 32) = w 0
      decide +kernel
  case invalid => exact .invalid rfl
  case staticCall => exact .invalid rfl

def childShared (object : Contract.CompiledObject) (scenario : Scenario) : AccountCallSemantics.Shared :=
  RuntimeCallEffectsSemantics.shared ⟨(childFinal object scenario).external, (request object scenario).depth⟩
def finalShared (object : Contract.CompiledObject) (scenario : Scenario) : AccountCallSemantics.Shared :=
  if scenario = .returned then childShared object scenario else RuntimeCallEffectsSemantics.shared (logged object).external

theorem child_called (object : Contract.CompiledObject) (scenario : Scenario) :
    ChildFrameSemantics.CallFree (catalog scenario) (logged object).external .ordinary (w 0)
      (request object scenario) (RuntimeCallEffectsSemantics.shared (logged object).external)
      (.value (response object scenario)) (childShared object scenario) := by
  apply ChildFrameSemantics.CallFree.executed (account := childAccount) (code := sourceCode scenario)
  · change AccountCallSemantics.isPrecompile (w 100) = false
    decide +kernel
  · rfl
  · rfl
  · rfl
  · exact child_source object scenario
  · exact child_response object scenario

def transportAfter (object : Contract.CompiledObject) (scenario : Scenario) : CallTransportSemantics.State :=
  let old := (parentRuntime (logged object)).memory
  let response := response object scenario
  let memory := if scenario = .returned ∨ scenario = .reverted then
      {old with words := MemoryCopySemantics.written old.words (w 2) (w 1) (MemoryCopySemantics.copiedWord response.data (w 0) (w 1))}
    else old
  ⟨memory, response.data, response.size⟩
def callValue (scenario : Scenario) : Core.Word := if scenario = .returned then w 1 else w 0
def afterCall (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], RuntimeCallEffectsSemantics.withTransport (logged object).external
    (transportAfter object scenario) (finalShared object scenario)⟩
def afterStatus (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withRuntime (afterCall object scenario) {parentRuntime (afterCall object scenario) with
    memory := (MemorySemantics.mstore8 (transportAfter object scenario).memory (w 0) (callValue scenario)).2}
def afterSize (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withRuntime (afterStatus object scenario) {parentRuntime (afterStatus object scenario) with
    memory := (MemorySemantics.mstore8 (parentRuntime (afterStatus object scenario)).memory
      (w 1) (response object scenario).size).2}
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withRuntime (afterSize object scenario) (TerminationSemantics.terminate (parentRuntime (afterSize object scenario)) 1 (w 0) (w 4)).2

def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (effects scenario) [] seed
      (initial object) (.value .unit) (seeded object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "3") rfl) (.cons (.word (text := "170") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem storage_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (effects scenario) [] priorStorage
      (seeded object) (.value .unit) (stored object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "42") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem log_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (effects scenario) [] priorLog
      (stored object) (.value .unit) (logged object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "3") rfl) (.cons (.word (text := "1") rfl) .nil)
  · apply Semantics.EvalCall.external (by rfl) rfl
    apply RuntimeCallEffectsSemantics.Builtin.runtime
    apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
    apply RuntimeCodeEffectsSemantics.Builtin.runtime
    apply RuntimeAccountEffectsSemantics.Builtin.runtime
    apply RuntimeHashEffectsSemantics.Builtin.runtime
    apply RuntimeCopyEffectsSemantics.Builtin.runtime
    apply RuntimeFullEffectsSemantics.Builtin.runtime
    apply RuntimeLogEffectsSemantics.Builtin.logs
    apply LogsSemantics.Builtin.log .log0 .unit (w 3) (w 1) [] rfl
    apply LogsSemantics.Execute.writable rfl
    apply LogsSemantics.Append.done (size := w 32)
    · decide +kernel
    · change ¬w 0 > LogsSemantics.nextCursor (w 0) (w 1) []
      decide +kernel
    · change MemorySemantics.touchSize? (w 32) (w 3) (w 1) = some (w 32)
      decide +kernel
    · exact log_copied _ _

private theorem output_copied (object : Contract.CompiledObject) (scenario : Scenario) :
    MemoryCopySemantics.From (response object scenario).data (w 2) (w 0)
      (CallTransportSemantics.copiedLength (arguments object scenario) (response object scenario))
      (parentRuntime (logged object)).memory (.value .unit) (transportAfter object scenario).memory := by
  cases scenario
  all_goals first
    | exact .done rfl (.empty _ _ _ _)
    | change MemoryCopySemantics.From _ (w 2) (w 0) (w 1) _ _ _
      apply MemoryCopySemantics.From.done
      · change MemorySemantics.touchSize? (w 32) (w 2) (w 1) = some (w 32)
        decide +kernel
      · apply MemoryCopySemantics.Copy.step (by decide +kernel)
        change MemoryCopySemantics.Copy _ _ _ ((w 1).sub (w 1)) _ _
        rw [show (w 1).sub (w 1) = Core.Word.zero from by decide +kernel]
        exact .empty _ _ _ _

private theorem called_source (object : Contract.CompiledObject) (scenario : Scenario) :
    RuntimeCallEffectsSemantics.Call (ChildFrameSemantics.CallFree (catalog scenario))
      (if scenario = .staticCall then .staticCall else .ordinary)
      (w 100) (w 100) (w 0) (w 0) (w 0) (w 2) (w 1)
      (logged object).external (.value (.word (callValue scenario))) (afterCall object scenario).external := by
  apply RuntimeCallEffectsSemantics.Call.invoked (.inr (.inl rfl))
  · intros ordinary nonzero
    exact False.elim (nonzero rfl)
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 32)
  · rfl
  · change MemorySemantics.touchSize? (w 32) (w 2) (w 1) = some (w 32)
    decide +kernel
  have finished : CallTransportSemantics.finishResult (response object scenario) (.value .unit) =
      .value (.word (callValue scenario)) := by cases scenario <;> rfl
  rw [←finished]
  apply CallTransportSemantics.Dispatch.returned (input := {}) (response := response object scenario) (result := .value .unit)
  · change ¬w 0 > w 1023
    decide +kernel
  · exact .done rfl (.empty _ _ _ _)
  · rfl
  · cases scenario
    case returned =>
      apply AccountCallSemantics.Dispatch.succeeded (transferred := RuntimeCallEffectsSemantics.shared (logged object).external)
      · exact .inr (by change ¬w 0 > w 0; decide +kernel)
      · rfl
      · exact .child (child_called object .returned)
      · rfl
    all_goals
      apply AccountCallSemantics.Dispatch.refused (transferred := RuntimeCallEffectsSemantics.shared (logged object).external)
      · exact .inr (by change ¬w 0 > w 0; decide +kernel)
      · rfl
      · first | exact .child (child_called object .reverted) | exact .child (child_called object .invalid) | exact .child (child_called object .staticCall)
      · rfl
  · exact output_copied object scenario

private theorem call_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (effects scenario) [] (invoke scenario)
      (logged object) (.value (.word (callValue scenario))) (afterCall object scenario) := by
  cases scenario <;> apply Semantics.EvalExpr.call rfl
  all_goals first
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "1") rfl) .nil)))))))
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "1") rfl) .nil))))))
    | exact .external (by rfl) rfl (.call (called_source object .returned))
    | exact .external (by rfl) rfl (.call (called_source object .reverted))
    | exact .external (by rfl) rfl (.call (called_source object .invalid))
    | exact .external (by rfl) rfl (.staticCall (called_source object .staticCall))

private theorem status_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (effects scenario) [] (storedStatus scenario)
      (logged object) (.value .unit) (afterStatus object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (call_source object scenario) .nil))
  exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem size_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (effects scenario) [] storedSize
      (afterStatus object scenario) (.value .unit) (afterSize object scenario) := by
  have sizeObserved : Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (effects scenario) []
      (call .word "returndatasize" []) (afterStatus object scenario) (.value (.word (response object scenario).size)) (afterStatus object scenario) := by
    apply Semantics.EvalExpr.call rfl .nil
    exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "1") rfl) (.cons sizeObserved .nil))
  exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (effects scenario) [] returned
      (afterSize object scenario) result (finalState object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "4") rfl) .nil))
  exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] (effects scenario)
      (AccountRuntime.frameFunction (code scenario)) [] (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (storage_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (log_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (status_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (size_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object scenario))
    (by intro impossible; cases impossible)

def runtimeNames : List String := ["mstore8", "sstore", "tstore", "log0", "returndatasize", "return", "revert", "invalid"]
def usedNames : List String := runtimeNames ++ ["call", "staticcall"]

private theorem atoms {supported : String → Prop} (functions : List Function) (type : Ty) (name : String)
    (arguments : List String) (available : supported name)
    (absent : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (call type name (arguments.map word)) := by
  apply ExecutableExpression.external (name := name) available absent
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

theorem child_eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ runtimeNames, supported name) :
    ExecutableProgram supported (sourceCode scenario).functions := by
  intro function member statement statementMember
  simp only [sourceCode, ChildFrameSemantics.Code.functions, program, childCode, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [ChildFrameSemantics.Code.entry, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["0", "187"] (available _ (by simp [runtimeNames])) (by rfl)
  · exact atoms _ .unit "sstore" ["8", "99"] (available _ (by simp [runtimeNames])) (by rfl)
  · exact atoms _ .unit "tstore" ["9", "77"] (available _ (by simp [runtimeNames])) (by rfl)
  · exact atoms _ .unit "log0" ["0", "1"] (available _ (by simp [runtimeNames])) (by rfl)
  · cases scenario <;> first
      | exact atoms _ .unit "return" ["0", "1"] (available _ (by simp [runtimeNames])) (by rfl)
      | exact atoms _ .unit "revert" ["0", "1"] (available _ (by simp [runtimeNames])) (by rfl)
      | exact atoms _ .unit "invalid" [] (available _ (by simp [runtimeNames])) (by rfl)

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported [AccountRuntime.frameFunction (code scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["3", "170"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
  · exact atoms _ .unit "sstore" ["7", "42"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
  · exact atoms _ .unit "log0" ["3", "1"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases scenario <;> first
        | exact atoms _ .word "staticcall" ["100", "100", "0", "0", "2", "1"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["100", "100", "0", "0", "0", "2", "1"] (available _ (by simp [usedNames])) (by rfl)
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · exact atoms _ .word "returndatasize" [] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
  · exact atoms _ .unit "return" ["0", "4"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)

private theorem runtime_supported : ∀ name ∈ runtimeNames, ContractCodeCorrespondence.supported name := by
  intro name member
  simp only [runtimeNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (⟨.store8, rfl⟩))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.store false, rfl⟩)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.store true, rfl⟩)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inr ⟨.log0, rfl⟩)))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.direct .returnDataSize, rfl, by intro input member; simp [EnvironmentBuiltinCorrespondence.inputs] at member; subst input; simp [Effects.slots, EnvironmentSemantics.Direct.slot]⟩))))))
  · exact .inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))
  · exact .inl (.inl (.inl (.inl (.inr ⟨.reverted, rfl⟩))))
  · exact .inl (.inl (.inl (.inl (.inr ⟨.invalid, rfl⟩))))

theorem names_supported : ∀ name ∈ usedNames, ContractCallCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with prior | rfl | rfl
  · exact .inl (.inl (runtime_supported name prior))
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

theorem child_names_supported : ∀ name ∈ runtimeNames, ContractReturnDataCorrespondence.supported true name :=
  fun name member => .inl (runtime_supported name member)

def anchors : List CatalogWorldCorrespondence.Anchor := [⟨w 100, childBytes, 2⟩]

theorem catalog_connection (scenario : Scenario) :
    ChildCatalogExecutionCorrespondence.CatalogConnection (catalog scenario) (compiledCatalog scenario) anchors := by
  intro address source selected
  by_cases same : w 100 == address
  · have addressEq : w 100 = address := by simpa only [beq_iff_eq] using same
    subst address
    have sourceEq : sourceCode scenario = source := by
      simpa [ChildFrameSemantics.select, catalog] using selected
    subst source
    refine ⟨0, {program := program scenario, path := ["Child"], bytes := childBytes}, rfl, rfl, rfl, rfl, ?_, ?_, ?_, child_eligible scenario child_names_supported⟩
    · simp [anchors, sourceCode]
    · decide +kernel
    · change (List.range 2).find? (fun candidate => w 2 == w (candidate + 1)) = some 1
      decide +kernel
  · simp [ChildFrameSemantics.select, catalog, same] at selected

theorem initial_links (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    CatalogWorldCorrespondence.Links anchors
      (StorageCorrespondence.canonical (object.initialWorld (Contract.normalizeContext context))) := by
  intro anchor member
  simp only [anchors, List.mem_cons, List.not_mem_nil, or_false] at member
  subst anchor
  exact CatalogWorldCorrespondence.compiled_single_catalog_anchor accepted (Contract.normalizeContext context)
    (address := w 100) (account := childAccount) (by intro impossible; cases impossible) rfl (by decide +kernel) rfl

theorem initial_context_links (scenario : Scenario) (object : Contract.CompiledObject) :
    ContractChildCallCorrespondence.InitialContextLinks none (compiledCatalog scenario) object context anchors := by
  intro anchor member
  simp only [anchors, List.mem_cons, List.not_mem_nil, or_false] at member
  subst anchor
  refine ⟨childAccount, rfl, rfl, ?_, rfl⟩
  decide +kernel

theorem public_evaluates (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      ContractChildCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value := by
  exact ContractChildCallCorrespondence.compileObject_preserves (code := code scenario) (by rfl) accepted rfl
    (eligible scenario names_supported) (catalog_connection scenario) context rfl
    (initial_context_links scenario object) (source object scenario)

theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    ∃ value, ContractChildCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractChildCallCorrespondence.compileObject_resumes_exact (code := code scenario) (by rfl) accepted rfl
    (eligible scenario names_supported) (catalog_connection scenario) context rfl
    (initial_context_links scenario object) (source object scenario)

private def expectedBytes (scenario : Scenario) : List UInt8 :=
  match scenario with
  | .returned => [1, 1, 187, 170]
  | .reverted => [0, 1, 187, 170]
  | _ => [0, 0, 0, 170]
private def expectedEvents (scenario : Scenario) : List Logs.Event :=
  [⟨w 0, [], [170]⟩] ++ if scenario = .returned then [⟨w 100, [], [187]⟩] else []
private def checkWorld (label : String) (scenario : Scenario) (world : List AccountState.Account) : IO Unit := do
  let some parent := world.find? (·.address == w 0) | throw (IO.userError s!"{label}: missing parent")
  let some child := world.find? (·.address == w 100) | throw (IO.userError s!"{label}: missing child")
  let expectedChild := if scenario = .returned then [(w 8, w 99)] else []
  unless world.length == 2 && parent.storage == [(w 7, w 42)] && child.storage == expectedChild &&
      parent.transient.isEmpty && child.transient.isEmpty && child.code == some childBytes do
    throw (IO.userError s!"{label}: wrong commit/rollback/finalization for {reprStr scenario}: {reprStr world}")

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"child call: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"child call: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"child call: short resume completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 2000000, Contract.resumeWithReceipt checkpoint 2000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == expectedBytes scenario && storage == [(w 7, w 42)] &&
            receipt.logs == expectedEvents scenario && receipt.balances == [(w 0, w 0)] do
          throw (IO.userError s!"child call: wrong result for {reprStr scenario}: {reprStr receipt}")
        checkWorld "receipt" scenario receipt.world
    | outcome => throw (IO.userError s!"child call: expected return for {reprStr scenario}: {reprStr outcome}")
  match Core.runStateful 2000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair count (.pair memory (.pair storage (.pair logs (.pair cursor (.pair balances world))))))))) _ =>
      let expected := (finalState object scenario).external
      let runtime := expected.runtime.runtime.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words && storage == Core.WordMapping.encode [(w 7, w 42)] &&
          logs == Core.WordMapping.encode expected.runtime.runtime.runtime.words && cursor == .word expected.runtime.runtime.runtime.cursor &&
          balances == Core.WordMapping.encode [(w 0, w 0)] && exit == .word runtime.storage.exit &&
          offset == .word runtime.storage.returnOffset && count == .word runtime.storage.returnSize do
        throw (IO.userError s!"child call: internal snapshot differs from independent source for {reprStr scenario}")
      let accounts ← match AccountState.decode world with
        | .ok accounts => pure accounts
        | .error error => throw (IO.userError s!"child call: bad world snapshot: {error}")
      checkWorld "Core snapshot" scenario accounts
  | outcome => throw (IO.userError s!"child call: Core failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.returned, .reverted, .invalid, .staticCall] do
    check scenario

end Tests.RustHullChildCallCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullFaultCorrespondence
/-! Fault regressions start with independent Hull execution derivations. They
retain allocations and writes before a fault, skip later computations, and
exercise the actual compiler and repeated public checkpoint resumption. -/
set_option autoImplicit false
namespace Tests.RustHullFaultCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def reason : Core.Word := word 4
private def fault : Semantics.Fault := .language reason
private def v (name : String) : Expr := ⟨.word, .var name, none⟩
private def lit (text : String) : Expr := ⟨.word, .word text, none⟩
private def invoke (name : String) (args : List Expr := []) (type : Ty := .word) : Expr :=
  ⟨type, .call name args, none⟩
private def assign (name : String) (rhs : Expr) : Stmt := ⟨.assign (v name) rhs, none⟩
private def ret (value : Expr) : Stmt := ⟨.returnStmt value, none⟩
private def expr (value : Expr) : Stmt := ⟨.expression value, none⟩
private def decl (name : String) : Stmt := ⟨.letDecl name .word, none⟩
private def yes : Expr := ⟨.bool, .bool true, none⟩
private def loop (condition : Expr) (post body : List Stmt) : Stmt :=
  ⟨.forLoop [] condition post body, none⟩
private def missingBody : List Stmt := [decl "marker", assign "marker" (lit "17")]

def missingWord : Function := {name := "missingWord", args := [], ret := .word, body := missingBody}
def missingBool : Function := {name := "missingBool", args := [], ret := .bool, body := missingBody}
def touch : Function := {
  name := "touch", args := [{name := "value", ty := .word}], ret := .word, body := [ret (v "value")]
}
def combine : Function := {
  name := "combine", args := [{name := "first", ty := .word}, {name := "second", ty := .word}], ret := .word,
  body := [decl "calleeMarker", assign "calleeMarker" (lit "999"), ret (v "first")]
}
def namedFault : Function := {
  name := "namedFault", args := [], ret := .word, body := [ret (invoke "missingWord"), ret (lit "999")]
}
def argumentFault : Function := {
  name := "argumentFault", args := [], ret := .word,
  body := [ret (invoke "primAddWord" [invoke "missingWord", invoke "touch" [lit "999"]])]
}
def namedArgumentsFault : Function := {
  name := "namedArgumentsFault", args := [], ret := .word,
  body := [ret (invoke "combine" [invoke "touch" [lit "7"], invoke "missingWord"])]
}
private def pairValue : Expr := ⟨.product .word .word,
  .pair (invoke "touch" [lit "7"]) (invoke "missingWord"), none⟩
def pairFault : Function := {
  name := "pairFault", args := [], ret := .product .word .word, body := [ret pairValue]
}
private def setup : List Stmt := [decl "total", assign "total" (lit "7")]
private def afterFault : List Stmt := [assign "total" (lit "999"), ret (v "total")]
def assignmentFault : Function := {
  name := "assignmentFault", args := [], ret := .word,
  body := setup ++ [assign "total" (invoke "missingWord")] ++ afterFault
}
def conditionFault : Function := {
  name := "conditionFault", args := [], ret := .word,
  body := setup ++ [loop (invoke "missingBool" [] .bool)
    [assign "total" (lit "999")] [assign "total" (lit "999")]] ++ afterFault
}
def bodyFault : Function := {
  name := "bodyFault", args := [], ret := .word,
  body := setup ++ [loop yes [assign "total" (lit "999")]
    [assign "total" (lit "11"), expr (invoke "missingWord"), assign "total" (lit "999")]] ++ afterFault
}
def postFault : Function := {
  name := "postFault", args := [], ret := .word,
  body := setup ++ [loop yes
    [assign "total" (lit "13"), expr (invoke "missingWord"), assign "total" (lit "999")]
    [assign "total" (lit "11")]] ++ afterFault
}

def program : Program := {
  entryPoints := ["missingWord", "namedFault", "argumentFault", "namedArgumentsFault", "pairFault", "assignmentFault",
    "conditionFault", "bodyFault", "postFault"],
  functions := [missingWord, missingBool, touch, namedFault, argumentFault, pairFault,
    assignmentFault, conditionFault, bodyFault, postFault, combine, namedArgumentsFault], objects := []
}

private theorem literal_eligible (text : String) : RecursiveExpression program.functions (lit text) := .word _ _ _
private theorem variable_eligible (name : String) : RecursiveExpression program.functions (v name) := .var _ _ _
private theorem missing_word_eligible : RecursiveExpression program.functions (invoke "missingWord") := by
  apply RecursiveExpression.named (function := missingWord) rfl
  intro argument member
  cases member
private theorem missing_bool_eligible : RecursiveExpression program.functions (invoke "missingBool" [] .bool) := by
  apply RecursiveExpression.named (function := missingBool) rfl
  intro argument member
  cases member
private theorem touch_eligible (text : String) : RecursiveExpression program.functions (invoke "touch" [lit text]) := by
  apply RecursiveExpression.named (function := touch) rfl
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst argument
  exact literal_eligible _

theorem program_eligible : RecursiveProgram program.functions := by
  intro function member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [missingWord, missingBool, touch, namedFault, argumentFault, pairFault, assignmentFault,
      conditionFault, bodyFault, postFault, combine, namedArgumentsFault, setup, afterFault, missingBody, List.cons_append, List.nil_append,
      ret, decl, assign, expr, v, loop, ExecutableStatement, List.forall_mem_cons,
      List.not_mem_nil, false_implies, implies_true, true_and, and_true]
  · exact literal_eligible _
  · exact literal_eligible _
  · exact variable_eligible _
  · exact ⟨missing_word_eligible, literal_eligible _⟩
  · apply RecursiveExpression.builtin (operation := .binary .add) rfl (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact missing_word_eligible
    · exact touch_eligible _
  · exact .pair (touch_eligible _) missing_word_eligible _ _
  · exact ⟨literal_eligible _, missing_word_eligible, literal_eligible _, variable_eligible _⟩
  · exact ⟨literal_eligible _, ⟨missing_bool_eligible, literal_eligible _, literal_eligible _⟩,
      literal_eligible _, variable_eligible _⟩
  · exact ⟨literal_eligible _, ⟨.bool _ _ _, literal_eligible _, literal_eligible _,
      missing_word_eligible, literal_eligible _⟩, literal_eligible _, variable_eligible _⟩
  · exact ⟨literal_eligible _, ⟨.bool _ _ _, ⟨literal_eligible _, missing_word_eligible,
      literal_eligible _⟩, literal_eligible _⟩, literal_eligible _, variable_eligible _⟩
  · exact ⟨literal_eligible _, variable_eligible _⟩
  · apply RecursiveExpression.named (function := combine) rfl
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact touch_eligible _
    · exact missing_word_eligible

private def pushed {σ : Type} (initial : Semantics.State σ) (value : Core.Word) : Semantics.State σ :=
  {initial with heap := initial.heap ++ [.word value]}

private theorem missing_body_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) :
    Semantics.EvalStatements program.functions effects [] missingBody initial .fallthrough (pushed initial (word 17)) := by
  apply Semantics.EvalStatements.declare (name := "marker") (type := .word) (value := .word (word 0)) rfl rfl
  apply Semantics.EvalStatements.next (middle := pushed initial (word 17))
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.assign (value := .word (word 17)) rfl (.word (text := "17") rfl)
    simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation, Semantics.updateProduct?,
      Semantics.write?, Semantics.allocate, pushed, v]
  · exact .nil

theorem missing_word_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) :
    Semantics.EvalFunction program.functions effects missingWord [] initial (.fault fault) (pushed initial (word 17)) := by
  apply Semantics.EvalFunction.body (control := .fallthrough) rfl
  exact missing_body_source effects initial

theorem missing_bool_source {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) :
    Semantics.EvalFunction program.functions effects missingBool [] initial (.fault fault) (pushed initial (word 17)) := by
  apply Semantics.EvalFunction.body (control := .fallthrough) rfl
  exact missing_body_source effects initial

private theorem missing_word_call {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) (environment : Semantics.Environment) :
    Semantics.EvalExpr program.functions effects environment (invoke "missingWord") initial
      (.fault fault) (pushed initial (word 17)) :=
  .call rfl .nil (.function (function := missingWord) rfl (missing_word_source effects initial))

private theorem missing_bool_call {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) (environment : Semantics.Environment) :
    Semantics.EvalExpr program.functions effects environment (invoke "missingBool" [] .bool) initial
      (.fault fault) (pushed initial (word 17)) :=
  .call rfl .nil (.function (function := missingBool) (by rfl) (missing_bool_source effects initial))

private theorem touch_call {σ : Type} (effects : Semantics.ExternalSemantics σ)
    (initial : Semantics.State σ) (environment : Semantics.Environment) :
    Semantics.EvalExpr program.functions effects environment (invoke "touch" [lit "7"]) initial
      (.value (.word (word 7))) (pushed initial (word 7)) := by
  apply Semantics.EvalExpr.call (values := [.word (word 7)]) rfl (.cons (.word (text := "7") rfl) .nil)
  apply Semantics.EvalCall.function (function := touch) (by rfl)
  apply Semantics.EvalFunction.body (control := .returned (.word (word 7))) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.returned rfl
    have read := Semantics.EvalExpr.var (functions := program.functions) (effects := effects)
      (env := [("value", initial.heap.length)]) (state := pushed initial (word 7)) (expression := v "value") rfl
    simpa [pushed, Semantics.readResult, Semantics.lookupLocation] using read
  · intro same; cases same

theorem named_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects namedFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .returnFault rfl (missing_word_call effects _ _)
  · intro same; cases same

theorem argument_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects argumentFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .returnFault rfl (.callFault rfl (.fault (missing_word_call effects _ _)))
  · intro same; cases same

theorem pair_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects pairFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 7), .word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .returnFault rfl (.pair rfl (touch_call effects _ _) (missing_word_call effects _ _))
  · intro same; cases same

/-- Argument evaluation retains the first call's allocation and the later
fault's heap. The selected callee neither allocates parameters nor runs. -/
theorem named_arguments_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects namedArgumentsFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 7), .word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .returnFault rfl (.callFault rfl
      (.cons (touch_call effects _ _) (.fault (missing_word_call effects _ _))))
  · intro same; cases same

private def state {σ : Type} (external : σ) (total : Nat) : Semantics.State σ := ⟨[.word (word total)], external⟩
private def env : Semantics.Environment := [("total", 0)]

private theorem write_total {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    (before after : Nat) (text : String) (literal : Semantics.literalResult text = .value (.word (word after))) :
    Semantics.EvalStmt program.functions effects env (assign "total" (lit text)) (state external before)
      .fallthrough (state external after) := by
  apply Semantics.EvalStmt.assign (value := .word (word after)) rfl
  · simpa only [literal] using (Semantics.EvalExpr.word (functions := program.functions) (effects := effects)
      (env := env) (state := state external before) (expression := lit text) rfl)
  · simp [Semantics.assignResult, Semantics.place?, Semantics.lookupLocation,
      Semantics.updateProduct?, Semantics.write?, state, env, v]

private theorem with_setup {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {tail : List Stmt} {final : Semantics.State σ}
    (continued : Semantics.EvalStatements program.functions effects env tail (state external 7) (.fault fault) final) :
    Semantics.EvalStatements program.functions effects [] (setup ++ tail) ⟨[], external⟩ (.fault fault) final := by
  apply Semantics.EvalStatements.declare (name := "total") (type := .word) (value := .word (word 0)) rfl rfl
  apply Semantics.EvalStatements.next
  · intros; intro same; cases same
  · exact write_total effects external 0 7 "7" rfl
  · exact continued

theorem assignment_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects assignmentFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 7), .word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply with_setup effects external
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .assignFault rfl (missing_word_call effects _ _)
  · intro same; cases same

theorem condition_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects conditionFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 7), .word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply with_setup effects external
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · exact .forLoop rfl (.conditionFault (missing_bool_call effects _ _))
  · intro same; cases same

theorem body_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects bodyFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 11), .word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply with_setup effects external
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.forLoop rfl
    apply Semantics.EvalLoop.bodyStop (value := .bool true) (.bool rfl) rfl
    · apply Semantics.EvalStatements.next
      · intros; intro same; cases same
      · exact write_total effects external 7 11 "11" rfl
      · apply Semantics.EvalStatements.stop
        · intros; intro same; cases same
        · exact .expressionFault rfl (missing_word_call effects _ _)
        · intro same; cases same
    · exact Or.inr ⟨fault, rfl⟩
  · intro same; cases same

theorem post_fault_source {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ) :
    Semantics.EvalFunction program.functions effects postFault [] ⟨[], external⟩
      (.fault fault) ⟨[.word (word 13), .word (word 17)], external⟩ := by
  apply Semantics.EvalFunction.body (control := .fault fault) rfl
  apply with_setup effects external
  apply Semantics.EvalStatements.stop
  · intros; intro same; cases same
  · apply Semantics.EvalStmt.forLoop rfl
    apply Semantics.EvalLoop.postStop (value := .bool true) (bodyControl := .fallthrough) (.bool rfl) rfl
    · apply Semantics.EvalStatements.next
      · intros; intro same; cases same
      · exact write_total effects external 7 11 "11" rfl
      · exact .nil
    · exact Or.inl rfl
    · apply Semantics.EvalStatements.next
      · intros; intro same; cases same
      · exact write_total effects external 11 13 "13" rfl
      · apply Semantics.EvalStatements.stop
        · intros; intro same; cases same
        · exact .expressionFault rfl (missing_word_call effects _ _)
        · intro same; cases same
    · exact Or.inr ⟨fault, rfl⟩
  · intro same; cases same

/-- Every genuine checkpoint chain retains the exact source fault reason and
all allocations and writes preceding it. Insufficient fuel remains resumable. -/
def PublicFaultResult (prepared : ScalarExecution.Prepared) (heap : Semantics.Heap) : Prop :=
  ∃ world finalStore required,
    HeapRel world heap finalStore ∧
    ∀ fuel additional last, ScalarExecution.Resumes (ScalarExecution.run prepared fuel) additional last →
      (last = .done (.inLeft prepared.compiled.result (.word reason)) finalStore ↔ required ≤ fuel + additional) ∧
      ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required)

private theorem public_fixture {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {entry : String} {function : Function} {heap : Semantics.Heap}
    (selected : program.functions.find? (·.name == entry) = some function)
    (arity : function.args = [])
    (source : Semantics.EvalFunction program.functions effects function [] ⟨[], external⟩
      (.fault fault) ⟨heap, external⟩)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program entry [] 96 = .ok prepared) :
    PublicFaultResult prepared heap := by
  have parameters : prepared.compiled.parameters = [] := by
    obtain ⟨compiled, argument, checked, _, rfl⟩ := ScalarExecution.prepare_components accepted
    obtain ⟨own, allocated, assembled, rfl⟩ := StatementCorrespondence.compile_components checked
    obtain ⟨signatures, codes, sourceFunction, code, index, _, sourceSelected, signatureCompiled, _⟩ :=
      assemble_selection assembled
    have same := Option.some.inj (selected.symm.trans sourceSelected)
    subst sourceFunction
    obtain ⟨lengths, _⟩ := StatementCorrespondence.signature_components signatureCompiled
    rw [arity] at lengths
    exact List.eq_nil_of_length_eq_zero lengths.symm
  obtain ⟨sourceFunction, sources, sourceSelected, inputs, execute⟩ :=
    prepare_recursive_program_resumes accepted program_eligible external (effects := effects)
  have same := Option.some.inj (selected.symm.trans sourceSelected)
  subst sourceFunction
  rw [parameters] at inputs
  cases inputs
  obtain ⟨world, target, finalStore, required, related, heapRelated, completed⟩ :=
    execute _ _ source
  cases related
  exact ⟨world, finalStore, required, heapRelated, completed⟩

/-- The operational premise is actual public preparation; this theorem supplies
its independent missing-return execution rather than assuming it. -/
theorem missing_word_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "missingWord" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 17)] :=
  public_fixture effects external (function := missingWord) rfl rfl (missing_word_source effects _) accepted

theorem named_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "namedFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 17)] :=
  public_fixture effects external (function := namedFault) rfl rfl (named_fault_source effects external) accepted

theorem argument_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "argumentFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 17)] :=
  public_fixture effects external (function := argumentFault) rfl rfl (argument_fault_source effects external) accepted

theorem pair_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "pairFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 7), .word (word 17)] :=
  public_fixture effects external (function := pairFault) rfl rfl (pair_fault_source effects external) accepted

theorem named_arguments_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "namedArgumentsFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 7), .word (word 17)] :=
  public_fixture effects external (function := namedArgumentsFault) rfl rfl
    (named_arguments_fault_source effects external) accepted

theorem assignment_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "assignmentFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 7), .word (word 17)] :=
  public_fixture effects external (function := assignmentFault) rfl rfl (assignment_fault_source effects external) accepted

theorem condition_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "conditionFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 7), .word (word 17)] :=
  public_fixture effects external (function := conditionFault) rfl rfl (condition_fault_source effects external) accepted

theorem body_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "bodyFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 11), .word (word 17)] :=
  public_fixture effects external (function := bodyFault) rfl rfl (body_fault_source effects external) accepted

theorem post_fault_public {σ : Type} (effects : Semantics.ExternalSemantics σ) (external : σ)
    {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program "postFault" [] 96 = .ok prepared) :
    PublicFaultResult prepared [.word (word 13), .word (word 17)] :=
  public_fixture effects external (function := postFault) rfl rfl (post_fault_source effects external) accepted

private def check (entry : String) (heap : List Semantics.Value) (loopCells : Nat) : IO Unit := do
  let prepared ← match ScalarExecution.prepare program entry [] 96 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"fault correspondence: {entry} preparation failed: {reprStr error}")
  let checkpoint ← match ScalarExecution.run prepared 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"fault correspondence: {entry} zero fuel completed: {reprStr result}")
  let checkpoint ← match ScalarExecution.resume checkpoint 17 with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"fault correspondence: {entry} short resume completed: {reprStr result}")
  match ScalarExecution.resume checkpoint 100000 with
  | .done (.inLeft _ (.word actual)) store =>
      unless actual == reason do throw (IO.userError s!"fault correspondence: {entry} wrong fault reason")
      unless store.length == program.functions.length + loopCells + heap.length do
        throw (IO.userError s!"fault correspondence: {entry} wrong allocation count")
      let sourceCells := store.filterMap fun cell => match cell with
        | .inRight .unit (.word value) => some (Semantics.Value.word value)
        | _ => none
      unless sourceCells == heap do throw (IO.userError s!"fault correspondence: {entry} wrong source heap")
  | result => throw (IO.userError s!"fault correspondence: {entry} resume failed: {reprStr result}")

def run : IO Unit := do
  check "missingWord" [.word (word 17)] 0
  check "namedFault" [.word (word 17)] 0
  check "argumentFault" [.word (word 17)] 0
  check "namedArgumentsFault" [.word (word 7), .word (word 17)] 0
  check "pairFault" [.word (word 7), .word (word 17)] 0
  check "assignmentFault" [.word (word 7), .word (word 17)] 0
  check "conditionFault" [.word (word 7), .word (word 17)] 1
  check "bodyFault" [.word (word 11), .word (word 17)] 1
  check "postFault" [.word (word 13), .word (word 17)] 1

end Tests.RustHullFaultCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullNestedChildCallCorrespondence
/-! Two compiled catalog entries execute a finite nested call tree. Local
memory survives descendants, while each account checkpoint controls shared
storage and event commit independently of returned data. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.RustHullNestedChildCallCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where | committed | grandchildReverted | childReverted
  deriving DecidableEq, Repr
inductive Role where | parent | child | grandchild
  deriving DecidableEq, Repr
private abbrev w := Core.Word.ofNatModulo
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def address : Role → Core.Word | .parent => w 0 | .child => w 100 | .grandchild => w 200
def height : Role → Nat | .parent => 2 | .child => 1 | .grandchild => 0
def image : Role → Option (List UInt8) | .parent => none | .child => some [0x60, 0x00] | .grandchild => some [0x60, 0x01]
def seedOffset : Role → Core.Word | .parent => w 6 | .child => w 3 | .grandchild => w 0
def seedByte : Role → Core.Word | .parent => w 170 | .child => w 187 | .grandchild => w 204
def storageKey : Role → Core.Word | .parent => w 7 | .child => w 8 | .grandchild => w 9
def storageValue : Role → Core.Word | .parent => w 42 | .child => w 99 | .grandchild => w 77
def outputLength : Role → Core.Word | .parent => w 4 | _ => w 1
def returnLength : Role → Core.Word | .parent => w 7 | .child => w 4 | .grandchild => w 1
def target : Role → Core.Word | .parent => w 100 | _ => w 200
def reverts (scenario : Scenario) : Role → Bool
  | .parent => false | .child => scenario = .childReverted | .grandchild => scenario = .grandchildReverted

def seed : Role → Expr
  | .parent => call .unit "mstore8" [word "6", word "170"]
  | .child => call .unit "mstore8" [word "3", word "187"]
  | .grandchild => call .unit "mstore8" [word "0", word "204"]
def storageWrite : Role → Expr
  | .parent => call .unit "sstore" [word "7", word "42"]
  | .child => call .unit "sstore" [word "8", word "99"]
  | .grandchild => call .unit "sstore" [word "9", word "77"]
def event : Role → Expr
  | .parent => call .unit "log0" [word "6", word "1"]
  | .child => call .unit "log0" [word "3", word "1"]
  | .grandchild => call .unit "log0" [word "0", word "1"]
def invoke : Role → Expr
  | .parent => call .word "call" [word "100", word "100", word "0", word "0", word "0", word "2", word "4"]
  | _ => call .word "call" [word "100", word "200", word "0", word "0", word "0", word "2", word "1"]
def storedStatus (role : Role) : Expr := call .unit "mstore8" [word "0", invoke role]
def storedSize : Expr := call .unit "mstore8" [word "1", call .word "returndatasize" []]
def finish (scenario : Scenario) (role : Role) : Expr :=
  call .unit (if reverts scenario role then "revert" else "return")
    [word "0", word (match role with | .parent => "7" | .child => "4" | .grandchild => "1")]
def code (scenario : Scenario) (role : Role) : CodeBlock := {
  stmts := [expression (seed role), expression (storageWrite role), expression (event role)] ++
    (if role = .grandchild then [] else [expression (storedStatus role), expression storedSize]) ++
    [expression (finish scenario role)], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Parent" (code scenario .parent) [],
    .object "Child" (code scenario .child) [], .object "Grandchild" (code scenario .grandchild) []]}
def compiledCatalog (scenario : Scenario) : List AccountRuntime.CodeDefinition := [
  {program := program scenario, path := ["Child"], bytes := (image .child).getD []},
  {program := program scenario, path := ["Grandchild"], bytes := (image .grandchild).getD []}]
def sourceCode (scenario : Scenario) (role : Role) : ChildFrameSemantics.Code :=
  ⟨program scenario, code scenario role, (image role).getD []⟩
def catalog (scenario : Scenario) : ChildFrameSemantics.Catalog :=
  [(w 100, sourceCode scenario .child), (w 200, sourceCode scenario .grandchild)]
def effects (scenario : Scenario) (role : Role) := ChildFrameSemantics.effectsAt (catalog scenario) (height role) (image role)
def childAccount : AccountState.Account := {address := w 100, code := image .child, nonce := w 1}
def grandchildAccount : AccountState.Account := {address := w 200, code := image .grandchild, nonce := w 1}
def context : Contract.Context := {world := [childAccount, grandchildAccount], completeWorld := true}
abbrev SourceState := Semantics.State RuntimeCallEffectsSemantics.State

def runtime (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withRuntime (state : SourceState) (next : RuntimeEffectsSemantics.State) : SourceState :=
  {state with external := {state.external with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime next}}
def seeded (state : SourceState) (role : Role) : SourceState :=
  withRuntime state {runtime state with memory := (MemorySemantics.mstore8 (runtime state).memory (seedOffset role) (seedByte role)).2}
def stored (state : SourceState) (role : Role) : SourceState :=
  withRuntime state {runtime state with storage := (StorageSemantics.store (runtime state).storage (storageKey role) (storageValue role) false).2}
def logWords (state : LogsSemantics.State) (offset : Core.Word) : LogsSemantics.Words :=
  MemorySemantics.insert (state.cursor.add (w 3)) (LogsSemantics.paddedWord state.memory.words offset (w 1))
    (LogsSemantics.insertWords state.words state.cursor (LogsSemantics.headers state.address (w 1) []))
def logged (state : SourceState) (role : Role) : SourceState :=
  let old := state.external.runtime.runtime.runtime
  let logs := RuntimeLogEffectsSemantics.logsState old
  let next := RuntimeLogEffectsSemantics.withLogs old {logs with words := logWords logs (seedOffset role), cursor := LogsSemantics.nextCursor logs.cursor (w 1) []}
  {state with external := {state.external with runtime := {state.external.runtime with runtime := {state.external.runtime.runtime with runtime := next}}}}
def preparedFrame (state : SourceState) (role : Role) : SourceState := logged (stored (seeded state role) role) role

def arguments (state : SourceState) (role : Role) : CallTransportSemantics.Arguments :=
  RuntimeCallEffectsSemantics.arguments .ordinary state.external (w 100) (target role) (w 0) (w 0) (w 0) (w 2) (outputLength role)
def request (state : SourceState) (role : Role) : AccountCallSemantics.Request :=
  CallTransportSemantics.request (arguments state role) []
def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState none object (Contract.normalizeContext context)⟩
def parentPrefix (object : Contract.CompiledObject) : SourceState := preparedFrame (initial object) .parent
def childInitial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ChildFrameSemantics.initial (parentPrefix object).external (request (parentPrefix object) .parent)
    (RuntimeCallEffectsSemantics.shared (parentPrefix object).external) ((image .child).getD [])⟩
def childPrefix (object : Contract.CompiledObject) : SourceState := preparedFrame (childInitial object) .child
def grandchildInitial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ChildFrameSemantics.initial (childPrefix object).external (request (childPrefix object) .child)
    (RuntimeCallEffectsSemantics.shared (childPrefix object).external) ((image .grandchild).getD [])⟩
def grandchildPrefix (object : Contract.CompiledObject) : SourceState := preparedFrame (grandchildInitial object) .grandchild

def terminated (state : SourceState) (scenario : Scenario) (role : Role) : SourceState :=
  withRuntime state (TerminationSemantics.terminate (runtime state) (if reverts scenario role then 2 else 1) (w 0) (returnLength role)).2
def grandchildFinal (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  terminated (grandchildPrefix object) scenario .grandchild

def response (state : SourceState) (scenario : Scenario) (role : Role) : AccountCallSemantics.Response :=
  ⟨!(reverts scenario role), MemorySnapshotSemantics.aligned (runtime state).memory.words (w 0) (returnLength role), returnLength role⟩
def grandchildResponse (object : Contract.CompiledObject) (scenario : Scenario) := response (grandchildFinal object scenario) scenario .grandchild

def copyFour (source destination : MemorySemantics.Entries) : MemorySemantics.Entries :=
  MemorySemantics.writeByte (MemorySemantics.writeByte
    (MemorySemantics.writeByte (MemorySemantics.writeByte destination (w 2) (MemoryCopySemantics.readByte source (w 0)))
      (w 3) (MemoryCopySemantics.readByte source (w 1))) (w 4) (MemoryCopySemantics.readByte source (w 2)))
    (w 5) (MemoryCopySemantics.readByte source (w 3))

def transportAfter (state : SourceState) (role : Role) (answer : AccountCallSemantics.Response) : CallTransportSemantics.State :=
  let count := CallTransportSemantics.copiedLength (arguments state role) answer
  ⟨{(runtime state).memory with words := match role with | .parent => copyFour answer.data (runtime state).memory.words | _ => MemoryCopySemantics.written (runtime state).memory.words (w 2) count (MemoryCopySemantics.copiedWord answer.data (w 0) count)}, answer.data, answer.size⟩
def afterCall (state : SourceState) (role : Role) (child : SourceState) (answer : AccountCallSemantics.Response) : SourceState :=
  let shared := RuntimeCallEffectsSemantics.shared (if answer.success then child.external else state.external)
  {state with external := RuntimeCallEffectsSemantics.withTransport state.external (transportAfter state role answer) shared}
def afterStatus (state : SourceState) (answer : AccountCallSemantics.Response) : SourceState :=
  withRuntime state {runtime state with memory := (MemorySemantics.mstore8 (runtime state).memory (w 0) (w (if answer.success then 1 else 0))).2}
def afterSize (state : SourceState) (answer : AccountCallSemantics.Response) : SourceState :=
  withRuntime state {runtime state with memory := (MemorySemantics.mstore8 (runtime state).memory (w 1) answer.size).2}
def childAfterCall (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  afterCall (childPrefix object) .child (grandchildFinal object scenario) (grandchildResponse object scenario)
def childAfterStatus (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  afterStatus (childAfterCall object scenario) (grandchildResponse object scenario)
def childAfterSize (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  afterSize (childAfterStatus object scenario) (grandchildResponse object scenario)
def childFinal (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  terminated (childAfterSize object scenario) scenario .child
def childResponse (object : Contract.CompiledObject) (scenario : Scenario) := response (childFinal object scenario) scenario .child

def parentAfterCall (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  afterCall (parentPrefix object) .parent (childFinal object scenario) (childResponse object scenario)
def parentAfterStatus (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  afterStatus (parentAfterCall object scenario) (childResponse object scenario)
def parentAfterSize (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  afterSize (parentAfterStatus object scenario) (childResponse object scenario)
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  terminated (parentAfterSize object scenario) scenario .parent

def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

def roleInitial (object : Contract.CompiledObject) : Role → SourceState
  | .parent => initial object | .child => childInitial object | .grandchild => grandchildInitial object

def functions (scenario : Scenario) (role : Role) : List Function := [AccountRuntime.frameFunction (code scenario role)]

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) (role : Role) :
    Semantics.EvalExpr (functions scenario role) (effects scenario role) [] (seed role)
      (roleInitial object role) (.value .unit) (seeded (roleInitial object role) role) := by
  cases role <;> apply Semantics.EvalExpr.call rfl
  all_goals first
    | exact .cons (.word (text := "6") rfl) (.cons (.word (text := "170") rfl) .nil)
    | exact .cons (.word (text := "3") rfl) (.cons (.word (text := "187") rfl) .nil)
    | exact .cons (.word (text := "0") rfl) (.cons (.word (text := "204") rfl) .nil)
    | exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem storage_source (object : Contract.CompiledObject) (scenario : Scenario) (role : Role) :
    Semantics.EvalExpr (functions scenario role) (effects scenario role) [] (storageWrite role)
      (seeded (roleInitial object role) role) (.value .unit) (stored (seeded (roleInitial object role) role) role) := by
  cases role <;> apply Semantics.EvalExpr.call rfl
  all_goals first
    | exact .cons (.word (text := "7") rfl) (.cons (.word (text := "42") rfl) .nil)
    | exact .cons (.word (text := "8") rfl) (.cons (.word (text := "99") rfl) .nil)
    | exact .cons (.word (text := "9") rfl) (.cons (.word (text := "77") rfl) .nil)
    | exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem log_copied (state : LogsSemantics.State) (offset : Core.Word) :
    LogsSemantics.Copy state.memory.words offset (w 1)
      (LogsSemantics.insertWords state.words state.cursor (LogsSemantics.headers state.address (w 1) []))
      (state.cursor.add (w 3)) (logWords state offset) := by
  apply LogsSemantics.Copy.step (by decide +kernel)
  exact .empty _ _ _

private theorem log_source (object : Contract.CompiledObject) (scenario : Scenario) (role : Role) :
    Semantics.EvalExpr (functions scenario role) (effects scenario role) [] (event role)
      (stored (seeded (roleInitial object role) role) role) (.value .unit) (preparedFrame (roleInitial object role) role) := by
  cases role
  all_goals
    apply Semantics.EvalExpr.call rfl
    · first
        | exact .cons (.word (text := "6") rfl) (.cons (.word (text := "1") rfl) .nil)
        | exact .cons (.word (text := "3") rfl) (.cons (.word (text := "1") rfl) .nil)
        | exact .cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil)
    · apply Semantics.EvalCall.external (by rfl) rfl
      apply RuntimeCallEffectsSemantics.Builtin.runtime
      apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
      apply RuntimeCodeEffectsSemantics.Builtin.runtime
      apply RuntimeAccountEffectsSemantics.Builtin.runtime
      apply RuntimeHashEffectsSemantics.Builtin.runtime
      apply RuntimeCopyEffectsSemantics.Builtin.runtime
      apply RuntimeFullEffectsSemantics.Builtin.runtime
      apply RuntimeLogEffectsSemantics.Builtin.logs
      first
        | apply LogsSemantics.Builtin.log .log0 .unit (w 6) (w 1) [] rfl
        | apply LogsSemantics.Builtin.log .log0 .unit (w 3) (w 1) [] rfl
        | apply LogsSemantics.Builtin.log .log0 .unit (w 0) (w 1) [] rfl
      apply LogsSemantics.Execute.writable rfl
      apply LogsSemantics.Append.done (size := w 32)
      · decide +kernel
      · first
          | change ¬w 0 > LogsSemantics.nextCursor (w 0) (w 1) []; decide +kernel
          | change ¬w 4 > LogsSemantics.nextCursor (w 4) (w 1) []; decide +kernel
          | change ¬w 8 > LogsSemantics.nextCursor (w 8) (w 1) []; decide +kernel
      · first
          | change MemorySemantics.touchSize? (w 32) (w 6) (w 1) = some (w 32); decide +kernel
          | change MemorySemantics.touchSize? (w 32) (w 3) (w 1) = some (w 32); decide +kernel
          | change MemorySemantics.touchSize? (w 32) (w 0) (w 1) = some (w 32); decide +kernel
      · exact log_copied _ _

def beforeFinish (object : Contract.CompiledObject) (scenario : Scenario) : Role → SourceState
  | .parent => parentAfterSize object scenario | .child => childAfterSize object scenario | .grandchild => grandchildPrefix object

def finishedState (object : Contract.CompiledObject) (scenario : Scenario) : Role → SourceState
  | .parent => finalState object scenario | .child => childFinal object scenario | .grandchild => grandchildFinal object scenario

private theorem finish_source (object : Contract.CompiledObject) (scenario : Scenario) (role : Role) :
    Semantics.EvalExpr (functions scenario role) (effects scenario role) [] (finish scenario role)
      (beforeFinish object scenario role) result (finishedState object scenario role) := by
  cases role <;> cases scenario <;> apply Semantics.EvalExpr.call rfl
  all_goals first
    | exact .cons (.word (text := "0") rfl) (.cons (.word (text := "7") rfl) .nil)
    | exact .cons (.word (text := "0") rfl) (.cons (.word (text := "4") rfl) .nil)
    | exact .cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil)
    | exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem grandchild_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario .grandchild) (effects scenario .grandchild)
      (AccountRuntime.frameFunction (code scenario .grandchild)) [] (grandchildInitial object) result (grandchildFinal object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object scenario .grandchild))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (storage_source object scenario .grandchild))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (log_source object scenario .grandchild))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (finish_source object scenario .grandchild))
    (by intro impossible; cases impossible)

private theorem grandchild_response (object : Contract.CompiledObject) (scenario : Scenario) :
    ChildResultSemantics.Respond (ChildFrameSemantics.completedStatus result (runtime (grandchildFinal object scenario)))
      (runtime (grandchildFinal object scenario)) (.value (grandchildResponse object scenario)) := by
  cases scenario
  all_goals
    first
      | apply ChildResultSemantics.Respond.returned (data := .value (MemorySnapshotSemantics.aligned (runtime (grandchildPrefix object)).memory.words (w 0) (w 1))) rfl
      | apply ChildResultSemantics.Respond.reverted (data := .value (MemorySnapshotSemantics.aligned (runtime (grandchildPrefix object)).memory.words (w 0) (w 1))) rfl
    apply MemorySnapshotSemantics.Extract.aligned (size := w 32)
    · change MemorySemantics.touchSize? (w 0) (w 0) (w 1) = some (w 32)
      decide +kernel
    · change w 1 ≠ w 0
      decide +kernel
    · rfl

theorem grandchild_called (object : Contract.CompiledObject) (scenario : Scenario) :
    ChildFrameSemantics.Children (catalog scenario) (ChildFrameSemantics.effectsAt (catalog scenario) 0)
      (childPrefix object).external .ordinary (runtime (childPrefix object)).storage.address (request (childPrefix object) .child)
      (RuntimeCallEffectsSemantics.shared (childPrefix object).external) (.value (grandchildResponse object scenario))
      (RuntimeCallEffectsSemantics.shared (grandchildFinal object scenario).external) := by
  apply ChildFrameSemantics.Children.executed (account := grandchildAccount) (code := sourceCode scenario .grandchild)
  · change AccountCallSemantics.isPrecompile (w 200) = false
    decide +kernel
  · rfl
  · rfl
  · rfl
  · exact grandchild_source object scenario
  · exact grandchild_response object scenario

private theorem grandchild_output (object : Contract.CompiledObject) (scenario : Scenario) :
    MemoryCopySemantics.From (grandchildResponse object scenario).data (w 2) (w 0)
      (CallTransportSemantics.copiedLength (arguments (childPrefix object) .child) (grandchildResponse object scenario))
      (runtime (childPrefix object)).memory (.value .unit)
      (transportAfter (childPrefix object) .child (grandchildResponse object scenario)).memory := by
  cases scenario
  all_goals
    change MemoryCopySemantics.From _ (w 2) (w 0) (w 1) _ _ _
    apply MemoryCopySemantics.From.done
    · change MemorySemantics.touchSize? (w 32) (w 2) (w 1) = some (w 32)
      decide +kernel
    · apply MemoryCopySemantics.Copy.step (by decide +kernel)
      change MemoryCopySemantics.Copy _ _ _ ((w 1).sub (w 1)) _ _
      rw [show (w 1).sub (w 1) = Core.Word.zero from by decide +kernel]
      exact .empty _ _ _ _

private theorem child_invoked (object : Contract.CompiledObject) (scenario : Scenario) :
    RuntimeCallEffectsSemantics.Call
      (ChildFrameSemantics.Children (catalog scenario) (ChildFrameSemantics.effectsAt (catalog scenario) 0)) .ordinary
      (w 100) (w 200) (w 0) (w 0) (w 0) (w 2) (w 1) (childPrefix object).external
      (.value (.word (w (if (grandchildResponse object scenario).success then 1 else 0))))
      (childAfterCall object scenario).external := by
  apply RuntimeCallEffectsSemantics.Call.invoked (.inr (.inl rfl))
  · intros ordinary nonzero
    exact False.elim (nonzero rfl)
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 32)
  · rfl
  · change MemorySemantics.touchSize? (w 32) (w 2) (w 1) = some (w 32)
    decide +kernel
  apply CallTransportSemantics.Dispatch.returned (input := {}) (response := grandchildResponse object scenario) (result := .value .unit)
  · change ¬w 1 > w 1023
    decide +kernel
  · exact .done rfl (.empty _ _ _ _)
  · rfl
  · cases scenario
    case grandchildReverted =>
      apply AccountCallSemantics.Dispatch.refused (transferred := RuntimeCallEffectsSemantics.shared (childPrefix object).external)
      · exact .inr (by change ¬w 0 > w 0; decide +kernel)
      · rfl
      · exact .child (grandchild_called object .grandchildReverted)
      · rfl
    all_goals
      apply AccountCallSemantics.Dispatch.succeeded (transferred := RuntimeCallEffectsSemantics.shared (childPrefix object).external)
      · exact .inr (by change ¬w 0 > w 0; decide +kernel)
      · rfl
      · first | exact .child (grandchild_called object .committed) | exact .child (grandchild_called object .childReverted)
      · rfl
  · exact grandchild_output object scenario

private theorem child_call_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario .child) (effects scenario .child) [] (invoke .child)
      (childPrefix object) (.value (.word (w (if (grandchildResponse object scenario).success then 1 else 0))))
      (childAfterCall object scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "200") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "1") rfl) .nil)))))))
  · exact .external (by rfl) rfl (.call (child_invoked object scenario))

private theorem child_status_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario .child) (effects scenario .child) [] (storedStatus .child)
      (childPrefix object) (.value .unit) (childAfterStatus object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (child_call_source object scenario) .nil))
  exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem size_builtin (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children)
    (bytes : Option (List UInt8)) (state : RuntimeCallEffectsSemantics.State) :
    RuntimeCallEffectsSemantics.Builtin children bytes "returndatasize" .word [] state
      (.value (.word (RuntimeReturnDataEffectsSemantics.size state.runtime))) state := by
  exact .runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))))

private theorem byte_builtin (children : RuntimeCallEffectsSemantics.State → AccountCallSemantics.Children)
    (bytes : Option (List UInt8)) (state : SourceState) (offset value size : Core.Word)
    (touched : MemorySemantics.touchSize? (runtime state).memory.size offset (w 1) = some size) :
    RuntimeCallEffectsSemantics.Builtin children bytes "mstore8" .unit [.word offset, .word value] state.external
      (.value .unit) (withRuntime state {runtime state with memory := (MemorySemantics.mstore8 (runtime state).memory offset value).2}).external := by
  apply RuntimeCallEffectsSemantics.Builtin.runtime
  apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
  apply RuntimeCodeEffectsSemantics.Builtin.runtime
  apply RuntimeAccountEffectsSemantics.Builtin.runtime
  apply RuntimeHashEffectsSemantics.Builtin.runtime
  apply RuntimeCopyEffectsSemantics.Builtin.runtime
  apply RuntimeFullEffectsSemantics.Builtin.runtime
  apply RuntimeLogEffectsSemantics.Builtin.runtime
  simp only [runtime] at touched
  simp only [RuntimeEnvironmentEffectsSemantics.builtin, RuntimeEffectsSemantics.builtin,
    MemorySemantics.builtin, MemorySemantics.mstore8, runtime, touched]

private theorem child_size_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario .child) (effects scenario .child) [] storedSize
      (childAfterStatus object scenario) (.value .unit) (childAfterSize object scenario) := by
  have observed : Semantics.EvalExpr (functions scenario .child) (effects scenario .child) []
      (call .word "returndatasize" []) (childAfterStatus object scenario)
      (.value (.word (grandchildResponse object scenario).size)) (childAfterStatus object scenario) := by
    apply Semantics.EvalExpr.call rfl .nil
    exact .external (by rfl) rfl (size_builtin _ _ _)
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "1") rfl) (.cons observed .nil))
  apply Semantics.EvalCall.external (by rfl) rfl
  apply byte_builtin (size := w 32)
  change MemorySemantics.touchSize? (w 32) (w 1) (w 1) = some (w 32)
  decide +kernel

theorem child_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario .child) (effects scenario .child)
      (AccountRuntime.frameFunction (code scenario .child)) [] (childInitial object) result (childFinal object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object scenario .child))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (storage_source object scenario .child))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (log_source object scenario .child))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_status_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_size_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (finish_source object scenario .child))
    (by intro impossible; cases impossible)

private theorem child_response (object : Contract.CompiledObject) (scenario : Scenario) :
    ChildResultSemantics.Respond (ChildFrameSemantics.completedStatus result (runtime (childFinal object scenario)))
      (runtime (childFinal object scenario)) (.value (childResponse object scenario)) := by
  cases scenario
  case committed =>
    apply ChildResultSemantics.Respond.returned (data := .value (childResponse object .committed).data) rfl
    apply MemorySnapshotSemantics.Extract.aligned (size := w 32)
    · change MemorySemantics.touchSize? (w 0) (w 0) (w 4) = some (w 32)
      decide +kernel
    · change w 4 ≠ w 0
      decide +kernel
    · rfl
  case grandchildReverted =>
    apply ChildResultSemantics.Respond.returned (data := .value (childResponse object .grandchildReverted).data) rfl
    apply MemorySnapshotSemantics.Extract.aligned (size := w 32)
    · change MemorySemantics.touchSize? (w 0) (w 0) (w 4) = some (w 32)
      decide +kernel
    · change w 4 ≠ w 0
      decide +kernel
    · rfl
  case childReverted =>
    apply ChildResultSemantics.Respond.reverted (data := .value (childResponse object .childReverted).data) rfl
    apply MemorySnapshotSemantics.Extract.aligned (size := w 32)
    · change MemorySemantics.touchSize? (w 0) (w 0) (w 4) = some (w 32)
      decide +kernel
    · change w 4 ≠ w 0
      decide +kernel
    · rfl

theorem child_called (object : Contract.CompiledObject) (scenario : Scenario) :
    ChildFrameSemantics.Children (catalog scenario) (ChildFrameSemantics.effectsAt (catalog scenario) 1)
      (parentPrefix object).external .ordinary (w 0) (request (parentPrefix object) .parent)
      (RuntimeCallEffectsSemantics.shared (parentPrefix object).external) (.value (childResponse object scenario))
      (RuntimeCallEffectsSemantics.shared (childFinal object scenario).external) := by
  apply ChildFrameSemantics.Children.executed (account := childAccount) (code := sourceCode scenario .child)
  · change AccountCallSemantics.isPrecompile (w 100) = false
    decide +kernel
  · rfl
  · rfl
  · rfl
  · exact child_source object scenario
  · exact child_response object scenario


private theorem copyFour_source (source destination : MemorySemantics.Entries) :
    MemoryCopySemantics.From source (w 2) (w 0) (w 4) ⟨destination, w 32⟩ (.value .unit)
      ⟨copyFour source destination, w 32⟩ := by
  apply MemoryCopySemantics.From.done
  · change MemorySemantics.touchSize? (w 32) (w 2) (w 4) = some (w 32)
    decide +kernel
  · apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    exact .empty _ _ _ _

private theorem child_output (object : Contract.CompiledObject) (scenario : Scenario) :
    MemoryCopySemantics.From (childResponse object scenario).data (w 2) (w 0)
      (CallTransportSemantics.copiedLength (arguments (parentPrefix object) .parent) (childResponse object scenario))
      (runtime (parentPrefix object)).memory (.value .unit)
      (transportAfter (parentPrefix object) .parent (childResponse object scenario)).memory := by
  exact copyFour_source _ _

private theorem parent_invoked (object : Contract.CompiledObject) (scenario : Scenario) :
    RuntimeCallEffectsSemantics.Call
      (ChildFrameSemantics.Children (catalog scenario) (ChildFrameSemantics.effectsAt (catalog scenario) 1)) .ordinary
      (w 100) (w 100) (w 0) (w 0) (w 0) (w 2) (w 4) (parentPrefix object).external
      (.value (.word (w (if (childResponse object scenario).success then 1 else 0))))
      (parentAfterCall object scenario).external := by
  apply RuntimeCallEffectsSemantics.Call.invoked (.inr (.inl rfl))
  · intros ordinary nonzero
    exact False.elim (nonzero rfl)
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 32)
  · rfl
  · change MemorySemantics.touchSize? (w 32) (w 2) (w 4) = some (w 32)
    decide +kernel
  apply CallTransportSemantics.Dispatch.returned (input := {}) (response := childResponse object scenario) (result := .value .unit)
  · change ¬w 0 > w 1023
    decide +kernel
  · exact .done rfl (.empty _ _ _ _)
  · rfl
  · cases scenario
    case childReverted =>
      apply AccountCallSemantics.Dispatch.refused (transferred := RuntimeCallEffectsSemantics.shared (parentPrefix object).external)
      · exact .inr (by change ¬w 0 > w 0; decide +kernel)
      · rfl
      · exact .child (child_called object .childReverted)
      · rfl
    all_goals
      apply AccountCallSemantics.Dispatch.succeeded (transferred := RuntimeCallEffectsSemantics.shared (parentPrefix object).external)
      · exact .inr (by change ¬w 0 > w 0; decide +kernel)
      · rfl
      · first | exact .child (child_called object .committed) | exact .child (child_called object .grandchildReverted)
      · rfl
  · exact child_output object scenario

private theorem parent_call_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario .parent) (effects scenario .parent) [] (invoke .parent)
      (parentPrefix object) (.value (.word (w (if (childResponse object scenario).success then 1 else 0))))
      (parentAfterCall object scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "4") rfl) .nil)))))))
  · exact .external (by rfl) rfl (.call (parent_invoked object scenario))

private theorem parent_status_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario .parent) (effects scenario .parent) [] (storedStatus .parent)
      (parentPrefix object) (.value .unit) (parentAfterStatus object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (parent_call_source object scenario) .nil))
  exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))


private theorem parent_size_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario .parent) (effects scenario .parent) [] storedSize
      (parentAfterStatus object scenario) (.value .unit) (parentAfterSize object scenario) := by
  have observed : Semantics.EvalExpr (functions scenario .parent) (effects scenario .parent) []
      (call .word "returndatasize" []) (parentAfterStatus object scenario)
      (.value (.word (childResponse object scenario).size)) (parentAfterStatus object scenario) := by
    apply Semantics.EvalExpr.call rfl .nil
    exact .external (by rfl) rfl (size_builtin _ _ _)
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "1") rfl) (.cons observed .nil))
  apply Semantics.EvalCall.external (by rfl) rfl
  apply byte_builtin (size := w 32)
  change MemorySemantics.touchSize? (w 32) (w 1) (w 1) = some (w 32)
  decide +kernel

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario .parent) (effects scenario .parent)
      (AccountRuntime.frameFunction (code scenario .parent)) [] (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object scenario .parent))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (storage_source object scenario .parent))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (log_source object scenario .parent))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (parent_status_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (parent_size_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (finish_source object scenario .parent))
    (by intro impossible; cases impossible)



def runtimeNames : List String := ["mstore8", "sstore", "log0", "returndatasize", "return", "revert"]
def usedNames : List String := runtimeNames ++ ["call"]

private theorem atoms {supported : String → Prop} (functions : List Function) (type : Ty) (name : String)
    (arguments : List String) (available : supported name)
    (absent : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (call type name (arguments.map word)) := by
  apply ExecutableExpression.external (name := name) available absent
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

theorem eligible (scenario : Scenario) (role : Role) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario role) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  cases role
  case parent =>
    change statement ∈ [expression (seed .parent), expression (storageWrite .parent), expression (event .parent), expression (storedStatus .parent), expression storedSize, expression (finish scenario .parent)] at statementMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at statementMember
    rcases statementMember with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [expression, ExecutableStatement]
    · exact atoms _ .unit "mstore8" ["6", "170"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · exact atoms _ .unit "sstore" ["7", "42"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · exact atoms _ .unit "log0" ["6", "1"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .word _ _ _
      · exact atoms _ .word "call" ["100", "100", "0", "0", "0", "2", "4"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .word _ _ _
      · exact atoms _ .word "returndatasize" [] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · cases scenario <;> first
        | exact atoms _ .unit "return" ["0", "7"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
        | exact atoms _ .unit "revert" ["0", "7"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
  case child =>
    change statement ∈ [expression (seed .child), expression (storageWrite .child), expression (event .child), expression (storedStatus .child), expression storedSize, expression (finish scenario .child)] at statementMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at statementMember
    rcases statementMember with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [expression, ExecutableStatement]
    · exact atoms _ .unit "mstore8" ["3", "187"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · exact atoms _ .unit "sstore" ["8", "99"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · exact atoms _ .unit "log0" ["3", "1"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .word _ _ _
      · exact atoms _ .word "call" ["100", "200", "0", "0", "0", "2", "1"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .word _ _ _
      · exact atoms _ .word "returndatasize" [] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · cases scenario <;> first
        | exact atoms _ .unit "return" ["0", "4"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
        | exact atoms _ .unit "revert" ["0", "4"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
  case grandchild =>
    change statement ∈ [expression (seed .grandchild), expression (storageWrite .grandchild), expression (event .grandchild), expression (finish scenario .grandchild)] at statementMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at statementMember
    rcases statementMember with rfl | rfl | rfl | rfl
    all_goals simp only [expression, ExecutableStatement]
    · exact atoms _ .unit "mstore8" ["0", "204"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · exact atoms _ .unit "sstore" ["9", "77"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · exact atoms _ .unit "log0" ["0", "1"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
    · cases scenario <;> first
        | exact atoms _ .unit "return" ["0", "1"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)
        | exact atoms _ .unit "revert" ["0", "1"] (available _ (by simp [usedNames, runtimeNames])) (by rfl)

private theorem runtime_supported : ∀ name ∈ runtimeNames, ContractCodeCorrespondence.supported name := by
  intro name member
  simp only [runtimeNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (⟨.store8, rfl⟩))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.store false, rfl⟩)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inr ⟨.log0, rfl⟩)))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.direct .returnDataSize, rfl, by intro input member; simp [EnvironmentBuiltinCorrespondence.inputs] at member; subst input; simp [Effects.slots, EnvironmentSemantics.Direct.slot]⟩))))))
  · exact .inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))
  · exact .inl (.inl (.inl (.inl (.inr ⟨.reverted, rfl⟩))))

theorem names_supported : ∀ name ∈ usedNames, ContractCallCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with prior | rfl
  · exact .inl (.inl (runtime_supported name prior))
  · exact .inr (.inl rfl)


end Tests.RustHullNestedChildCallCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullCallModeCorrespondence
/-! CALLCODE and DELEGATECALL select another account's code while retaining the
invoking storage address. The returned bytes expose address, caller and value. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.RustHullCallModeCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
private abbrev w := Core.Word.ofNatModulo
inductive Scenario where | callCode | delegated | reverted
  deriving BEq, DecidableEq, Repr
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def operation : Scenario → RuntimeCallModeSemantics.Operation
  | .callCode => .callCode | _ => .delegateCall
def value : Scenario → Core.Word | .callCode => w 5 | _ => w 7
def reverts (scenario : Scenario) : Bool := scenario == .reverted

def byte (offset data : String) : Expr := call .unit "mstore8" [word offset, word data]
def storage (key data : String) : Expr := call .unit "sstore" [word key, word data]
def observedByte (offset name : String) : Expr := call .unit "mstore8" [word offset, call .word name []]
def childFinish (scenario : Scenario) : Expr := call .unit (if reverts scenario then "revert" else "return") [word "0", word "4"]
def childCode (scenario : Scenario) : CodeBlock := {
  stmts := [expression (observedByte "0" "address"), expression (observedByte "1" "caller"),
    expression (observedByte "2" "callvalue"), expression (byte "3" "187"), expression (storage "8" "99"),
    expression (call .unit "log0" [word "3", word "1"]), expression (childFinish scenario)], functions := []}
def invoke : Scenario → Expr
  | .callCode => call .word "callcode" [word "100", word "100", word "5", word "0", word "0", word "2", word "4"]
  | _ => call .word "delegatecall" [word "100", word "100", word "0", word "0", word "2", word "4"]
def storedStatus (scenario : Scenario) : Expr := call .unit "mstore8" [word "0", invoke scenario]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression (byte "6" "170"), expression (storage "7" "42"), expression (storedStatus scenario),
    expression (observedByte "1" "returndatasize"), expression (call .unit "return" [word "0", word "7"])], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Parent" (code scenario) [], .object "Child" (childCode scenario) []]}
def childBytes : List UInt8 := [0x60, 0x00]
def compiledCatalog (scenario : Scenario) : List AccountRuntime.CodeDefinition :=
  [{program := program scenario, path := ["Child"], bytes := childBytes}]
def sourceCode (scenario : Scenario) : ChildFrameSemantics.Code := ⟨program scenario, childCode scenario, childBytes⟩
def catalog (scenario : Scenario) : ChildFrameModeSemantics.Catalog := [(w 100, sourceCode scenario)]
def parentEffects (scenario : Scenario) := ChildFrameModeSemantics.effectsAt (catalog scenario) {} 1 none
def childEffects (scenario : Scenario) := ChildFrameModeSemantics.effectsAt (catalog scenario) {} 0 (some childBytes)
def parentFunctions (scenario : Scenario) := [AccountRuntime.frameFunction (code scenario)]
def childFunctions (scenario : Scenario) := [AccountRuntime.frameFunction (childCode scenario)]
def childAccount : AccountState.Account := {address := w 100, code := some childBytes, nonce := w 1}
def context : Contract.Context := {caller := w 55, value := w 7, balance := w 100, world := [childAccount], completeWorld := true}
abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def runtime (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withRuntime (state : SourceState) (next : RuntimeEffectsSemantics.State) : SourceState :=
  {state with external := {state.external with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime next}}
def written (state : SourceState) (offset data : Core.Word) : SourceState :=
  withRuntime state {runtime state with memory := (MemorySemantics.mstore8 (runtime state).memory offset data).2}
def stored (state : SourceState) (key data : Core.Word) : SourceState :=
  withRuntime state {runtime state with storage := (StorageSemantics.store (runtime state).storage key data false).2}
def initial (object : Contract.CompiledObject) : SourceState := ⟨[], ContractCallCorrespondence.contextInitialState none object (Contract.normalizeContext context)⟩
def parentWritten (object : Contract.CompiledObject) : SourceState := written (initial object) (w 6) (w 170)
def parentBefore (object : Contract.CompiledObject) : SourceState := stored (parentWritten object) (w 7) (w 42)
def arguments (object : Contract.CompiledObject) (scenario : Scenario) :=
  RuntimeCallModeSemantics.arguments (operation scenario) (parentBefore object).external (w 100) (w 100) (value scenario) (w 0) (w 0) (w 2) (w 4)
def request (object : Contract.CompiledObject) (scenario : Scenario) := CallTransportSemantics.request (arguments object scenario) []
def childInitial (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], ChildFrameModeSemantics.initial (operation scenario).mode (w 0) (parentBefore object).external
    (request object scenario) (RuntimeCallModeSemantics.shared (parentBefore object).external) childBytes⟩
def childAddress (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  written (childInitial object scenario) (w 0) ((RuntimeCallModeSemantics.observations (childInitial object scenario).external).direct .address)
def childCaller (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  written (childAddress object scenario) (w 1) ((RuntimeCallModeSemantics.observations (childAddress object scenario).external).direct .caller)
def childValue (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  written (childCaller object scenario) (w 2) ((RuntimeCallModeSemantics.observations (childCaller object scenario).external).direct .callvalue)
def childWritten (object : Contract.CompiledObject) (scenario : Scenario) : SourceState := written (childValue object scenario) (w 3) (w 187)
def childStored (object : Contract.CompiledObject) (scenario : Scenario) : SourceState := stored (childWritten object scenario) (w 8) (w 99)
def childLogged (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := childStored object scenario
  let old := state.external.runtime.runtime.runtime
  let logs := RuntimeLogEffectsSemantics.logsState old
  let next := RuntimeLogEffectsSemantics.withLogs old {logs with
    words := Tests.RustHullNestedChildCallCorrespondence.logWords logs (w 3), cursor := LogsSemantics.nextCursor logs.cursor (w 1) []}
  {state with external := {state.external with runtime := {state.external.runtime with runtime := {state.external.runtime.runtime with runtime := next}}}}
def terminated (state : SourceState) (exit length : Nat) : SourceState :=
  withRuntime state (TerminationSemantics.terminate (runtime state) exit (w 0) (w length)).2
def childFinal (object : Contract.CompiledObject) (scenario : Scenario) := terminated (childLogged object scenario) (if reverts scenario then 2 else 1) 4
def response (object : Contract.CompiledObject) (scenario : Scenario) : AccountCallSemantics.Response :=
  ⟨!reverts scenario, MemorySnapshotSemantics.aligned (runtime (childFinal object scenario)).memory.words (w 0) (w 4), w 4⟩
def transportAfter (object : Contract.CompiledObject) (scenario : Scenario) : CallTransportSemantics.State :=
  ⟨{(runtime (parentBefore object)).memory with words := Tests.RustHullNestedChildCallCorrespondence.copyFour (response object scenario).data (runtime (parentBefore object)).memory.words}, (response object scenario).data, w 4⟩
def afterCall (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := parentBefore object
  {state with external := RuntimeCallModeSemantics.withTransport state.external (transportAfter object scenario) (RuntimeCallModeSemantics.shared (if reverts scenario then state.external else (childFinal object scenario).external))}
def afterStatus (object : Contract.CompiledObject) (scenario : Scenario) := written (afterCall object scenario) (w 0) (w (if reverts scenario then 0 else 1))
def afterSize (object : Contract.CompiledObject) (scenario : Scenario) := written (afterStatus object scenario) (w 1) (w 4)
def finalState (object : Contract.CompiledObject) (scenario : Scenario) := terminated (afterSize object scenario) 1 7
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)



inductive Observation where | address | caller | value | returnSize
private def Observation.direct : Observation → EnvironmentSemantics.Direct
  | .address => .address | .caller => .caller | .value => .callvalue | .returnSize => .returnDataSize
private def Observation.name : Observation → String
  | .address => "address" | .caller => "caller" | .value => "callvalue" | .returnSize => "returndatasize"

private theorem read_source (functions : List Function)
    (children : RuntimeCallModeSemantics.State → AccountCallSemantics.Children)
    (image : Option (List UInt8)) (observation : Observation) (state : SourceState)
    (absent : functions.find? (·.name == observation.name) = none) :
    Semantics.EvalExpr functions (RuntimeCallModeSemantics.effectsWith children image) []
      (call .word observation.name []) state
      (.value (.word ((RuntimeCallModeSemantics.observations state.external).direct observation.direct))) state := by
  cases observation <;> apply Semantics.EvalExpr.call rfl .nil
  all_goals exact .external absent rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem byte_builtin (children : RuntimeCallModeSemantics.State → AccountCallSemantics.Children)
    (image : Option (List UInt8)) (state : SourceState) (offset data size : Core.Word)
    (touched : MemorySemantics.touchSize? (runtime state).memory.size offset (w 1) = some size) :
    RuntimeCallModeSemantics.Builtin children image "mstore8" .unit [.word offset, .word data] state.external
      (.value .unit) (written state offset data).external := by
  apply RuntimeCallModeSemantics.Builtin.runtime
  apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
  apply RuntimeCodeEffectsSemantics.Builtin.runtime
  apply RuntimeAccountEffectsSemantics.Builtin.runtime
  apply RuntimeHashEffectsSemantics.Builtin.runtime
  apply RuntimeCopyEffectsSemantics.Builtin.runtime
  apply RuntimeFullEffectsSemantics.Builtin.runtime
  apply RuntimeLogEffectsSemantics.Builtin.runtime
  simp only [runtime] at touched
  simp only [RuntimeEnvironmentEffectsSemantics.builtin, RuntimeEffectsSemantics.builtin,
    MemorySemantics.builtin, MemorySemantics.mstore8, runtime, touched]

private theorem child_address_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (childFunctions scenario) (childEffects scenario) [] (observedByte "0" "address")
      (childInitial object scenario) (.value .unit) (childAddress object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (read_source _ _ _ .address _ rfl) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply byte_builtin (size := w 32)
  cases scenario <;> change MemorySemantics.touchSize? (w 0) (w 0) (w 1) = some (w 32)
  all_goals decide +kernel

private theorem child_caller_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (childFunctions scenario) (childEffects scenario) [] (observedByte "1" "caller")
      (childAddress object scenario) (.value .unit) (childCaller object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "1") rfl) (.cons (read_source _ _ _ .caller _ rfl) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply byte_builtin (size := w 32)
  cases scenario <;> change MemorySemantics.touchSize? (w 32) (w 1) (w 1) = some (w 32)
  all_goals decide +kernel

private theorem child_value_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (childFunctions scenario) (childEffects scenario) [] (observedByte "2" "callvalue")
      (childCaller object scenario) (.value .unit) (childValue object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "2") rfl) (.cons (read_source _ _ _ .value _ rfl) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply byte_builtin (size := w 32)
  cases scenario <;> change MemorySemantics.touchSize? (w 32) (w 2) (w 1) = some (w 32)
  all_goals decide +kernel

private theorem child_written_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (childFunctions scenario) (childEffects scenario) [] (byte "3" "187")
      (childValue object scenario) (.value .unit) (childWritten object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "3") rfl) (.cons (.word (text := "187") rfl) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply byte_builtin (size := w 32)
  cases scenario <;> change MemorySemantics.touchSize? (w 32) (w 3) (w 1) = some (w 32)
  all_goals decide +kernel

private theorem child_stored_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (childFunctions scenario) (childEffects scenario) [] (storage "8" "99")
      (childWritten object scenario) (.value .unit) (childStored object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "8") rfl) (.cons (.word (text := "99") rfl) .nil))
  cases scenario <;> exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem log_copied (state : LogsSemantics.State) :
    LogsSemantics.Copy state.memory.words (w 3) (w 1)
      (LogsSemantics.insertWords state.words state.cursor (LogsSemantics.headers state.address (w 1) []))
      (state.cursor.add (w 3)) (Tests.RustHullNestedChildCallCorrespondence.logWords state (w 3)) := by
  apply LogsSemantics.Copy.step (by decide +kernel)
  exact .empty _ _ _

private theorem child_logged_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (childFunctions scenario) (childEffects scenario) [] (call .unit "log0" [word "3", word "1"])
      (childStored object scenario) (.value .unit) (childLogged object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "3") rfl) (.cons (.word (text := "1") rfl) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply RuntimeCallModeSemantics.Builtin.runtime
  apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
  apply RuntimeCodeEffectsSemantics.Builtin.runtime
  apply RuntimeAccountEffectsSemantics.Builtin.runtime
  apply RuntimeHashEffectsSemantics.Builtin.runtime
  apply RuntimeCopyEffectsSemantics.Builtin.runtime
  apply RuntimeFullEffectsSemantics.Builtin.runtime
  apply RuntimeLogEffectsSemantics.Builtin.logs
  apply LogsSemantics.Builtin.log .log0 .unit (w 3) (w 1) [] rfl
  apply LogsSemantics.Execute.writable (by cases scenario <;> rfl)
  apply LogsSemantics.Append.done (size := w 32)
  · decide +kernel
  · change ¬w 0 > LogsSemantics.nextCursor (w 0) (w 1) []
    decide +kernel
  · cases scenario <;> change MemorySemantics.touchSize? (w 32) (w 3) (w 1) = some (w 32)
    all_goals decide +kernel
  · exact log_copied _

private theorem child_finish_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (childFunctions scenario) (childEffects scenario) [] (childFinish scenario)
      (childLogged object scenario) result (childFinal object scenario) := by
  cases scenario <;> apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "4") rfl) .nil))
  all_goals exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem child_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (childFunctions scenario) (childEffects scenario) (AccountRuntime.frameFunction (childCode scenario)) []
      (childInitial object scenario) result (childFinal object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_address_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_caller_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_value_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_written_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_stored_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_logged_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (child_finish_source object scenario))
    (by intro impossible; cases impossible)



private theorem child_response (object : Contract.CompiledObject) (scenario : Scenario) :
    ChildResultSemantics.Respond (ChildFrameModeSemantics.completedStatus result (runtime (childFinal object scenario)))
      (runtime (childFinal object scenario)) (.value (response object scenario)) := by
  cases scenario
  case callCode =>
    apply ChildResultSemantics.Respond.returned (data := .value (response object .callCode).data) rfl
    apply MemorySnapshotSemantics.Extract.aligned (size := w 32)
    · change MemorySemantics.touchSize? (w 0) (w 0) (w 4) = some (w 32)
      decide +kernel
    · change w 4 ≠ Core.Word.zero
      decide +kernel
    · rfl
  case delegated =>
    apply ChildResultSemantics.Respond.returned (data := .value (response object .delegated).data) rfl
    apply MemorySnapshotSemantics.Extract.aligned (size := w 32)
    · change MemorySemantics.touchSize? (w 0) (w 0) (w 4) = some (w 32)
      decide +kernel
    · change w 4 ≠ Core.Word.zero
      decide +kernel
    · rfl
  case reverted =>
    apply ChildResultSemantics.Respond.reverted (data := .value (response object .reverted).data) rfl
    apply MemorySnapshotSemantics.Extract.aligned (size := w 32)
    · change MemorySemantics.touchSize? (w 0) (w 0) (w 4) = some (w 32)
      decide +kernel
    · change w 4 ≠ Core.Word.zero
      decide +kernel
    · rfl

theorem child_called (object : Contract.CompiledObject) (scenario : Scenario) :
    ChildFrameModeSemantics.Children (catalog scenario) (ChildFrameModeSemantics.effectsAt (catalog scenario) {} 0)
      (parentBefore object).external (operation scenario).mode (w 0) (request object scenario)
      (RuntimeCallModeSemantics.shared (parentBefore object).external) (.value (response object scenario))
      (RuntimeCallModeSemantics.shared (childFinal object scenario).external) := by
  apply ChildFrameModeSemantics.Children.executed (account := childAccount) (code := sourceCode scenario)
  · cases scenario <;> change AccountCallSemantics.isPrecompile (w 100) = false
    all_goals decide +kernel
  · cases scenario <;> rfl
  · cases scenario <;> rfl
  · rfl
  · exact child_source object scenario
  · exact child_response object scenario

private theorem copyFour_source (source destination : MemorySemantics.Entries) :
    MemoryCopySemantics.From source (w 2) (w 0) (w 4) ⟨destination, w 32⟩ (.value .unit)
      ⟨Tests.RustHullNestedChildCallCorrespondence.copyFour source destination, w 32⟩ := by
  apply MemoryCopySemantics.From.done
  · change MemorySemantics.touchSize? (w 32) (w 2) (w 4) = some (w 32)
    decide +kernel
  · apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    exact .empty _ _ _ _

private theorem invoked (object : Contract.CompiledObject) (scenario : Scenario) :
    RuntimeCallModeSemantics.Call (ChildFrameModeSemantics.Children (catalog scenario) (ChildFrameModeSemantics.effectsAt (catalog scenario) {} 0))
      (operation scenario) (w 100) (w 100) (value scenario) (w 0) (w 0) (w 2) (w 4) (parentBefore object).external
      (.value (.word (w (if reverts scenario then 0 else 1)))) (afterCall object scenario).external := by
  apply RuntimeCallModeSemantics.Call.invoked
  · exact .inl (by cases scenario <;> intro impossible <;> cases impossible)
  · intro stipend nonzero
    change ¬w 100 > w (Core.wordModulus - 2301)
    decide +kernel
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 32)
  · rfl
  · rfl
  have returnedResult : CallTransportSemantics.finishResult (response object scenario) (.value .unit) =
      Semantics.Result.value (.word (w (if reverts scenario then 0 else 1))) := by cases scenario <;> rfl
  rw [← returnedResult]
  apply CallTransportSemantics.Dispatch.returned (input := {}) (response := response object scenario) (result := .value .unit)
  · change ¬w 0 > w 1023
    decide +kernel
  · exact .done rfl (.empty _ _ _ _)
  · rfl
  · cases scenario
    case reverted =>
      apply AccountCallSemantics.Dispatch.refused (transferred := RuntimeCallModeSemantics.shared (parentBefore object).external)
      · exact .inl rfl
      · rfl
      · exact .child (child_called object .reverted)
      · rfl
    case callCode =>
      apply AccountCallSemantics.Dispatch.succeeded (transferred := RuntimeCallModeSemantics.shared (parentBefore object).external)
      · exact .inr (by change ¬w 5 > w 100; decide +kernel)
      · rfl
      · exact .child (child_called object .callCode)
      · rfl
    case delegated =>
      apply AccountCallSemantics.Dispatch.succeeded (transferred := RuntimeCallModeSemantics.shared (parentBefore object).external)
      · exact .inl rfl
      · rfl
      · exact .child (child_called object .delegated)
      · rfl
  · exact copyFour_source _ _

private theorem call_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (invoke scenario)
      (parentBefore object) (.value (.word (w (if reverts scenario then 0 else 1)))) (afterCall object scenario) := by
  cases scenario <;> apply Semantics.EvalExpr.call rfl
  case callCode.argumentsEvaluated =>
    exact .cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "5") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "4") rfl) .nil))))))
  case callCode.called => exact .external rfl rfl (.callCode (invoked object .callCode))
  all_goals first
    | exact .cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "4") rfl) .nil)))))
    | exact .external rfl rfl (.delegateCall (invoked object .delegated))
    | exact .external rfl rfl (.delegateCall (invoked object .reverted))

private theorem status_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (storedStatus scenario)
      (parentBefore object) (.value .unit) (afterStatus object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (call_source object scenario) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply byte_builtin (size := w 32)
  change MemorySemantics.touchSize? (w 32) (w 0) (w 1) = some (w 32)
  decide +kernel

private theorem size_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (observedByte "1" "returndatasize")
      (afterStatus object scenario) (.value .unit) (afterSize object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "1") rfl) (.cons (read_source _ _ _ .returnSize _ rfl) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply byte_builtin (size := w 32)
  change MemorySemantics.touchSize? (w 32) (w 1) (w 1) = some (w 32)
  decide +kernel

private theorem parent_written_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (byte "6" "170")
      (initial object) (.value .unit) (parentWritten object) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "6") rfl) (.cons (.word (text := "170") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem parent_stored_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (storage "7" "42")
      (parentWritten object) (.value .unit) (parentBefore object) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "7") rfl) (.cons (.word (text := "42") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem finish_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (call .unit "return" [word "0", word "7"])
      (afterSize object scenario) result (finalState object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "7") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (parentFunctions scenario) (parentEffects scenario) (AccountRuntime.frameFunction (code scenario)) []
      (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (parent_written_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (parent_stored_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (status_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (size_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (finish_source object scenario))
    (by intro impossible; cases impossible)



def runtimeNames : List String := ["mstore8", "sstore", "log0", "returndatasize", "return", "revert", "address", "caller", "callvalue"]
def usedNames : List String := runtimeNames ++ ["callcode", "delegatecall"]

private theorem atoms {supported : String → Prop} (functions : List Function) (type : Ty) (name : String)
    (arguments : List String) (available : supported name)
    (absent : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (call type name (arguments.map word)) := by
  apply ExecutableExpression.external (name := name) available absent
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

private theorem observed_eligible {supported : String → Prop} (functions : List Function) (offset name : String)
    (available : ∀ name ∈ usedNames, supported name) (used : name ∈ runtimeNames)
    (storeAbsent : functions.find? (·.name == "mstore8") = none) (absent : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (observedByte offset name) := by
  apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) storeAbsent
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .word _ _ _
  · exact atoms _ .word name [] (available _ (List.mem_append_left _ used)) absent

theorem child_eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (childFunctions scenario) := by
  intro function member statement statementMember
  simp only [childFunctions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, childCode, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact observed_eligible _ _ _ available (by simp [runtimeNames]) rfl rfl
  · exact observed_eligible _ _ _ available (by simp [runtimeNames]) rfl rfl
  · exact observed_eligible _ _ _ available (by simp [runtimeNames]) rfl rfl
  · exact atoms _ .unit "mstore8" ["3", "187"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "sstore" ["8", "99"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "log0" ["3", "1"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · cases scenario <;> first
      | exact atoms _ .unit "return" ["0", "4"] (available _ (by simp [usedNames, runtimeNames])) rfl
      | exact atoms _ .unit "revert" ["0", "4"] (available _ (by simp [usedNames, runtimeNames])) rfl

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (parentFunctions scenario) := by
  intro function member statement statementMember
  simp only [parentFunctions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["6", "170"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "sstore" ["7", "42"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) rfl
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases scenario <;> first
        | exact atoms _ .word "callcode" ["100", "100", "5", "0", "0", "2", "4"] (available _ (by simp [usedNames])) rfl
        | exact atoms _ .word "delegatecall" ["100", "100", "0", "0", "2", "4"] (available _ (by simp [usedNames])) rfl
  · exact observed_eligible _ _ _ available (by simp [runtimeNames]) rfl rfl
  · exact atoms _ .unit "return" ["0", "7"] (available _ (by simp [usedNames, runtimeNames])) rfl

private theorem runtime_supported : ∀ name ∈ runtimeNames, ContractCodeCorrespondence.supported name := by
  intro name member
  simp only [runtimeNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (⟨.store8, rfl⟩))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.store false, rfl⟩)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inr ⟨.log0, rfl⟩)))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.direct .returnDataSize, rfl, by intro input member; simp [EnvironmentBuiltinCorrespondence.inputs] at member; subst input; simp [Effects.slots, EnvironmentSemantics.Direct.slot]⟩))))))
  · exact .inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))
  · exact .inl (.inl (.inl (.inl (.inr ⟨.reverted, rfl⟩))))

  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.direct .address, rfl, by intro input member; simp [EnvironmentBuiltinCorrespondence.inputs] at member; subst input; simp [Effects.slots, EnvironmentSemantics.Direct.slot, EnvironmentSemantics.Direct.name]⟩))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.direct .caller, rfl, by intro input member; simp [EnvironmentBuiltinCorrespondence.inputs] at member; subst input; simp [Effects.slots, EnvironmentSemantics.Direct.slot, EnvironmentSemantics.Direct.name]⟩))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.direct .callvalue, rfl, by intro input member; simp [EnvironmentBuiltinCorrespondence.inputs] at member; subst input; simp [Effects.slots, EnvironmentSemantics.Direct.slot, EnvironmentSemantics.Direct.name]⟩))))))

theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with prior | rfl | rfl
  · exact .inl (.inl (runtime_supported name prior))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr (.inl rfl))))

end Tests.RustHullCallModeCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullCallModePublic
/-! Concrete CALLCODE and DELEGATECALL derivations reach public execution and
resumption. Catalog identities come from the actual supplied code and context. -/
set_option autoImplicit false
namespace Tests.RustHullCallModeCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
private abbrev number := Core.Word.ofNatModulo

def anchors : List CatalogWorldCorrespondence.Anchor := [⟨number 100, childBytes, 2⟩]

theorem catalog_connection_of_eligible (scenario : Scenario)
    (childEligible : ExecutableProgram (ContractCallModeCorrespondence.supported true) (childFunctions scenario)) :
    ModeChildCatalogExecutionCorrespondence.CatalogConnection (catalog scenario) (compiledCatalog scenario) anchors := by
  intro target source selected
  by_cases child : number 100 == target
  · have addressEq : number 100 = target := by simpa only [beq_iff_eq] using child
    subst target
    have sourceEq : sourceCode scenario = source := by
      simpa [ChildFrameSemantics.select, ChildFrameModeSemantics.select, catalog] using selected
    subst source
    refine ⟨0, {program := program scenario, path := ["Child"], bytes := childBytes},
      rfl, rfl, rfl, rfl, ?_, ?_, ?_, childEligible⟩
    · simp [anchors, sourceCode]
    · decide +kernel
    · change (List.range 2).find? (fun candidate => number 2 == number (candidate + 1)) = some 1
      decide +kernel
  · simp [ChildFrameSemantics.select, catalog, child] at selected

theorem catalog_connection (scenario : Scenario) :
    ModeChildCatalogExecutionCorrespondence.CatalogConnection (catalog scenario) (compiledCatalog scenario) anchors :=
  catalog_connection_of_eligible scenario (child_eligible scenario names_supported)

theorem initial_context_links (scenario : Scenario) (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks none (compiledCatalog scenario) object context anchors := by
  intro anchor member
  simp only [anchors, List.mem_cons, List.not_mem_nil, or_false] at member
  subst anchor
  refine ⟨childAccount, rfl, rfl, ?_, rfl⟩
  decide +kernel

theorem public_evaluates (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      ContractCallModeCorrespondence.PublicMessageRel context result (finalState object scenario).external value := by
  exact ContractCallModeCorrespondence.compileObject_preserves (height := 0) (code := code scenario) (by rfl) accepted rfl
    (eligible scenario names_supported) (catalog_connection scenario) (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by cases scenario <;> decide)) context rfl
    (initial_context_links scenario object) (source object scenario)

theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel context result (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl) accepted rfl
    (eligible scenario names_supported) (catalog_connection scenario) (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by cases scenario <;> decide)) context rfl
    (initial_context_links scenario object) (source object scenario)

end Tests.RustHullCallModeCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullCallModeRuntime
/-! Public CALLCODE and DELEGATECALL preserve the invoking storage address.
Returned observations and shared checkpoints agree with the source derivations. -/
set_option autoImplicit false
namespace Tests.RustHullCallModeRuntime
open Solcore Solcore.Frontend.RustHull RustHullCallModeCorrespondence

private abbrev w := Core.Word.ofNatModulo

private def expectedBytes : Scenario → List UInt8
  | .callCode => [1, 4, 0, 0, 5, 187, 170]
  | .delegated => [1, 4, 0, 55, 7, 187, 170]
  | .reverted => [0, 4, 0, 55, 7, 187, 170]

private def expectedEvents (scenario : Scenario) : List Logs.Event :=
  if scenario = .reverted then [] else [⟨w 0, [], [187]⟩]

private def expectedStorage (scenario : Scenario) : List (Core.Word × Core.Word) :=
  [(w 7, w 42)] ++ if scenario = .reverted then [] else [(w 8, w 99)]

private def checkWorld (label : String) (scenario : Scenario)
    (world : List AccountState.Account) : IO Unit := do
  let some parent := world.find? (·.address == w 0) |
    throw (IO.userError s!"{label}: missing parent")
  let some child := world.find? (·.address == w 100) |
    throw (IO.userError s!"{label}: missing code account")
  unless world.length == 2 && parent.storage == expectedStorage scenario && child.storage.isEmpty &&
      parent.transient.isEmpty && child.transient.isEmpty && child.code == some childBytes do
    throw (IO.userError s!"{label}: wrong mode checkpoint for {reprStr scenario}: {reprStr world}")

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"call mode: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"call mode: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"call mode: short resume completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 4000000,
      Contract.resumeWithReceipt checkpoint 4000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == expectedBytes scenario && storage == expectedStorage scenario &&
            receipt.logs == expectedEvents scenario && receipt.balances == [(w 0, w 100)] do
          throw (IO.userError s!"call mode: wrong result for {reprStr scenario}: {reprStr receipt}")
        checkWorld "receipt" scenario receipt.world
    | outcome => throw (IO.userError s!"call mode: expected return for {reprStr scenario}: {reprStr outcome}")
  match Core.runStateful 4000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair count (.pair memory (.pair storage (.pair logs (.pair cursor (.pair balances world))))))))) _ =>
      let expected := (finalState object scenario).external
      let runtime := expected.runtime.runtime.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words &&
          storage == Core.WordMapping.encode (expectedStorage scenario) &&
          logs == Core.WordMapping.encode expected.runtime.runtime.runtime.words &&
          cursor == .word expected.runtime.runtime.runtime.cursor &&
          balances == Core.WordMapping.encode [(w 0, w 100)] &&
          exit == .word runtime.storage.exit && offset == .word runtime.storage.returnOffset &&
          count == .word runtime.storage.returnSize do
        throw (IO.userError s!"call mode: snapshot differs from source for {reprStr scenario}")
      let accounts ← match AccountState.decode world with
        | .ok accounts => pure accounts
        | .error error => throw (IO.userError s!"call mode: bad world snapshot: {error}")
      checkWorld "Core snapshot" scenario accounts
  | outcome => throw (IO.userError s!"call mode: Core failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.callCode, .delegated, .reverted] do
    check scenario

end Tests.RustHullCallModeRuntime
end

section
-- leanmerge: from Solcore.Test.RustHullNestedChildCallRuntime
/-! Public execution and resumptions observe the same nested checkpoints as
the independent source derivations, including retained revert data. -/
set_option autoImplicit false
namespace Tests.RustHullNestedChildCallRuntime
open Solcore Solcore.Frontend.RustHull RustHullNestedChildCallCorrespondence

private abbrev w := Core.Word.ofNatModulo

private def expectedBytes : Scenario → List UInt8
  | .committed => [1, 4, 1, 1, 204, 187, 170]
  | .grandchildReverted => [1, 4, 0, 1, 204, 187, 170]
  | .childReverted => [0, 4, 1, 1, 204, 187, 170]

private def expectedEvents (scenario : Scenario) : List Logs.Event :=
  [⟨w 0, [], [170]⟩] ++
    (if scenario = .childReverted then [] else [⟨w 100, [], [187]⟩]) ++
    (if scenario = .committed then [⟨w 200, [], [204]⟩] else [])

private def checkWorld (label : String) (scenario : Scenario)
    (world : List AccountState.Account) : IO Unit := do
  let some parent := world.find? (·.address == w 0) |
    throw (IO.userError s!"{label}: missing parent")
  let some child := world.find? (·.address == w 100) |
    throw (IO.userError s!"{label}: missing child")
  let some grandchild := world.find? (·.address == w 200) |
    throw (IO.userError s!"{label}: missing grandchild")
  let childStorage := if scenario = .childReverted then [] else [(w 8, w 99)]
  let grandchildStorage := if scenario = .committed then [(w 9, w 77)] else []
  unless world.length == 3 && parent.storage == [(w 7, w 42)] &&
      child.storage == childStorage && grandchild.storage == grandchildStorage &&
      parent.transient.isEmpty && child.transient.isEmpty && grandchild.transient.isEmpty &&
      child.code == image .child && grandchild.code == image .grandchild do
    throw (IO.userError s!"{label}: wrong nested checkpoint for {reprStr scenario}: {reprStr world}")

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"nested call: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"nested call: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"nested call: short resume completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 4000000,
      Contract.resumeWithReceipt checkpoint 4000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == expectedBytes scenario && storage == [(w 7, w 42)] &&
            receipt.logs == expectedEvents scenario && receipt.balances == [(w 0, w 0)] do
          throw (IO.userError s!"nested call: wrong result for {reprStr scenario}: {reprStr receipt}")
        checkWorld "receipt" scenario receipt.world
    | outcome => throw (IO.userError s!"nested call: expected return for {reprStr scenario}: {reprStr outcome}")
  match Core.runStateful 4000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair count (.pair memory (.pair storage (.pair logs (.pair cursor (.pair balances world))))))))) _ =>
      let expected := (finalState object scenario).external
      let runtime := expected.runtime.runtime.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words &&
          storage == Core.WordMapping.encode [(w 7, w 42)] &&
          logs == Core.WordMapping.encode expected.runtime.runtime.runtime.words &&
          cursor == .word expected.runtime.runtime.runtime.cursor &&
          balances == Core.WordMapping.encode [(w 0, w 0)] &&
          exit == .word runtime.storage.exit && offset == .word runtime.storage.returnOffset &&
          count == .word runtime.storage.returnSize do
        throw (IO.userError s!"nested call: snapshot differs from source for {reprStr scenario}")
      let accounts ← match AccountState.decode world with
        | .ok accounts => pure accounts
        | .error error => throw (IO.userError s!"nested call: bad world snapshot: {error}")
      checkWorld "Core snapshot" scenario accounts
  | outcome => throw (IO.userError s!"nested call: Core failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.committed, .grandchildReverted, .childReverted] do
    check scenario

end Tests.RustHullNestedChildCallRuntime
end

section
-- leanmerge: from Solcore.Test.RustHullNestedChildCatalogCorrespondence
/-! The two concrete child accounts select their actual catalog entries and
obtain exact executable identities from public context initialization. -/
set_option autoImplicit false
namespace Tests.RustHullNestedChildCallCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
private abbrev number := Core.Word.ofNatModulo

def anchors : List CatalogWorldCorrespondence.Anchor :=
  [⟨number 100, (image .child).getD [], 2⟩, ⟨number 200, (image .grandchild).getD [], 3⟩]

theorem catalog_connection_of_eligible (scenario : Scenario)
    (childEligible : ExecutableProgram (ContractChildCallCorrespondence.supported true) (functions scenario .child))
    (grandchildEligible : ExecutableProgram (ContractChildCallCorrespondence.supported true) (functions scenario .grandchild)) :
    NestedChildCatalogExecutionCorrespondence.CatalogConnection (catalog scenario) (compiledCatalog scenario) anchors := by
  intro target source selected
  by_cases child : number 100 == target
  · have addressEq : number 100 = target := by simpa only [beq_iff_eq] using child
    subst target
    have sourceEq : sourceCode scenario .child = source := by
      simpa [ChildFrameSemantics.select, catalog] using selected
    subst source
    refine ⟨0, {program := program scenario, path := ["Child"], bytes := (image .child).getD []},
      rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [anchors, sourceCode]
    · decide +kernel
    · change (List.range 3).find? (fun candidate => number 2 == number (candidate + 1)) = some 1
      decide +kernel
    · exact childEligible
  · by_cases grandchild : number 200 == target
    · have addressEq : number 200 = target := by simpa only [beq_iff_eq] using grandchild
      subst target
      have sourceEq : sourceCode scenario .grandchild = source := by
        simpa [ChildFrameSemantics.select, catalog, child] using selected
      subst source
      refine ⟨1, {program := program scenario, path := ["Grandchild"], bytes := (image .grandchild).getD []},
        rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simp [anchors, sourceCode]
      · decide +kernel
      · change (List.range 3).find? (fun candidate => number 3 == number (candidate + 1)) = some 2
        decide +kernel
      · exact grandchildEligible
    · simp [ChildFrameSemantics.select, catalog, child, grandchild] at selected

theorem catalog_connection (scenario : Scenario) :
    NestedChildCatalogExecutionCorrespondence.CatalogConnection (catalog scenario) (compiledCatalog scenario) anchors :=
  catalog_connection_of_eligible scenario (eligible scenario .child names_supported)
    (eligible scenario .grandchild names_supported)

theorem initial_context_links (scenario : Scenario) (object : Contract.CompiledObject) :
    ContractNestedChildCallCorrespondence.InitialContextLinks none (compiledCatalog scenario) object context anchors := by
  intro anchor member
  simp only [anchors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨childAccount, rfl, rfl, ?_, rfl⟩
    decide +kernel
  · refine ⟨grandchildAccount, rfl, rfl, ?_, rfl⟩
    decide +kernel

end Tests.RustHullNestedChildCallCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullNestedChildCallPublic
/-! Independent two-level call derivations reach actual compilation, public
receipts and exact resumption thresholds. Catalog identities and initial code
links are discharged by the concrete source/context fixtures. -/
set_option autoImplicit false
namespace Tests.RustHullNestedChildCallCorrespondence
open Solcore Solcore.Frontend.RustHull

theorem public_evaluates (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      ContractNestedChildCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value := by
  exact ContractNestedChildCallCorrespondence.compileObject_preserves (height := 1) (code := code scenario .parent) (by rfl) accepted rfl
    (eligible scenario .parent names_supported) (catalog_connection scenario) context rfl
    (initial_context_links scenario object) (source object scenario)

theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    ∃ value, ContractNestedChildCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractNestedChildCallCorrespondence.compileObject_resumes_exact (height := 1) (code := code scenario .parent) (by rfl) accepted rfl
    (eligible scenario .parent names_supported) (catalog_connection scenario) context rfl
    (initial_context_links scenario object) (source object scenario)

end Tests.RustHullNestedChildCallCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullReturnDataCorrespondence
/-! Return-data bounds are checked before destination expansion. Prior storage,
memory and event updates remain in the internal snapshot, while an invalid
message exports none of those changes. Linked code and account reads share the
same execution as return-data operations. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullReturnDataCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where | empty | sourceInvalid | lengthInvalid
  deriving DecidableEq, Repr
private abbrev w := Core.Word.ofNatModulo
private def maximum := "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def image (linked : Bool) : Option (List UInt8) := if linked then some [205] else none
def guard : Expr := call .word "memoryguard" [word "171"]
def seed : Expr := call .unit "mstore8" [word "1", guard]
def storageWrite : Expr := call .unit "sstore" [word "7", word "42"]
def event : Expr := call .unit "log0" [word "1", word "1"]
def balance : Expr := call .word "selfbalance" []
def size : Expr := call .word "returndatasize" []
def codeCopy (linked : Bool) : Expr :=
  if linked then call .unit "codecopy" [word "7", word "0", word "1"] else call .word "msize" []
def copy (scenario : Scenario) : Expr := match scenario with
  | .empty => call .unit "returndatacopy" [word maximum, word "0", word "0"]
  | .sourceInvalid => call .unit "returndatacopy" [word maximum, word "1", word "0"]
  | .lengthInvalid => call .unit "returndatacopy" [word maximum, word "0", word "1"]
def returned : Expr := call .unit "return" [word "1", word "1"]
def code (scenario : Scenario) (linked : Bool) : CodeBlock := {
  stmts := [expression seed, expression storageWrite, expression event, expression balance,
    expression (codeCopy linked), expression size, expression (copy scenario), expression returned]
  functions := []}
def program (scenario : Scenario) (linked : Bool) : Program :=
  {entryPoints := [], functions := [], objects := [.object "ReturnData" (code scenario linked) []]}
def context : Contract.Context := {balance := w 11}
def initial (object : Contract.CompiledObject) (linked : Bool) : Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  ⟨[], ⟨ContractCodeCorrespondence.contextInitialState (image linked) object (Contract.normalizeContext context), []⟩⟩
def seeded : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 1) (w 171)).2
def memoryWritten (object : Contract.CompiledObject) (linked : Bool) : Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  ⟨[], {(initial object linked).external with runtime := RuntimeAccountEffectsSemantics.withMemory (initial object linked).external.runtime seeded}⟩
def storageWritten (object : Contract.CompiledObject) (linked : Bool) : Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  let state := (memoryWritten object linked).external.runtime.runtime.runtime.runtime
  ⟨[], RuntimeReturnDataEffectsSemantics.withRuntime (memoryWritten object linked).external
    {state with storage := (StorageSemantics.store state.storage (w 7) (w 42) false).2}⟩
def loggedWords : LogsSemantics.Words :=
  [(w 0, w 0), (w 1, w 0), (w 2, w 1), (w 3, LogsSemantics.paddedWord seeded.words (w 1) (w 1))]
def logged (object : Contract.CompiledObject) (linked : Bool) : Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  let state := (storageWritten object linked).external
  let previous := RuntimeLogEffectsSemantics.logsState state.runtime.runtime
  let logs := {previous with words := loggedWords, cursor := w 4}
  ⟨[], {state with runtime := {state.runtime with runtime := RuntimeLogEffectsSemantics.withLogs state.runtime.runtime logs}}⟩
def copiedMemory (linked : Bool) : MemorySemantics.State :=
  if linked then ⟨MemorySemantics.writeByte seeded.words (w 7) (w 205), seeded.size⟩ else seeded
def codeCopied (object : Contract.CompiledObject) (linked : Bool) : Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  let state := (logged object linked).external
  ⟨[], {state with runtime := RuntimeAccountEffectsSemantics.withMemory state.runtime (copiedMemory linked)}⟩
def terminated (object : Contract.CompiledObject) (linked : Bool) (kind : Nat) (offset length : Core.Word) :
    Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  let state := (codeCopied object linked).external
  ⟨[], RuntimeReturnDataEffectsSemantics.withRuntime state
    (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime kind offset length).2⟩
def finalState (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) : Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  if scenario = .empty then terminated object linked 1 (w 1) (w 1) else terminated object linked 3 (w 0) (w 0)
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem guard_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] guard
      (initial object linked) (.value (.word (w 171))) (initial object linked) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "171") rfl) .nil
  · exact .external (by rfl) rfl (.guard .guarded)

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] seed
      (initial object linked) (.value .unit) (memoryWritten object linked) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (guard_source object scenario linked) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))))

private theorem storage_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] storageWrite
      (memoryWritten object linked) (.value .unit) (storageWritten object linked) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "42") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))))

private theorem event_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] event
      (storageWritten object linked) (.value .unit) (logged object linked) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) .nil)
  · apply Semantics.EvalCall.external (by rfl) rfl
    apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
    apply RuntimeCodeEffectsSemantics.Builtin.runtime
    apply RuntimeAccountEffectsSemantics.Builtin.runtime
    apply RuntimeHashEffectsSemantics.Builtin.runtime
    apply RuntimeCopyEffectsSemantics.Builtin.runtime
    apply RuntimeFullEffectsSemantics.Builtin.runtime
    apply RuntimeLogEffectsSemantics.Builtin.logs
    apply LogsSemantics.Builtin.log .log0 .unit (w 1) (w 1) [] rfl
    apply LogsSemantics.Execute.writable rfl
    apply LogsSemantics.Append.done (size := w 32) (words := loggedWords)
    · decide +kernel
    · change ¬w 0 > LogsSemantics.nextCursor (w 0) (w 1) []
      decide +kernel
    · change MemorySemantics.touchSize? seeded.size (w 1) (w 1) = some (w 32)
      decide +kernel
    · apply LogsSemantics.Copy.step (by decide +kernel)
      exact .empty _ _ _

private theorem balance_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] balance
      (logged object linked) (.value (.word (w 11))) (logged object linked) := by
  apply Semantics.EvalExpr.call rfl .nil
  exact .external (by rfl) rfl (.runtime (.runtime (.observation (.selfbalance .word _))))

private theorem code_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] (codeCopy linked)
      (logged object linked) (if linked then .value .unit else .value (.word (w 32))) (codeCopied object linked) := by
  cases linked
  case false =>
    apply Semantics.EvalExpr.call rfl .nil
    exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))))
  case true =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil))
    · apply Semantics.EvalCall.external (by rfl) rfl
      apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
      apply RuntimeCodeEffectsSemantics.Builtin.copy
      apply CodeImageSemantics.Builtin.copy .codeCopy
      apply CodeImageSemantics.Execute.copied rfl
      apply MemoryCopySemantics.From.done (by change MemorySemantics.touchSize? (w 32) (w 7) (w 1) = some (w 32); decide +kernel)
      apply MemoryCopySemantics.Copy.step (by decide +kernel)
      exact .empty _ _ _ _

private theorem size_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] size
      (codeCopied object linked) (.value (.word (w 0))) (codeCopied object linked) := by
  apply Semantics.EvalExpr.call rfl .nil
  exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))))

private theorem copy_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] (copy scenario)
      (codeCopied object linked) (if scenario = .empty then .value .unit else result)
      (if scenario = .empty then codeCopied object linked else finalState object scenario linked) := by
  cases scenario
  case empty =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) .nil))
    · apply Semantics.EvalCall.external (by rfl) rfl
      apply RuntimeReturnDataEffectsSemantics.Builtin.copy
      exact .copy (.copied (by change ¬w 0 > w 0; decide +kernel) (by change ¬w 0 > (w 0).sub (w 0); decide +kernel)
        (.done (by cases linked <;> rfl) (.empty _ _ _ _)))
  case sourceInvalid =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "0") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.copy (.sourceOverflow _ (by change w 1 > w 0; decide +kernel))))
  case lengthInvalid =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.copy (.lengthOverflow _ (by change ¬w 0 > w 0; decide +kernel) (by change w 1 > (w 0).sub (w 0); decide +kernel))))

private theorem return_source (object : Contract.CompiledObject) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code .empty linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] returned
      (codeCopied object linked) result (finalState object .empty linked) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked))
      (AccountRuntime.frameFunction (code scenario linked)) [] (initial object linked) result (finalState object scenario linked) := by
  apply Semantics.EvalFunction.body (control := .fault (.language Core.Word.maximum)) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object scenario linked))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (storage_source object scenario linked))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (event_source object scenario linked))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (balance_source object scenario linked))
  have copied := code_source object scenario linked
  cases isLinked : linked <;> simp only [isLinked, Bool.false_eq_true, ↓reduceIte] at copied
  all_goals
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl copied)
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (size_source object scenario _))
    cases scenario
  all_goals first
    | apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (copy_source object .empty _))
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object _))
        (by intro impossible; cases impossible)
    | exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (copy_source object _ _))
        (by intro impossible; cases impossible)

def usedNames (linked : Bool) : List String :=
  ["mstore8", "memoryguard", "sstore", "log0", "selfbalance",
    if linked then "codecopy" else "msize", "returndatasize", "returndatacopy", "return"]

theorem eligible (scenario : Scenario) (linked : Bool) {supported : String → Prop}
    (available : ∀ name ∈ usedNames linked, supported name) :
    ExecutableProgram supported [AccountRuntime.frameFunction (code scenario linked)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · apply ExecutableExpression.external (name := "memoryguard") (available _ (by simp [usedNames])) (by rfl)
      intro argument member
      simp only [List.mem_singleton] at member
      subst argument
      exact .word _ _ _
  · apply ExecutableExpression.external (name := "sstore") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "log0") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · exact .external (name := "selfbalance") (available _ (by simp [usedNames])) (by rfl) (by intro _ member; cases member) _ _
  · cases linked
    case false =>
      exact .external (name := "msize") (available _ (by simp [usedNames])) (by rfl) (by intro _ member; cases member) _ _
    case true =>
      apply ExecutableExpression.external (name := "codecopy") (available _ (by simp [usedNames])) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact .word _ _ _
  · exact .external (name := "returndatasize") (available _ (by simp [usedNames])) (by rfl) (by intro _ member; cases member) _ _
  · cases scenario
    all_goals
      apply ExecutableExpression.external (name := "returndatacopy") (available _ (by simp [usedNames])) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "return") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _

private theorem account_supported (name : String)
    (member : name ∈ ["mstore8", "sstore", "log0", "selfbalance", "msize", "returndatasize", "return"]) :
    ContractAccountCorrespondence.supported name := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨.store8, rfl⟩))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨.store false, rfl⟩))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨.log0, rfl⟩))))
  · exact Or.inr ⟨.selfbalance, rfl⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨.size, rfl⟩))))))
  · apply Or.inl; apply Or.inl; apply Or.inl; apply Or.inl; apply Or.inl
    refine Or.inr ⟨.direct .returnDataSize, rfl, ?_⟩
    intro input member
    simp only [EnvironmentBuiltinCorrespondence.inputs, List.mem_singleton] at member
    subst input
    simp [Effects.slots, EnvironmentSemantics.Direct.slot]
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨.returned, rfl⟩)))

private theorem lift_account (linked : Bool) {name : String} (available : ContractAccountCorrespondence.supported name) :
    ContractReturnDataCorrespondence.supported linked name := by
  cases linked
  · exact .inl available
  · exact .inl (.inl available)

private theorem names_supported (linked : Bool) :
    ∀ name ∈ usedNames linked, ContractReturnDataCorrespondence.supported linked name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lift_account linked (account_supported _ (by simp))
  · exact .inr (.inr rfl)
  · exact lift_account linked (account_supported _ (by simp))
  · exact lift_account linked (account_supported _ (by simp))
  · exact lift_account linked (account_supported _ (by simp))
  · cases linked
    · exact lift_account false (account_supported _ (by simp))
    · exact .inl (.inr (.inr ⟨.codeCopy, rfl⟩))
  · exact lift_account linked (account_supported _ (by simp))
  · exact .inr (.inl rfl)
  · exact lift_account linked (account_supported _ (by simp))

theorem public_resumes (scenario : Scenario) (linked : Bool) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario linked) ["ReturnData"] 64 (image linked) [] = .ok object) :
    ∃ value, ContractReturnDataCorrespondence.PublicMessageRel context result (finalState object scenario linked).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  have enabled : ((image linked).isSome || !([] : List AccountRuntime.CodeDefinition).isEmpty) = linked := by
    cases linked <;> rfl
  apply ContractReturnDataCorrespondence.compileObject_resumes_exact (code := code scenario linked)
    (by rfl) accepted
  · rw [enabled]
    exact eligible scenario linked (names_supported linked)
  · rfl
  · exact source object scenario linked

theorem public_prepared (scenario : Scenario) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program scenario false) ["ReturnData"] context 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program scenario false) ["ReturnData"] 64 none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∃ value, ContractReturnDataCorrespondence.PublicMessageRel context result (finalState object scenario false).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractReturnDataCorrespondence.prepare_resumes_exact
    (code := code scenario false) (by rfl) accepted (eligible scenario false (names_supported false)) rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object scenario false)⟩

def nonemptyEntries : MemorySemantics.Entries := Memory.packBytes [171, 205]
def nonemptyMemory (overflow : Bool) : MemorySemantics.State :=
  if overflow then seeded else
    ⟨MemorySemantics.writeByte (MemorySemantics.writeByte seeded.words (w 31) (w 171)) (w 32) (w 205), w 64⟩

theorem nonempty_source (overflow : Bool) (storage : StorageSemantics.State) :
    ReturnDataSemantics.Execute nonemptyEntries (w 2) (if overflow then Core.Word.maximum else w 31) (w 0)
      (if overflow then w 1 else w 2) ⟨seeded, storage⟩
      (if overflow then MemorySemantics.overflow else .value .unit) ⟨nonemptyMemory overflow, storage⟩ := by
  cases overflow
  case false =>
    apply ReturnDataSemantics.Execute.copied (by decide +kernel) (by decide +kernel)
    apply MemoryCopySemantics.From.done (by change MemorySemantics.touchSize? seeded.size (w 31) (w 2) = some (w 64); decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    exact .empty _ _ _ _
  case true =>
    exact .copied (by decide +kernel) (by decide +kernel) (.overflow (by change MemorySemantics.touchSize? seeded.size Core.Word.maximum (w 1) = none; decide +kernel))

private def expectedEvents : List Logs.Event := [⟨w 0, [], [171]⟩]
private def check (scenario : Scenario) (linked : Bool) : IO Unit := do
  let object ← match Contract.compileObject (program scenario linked) ["ReturnData"] 64 (image linked) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"return-data correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"return-data correspondence: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"return-data correspondence: short resume completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    if scenario = .empty then
      match receipt.outcome with
      | .returned bytes storage =>
          unless bytes == [171] && storage == [(w 7, w 42)] && receipt.logs == expectedEvents do
            throw (IO.userError "return-data correspondence: successful message lost earlier writes or logs")
      | outcome => throw (IO.userError s!"return-data correspondence: expected return, got {reprStr outcome}")
    else
      match receipt.outcome with
      | .invalid =>
          unless receipt.world.isEmpty && receipt.logs.isEmpty do
            throw (IO.userError "return-data correspondence: invalid message exported changes")
      | outcome => throw (IO.userError s!"return-data correspondence: expected invalid before destination fault, got {reprStr outcome}")
  match Core.runStateful 1000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair length (.pair memory (.pair storage (.pair logs (.pair cursor _)))))))) _ =>
      let expected := (finalState object scenario linked).external.runtime
      let runtime := expected.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words && storage == Core.WordMapping.encode [(w 7, w 42)] &&
          logs == Core.WordMapping.encode expected.runtime.words && cursor == .word expected.runtime.cursor &&
          exit == .word runtime.storage.exit && offset == .word runtime.storage.returnOffset && length == .word runtime.storage.returnSize do
        throw (IO.userError "return-data correspondence: internal snapshot lost earlier state changes")
      match Logs.decodeValues logs cursor with
      | .ok events =>
          unless events == expectedEvents do
            throw (IO.userError "return-data correspondence: invalid message lost its internal event snapshot")
      | .error error => throw (IO.userError s!"return-data correspondence: malformed internal logs: {error}")
  | outcome => throw (IO.userError s!"return-data correspondence: Core failed: {reprStr outcome}")

private def checkNonempty (overflow : Bool) : IO Unit := do
  let slots : List (String × Core.Ty) := [("memory", Core.WordMapping.type), ("memorySize", .word),
    ("returnData", Core.WordMapping.type), ("returnDataSize", .word),
    ("exit", .word), ("returnOffset", .word), ("returnSize", .word)]
  let arguments : List Lowered := [⟨.word, Core.LanguageResult.success (.word (if overflow then Core.Word.maximum else w 31))⟩,
    ⟨.word, Core.LanguageResult.success (.word (w 0))⟩, ⟨.word, Core.LanguageResult.success (.word (if overflow then w 1 else w 2))⟩]
  let lowered ← match lowerBuiltin (AccountRuntime.frameScope slots) "returndatacopy" .unit arguments with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError s!"return-data correspondence: direct lowering failed: {reprStr error}")
  let cells : List (Core.Ty × Core.Expr) := [
    ⟨Core.WordMapping.type, Core.WordMapping.literal seeded.words⟩, ⟨.word, .word seeded.size⟩,
    ⟨Core.WordMapping.type, Core.WordMapping.literal nonemptyEntries⟩, ⟨.word, .word (w 2)⟩,
    ⟨.word, .word (w 0)⟩, ⟨.word, .word (w 9)⟩, ⟨.word, .word (w 9)⟩]
  let expression := cells.foldr (fun (type, value) body => .letE (.newCell type value) body) lowered.expression
  match Core.runStateful 1000000 (Core.State.initial expression) with
  | .done value store =>
      let expected := if overflow then Core.Value.inLeft .unit (.word (w 6)) else .inRight .word .unit
      unless value == expected && store[0]? == some (Core.WordMapping.encode (nonemptyMemory overflow).words) &&
          store[1]? == some (.word (nonemptyMemory overflow).size) &&
          store[2]? == some (Core.WordMapping.encode nonemptyEntries) && store[3]? == some (.word (w 2)) &&
          store[4]? == some (.word (w 0)) && store[5]? == some (.word (w 9)) && store[6]? == some (.word (w 9)) do
        throw (IO.userError "return-data correspondence: nonempty copy changed the source or termination registers")
  | .fault fault _ => throw (IO.userError s!"return-data correspondence: direct copy fault: {reprStr fault}")
  | .outOfFuel _ => throw (IO.userError "return-data correspondence: direct copy exceeded fuel")

def run : IO Unit := do
  for scenario in [Scenario.empty, .sourceInvalid, .lengthInvalid] do
    check scenario false
    check scenario true
  checkNonempty false
  checkNonempty true

end Tests.RustHullReturnDataCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullRevertCorrespondence
/-! Hull's explicit revert reaches the actual lowering, memory write and revert
termination through the call-mode public theorem. Each scenario reverts with a
message of at most one EVM word: a short message, an empty one, a full word of
32 bytes, and a short message written over an earlier word at offset zero. The
independent source stores the left-aligned message word and reverts with
exactly the message bytes. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullRevertCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | short | empty | full | overwrite
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩

def rootBytes : List UInt8 := [0]
def message : Scenario → String
  | .short => "boom"
  | .empty => ""
  | .full => "abcdefghijklmnopqrstuvwxyz012345"
  | .overwrite => "ok"
def reverting (scenario : Scenario) : Stmt := ⟨.revert (message scenario), none⟩
/-- A word of ones written before the revert in the overwrite scenario. -/
def seed : Stmt := expression (call .unit "mstore" [word "0",
  word "115792089237316195423570985008687907853269984665640564039457584007913129639935"])
def code (scenario : Scenario) : CodeBlock := {
  stmts := (if scenario = .overwrite then [seed] else []) ++ [reverting scenario], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Reverter" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] {} 1 (some rootBytes)
def context : Contract.Context := {}

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def frame (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withMemory (state : SourceState) (memory : MemorySemantics.State) : SourceState :=
  ⟨[], {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime
    {frame state with memory := memory})}⟩
def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩
def seeded (object : Contract.CompiledObject) : SourceState :=
  withMemory (initial object)
    (MemorySemantics.mstore (frame (initial object)).memory (w 0) (w (Core.wordModulus - 1))).2
def beforeRevert (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  if scenario = .overwrite then seeded object else initial object

/-- The independent effect of the revert: the message word at offset zero and
the revert registers over the message bytes. -/
def stored (state : SourceState) (scenario : Scenario) : MemorySemantics.State :=
  (MemorySemantics.mstore (frame state).memory Core.Word.zero (RevertSemantics.messageWord (message scenario))).2
def halted (state : SourceState) (scenario : Scenario) : RuntimeEffectsSemantics.State :=
  (TerminationSemantics.terminate {frame state with memory := stored state scenario} 2 Core.Word.zero
    (RevertSemantics.messageLength (message scenario))).2
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := beforeRevert object scenario
  {state with external := {state.external with
    runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime (halted state scenario)}}
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem fits (scenario : Scenario) : (message scenario).toUTF8.size ≤ 32 := by
  cases scenario <;> decide +kernel

private theorem revert_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalStmt (functions scenario) effects [] (reverting scenario) (beforeRevert object scenario)
      (.fault (.language Core.Word.maximum)) (finalState object scenario) := by
  cases scenario
  all_goals
    apply Semantics.EvalStmt.revert rfl
    exact RevertSemantics.Reverted.reverted (fits _) rfl rfl

private theorem seed_source (object : Contract.CompiledObject) :
    Semantics.EvalStmt (functions .overwrite) effects [] seed (initial object) .fallthrough (seeded object) := by
  apply Semantics.EvalStmt.expression rfl
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0") rfl)
      (.cons (.word (text := "115792089237316195423570985008687907853269984665640564039457584007913129639935") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  cases scenario
  case overwrite =>
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (seed_source object)
    exact .stop (by intros; intro impossible; cases impossible) (revert_source object .overwrite)
      (by intro impossible; cases impossible)
  all_goals
    exact .stop (by intros; intro impossible; cases impossible) (revert_source object _)
      (by intro impossible; cases impossible)

def usedNames : List String := ["mstore", "revert"]

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  have revertAvailable : supported "revert" := available _ (by simp [usedNames])
  cases scenario <;>
    simp only [AccountRuntime.frameFunction, code, reverting, seed, if_true, if_false, reduceCtorEq,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  all_goals try (subst statement; simpa only [ExecutableStatement] using revertAvailable)
  rcases statementMember with rfl | rfl
  · simp only [expression, ExecutableStatement]
    apply ExecutableExpression.external (name := "mstore") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · simpa only [ExecutableStatement] using revertAvailable

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.reverted, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object context [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for Hull's explicit revert: short,
empty and full-word messages, and a message over an earlier memory word. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Reverter"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel context result
        (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) context rfl (empty_links object)
    (source object scenario)

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Reverter"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"revert correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"revert correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .reverted bytes =>
        unless bytes == (message scenario).toUTF8.toList do
          throw (IO.userError s!"revert correspondence: wrong bytes for {reprStr scenario}: {reprStr bytes}")
    | outcome =>
        throw (IO.userError s!"revert correspondence: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.short, .empty, .full, .overwrite] do
    check scenario

end Tests.RustHullRevertCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullRootCallCorrespondence
/-! Root reentry selects the actual root closure at identity one. A calldata
flag separates the parent and child paths of the same compiled frame. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.RustHullRootCallCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
private abbrev w := Core.Word.ofNatModulo
inductive Scenario where | success | parentReverted
  deriving BEq, DecidableEq, Repr
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def byte (offset data : String) : Expr := call .unit "mstore8" [word offset, word data]
def storage (key data : String) : Expr := call .unit "sstore" [word key, word data]
def invoke : Expr := call .word "call" [word "100", word "100", word "0", word "0", word "1", word "2", word "2"]
def storedStatus : Expr := call .unit "mstore8" [word "1", invoke]
def observedStorage : Expr := call .unit "mstore8" [word "4", call .word "sload" [word "8"]]
def finish (scenario : Scenario) : Expr := call .unit (if scenario == .parentReverted then "revert" else "return") [word "0", word "7"]
def parent (scenario : Scenario) : Function := {
  name := "parent", args := [], ret := .unit,
  body := [expression (byte "0" "1"), expression (byte "6" "170"), expression (storage "7" "42"),
    expression storedStatus, expression observedStorage, expression (finish scenario)]}
def child : Function := {
  name := "child", args := [], ret := .unit,
  body := [expression (byte "1" "187"), expression (storage "8" "99"),
    expression (call .unit "return" [word "0", word "2"])]}
def condition : Expr := call .bool "eq" [call .word "calldatasize" [], word "0"]
def branch : Expr := ⟨.unit, .ifThen .unit condition (call .unit "parent" []) (call .unit "child" []), none⟩
def code (scenario : Scenario) : CodeBlock := {stmts := [expression branch], functions := [parent scenario, child]}
def program (scenario : Scenario) : Program := {entryPoints := [], functions := [], objects := [.object "Root" (code scenario) []]}
def rootBytes : List UInt8 := [0x60, 0x00]
def sourceCode (scenario : Scenario) : ChildFrameSemantics.Code := ⟨program scenario, code scenario, rootBytes⟩
def catalog (scenario : Scenario) : ChildFrameModeSemantics.Catalog := [(w 100, sourceCode scenario)]
def parentEffects (scenario : Scenario) := ChildFrameModeSemantics.effectsAt (catalog scenario) {} 1 (some rootBytes)
def childEffects (scenario : Scenario) := ChildFrameModeSemantics.effectsAt (catalog scenario) {} 0 (some rootBytes)
def functions (scenario : Scenario) := [parent scenario, child, AccountRuntime.frameFunction (code scenario)]
def context : Contract.Context := {address := w 100, completeWorld := true}
abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def runtime (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withRuntime (state : SourceState) (next : RuntimeEffectsSemantics.State) : SourceState :=
  {state with external := {state.external with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime next}}
def written (state : SourceState) (offset data : Core.Word) : SourceState :=
  withRuntime state {runtime state with memory := (MemorySemantics.mstore8 (runtime state).memory offset data).2}
def stored (state : SourceState) (key data : Core.Word) : SourceState :=
  withRuntime state {runtime state with storage := (StorageSemantics.store (runtime state).storage key data false).2}
def terminated (state : SourceState) (exit length : Nat) : SourceState :=
  withRuntime state (TerminationSemantics.terminate (runtime state) exit (w 0) (w length)).2
def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩
def parentFlag (object : Contract.CompiledObject) := written (initial object) (w 0) (w 1)
def parentWritten (object : Contract.CompiledObject) := written (parentFlag object) (w 6) (w 170)
def parentBefore (object : Contract.CompiledObject) := stored (parentWritten object) (w 7) (w 42)
def arguments (object : Contract.CompiledObject) := RuntimeCallModeSemantics.arguments .ordinary
  (parentBefore object).external (w 100) (w 100) (w 0) (w 0) (w 1) (w 2) (w 2)
def inputWords (object : Contract.CompiledObject) : MemorySemantics.Entries :=
  MemorySemantics.writeByte [] (w 0) (MemoryCopySemantics.readByte (runtime (parentBefore object)).memory.words (w 0))
def request (object : Contract.CompiledObject) := CallTransportSemantics.request (arguments object) (inputWords object)
def childInitial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ChildFrameModeSemantics.initial .ordinary (w 100) (parentBefore object).external
    (request object) (RuntimeCallModeSemantics.shared (parentBefore object).external) rootBytes⟩
def childWritten (object : Contract.CompiledObject) := written (childInitial object) (w 1) (w 187)
def childStored (object : Contract.CompiledObject) := stored (childWritten object) (w 8) (w 99)
def childFinal (object : Contract.CompiledObject) := terminated (childStored object) 1 2
def response (object : Contract.CompiledObject) : AccountCallSemantics.Response :=
  ⟨true, MemorySnapshotSemantics.aligned (runtime (childFinal object)).memory.words (w 0) (w 2), w 2⟩
def copyTwo (source destination : MemorySemantics.Entries) : MemorySemantics.Entries :=
  MemorySemantics.writeByte (MemorySemantics.writeByte destination (w 2) (MemoryCopySemantics.readByte source (w 0)))
    (w 3) (MemoryCopySemantics.readByte source (w 1))
def transportAfter (object : Contract.CompiledObject) : CallTransportSemantics.State :=
  ⟨{(runtime (parentBefore object)).memory with words := copyTwo (response object).data (runtime (parentBefore object)).memory.words},
    (response object).data, w 2⟩
def afterCall (object : Contract.CompiledObject) : SourceState :=
  let state := parentBefore object
  {state with external := RuntimeCallModeSemantics.withTransport state.external (transportAfter object) (RuntimeCallModeSemantics.shared (childFinal object).external)}
def afterStatus (object : Contract.CompiledObject) := written (afterCall object) (w 1) (w 1)
def afterStorage (object : Contract.CompiledObject) := written (afterStatus object) (w 4) (w 99)
def finalState (object : Contract.CompiledObject) (scenario : Scenario) :=
  terminated (afterStorage object) (if scenario == .parentReverted then 2 else 1) 7
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem byte_builtin (children : RuntimeCallModeSemantics.State → AccountCallSemantics.Children)
    (image : Option (List UInt8)) (state : SourceState) (offset data size : Core.Word)
    (touched : MemorySemantics.touchSize? (runtime state).memory.size offset (w 1) = some size) :
    RuntimeCallModeSemantics.Builtin children image "mstore8" .unit [.word offset, .word data] state.external
      (.value .unit) (written state offset data).external := by
  apply RuntimeCallModeSemantics.Builtin.runtime
  apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
  apply RuntimeCodeEffectsSemantics.Builtin.runtime
  apply RuntimeAccountEffectsSemantics.Builtin.runtime
  apply RuntimeHashEffectsSemantics.Builtin.runtime
  apply RuntimeCopyEffectsSemantics.Builtin.runtime
  apply RuntimeFullEffectsSemantics.Builtin.runtime
  apply RuntimeLogEffectsSemantics.Builtin.runtime
  simp only [runtime] at touched
  simp only [RuntimeEnvironmentEffectsSemantics.builtin, RuntimeEffectsSemantics.builtin,
    MemorySemantics.builtin, MemorySemantics.mstore8, runtime, touched]

private theorem byte_source (scenario : Scenario)
    (children : RuntimeCallModeSemantics.State → AccountCallSemantics.Children)
    (state : SourceState) (offset data : String) (a b size : Core.Word)
    (offsetParsed : Semantics.parseWord? offset = some a)
    (dataParsed : Semantics.parseWord? data = some b)
    (touched : MemorySemantics.touchSize? (runtime state).memory.size a (w 1) = some size) :
    Semantics.EvalExpr (functions scenario) (RuntimeCallModeSemantics.effectsWith children (some rootBytes)) []
      (byte offset data) state (.value .unit) (written state a b) := by
  have offsetEval : Semantics.EvalExpr (functions scenario) (RuntimeCallModeSemantics.effectsWith children (some rootBytes)) []
      (word offset) state (.value (.word a)) state := by
    simpa only [Semantics.literalResult, offsetParsed] using (Semantics.EvalExpr.word (functions := functions scenario)
      (effects := RuntimeCallModeSemantics.effectsWith children (some rootBytes)) (env := []) (state := state) (expression := word offset) rfl)
  have dataEval : Semantics.EvalExpr (functions scenario) (RuntimeCallModeSemantics.effectsWith children (some rootBytes)) []
      (word data) state (.value (.word b)) state := by
    simpa only [Semantics.literalResult, dataParsed] using (Semantics.EvalExpr.word (functions := functions scenario)
      (effects := RuntimeCallModeSemantics.effectsWith children (some rootBytes)) (env := []) (state := state) (expression := word data) rfl)
  apply Semantics.EvalExpr.call rfl (.cons offsetEval (.cons dataEval .nil))
  exact .external rfl rfl (byte_builtin children _ state a b size touched)

private theorem calldata_source (scenario : Scenario)
    (children : RuntimeCallModeSemantics.State → AccountCallSemantics.Children) (state : SourceState) :
    Semantics.EvalExpr (functions scenario) (RuntimeCallModeSemantics.effectsWith children (some rootBytes)) []
      (call .word "calldatasize" []) state
      (.value (.word ((RuntimeCallModeSemantics.observations state.external).direct .calldataSize))) state := by
  apply Semantics.EvalExpr.call rfl .nil
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem child_written_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) (childEffects scenario) [] (byte "1" "187")
      (childInitial object) (.value .unit) (childWritten object) := by
  apply byte_source (size := w 32) _ _ _ _ _ _ _ rfl rfl
  change MemorySemantics.touchSize? (w 0) (w 1) (w 1) = some (w 32)
  decide +kernel

private theorem child_stored_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) (childEffects scenario) [] (storage "8" "99")
      (childWritten object) (.value .unit) (childStored object) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "8") rfl) (.cons (.word (text := "99") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem child_finish_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) (childEffects scenario) [] (call .unit "return" [word "0", word "2"])
      (childStored object) result (childFinal object) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

private theorem child_body_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) (childEffects scenario) child []
      (childInitial object) result (childFinal object) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_written_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_stored_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (child_finish_source object scenario))
    (by intro impossible; cases impossible)

theorem child_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) (childEffects scenario) (AccountRuntime.frameFunction (code scenario)) []
      (childInitial object) result (childFinal object) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.stop (by intros; intro impossible; cases impossible) _ (by intro impossible; cases impossible)
  apply Semantics.EvalStmt.expressionFault rfl
  apply Semantics.EvalExpr.ifFalse (value := .bool false) rfl
  · apply Semantics.EvalExpr.call rfl (.cons (calldata_source _ _ _) (.cons (.word (text := "0") rfl) .nil))
    exact .primitive rfl rfl
  · rfl
  · exact .call rfl .nil (.function (function := child) rfl (child_body_source object scenario))

private theorem child_response (object : Contract.CompiledObject) :
    ChildResultSemantics.Respond (ChildFrameModeSemantics.completedStatus result (runtime (childFinal object)))
      (runtime (childFinal object)) (.value (response object)) := by
  apply ChildResultSemantics.Respond.returned (data := .value (response object).data) rfl
  apply MemorySnapshotSemantics.Extract.aligned (size := w 32)
  · change MemorySemantics.touchSize? (w 0) (w 0) (w 2) = some (w 32)
    decide +kernel
  · change w 2 ≠ Core.Word.zero
    decide +kernel
  · rfl


def rootAccount (object : Contract.CompiledObject) : AccountState.Account :=
  {address := w 100, storage := [(w 7, w 42)], code := object.codeImages.head?.getD none, nonce := w 1}

theorem child_called (object : Contract.CompiledObject) (scenario : Scenario)
    (image : object.codeImages.head?.getD none = some rootBytes) :
    ChildFrameModeSemantics.Children (catalog scenario) (ChildFrameModeSemantics.effectsAt (catalog scenario) {} 0)
      (parentBefore object).external .ordinary (w 100) (request object)
      (RuntimeCallModeSemantics.shared (parentBefore object).external) (.value (response object))
      (RuntimeCallModeSemantics.shared (childFinal object).external) := by
  apply ChildFrameModeSemantics.Children.executed (account := rootAccount object) (code := sourceCode scenario)
  · change AccountCallSemantics.isPrecompile (w 100) = false
    decide +kernel
  · rfl
  · rfl
  · exact image
  · exact child_source object scenario
  · exact child_response object

private theorem copyTwo_source (source destination : MemorySemantics.Entries) :
    MemoryCopySemantics.From source (w 2) (w 0) (w 2) ⟨destination, w 32⟩ (.value .unit)
      ⟨copyTwo source destination, w 32⟩ := by
  apply MemoryCopySemantics.From.done
  · change MemorySemantics.touchSize? (w 32) (w 2) (w 2) = some (w 32)
    decide +kernel
  · apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    exact .empty _ _ _ _

private theorem invoked (object : Contract.CompiledObject) (scenario : Scenario)
    (image : object.codeImages.head?.getD none = some rootBytes) :
    RuntimeCallModeSemantics.Call (ChildFrameModeSemantics.Children (catalog scenario) (ChildFrameModeSemantics.effectsAt (catalog scenario) {} 0))
      .ordinary (w 100) (w 100) (w 0) (w 0) (w 1) (w 2) (w 2) (parentBefore object).external
      (.value (.word (w 1))) (afterCall object).external := by
  apply RuntimeCallModeSemantics.Call.invoked
  · exact .inr (.inl rfl)
  · intro _ nonzero
    exact False.elim (nonzero rfl)
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 32)
  · rfl
  · rfl
  apply CallTransportSemantics.Dispatch.returned (input := ⟨inputWords object, w 32⟩) (response := response object) (result := .value .unit)
  · change ¬w 0 > w 1023
    decide +kernel
  · apply MemoryCopySemantics.From.done
    · rfl
    · change MemoryCopySemantics.Copy (runtime (parentBefore object)).memory.words (w 0) (w 0) (w 1) [] (inputWords object)
      apply MemoryCopySemantics.Copy.step (by decide +kernel)
      exact .empty _ _ _ _
  · rfl
  · apply AccountCallSemantics.Dispatch.succeeded (transferred := RuntimeCallModeSemantics.shared (parentBefore object).external)
    · exact .inr (by change ¬w 0 > w 0; decide +kernel)
    · rfl
    · exact .child (child_called object scenario image)
    · rfl
  · exact copyTwo_source _ _

private theorem call_source (object : Contract.CompiledObject) (scenario : Scenario)
    (image : object.codeImages.head?.getD none = some rootBytes) :
    Semantics.EvalExpr (functions scenario) (parentEffects scenario) [] invoke
      (parentBefore object) (.value (.word (w 1))) (afterCall object) := by
  apply Semantics.EvalExpr.call rfl
    (.cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "2") rfl) .nil)))))))
  exact .external rfl rfl (.call (invoked object scenario image))

private theorem status_source (object : Contract.CompiledObject) (scenario : Scenario)
    (image : object.codeImages.head?.getD none = some rootBytes) :
    Semantics.EvalExpr (functions scenario) (parentEffects scenario) [] storedStatus
      (parentBefore object) (.value .unit) (afterStatus object) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "1") rfl) (.cons (call_source object scenario image) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply byte_builtin (size := w 32)
  change MemorySemantics.touchSize? (w 32) (w 1) (w 1) = some (w 32)
  decide +kernel

private theorem observed_storage_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) (parentEffects scenario) [] observedStorage
      (afterStatus object) (.value .unit) (afterStorage object) := by
  have loaded : Semantics.EvalExpr (functions scenario) (parentEffects scenario) [] (call .word "sload" [word "8"])
      (afterStatus object) (.value (.word (w 99))) (afterStatus object) := by
    apply Semantics.EvalExpr.call rfl (.cons (.word (text := "8") rfl) .nil)
    exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "4") rfl) (.cons loaded .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply byte_builtin (size := w 32)
  change MemorySemantics.touchSize? (w 32) (w 4) (w 1) = some (w 32)
  decide +kernel

private theorem parent_flag_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) (parentEffects scenario) [] (byte "0" "1")
      (initial object) (.value .unit) (parentFlag object) := by
  apply byte_source (size := w 32) _ _ _ _ _ _ _ rfl rfl
  change MemorySemantics.touchSize? (w 0) (w 0) (w 1) = some (w 32)
  decide +kernel

private theorem parent_written_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) (parentEffects scenario) [] (byte "6" "170")
      (parentFlag object) (.value .unit) (parentWritten object) := by
  apply byte_source (size := w 32) _ _ _ _ _ _ _ rfl rfl
  change MemorySemantics.touchSize? (w 32) (w 6) (w 1) = some (w 32)
  decide +kernel

private theorem parent_stored_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) (parentEffects scenario) [] (storage "7" "42")
      (parentWritten object) (.value .unit) (parentBefore object) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "7") rfl) (.cons (.word (text := "42") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem finish_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) (parentEffects scenario) [] (finish scenario)
      (afterStorage object) result (finalState object scenario) := by
  cases scenario <;> apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "7") rfl) .nil))
  all_goals exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

private theorem parent_source (object : Contract.CompiledObject) (scenario : Scenario)
    (image : object.codeImages.head?.getD none = some rootBytes) :
    Semantics.EvalFunction (functions scenario) (parentEffects scenario) (parent scenario) []
      (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (parent_flag_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (parent_written_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (parent_stored_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (status_source object scenario image))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (observed_storage_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (finish_source object scenario))
    (by intro impossible; cases impossible)

theorem source (object : Contract.CompiledObject) (scenario : Scenario)
    (image : object.codeImages.head?.getD none = some rootBytes) :
    Semantics.EvalFunction (functions scenario) (parentEffects scenario) (AccountRuntime.frameFunction (code scenario)) []
      (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.stop (by intros; intro impossible; cases impossible) _ (by intro impossible; cases impossible)
  apply Semantics.EvalStmt.expressionFault rfl
  apply Semantics.EvalExpr.ifTrue (value := .bool true) rfl
  · apply Semantics.EvalExpr.call rfl (.cons (calldata_source _ _ _) (.cons (.word (text := "0") rfl) .nil))
    exact .primitive rfl rfl
  · rfl
  · exact .call rfl .nil (.function (function := parent scenario) rfl (parent_source object scenario image))


def runtimeNames : List String := ["mstore8", "sstore", "sload", "calldatasize", "return", "revert"]
def usedNames : List String := runtimeNames ++ ["call"]

private theorem atoms {supported : String → Prop} (scenario : Scenario) (type : Ty) (name : String)
    (arguments : List String) (available : supported name)
    (absent : (functions scenario).find? (·.name == name) = none) :
    ExecutableExpression supported (functions scenario) (call type name (arguments.map word)) := by
  apply ExecutableExpression.external (name := name) available absent
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

private theorem parent_eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ∀ statement ∈ (parent scenario).body, ExecutableStatement supported (functions scenario) statement := by
  intro statement member
  simp only [parent, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["0", "1"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "mstore8" ["6", "170"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "sstore" ["7", "42"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) rfl
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · exact atoms _ .word "call" ["100", "100", "0", "0", "1", "2", "2"] (available _ (by simp [usedNames])) rfl
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) rfl
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · exact atoms _ .word "sload" ["8"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · cases scenario <;> first
      | exact atoms _ .unit "return" ["0", "7"] (available _ (by simp [usedNames, runtimeNames])) rfl
      | exact atoms _ .unit "revert" ["0", "7"] (available _ (by simp [usedNames, runtimeNames])) rfl

private theorem child_eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ∀ statement ∈ child.body, ExecutableStatement supported (functions scenario) statement := by
  intro statement member
  simp only [child, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["1", "187"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "sstore" ["8", "99"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "return" ["0", "2"] (available _ (by simp [usedNames, runtimeNames])) rfl

private theorem branch_eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableExpression supported (functions scenario) branch := by
  apply ExecutableExpression.conditional
  · apply ExecutableExpression.builtin (name := "eq") rfl rfl
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact atoms _ .word "calldatasize" [] (available _ (by simp [usedNames, runtimeNames])) rfl
    · exact .word _ _ _
  · exact .named (function := parent scenario) rfl (by simp) _ _
  · exact .named (function := child) rfl (by simp) _ _

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) : ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact parent_eligible scenario available statement statementMember
  · exact child_eligible scenario available statement statementMember
  · simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
    subst statement
    simpa only [expression, ExecutableStatement] using branch_eligible scenario available

private theorem runtime_supported : ∀ name ∈ runtimeNames, ContractCodeCorrespondence.supported name := by
  intro name member
  simp only [runtimeNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (⟨.store8, rfl⟩))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.store false, rfl⟩)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.load false, rfl⟩)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.direct .calldataSize, rfl, by intro input member; simp [EnvironmentBuiltinCorrespondence.inputs] at member; subst input; simp [Effects.slots, EnvironmentSemantics.Direct.slot]⟩))))))
  · exact .inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))
  · exact .inl (.inl (.inl (.inl (.inr ⟨.reverted, rfl⟩))))

theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with prior | rfl
  · exact .inl (.inl (runtime_supported name prior))
  · exact .inr (.inl rfl)

end Tests.RustHullRootCallCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullRootCallPublic
/-! The actual accepted root compilation establishes its code identity and
captured closure. No catalog entry or assumed Core execution is required. -/
set_option autoImplicit false
namespace Tests.RustHullRootCallCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
private abbrev number := Core.Word.ofNatModulo

def anchors : List CatalogWorldCorrespondence.Anchor := [⟨number 100, rootBytes, 1⟩]

theorem catalog_connection (scenario : Scenario) :
    RootChildCatalogExecutionCorrespondence.CatalogConnection
      (sourceCode scenario) (catalog scenario) [] anchors := by
  intro target source selected
  by_cases root : number 100 == target
  · have addressEq : number 100 = target := by simpa only [beq_iff_eq] using root
    subst target
    have sourceEq : sourceCode scenario = source := by
      simpa [ChildFrameSemantics.select, ChildFrameModeSemantics.select, catalog] using selected
    subst source
    exact .inl ⟨rfl, by simp [anchors, sourceCode]⟩
  · simp [ChildFrameSemantics.select, catalog, root] at selected

theorem initial_context_links (object : Contract.CompiledObject) :
    ContractRootCallCorrespondence.InitialContextLinks (some rootBytes) [] object context anchors := by
  intro anchor member
  simp only [anchors, List.mem_cons, List.not_mem_nil, or_false] at member
  subst anchor
  exact .inl ⟨rfl, rfl, rfl, rfl⟩

theorem public_evaluates (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Root"] 64 (some rootBytes) [] = .ok object) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      ContractRootCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value := by
  have image : object.codeImages.head?.getD none = some rootBytes := by
    rw [CatalogWorldCorrespondence.compileObject_images accepted]
    rfl
  exact ContractRootCallCorrespondence.compileObject_preserves (height := 0) (code := code scenario) rfl accepted
    (eligible scenario names_supported) (catalog_connection scenario) (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) context rfl
    (initial_context_links object) (source object scenario image)

theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Root"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractRootCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  have image : object.codeImages.head?.getD none = some rootBytes := by
    rw [CatalogWorldCorrespondence.compileObject_images accepted]
    rfl
  exact ContractRootCallCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) rfl accepted
    (eligible scenario names_supported) (catalog_connection scenario) (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) context rfl
    (initial_context_links object) (source object scenario image)

end Tests.RustHullRootCallCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullRootCallRuntime
/-! Reentry invokes the root closure with fresh calldata and memory while
sharing storage. Parent revert suppresses the complete transaction receipt. -/
set_option autoImplicit false
namespace Tests.RustHullRootCallRuntime
open Solcore Solcore.Frontend.RustHull RustHullRootCallCorrespondence

private abbrev w := Core.Word.ofNatModulo

private def expectedBytes : List UInt8 := [1, 1, 0, 187, 99, 0, 170]
private def expectedStorage : Core.WordMapping.Entries := [(w 7, w 42), (w 8, w 99)]
private def expectedBalances : Core.WordMapping.Entries :=
  Core.WordMapping.insertEntries context.address context.balance context.accounts

private def checkWorld (label : String) (world : List AccountState.Account) : IO Unit := do
  let some root := world.find? (·.address == w 100) |
    throw (IO.userError s!"root reentry {label}: missing root account")
  unless world.length == 1 && root.storage == expectedStorage && root.transient.isEmpty &&
      root.code == some rootBytes do
    throw (IO.userError s!"root reentry {label}: incorrect shared state: {reprStr world}")

private def checkReceipt (scenario : Scenario) (receipt : Contract.Receipt) : IO Unit := do
  match scenario, receipt.outcome with
  | .success, .returned bytes storage =>
      unless bytes == expectedBytes && storage == expectedStorage && receipt.logs.isEmpty &&
          receipt.balances == expectedBalances do
        throw (IO.userError s!"root reentry: incorrect successful receipt: {reprStr receipt}")
      checkWorld "receipt" receipt.world
  | .parentReverted, .reverted bytes =>
      unless bytes == expectedBytes && receipt.logs.isEmpty && receipt.world.isEmpty && receipt.balances.isEmpty do
        throw (IO.userError s!"root reentry: parent revert exported transaction changes: {reprStr receipt}")
  | _, outcome =>
      throw (IO.userError s!"root reentry: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Root"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"root reentry: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let mut checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"root reentry: zero fuel completed: {reprStr outcome}")
  for fuel in [19, 173, 997] do
    checkpoint ← match (Contract.resumeWithReceipt checkpoint fuel).outcome with
      | .outOfFuel next => pure next
      | outcome => throw (IO.userError s!"root reentry: short resumption completed: {reprStr outcome}")
  checkReceipt scenario (Contract.runWithReceipt prepared 4000000)
  checkReceipt scenario (Contract.resumeWithReceipt checkpoint 4000000)
  match Core.runStateful 4000000 (Core.State.initial prepared.expression) with
  | .done (.pair status (.pair exit (.pair offset (.pair count (.pair memory (.pair storage (.pair logs (.pair cursor (.pair balances world))))))))) _ =>
      let expected := (finalState object scenario).external
      let runtime := expected.runtime.runtime.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words &&
          storage == Core.WordMapping.encode expectedStorage &&
          logs == Core.WordMapping.encode expected.runtime.runtime.runtime.words &&
          cursor == .word expected.runtime.runtime.runtime.cursor &&
          balances == Core.WordMapping.encode expectedBalances &&
          status == .inLeft .unit (.word Core.Word.maximum) &&
          exit == .word runtime.storage.exit && offset == .word runtime.storage.returnOffset &&
          count == .word runtime.storage.returnSize do
        throw (IO.userError s!"root reentry: Core snapshot differs from source for {reprStr scenario}")
      let accounts ← match AccountState.decode world with
        | .ok accounts => pure accounts
        | .error error => throw (IO.userError s!"root reentry: invalid world snapshot: {error}")
      checkWorld "Core snapshot" accounts
  | outcome => throw (IO.userError s!"root reentry: Core execution failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.success, .parentReverted] do
    check scenario

end Tests.RustHullRootCallRuntime
end

section
-- leanmerge: from Solcore.Test.RustHullTerminationCorrespondence
/-! Message termination follows memory, event, and storage effects. The source
trace reaches actual public execution and resumption; later statements stay
unreachable, including when the termination range overflows. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullTerminationCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where | returned | reverted | stopped | invalid | overflow
  deriving DecidableEq, Repr

private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (name : String) (arguments : List Expr) : Expr := ⟨.unit, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def memoryWrite : Expr := call "mstore8" [word "1", word "171"]
def logWrite : Expr := call "log1" [word "1", word "33", word "7"]
def storageWrite : Expr := call "sstore" [word "7", word "42"]
def unreachableWrite : Expr := call "sstore" [word "8", word "99"]
def termination : Scenario → Expr
  | .returned => call "return" [word "1", word "1"]
  | .reverted => call "revert" [word "1", word "1"]
  | .stopped => call "stop" []
  | .invalid => call "invalid" []
  | .overflow => call "return" [word "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", word "1"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression memoryWrite, expression logWrite, expression storageWrite,
    expression (termination scenario), expression unreachableWrite]
  functions := []
}
def program (scenario : Scenario) : Program := {
  entryPoints := [], functions := [], objects := [.object "Termination" (code scenario) []]
}
def initial (object : Contract.CompiledObject) : Semantics.State RuntimeFullEffectsSemantics.State :=
  ⟨[], ContractFullCorrespondence.contextInitialState object (Contract.normalizeContext {})⟩
def memoryWritten (object : Contract.CompiledObject) : Semantics.State RuntimeFullEffectsSemantics.State :=
  ⟨[], {(initial object).external with runtime :=
    {(initial object).external.runtime with runtime :=
      {(initial object).external.runtime.runtime with memory := RustHullLogDerivations.firstMemory}}}⟩
def logged (object : Contract.CompiledObject) : Semantics.State RuntimeFullEffectsSemantics.State :=
  ⟨[], RuntimeLogEffectsSemantics.withLogs (memoryWritten object).external
    (RustHullLogDerivations.afterFirst Core.Word.zero)⟩
def stored (object : Contract.CompiledObject) : Semantics.State RuntimeFullEffectsSemantics.State :=
  ⟨[], {(logged object).external with runtime :=
    {(logged object).external.runtime with runtime :=
      {(logged object).external.runtime.runtime with storage :=
        (StorageSemantics.store (logged object).external.runtime.runtime.storage
          (Core.Word.ofNatModulo 7) (Core.Word.ofNatModulo 42) false).2}}}⟩
def terminated (object : Contract.CompiledObject) : Scenario → RuntimeEffectsSemantics.State
  | .returned => (TerminationSemantics.terminate (stored object).external.runtime.runtime 1 (Core.Word.ofNatModulo 1) (Core.Word.ofNatModulo 1)).2
  | .reverted => (TerminationSemantics.terminate (stored object).external.runtime.runtime 2 (Core.Word.ofNatModulo 1) (Core.Word.ofNatModulo 1)).2
  | .stopped => (TerminationSemantics.terminate (stored object).external.runtime.runtime 1 Core.Word.zero Core.Word.zero).2
  | .invalid => (TerminationSemantics.terminate (stored object).external.runtime.runtime 3 Core.Word.zero Core.Word.zero).2
  | .overflow => (stored object).external.runtime.runtime

def finalState (object : Contract.CompiledObject) (scenario : Scenario) : Semantics.State RuntimeFullEffectsSemantics.State :=
  ⟨[], {(stored object).external with runtime :=
    {(stored object).external.runtime with runtime := terminated object scenario}}⟩
def reason : Scenario → Core.Word
  | .overflow => Core.Word.ofNatModulo 6
  | _ => Core.Word.maximum

def result (scenario : Scenario) : Semantics.Result Semantics.Value := .fault (.language (reason scenario))

private theorem memory_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeFullEffectsSemantics.effects [] memoryWrite
      (initial object) (.value .unit) (memoryWritten object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime rfl))

private theorem log_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeFullEffectsSemantics.effects [] logWrite
      (memoryWritten object) (.value .unit) (logged object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "33") rfl) (.cons (.word (text := "7") rfl) .nil))
  · exact .external (by rfl) rfl (.runtime (.logs (.log .log1 .unit (Core.Word.ofNatModulo 1)
      (Core.Word.ofNatModulo 33) [Core.Word.ofNatModulo 7] rfl (RustHullLogDerivations.first_execute Core.Word.zero))))

private theorem storage_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeFullEffectsSemantics.effects [] storageWrite
      (logged object) (.value .unit) (stored object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "42") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime rfl))

private theorem termination_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeFullEffectsSemantics.effects [] (termination scenario)
      (stored object) (result scenario) (finalState object scenario) := by
  cases scenario
  case returned =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) .nil)
    · exact .external (by rfl) rfl (.termination rfl)
  case reverted =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) .nil)
    · exact .external (by rfl) rfl (.termination rfl)
  case stopped => exact .call rfl .nil (.external (by rfl) rfl (.termination rfl))
  case invalid => exact .call rfl .nil (.external (by rfl) rfl (.termination rfl))
  case overflow =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff") rfl)
        (.cons (.word (text := "1") rfl) .nil)
    · exact .external (by rfl) rfl (.termination rfl)

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] RuntimeFullEffectsSemantics.effects
      (AccountRuntime.frameFunction (code scenario)) [] (initial object) (result scenario) (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault (.language (reason scenario))) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (memory_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (log_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (storage_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (termination_source object scenario))
    (by intro impossible; cases impossible)

private theorem words_eligible {name : String} {texts : List String} (scenario : Scenario)
    (available : ContractFullCorrespondence.supported name)
    (absent : [AccountRuntime.frameFunction (code scenario)].find? (·.name == name) = none) :
    ExecutableExpression ContractFullCorrespondence.supported [AccountRuntime.frameFunction (code scenario)]
      (call name (texts.map word)) := by
  apply ExecutableExpression.external available absent
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

private theorem termination_eligible (scenario : Scenario) :
    ExecutableExpression ContractFullCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] (termination scenario) := by
  cases scenario
  case returned => exact words_eligible (texts := ["1", "1"]) .returned (Or.inr ⟨.returned, rfl⟩) rfl
  case reverted => exact words_eligible (texts := ["1", "1"]) .reverted (Or.inr ⟨.reverted, rfl⟩) rfl
  case stopped => exact words_eligible (texts := []) .stopped (Or.inr ⟨.stopped, rfl⟩) rfl
  case invalid => exact words_eligible (texts := []) .invalid (Or.inr ⟨.invalid, rfl⟩) rfl
  case overflow => exact words_eligible (texts := ["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", "1"]) .overflow (Or.inr ⟨.returned, rfl⟩) rfl

theorem eligible (scenario : Scenario) :
    ExecutableProgram ContractFullCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact words_eligible (texts := ["1", "171"]) scenario (Or.inl (Or.inl (Or.inl (Or.inl ⟨.store8, rfl⟩)))) rfl
  · exact words_eligible (texts := ["1", "33", "7"]) scenario (Or.inl (Or.inr ⟨.log1, rfl⟩)) rfl
  · exact words_eligible (texts := ["7", "42"]) scenario (Or.inl (Or.inl (Or.inl (Or.inr ⟨.store false, rfl⟩)))) rfl
  · exact termination_eligible scenario
  · exact words_eligible (texts := ["8", "99"]) scenario (Or.inl (Or.inl (Or.inl (Or.inr ⟨.store false, rfl⟩)))) rfl

theorem public_resumes (scenario : Scenario) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program scenario) ["Termination"] {} 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program scenario) ["Termination"] 64 none [] = .ok object ∧
      prepared = object.instantiate {} ∧
      ∃ value, ContractFullCorrespondence.PublicMessageRel {} (result scenario) (finalState object scenario).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractFullCorrespondence.prepare_resumes_exact
    (code := code scenario) (by rfl) accepted (eligible scenario) rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object scenario)⟩

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Termination"] 64 with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"termination correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate {}
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"termination correspondence: zero fuel completed: {reprStr result}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 11).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"termination correspondence: short resume completed: {reprStr result}")
  let receipt := Contract.resumeWithReceipt checkpoint 1000000
  let expectedStorage := [(Core.Word.ofNatModulo 7, Core.Word.ofNatModulo 42)]
  match scenario, receipt.outcome with
  | .returned, .returned bytes storage =>
      unless bytes == [171] && storage == expectedStorage do
        throw (IO.userError "termination correspondence: return bytes/storage differ")
  | .stopped, .returned bytes storage =>
      unless bytes.isEmpty && storage == expectedStorage do
        throw (IO.userError "termination correspondence: stop bytes/storage differ")
  | .reverted, .reverted bytes =>
      unless bytes == [171] do throw (IO.userError "termination correspondence: revert bytes differ")
  | .invalid, .invalid => pure ()
  | .overflow, .languageFailure (.word reason) =>
      unless reason == Core.Word.ofNatModulo 6 do throw (IO.userError "termination correspondence: overflow reason differs")
  | _, outcome => throw (IO.userError s!"termination correspondence: incorrect outcome: {reprStr outcome}")
  match scenario with
  | .returned | .stopped =>
      match receipt.logs with
      | [event] =>
          unless event.address == Core.Word.zero && event.topics == [Core.Word.ofNatModulo 7] &&
              event.data == [171] ++ List.replicate 32 0 do
            throw (IO.userError "termination correspondence: successful receipt lost event")
      | _ => throw (IO.userError "termination correspondence: incorrect event count")
  | _ =>
      unless receipt.logs.isEmpty && receipt.world.isEmpty do
        throw (IO.userError "termination correspondence: failed receipt exported effects")
  match Core.runStateful 1000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair count (.pair memory (.pair storage (.pair logs (.pair cursor _)))))))) _ =>
      let state := (finalState object scenario).external
      unless exit == .word state.runtime.runtime.storage.exit && offset == .word state.runtime.runtime.storage.returnOffset &&
          count == .word state.runtime.runtime.storage.returnSize && memory == Core.WordMapping.encode state.runtime.runtime.memory.words &&
          storage == Core.WordMapping.encode expectedStorage && logs == Core.WordMapping.encode state.words && cursor == .word state.cursor do
        throw (IO.userError "termination correspondence: Core snapshot differs from source")
  | outcome => throw (IO.userError s!"termination correspondence: Core failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.returned, .reverted, .stopped, .invalid, .overflow] do check scenario

end Tests.RustHullTerminationCorrespondence
end
