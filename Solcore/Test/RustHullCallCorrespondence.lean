import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
import Solcore.Frontend.RustHull.ContractCallExecutionCorrespondence

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
