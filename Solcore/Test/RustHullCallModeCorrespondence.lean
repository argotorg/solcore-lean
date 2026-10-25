import Solcore.Frontend.RustHull.ChildFrameModeSemantics
import Solcore.Frontend.RustHull.ContractCallExecutionCorrespondence
import Solcore.Test.RustHullNestedChildCallCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeSupported

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
def parentEffects (scenario : Scenario) := ChildFrameModeSemantics.effectsAt (catalog scenario) 1 none
def childEffects (scenario : Scenario) := ChildFrameModeSemantics.effectsAt (catalog scenario) 0 (some childBytes)
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
    ChildFrameModeSemantics.Children (catalog scenario) (ChildFrameModeSemantics.effectsAt (catalog scenario) 0)
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
    RuntimeCallModeSemantics.Call (ChildFrameModeSemantics.Children (catalog scenario) (ChildFrameModeSemantics.effectsAt (catalog scenario) 0))
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
