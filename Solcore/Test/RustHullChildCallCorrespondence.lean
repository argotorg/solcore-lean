import Solcore.Frontend.RustHull.ChildFrameSemantics
import Solcore.Frontend.RustHull.ContractCallExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractChildCallExecutionCorrespondence

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
