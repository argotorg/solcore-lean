import Solcore.Frontend.RustHull.ChildFrameModeSemantics
import Solcore.Frontend.RustHull.ContractCallModeSupported
import Solcore.Frontend.RustHull.ContractCallExecutionCorrespondence
import Solcore.Test.RustHullNestedChildCallCorrespondence

/-! A child schedules account destruction, then its parent observes the code
and continues. Transaction finalization and a parent revert are separate steps. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.RustHullLifecycleCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
private abbrev w := Core.Word.ofNatModulo
inductive Scenario where | existing | created | parentReverted
  deriving BEq, DecidableEq, Repr
def created (scenario : Scenario) : Bool := scenario != .existing
def reverts (scenario : Scenario) : Bool := scenario == .parentReverted
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def byte (offset data : String) : Expr := call .unit "mstore8" [word offset, word data]
def storage (key data : String) : Expr := call .unit "sstore" [word key, word data]
def childCode : CodeBlock := {stmts := [expression (byte "0" "187"), expression (storage "8" "99"),
  expression (call .unit "log0" [word "0", word "1"]), expression (call .unit "selfdestruct" [word "200"])], functions := []}
def invoke : Expr := call .word "call" [word "100", word "100", word "0", word "0", word "0", word "0", word "0"]
def storedStatus : Expr := call .unit "mstore8" [word "0", invoke]
def storedSize : Expr := call .unit "mstore8" [word "1", call .word "extcodesize" [word "100"]]
def finish (scenario : Scenario) : Expr := call .unit (if reverts scenario then "revert" else "return") [word "0", word "3"]
def code (scenario : Scenario) : CodeBlock := {stmts := [expression (byte "2" "170"), expression (storage "7" "42"),
  expression storedStatus, expression storedSize, expression (finish scenario)], functions := []}
def program (scenario : Scenario) : Program := {
  entryPoints := []
  functions := []
  objects := [.object "Parent" (code scenario) [], .object "Child" childCode []]
}
def childBytes : List UInt8 := [0x60, 0x00]
def compiledCatalog (scenario : Scenario) : List AccountRuntime.CodeDefinition :=
  [{program := program scenario, path := ["Child"], bytes := childBytes}]
def sourceCode (scenario : Scenario) : ChildFrameSemantics.Code := ⟨program scenario, childCode, childBytes⟩
def catalog (scenario : Scenario) : ChildFrameModeSemantics.Catalog := [(w 100, sourceCode scenario)]
def parentEffects (scenario : Scenario) := ChildFrameModeSemantics.effectsAt (catalog scenario) 1 none
def childEffects (scenario : Scenario) := ChildFrameModeSemantics.effectsAt (catalog scenario) 0 (some childBytes)
def parentFunctions (scenario : Scenario) := [AccountRuntime.frameFunction (code scenario)]
def childFunctions := [AccountRuntime.frameFunction childCode]
def childAccount (scenario : Scenario) : AccountState.Account :=
  {address := w 100, code := some childBytes, nonce := w 1, created := created scenario}
def context (scenario : Scenario) : Contract.Context :=
  {balance := w 100, accounts := [(w 100, w 60), (w 200, w 20)], world := [childAccount scenario], completeWorld := true}
abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def runtime (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withRuntime (state : SourceState) (next : RuntimeEffectsSemantics.State) : SourceState :=
  {state with external := {state.external with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime next}}
def written (state : SourceState) (offset data : Core.Word) : SourceState :=
  withRuntime state {runtime state with memory := (MemorySemantics.mstore8 (runtime state).memory offset data).2}
def stored (state : SourceState) (key data : Core.Word) : SourceState :=
  withRuntime state {runtime state with storage := (StorageSemantics.store (runtime state).storage key data false).2}
def initial (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState none object (Contract.normalizeContext (context scenario))⟩
def parentWritten (object : Contract.CompiledObject) (scenario : Scenario) := written (initial object scenario) (w 2) (w 170)
def parentBefore (object : Contract.CompiledObject) (scenario : Scenario) := stored (parentWritten object scenario) (w 7) (w 42)
def arguments (object : Contract.CompiledObject) (scenario : Scenario) :=
  RuntimeCallModeSemantics.arguments .ordinary (parentBefore object scenario).external (w 100) (w 100) (w 0) (w 0) (w 0) (w 0) (w 0)
def request (object : Contract.CompiledObject) (scenario : Scenario) := CallTransportSemantics.request (arguments object scenario) []
def childInitial (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], ChildFrameModeSemantics.initial .ordinary (w 0) (parentBefore object scenario).external
    (request object scenario) (RuntimeCallModeSemantics.shared (parentBefore object scenario).external) childBytes⟩
def childWritten (object : Contract.CompiledObject) (scenario : Scenario) := written (childInitial object scenario) (w 0) (w 187)
def childStored (object : Contract.CompiledObject) (scenario : Scenario) := stored (childWritten object scenario) (w 8) (w 99)
def childLogged (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := childStored object scenario
  let old := state.external.runtime.runtime.runtime
  let logs := RuntimeLogEffectsSemantics.logsState old
  let next := RuntimeLogEffectsSemantics.withLogs old {logs with
    words := Tests.RustHullNestedChildCallCorrespondence.logWords logs (w 0), cursor := LogsSemantics.nextCursor logs.cursor (w 1) []}
  {state with external := {state.external with runtime := {state.external.runtime with runtime := {state.external.runtime.runtime with runtime := next}}}}
def destroyedWorld (object : Contract.CompiledObject) (scenario : Scenario) :=
  AccountLifecycleSemantics.publish (runtime (childLogged object scenario)).storage.world (w 100)
    {childAccount scenario with storage := [(w 8, w 99)]}
def destroyedBalances : StorageSemantics.Words := [(w 100, w 0), (w 200, w 80), (w 0, w 100)]
def childFinal (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := childLogged object scenario
  {state with external := (RuntimeLifecycleSemantics.terminate
    (RuntimeLifecycleSemantics.updated state.external (destroyedWorld object scenario) destroyedBalances) 1).2}
def response : AccountCallSemantics.Response := AccountCallSemantics.emptyResponse true
def afterCall (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := parentBefore object scenario
  {state with external := (RuntimeCallModeSemantics.withTransport state.external ⟨(runtime state).memory, [], w 0⟩
    (RuntimeCallModeSemantics.shared (childFinal object scenario).external))}
def afterStatus (object : Contract.CompiledObject) (scenario : Scenario) := written (afterCall object scenario) (w 0) (w 1)
def afterSize (object : Contract.CompiledObject) (scenario : Scenario) := written (afterStatus object scenario) (w 1) (w 2)
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withRuntime (afterSize object scenario) (TerminationSemantics.terminate (runtime (afterSize object scenario))
    (if reverts scenario then 2 else 1) (w 0) (w 3)).2
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem child_written_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr childFunctions (childEffects scenario) [] (byte "0" "187")
      (childInitial object scenario) (.value .unit) (childWritten object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "187") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem child_stored_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr childFunctions (childEffects scenario) [] (storage "8" "99")
      (childWritten object scenario) (.value .unit) (childStored object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "8") rfl) (.cons (.word (text := "99") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem log_copied (state : LogsSemantics.State) :
    LogsSemantics.Copy state.memory.words (w 0) (w 1)
      (LogsSemantics.insertWords state.words state.cursor (LogsSemantics.headers state.address (w 1) []))
      (state.cursor.add (w 3)) (Tests.RustHullNestedChildCallCorrespondence.logWords state (w 0)) := by
  apply LogsSemantics.Copy.step (by decide +kernel)
  exact .empty _ _ _

private theorem child_logged_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr childFunctions (childEffects scenario) [] (call .unit "log0" [word "0", word "1"])
      (childStored object scenario) (.value .unit) (childLogged object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply RuntimeCallModeSemantics.Builtin.runtime
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
  · change ¬w 0 > LogsSemantics.nextCursor (w 0) (w 1) []
    decide +kernel
  · change MemorySemantics.touchSize? (w 32) (w 0) (w 1) = some (w 32)
    decide +kernel
  · exact log_copied _

private theorem child_world (object : Contract.CompiledObject) (scenario : Scenario) :
 (runtime (childLogged object scenario)).storage.world =
 StorageSemantics.put (w 100) {childAccount scenario with storage := [(w 8, w 99)]}
   (runtime (parentBefore object scenario)).storage.world := by
  have address : (runtime (childWritten object scenario)).storage.address = w 100 := by
    change (w 100).bitAnd (w (2 ^ 160 - 1)) = w 100
    decide +kernel
  have found : StorageSemantics.get (runtime (childWritten object scenario)).storage.world (w 100) true =
    .ok (childAccount scenario) := rfl
  change (StorageSemantics.store (runtime (childWritten object scenario)).storage (w 8) (w 99) false).2.world = _
  unfold StorageSemantics.store
  change (match StorageSemantics.writeStorage (runtime (childWritten object scenario)).storage.world
    (runtime (childWritten object scenario)).storage.address true (w 8) (w 99) false with
    | .ok world => world
    | .error _ => (runtime (childWritten object scenario)).storage.world) = _
  rw [address]
  unfold StorageSemantics.writeStorage
  rw [found]
  rfl

theorem child_destroyed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr childFunctions (childEffects scenario) [] (call .unit "selfdestruct" [word "200"])
      (childLogged object scenario) result (childFinal object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "200") rfl) .nil)
  apply Semantics.EvalCall.external rfl rfl
  apply RuntimeCallModeSemantics.Builtin.destroy
  apply RuntimeLifecycleSemantics.Destroy.completed (state := (childLogged object scenario).external) (world := destroyedWorld object scenario) (balances := destroyedBalances) rfl
  change AccountLifecycleSemantics.destroy (runtime (childLogged object scenario)).storage.world
    (childLogged object scenario).external.runtime.runtime.balances (w 100) (w 200) true =
      .ok (destroyedWorld object scenario, destroyedBalances)
  have found : StorageSemantics.get (runtime (childLogged object scenario)).storage.world (w 100) true =
      .ok {childAccount scenario with storage := [(w 8, w 99)]} := by
    rw [child_world]
    rfl
  unfold AccountLifecycleSemantics.destroy
  change (do
    let account ← StorageSemantics.get (runtime (childLogged object scenario)).storage.world (w 100) true
    let next ← AccountLifecycleSemantics.balances account.created (w 100) (w 200)
      (childLogged object scenario).external.runtime.runtime.balances
    pure (AccountLifecycleSemantics.publish (runtime (childLogged object scenario)).storage.world (w 100) account, next)) = _
  rw [found]
  cases scenario <;> rfl

theorem child_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction childFunctions (childEffects scenario) (AccountRuntime.frameFunction childCode) []
      (childInitial object scenario) result (childFinal object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_written_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_stored_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_logged_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (child_destroyed_source object scenario))
    (by intro impossible; cases impossible)

theorem child_response (object : Contract.CompiledObject) (scenario : Scenario) :
    ChildResultSemantics.Respond (ChildFrameModeSemantics.completedStatus result (runtime (childFinal object scenario)))
      (runtime (childFinal object scenario)) (.value response) := by
  apply ChildResultSemantics.Respond.returned (data := .value []) rfl
  exact .empty rfl

theorem child_called (object : Contract.CompiledObject) (scenario : Scenario) :
    ChildFrameModeSemantics.Children (catalog scenario) (ChildFrameModeSemantics.effectsAt (catalog scenario) 0)
      (parentBefore object scenario).external .ordinary (w 0) (request object scenario)
      (RuntimeCallModeSemantics.shared (parentBefore object scenario).external) (.value response)
      (RuntimeCallModeSemantics.shared (childFinal object scenario).external) := by
  apply ChildFrameModeSemantics.Children.executed (account := childAccount scenario) (code := sourceCode scenario)
  · change AccountCallSemantics.isPrecompile (w 100) = false
    decide +kernel
  · rfl
  · rfl
  · rfl
  · exact child_source object scenario
  · exact child_response object scenario

theorem invoked (object : Contract.CompiledObject) (scenario : Scenario) :
    RuntimeCallModeSemantics.Call (ChildFrameModeSemantics.Children (catalog scenario) (ChildFrameModeSemantics.effectsAt (catalog scenario) 0))
      .ordinary (w 100) (w 100) (w 0) (w 0) (w 0) (w 0) (w 0) (parentBefore object scenario).external
      (.value (.word (w 1))) (afterCall object scenario).external := by
  apply RuntimeCallModeSemantics.Call.invoked
  · exact .inr (.inl rfl)
  · intro _ impossible
    exact False.elim (impossible rfl)
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 32) rfl rfl
  apply CallTransportSemantics.Dispatch.returned (input := {}) (response := response) (result := .value .unit)
  · change ¬w 0 > w 1023
    decide +kernel
  · exact .done rfl (.empty _ _ _ _)
  · rfl
  · apply AccountCallSemantics.Dispatch.succeeded (transferred := RuntimeCallModeSemantics.shared (parentBefore object scenario).external)
    · exact .inr (by change ¬w 0 > w 100; decide +kernel)
    · rfl
    · exact .child (child_called object scenario)
    · rfl
  · exact .done rfl (.empty _ _ _ _)

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

private theorem call_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] invoke
      (parentBefore object scenario) (.value (.word (w 1))) (afterCall object scenario) := by
  apply Semantics.EvalExpr.call rfl
    (.cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl)
        (.cons (.word (text := "0") rfl) .nil)))))))
  exact .external rfl rfl (.call (invoked object scenario))

private theorem status_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] storedStatus
      (parentBefore object scenario) (.value .unit) (afterStatus object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (call_source object scenario) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply byte_builtin (size := w 32)
  change MemorySemantics.touchSize? (w 32) (w 0) (w 1) = some (w 32)
  decide +kernel

theorem code_still_observable (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (call .word "extcodesize" [word "100"])
      (afterStatus object scenario) (.value (.word (w 2))) (afterStatus object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "100") rfl) .nil)
  apply Semantics.EvalCall.external rfl rfl
  apply RuntimeCallModeSemantics.Builtin.runtime
  apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
  apply RuntimeCodeEffectsSemantics.Builtin.runtime
  apply RuntimeAccountEffectsSemantics.Builtin.observation
  apply AccountObservationSemantics.Builtin.sizeKnown (bytes := childBytes)
    (account := {childAccount scenario with storage := [(w 8, w 99)], destroyed := created scenario})
  · change StorageSemantics.get (destroyedWorld object scenario) (AccountObservationSemantics.address (w 100)) true = _
    have masked : AccountObservationSemantics.address (w 100) = w 100 := by decide +kernel
    rw [masked]
    unfold destroyedWorld
    rw [child_world]
    cases scenario <;> rfl
  · rfl

private theorem size_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] storedSize
      (afterStatus object scenario) (.value .unit) (afterSize object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "1") rfl) (.cons (code_still_observable object scenario) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply byte_builtin (size := w 32)
  change MemorySemantics.touchSize? (w 32) (w 1) (w 1) = some (w 32)
  decide +kernel

private theorem parent_written_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (byte "2" "170")
      (initial object scenario) (.value .unit) (parentWritten object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "2") rfl) (.cons (.word (text := "170") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem parent_stored_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (storage "7" "42")
      (parentWritten object scenario) (.value .unit) (parentBefore object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "7") rfl) (.cons (.word (text := "42") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem finish_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (finish scenario)
      (afterSize object scenario) result (finalState object scenario) := by
  cases scenario <;> apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "3") rfl) .nil))
  all_goals exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (parentFunctions scenario) (parentEffects scenario) (AccountRuntime.frameFunction (code scenario)) []
      (initial object scenario) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (parent_written_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (parent_stored_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (status_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (size_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (finish_source object scenario))
    (by intro impossible; cases impossible)

def runtimeNames : List String := ["mstore8", "sstore", "log0", "extcodesize", "return", "revert"]
def usedNames : List String := runtimeNames ++ ["call", "selfdestruct"]

private theorem atoms {supported : String → Prop} (functions : List Function) (type : Ty) (name : String)
    (arguments : List String) (available : supported name)
    (absent : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (call type name (arguments.map word)) := by
  apply ExecutableExpression.external (name := name) available absent
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

theorem child_eligible {supported : String → Prop} (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported childFunctions := by
  intro function member statement statementMember
  simp only [childFunctions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, childCode, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["0", "187"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "sstore" ["8", "99"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "log0" ["0", "1"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "selfdestruct" ["200"] (available _ (by simp [usedNames, runtimeNames])) rfl

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) : ExecutableProgram supported (parentFunctions scenario) := by
  intro function member statement statementMember
  simp only [parentFunctions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["2", "170"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "sstore" ["7", "42"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) rfl
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · exact atoms _ .word "call" ["100", "100", "0", "0", "0", "0", "0"] (available _ (by simp [usedNames])) rfl
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) rfl
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · exact atoms _ .word "extcodesize" ["100"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · cases scenario <;> first
      | exact atoms _ .unit "return" ["0", "3"] (available _ (by simp [usedNames, runtimeNames])) rfl
      | exact atoms _ .unit "revert" ["0", "3"] (available _ (by simp [usedNames, runtimeNames])) rfl

private theorem runtime_supported : ∀ name ∈ runtimeNames, ContractCodeCorrespondence.supported name := by
  intro name member
  simp only [runtimeNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (⟨.store8, rfl⟩))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.store false, rfl⟩)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inr ⟨.log0, rfl⟩)))))
  · exact .inl (.inr ⟨.size, rfl⟩)
  · exact .inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))
  · exact .inl (.inl (.inl (.inl (.inr ⟨.reverted, rfl⟩))))

theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with prior | rfl | rfl
  · exact .inl (.inl (runtime_supported name prior))
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inr (.inr (.inr rfl))))

end Tests.RustHullLifecycleCorrespondence
