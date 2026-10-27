import Solcore.Frontend.RustHull.ChildFrameModeSemantics
import Solcore.Frontend.RustHull.ContractCallExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeSupported

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
