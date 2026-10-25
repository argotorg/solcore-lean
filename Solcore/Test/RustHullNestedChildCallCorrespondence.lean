import Solcore.Frontend.RustHull.ChildFrameSemantics
import Solcore.Frontend.RustHull.ContractCallExecutionCorrespondence

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
