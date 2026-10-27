import Solcore.Frontend.RustHull.ContractCallModeExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeSupported

/-! CREATE and CREATE2 attempts refused before init code runs reach the actual
lowering, transport and installed create handler through the call-mode public
theorem. Each scenario writes a byte, attempts a creation, stores its result
and returns two bytes. A static frame or oversized init code halts the frame,
a missing gas observation or an unaddressable init range faults, and an
insufficient endowment or an exhausted nonce returns zero without changing
the creator's nonce. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullCreationCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | staticFrame | oversized | missingGas | inputOverflow | underfunded | nonceExhausted
  | oversized2 | underfunded2
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩

def rootBytes : List UInt8 := [0]
def context : Scenario → Contract.Context
  | .staticFrame => {balance := w 3, availableGas := some (w 100), completeWorld := true, isStatic := true}
  | .missingGas => {balance := w 3, completeWorld := true}
  | .nonceExhausted => {balance := w 3, availableGas := some (w 100), completeWorld := true, nonce := w (2 ^ 64 - 1)}
  | _ => {balance := w 3, availableGas := some (w 100), completeWorld := true}

/-- Endowment, init offset and init length of each attempt. -/
def value : Scenario → Core.Word
  | .underfunded | .underfunded2 => w 5
  | _ => w 0
def offset : Scenario → Core.Word
  | .inputOverflow => w (Core.wordModulus - 16)
  | _ => w 0
def length : Scenario → Core.Word
  | .oversized | .oversized2 => w 49153
  | .inputOverflow => w 32
  | .underfunded | .underfunded2 | .nonceExhausted => w 2
  | _ => w 1

def invoked : Scenario → Expr
  | .staticFrame => call .word "create" [word "0", word "0", word "1"]
  | .oversized => call .word "create" [word "0", word "0", word "49153"]
  | .missingGas => call .word "create" [word "0", word "0", word "1"]
  | .inputOverflow => call .word "create" [word "0",
      word "115792089237316195423570985008687907853269984665640564039457584007913129639920", word "32"]
  | .underfunded => call .word "create" [word "5", word "0", word "2"]
  | .nonceExhausted => call .word "create" [word "0", word "0", word "2"]
  | .oversized2 => call .word "create2" [word "0", word "0", word "49153", word "7"]
  | .underfunded2 => call .word "create2" [word "5", word "0", word "2", word "7"]
def seed : Expr := call .unit "mstore8" [word "1", word "171"]
def stored (scenario : Scenario) : Expr := call .unit "mstore8" [word "2", invoked scenario]
def returned : Expr := call .unit "return" [word "1", word "2"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression seed, expression (stored scenario), expression returned], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Creator" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] {} 1 (some rootBytes)

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def frame (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withMemory (state : SourceState) (memory : MemorySemantics.State) : SourceState :=
  ⟨[], {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime
    {frame state with memory := memory})}⟩
def initial (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext (context scenario))⟩
def seeded : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 1) (w 171)).2
def memoryWritten (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withMemory (initial object scenario) seeded

/-- The frame state after the attempt: halted, unchanged, or refused with the
init range covered and return data cleared. -/
def afterAttempt (object : Contract.CompiledObject) : Scenario → SourceState
  | .staticFrame => ⟨[], (RuntimeCallEffectsSemantics.invalid (memoryWritten object .staticFrame).external).2⟩
  | .oversized => ⟨[], (RuntimeCallEffectsSemantics.invalid (memoryWritten object .oversized).external).2⟩
  | .oversized2 => ⟨[], (RuntimeCallEffectsSemantics.invalid (memoryWritten object .oversized2).external).2⟩
  | .missingGas => memoryWritten object .missingGas
  | .inputOverflow => memoryWritten object .inputOverflow
  | scenario => ⟨[], CreationSemantics.refused (memoryWritten object scenario).external (w 32)⟩
def attemptResult : Scenario → Semantics.Result Semantics.Value
  | .staticFrame | .oversized | .oversized2 => .fault (.language Core.Word.maximum)
  | .missingGas => .fault (.language (w 9))
  | .inputOverflow => MemorySemantics.overflow
  | _ => .value (.word (w 0))
def afterStore (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withMemory (afterAttempt object scenario) (MemorySemantics.mstore8 (frame (afterAttempt object scenario)).memory (w 2) (w 0)).2
def finished (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := (afterStore object scenario).external
  ⟨[], {state with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.runtime
    (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 1 (w 1) (w 2)).2)}⟩

/-- Refused attempts continue to the return; the others stop the frame. -/
def refuses : Scenario → Bool
  | .underfunded | .nonceExhausted | .underfunded2 => true
  | _ => false
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  if refuses scenario then finished object scenario else afterAttempt object scenario
def result (scenario : Scenario) : Semantics.Result Semantics.Value :=
  if refuses scenario then .fault (.language Core.Word.maximum) else attemptResult scenario

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] seed (initial object scenario) (.value .unit)
      (memoryWritten object scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

/-- The independent refusal of each attempt. -/
private theorem refused (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationSemantics.Refused (value scenario) (offset scenario) (length scenario)
      (memoryWritten object scenario).external (attemptResult scenario) (afterAttempt object scenario).external := by
  have gas : ∀ scenario, scenario ≠ .missingGas → scenario ≠ .staticFrame →
      CreationSemantics.availableGas (memoryWritten object scenario).external = some (w 100) := by
    intro scenario notMissing notStatic
    cases scenario <;> first | rfl | contradiction
  cases scenario
  · exact .staticFrame _ rfl
  · exact .oversized _ rfl (by decide)
  · exact .missingGas _ rfl (by decide) rfl
  · exact .inputOverflow _ rfl (by decide) (gas _ (by decide) (by decide))
      (by change MemorySemantics.touchSize? (w 32) (w (Core.wordModulus - 16)) (w 32) = none; decide)
  · apply CreationSemantics.Refused.underfunded rfl (by decide) (gas _ (by decide) (by decide))
      (by change MemorySemantics.touchSize? (w 32) (w 0) (w 2) = some (w 32); decide)
      (by change Core.Word.zero.val < CreationSemantics.depthLimit; decide)
    change (w 3).val < (w 5).val
    decide
  · apply CreationSemantics.Refused.nonceExhausted rfl (by decide) (gas _ (by decide) (by decide))
      (by change MemorySemantics.touchSize? (w 32) (w 0) (w 2) = some (w 32); decide)
      (by change Core.Word.zero.val < CreationSemantics.depthLimit; decide)
      (by change (w 0).val ≤ (w 3).val; decide) rfl
    change CreationSemantics.maxNonce ≤ (w (2 ^ 64 - 1)).val
    decide
  · exact .oversized _ rfl (by decide)
  · apply CreationSemantics.Refused.underfunded rfl (by decide) (gas _ (by decide) (by decide))
      (by change MemorySemantics.touchSize? (w 32) (w 0) (w 2) = some (w 32); decide)
      (by change Core.Word.zero.val < CreationSemantics.depthLimit; decide)
    change (w 3).val < (w 5).val
    decide

private theorem attempt_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] (invoked scenario) (memoryWritten object scenario)
      (attemptResult scenario) (afterAttempt object scenario) := by
  have computed := refused object scenario
  cases scenario
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil)))
      (.external (by rfl) rfl (.create computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "49153") rfl) .nil)))
      (.external (by rfl) rfl (.create computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil)))
      (.external (by rfl) rfl (.create computed))
  · exact .call rfl (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "115792089237316195423570985008687907853269984665640564039457584007913129639920") rfl)
        (.cons (.word (text := "32") rfl) .nil)))
      (.external (by rfl) rfl (.create computed))
  · exact .call rfl (.cons (.word (text := "5") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) .nil)))
      (.external (by rfl) rfl (.create computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) .nil)))
      (.external (by rfl) rfl (.create computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "49153") rfl)
      (.cons (.word (text := "7") rfl) .nil))))
      (.external (by rfl) rfl (.create2 (salt := w 7) computed))
  · exact .call rfl (.cons (.word (text := "5") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl)
      (.cons (.word (text := "7") rfl) .nil))))
      (.external (by rfl) rfl (.create2 (salt := w 7) computed))

private theorem store_source (object : Contract.CompiledObject) (scenario : Scenario) (refusing : refuses scenario = true) :
    Semantics.EvalExpr (functions scenario) effects [] (stored scenario) (memoryWritten object scenario)
      (.value .unit) (afterStore object scenario) := by
  cases scenario
  all_goals first
    | exact absurd refusing (by decide)
    | apply Semantics.EvalExpr.call rfl
      · exact .cons (.word (text := "2") rfl) (.cons (attempt_source object _) .nil)
      · exact .external (by rfl) rfl
          (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem store_fault (object : Contract.CompiledObject) (scenario : Scenario) (stopping : refuses scenario = false) :
    ∃ reason, attemptResult scenario = .fault reason ∧
      Semantics.EvalExpr (functions scenario) effects [] (stored scenario) (memoryWritten object scenario)
        (.fault reason) (afterAttempt object scenario) := by
  have attempted := attempt_source object scenario
  obtain ⟨reason, faulted⟩ : ∃ reason, attemptResult scenario = .fault reason := by
    cases scenario <;> first | exact ⟨_, rfl⟩ | cases stopping
  rw [faulted] at attempted
  exact ⟨reason, faulted, .callFault rfl (.cons (.word (text := "2") rfl) (.fault attempted))⟩

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] returned (afterStore object scenario)
      (.fault (.language Core.Word.maximum)) (finished object scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "2") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object scenario) (result scenario) (finalState object scenario) := by
  cases refusing : refuses scenario
  · obtain ⟨reason, faulted, attempted⟩ := store_fault object scenario refusing
    have resulted : result scenario = .fault reason := by simp [result, refusing, faulted]
    have final : finalState object scenario = afterAttempt object scenario := by simp [finalState, refusing]
    rw [resulted, final]
    apply Semantics.EvalFunction.body (control := .fault reason) rfl
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
      (.expression rfl (seed_source object scenario))
    exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl attempted)
      (by intro impossible; cases impossible)
  · have resulted : result scenario = .fault (.language Core.Word.maximum) := by simp [result, refusing]
    have final : finalState object scenario = finished object scenario := by simp [finalState, refusing]
    rw [resulted, final]
    apply Semantics.EvalFunction.body (control := .fault _) rfl
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
      (.expression rfl (seed_source object scenario))
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
      (.expression rfl (store_source object scenario refusing))
    exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object scenario))
      (by intro impossible; cases impossible)

def usedNames : List String := ["mstore8", "create", "create2", "return"]

private theorem atoms {supported : String → Prop} (functions : List Function) (type : Ty) (name : String)
    (texts : List String) (available : supported name) (notFunction : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (call type name (texts.map word)) := by
  apply ExecutableExpression.external available notFunction
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["1", "171"] (available _ (by simp [usedNames])) (by rfl)
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases scenario <;> first
        | exact atoms _ .word "create" ["0", "0", "1"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create" ["0", "0", "49153"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create" ["0",
            "115792089237316195423570985008687907853269984665640564039457584007913129639920", "32"]
            (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create" ["5", "0", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create" ["0", "0", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create2" ["0", "0", "49153", "7"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create2" ["5", "0", "2", "7"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "return" ["1", "2"] (available _ (by simp [usedNames])) (by rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store8, rfl⟩)))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) (scenario : Scenario) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object (context scenario) [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for every refusal reachable from
the outermost frame. The depth refusal needs a frame at depth 1024. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Creator"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel (context scenario) (result scenario)
        (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate (context scenario)) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) (context scenario)
    (by cases scenario <;> rfl) (empty_links object scenario) (source object scenario)

private def expectedNonce (scenario : Scenario) : Core.Word :=
  if scenario = .nonceExhausted then w (2 ^ 64 - 1) else w 1

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Creator"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"creation correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate (context scenario)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"creation correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match scenario, receipt.outcome with
    | .staticFrame, .invalid | .oversized, .invalid | .oversized2, .invalid => pure ()
    | .missingGas, .languageFailure reason =>
        unless reason == .word (w 9) do
          throw (IO.userError s!"creation correspondence: wrong gas fault: {reprStr reason}")
    | .inputOverflow, .languageFailure reason =>
        unless reason == .word Memory.overflowReason do
          throw (IO.userError s!"creation correspondence: wrong range fault: {reprStr reason}")
    | _, .returned bytes storage =>
        let account := receipt.world.find? (·.address == Core.Word.zero)
        unless refuses scenario && bytes == [171, 0] && storage.isEmpty && receipt.logs.isEmpty &&
            receipt.balances == [(w 0, w 3)] && receipt.world.length == 1 &&
            account.map (·.nonce) == some (expectedNonce scenario) do
          throw (IO.userError s!"creation correspondence: wrong refusal for {reprStr scenario}: {reprStr receipt}")
    | _, outcome =>
        throw (IO.userError s!"creation correspondence: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.staticFrame, .oversized, .missingGas, .inputOverflow, .underfunded,
      .nonceExhausted, .oversized2, .underfunded2] do
    check scenario

end Tests.RustHullCreationCorrespondence
