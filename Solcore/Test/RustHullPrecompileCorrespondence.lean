import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
import Solcore.Frontend.RustHull.ContractCallExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeExecutionCorrespondence

/-! Calls to the identity precompile reach the actual dispatcher and precompile
code. The child-free scenarios cover a funded copy, insufficient forwarded gas,
a value transfer to the precompiled account and a static call, followed by the
caller's output copy and public resumption. CALLCODE and DELEGATECALL reach the
same precompile through the call-mode theorem. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullPrecompileCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | identity | underfunded | transfer | staticCall
  deriving DecidableEq, Repr
private abbrev w := Core.Word.ofNatModulo
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def context : Contract.Context := {balance := w 10, completeWorld := true}
def operation (scenario : Scenario) : RuntimeCallEffectsSemantics.Operation :=
  if scenario = .staticCall then .staticCall else .ordinary
def gasText (scenario : Scenario) : String := if scenario = .underfunded then "17" else "100"
def gas (scenario : Scenario) : Core.Word := if scenario = .underfunded then w 17 else w 100
def valueText (scenario : Scenario) : String := if scenario = .transfer then "3" else "0"
def value (scenario : Scenario) : Core.Word := if scenario = .transfer then w 3 else w 0
def seed : Expr := call .unit "mstore8" [word "1", word "171"]
def invoked (scenario : Scenario) : Expr :=
  let tail := [word "1", word "1", word "3", word "2"]
  if scenario = .staticCall then call .word "staticcall" ([word (gasText scenario), word "4"] ++ tail)
  else call .word "call" ([word (gasText scenario), word "4", word (valueText scenario)] ++ tail)
def stored (scenario : Scenario) : Expr := call .unit "mstore8" [word "2", invoked scenario]
def returned : Expr := call .unit "return" [word "1", word "3"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression seed, expression (stored scenario), expression returned], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Precompile" (code scenario) []]}
abbrev SourceState := Semantics.State RuntimeCallEffectsSemantics.State

def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ⟨⟨ContractCodeCorrespondence.contextInitialState none object (Contract.normalizeContext context), []⟩, w 0⟩⟩
def withMemory (state : SourceState) (memory : MemorySemantics.State) : SourceState :=
  ⟨[], {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime
    {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory})}⟩
def seeded : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 1) (w 171)).2
def memoryWritten (object : Contract.CompiledObject) : SourceState := withMemory (initial object) seeded

/-- The caller's one-byte input snapshot and the identity output copied from it. -/
def input : MemorySemantics.State :=
  ⟨MemoryCopySemantics.written [] (w 0) (w 1) (MemoryCopySemantics.copiedWord seeded.words (w 1) (w 1)), w 32⟩
def output : MemorySemantics.Entries :=
  MemoryCopySemantics.written [] (w 0) (w 1) (MemoryCopySemantics.copiedWord input.words (w 0) (w 1))
def response (scenario : Scenario) : AccountCallSemantics.Response :=
  if scenario = .underfunded then AccountCallSemantics.emptyResponse false else ⟨true, output, w 1⟩
def status (scenario : Scenario) : Core.Word := if scenario = .underfunded then w 0 else w 1
def copiedMemory (scenario : Scenario) : MemorySemantics.State :=
  if scenario = .underfunded then ⟨seeded.words, w 32⟩
  else ⟨MemoryCopySemantics.written seeded.words (w 3) (w 1) (MemoryCopySemantics.copiedWord output (w 0) (w 1)), w 32⟩
def sharedAfter (object : Contract.CompiledObject) (scenario : Scenario) : AccountCallSemantics.Shared :=
  let old := RuntimeCallEffectsSemantics.shared (memoryWritten object).external
  if scenario = .transfer then {old with balances := [(w 0, w 7), (w 4, w 3)]} else old
def nextTransport (scenario : Scenario) : CallTransportSemantics.State :=
  ⟨copiedMemory scenario, (response scenario).data, (response scenario).size⟩
def afterCall (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], RuntimeCallEffectsSemantics.withTransport (memoryWritten object).external (nextTransport scenario)
    (sharedAfter object scenario)⟩
def afterStore (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withMemory (afterCall object scenario) (MemorySemantics.mstore8 (copiedMemory scenario) (w 2) (status scenario)).2
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := (afterStore object scenario).external
  ⟨[], {state with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.runtime
    (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 1 (w 1) (w 3)).2)}⟩
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] seed
      (initial object) (.value .unit) (memoryWritten object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem input_copied :
    MemoryCopySemantics.From seeded.words (w 0) (w 1) (w 1) {} (.value .unit) input := by
  apply MemoryCopySemantics.From.done (by decide +kernel)
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  change MemoryCopySemantics.Copy _ _ _ ((w 1).sub (w 1)) input.words input.words
  rw [show (w 1).sub (w 1) = Core.Word.zero from by decide +kernel]
  exact .empty _ _ _ _

/-- The independent identity meaning: a byte copy of the complete input. -/
private theorem identity_copied :
    MemoryCopySemantics.Copy input.words Core.Word.zero Core.Word.zero (w 1) [] output := by
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  change MemoryCopySemantics.Copy _ _ _ ((w 1).sub (w 1)) output output
  rw [show (w 1).sub (w 1) = Core.Word.zero from by decide +kernel]
  exact .empty _ _ _ _

private theorem output_copied :
    MemoryCopySemantics.Copy output (w 3) Core.Word.zero (w 1) seeded.words (copiedMemory .identity).words := by
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  change MemoryCopySemantics.Copy _ _ _ ((w 1).sub (w 1)) (copiedMemory .identity).words (copiedMemory .identity).words
  rw [show (w 1).sub (w 1) = Core.Word.zero from by decide +kernel]
  exact .empty _ _ _ _

private theorem transfer_balances :
    AccountCallSemantics.transfer (w 0) (w 4) (w 3) [(w 0, w 10)] = .ok [(w 0, w 7), (w 4, w 3)] := by
  have computed : (AccountCallSemantics.transfer (w 0) (w 4) (w 3) [(w 0, w 10)]).toOption =
      some [(w 0, w 7), (w 4, w 3)] := by decide +kernel
  cases found : AccountCallSemantics.transfer (w 0) (w 4) (w 3) [(w 0, w 10)] with
  | error error => simp [found, Except.toOption] at computed
  | ok entries => exact congrArg Except.ok (Option.some.inj (by simpa only [found, Except.toOption] using computed))

private theorem target_masked : (w 4).bitAnd (w (2 ^ 160 - 1)) = w 4 := by decide +kernel

private theorem invoked_source (object : Contract.CompiledObject) (scenario : Scenario) :
    RuntimeCallEffectsSemantics.Call (fun _ => AccountCallSemantics.noChildren) (operation scenario)
      (gas scenario) (w 4) (value scenario) (w 1) (w 1) (w 3) (w 2)
      (memoryWritten object).external (.value (.word (status scenario))) (afterCall object scenario).external := by
  apply RuntimeCallEffectsSemantics.Call.invoked
  · cases scenario
    · exact .inr (.inl rfl)
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)
    · exact .inl rfl
  · intros ordinary nonzero
    cases scenario <;> first | exact False.elim (nonzero rfl) | decide +kernel
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 32)
  · change MemorySemantics.touchSize? seeded.size (w 1) (w 1) = some (w 32)
    decide +kernel
  · change MemorySemantics.touchSize? (w 32) (w 3) (w 2) = some (w 32)
    decide +kernel
  cases scenario
  case identity =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := response .identity) (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · apply AccountCallSemantics.Dispatch.succeeded
        (transferred := RuntimeCallEffectsSemantics.shared (memoryWritten object).external)
      · exact .inr (by change ¬w 0 > w 10; decide +kernel)
      · rfl
      · apply AccountCallSemantics.Run.precompile
        apply AccountCallSemantics.Precompile.identity (size := w 32)
        · exact target_masked
        · change MemorySemantics.touchSize? Core.Word.zero Core.Word.zero (w 1) = some (w 32)
          decide +kernel
        · change AccountCallSemantics.linearCost 15 3 (w 1) ≤ (w 100).val
          decide
        · exact identity_copied
      · rfl
    · apply MemoryCopySemantics.From.done (size := w 32)
      · change MemorySemantics.touchSize? (w 32) (w 3) (w 1) = some (w 32)
        decide +kernel
      · exact output_copied
  case underfunded =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := response .underfunded) (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · apply AccountCallSemantics.Dispatch.refused
        (transferred := RuntimeCallEffectsSemantics.shared (memoryWritten object).external)
      · exact .inr (by change ¬w 0 > w 10; decide +kernel)
      · rfl
      · apply AccountCallSemantics.Run.precompile
        apply AccountCallSemantics.Precompile.identityUnderfunded (size := w 32)
        · exact target_masked
        · change MemorySemantics.touchSize? Core.Word.zero Core.Word.zero (w 1) = some (w 32)
          decide +kernel
        · change (w 17).val < AccountCallSemantics.linearCost 15 3 (w 1)
          decide
      · rfl
    · exact .done rfl (.empty _ _ _ _)
  case transfer =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := response .transfer) (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · apply AccountCallSemantics.Dispatch.succeeded (transferred := sharedAfter object .transfer)
      · exact .inr (by change ¬w 3 > w 10; decide +kernel)
      · dsimp only [AccountCallSemantics.transferFor]
        simp only [show (AccountCallSemantics.Mode.ordinary == .ordinary) = true from rfl, ↓reduceIte]
        have moved : AccountCallSemantics.transfer (w 0) ((w 4).bitAnd (w (2 ^ 160 - 1))) (w 3) [(w 0, w 10)] =
            .ok [(w 0, w 7), (w 4, w 3)] := by
          rw [target_masked]
          exact transfer_balances
        change Except.map _ (AccountCallSemantics.transfer (w 0) ((w 4).bitAnd (w (2 ^ 160 - 1))) (w 3) [(w 0, w 10)]) = _
        rw [moved]
        rfl
      · apply AccountCallSemantics.Run.precompile
        apply AccountCallSemantics.Precompile.identity (size := w 32)
        · exact target_masked
        · change MemorySemantics.touchSize? Core.Word.zero Core.Word.zero (w 1) = some (w 32)
          decide +kernel
        · change AccountCallSemantics.linearCost 15 3 (w 1) ≤ ((w 100).add (w 2300)).val
          decide +kernel
        · exact identity_copied
      · rfl
    · apply MemoryCopySemantics.From.done (size := w 32)
      · change MemorySemantics.touchSize? (w 32) (w 3) (w 1) = some (w 32)
        decide +kernel
      · exact output_copied
  case staticCall =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := response .staticCall) (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · apply AccountCallSemantics.Dispatch.succeeded
        (transferred := RuntimeCallEffectsSemantics.shared (memoryWritten object).external)
      · exact .inr (by change ¬w 0 > w 10; decide +kernel)
      · rfl
      · apply AccountCallSemantics.Run.precompile
        apply AccountCallSemantics.Precompile.identity (size := w 32)
        · exact target_masked
        · change MemorySemantics.touchSize? Core.Word.zero Core.Word.zero (w 1) = some (w 32)
          decide +kernel
        · change AccountCallSemantics.linearCost 15 3 (w 1) ≤ (w 100).val
          decide
        · exact identity_copied
      · rfl
    · apply MemoryCopySemantics.From.done (size := w 32)
      · change MemorySemantics.touchSize? (w 32) (w 3) (w 1) = some (w 32)
        decide +kernel
      · exact output_copied

private theorem call_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] (invoked scenario)
      (memoryWritten object) (.value (.word (status scenario))) (afterCall object scenario) := by
  cases scenario <;> apply Semantics.EvalExpr.call rfl
  all_goals first
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "4") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "2") rfl) .nil)))))))
    | exact (.cons (.word (text := "17") rfl) (.cons (.word (text := "4") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "2") rfl) .nil)))))))
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "4") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "2") rfl) .nil)))))))
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "4") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "2") rfl) .nil))))))
    | exact .external (by rfl) rfl (.call (invoked_source object .identity))
    | exact .external (by rfl) rfl (.call (invoked_source object .underfunded))
    | exact .external (by rfl) rfl (.call (invoked_source object .transfer))
    | exact .external (by rfl) rfl (.staticCall (invoked_source object .staticCall))

private theorem store_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] (stored scenario)
      (memoryWritten object) (.value .unit) (afterStore object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "2") rfl) (.cons (call_source object scenario) .nil))
  cases scenario <;>
    exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] returned
      (afterStore object scenario) result (finalState object scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) .nil)
  · cases scenario <;>
      exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none)
      (AccountRuntime.frameFunction (code scenario)) [] (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object _))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (store_source object _))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object _))
    (by intro impossible; cases impossible)

def usedNames : List String := ["mstore8", "call", "staticcall", "return"]

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
  rcases statementMember with rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["1", "171"] (available _ (by simp [usedNames])) (by rfl)
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases scenario <;> first
        | exact atoms _ .word "staticcall" ["100", "4", "1", "1", "3", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["100", "4", "0", "1", "1", "3", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["17", "4", "0", "1", "1", "3", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["100", "4", "3", "1", "1", "3", "2"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "return" ["1", "3"] (available _ (by simp [usedNames])) (by rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallCorrespondence.supported false name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store8, rfl⟩))))))))
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)
  · exact .inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩)))))

/-- Public consumer: actual compilation success is the only premise besides the
independent source derivation constructed above. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Precompile"] 64 none [] = .ok object) :
    ∃ value, ContractCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallCorrespondence.compileObject_resumes_exact (code := code scenario) (by rfl) accepted
    (eligible scenario names_supported) context rfl (source object scenario)

theorem public_prepared (scenario : Scenario) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program scenario) ["Precompile"] context 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program scenario) ["Precompile"] 64 none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∃ value, ContractCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractCallCorrespondence.prepare_resumes_exact
    (code := code scenario) (by rfl) accepted (eligible scenario names_supported) rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object scenario)⟩

private def expectedBytes (scenario : Scenario) : List UInt8 :=
  if scenario = .underfunded then [171, 0, 0] else [171, 1, 171]
private def expectedBalances (scenario : Scenario) : Core.WordMapping.Entries :=
  if scenario = .transfer then [(w 0, w 7), (w 4, w 3)] else [(w 0, w 10)]

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Precompile"] 64 none [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"precompile correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"precompile correspondence: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"precompile correspondence: short resume completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == expectedBytes scenario && storage.isEmpty && receipt.logs.isEmpty &&
            receipt.balances == expectedBalances scenario do
          throw (IO.userError s!"precompile correspondence: wrong result for {reprStr scenario}: {reprStr receipt}")
    | outcome => throw (IO.userError s!"precompile correspondence: expected return for {reprStr scenario}: {reprStr outcome}")
  match Core.runStateful 1000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair length (.pair memory (.pair _ (.pair _ (.pair _ (.pair balances _))))))))) _ =>
      let expected := (finalState object scenario).external
      let runtime := expected.runtime.runtime.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words &&
          balances == Core.WordMapping.encode (expectedBalances scenario) && exit == .word runtime.storage.exit &&
          offset == .word runtime.storage.returnOffset && length == .word runtime.storage.returnSize do
        throw (IO.userError s!"precompile correspondence: internal snapshot mismatch for {reprStr scenario}")
  | outcome => throw (IO.userError s!"precompile correspondence: Core failed: {reprStr outcome}")

namespace Modes

/-- CALLCODE with value and DELEGATECALL select the precompile by the requested
target. Neither moves balances; CALLCODE still checks the caller's funds. -/
inductive Scenario where
  | callCode | delegated
  deriving DecidableEq, Repr
def rootBytes : List UInt8 := [0]
def context : Contract.Context := {caller := w 55, value := w 7, balance := w 10, completeWorld := true}
def operation : Scenario → RuntimeCallModeSemantics.Operation
  | .callCode => .callCode | .delegated => .delegateCall
def invoked : Scenario → Expr
  | .callCode => call .word "callcode" [word "100", word "4", word "5", word "1", word "1", word "3", word "2"]
  | .delegated => call .word "delegatecall" [word "100", word "4", word "1", word "1", word "3", word "2"]
def stored (scenario : Scenario) : Expr := call .unit "mstore8" [word "2", invoked scenario]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression seed, expression (stored scenario), expression returned], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Precompile" (code scenario) []]}
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] 1 (some rootBytes)

def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩
def memoryWritten (object : Contract.CompiledObject) : SourceState := withMemory (initial object) seeded
def value (object : Contract.CompiledObject) : Scenario → Core.Word
  | .callCode => w 5
  | .delegated => (RuntimeCallModeSemantics.observations (memoryWritten object).external).direct .callvalue
def afterCall (object : Contract.CompiledObject) : SourceState :=
  ⟨[], RuntimeCallEffectsSemantics.withTransport (memoryWritten object).external (nextTransport .identity)
    (RuntimeCallEffectsSemantics.shared (memoryWritten object).external)⟩
def afterStore (object : Contract.CompiledObject) : SourceState :=
  withMemory (afterCall object) (MemorySemantics.mstore8 (copiedMemory .identity) (w 2) (w 1)).2
def finalState (object : Contract.CompiledObject) : SourceState :=
  let state := (afterStore object).external
  ⟨[], {state with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.runtime
    (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 1 (w 1) (w 3)).2)}⟩

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] effects [] seed
      (initial object) (.value .unit) (memoryWritten object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem invoked_source (object : Contract.CompiledObject) (scenario : Scenario) :
    RuntimeCallModeSemantics.Call (ChildFrameModeSemantics.Children [] (ChildFrameModeSemantics.effectsAt [] 0))
      (operation scenario) (w 100) (w 4) (value object scenario) (w 1) (w 1) (w 3) (w 2)
      (memoryWritten object).external (.value (.word (w 1))) (afterCall object).external := by
  apply RuntimeCallModeSemantics.Call.invoked
  · exact .inl (by cases scenario <;> intro impossible <;> cases impossible)
  · intro stipend nonzero
    cases scenario
    · change ¬w 100 > w (Core.wordModulus - 2301)
      decide +kernel
    · cases stipend
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 32)
  · change MemorySemantics.touchSize? seeded.size (w 1) (w 1) = some (w 32)
    decide +kernel
  · change MemorySemantics.touchSize? (w 32) (w 3) (w 2) = some (w 32)
    decide +kernel
  apply CallTransportSemantics.Dispatch.returned (input := input) (response := response .identity) (result := .value .unit)
  · change ¬w 0 > w 1023
    decide +kernel
  · exact input_copied
  · rfl
  · apply AccountCallSemantics.Dispatch.succeeded
      (transferred := RuntimeCallEffectsSemantics.shared (memoryWritten object).external)
    · cases scenario
      · exact .inr (by change ¬w 5 > w 10; decide +kernel)
      · exact .inl rfl
    · cases scenario <;> rfl
    · apply AccountCallSemantics.Run.precompile
      apply AccountCallSemantics.Precompile.identity (size := w 32)
      · exact target_masked
      · change MemorySemantics.touchSize? Core.Word.zero Core.Word.zero (w 1) = some (w 32)
        decide +kernel
      · cases scenario
        · change AccountCallSemantics.linearCost 15 3 (w 1) ≤ ((w 100).add (w 2300)).val
          decide +kernel
        · change AccountCallSemantics.linearCost 15 3 (w 1) ≤ (w 100).val
          decide
      · exact identity_copied
    · rfl
  · apply MemoryCopySemantics.From.done (size := w 32)
    · change MemorySemantics.touchSize? (w 32) (w 3) (w 1) = some (w 32)
      decide +kernel
    · exact output_copied

private theorem call_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] effects [] (invoked scenario)
      (memoryWritten object) (.value (.word (w 1))) (afterCall object) := by
  cases scenario <;> apply Semantics.EvalExpr.call rfl
  case callCode.argumentsEvaluated =>
    exact .cons (.word (text := "100") rfl) (.cons (.word (text := "4") rfl) (.cons (.word (text := "5") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "2") rfl) .nil))))))
  case callCode.called => exact .external (by rfl) rfl (.callCode (invoked_source object .callCode))
  case delegated.argumentsEvaluated =>
    exact .cons (.word (text := "100") rfl) (.cons (.word (text := "4") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "2") rfl) .nil)))))
  case delegated.called => exact .external (by rfl) rfl (.delegateCall (invoked_source object .delegated))

private theorem store_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] effects [] (stored scenario)
      (memoryWritten object) (.value .unit) (afterStore object) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "2") rfl) (.cons (call_source object scenario) .nil))
  exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] effects [] returned
      (afterStore object) result (finalState object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] effects
      (AccountRuntime.frameFunction (code scenario)) [] (initial object) result (finalState object) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object _))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (store_source object _))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object _))
    (by intro impossible; cases impossible)

def usedNames : List String := ["mstore8", "callcode", "delegatecall", "return"]

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported [AccountRuntime.frameFunction (code scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
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
        | exact atoms _ .word "callcode" ["100", "4", "5", "1", "1", "3", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "delegatecall" ["100", "4", "1", "1", "3", "2"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "return" ["1", "3"] (available _ (by simp [usedNames])) (by rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store8, rfl⟩)))))))))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr (.inl rfl))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object context [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem: the empty catalog has no
selected child and no initial code links. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Precompile"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel context result (finalState object).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection context rfl (empty_links object)
    (source object scenario)

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Precompile"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"precompile mode correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"precompile mode correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == [171, 1, 171] && storage.isEmpty && receipt.logs.isEmpty &&
            receipt.balances == [(w 0, w 10)] do
          throw (IO.userError s!"precompile mode correspondence: wrong result for {reprStr scenario}: {reprStr receipt}")
    | outcome => throw (IO.userError s!"precompile mode correspondence: expected return for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.callCode, .delegated] do
    check scenario

end Modes

def run : IO Unit := do
  for scenario in [Scenario.identity, .underfunded, .transfer, .staticCall] do
    check scenario
  Modes.run

end Tests.RustHullPrecompileCorrespondence
