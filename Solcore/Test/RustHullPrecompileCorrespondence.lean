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
  ChildFrameModeSemantics.effectsAt [] {} 1 (some rootBytes)

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
    RuntimeCallModeSemantics.Call (ChildFrameModeSemantics.Children [] (ChildFrameModeSemantics.effectsAt [] {} 0))
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
    accepted rfl (eligible scenario names_supported) empty_connection (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) context rfl (empty_links object)
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

namespace Digest

/-- The digest precompiles: SHA-256 at address 2 and RIPEMD-160 at address 3. -/
inductive Algorithm where
  | sha256 | ripemd160
  deriving DecidableEq, Repr

/-- "abc" from caller memory, digested and copied back into caller memory. The
underfunded scenario forwards one gas unit less than the charge for three
bytes: 72 for SHA-256 and 720 for RIPEMD-160. -/
inductive Scenario where
  | funded | underfunded
  deriving DecidableEq, Repr
def address : Algorithm → Nat | .sha256 => 2 | .ripemd160 => 3
def addressText : Algorithm → String | .sha256 => "2" | .ripemd160 => "3"
def gasText : Algorithm → Scenario → String
  | .sha256, .funded => "100" | .sha256, .underfunded => "71"
  | .ripemd160, .funded => "1000" | .ripemd160, .underfunded => "719"
def gas : Algorithm → Scenario → Core.Word
  | .sha256, .funded => w 100 | .sha256, .underfunded => w 71
  | .ripemd160, .funded => w 1000 | .ripemd160, .underfunded => w 719
def seeds : List Expr := [call .unit "mstore8" [word "0", word "97"], call .unit "mstore8" [word "1", word "98"],
  call .unit "mstore8" [word "2", word "99"]]
def invoked (algorithm : Algorithm) (scenario : Scenario) : Expr :=
  call .word "call" [word (gasText algorithm scenario), word (addressText algorithm), word "0", word "0", word "3",
    word "32", word "32"]
def stored (algorithm : Algorithm) (scenario : Scenario) : Expr :=
  call .unit "mstore8" [word "64", invoked algorithm scenario]
def returned : Expr := call .unit "return" [word "32", word "33"]
def code (algorithm : Algorithm) (scenario : Scenario) : CodeBlock := {
  stmts := seeds.map expression ++ [expression (stored algorithm scenario), expression returned], functions := []}
def program (algorithm : Algorithm) (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Digest" (code algorithm scenario) []]}

def first : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 0) (w 97)).2
def second : MemorySemantics.State := (MemorySemantics.mstore8 first (w 1) (w 98)).2
def third : MemorySemantics.State := (MemorySemantics.mstore8 second (w 2) (w 99)).2
def afterThird (object : Contract.CompiledObject) : SourceState := withMemory (initial object) third

/-- The three-byte input snapshot copied by the caller. -/
def input : MemorySemantics.State :=
  ⟨MemoryCopySemantics.written (MemoryCopySemantics.written (MemoryCopySemantics.written [] (w 0) (w 3)
      (MemoryCopySemantics.copiedWord third.words (w 0) (w 3))) (w 1) (w 2)
      (MemoryCopySemantics.copiedWord third.words (w 1) (w 2))) (w 2) (w 1)
      (MemoryCopySemantics.copiedWord third.words (w 2) (w 1)), w 32⟩
/-- The independent digest of the snapshot. -/
def digest : Algorithm → Core.Word
  | .sha256 => Sha256Semantics.digest (Sha256Semantics.compress Sha256Semantics.initial
      (Sha256Semantics.readBlock input.words Core.Word.zero (w 3) (Sha256Semantics.bitLength (w 3)) false))
  | .ripemd160 => Ripemd160Semantics.digest (Ripemd160Semantics.compress Ripemd160Semantics.initial
      (Ripemd160Semantics.readBlock input.words Core.Word.zero (w 3) (Ripemd160Semantics.bitLength (w 3)) false))
def response (algorithm : Algorithm) (scenario : Scenario) : AccountCallSemantics.Response :=
  if scenario = .underfunded then AccountCallSemantics.emptyResponse false
  else ⟨true, [(Core.Word.zero, digest algorithm)], w 32⟩
def status (scenario : Scenario) : Core.Word := if scenario = .underfunded then w 0 else w 1
def copiedMemory (algorithm : Algorithm) (scenario : Scenario) : MemorySemantics.State :=
  if scenario = .underfunded then ⟨third.words, w 64⟩
  else ⟨MemoryCopySemantics.written third.words (w 32) (w 32)
    (MemoryCopySemantics.copiedWord [(Core.Word.zero, digest algorithm)] (w 0) (w 32)), w 64⟩
def nextTransport (algorithm : Algorithm) (scenario : Scenario) : CallTransportSemantics.State :=
  ⟨copiedMemory algorithm scenario, (response algorithm scenario).data, (response algorithm scenario).size⟩
def afterCall (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) : SourceState :=
  ⟨[], RuntimeCallEffectsSemantics.withTransport (afterThird object).external (nextTransport algorithm scenario)
    (RuntimeCallEffectsSemantics.shared (afterThird object).external)⟩
def afterStore (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) : SourceState :=
  withMemory (afterCall object algorithm scenario)
    (MemorySemantics.mstore8 (copiedMemory algorithm scenario) (w 64) (status scenario)).2
def finalState (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) : SourceState :=
  let state := (afterStore object algorithm scenario).external
  ⟨[], {state with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.runtime
    (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 1 (w 32) (w 33)).2)}⟩

private theorem first_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none) []
      (call .unit "mstore8" [word "0", word "97"]) (initial object) (.value .unit) (withMemory (initial object) first) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0") rfl) (.cons (.word (text := "97") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem second_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none) []
      (call .unit "mstore8" [word "1", word "98"]) (withMemory (initial object) first) (.value .unit)
      (withMemory (initial object) second) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "98") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem third_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none) []
      (call .unit "mstore8" [word "2", word "99"]) (withMemory (initial object) second) (.value .unit)
      (afterThird object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "2") rfl) (.cons (.word (text := "99") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem input_copied :
    MemoryCopySemantics.From third.words (w 0) (w 0) (w 3) {} (.value .unit) input := by
  apply MemoryCopySemantics.From.done (by decide +kernel)
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  rw [show (((w 3).sub (Core.Word.ofNatModulo (MemoryCopySemantics.width (w 3)))).sub
      (Core.Word.ofNatModulo (MemoryCopySemantics.width ((w 3).sub (Core.Word.ofNatModulo (MemoryCopySemantics.width (w 3))))))).sub
      (Core.Word.ofNatModulo (MemoryCopySemantics.width (((w 3).sub (Core.Word.ofNatModulo (MemoryCopySemantics.width (w 3)))).sub
        (Core.Word.ofNatModulo (MemoryCopySemantics.width ((w 3).sub (Core.Word.ofNatModulo (MemoryCopySemantics.width (w 3))))))))) =
      Core.Word.zero from by decide +kernel]
  exact .empty _ _ _ _

private theorem output_copied (algorithm : Algorithm) :
    MemoryCopySemantics.Copy [(Core.Word.zero, digest algorithm)] (w 32) Core.Word.zero (w 32) third.words
      (copiedMemory algorithm .funded).words := by
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  rw [show (w 32).sub (Core.Word.ofNatModulo (MemoryCopySemantics.width (w 32))) = Core.Word.zero from by decide +kernel]
  exact .empty _ _ _ _

private theorem target_masked (algorithm : Algorithm) :
    (w (address algorithm)).bitAnd (w (2 ^ 160 - 1)) = w (address algorithm) := by
  cases algorithm <;> decide +kernel

private theorem precompile_source (algorithm : Algorithm) (scenario : Scenario)
    (request : AccountCallSemantics.Request) (target : request.target = w (address algorithm))
    (gasEq : request.gas = gas algorithm scenario) (calldata : request.calldata = input.words)
    (length : request.calldataSize = w 3) :
    AccountCallSemantics.Precompile request (.value (response algorithm scenario)) := by
  have valid : MemorySemantics.touchSize? Core.Word.zero Core.Word.zero request.calldataSize = some (w 32) := by
    rw [length]; decide +kernel
  cases algorithm <;> cases scenario
  · rw [show response .sha256 .funded = ⟨true, [(Core.Word.zero, digest .sha256)], w 32⟩ from rfl]
    apply AccountCallSemantics.Precompile.sha256 target valid (by rw [gasEq, length]; decide)
    rw [calldata, length]
    exact .last (by decide +kernel) (by decide +kernel)
  · exact AccountCallSemantics.Precompile.sha256Underfunded target valid (by rw [gasEq, length]; decide)
  · rw [show response .ripemd160 .funded = ⟨true, [(Core.Word.zero, digest .ripemd160)], w 32⟩ from rfl]
    apply AccountCallSemantics.Precompile.ripemd160 target valid (by rw [gasEq, length]; decide)
    rw [calldata, length]
    exact .last (by decide +kernel) (by decide +kernel)
  · exact AccountCallSemantics.Precompile.ripemd160Underfunded target valid (by rw [gasEq, length]; decide)

private theorem invoked_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    RuntimeCallEffectsSemantics.Call (fun _ => AccountCallSemantics.noChildren) .ordinary
      (gas algorithm scenario) (w (address algorithm)) (w 0) (w 0) (w 3) (w 32) (w 32)
      (afterThird object).external (.value (.word (status scenario))) (afterCall object algorithm scenario).external := by
  apply RuntimeCallEffectsSemantics.Call.invoked (.inr (.inl rfl)) (by intros _ nonzero; exact False.elim (nonzero rfl))
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 64)
  · change MemorySemantics.touchSize? third.size (w 0) (w 3) = some (w 32)
    decide +kernel
  · change MemorySemantics.touchSize? (w 32) (w 32) (w 32) = some (w 64)
    decide +kernel
  have computed := precompile_source algorithm scenario
    (CallTransportSemantics.request
      (RuntimeCallEffectsSemantics.arguments .ordinary (afterThird object).external (gas algorithm scenario)
        (w (address algorithm)) (w 0) (w 0) (w 3) (w 32) (w 32)) input.words)
    (target_masked algorithm) rfl rfl rfl
  cases scenario
  case funded =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := response algorithm .funded)
      (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · exact AccountCallSemantics.Dispatch.succeeded
        (transferred := RuntimeCallEffectsSemantics.shared (afterThird object).external)
        (.inr (by change ¬w 0 > w 10; decide +kernel)) rfl (.precompile computed) rfl
    · apply MemoryCopySemantics.From.done (size := w 64)
      · change MemorySemantics.touchSize? (w 64) (w 32) (w 32) = some (w 64)
        decide +kernel
      · exact output_copied algorithm
  case underfunded =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := response algorithm .underfunded)
      (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · exact AccountCallSemantics.Dispatch.refused
        (transferred := RuntimeCallEffectsSemantics.shared (afterThird object).external)
        (.inr (by change ¬w 0 > w 10; decide +kernel)) rfl (.precompile computed) rfl
    · exact .done rfl (.empty _ _ _ _)

private theorem call_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none) []
      (invoked algorithm scenario) (afterThird object) (.value (.word (status scenario)))
      (afterCall object algorithm scenario) := by
  cases algorithm <;> cases scenario <;> apply Semantics.EvalExpr.call rfl
  all_goals first
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "32") rfl) (.cons (.word (text := "32") rfl) .nil)))))))
    | exact (.cons (.word (text := "71") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "32") rfl) (.cons (.word (text := "32") rfl) .nil)))))))
    | exact (.cons (.word (text := "1000") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "32") rfl) (.cons (.word (text := "32") rfl) .nil)))))))
    | exact (.cons (.word (text := "719") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "32") rfl) (.cons (.word (text := "32") rfl) .nil)))))))
    | exact .external (by rfl) rfl (.call (invoked_source object .sha256 .funded))
    | exact .external (by rfl) rfl (.call (invoked_source object .sha256 .underfunded))
    | exact .external (by rfl) rfl (.call (invoked_source object .ripemd160 .funded))
    | exact .external (by rfl) rfl (.call (invoked_source object .ripemd160 .underfunded))

private theorem store_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none) []
      (stored algorithm scenario) (afterThird object) (.value .unit) (afterStore object algorithm scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "64") rfl) (.cons (call_source object algorithm scenario) .nil))
  cases algorithm <;> cases scenario <;>
    exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem return_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none) []
      returned (afterStore object algorithm scenario) result (finalState object algorithm scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "32") rfl) (.cons (.word (text := "33") rfl) .nil)
  · cases algorithm <;> cases scenario <;>
      exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none)
      (AccountRuntime.frameFunction (code algorithm scenario)) [] (initial object) result
      (finalState object algorithm scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (first_source object algorithm scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (second_source object algorithm scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (third_source object algorithm scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (store_source object algorithm scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object algorithm scenario))
    (by intro impossible; cases impossible)

def usedNames : List String := ["mstore8", "call", "return"]

theorem eligible (algorithm : Algorithm) (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported [AccountRuntime.frameFunction (code algorithm scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, seeds, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["0", "97"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "mstore8" ["1", "98"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "mstore8" ["2", "99"] (available _ (by simp [usedNames])) (by rfl)
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases algorithm <;> cases scenario <;> first
        | exact atoms _ .word "call" ["100", "2", "0", "0", "3", "32", "32"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["71", "2", "0", "0", "3", "32", "32"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["1000", "3", "0", "0", "3", "32", "32"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["719", "3", "0", "0", "3", "32", "32"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "return" ["32", "33"] (available _ (by simp [usedNames])) (by rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallCorrespondence.supported false name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store8, rfl⟩))))))))
  · exact .inr (.inl rfl)
  · exact .inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩)))))

/-- Public consumer for both digests: actual compilation success is the only
premise besides the independent source derivation. -/
theorem public_resumes (algorithm : Algorithm) (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program algorithm scenario) ["Digest"] 64 none [] = .ok object) :
    ∃ value, ContractCallCorrespondence.PublicMessageRel context result (finalState object algorithm scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallCorrespondence.compileObject_resumes_exact (code := code algorithm scenario) (by rfl) accepted
    (eligible algorithm scenario names_supported) context rfl (source object algorithm scenario)

/-- Published test vectors for "abc": FIPS 180-4 for SHA-256 and the
designers' list for RIPEMD-160. -/
def expected : Algorithm → Nat
  | .sha256 => 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
  | .ripemd160 => 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc

theorem digest_eq (algorithm : Algorithm) : digest algorithm = w (expected algorithm) := by
  cases algorithm <;> decide +kernel

private def digestBytes (algorithm : Algorithm) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (expected algorithm / 256 ^ (31 - index) % 256)

private def check (algorithm : Algorithm) (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program algorithm scenario) ["Digest"] 64 none [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"digest correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"digest correspondence: zero fuel completed: {reprStr outcome}")
  let expectedBytes := if scenario = .underfunded then List.replicate 32 0 ++ [0] else digestBytes algorithm ++ [1]
  for receipt in [Contract.runWithReceipt prepared 100000000, Contract.resumeWithReceipt checkpoint 100000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == expectedBytes && storage.isEmpty && receipt.logs.isEmpty && receipt.balances == [(w 0, w 10)] do
          throw (IO.userError s!"digest correspondence: wrong result for {reprStr algorithm} {reprStr scenario}: {reprStr receipt}")
    | outcome =>
        throw (IO.userError s!"digest correspondence: expected return for {reprStr algorithm} {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for algorithm in [Algorithm.sha256, .ripemd160] do
    for scenario in [Scenario.funded, .underfunded] do
      check algorithm scenario

end Digest

def run : IO Unit := do
  for scenario in [Scenario.identity, .underfunded, .transfer, .staticCall] do
    check scenario
  Modes.run
  Digest.run

end Tests.RustHullPrecompileCorrespondence
