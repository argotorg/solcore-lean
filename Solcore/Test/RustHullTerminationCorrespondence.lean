import Solcore.Frontend.RustHull.ContractFullExecutionCorrespondence
import Solcore.Test.RustHullLogDerivations

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
