import Solcore.Frontend.RustHull.ContractLogExecutionCorrespondence
import Solcore.Test.RustHullLogDerivations

/-! An unaligned event captures its bytes before later memory writes. The same
independent source derivation reaches public completion, failure and resumption. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullLogCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (name : String) (type : Ty) (arguments : List Expr) : Expr :=
  ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def memoryWrite : Expr := call "mstore8" .unit [word "1", word "171"]
def firstLog : Expr := call "log1" .unit [word "1", word "33", word "7"]
def memoryOverwrite : Expr := call "mstore8" .unit [word "1", word "205"]
def secondLog : Expr := call "log0" .unit [word "1", word "1"]
def gas : Expr := call "gas" .word []
def code : CodeBlock := {
  stmts := [expression memoryWrite, expression firstLog, expression memoryOverwrite, expression secondLog, expression gas]
  functions := []
}
def program : Program := {entryPoints := [], functions := [], objects := [.object "Logs" code []]}
def context (missingGas isStatic : Bool) : Contract.Context := {
  address := Core.Word.ofNatModulo (2 ^ 160 + 11)
  isStatic := isStatic
  availableGas := if missingGas then none else some (Core.Word.ofNatModulo 10000)
}
def initial (object : Contract.CompiledObject) (missingGas isStatic : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  ⟨[], ContractLogCorrespondence.contextInitialState object (Contract.normalizeContext (context missingGas isStatic))⟩
def memoryWritten (object : Contract.CompiledObject) (missingGas isStatic : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  ⟨[], {(initial object missingGas isStatic).external with runtime :=
    {(initial object missingGas isStatic).external.runtime with runtime :=
      {(initial object missingGas isStatic).external.runtime.runtime with memory := RustHullLogDerivations.firstMemory}}}⟩
def firstLogged (object : Contract.CompiledObject) (missingGas : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  ⟨[], RuntimeLogEffectsSemantics.withLogs (memoryWritten object missingGas false).external
    (RustHullLogDerivations.afterFirst (Core.Word.ofNatModulo 11))⟩
def memoryOverwritten (object : Contract.CompiledObject) (missingGas : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  ⟨[], {(firstLogged object missingGas).external with runtime :=
    {(firstLogged object missingGas).external.runtime with runtime :=
      {(firstLogged object missingGas).external.runtime.runtime with memory := RustHullLogDerivations.overwrittenMemory}}}⟩
def secondLogged (object : Contract.CompiledObject) (missingGas : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  ⟨[], RuntimeLogEffectsSemantics.withLogs (memoryOverwritten object missingGas).external
    (RustHullLogDerivations.afterSecond (Core.Word.ofNatModulo 11))⟩
def rejected (object : Contract.CompiledObject) (missingGas : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  ⟨[], RuntimeLogEffectsSemantics.withLogs (memoryWritten object missingGas true).external
    {RuntimeLogEffectsSemantics.logsState (memoryWritten object missingGas true).external with
      exit := Core.Word.ofNatModulo 3, returnOffset := Core.Word.zero, returnSize := Core.Word.zero}⟩
def finalState (object : Contract.CompiledObject) (missingGas isStatic : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  if isStatic then rejected object missingGas else secondLogged object missingGas

def result (missingGas isStatic : Bool) : Semantics.Result Semantics.Value :=
  if isStatic then .fault (.language Core.Word.maximum)
  else if missingGas then .fault (.language (Core.Word.ofNatModulo 9)) else .value .unit

private theorem memory_source (object : Contract.CompiledObject) (missingGas isStatic : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects [] memoryWrite
      (initial object missingGas isStatic) (.value .unit) (memoryWritten object missingGas isStatic) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime rfl)

private theorem first_log_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects [] firstLog
      (memoryWritten object missingGas false) (.value .unit) (firstLogged object missingGas) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "33") rfl) (.cons (.word (text := "7") rfl) .nil))
  · have observed : RuntimeLogEffectsSemantics.logsState (memoryWritten object missingGas false).external =
        RustHullLogDerivations.beforeFirst (Core.Word.ofNatModulo 11) := by
      change ({memory := RustHullLogDerivations.firstMemory, address := Contract.normalizeAddress (Core.Word.ofNatModulo (2 ^ 160 + 11))} : LogsSemantics.State) = _
      have normalized : Contract.normalizeAddress (Core.Word.ofNatModulo (2 ^ 160 + 11)) = Core.Word.ofNatModulo 11 := by decide +kernel
      rw [normalized]
      rfl
    apply Semantics.EvalCall.external (by rfl) rfl
    apply RuntimeLogEffectsSemantics.Builtin.logs
    apply LogsSemantics.Builtin.log .log1 .unit (Core.Word.ofNatModulo 1) (Core.Word.ofNatModulo 33) [Core.Word.ofNatModulo 7] rfl
    rw [observed]
    exact RustHullLogDerivations.first_execute (Core.Word.ofNatModulo 11)

private theorem overwrite_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects [] memoryOverwrite
      (firstLogged object missingGas) (.value .unit) (memoryOverwritten object missingGas) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "205") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime rfl)

private theorem second_log_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects [] secondLog
      (memoryOverwritten object missingGas) (.value .unit) (secondLogged object missingGas) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) .nil)
  · exact .external (by rfl) rfl (.logs (.log .log0 .unit (Core.Word.ofNatModulo 1) (Core.Word.ofNatModulo 1) [] rfl (RustHullLogDerivations.second_execute (Core.Word.ofNatModulo 11))))

private theorem static_log_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects [] firstLog
      (memoryWritten object missingGas true) (.fault (.language Core.Word.maximum)) (rejected object missingGas) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "33") rfl) (.cons (.word (text := "7") rfl) .nil))
  · exact .external (by rfl) rfl (.logs (.log .log1 .unit (Core.Word.ofNatModulo 1) (Core.Word.ofNatModulo 33) [Core.Word.ofNatModulo 7] rfl (.static rfl)))

private theorem gas_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects [] gas
      (secondLogged object missingGas)
      (if missingGas then .fault (.language (Core.Word.ofNatModulo 9)) else .value (.word (Core.Word.ofNatModulo 10000)))
      (secondLogged object missingGas) := by
  apply Semantics.EvalExpr.call rfl .nil
  cases missingGas <;> exact .external (by rfl) rfl (.runtime rfl)

theorem source (object : Contract.CompiledObject) (missingGas isStatic : Bool) :
    Semantics.EvalFunction [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] (initial object missingGas isStatic)
      (result missingGas isStatic) (finalState object missingGas isStatic) := by
  cases isStatic with
  | true =>
      apply Semantics.EvalFunction.body (control := .fault (.language Core.Word.maximum)) rfl
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (memory_source object missingGas true))
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (static_log_source object missingGas))
        (by intro impossible; cases impossible)
  | false =>
    cases missingGas with
    | false =>
        apply Semantics.EvalFunction.body (control := .fallthrough) rfl
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (memory_source object false false))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (first_log_source object false))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (overwrite_source object false))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (second_log_source object false))
        exact .next (by intros; intro impossible; cases impossible) (.expression rfl (gas_source object false)) .nil
    | true =>
        apply Semantics.EvalFunction.body (control := .fault (.language (Core.Word.ofNatModulo 9))) rfl
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (memory_source object true false))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (first_log_source object true))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (overwrite_source object true))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (second_log_source object true))
        exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (gas_source object true))
          (by intro impossible; cases impossible)


private theorem gas_supported : ContractLogCorrespondence.supported "gas" := by
  refine Or.inl (Or.inr ⟨.gas, rfl, ?_⟩)
  intro input present
  simp only [EnvironmentBuiltinCorrespondence.inputs, List.mem_singleton] at present
  subst input
  simp [Effects.slots, EnvironmentBuiltinCorrespondence.optionalWord]

theorem eligible : ExecutableProgram ContractLogCorrespondence.supported [AccountRuntime.frameFunction code] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore8") (Or.inl (Or.inl (Or.inl ⟨.store8, rfl⟩))) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "log1") (Or.inr ⟨.log1, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "mstore8") (Or.inl (Or.inl (Or.inl ⟨.store8, rfl⟩))) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "log0") (Or.inr ⟨.log0, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · exact .external gas_supported (by rfl) (by intro _ member; cases member) _ _

theorem public_resumes (missingGas isStatic : Bool) {prepared : Contract.Prepared}
    (accepted : Contract.prepare program ["Logs"] (context missingGas isStatic) 64 = .ok prepared) :
    ∃ object, Contract.compileObject program ["Logs"] 64 none [] = .ok object ∧
      prepared = object.instantiate (context missingGas isStatic) ∧
      ∃ value, ContractLogCorrespondence.PublicMessageRel (context missingGas isStatic)
        (result missingGas isStatic) (finalState object missingGas isStatic).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractLogCorrespondence.prepare_resumes_exact
    (code := code) (by rfl) accepted eligible rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object missingGas isStatic)⟩

def expectedEvents : List Logs.Event := [
  ⟨Core.Word.ofNatModulo 11, [Core.Word.ofNatModulo 7], 171 :: List.replicate 32 0⟩,
  ⟨Core.Word.ofNatModulo 11, [], [205]⟩]

private def check (missingGas isStatic : Bool) : IO Unit := do
  let object ← match Contract.compileObject program ["Logs"] 64 with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"log correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate (context missingGas isStatic)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"log correspondence: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 11).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"log correspondence: short resume completed: {reprStr outcome}")
  let resumed := Contract.resumeWithReceipt checkpoint 500000
  for receipt in [Contract.runWithReceipt prepared 500000, resumed] do
    match isStatic, missingGas, receipt.outcome with
    | false, false, .returned [] [] =>
        unless receipt.logs == expectedEvents do
          throw (IO.userError s!"log correspondence: event payload snapshot changed: {reprStr receipt.logs}")
    | false, true, .languageFailure (.word reason) =>
        unless reason == Core.Word.ofNatModulo 9 && receipt.logs.isEmpty && receipt.world.isEmpty do
          throw (IO.userError "log correspondence: failed message exported logs or world")
    | true, _, .invalid =>
        unless receipt.logs.isEmpty && receipt.world.isEmpty do
          throw (IO.userError "log correspondence: static rejection exported logs or world")
    | _, _, outcome => throw (IO.userError s!"log correspondence: incorrect outcome: {reprStr outcome}")
  match Core.runStateful 500000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair _ (.pair _ (.pair memory (.pair _ (.pair logs (.pair cursor _)))))))) _ =>
      let expected := (finalState object missingGas isStatic).external
      unless memory == Core.WordMapping.encode expected.runtime.runtime.memory.words &&
          logs == Core.WordMapping.encode expected.words && cursor == .word expected.cursor &&
          exit == .word expected.runtime.runtime.storage.exit do
        throw (IO.userError "log correspondence: internal snapshot lost earlier memory or logs")
      match Logs.decodeValues logs cursor with
      | .ok events =>
          unless events == (if isStatic then [] else expectedEvents) do
            throw (IO.userError "log correspondence: internal event snapshot differs")
      | .error error => throw (IO.userError s!"log correspondence: malformed log snapshot: {error}")
  | outcome => throw (IO.userError s!"log correspondence: Core failed: {reprStr outcome}")

def run : IO Unit := do
  check false false
  check true false
  check false true

end Tests.RustHullLogCorrespondence
