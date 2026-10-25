import Solcore.Frontend.RustHull.ContractRuntimeEffectsExecutionCorrespondence

/-! Concrete independent traces interleave memory and persistent/transient
storage. Public execution checks success, failure after writes and static mode. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullRuntimeEffectsCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (name : String) (type : Ty) (arguments : List Expr) : Expr :=
  ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩

def memoryWrite : Expr := call "mstore" .unit [word "1", word "171"]
def storageWrite : Expr := call "sstore" .unit [word "7", word "42"]
def transientWrite : Expr := call "tstore" .unit [word "8", word "99"]
def memoryRead : Expr := call "mload" .word [word "1"]
def storageRead : Expr := call "sload" .word [word "7"]
def transientRead : Expr := call "tload" .word [word "8"]
def overflow : Expr := call "mload" .word [word "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"]
def code (fault : Bool) : CodeBlock := {
  stmts := [expression memoryWrite, expression storageWrite, expression transientWrite,
    expression memoryRead, expression storageRead, expression (if fault then overflow else transientRead)]
  functions := []
}
def program (fault : Bool) : Program := {
  entryPoints := [], functions := [], objects := [.object "State" (code fault) []]
}
def context (isStatic : Bool) : Contract.Context := {isStatic := isStatic}
def initial (object : Contract.CompiledObject) (isStatic : Bool) : Semantics.State RuntimeEffectsSemantics.State :=
  ⟨[], {storage := {
    world := (StorageCorrespondence.canonical (object.initialWorld (Contract.normalizeContext (context isStatic)))).map Prod.fst
    isStatic := isStatic}}⟩
def memoryWritten (object : Contract.CompiledObject) (isStatic : Bool) : Semantics.State RuntimeEffectsSemantics.State :=
  ⟨[], {(initial object isStatic).external with
    memory := (MemorySemantics.mstore {} (Core.Word.ofNatModulo 1) (Core.Word.ofNatModulo 171)).2}⟩
def storageWritten (object : Contract.CompiledObject) (isStatic : Bool) : Semantics.State RuntimeEffectsSemantics.State :=
  ⟨[], {(memoryWritten object isStatic).external with
    storage := (StorageSemantics.store (initial object isStatic).external.storage
      (Core.Word.ofNatModulo 7) (Core.Word.ofNatModulo 42) false).2}⟩
def transientWritten (object : Contract.CompiledObject) : Semantics.State RuntimeEffectsSemantics.State :=
  ⟨[], {(storageWritten object false).external with
    storage := (StorageSemantics.store (storageWritten object false).external.storage
      (Core.Word.ofNatModulo 8) (Core.Word.ofNatModulo 99) true).2}⟩
def finalState (object : Contract.CompiledObject) (isStatic : Bool) : Semantics.State RuntimeEffectsSemantics.State :=
  if isStatic then storageWritten object true else transientWritten object
def result (fault isStatic : Bool) : Semantics.Result Semantics.Value :=
  if isStatic then .fault (.language Core.Word.maximum)
  else if fault then .fault (.language (Core.Word.ofNatModulo 6)) else .value .unit

private theorem memory_write_source (object : Contract.CompiledObject) (fault isStatic : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code fault)] RuntimeEffectsSemantics.effects [] memoryWrite
      (initial object isStatic) (.value .unit) (memoryWritten object isStatic) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl rfl

private theorem storage_write_source (object : Contract.CompiledObject) (fault isStatic : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code fault)] RuntimeEffectsSemantics.effects [] storageWrite
      (memoryWritten object isStatic)
      (if isStatic then .fault (.language Core.Word.maximum) else .value .unit) (storageWritten object isStatic) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "42") rfl) .nil)
  · cases isStatic <;> exact .external (by rfl) rfl rfl

private theorem transient_write_source (object : Contract.CompiledObject) (fault : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code fault)] RuntimeEffectsSemantics.effects [] transientWrite
      (storageWritten object false) (.value .unit) (transientWritten object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "8") rfl) (.cons (.word (text := "99") rfl) .nil)
  · exact .external (by rfl) rfl rfl

private theorem memory_read_source (object : Contract.CompiledObject) (fault : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code fault)] RuntimeEffectsSemantics.effects [] memoryRead
      (transientWritten object) (.value (.word (Core.Word.ofNatModulo 171))) (transientWritten object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) .nil
  · apply Semantics.EvalCall.external rfl rfl
    change RuntimeEffectsSemantics.builtin "mload" .word [.word (Core.Word.ofNatModulo 1)]
      (transientWritten object).external = some (.value (.word (Core.Word.ofNatModulo 171)), (transientWritten object).external)
    simp only [RuntimeEffectsSemantics.builtin, MemorySemantics.builtin, transientWritten, storageWritten, memoryWritten]
    rfl

private theorem storage_read_source (object : Contract.CompiledObject) (fault : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code fault)] RuntimeEffectsSemantics.effects [] storageRead
      (transientWritten object) (.value (.word (Core.Word.ofNatModulo 42))) (transientWritten object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "7") rfl) .nil
  · exact .external (by rfl) rfl rfl

private theorem transient_read_source (object : Contract.CompiledObject) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code false)] RuntimeEffectsSemantics.effects [] transientRead
      (transientWritten object) (.value (.word (Core.Word.ofNatModulo 99))) (transientWritten object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "8") rfl) .nil
  · exact .external (by rfl) rfl rfl

private theorem overflow_source (object : Contract.CompiledObject) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code true)] RuntimeEffectsSemantics.effects [] overflow
      (transientWritten object) (.fault (.language (Core.Word.ofNatModulo 6))) (transientWritten object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff") rfl) .nil
  · exact .external (by rfl) rfl rfl

theorem source (object : Contract.CompiledObject) (fault isStatic : Bool) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code fault)] RuntimeEffectsSemantics.effects
      (AccountRuntime.frameFunction (code fault)) [] (initial object isStatic)
      (result fault isStatic) (finalState object isStatic) := by
  cases isStatic with
  | true =>
      apply Semantics.EvalFunction.body (control := .fault (.language Core.Word.maximum)) rfl
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (memory_write_source object fault true))
      exact .stop (by intros; intro impossible; cases impossible)
        (.expressionFault rfl (storage_write_source object fault true)) (by intro impossible; cases impossible)
  | false =>
      cases fault with
      | false =>
          apply Semantics.EvalFunction.body (control := .fallthrough) rfl
          apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
            (.expression rfl (memory_write_source object false false))
          apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
            (.expression rfl (storage_write_source object false false))
          apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
            (.expression rfl (transient_write_source object false))
          apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
            (.expression rfl (memory_read_source object false))
          apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
            (.expression rfl (storage_read_source object false))
          exact .next (by intros; intro impossible; cases impossible) (.expression rfl (transient_read_source object)) .nil
      | true =>
          apply Semantics.EvalFunction.body (control := .fault (.language (Core.Word.ofNatModulo 6))) rfl
          apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
            (.expression rfl (memory_write_source object true false))
          apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
            (.expression rfl (storage_write_source object true false))
          apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
            (.expression rfl (transient_write_source object true))
          apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
            (.expression rfl (memory_read_source object true))
          apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
            (.expression rfl (storage_read_source object true))
          exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (overflow_source object))
            (by intro impossible; cases impossible)

theorem eligible (fault : Bool) :
    ExecutableProgram RuntimeEffectsCorrespondence.supported [AccountRuntime.frameFunction (code fault)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore") (Or.inl ⟨.store, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "sstore") (Or.inr ⟨.store false, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "tstore") (Or.inr ⟨.store true, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "mload") (Or.inl ⟨.load, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst argument
    exact .word _ _ _
  · apply ExecutableExpression.external (name := "sload") (Or.inr ⟨.load false, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst argument
    exact .word _ _ _
  · cases fault
    · apply ExecutableExpression.external (name := "tload") (Or.inr ⟨.load true, rfl⟩) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst argument
      exact .word _ _ _
    · apply ExecutableExpression.external (name := "mload") (Or.inl ⟨.load, rfl⟩) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst argument
      exact .word _ _ _

/-- The concrete source traces determine public receipts across every actual
resumption chain. No source-execution premise remains in this consumer. -/
theorem public_resumes (fault isStatic : Bool) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program fault) ["State"] (context isStatic) 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program fault) ["State"] 64 none [] = .ok object ∧
      prepared = object.instantiate (context isStatic) ∧
      ∃ value, ContractRuntimeEffectsCorrespondence.PublicMessageRel (context isStatic)
        (result fault isStatic) (finalState object isStatic).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractRuntimeEffectsCorrespondence.prepare_resumes_exact
    (code := code fault) (by rfl) accepted (eligible fault) rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object fault isStatic)⟩

private def check (fault isStatic : Bool) : IO Unit := do
  let object ← match Contract.compileObject (program fault) ["State"] 64 with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"state correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate (context isStatic)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"state correspondence: zero fuel completed: {reprStr result}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 11).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"state correspondence: short resume completed: {reprStr result}")
  let receipt := Contract.resumeWithReceipt checkpoint 500000
  match fault, isStatic, receipt.outcome with
  | false, false, .returned [] storage =>
      unless storage == [(Core.Word.ofNatModulo 7, Core.Word.ofNatModulo 42)] do
        throw (IO.userError "state correspondence: persistent write not committed")
      unless receipt.world.all (·.transient.isEmpty) do
        throw (IO.userError "state correspondence: transaction finalization retained transient storage")
  | true, false, .languageFailure (.word reason) =>
      unless reason == Core.Word.ofNatModulo 6 do
        throw (IO.userError "state correspondence: incorrect fault reason")
  | _, true, .invalid => pure ()
  | _, _, outcome => throw (IO.userError s!"state correspondence: incorrect outcome: {reprStr outcome}")
  unless !fault && !isStatic || receipt.world.isEmpty do
    throw (IO.userError "state correspondence: failed execution exported world changes")
  match Core.runStateful 500000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair _ (.pair _ (.pair _ (.pair memory (.pair storage _)))))) _ =>
      unless memory == Core.WordMapping.encode (finalState object isStatic).external.memory.words do
        throw (IO.userError "state correspondence: memory write lost before snapshot")
      let expected := if isStatic then [] else [(Core.Word.ofNatModulo 7, Core.Word.ofNatModulo 42)]
      unless storage == Core.WordMapping.encode expected do
        throw (IO.userError "state correspondence: incorrect storage snapshot")
  | outcome => throw (IO.userError s!"state correspondence: Core failed: {reprStr outcome}")

def run : IO Unit := do
  check false false
  check true false
  check false true

end Tests.RustHullRuntimeEffectsCorrespondence
