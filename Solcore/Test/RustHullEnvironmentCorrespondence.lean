import Solcore.Frontend.RustHull.ContractEnvironmentExecutionCorrespondence

/-! Independent environment observations feed memory and storage writes before
successful completion or a missing-gas fault in actual public execution. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullEnvironmentCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (name : String) (type : Ty) (arguments : List Expr) : Expr :=
  ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def calldata : Expr := call "calldataload" .word [word "0"]
def timestamp : Expr := call "timestamp" .word []
def blockHash : Expr := call "blockhash" .word [word "999"]
def blobHash : Expr := call "blobhash" .word [word "1"]
def gas : Expr := call "gas" .word []
def memoryWrite : Expr := call "mstore" .unit [word "1", calldata]
def storageWrite : Expr := call "sstore" .unit [word "7", timestamp]
def transientWrite : Expr := call "tstore" .unit [word "8", blockHash]
def code : CodeBlock := {
  stmts := [expression memoryWrite, expression storageWrite, expression transientWrite,
    expression blobHash, expression gas]
  functions := []
}
def program : Program := {entryPoints := [], functions := [], objects := [.object "Environment" code []]}
def context (missingGas : Bool) : Contract.Context := {
  address := Core.Word.ofNatModulo (2 ^ 160 + 11)
  caller := Core.Word.ofNatModulo (2 ^ 160 + 12)
  value := Core.Word.ofNatModulo 13
  calldata := List.replicate 31 0 ++ [171]
  availableGas := if missingGas then none else some (Core.Word.ofNatModulo 10000)
  ambient := {
    timestamp := some (Core.Word.ofNatModulo 42)
    number := some (Core.Word.ofNatModulo 1000)
    blockHashes := some [(Core.Word.ofNatModulo 999, Core.Word.ofNatModulo 77)]
    blobHashes := some [Core.Word.ofNatModulo 90, Core.Word.ofNatModulo 91]
  }
}
def initial (object : Contract.CompiledObject) (missingGas : Bool) : Semantics.State RuntimeEnvironmentEffectsSemantics.State :=
  ⟨[], ContractEnvironmentCorrespondence.contextInitialState object (Contract.normalizeContext (context missingGas))⟩
def memoryWritten (object : Contract.CompiledObject) (missingGas : Bool) : Semantics.State RuntimeEnvironmentEffectsSemantics.State :=
  ⟨[], {(initial object missingGas).external with runtime :=
    {(initial object missingGas).external.runtime with
      memory := (MemorySemantics.mstore {} (Core.Word.ofNatModulo 1) (Core.Word.ofNatModulo 171)).2}}⟩
def storageWritten (object : Contract.CompiledObject) (missingGas : Bool) : Semantics.State RuntimeEnvironmentEffectsSemantics.State :=
  ⟨[], {(memoryWritten object missingGas).external with runtime :=
    {(memoryWritten object missingGas).external.runtime with storage :=
      (StorageSemantics.store (initial object missingGas).external.runtime.storage
        (Core.Word.ofNatModulo 7) (Core.Word.ofNatModulo 42) false).2}}⟩
def finalState (object : Contract.CompiledObject) (missingGas : Bool) : Semantics.State RuntimeEnvironmentEffectsSemantics.State :=
  ⟨[], {(storageWritten object missingGas).external with runtime :=
    {(storageWritten object missingGas).external.runtime with storage :=
      (StorageSemantics.store (storageWritten object missingGas).external.runtime.storage
        (Core.Word.ofNatModulo 8) (Core.Word.ofNatModulo 77) true).2}}⟩
def result (missingGas : Bool) : Semantics.Result Semantics.Value :=
  if missingGas then .fault (.language (Core.Word.ofNatModulo 9)) else .value .unit

private theorem memory_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeEnvironmentEffectsSemantics.effects [] memoryWrite
      (initial object missingGas) (.value .unit) (memoryWritten object missingGas) := by
  apply Semantics.EvalExpr.call (values := [.word (Core.Word.ofNatModulo 1), .word (Core.Word.ofNatModulo 171)])
    (middle := initial object missingGas) rfl
  · refine .cons (.word (text := "1") rfl) (.cons (value := .word (Core.Word.ofNatModulo 171)) ?_ .nil)
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "0") rfl) .nil
    · exact .external (by rfl) rfl rfl
  · exact .external (by rfl) rfl rfl

set_option linter.unusedSimpArgs false in
private theorem storage_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeEnvironmentEffectsSemantics.effects [] storageWrite
      (memoryWritten object missingGas) (.value .unit) (storageWritten object missingGas) := by
  apply Semantics.EvalExpr.call (values := [.word (Core.Word.ofNatModulo 7), .word (Core.Word.ofNatModulo 42)])
    (middle := memoryWritten object missingGas) rfl
  · refine .cons (.word (text := "7") rfl) (.cons (value := .word (Core.Word.ofNatModulo 42)) ?_ .nil)
    exact .call rfl .nil (.external (by rfl) rfl rfl)
  · apply Semantics.EvalCall.external rfl rfl
    simp [RuntimeEnvironmentEffectsSemantics.effects, RuntimeEnvironmentEffectsSemantics.builtin,
      RuntimeEffectsSemantics.builtin, MemorySemantics.builtin, StorageSemantics.builtin,
      finalState, storageWritten, memoryWritten, initial, ContractEnvironmentCorrespondence.contextInitialState,
      ContractRuntimeEffectsCorrespondence.contextInitialState, ContractRuntimeEffectsCorrespondence.initialState,
      StorageSemantics.store, StorageSemantics.writeStorage, StorageSemantics.get, StorageSemantics.lookup,
      Contract.CompiledObject.initialWorld, Contract.normalizeContext, Contract.normalizeAddress, Core.Word.ofNatModulo, Core.wordModulus,
      StorageCorrespondence.canonical, context, StorageSemantics.put, StorageSemantics.update, StorageSemantics.writeWord]
    rfl

set_option linter.unusedSimpArgs false in
private theorem transient_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeEnvironmentEffectsSemantics.effects [] transientWrite
      (storageWritten object missingGas) (.value .unit) (finalState object missingGas) := by
  apply Semantics.EvalExpr.call (values := [.word (Core.Word.ofNatModulo 8), .word (Core.Word.ofNatModulo 77)])
    (middle := storageWritten object missingGas) rfl
  · refine .cons (.word (text := "8") rfl) (.cons (value := .word (Core.Word.ofNatModulo 77)) ?_ .nil)
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "999") rfl) .nil
    · exact .external (by rfl) rfl rfl
  · apply Semantics.EvalCall.external rfl rfl
    simp [RuntimeEnvironmentEffectsSemantics.effects, RuntimeEnvironmentEffectsSemantics.builtin,
      RuntimeEffectsSemantics.builtin, MemorySemantics.builtin, StorageSemantics.builtin,
      finalState, storageWritten, memoryWritten, initial, ContractEnvironmentCorrespondence.contextInitialState,
      ContractRuntimeEffectsCorrespondence.contextInitialState, ContractRuntimeEffectsCorrespondence.initialState,
      StorageSemantics.store, StorageSemantics.writeStorage, StorageSemantics.get, StorageSemantics.lookup,
      Contract.CompiledObject.initialWorld, Contract.normalizeContext, Contract.normalizeAddress, Core.Word.ofNatModulo, Core.wordModulus,
      StorageCorrespondence.canonical, context, StorageSemantics.put, StorageSemantics.update, StorageSemantics.writeWord]
    rfl

private theorem blob_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeEnvironmentEffectsSemantics.effects [] blobHash
      (finalState object missingGas) (.value (.word (Core.Word.ofNatModulo 91))) (finalState object missingGas) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) .nil
  · exact .external (by rfl) rfl rfl

private theorem gas_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeEnvironmentEffectsSemantics.effects [] gas
      (finalState object missingGas)
      (if missingGas then .fault (.language (Core.Word.ofNatModulo 9)) else .value (.word (Core.Word.ofNatModulo 10000)))
      (finalState object missingGas) := by
  apply Semantics.EvalExpr.call rfl .nil
  cases missingGas <;> exact .external (by rfl) rfl rfl

theorem source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalFunction [AccountRuntime.frameFunction code] RuntimeEnvironmentEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] (initial object missingGas)
      (result missingGas) (finalState object missingGas) := by
  cases missingGas with
  | false =>
      apply Semantics.EvalFunction.body (control := .fallthrough) rfl
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (memory_source object false))
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (storage_source object false))
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (transient_source object false))
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (blob_source object false))
      exact .next (by intros; intro impossible; cases impossible) (.expression rfl (gas_source object false)) .nil
  | true =>
      apply Semantics.EvalFunction.body (control := .fault (.language (Core.Word.ofNatModulo 9))) rfl
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (memory_source object true))
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (storage_source object true))
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (transient_source object true))
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (blob_source object true))
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (gas_source object true))
        (by intro impossible; cases impossible)

set_option linter.unusedSimpArgs false in
private theorem environment_supported (operation : EnvironmentSemantics.Operation)
    (member : operation ∈ [.calldataLoad, .ambient .timestamp, .blockHash, .blobHash, .gas]) :
    ContractEnvironmentCorrespondence.supported operation.name := by
  refine Or.inr ⟨operation, rfl, ?_⟩
  intro input present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [EnvironmentBuiltinCorrespondence.inputs, List.mem_cons, List.not_mem_nil, or_false] at present
    first
    | (subst input; simp [Effects.slots, Ambient.slots, EnvironmentSemantics.AmbientWord.name, EnvironmentBuiltinCorrespondence.optionalWord, EnvironmentBuiltinCorrespondence.optionalHashes, Ambient.optionalWord, Ambient.optionalHashes])
    | (rcases present with rfl | rfl <;> simp [Effects.slots, Ambient.slots, EnvironmentSemantics.AmbientWord.name, EnvironmentBuiltinCorrespondence.optionalWord, EnvironmentBuiltinCorrespondence.optionalHashes, Ambient.optionalWord, Ambient.optionalHashes])

private theorem calldata_eligible : ExecutableExpression ContractEnvironmentCorrespondence.supported
    [AccountRuntime.frameFunction code] calldata := by
  apply ExecutableExpression.external (environment_supported .calldataLoad (by simp)) (by rfl)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst argument
  exact .word _ _ _

private theorem timestamp_eligible : ExecutableExpression ContractEnvironmentCorrespondence.supported
    [AccountRuntime.frameFunction code] timestamp :=
  .external (environment_supported (.ambient .timestamp) (by simp)) (by rfl) (by intro _ member; cases member) _ _

private theorem block_eligible : ExecutableExpression ContractEnvironmentCorrespondence.supported
    [AccountRuntime.frameFunction code] blockHash := by
  apply ExecutableExpression.external (environment_supported .blockHash (by simp)) (by rfl)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst argument
  exact .word _ _ _

theorem eligible : ExecutableProgram ContractEnvironmentCorrespondence.supported [AccountRuntime.frameFunction code] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore") (Or.inl (Or.inl ⟨.store, rfl⟩)) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · exact calldata_eligible
  · apply ExecutableExpression.external (name := "sstore") (Or.inl (Or.inr ⟨.store false, rfl⟩)) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · exact timestamp_eligible
  · apply ExecutableExpression.external (name := "tstore") (Or.inl (Or.inr ⟨.store true, rfl⟩)) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · exact block_eligible
  · apply ExecutableExpression.external (environment_supported .blobHash (by simp)) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst argument
    exact .word _ _ _
  · exact .external (environment_supported .gas (by simp)) (by rfl) (by intro _ member; cases member) _ _

theorem public_resumes (missingGas : Bool) {prepared : Contract.Prepared}
    (accepted : Contract.prepare program ["Environment"] (context missingGas) 64 = .ok prepared) :
    ∃ object, Contract.compileObject program ["Environment"] 64 none [] = .ok object ∧
      prepared = object.instantiate (context missingGas) ∧
      ∃ value, ContractEnvironmentCorrespondence.PublicMessageRel (context missingGas)
        (result missingGas) (finalState object missingGas).external.runtime value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractEnvironmentCorrespondence.prepare_resumes_exact
    (code := code) (by rfl) accepted eligible rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object missingGas)⟩

private def check (missingGas : Bool) : IO Unit := do
  let object ← match Contract.compileObject program ["Environment"] 64 with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"environment correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate (context missingGas)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"environment correspondence: zero fuel completed: {reprStr result}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 11).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"environment correspondence: short resume completed: {reprStr result}")
  let receipt := Contract.resumeWithReceipt checkpoint 500000
  match missingGas, receipt.outcome with
  | false, .returned [] storage =>
      unless storage == [(Core.Word.ofNatModulo 7, Core.Word.ofNatModulo 42)] do
        throw (IO.userError "environment correspondence: timestamp was not stored")
      unless receipt.world.all (fun account => account.address == Core.Word.ofNatModulo 11 && account.transient.isEmpty) do
        throw (IO.userError "environment correspondence: address normalization or transient finalization failed")
  | true, .languageFailure (.word reason) =>
      unless reason == Core.Word.ofNatModulo 9 && receipt.world.isEmpty do
        throw (IO.userError "environment correspondence: missing gas fault/export differs")
  | _, outcome => throw (IO.userError s!"environment correspondence: incorrect outcome: {reprStr outcome}")
  match Core.runStateful 500000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair _ (.pair _ (.pair _ (.pair memory (.pair storage _)))))) _ =>
      unless memory == Core.WordMapping.encode (finalState object missingGas).external.runtime.memory.words &&
          storage == Core.WordMapping.encode [(Core.Word.ofNatModulo 7, Core.Word.ofNatModulo 42)] do
        throw (IO.userError "environment correspondence: environment-driven writes lost before snapshot")
  | outcome => throw (IO.userError s!"environment correspondence: Core failed: {reprStr outcome}")

def run : IO Unit := do
  check false
  check true

end Tests.RustHullEnvironmentCorrespondence
