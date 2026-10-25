import Solcore.Frontend.RustHull.ContractReturnDataExecutionCorrespondence
import Solcore.Frontend.RustHull.RuntimeReturnDataEffectsSemantics
import Solcore.Frontend.RustHull.ReturnDataBuiltinCorrespondence

/-! Return-data bounds are checked before destination expansion. Prior storage,
memory and event updates remain in the internal snapshot, while an invalid
message exports none of those changes. Linked code and account reads share the
same execution as return-data operations. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullReturnDataCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where | empty | sourceInvalid | lengthInvalid
  deriving DecidableEq, Repr
private abbrev w := Core.Word.ofNatModulo
private def maximum := "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def image (linked : Bool) : Option (List UInt8) := if linked then some [205] else none
def guard : Expr := call .word "memoryguard" [word "171"]
def seed : Expr := call .unit "mstore8" [word "1", guard]
def storageWrite : Expr := call .unit "sstore" [word "7", word "42"]
def event : Expr := call .unit "log0" [word "1", word "1"]
def balance : Expr := call .word "selfbalance" []
def size : Expr := call .word "returndatasize" []
def codeCopy (linked : Bool) : Expr :=
  if linked then call .unit "codecopy" [word "7", word "0", word "1"] else call .word "msize" []
def copy (scenario : Scenario) : Expr := match scenario with
  | .empty => call .unit "returndatacopy" [word maximum, word "0", word "0"]
  | .sourceInvalid => call .unit "returndatacopy" [word maximum, word "1", word "0"]
  | .lengthInvalid => call .unit "returndatacopy" [word maximum, word "0", word "1"]
def returned : Expr := call .unit "return" [word "1", word "1"]
def code (scenario : Scenario) (linked : Bool) : CodeBlock := {
  stmts := [expression seed, expression storageWrite, expression event, expression balance,
    expression (codeCopy linked), expression size, expression (copy scenario), expression returned]
  functions := []}
def program (scenario : Scenario) (linked : Bool) : Program :=
  {entryPoints := [], functions := [], objects := [.object "ReturnData" (code scenario linked) []]}
def context : Contract.Context := {balance := w 11}
def initial (object : Contract.CompiledObject) (linked : Bool) : Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  ⟨[], ⟨ContractCodeCorrespondence.contextInitialState (image linked) object (Contract.normalizeContext context), []⟩⟩
def seeded : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 1) (w 171)).2
def memoryWritten (object : Contract.CompiledObject) (linked : Bool) : Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  ⟨[], {(initial object linked).external with runtime := RuntimeAccountEffectsSemantics.withMemory (initial object linked).external.runtime seeded}⟩
def storageWritten (object : Contract.CompiledObject) (linked : Bool) : Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  let state := (memoryWritten object linked).external.runtime.runtime.runtime.runtime
  ⟨[], RuntimeReturnDataEffectsSemantics.withRuntime (memoryWritten object linked).external
    {state with storage := (StorageSemantics.store state.storage (w 7) (w 42) false).2}⟩
def loggedWords : LogsSemantics.Words :=
  [(w 0, w 0), (w 1, w 0), (w 2, w 1), (w 3, LogsSemantics.paddedWord seeded.words (w 1) (w 1))]
def logged (object : Contract.CompiledObject) (linked : Bool) : Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  let state := (storageWritten object linked).external
  let previous := RuntimeLogEffectsSemantics.logsState state.runtime.runtime
  let logs := {previous with words := loggedWords, cursor := w 4}
  ⟨[], {state with runtime := {state.runtime with runtime := RuntimeLogEffectsSemantics.withLogs state.runtime.runtime logs}}⟩
def copiedMemory (linked : Bool) : MemorySemantics.State :=
  if linked then ⟨MemorySemantics.writeByte seeded.words (w 7) (w 205), seeded.size⟩ else seeded
def codeCopied (object : Contract.CompiledObject) (linked : Bool) : Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  let state := (logged object linked).external
  ⟨[], {state with runtime := RuntimeAccountEffectsSemantics.withMemory state.runtime (copiedMemory linked)}⟩
def terminated (object : Contract.CompiledObject) (linked : Bool) (kind : Nat) (offset length : Core.Word) :
    Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  let state := (codeCopied object linked).external
  ⟨[], RuntimeReturnDataEffectsSemantics.withRuntime state
    (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime kind offset length).2⟩
def finalState (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) : Semantics.State RuntimeReturnDataEffectsSemantics.State :=
  if scenario = .empty then terminated object linked 1 (w 1) (w 1) else terminated object linked 3 (w 0) (w 0)
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem guard_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] guard
      (initial object linked) (.value (.word (w 171))) (initial object linked) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "171") rfl) .nil
  · exact .external (by rfl) rfl (.guard .guarded)

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] seed
      (initial object linked) (.value .unit) (memoryWritten object linked) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (guard_source object scenario linked) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))))

private theorem storage_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] storageWrite
      (memoryWritten object linked) (.value .unit) (storageWritten object linked) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "42") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))))

private theorem event_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] event
      (storageWritten object linked) (.value .unit) (logged object linked) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) .nil)
  · apply Semantics.EvalCall.external (by rfl) rfl
    apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
    apply RuntimeCodeEffectsSemantics.Builtin.runtime
    apply RuntimeAccountEffectsSemantics.Builtin.runtime
    apply RuntimeHashEffectsSemantics.Builtin.runtime
    apply RuntimeCopyEffectsSemantics.Builtin.runtime
    apply RuntimeFullEffectsSemantics.Builtin.runtime
    apply RuntimeLogEffectsSemantics.Builtin.logs
    apply LogsSemantics.Builtin.log .log0 .unit (w 1) (w 1) [] rfl
    apply LogsSemantics.Execute.writable rfl
    apply LogsSemantics.Append.done (size := w 32) (words := loggedWords)
    · decide +kernel
    · change ¬w 0 > LogsSemantics.nextCursor (w 0) (w 1) []
      decide +kernel
    · change MemorySemantics.touchSize? seeded.size (w 1) (w 1) = some (w 32)
      decide +kernel
    · apply LogsSemantics.Copy.step (by decide +kernel)
      exact .empty _ _ _

private theorem balance_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] balance
      (logged object linked) (.value (.word (w 11))) (logged object linked) := by
  apply Semantics.EvalExpr.call rfl .nil
  exact .external (by rfl) rfl (.runtime (.runtime (.observation (.selfbalance .word _))))

private theorem code_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] (codeCopy linked)
      (logged object linked) (if linked then .value .unit else .value (.word (w 32))) (codeCopied object linked) := by
  cases linked
  case false =>
    apply Semantics.EvalExpr.call rfl .nil
    exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))))
  case true =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil))
    · apply Semantics.EvalCall.external (by rfl) rfl
      apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
      apply RuntimeCodeEffectsSemantics.Builtin.copy
      apply CodeImageSemantics.Builtin.copy .codeCopy
      apply CodeImageSemantics.Execute.copied rfl
      apply MemoryCopySemantics.From.done (by change MemorySemantics.touchSize? (w 32) (w 7) (w 1) = some (w 32); decide +kernel)
      apply MemoryCopySemantics.Copy.step (by decide +kernel)
      exact .empty _ _ _ _

private theorem size_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] size
      (codeCopied object linked) (.value (.word (w 0))) (codeCopied object linked) := by
  apply Semantics.EvalExpr.call rfl .nil
  exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))))

private theorem copy_source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] (copy scenario)
      (codeCopied object linked) (if scenario = .empty then .value .unit else result)
      (if scenario = .empty then codeCopied object linked else finalState object scenario linked) := by
  cases scenario
  case empty =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) .nil))
    · apply Semantics.EvalCall.external (by rfl) rfl
      apply RuntimeReturnDataEffectsSemantics.Builtin.copy
      exact .copy (.copied (by change ¬w 0 > w 0; decide +kernel) (by change ¬w 0 > (w 0).sub (w 0); decide +kernel)
        (.done (by cases linked <;> rfl) (.empty _ _ _ _)))
  case sourceInvalid =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "0") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.copy (.sourceOverflow _ (by change w 1 > w 0; decide +kernel))))
  case lengthInvalid =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.copy (.lengthOverflow _ (by change ¬w 0 > w 0; decide +kernel) (by change w 1 > (w 0).sub (w 0); decide +kernel))))

private theorem return_source (object : Contract.CompiledObject) (linked : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code .empty linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked)) [] returned
      (codeCopied object linked) result (finalState object .empty linked) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) (linked : Bool) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario linked)] (RuntimeReturnDataEffectsSemantics.effects (image linked))
      (AccountRuntime.frameFunction (code scenario linked)) [] (initial object linked) result (finalState object scenario linked) := by
  apply Semantics.EvalFunction.body (control := .fault (.language Core.Word.maximum)) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object scenario linked))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (storage_source object scenario linked))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (event_source object scenario linked))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (balance_source object scenario linked))
  have copied := code_source object scenario linked
  cases isLinked : linked <;> simp only [isLinked, Bool.false_eq_true, ↓reduceIte] at copied
  all_goals
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl copied)
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (size_source object scenario _))
    cases scenario
  all_goals first
    | apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (copy_source object .empty _))
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object _))
        (by intro impossible; cases impossible)
    | exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (copy_source object _ _))
        (by intro impossible; cases impossible)

def usedNames (linked : Bool) : List String :=
  ["mstore8", "memoryguard", "sstore", "log0", "selfbalance",
    if linked then "codecopy" else "msize", "returndatasize", "returndatacopy", "return"]

theorem eligible (scenario : Scenario) (linked : Bool) {supported : String → Prop}
    (available : ∀ name ∈ usedNames linked, supported name) :
    ExecutableProgram supported [AccountRuntime.frameFunction (code scenario linked)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · apply ExecutableExpression.external (name := "memoryguard") (available _ (by simp [usedNames])) (by rfl)
      intro argument member
      simp only [List.mem_singleton] at member
      subst argument
      exact .word _ _ _
  · apply ExecutableExpression.external (name := "sstore") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "log0") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · exact .external (name := "selfbalance") (available _ (by simp [usedNames])) (by rfl) (by intro _ member; cases member) _ _
  · cases linked
    case false =>
      exact .external (name := "msize") (available _ (by simp [usedNames])) (by rfl) (by intro _ member; cases member) _ _
    case true =>
      apply ExecutableExpression.external (name := "codecopy") (available _ (by simp [usedNames])) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact .word _ _ _
  · exact .external (name := "returndatasize") (available _ (by simp [usedNames])) (by rfl) (by intro _ member; cases member) _ _
  · cases scenario
    all_goals
      apply ExecutableExpression.external (name := "returndatacopy") (available _ (by simp [usedNames])) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "return") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _

private theorem account_supported (name : String)
    (member : name ∈ ["mstore8", "sstore", "log0", "selfbalance", "msize", "returndatasize", "return"]) :
    ContractAccountCorrespondence.supported name := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨.store8, rfl⟩))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨.store false, rfl⟩))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨.log0, rfl⟩))))
  · exact Or.inr ⟨.selfbalance, rfl⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨.size, rfl⟩))))))
  · apply Or.inl; apply Or.inl; apply Or.inl; apply Or.inl; apply Or.inl
    refine Or.inr ⟨.direct .returnDataSize, rfl, ?_⟩
    intro input member
    simp only [EnvironmentBuiltinCorrespondence.inputs, List.mem_singleton] at member
    subst input
    simp [Effects.slots, EnvironmentSemantics.Direct.slot]
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨.returned, rfl⟩)))

private theorem lift_account (linked : Bool) {name : String} (available : ContractAccountCorrespondence.supported name) :
    ContractReturnDataCorrespondence.supported linked name := by
  cases linked
  · exact .inl available
  · exact .inl (.inl available)

private theorem names_supported (linked : Bool) :
    ∀ name ∈ usedNames linked, ContractReturnDataCorrespondence.supported linked name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lift_account linked (account_supported _ (by simp))
  · exact .inr (.inr rfl)
  · exact lift_account linked (account_supported _ (by simp))
  · exact lift_account linked (account_supported _ (by simp))
  · exact lift_account linked (account_supported _ (by simp))
  · cases linked
    · exact lift_account false (account_supported _ (by simp))
    · exact .inl (.inr (.inr ⟨.codeCopy, rfl⟩))
  · exact lift_account linked (account_supported _ (by simp))
  · exact .inr (.inl rfl)
  · exact lift_account linked (account_supported _ (by simp))

theorem public_resumes (scenario : Scenario) (linked : Bool) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario linked) ["ReturnData"] 64 (image linked) [] = .ok object) :
    ∃ value, ContractReturnDataCorrespondence.PublicMessageRel context result (finalState object scenario linked).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  have enabled : ((image linked).isSome || !([] : List AccountRuntime.CodeDefinition).isEmpty) = linked := by
    cases linked <;> rfl
  apply ContractReturnDataCorrespondence.compileObject_resumes_exact (code := code scenario linked)
    (by rfl) accepted
  · rw [enabled]
    exact eligible scenario linked (names_supported linked)
  · rfl
  · exact source object scenario linked

theorem public_prepared (scenario : Scenario) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program scenario false) ["ReturnData"] context 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program scenario false) ["ReturnData"] 64 none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∃ value, ContractReturnDataCorrespondence.PublicMessageRel context result (finalState object scenario false).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractReturnDataCorrespondence.prepare_resumes_exact
    (code := code scenario false) (by rfl) accepted (eligible scenario false (names_supported false)) rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object scenario false)⟩

def nonemptyEntries : MemorySemantics.Entries := Memory.packBytes [171, 205]
def nonemptyMemory (overflow : Bool) : MemorySemantics.State :=
  if overflow then seeded else
    ⟨MemorySemantics.writeByte (MemorySemantics.writeByte seeded.words (w 31) (w 171)) (w 32) (w 205), w 64⟩

theorem nonempty_source (overflow : Bool) (storage : StorageSemantics.State) :
    ReturnDataSemantics.Execute nonemptyEntries (w 2) (if overflow then Core.Word.maximum else w 31) (w 0)
      (if overflow then w 1 else w 2) ⟨seeded, storage⟩
      (if overflow then MemorySemantics.overflow else .value .unit) ⟨nonemptyMemory overflow, storage⟩ := by
  cases overflow
  case false =>
    apply ReturnDataSemantics.Execute.copied (by decide +kernel) (by decide +kernel)
    apply MemoryCopySemantics.From.done (by change MemorySemantics.touchSize? seeded.size (w 31) (w 2) = some (w 64); decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    exact .empty _ _ _ _
  case true =>
    exact .copied (by decide +kernel) (by decide +kernel) (.overflow (by change MemorySemantics.touchSize? seeded.size Core.Word.maximum (w 1) = none; decide +kernel))

private def expectedEvents : List Logs.Event := [⟨w 0, [], [171]⟩]
private def check (scenario : Scenario) (linked : Bool) : IO Unit := do
  let object ← match Contract.compileObject (program scenario linked) ["ReturnData"] 64 (image linked) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"return-data correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"return-data correspondence: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"return-data correspondence: short resume completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    if scenario = .empty then
      match receipt.outcome with
      | .returned bytes storage =>
          unless bytes == [171] && storage == [(w 7, w 42)] && receipt.logs == expectedEvents do
            throw (IO.userError "return-data correspondence: successful message lost earlier writes or logs")
      | outcome => throw (IO.userError s!"return-data correspondence: expected return, got {reprStr outcome}")
    else
      match receipt.outcome with
      | .invalid =>
          unless receipt.world.isEmpty && receipt.logs.isEmpty do
            throw (IO.userError "return-data correspondence: invalid message exported changes")
      | outcome => throw (IO.userError s!"return-data correspondence: expected invalid before destination fault, got {reprStr outcome}")
  match Core.runStateful 1000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair length (.pair memory (.pair storage (.pair logs (.pair cursor _)))))))) _ =>
      let expected := (finalState object scenario linked).external.runtime
      let runtime := expected.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words && storage == Core.WordMapping.encode [(w 7, w 42)] &&
          logs == Core.WordMapping.encode expected.runtime.words && cursor == .word expected.runtime.cursor &&
          exit == .word runtime.storage.exit && offset == .word runtime.storage.returnOffset && length == .word runtime.storage.returnSize do
        throw (IO.userError "return-data correspondence: internal snapshot lost earlier state changes")
      match Logs.decodeValues logs cursor with
      | .ok events =>
          unless events == expectedEvents do
            throw (IO.userError "return-data correspondence: invalid message lost its internal event snapshot")
      | .error error => throw (IO.userError s!"return-data correspondence: malformed internal logs: {error}")
  | outcome => throw (IO.userError s!"return-data correspondence: Core failed: {reprStr outcome}")

private def checkNonempty (overflow : Bool) : IO Unit := do
  let slots : List (String × Core.Ty) := [("memory", Core.WordMapping.type), ("memorySize", .word),
    ("returnData", Core.WordMapping.type), ("returnDataSize", .word),
    ("exit", .word), ("returnOffset", .word), ("returnSize", .word)]
  let arguments : List Lowered := [⟨.word, Core.LanguageResult.success (.word (if overflow then Core.Word.maximum else w 31))⟩,
    ⟨.word, Core.LanguageResult.success (.word (w 0))⟩, ⟨.word, Core.LanguageResult.success (.word (if overflow then w 1 else w 2))⟩]
  let lowered ← match lowerBuiltin (AccountRuntime.frameScope slots) "returndatacopy" .unit arguments with
    | .ok lowered => pure lowered
    | .error error => throw (IO.userError s!"return-data correspondence: direct lowering failed: {reprStr error}")
  let cells : List (Core.Ty × Core.Expr) := [
    ⟨Core.WordMapping.type, Core.WordMapping.literal seeded.words⟩, ⟨.word, .word seeded.size⟩,
    ⟨Core.WordMapping.type, Core.WordMapping.literal nonemptyEntries⟩, ⟨.word, .word (w 2)⟩,
    ⟨.word, .word (w 0)⟩, ⟨.word, .word (w 9)⟩, ⟨.word, .word (w 9)⟩]
  let expression := cells.foldr (fun (type, value) body => .letE (.newCell type value) body) lowered.expression
  match Core.runStateful 1000000 (Core.State.initial expression) with
  | .done value store =>
      let expected := if overflow then Core.Value.inLeft .unit (.word (w 6)) else .inRight .word .unit
      unless value == expected && store[0]? == some (Core.WordMapping.encode (nonemptyMemory overflow).words) &&
          store[1]? == some (.word (nonemptyMemory overflow).size) &&
          store[2]? == some (Core.WordMapping.encode nonemptyEntries) && store[3]? == some (.word (w 2)) &&
          store[4]? == some (.word (w 0)) && store[5]? == some (.word (w 9)) && store[6]? == some (.word (w 9)) do
        throw (IO.userError "return-data correspondence: nonempty copy changed the source or termination registers")
  | .fault fault _ => throw (IO.userError s!"return-data correspondence: direct copy fault: {reprStr fault}")
  | .outOfFuel _ => throw (IO.userError "return-data correspondence: direct copy exceeded fuel")

def run : IO Unit := do
  for scenario in [Scenario.empty, .sourceInvalid, .lengthInvalid] do
    check scenario false
    check scenario true
  checkNonempty false
  checkNonempty true

end Tests.RustHullReturnDataCorrespondence
