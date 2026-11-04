import Solcore.Synthesis.Internal.Storage
import Solcore.Synthesis.Source.ScalarMeaning.PureTheorems
import Solcore.Synthesis.Source.ScalarMeaning.LoopTheorems
import Solcore.Synthesis.Source.ScalarMeaning.StorageGrammar
import Solcore.ContractRuntime.TopLevelExecution
import Solcore.Synthesis.Internal.AdtStorage

/-!
# Emitter meaning: stateful profiles

The same for one top-level transaction on an installed contract. Main theorems:
`Storage.emit_source_meaning`, `StorageRollback.emit_source_meaning`,
`KeyedStorage.emit_source_meaning`, `EventLog.emit_source_meaning`.
-/

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.StorageEmitter
/-! Meaning preservation for the actual two-slot storage emitter
(`Storage.emit`, profile `stateful-storage`). The file imports `sload` and
`sstore`, declares the helpers as for the aggregate emitter and the entry as
`sc_step`. Its method reads slots 0 and 1, stores `sc_step(input + slot 0)` in
slot 0 and slot 1 plus one in slot 1, reads both slots again and returns their
sum.

The Core reference is a host-runtime contract: it reads the input word from
calldata at offset 4 and accesses storage through host requests. One
top-level transaction runs it with `TopLevelExecution.run` against a world in
which the contract is installed; the observation is the transaction's outcome
and the account storage of the world it commits. The step may allocate private
cells, which stay in the transaction's Core store. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core.StorageContract (CheckedPlan)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind?)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)
open Solcore.ContractRuntime

/-! ### The emitted text -/

/-- The fourteen primitive aliases, printed as `opcode as alias`. -/
theorem primitiveAliases_printed :
    primitiveAliases.map (fun alias => alias.1 ++ " as " ++ alias.2) =
      AggregateRenderer.opcodeAliases := by
  decide +kernel

theorem storageImport_eq (bodies : List CoreExpr) :
    AggregateRenderer.opcodeImportWith ["sload", "sstore"] bodies =
      storageImportLine (aggregateAliases bodies) := by
  unfold AggregateRenderer.opcodeImportWith storageImportLine aggregateAliases
  by_cases used : bodies.any AggregateRenderer.usesOpcodeAliases = true
  · simp only [used, if_true, primitiveAliases_printed]
  · simp only [used, Bool.false_eq_true, if_false, List.map_nil]

theorem Storage.emit_success {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : Storage.emit plan = .ok emitted) :
    ∃ (names lines : List String) (entry : ARendered) (result : String),
      aggregateLoop plan.step.helpers 0 []
        ["import * from std;", "import * from std.dispatch;",
          storageImportLine (aggregateAliases (plan.step.helpers ++ [plan.step.entry])), ""] =
        .ok (names, lines) ∧
      AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry = .ok entry ∧
      entry.value = some result ∧
      emitted.source = String.intercalate "\n" (lines ++
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
        ["    return " ++ result ++ ";", "}", "",
          "contract " ++ Storage.contractName ++ " {",
          "    function " ++ Storage.methodName ++ "(input: uint256) public returns (uint256) {",
          "        let sc_input: word = Typedef.rep(input);",
          "        let sc_old0: word = sload(0);",
          "        let sc_old1: word = sload(1);",
          "        let sc_computed: word = sc_step(sc_input + sc_old0);",
          "        sstore(0, sc_computed);",
          "        sstore(1, sc_old1 + 1);",
          "        let sc_final0: word = sload(0);",
          "        let sc_final1: word = sload(1);",
          "        return uint256(sc_final0 + sc_final1);", "    }", "}"]) ++ "\n" := by
  unfold Storage.emit at emitted_eq
  dsimp only at emitted_eq
  rw [forIn_aggregateLoop (fun _ _ _ _ => rfl), storageImport_eq] at emitted_eq
  cases loop : aggregateLoop plan.step.helpers 0 []
    ["import * from std;", "import * from std.dispatch;",
      storageImportLine (aggregateAliases (plan.step.helpers ++ [plan.step.entry])), ""] with
  | error error =>
      rw [loop] at emitted_eq
      cases emitted_eq
  | ok loopResult =>
      obtain ⟨names, lines⟩ := loopResult
      rw [loop] at emitted_eq
      cases entry : AggregateRenderer.render names .word [.word "sc_arg"] 4 0
        plan.step.entry with
      | error error =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases emitted_eq
      | ok rendered =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases value : AggregateRenderer.requireValue rendered with
          | error error =>
              simp only [value] at emitted_eq
              cases emitted_eq
          | ok result =>
              simp only [value, pure, Except.pure, Except.ok.injEq] at emitted_eq
              subst emitted_eq
              exact ⟨names, lines, rendered, result, rfl, entry, arequireValue_ok value, rfl⟩

/-- The method body the storage emitter prints. -/
def storageBody : List StorageStmt :=
  [.plain (.letDecl "sc_input" .word (.typedefRep (.name "input"))),
    .plain (.letDecl "sc_old0" .word (.call1 "sload" (.number 0))),
    .plain (.letDecl "sc_old1" .word (.call1 "sload" (.number 1))),
    .letCall "sc_computed" .word "sc_step" .add (.name "sc_input") (.name "sc_old0"),
    .store (.plain (.number 0)) (.plain (.name "sc_computed")),
    .store (.plain (.number 1)) (.operation .add (.name "sc_old1") (.number 1)),
    .plain (.letDecl "sc_final0" .word (.call1 "sload" (.number 0))),
    .plain (.letDecl "sc_final1" .word (.call1 "sload" (.number 1)))]

/-- The method the storage emitter prints. -/
def storageMethod : StorageMethod where
  name := "run"
  parameters := ["input"]
  body := storageBody
  result := .operation .add (.name "sc_final0") (.name "sc_final1")

/-- The storage file printed by the storage emitter. -/
def storageFile (aliases : List (String × String)) (declarations : List FunctionDecl)
    (statements : List Stmt) (value : String) : StorageFile where
  opcodeAliases := aliases
  functions := declarations ++ [stepDecl statements value]
  contract := "SynthesizedStorage"
  method := storageMethod

private theorem lines_eq_of_chars {first second : List String}
    (same : first.map String.toList = second.map String.toList) : first = second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons _ _ => simp at same
  | cons line rest ih =>
      cases second with
      | nil => simp at same
      | cons other more =>
          simp only [List.map_cons, List.cons.injEq] at same
          rw [String.toList_inj.mp same.1, ih same.2]

private theorem digits_one : Nat.toDigits 10 1 = ['1'] := by decide

theorem storageMethod_lines (rest : List String) :
    StorageStmt.listLines 8 storageMethod.body ++
      ("        return uint256(" ++ storageMethod.result.print ++ ");") :: rest =
    "        let sc_input: word = Typedef.rep(input);" ::
      "        let sc_old0: word = sload(0);" ::
      "        let sc_old1: word = sload(1);" ::
      "        let sc_computed: word = sc_step(sc_input + sc_old0);" ::
      "        sstore(0, sc_computed);" ::
      "        sstore(1, sc_old1 + 1);" ::
      "        let sc_final0: word = sload(0);" ::
      "        let sc_final1: word = sload(1);" ::
      "        return uint256(sc_final0 + sc_final1);" :: rest := by
  apply lines_eq_of_chars
  simp [storageMethod, storageBody, StorageStmt.listLines, StorageStmt.lines, Stmt.lines,
    indentLine, Expr.print, Operand.print, LocalType.spelling, BinaryOp.spelling, digits_one]

theorem storageBody_names_ok :
    ∀ name ∈ StorageStmt.listIdentifiers storageMethod.body ++ storageMethod.result.identifiers,
      ValidIdentifier name ∧ isReserved name = false := by
  have checked : ∀ name ∈ ["sc_input", "input", "sc_old0", "sload", "sc_old1", "sc_computed",
      "sc_step", "sc_final0", "sc_final1"],
      validIdentifier name = true ∧ isReserved name = false := by
    decide
  have within : ∀ name ∈ StorageStmt.listIdentifiers storageMethod.body ++
      storageMethod.result.identifiers,
      name ∈ ["sc_input", "input", "sc_old0", "sload", "sc_old1", "sc_computed", "sc_step",
        "sc_final0", "sc_final1"] := by
    simp [storageMethod, storageBody, StorageStmt.listIdentifiers, StorageStmt.identifiers,
      Operand.identifiers, Stmt.identifiers, Expr.identifiers]
  intro name mem
  have found := within name mem
  exact ⟨keyword_valid (checked name found).1, (checked name found).2⟩

/-! ### The source method -/

theorem Context.withStorage_call_sload (context : Context) (storage : Storage) (slot : Nat) :
    (context.withStorage storage).call "sload" [.word slot] = some (.word (storage slot)) := by
  simp [Context.withStorage, Context.call, loadMeaning]

theorem Context.withStorage_call_other (context : Context) (storage : Storage)
    {callee : String} (different : callee ≠ "sload") (arguments : List Value) :
    (context.withStorage storage).call callee arguments = context.call callee arguments := by
  have notSload : ("sload" == callee) = false := by
    simp only [beq_eq_false_iff_ne]
    exact fun same => different same.symm
  simp only [Context.withStorage, Context.call, List.find?_cons, notSload]

/-- The method reads both slots, stores the step's result for the input plus
slot 0 in slot 0 and slot 1 plus one in slot 1, and returns the sum of the two
slots it reads back. -/
theorem storageMethod_run (context : Context) (storage : Storage)
    (input first second computed : Solcore.Core.Word)
    (stepCall : context.call "sc_step" [.word (input.add first).val] =
      some (.word computed.val))
    (firstSlot : storage 0 = first.val) (secondSlot : storage 1 = second.val) :
    storageMethod.run context storage [input.val] =
      some ((computed.add (second.add (Solcore.Core.Word.ofNatModulo 1))).val,
        (storage.write 0 computed.val).write 1
          (second.add (Solcore.Core.Word.ofNatModulo 1)).val) := by
  have zero : 0 < Evm.modulus := by decide
  have one : (Solcore.Core.Word.ofNatModulo 1).val = 1 := ofNatModulo_val_small (by decide)
  have increment : Evm.add second.val 1 = (second.add (Solcore.Core.Word.ofNatModulo 1)).val := by
    have := evm_add second (Solcore.Core.Word.ofNatModulo 1)
    rwa [one] at this
  have stepCallBase : (context.withStorage storage).call "sc_step"
      [.word (input.add first).val] = some (.word computed.val) := by
    rw [Context.withStorage_call_other _ _ (by decide)]
    exact stepCall
  simp [StorageMethod.run, storageMethod, storageBody, Method.bindParameters, word_lt_modulus,
    StorageStmt.execList, StorageStmt.exec, Stmt.exec, Expr.eval, Operand.expr, Frames.lookup,
    Scope.get?, LocalType.admits, Frames.declare, BinaryOp.apply, Context.withStorage_call_sload,
    firstSlot, secondSlot, evm_add, stepCallBase, Storage.write, increment, one_lt_modulus, zero]

/-! ### The Core reference on the host machine -/

theorem hostSteps_of_steps {steps : Nat} {start finish : Solcore.Core.State}
    (path : Solcore.Core.Steps steps start finish) : Solcore.Core.HostSteps steps start finish := by
  induction path with
  | refl => exact .refl
  | cons step _ ih => exact .cons (.core step) ih

theorem hostSteps_cons {start next finish : Solcore.Core.State}
    (step : Solcore.Core.Transition start next)
    (rest : ∃ steps, Solcore.Core.HostSteps steps next finish) :
    ∃ steps, Solcore.Core.HostSteps steps start finish := by
  obtain ⟨_, path⟩ := rest
  exact ⟨_, .cons (.core step) path⟩

theorem hostSteps_eval {environment : Solcore.Core.Environment}
    {store store' : Solcore.Core.Store} {expression : Solcore.Core.Expr} {value : CoreValue}
    {continuation : List Solcore.Core.Frame} {finish : Solcore.Core.State}
    (evaluation : Solcore.Core.Evaluates environment store expression value store')
    (rest : ∃ steps, Solcore.Core.HostSteps steps ⟨.ret value, continuation, store'⟩ finish) :
    ∃ steps, Solcore.Core.HostSteps steps ⟨.eval expression environment, continuation, store⟩
      finish := by
  obtain ⟨_, path⟩ := evaluation.toStepsWithContinuation continuation
  obtain ⟨_, rest⟩ := rest
  exact ⟨_, (hostSteps_of_steps path).trans rest⟩

/-- Applying a host function looked up from the environment evaluates the
argument and stops at the host application. -/
theorem hostSteps_apply {environment : Solcore.Core.Environment} {index : Nat}
    {function : Solcore.Core.HostFunction} {argument : Solcore.Core.Expr} {value : CoreValue}
    {store store' : Solcore.Core.Store} {continuation : List Solcore.Core.Frame}
    (found : environment[index]? = some (.hostFunction function))
    (evaluation : Solcore.Core.Evaluates environment store argument value store') :
    ∃ steps, Solcore.Core.HostSteps steps
      ⟨.eval (.apply (.var index) argument) environment, continuation, store⟩
      ⟨.ret value, .hostApply function :: continuation, store'⟩ := by
  obtain ⟨_, path⟩ := evaluation.toStepsWithContinuation (.hostApply function :: continuation)
  exact ⟨_, .cons (.core .enterApply) (.cons (.core (.var found))
    (.cons .beginApplication (hostSteps_of_steps path)))⟩

theorem handledSteps_request {HostContext : Type} {handler : HostHandler HostContext}
    {context nextContext finalContext : HostContext}
    {start requestState resumed finish : Solcore.Core.State}
    {suspension : Solcore.Core.HostSuspension}
    (prefixPath : ∃ steps, Solcore.Core.HostSteps steps start requestState)
    (emission : Solcore.Core.HostRequestEmission requestState suspension)
    (supported : handler.supports suspension.request = true)
    (handled : handler.handleSuspension context suspension = (nextContext, resumed))
    (suffix : ∃ steps,
      HostDriver.HandledSteps handler steps nextContext resumed finalContext finish) :
    ∃ steps, HostDriver.HandledSteps handler steps context start finalContext finish := by
  obtain ⟨_, path⟩ := prefixPath
  obtain ⟨_, rest⟩ := suffix
  exact ⟨_, .handle path emission supported handled rest⟩

theorem handleSuspension_inputDataWordBE (inputs : HostStorageDriver.ExecutionInputs)
    (context : TransactionHostStorageDriver.Context) (offset : Solcore.Core.Word)
    (continuation : List Solcore.Core.Frame) (store : Solcore.Core.Store) :
    (TransactionHostStorageDriver.handler inputs).handleSuspension context
        ⟨.inputDataWordBE? offset, continuation, store⟩ =
      (context, ⟨.ret (Solcore.Core.HostRequest.responseValue (.inputDataWordBE? offset)
        (inputs.inputData.wordBE? offset)), continuation, store⟩) :=
  rfl

/-- The wrapper of `StorageContract.canonicalProgram`, restated: the step
closure, the input word, both slots, the step's result, both writes and the
sum of both slots. -/
def storageExpression (stepBody : Solcore.Core.Wire.Expr) : Solcore.Core.Wire.Expr :=
  .letE stepBody
    (.letE (.caseE (.apply (.var 9) (.word (Solcore.Core.Word.ofNatModulo 4)))
        (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0))
      (.letE (.apply (.var 2) (.word (Solcore.Core.Word.ofNatModulo 0)))
        (.letE (.apply (.var 3) (.word (Solcore.Core.Word.ofNatModulo 1)))
          (.letE (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1)))
            (.letE (.apply (.var 6) (.pair (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0)))
              (.letE (.apply (.var 7) (.pair (.word (Solcore.Core.Word.ofNatModulo 1))
                  (.binary .wordAdd (.var 2) (.word (Solcore.Core.Word.ofNatModulo 1)))))
                (.binary .wordAdd (.apply (.var 7) (.word (Solcore.Core.Word.ofNatModulo 0)))
                  (.apply (.var 7) (.word (Solcore.Core.Word.ofNatModulo 1))))))))))

theorem storageProgram_body (step : Solcore.Synthesis.Core.Aggregates.CheckedDAG) :
    (Solcore.Synthesis.Core.StorageContract.canonicalProgram step).body =
      storageExpression step.program.body :=
  rfl

/-- The Core continuations of the wrapper, from the sum back to the input. -/
def storageTail7 : Solcore.Core.Expr :=
  .binary .wordAdd (.apply (.var 7) (.word (Solcore.Core.Word.ofNatModulo 0)))
    (.apply (.var 7) (.word (Solcore.Core.Word.ofNatModulo 1)))

def storageTail6 : Solcore.Core.Expr :=
  .letE (.apply (.var 7) (.pair (.word (Solcore.Core.Word.ofNatModulo 1))
    (.binary .wordAdd (.var 2) (.word (Solcore.Core.Word.ofNatModulo 1))))) storageTail7

def storageTail5 : Solcore.Core.Expr :=
  .letE (.apply (.var 6) (.pair (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0))) storageTail6

def storageTail4 : Solcore.Core.Expr :=
  .letE (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1))) storageTail5

def storageTail3 : Solcore.Core.Expr :=
  .letE (.apply (.var 3) (.word (Solcore.Core.Word.ofNatModulo 1))) storageTail4

def storageTail2 : Solcore.Core.Expr :=
  .letE (.apply (.var 2) (.word (Solcore.Core.Word.ofNatModulo 0))) storageTail3

def storageTail1 : Solcore.Core.Expr :=
  .letE (.caseE (.apply (.var 9) (.word (Solcore.Core.Word.ofNatModulo 4)))
    (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0)) storageTail2

theorem storageExpression_toCore (stepBody : Solcore.Core.Wire.Expr) :
    (storageExpression stepBody).toCore = .letE stepBody.toCore storageTail1 := by
  simp only [storageExpression, Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore,
    storageTail1, storageTail2, storageTail3, storageTail4, storageTail5, storageTail6,
    storageTail7]

/-- **The Core reference's transaction, as a handled host path.** From the
initial state, the wrapper binds the step closure, decodes the input, reads
both slots, applies the step, writes both slots and returns the sum of the
slots it reads back. -/
theorem storage_handled {inputs : HostStorageDriver.ExecutionInputs}
    {context : TransactionHostStorageDriver.Context} {step : Solcore.Core.Expr}
    {closure : CoreValue} {input computed : Solcore.Core.Word} {store : Solcore.Core.Store}
    (stepEvaluates : Solcore.Core.Evaluates Solcore.Core.hostEnvironment [] step closure [])
    (decoded : inputs.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 4) = some input)
    (applied : Solcore.Core.Evaluates
      (.word (context.readStorage (Solcore.Core.Word.ofNatModulo 1)) ::
        .word (context.readStorage (Solcore.Core.Word.ofNatModulo 0)) ::
        .word input :: closure :: Solcore.Core.hostEnvironment) []
      (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1))) (.word computed) store) :
    ∃ steps, HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
      (Solcore.Core.State.initial (.letE step storageTail1) Solcore.Core.hostEnvironment)
      ((context.writeStorage (Solcore.Core.Word.ofNatModulo 0) computed).writeStorage
        (Solcore.Core.Word.ofNatModulo 1)
        ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
          (Solcore.Core.Word.ofNatModulo 1)))
      (Solcore.Core.State.final (.word (computed.add
        ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
          (Solcore.Core.Word.ofNatModulo 1)))) store) := by
  let environment1 : Solcore.Core.Environment := closure :: Solcore.Core.hostEnvironment
  let environment2 : Solcore.Core.Environment := .word input :: environment1
  let environment3 : Solcore.Core.Environment :=
    .word (context.readStorage (Solcore.Core.Word.ofNatModulo 0)) :: environment2
  let environment5 : Solcore.Core.Environment := .word computed ::
    .word (context.readStorage (Solcore.Core.Word.ofNatModulo 1)) :: environment3
  let environment6 : Solcore.Core.Environment := .unit :: environment5
  let environment7 : Solcore.Core.Environment := .unit :: environment6
  let written : TransactionHostStorageDriver.Context :=
    context.writeStorage (Solcore.Core.Word.ofNatModulo 0) computed
  let final : TransactionHostStorageDriver.Context :=
    written.writeStorage (Solcore.Core.Word.ofNatModulo 1)
      ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
        (Solcore.Core.Word.ofNatModulo 1))
  have firstRead : final.readStorage (Solcore.Core.Word.ofNatModulo 0) = computed := by
    simp only [final, written]
    rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_other _ _ _ _
      (by decide), FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same]
  have secondRead : final.readStorage (Solcore.Core.Word.ofNatModulo 1) =
      (context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
        (Solcore.Core.Word.ofNatModulo 1) := by
    simp only [final]
    rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same]
  have finish : ∃ steps, HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs)
      steps final ⟨.ret (.word (final.readStorage (Solcore.Core.Word.ofNatModulo 1))),
        [.binaryApply .wordAdd (.word (final.readStorage (Solcore.Core.Word.ofNatModulo 0)))],
        store⟩ final
      (Solcore.Core.State.final (.word (computed.add
        ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
          (Solcore.Core.Word.ofNatModulo 1)))) store) := by
    rw [firstRead, secondRead]
    exact ⟨_, .core (.cons (.core (.applyBinary rfl)) .refl)⟩
  have secondFinal : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps final
        ⟨.ret (.word (final.readStorage (Solcore.Core.Word.ofNatModulo 0))),
          [.binaryRight .wordAdd (.apply (.var 7) (.word (Solcore.Core.Word.ofNatModulo 1)))
            environment7], store⟩ final
        (Solcore.Core.State.final (.word (computed.add
          ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
            (Solcore.Core.Word.ofNatModulo 1)))) store) :=
    handledSteps_request (hostSteps_cons .enterBinaryRight (hostSteps_apply (index := 7) rfl .word))
      .storageRead rfl rfl finish
  have firstFinal : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps final
        ⟨.ret .unit, [.letBody storageTail7 environment6], store⟩ final
        (Solcore.Core.State.final (.word (computed.add
          ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
            (Solcore.Core.Word.ofNatModulo 1)))) store) :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterBinary
      (hostSteps_apply (index := 7) rfl .word))) .storageRead rfl rfl secondFinal
  have secondWrite : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps written
        ⟨.ret .unit, [.letBody storageTail6 environment5], store⟩ final
        (Solcore.Core.State.final (.word (computed.add
          ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
            (Solcore.Core.Word.ofNatModulo 1)))) store) :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_apply (index := 7) rfl (.pair .word (.binary (.var rfl) .word rfl)))))
      .storageWrite rfl rfl firstFinal
  have firstWrite : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.word (context.readStorage (Solcore.Core.Word.ofNatModulo 1))),
          [.letBody storageTail4 environment3], []⟩ final
        (Solcore.Core.State.final (.word (computed.add
          ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
            (Solcore.Core.Word.ofNatModulo 1)))) store) :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_eval applied (hostSteps_cons .bindLet (hostSteps_cons .enterLet
        (hostSteps_apply (index := 6) rfl (.pair .word (.var rfl))))))))
      .storageWrite rfl rfl secondWrite
  have secondLoad : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.word (context.readStorage (Solcore.Core.Word.ofNatModulo 0))),
          [.letBody storageTail3 environment2], []⟩ final
        (Solcore.Core.State.final (.word (computed.add
          ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
            (Solcore.Core.Word.ofNatModulo 1)))) store) :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_apply (index := 3) rfl .word))) .storageRead rfl rfl firstWrite
  have firstLoad : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.inRight .unit (.word input)),
          [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment1,
            .letBody storageTail2 environment1], []⟩ final
        (Solcore.Core.State.final (.word (computed.add
          ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
            (Solcore.Core.Word.ofNatModulo 1)))) store) :=
    handledSteps_request (hostSteps_cons .chooseRight (hostSteps_cons (.var rfl)
      (hostSteps_cons .bindLet (hostSteps_cons .enterLet
        (hostSteps_apply (index := 2) rfl .word))))) .storageRead rfl rfl secondLoad
  have resumed : (TransactionHostStorageDriver.handler inputs).handleSuspension context
      ⟨.inputDataWordBE? (Solcore.Core.Word.ofNatModulo 4),
        [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment1,
          .letBody storageTail2 environment1], []⟩ =
      (context, ⟨.ret (.inRight .unit (.word input)),
        [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment1,
          .letBody storageTail2 environment1], []⟩) := by
    rw [handleSuspension_inputDataWordBE, decoded]
    rfl
  exact handledSteps_request (hostSteps_cons .enterLet (hostSteps_eval stepEvaluates
    (hostSteps_cons .bindLet (hostSteps_cons .enterLet (hostSteps_cons .enterCase
      (hostSteps_apply (index := 9) rfl .word)))))) .inputDataWordBE? rfl resumed firstLoad

/-! ### One top-level transaction -/

/-- A raw run that returns a value completes the top-level transaction with
the contract's decoding of that value. -/
theorem topLevel_run_completed {initialWorld : WorldState} (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed : InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) (context : TransactionHostStorageDriver.Context) (value : CoreValue)
    (store : Solcore.Core.Store) (outcome : FrameOutcome Solcore.Core.Word)
    (raw : TopLevelExecution.rawRun contract invocation installed fuel =
      ⟨context, .done value store⟩)
    (decoded : contract.decodeCompletion? value = some outcome) :
    ∃ result, TopLevelExecution.run contract invocation installed fuel = .completed result ∧
      result.outcome = outcome ∧ result.coreValue = value ∧ result.coreStore = store ∧
      result.terminalContext = context ∧
      ∀ data, outcome = .returned data →
        result.finalWorld = context.context.values.working.1 := by
  have resultEq : (TopLevelExecution.validatedRawRun contract invocation installed fuel).result =
      TopLevelExecution.rawRun contract invocation installed fuel := rfl
  unfold TopLevelExecution.run TopLevelExecution.classifyRawResult
  split
  · rename_i value' store' outcomeEq
    rw [resultEq, raw] at outcomeEq
    cases outcomeEq
    split
    · rename_i outcome' decodedEq
      rw [decoded] at decodedEq
      cases decodedEq
      refine ⟨_, rfl, by simp, by cases outcome <;> rfl, by cases outcome <;> rfl, ?_, ?_⟩
      · simp only [TopLevelExecution.terminalContext_finalize]
        rw [resultEq, raw]
      · intro data same
        subst same
        simp only [TopLevelExecution.finalWorld_finalize_returned]
        rw [resultEq, raw]
    · rename_i decodedEq
      rw [decoded] at decodedEq
      cases decodedEq
  all_goals
    rename_i outcomeEq
    rw [resultEq, raw] at outcomeEq
    cases outcomeEq

/-- The storage an account holds, read at each slot below `2^256`. -/
def accountStorage (account : Account) : Storage :=
  fun slot => (account.storageRead (Solcore.Core.Word.ofNatModulo slot)).val

/-- An account holds, at every slot, the word that a source storage holds there. -/
def StorageAgrees (account : Account) (storage : Storage) : Prop :=
  ∀ slot : Solcore.Core.Word, (account.storageRead slot).val = storage slot.val

/-- **The observation of one transaction.** With enough fuel, the top-level
transaction of the installed contract completes; every completed run returns
the ABI encoding of `word`, with Core result `word`, and commits a world whose
target account holds `storage`. -/
def CoreCommits {world : WorldState} (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed : InstalledCheckedCoreContract world invocation.target contract)
    (word : Solcore.Core.Word) (storage : Storage) : Prop :=
  (∃ enough, ∀ fuel, enough ≤ fuel →
    ∃ result, TopLevelExecution.run contract invocation installed fuel = .completed result) ∧
  ∀ fuel result, TopLevelExecution.run contract invocation installed fuel = .completed result →
    result.outcome = .returned (encodeWordBytesBE word) ∧ result.coreValue = .word word ∧
    ∃ account, result.finalWorld.account? invocation.target = some account ∧
      StorageAgrees account storage

theorem word_ofNatModulo_val (word : Solcore.Core.Word) :
    Solcore.Core.Word.ofNatModulo word.val = word :=
  Fin.ext (Nat.mod_eq_of_lt word.isLt)

/-- Two writes through the context, read as source storage. -/
theorem storageAgrees_writes (account : Account) (computed second : Solcore.Core.Word) :
    StorageAgrees ((account.storageWrite (Solcore.Core.Word.ofNatModulo 0) computed).storageWrite
        (Solcore.Core.Word.ofNatModulo 1) second)
      (((accountStorage account).write 0 computed.val).write 1 second.val) := by
  intro slot
  have zeroVal : (Solcore.Core.Word.ofNatModulo 0).val = 0 := ofNatModulo_val_small (by decide)
  have oneVal : (Solcore.Core.Word.ofNatModulo 1).val = 1 := ofNatModulo_val_small (by decide)
  by_cases isOne : slot = Solcore.Core.Word.ofNatModulo 1
  · subst isOne
    rw [Account.storageRead_storageWrite_same]
    simp [Storage.write, oneVal]
  · have oneNe : slot.val ≠ 1 := fun same => isOne (Fin.ext (by rw [same, oneVal]))
    rw [Account.storageRead_storageWrite_other _ _ _ _ isOne]
    by_cases isZero : slot = Solcore.Core.Word.ofNatModulo 0
    · subst isZero
      rw [Account.storageRead_storageWrite_same]
      simp [Storage.write, zeroVal]
    · have zeroNe : slot.val ≠ 0 := fun same => isZero (Fin.ext (by rw [same, zeroVal]))
      rw [Account.storageRead_storageWrite_other _ _ _ _ isZero]
      simp [Storage.write, accountStorage, oneNe, zeroNe, word_ofNatModulo_val]

/-! ### Preservation -/

/-- **Storage emitter preservation.** If the actual emitter succeeds, its source
text is the printing of a storage file with one free function per helper and
the step function `sc_step`, importing `sload`, `sstore` and the raw opcode
aliases exactly when a rendered body uses one, and parses back to it. For every
world in which the contract is installed and every calldata whose word at
offset 4 is `input`, calling `run(uint256)` from the installed account's
storage under the storage source semantics returns the Word and the final
storage that the original Core contract's top-level transaction returns and
commits. -/
theorem Storage.emit_preserves_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : Storage.emit plan = .ok emitted) :
    ∃ file : StorageFile, emitted.source = file.print ∧
      parseStorageSource emitted.source = some file ∧
      ∀ {world : WorldState} {invocation : TopLevelInvocation}
        (installed : InstalledCheckedCoreContract world invocation.target plan.contract)
        {input : Solcore.Core.Word},
        invocation.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 4) = some input →
        ∃ (word : Solcore.Core.Word) (storage : Storage),
          file.call (accountStorage installed.account) "run" [input.val] =
            some (word.val, storage) ∧
          CoreCommits plan.contract invocation installed word storage := by
  obtain ⟨names, lines, entry, result, loop, entryEquation, resultFound, source⟩ :=
    Storage.emit_success emitted_eq
  let bodies := plan.step.helpers ++ [plan.step.entry]
  let uses := bodies.any AggregateRenderer.usesOpcodeAliases
  have aliasesOk : uses = true → aggregateAliases bodies = primitiveAliases := by
    intro used
    simp only [aggregateAliases]
    rw [if_pos used]
  have bodyUses : ∀ body ∈ bodies, AggregateRenderer.usesOpcodeAliases body = true →
      uses = true := fun body mem used => List.any_eq_true.mpr ⟨body, mem, used⟩
  have startPrimitive : uses = true → PrimitiveContext ⟨[], aggregateAliases bodies⟩ := by
    intro used
    rw [aliasesOk used]
    exact primitiveContext_aliases
  obtain ⟨declarations, linesEq, namesEq, declarationsOk, primitive, agree⟩ :=
    aggregateLoop_spec aliasesOk plan.step.helpers 0 _ names lines [] Solcore.Core.hostEnvironment
      loop
      (fun index body found =>
        ⟨aggregate_helpers_accepted plan.step.helperScopes index body found,
          bodyUses body (List.mem_append_left _ (List.mem_of_getElem? found))⟩)
      startPrimitive (fun _ _ found => by simp [helperNames] at found)
  have entryKind : initializerKind? ([Binding.word "sc_arg"].map Binding.kind) names.length
      plan.step.entry = some Local.word := by
    rw [namesEq, helperNames_length, Nat.zero_add]
    exact aggregate_acceptsAt_kind plan.step.entryScope
  obtain ⟨statements, entryLines, _, valueName, entryNames, simulates⟩ :=
    (aggregate_render_spec plan.step.entry).1
      (fun context => uses = true → PrimitiveContext context)
      (fun context admitted used =>
        admitted (bodyUses plan.step.entry (List.mem_append_right _ (by simp)) used))
      names .word [.word "sc_arg"] 4 0 entry entryKind entryEquation
      (single_abinding_fresh argument_not_temporary cellTemp_ne_argument
        payloadTemp_ne_argument)
      (single_abinding_distinct _)
  let file := storageFile (aggregateAliases bodies) declarations statements result
  have argumentOk : ∀ index found, anameAt [Binding.word "sc_arg"] index = some found →
      ValidIdentifier found ∧ isReserved found = false :=
    single_abinding_ok (keyword_valid (by decide)) (by decide)
  have functionNamesOk : ∀ name ∈ names, ValidIdentifier name ∧ isReserved name = false := by
    rw [namesEq]
    exact helperNames_ok
  have valueOk := aggregate_identifier_ok argumentOk functionNamesOk
    (valueName result resultFound).uses
  have stepOk : (stepDecl statements result).NamesOk ∧
      ∀ name ∈ (stepDecl statements result).identifiers, ValidIdentifier name := by
    have bodyOk := fun name mem =>
      aggregate_identifier_ok argumentOk functionNamesOk (entryNames name mem)
    refine ⟨⟨show isReserved "sc_step" = false by decide, ?_,
      fun name mem => (bodyOk name mem).2, ?_⟩, ?_⟩
    · intro parameter mem
      simp only [stepDecl, List.mem_singleton] at mem
      subst mem
      decide
    · intro name mem
      simp only [stepDecl, Expr.identifiers, List.mem_singleton] at mem
      subst mem
      exact valueOk.2
    · intro name mem
      simp only [stepDecl, FunctionDecl.identifiers, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.mem_append, Expr.identifiers,
        List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | mem | rfl
      · exact keyword_valid (by decide)
      · exact keyword_valid (by decide)
      · exact (bodyOk name mem).1
      · exact valueOk.1
  have functionsOk : ∀ function ∈ file.functions, function.NamesOk ∧
      ∀ name ∈ function.identifiers, ValidIdentifier name := by
    intro function mem
    rcases List.mem_append.mp mem with mem | mem
    · exact declarationsOk function mem
    · simp only [List.mem_singleton] at mem
      subst mem
      exact stepOk
  have printed : emitted.source = file.print := by
    have stepLines : (stepDecl statements result).lines =
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
          ["    return " ++ result ++ ";", "}", ""] := by
      simp only [stepDecl, FunctionDecl.lines, entryLines, List.cons_append, List.nil_append,
        List.cons.injEq]
      refine ⟨?_, ?_⟩
      · apply String.toList_inj.mp
        simp [FunctionDecl.parameterText, LocalType.spelling]
      · simp [Expr.print]
    have functionLine : "    function " ++ Storage.methodName ++
        "(input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply String.toList_inj.mp
      simp [file, storageFile, storageMethod, Method.parameterText, Storage.methodName]
    rw [source, StorageFile.print, StorageFile.lines, linesEq, functionLine]
    simp [file, storageFile, Storage.contractName, stepLines, bodies, storageMethod_lines]
  have bodyNames := storageBody_names_ok
  have parsed : parseStorageSource emitted.source = some file := by
    rw [printed]
    apply parseStorageSource_print
    · refine ⟨fun function mem => (functionsOk function mem).1, rfl, rfl, ?_,
        fun name mem => (bodyNames name (List.mem_append_left _ mem)).2,
        fun name mem => (bodyNames name (List.mem_append_right _ mem)).2⟩
      intro parameter mem
      simp only [file, storageFile, storageMethod, List.mem_singleton] at mem
      subst mem
      decide
    · refine ⟨aggregateAliases_valid bodies, fun function mem => (functionsOk function mem).2,
        keyword_valid (show validIdentifier "SynthesizedStorage" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (bodyNames name (List.mem_append_left _ mem)).1,
        fun name mem => (bodyNames name (List.mem_append_right _ mem)).1⟩
      intro parameter mem
      simp only [file, storageFile, storageMethod, List.mem_singleton] at mem
      subst mem
      exact keyword_valid (by decide)
  refine ⟨file, printed, parsed, ?_⟩
  intro world invocation installed input calldata
  have stepCall : ∀ arguments, file.context.call "sc_step" arguments =
      (stepDecl statements result).denote
        ⟨declareFunctions (aggregateAliases bodies) [] declarations, aggregateAliases bodies⟩
        arguments := by
    intro arguments
    show Context.call ⟨declareFunctions (aggregateAliases bodies) []
      (declarations ++ [stepDecl statements result]), aggregateAliases bodies⟩ "sc_step"
        arguments = _
    rw [declareFunctions_append_single]
    exact Context.call_cons_same _ _ _ _ _
  let first := installed.account.storageRead (Solcore.Core.Word.ofNatModulo 0)
  let second := installed.account.storageRead (Solcore.Core.Word.ofNatModulo 1)
  obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _, _, _⟩ :=
    simulates ⟨declareFunctions (aggregateAliases bodies) [] declarations,
        aggregateAliases bodies⟩
      (.word (input.add first) :: plan.step.helpers.foldl closureStep Solcore.Core.hostEnvironment)
      [] [] [[("sc_arg", .word (input.add first).val)]] primitive
      (single_abinding_agree (by simp [Frames.lookup, Scope.get?]) _ [])
      (single_abinding_cells _ _ _) (by simp) (by simpa using agree)
  rw [resultFound, Option.bind_some] at represents
  obtain ⟨_, lookup, computed, rfl, rfl⟩ := represents
  have sourceStep : file.context.call "sc_step" [.word (input.add first).val] =
      some (.word computed.val) := by
    rw [stepCall]
    simp [stepDecl, FunctionDecl.denote, FunctionDecl.bindParameters, LocalType.admits, exec,
      Expr.eval, lookup]
  refine ⟨computed.add (second.add (Solcore.Core.Word.ofNatModulo 1)),
    ((accountStorage installed.account).write 0 computed.val).write 1
      (second.add (Solcore.Core.Word.ofNatModulo 1)).val, ?_, ?_⟩
  · show (if file.method.name = "run" then file.method.run file.context
      (accountStorage installed.account) [input.val] else none) = _
    rw [if_pos (show file.method.name = "run" from rfl)]
    exact storageMethod_run file.context _ input first second computed sourceStep rfl rfl
  · let context := TopLevelExecution.initialTransactionContext installed
    have stepEvaluates := dag_evaluates plan.step.entry plan.step.helpers
      Solcore.Core.hostEnvironment []
    have applied : Solcore.Core.Evaluates
        (.word (context.readStorage (Solcore.Core.Word.ofNatModulo 1)) ::
          .word (context.readStorage (Solcore.Core.Word.ofNatModulo 0)) ::
          .word input :: .closure (Solcore.Core.Wire.Ty.toCore .word)
            (Solcore.Core.Wire.Ty.toCore .word) plan.step.entry.toCore
            (plan.step.helpers.foldl closureStep Solcore.Core.hostEnvironment) ::
          Solcore.Core.hostEnvironment) []
        (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1))) (.word computed) store' :=
      .apply (.var rfl) (.binary (.var rfl) (.var rfl) rfl) evaluates
    obtain ⟨spent, path⟩ := storage_handled (inputs := invocation.executionInputs)
      (context := context) stepEvaluates calldata applied
    have body : plan.contract.code.program.body =
        .letE (Solcore.Synthesis.Core.functionDAGExpression plan.step.helpers
          plan.step.entry).toCore storageTail1 := by
      show (storageExpression plan.step.program.body).toCore = _
      rw [storageExpression_toCore]
      rfl
    have raw : ∀ fuel, spent ≤ fuel →
        TopLevelExecution.rawRun plan.contract invocation installed fuel =
          ⟨(context.writeStorage (Solcore.Core.Word.ofNatModulo 0) computed).writeStorage
              (Solcore.Core.Word.ofNatModulo 1) (second.add (Solcore.Core.Word.ofNatModulo 1)),
            .done (.word (computed.add (second.add (Solcore.Core.Word.ofNatModulo 1)))) store'⟩ := by
      intro fuel enough
      show HostDriver.run (TransactionHostStorageDriver.handler invocation.executionInputs)
        context fuel (Solcore.Core.State.initial plan.contract.code.program.body
          Solcore.Core.hostEnvironment) = _
      rw [body]
      exact HostDriver.run_done_complete _ path enough
    have committed : ∀ fuel, spent ≤ fuel → ∃ result,
        TopLevelExecution.run plan.contract invocation installed fuel = .completed result ∧
        result.outcome = .returned (encodeWordBytesBE
          (computed.add (second.add (Solcore.Core.Word.ofNatModulo 1)))) ∧
        result.coreValue = .word (computed.add (second.add (Solcore.Core.Word.ofNatModulo 1))) ∧
        ∃ account, result.finalWorld.account? invocation.target = some account ∧
          StorageAgrees account (((accountStorage installed.account).write 0 computed.val).write 1
            (second.add (Solcore.Core.Word.ofNatModulo 1)).val) := by
      intro fuel enough
      obtain ⟨result, run, outcome, value, _, _, finalWorld⟩ := topLevel_run_completed
        plan.contract invocation installed fuel _ _ _ _ (raw fuel enough) rfl
      let final : TransactionHostStorageDriver.Context :=
        (context.writeStorage (Solcore.Core.Word.ofNatModulo 0) computed).writeStorage
          (Solcore.Core.Word.ofNatModulo 1) (second.add (Solcore.Core.Word.ofNatModulo 1))
      have address : final.context.storageAddress = invocation.target := by
        simp [final, context]
      have account : final.storageAccount =
          (installed.account.storageWrite (Solcore.Core.Word.ofNatModulo 0) computed).storageWrite
            (Solcore.Core.Word.ofNatModulo 1) (second.add (Solcore.Core.Word.ofNatModulo 1)) := by
        simp [final, context]
      refine ⟨result, run, outcome, value, final.storageAccount, ?_, ?_⟩
      · rw [finalWorld _ rfl, ← address]
        exact final.storageAccount_present
      · rw [account]
        exact storageAgrees_writes installed.account computed _
    refine ⟨⟨spent, fun fuel enough => (committed fuel enough).elim fun result facts =>
      ⟨result, facts.1⟩⟩, ?_⟩
    intro fuel result run
    obtain ⟨result', run', facts⟩ := committed (fuel + spent) (by omega)
    have resumed := TopLevelExecution.resumeWithFuel_run plan.contract invocation installed fuel
      spent
    rw [run, TopLevelExecution.resumeWithFuel_completed, run'] at resumed
    cases resumed
    exact facts

/-- **Storage emitter preservation, on the emitted text.** Read as a storage
program, the emitted text called from the installed account's storage returns
the Word that the original Core contract's transaction returns, and ends with
the storage that the transaction commits for that account. -/
theorem Storage.emit_source_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : Storage.emit plan = .ok emitted)
    {world : WorldState} {invocation : TopLevelInvocation}
    (installed : InstalledCheckedCoreContract world invocation.target plan.contract)
    {input : Solcore.Core.Word}
    (calldata : invocation.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 4) = some input) :
    ∃ (word : Solcore.Core.Word) (storage : Storage),
      storageSourceCall emitted.source (accountStorage installed.account) "run" [input.val] =
        some (word.val, storage) ∧
      CoreCommits plan.contract invocation installed word storage := by
  obtain ⟨file, _, parsed, meaning⟩ := Storage.emit_preserves_meaning emitted_eq
  obtain ⟨word, storage, call, commits⟩ := meaning installed calldata
  exact ⟨word, storage, by simp [storageSourceCall, parsed, call], commits⟩

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.RollbackEmitter
/-! Meaning preservation for the actual two-slot rollback emitter
(`StorageRollback.emit`, profile `stateful-storage-rollback`). The file imports
`sload`, `sstore`, `mstore` and `revert_`, and declares the helpers and the
entry as the storage emitter does. Its method runs the storage protocol, binds
the sum of both slots read back, and, for an odd input, stores that sum at
memory offset 0 and reverts with those 32 bytes; otherwise it returns the sum.

The Core reference is a host-runtime contract with the three-way Word outcome
profile. It runs the same storage requests and then returns the sum on the
left of its result, or, for an odd input, the revert tag with the sum. One
top-level transaction runs it on a world in which it is installed. A returning
transaction commits its storage writes; a reverting one commits the world it
started from, so the installed account keeps its storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core.StorageRollback (CheckedPlan)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind?)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)
open Solcore.ContractRuntime

/-! ### The emitted text -/

theorem rollbackImport_eq (bodies : List CoreExpr) :
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_"] bodies =
      rollbackImportLine (aggregateAliases bodies) := by
  unfold AggregateRenderer.opcodeImportWith rollbackImportLine aggregateAliases
  by_cases used : bodies.any AggregateRenderer.usesOpcodeAliases = true
  · simp only [used, if_true, primitiveAliases_printed]
  · simp only [used, Bool.false_eq_true, if_false, List.map_nil]

theorem StorageRollback.emit_success {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : StorageRollback.emit plan = .ok emitted) :
    ∃ (names lines : List String) (entry : ARendered) (result : String),
      aggregateLoop plan.step.helpers 0 []
        ["import * from std;", "import * from std.dispatch;",
          rollbackImportLine (aggregateAliases (plan.step.helpers ++ [plan.step.entry])), ""] =
        .ok (names, lines) ∧
      AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry = .ok entry ∧
      entry.value = some result ∧
      emitted.source = String.intercalate "\n" (lines ++
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
        ["    return " ++ result ++ ";", "}", "",
          "contract " ++ StorageRollback.contractName ++ " {",
          "    function " ++ StorageRollback.methodName ++
            "(input: uint256) public returns (uint256) {",
          "        let sc_input: word = Typedef.rep(input);",
          "        let sc_old0: word = sload(0);",
          "        let sc_old1: word = sload(1);",
          "        let sc_computed: word = sc_step(sc_input + sc_old0);",
          "        sstore(0, sc_computed);",
          "        sstore(1, sc_old1 + 1);",
          "        let sc_final0: word = sload(0);",
          "        let sc_final1: word = sload(1);",
          "        let sc_result: word = sc_final0 + sc_final1;",
          "        if ((sc_input & 1) == 1) {",
          "            mstore(0, sc_result);",
          "            revert_(0, 32);",
          "        }",
          "        return uint256(sc_result);", "    }", "}"]) ++ "\n" := by
  unfold StorageRollback.emit at emitted_eq
  dsimp only at emitted_eq
  rw [forIn_aggregateLoop (fun _ _ _ _ => rfl), rollbackImport_eq] at emitted_eq
  cases loop : aggregateLoop plan.step.helpers 0 []
    ["import * from std;", "import * from std.dispatch;",
      rollbackImportLine (aggregateAliases (plan.step.helpers ++ [plan.step.entry])), ""] with
  | error error =>
      rw [loop] at emitted_eq
      cases emitted_eq
  | ok loopResult =>
      obtain ⟨names, lines⟩ := loopResult
      rw [loop] at emitted_eq
      cases entry : AggregateRenderer.render names .word [.word "sc_arg"] 4 0
        plan.step.entry with
      | error error =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases emitted_eq
      | ok rendered =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases value : AggregateRenderer.requireValue rendered with
          | error error =>
              simp only [value] at emitted_eq
              cases emitted_eq
          | ok result =>
              simp only [value, pure, Except.pure, Except.ok.injEq] at emitted_eq
              subst emitted_eq
              exact ⟨names, lines, rendered, result, rfl, entry, arequireValue_ok value, rfl⟩

/-- The method body the rollback emitter prints. -/
def rollbackBody : List RollbackStmt :=
  storageBody.map .storage ++
    [.letOperation "sc_result" .word .add (.name "sc_final0") (.name "sc_final1"),
      .revertIf .eq (.binary .bitAnd (.name "sc_input") (.number 1)) (.number 1)
        (.plain (.number 0)) (.plain (.name "sc_result")) (.plain (.number 0))
        (.plain (.number 32))]

/-- The method the rollback emitter prints. -/
def rollbackMethod : RollbackMethod where
  name := "run"
  parameters := ["input"]
  body := rollbackBody
  result := .plain (.name "sc_result")

/-- The rollback file printed by the rollback emitter. -/
def rollbackFile (aliases : List (String × String)) (declarations : List FunctionDecl)
    (statements : List Stmt) (value : String) : RollbackFile where
  opcodeAliases := aliases
  functions := declarations ++ [stepDecl statements value]
  contract := "SynthesizedRollback"
  method := rollbackMethod

private theorem digits_thirtyTwo : Nat.toDigits 10 32 = ['3', '2'] := by decide

theorem rollbackMethod_lines (rest : List String) :
    RollbackStmt.listLines 8 rollbackMethod.body ++
      ("        return uint256(" ++ rollbackMethod.result.print ++ ");") :: rest =
    "        let sc_input: word = Typedef.rep(input);" ::
      "        let sc_old0: word = sload(0);" ::
      "        let sc_old1: word = sload(1);" ::
      "        let sc_computed: word = sc_step(sc_input + sc_old0);" ::
      "        sstore(0, sc_computed);" ::
      "        sstore(1, sc_old1 + 1);" ::
      "        let sc_final0: word = sload(0);" ::
      "        let sc_final1: word = sload(1);" ::
      "        let sc_result: word = sc_final0 + sc_final1;" ::
      "        if ((sc_input & 1) == 1) {" ::
      "            mstore(0, sc_result);" ::
      "            revert_(0, 32);" ::
      "        }" ::
      "        return uint256(sc_result);" :: rest := by
  apply lines_eq_of_chars
  simp [rollbackMethod, rollbackBody, storageBody, RollbackStmt.listLines, RollbackStmt.lines,
    StorageStmt.lines, Stmt.lines, indentLine, Expr.print, Operand.print, LocalType.spelling,
    BinaryOp.spelling, digits_one, digits_thirtyTwo]

theorem rollbackBody_names_ok :
    ∀ name ∈ RollbackStmt.listIdentifiers rollbackMethod.body ++
      rollbackMethod.result.identifiers, ValidIdentifier name ∧ isReserved name = false := by
  have checked : ∀ name ∈ ["sc_input", "input", "sc_old0", "sload", "sc_old1", "sc_computed",
      "sc_step", "sc_final0", "sc_final1", "sc_result"],
      validIdentifier name = true ∧ isReserved name = false := by
    decide
  have within : ∀ name ∈ RollbackStmt.listIdentifiers rollbackMethod.body ++
      rollbackMethod.result.identifiers,
      name ∈ ["sc_input", "input", "sc_old0", "sload", "sc_old1", "sc_computed", "sc_step",
        "sc_final0", "sc_final1", "sc_result"] := by
    simp [rollbackMethod, rollbackBody, storageBody, RollbackStmt.listIdentifiers,
      RollbackStmt.identifiers, StorageStmt.identifiers, Operand.identifiers, Stmt.identifiers,
      Expr.identifiers]
  intro name mem
  have found := within name mem
  exact ⟨keyword_valid (checked name found).1, (checked name found).2⟩

/-! ### The source method -/

/-- The source test of the input's low bit is the Core one. -/
theorem rollback_flag (word : Solcore.Core.Word) :
    toBool (Evm.eq (Evm.and word.val 1) 1) =
      (word.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1) := by
  have conjunction := evm_and word (Solcore.Core.Word.ofNatModulo 1)
  have equality := evm_eq (word.bitAnd (Solcore.Core.Word.ofNatModulo 1))
    (Solcore.Core.Word.ofNatModulo 1)
  rw [ofNatModulo_val_small (by decide)] at conjunction equality
  rw [conjunction]
  exact equality

/-- The Core low-bit test is the parity of the input. -/
theorem rollback_parity (input : Solcore.Core.Word) :
    (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1) =
      decide (input.val % 2 = 1) := by
  have one : (Solcore.Core.Word.ofNatModulo 1).val = 1 := ofNatModulo_val_small (by decide)
  have masked : (input.bitAnd (Solcore.Core.Word.ofNatModulo 1)).val = input.val % 2 := by
    rw [← evm_and, one]
    simp [Evm.and, Nat.and_one_is_mod]
  by_cases odd : input.val % 2 = 1
  · have same : input.bitAnd (Solcore.Core.Word.ofNatModulo 1) =
        Solcore.Core.Word.ofNatModulo 1 := Fin.ext (by rw [masked, odd, one])
    simp [same, odd]
  · have different : input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ≠
        Solcore.Core.Word.ofNatModulo 1 := fun same => odd (by rw [← masked, same, one])
    simp [different, odd]

/-- The outcome the rollback method gives from the step's result: the sum of
both slots read back, reverted for an odd input and returned with the written
storage otherwise. -/
def rollbackOutcome (storage : Storage) (input second computed : Solcore.Core.Word) :
    RollbackOutcome :=
  if input.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1 then
    .reverted (computed.add (second.add (Solcore.Core.Word.ofNatModulo 1))).val
  else
    .returned (computed.add (second.add (Solcore.Core.Word.ofNatModulo 1))).val
      ((storage.write 0 computed.val).write 1 (second.add (Solcore.Core.Word.ofNatModulo 1)).val)

/-- The method runs the storage protocol, binds the sum of both slots read
back, and reverts with it for an odd input or returns it otherwise. -/
theorem rollbackMethod_run (context : Context) (storage : Storage)
    (input first second computed : Solcore.Core.Word)
    (stepCall : context.call "sc_step" [.word (input.add first).val] =
      some (.word computed.val))
    (firstSlot : storage 0 = first.val) (secondSlot : storage 1 = second.val) :
    rollbackMethod.run context storage [input.val] =
      some (rollbackOutcome storage input second computed) := by
  have zero : 0 < Evm.modulus := by decide
  have thirtyTwo : 32 < Evm.modulus := by decide
  have one : (Solcore.Core.Word.ofNatModulo 1).val = 1 := ofNatModulo_val_small (by decide)
  have increment : Evm.add second.val 1 = (second.add (Solcore.Core.Word.ofNatModulo 1)).val := by
    have := evm_add second (Solcore.Core.Word.ofNatModulo 1)
    rwa [one] at this
  have stepCallBase : (context.withStorage storage).call "sc_step"
      [.word (input.add first).val] = some (.word computed.val) := by
    rw [Context.withStorage_call_other _ _ (by decide)]
    exact stepCall
  unfold rollbackOutcome
  cases flag : (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
      Solcore.Core.Word.ofNatModulo 1) <;>
    simp [RollbackMethod.run, rollbackMethod, rollbackBody, storageBody, Method.bindParameters,
      word_lt_modulus, RollbackStmt.execList, RollbackStmt.exec, StorageStmt.exec, Stmt.exec,
      Expr.eval, Operand.expr, Frames.lookup, Scope.get?, LocalType.admits, Frames.declare,
      BinaryOp.apply, Context.withStorage_call_sload, firstSlot, secondSlot, evm_add,
      stepCallBase, Storage.write, increment, rollback_flag, flag, one_lt_modulus, zero,
      thirtyTwo]

/-! ### The Core reference on the host machine -/

/-- The wrapper of `StorageRollback.canonicalProgram`, restated: the storage
protocol, the sum of both slots read back and the outcome by the input's low
bit. -/
def rollbackExpression (stepBody : Solcore.Core.Wire.Expr) : Solcore.Core.Wire.Expr :=
  .letE stepBody
    (.letE (.caseE (.apply (.var 9) (.word (Solcore.Core.Word.ofNatModulo 4)))
        (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0))
      (.letE (.apply (.var 2) (.word (Solcore.Core.Word.ofNatModulo 0)))
        (.letE (.apply (.var 3) (.word (Solcore.Core.Word.ofNatModulo 1)))
          (.letE (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1)))
            (.letE (.apply (.var 6) (.pair (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0)))
              (.letE (.apply (.var 7) (.pair (.word (Solcore.Core.Word.ofNatModulo 1))
                  (.binary .wordAdd (.var 2) (.word (Solcore.Core.Word.ofNatModulo 1)))))
                (.letE (.binary .wordAdd (.apply (.var 7) (.word (Solcore.Core.Word.ofNatModulo 0)))
                    (.apply (.var 7) (.word (Solcore.Core.Word.ofNatModulo 1))))
                  (.ifE (.binary .wordEq (.binary .wordAnd (.var 6)
                      (.word (Solcore.Core.Word.ofNatModulo 1)))
                      (.word (Solcore.Core.Word.ofNatModulo 1)))
                    (.inRight .word (.inLeft .word (.var 0)))
                    (.inLeft (.sum .word .word) (.var 0))))))))))

theorem rollbackProgram_body (step : Solcore.Synthesis.Core.Aggregates.CheckedDAG) :
    (Solcore.Synthesis.Core.StorageRollback.canonicalProgram step).body =
      rollbackExpression step.program.body :=
  rfl

/-- The outcome by the input's low bit, with the sum as payload. -/
def rollbackCompletion : Solcore.Core.Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 6) (.word (Solcore.Core.Word.ofNatModulo 1)))
      (.word (Solcore.Core.Word.ofNatModulo 1)))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

/-- The Core continuations of the rollback wrapper, from the sum back to the
input. -/
def rollbackTail7 : Solcore.Core.Expr :=
  .letE (.binary .wordAdd (.apply (.var 7) (.word (Solcore.Core.Word.ofNatModulo 0)))
    (.apply (.var 7) (.word (Solcore.Core.Word.ofNatModulo 1)))) rollbackCompletion

def rollbackTail6 : Solcore.Core.Expr :=
  .letE (.apply (.var 7) (.pair (.word (Solcore.Core.Word.ofNatModulo 1))
    (.binary .wordAdd (.var 2) (.word (Solcore.Core.Word.ofNatModulo 1))))) rollbackTail7

def rollbackTail5 : Solcore.Core.Expr :=
  .letE (.apply (.var 6) (.pair (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0)))
    rollbackTail6

def rollbackTail4 : Solcore.Core.Expr :=
  .letE (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1))) rollbackTail5

def rollbackTail3 : Solcore.Core.Expr :=
  .letE (.apply (.var 3) (.word (Solcore.Core.Word.ofNatModulo 1))) rollbackTail4

def rollbackTail2 : Solcore.Core.Expr :=
  .letE (.apply (.var 2) (.word (Solcore.Core.Word.ofNatModulo 0))) rollbackTail3

def rollbackTail1 : Solcore.Core.Expr :=
  .letE (.caseE (.apply (.var 9) (.word (Solcore.Core.Word.ofNatModulo 4)))
    (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0)) rollbackTail2

theorem rollbackExpression_toCore (stepBody : Solcore.Core.Wire.Expr) :
    (rollbackExpression stepBody).toCore = .letE stepBody.toCore rollbackTail1 := by
  simp only [rollbackExpression, Solcore.Core.Wire.Expr.toCore,
    Solcore.Core.Wire.BinaryOp.toCore, Solcore.Core.Wire.Ty.toCore, rollbackTail1, rollbackTail2,
    rollbackTail3, rollbackTail4, rollbackTail5, rollbackTail6, rollbackTail7,
    rollbackCompletion]

/-- The Core value of the outcome: the revert tag with the sum when `flag`
holds, the sum on the left otherwise. -/
def rollbackValue (flag : Bool) (sum : Solcore.Core.Word) : CoreValue :=
  if flag then .inRight .word (.inLeft .word (.word sum))
  else .inLeft (.sum .word .word) (.word sum)

theorem rollbackCompletion_evaluates {environment : Solcore.Core.Environment}
    {store : Solcore.Core.Store} {input sum : Solcore.Core.Word}
    (inputAt : environment[5]? = some (.word input)) :
    Solcore.Core.Evaluates (.word sum :: environment) store rollbackCompletion
      (rollbackValue (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
        Solcore.Core.Word.ofNatModulo 1) sum) store := by
  have condition : Solcore.Core.Evaluates (.word sum :: environment) store
      (.binary .wordEq (.binary .wordAnd (.var 6) (.word (Solcore.Core.Word.ofNatModulo 1)))
        (.word (Solcore.Core.Word.ofNatModulo 1)))
      (.bool (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
        Solcore.Core.Word.ofNatModulo 1)) store :=
    .binary (.binary (.var (by simpa using inputAt)) .word rfl) .word rfl
  unfold rollbackValue
  cases flag : (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
      Solcore.Core.Word.ofNatModulo 1)
  · rw [flag] at condition
    exact .ifFalse condition (.inLeft (.var rfl))
  · rw [flag] at condition
    exact .ifTrue condition (.inRight (.inLeft (.var rfl)))

theorem handledSteps_core {HostContext : Type} {handler : HostHandler HostContext}
    {context : HostContext} {start finish : Solcore.Core.State}
    (path : ∃ steps, Solcore.Core.HostSteps steps start finish) :
    ∃ steps, HostDriver.HandledSteps handler steps context start context finish := by
  obtain ⟨_, path⟩ := path
  exact ⟨_, .core path⟩

/-- **The rollback reference's transaction, as a handled host path.** From the
initial state, the wrapper runs the storage protocol and ends with the outcome
value of the sum of both slots read back. -/
theorem rollback_handled {inputs : HostStorageDriver.ExecutionInputs}
    {context : TransactionHostStorageDriver.Context} {step : Solcore.Core.Expr}
    {closure : CoreValue} {input computed : Solcore.Core.Word} {store : Solcore.Core.Store}
    (stepEvaluates : Solcore.Core.Evaluates Solcore.Core.hostEnvironment [] step closure [])
    (decoded : inputs.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 4) = some input)
    (applied : Solcore.Core.Evaluates
      (.word (context.readStorage (Solcore.Core.Word.ofNatModulo 1)) ::
        .word (context.readStorage (Solcore.Core.Word.ofNatModulo 0)) ::
        .word input :: closure :: Solcore.Core.hostEnvironment) []
      (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1))) (.word computed) store) :
    ∃ steps, HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
      (Solcore.Core.State.initial (.letE step rollbackTail1) Solcore.Core.hostEnvironment)
      ((context.writeStorage (Solcore.Core.Word.ofNatModulo 0) computed).writeStorage
        (Solcore.Core.Word.ofNatModulo 1)
        ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
          (Solcore.Core.Word.ofNatModulo 1)))
      (Solcore.Core.State.final (rollbackValue
        (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1)
        (computed.add ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
          (Solcore.Core.Word.ofNatModulo 1)))) store) := by
  let environment1 : Solcore.Core.Environment := closure :: Solcore.Core.hostEnvironment
  let environment2 : Solcore.Core.Environment := .word input :: environment1
  let environment3 : Solcore.Core.Environment :=
    .word (context.readStorage (Solcore.Core.Word.ofNatModulo 0)) :: environment2
  let environment5 : Solcore.Core.Environment := .word computed ::
    .word (context.readStorage (Solcore.Core.Word.ofNatModulo 1)) :: environment3
  let environment6 : Solcore.Core.Environment := .unit :: environment5
  let environment7 : Solcore.Core.Environment := .unit :: environment6
  let written : TransactionHostStorageDriver.Context :=
    context.writeStorage (Solcore.Core.Word.ofNatModulo 0) computed
  let final : TransactionHostStorageDriver.Context :=
    written.writeStorage (Solcore.Core.Word.ofNatModulo 1)
      ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
        (Solcore.Core.Word.ofNatModulo 1))
  let outcome : Solcore.Core.State := Solcore.Core.State.final (rollbackValue
    (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1)
    (computed.add ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
      (Solcore.Core.Word.ofNatModulo 1)))) store
  have firstRead : final.readStorage (Solcore.Core.Word.ofNatModulo 0) = computed := by
    simp only [final, written]
    rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_other _ _ _ _
      (by decide), FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same]
  have secondRead : final.readStorage (Solcore.Core.Word.ofNatModulo 1) =
      (context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add
        (Solcore.Core.Word.ofNatModulo 1) := by
    simp only [final]
    rw [FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same]
  have finish : ∃ steps, HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs)
      steps final ⟨.ret (.word (final.readStorage (Solcore.Core.Word.ofNatModulo 1))),
        [.binaryApply .wordAdd (.word (final.readStorage (Solcore.Core.Word.ofNatModulo 0))),
          .letBody rollbackCompletion environment7], store⟩ final outcome := by
    rw [firstRead, secondRead]
    exact handledSteps_core (hostSteps_cons (.applyBinary rfl) (hostSteps_cons .bindLet
      (hostSteps_eval (rollbackCompletion_evaluates rfl) ⟨0, .refl⟩)))
  have secondFinal : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps final
        ⟨.ret (.word (final.readStorage (Solcore.Core.Word.ofNatModulo 0))),
          [.binaryRight .wordAdd (.apply (.var 7) (.word (Solcore.Core.Word.ofNatModulo 1)))
            environment7, .letBody rollbackCompletion environment7], store⟩ final outcome :=
    handledSteps_request (hostSteps_cons .enterBinaryRight
      (hostSteps_apply (index := 7) rfl .word)) .storageRead rfl rfl finish
  have firstFinal : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps final
        ⟨.ret .unit, [.letBody rollbackTail7 environment6], store⟩ final outcome :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_cons .enterBinary (hostSteps_apply (index := 7) rfl .word)))) .storageRead rfl
      rfl secondFinal
  have secondWrite : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps written
        ⟨.ret .unit, [.letBody rollbackTail6 environment5], store⟩ final outcome :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_apply (index := 7) rfl (.pair .word (.binary (.var rfl) .word rfl)))))
      .storageWrite rfl rfl firstFinal
  have firstWrite : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.word (context.readStorage (Solcore.Core.Word.ofNatModulo 1))),
          [.letBody rollbackTail4 environment3], []⟩ final outcome :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_eval applied (hostSteps_cons .bindLet (hostSteps_cons .enterLet
        (hostSteps_apply (index := 6) rfl (.pair .word (.var rfl))))))))
      .storageWrite rfl rfl secondWrite
  have secondLoad : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.word (context.readStorage (Solcore.Core.Word.ofNatModulo 0))),
          [.letBody rollbackTail3 environment2], []⟩ final outcome :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_apply (index := 3) rfl .word))) .storageRead rfl rfl firstWrite
  have firstLoad : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.inRight .unit (.word input)),
          [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment1,
            .letBody rollbackTail2 environment1], []⟩ final outcome :=
    handledSteps_request (hostSteps_cons .chooseRight (hostSteps_cons (.var rfl)
      (hostSteps_cons .bindLet (hostSteps_cons .enterLet
        (hostSteps_apply (index := 2) rfl .word))))) .storageRead rfl rfl secondLoad
  have resumed : (TransactionHostStorageDriver.handler inputs).handleSuspension context
      ⟨.inputDataWordBE? (Solcore.Core.Word.ofNatModulo 4),
        [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment1,
          .letBody rollbackTail2 environment1], []⟩ =
      (context, ⟨.ret (.inRight .unit (.word input)),
        [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment1,
          .letBody rollbackTail2 environment1], []⟩) := by
    rw [handleSuspension_inputDataWordBE, decoded]
    rfl
  exact handledSteps_request (hostSteps_cons .enterLet (hostSteps_eval stepEvaluates
    (hostSteps_cons .bindLet (hostSteps_cons .enterLet (hostSteps_cons .enterCase
      (hostSteps_apply (index := 9) rfl .word)))))) .inputDataWordBE? rfl resumed firstLoad

/-! ### One top-level transaction -/

/-- A raw run that returns a value completes the top-level transaction with the
contract's decoding of that value: a returned outcome commits the working
world, a reverted one the world the transaction started from. -/
theorem topLevel_run_settled {initialWorld : WorldState} (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed : InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) (context : TransactionHostStorageDriver.Context) (value : CoreValue)
    (store : Solcore.Core.Store) (outcome : FrameOutcome Solcore.Core.Word)
    (raw : TopLevelExecution.rawRun contract invocation installed fuel =
      ⟨context, .done value store⟩)
    (decoded : contract.decodeCompletion? value = some outcome) :
    ∃ result, TopLevelExecution.run contract invocation installed fuel = .completed result ∧
      result.outcome = outcome ∧
      (∀ data, outcome = .returned data →
        result.finalWorld = context.context.values.working.1) ∧
      (∀ data, outcome = .reverted data → result.finalWorld = initialWorld) := by
  have resultEq : (TopLevelExecution.validatedRawRun contract invocation installed fuel).result =
      TopLevelExecution.rawRun contract invocation installed fuel := rfl
  unfold TopLevelExecution.run TopLevelExecution.classifyRawResult
  split
  · rename_i value' store' outcomeEq
    rw [resultEq, raw] at outcomeEq
    cases outcomeEq
    split
    · rename_i outcome' decodedEq
      rw [decoded] at decodedEq
      cases decodedEq
      refine ⟨_, rfl, by simp, ?_, ?_⟩
      · intro data same
        subst same
        simp only [TopLevelExecution.finalWorld_finalize_returned]
        rw [resultEq, raw]
      · intro data same
        subst same
        simp only [TopLevelExecution.finalWorld_finalize_reverted]
    · rename_i decodedEq
      rw [decoded] at decodedEq
      cases decodedEq
  all_goals
    rename_i outcomeEq
    rw [resultEq, raw] at outcomeEq
    cases outcomeEq

/-- **The observation of one transaction with a rollback.** With enough fuel,
the top-level transaction of the installed contract completes. Every completed
run settles as the source outcome: it returns the ABI encoding of the returned
word and commits a world whose target account holds the returned storage, or
it reverts with the 32-byte encoding of the reverted word and commits the
world the transaction started from. -/
def CoreSettles {world : WorldState} (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed : InstalledCheckedCoreContract world invocation.target contract)
    (outcome : RollbackOutcome) : Prop :=
  (∃ enough, ∀ fuel, enough ≤ fuel →
    ∃ result, TopLevelExecution.run contract invocation installed fuel = .completed result) ∧
  ∀ fuel result, TopLevelExecution.run contract invocation installed fuel = .completed result →
    match outcome with
    | .returned value storage =>
        ∃ word : Solcore.Core.Word, word.val = value ∧
          result.outcome = .returned (encodeWordBytesBE word) ∧
          ∃ account, result.finalWorld.account? invocation.target = some account ∧
            StorageAgrees account storage
    | .reverted data =>
        ∃ word : Solcore.Core.Word, word.val = data ∧
          result.outcome = .reverted (encodeWordBytesBE word) ∧ result.finalWorld = world

/-! ### Preservation -/

/-- **Storage rollback emitter preservation.** If the actual emitter succeeds,
its source text is the printing of a rollback file with one free function per
helper and the step function `sc_step`, importing `sload`, `sstore`, `mstore`,
`revert_` and the raw opcode aliases exactly when a rendered body uses one,
and parses back to it. For every world in which the contract is installed and
every calldata whose word at offset 4 is `input`, calling `run(uint256)` from
the installed account's storage under the rollback source semantics reverts
exactly when the input is odd, and the original Core contract's top-level
transaction settles as that outcome. -/
theorem StorageRollback.emit_preserves_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : StorageRollback.emit plan = .ok emitted) :
    ∃ file : RollbackFile, emitted.source = file.print ∧
      parseRollbackSource emitted.source = some file ∧
      ∀ {world : WorldState} {invocation : TopLevelInvocation}
        (installed : InstalledCheckedCoreContract world invocation.target plan.contract)
        {input : Solcore.Core.Word},
        invocation.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 4) = some input →
        ∃ outcome : RollbackOutcome,
          file.call (accountStorage installed.account) "run" [input.val] = some outcome ∧
          ((∃ data, outcome = .reverted data) ↔ input.val % 2 = 1) ∧
          CoreSettles plan.contract invocation installed outcome := by
  obtain ⟨names, lines, entry, result, loop, entryEquation, resultFound, source⟩ :=
    StorageRollback.emit_success emitted_eq
  let bodies := plan.step.helpers ++ [plan.step.entry]
  let uses := bodies.any AggregateRenderer.usesOpcodeAliases
  have aliasesOk : uses = true → aggregateAliases bodies = primitiveAliases := by
    intro used
    simp only [aggregateAliases]
    rw [if_pos used]
  have bodyUses : ∀ body ∈ bodies, AggregateRenderer.usesOpcodeAliases body = true →
      uses = true := fun body mem used => List.any_eq_true.mpr ⟨body, mem, used⟩
  have startPrimitive : uses = true → PrimitiveContext ⟨[], aggregateAliases bodies⟩ := by
    intro used
    rw [aliasesOk used]
    exact primitiveContext_aliases
  obtain ⟨declarations, linesEq, namesEq, declarationsOk, primitive, agree⟩ :=
    aggregateLoop_spec aliasesOk plan.step.helpers 0 _ names lines [] Solcore.Core.hostEnvironment
      loop
      (fun index body found =>
        ⟨aggregate_helpers_accepted plan.step.helperScopes index body found,
          bodyUses body (List.mem_append_left _ (List.mem_of_getElem? found))⟩)
      startPrimitive (fun _ _ found => by simp [helperNames] at found)
  have entryKind : initializerKind? ([Binding.word "sc_arg"].map Binding.kind) names.length
      plan.step.entry = some Local.word := by
    rw [namesEq, helperNames_length, Nat.zero_add]
    exact aggregate_acceptsAt_kind plan.step.entryScope
  obtain ⟨statements, entryLines, _, valueName, entryNames, simulates⟩ :=
    (aggregate_render_spec plan.step.entry).1
      (fun context => uses = true → PrimitiveContext context)
      (fun context admitted used =>
        admitted (bodyUses plan.step.entry (List.mem_append_right _ (by simp)) used))
      names .word [.word "sc_arg"] 4 0 entry entryKind entryEquation
      (single_abinding_fresh argument_not_temporary cellTemp_ne_argument
        payloadTemp_ne_argument)
      (single_abinding_distinct _)
  let file := rollbackFile (aggregateAliases bodies) declarations statements result
  have argumentOk : ∀ index found, anameAt [Binding.word "sc_arg"] index = some found →
      ValidIdentifier found ∧ isReserved found = false :=
    single_abinding_ok (keyword_valid (by decide)) (by decide)
  have functionNamesOk : ∀ name ∈ names, ValidIdentifier name ∧ isReserved name = false := by
    rw [namesEq]
    exact helperNames_ok
  have valueOk := aggregate_identifier_ok argumentOk functionNamesOk
    (valueName result resultFound).uses
  have stepOk : (stepDecl statements result).NamesOk ∧
      ∀ name ∈ (stepDecl statements result).identifiers, ValidIdentifier name := by
    have bodyOk := fun name mem =>
      aggregate_identifier_ok argumentOk functionNamesOk (entryNames name mem)
    refine ⟨⟨show isReserved "sc_step" = false by decide, ?_,
      fun name mem => (bodyOk name mem).2, ?_⟩, ?_⟩
    · intro parameter mem
      simp only [stepDecl, List.mem_singleton] at mem
      subst mem
      decide
    · intro name mem
      simp only [stepDecl, Expr.identifiers, List.mem_singleton] at mem
      subst mem
      exact valueOk.2
    · intro name mem
      simp only [stepDecl, FunctionDecl.identifiers, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.mem_append, Expr.identifiers,
        List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | mem | rfl
      · exact keyword_valid (by decide)
      · exact keyword_valid (by decide)
      · exact (bodyOk name mem).1
      · exact valueOk.1
  have functionsOk : ∀ function ∈ file.functions, function.NamesOk ∧
      ∀ name ∈ function.identifiers, ValidIdentifier name := by
    intro function mem
    rcases List.mem_append.mp mem with mem | mem
    · exact declarationsOk function mem
    · simp only [List.mem_singleton] at mem
      subst mem
      exact stepOk
  have printed : emitted.source = file.print := by
    have stepLines : (stepDecl statements result).lines =
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
          ["    return " ++ result ++ ";", "}", ""] := by
      simp only [stepDecl, FunctionDecl.lines, entryLines, List.cons_append, List.nil_append,
        List.cons.injEq]
      refine ⟨?_, ?_⟩
      · apply String.toList_inj.mp
        simp [FunctionDecl.parameterText, LocalType.spelling]
      · simp [Expr.print]
    have functionLine : "    function " ++ StorageRollback.methodName ++
        "(input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply String.toList_inj.mp
      simp [file, rollbackFile, rollbackMethod, Method.parameterText, StorageRollback.methodName]
    rw [source, RollbackFile.print, RollbackFile.lines, linesEq, functionLine]
    simp [file, rollbackFile, StorageRollback.contractName, stepLines, bodies,
      rollbackMethod_lines]
  have bodyNames := rollbackBody_names_ok
  have parsed : parseRollbackSource emitted.source = some file := by
    rw [printed]
    apply parseRollbackSource_print
    · refine ⟨fun function mem => (functionsOk function mem).1, rfl, rfl, ?_,
        fun name mem => (bodyNames name (List.mem_append_left _ mem)).2,
        fun name mem => (bodyNames name (List.mem_append_right _ mem)).2⟩
      intro parameter mem
      simp only [file, rollbackFile, rollbackMethod, List.mem_singleton] at mem
      subst mem
      decide
    · refine ⟨aggregateAliases_valid bodies, fun function mem => (functionsOk function mem).2,
        keyword_valid (show validIdentifier "SynthesizedRollback" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (bodyNames name (List.mem_append_left _ mem)).1,
        fun name mem => (bodyNames name (List.mem_append_right _ mem)).1⟩
      intro parameter mem
      simp only [file, rollbackFile, rollbackMethod, List.mem_singleton] at mem
      subst mem
      exact keyword_valid (by decide)
  refine ⟨file, printed, parsed, ?_⟩
  intro world invocation installed input calldata
  have stepCall : ∀ arguments, file.context.call "sc_step" arguments =
      (stepDecl statements result).denote
        ⟨declareFunctions (aggregateAliases bodies) [] declarations, aggregateAliases bodies⟩
        arguments := by
    intro arguments
    show Context.call ⟨declareFunctions (aggregateAliases bodies) []
      (declarations ++ [stepDecl statements result]), aggregateAliases bodies⟩ "sc_step"
        arguments = _
    rw [declareFunctions_append_single]
    exact Context.call_cons_same _ _ _ _ _
  let first := installed.account.storageRead (Solcore.Core.Word.ofNatModulo 0)
  let second := installed.account.storageRead (Solcore.Core.Word.ofNatModulo 1)
  obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _, _, _⟩ :=
    simulates ⟨declareFunctions (aggregateAliases bodies) [] declarations,
        aggregateAliases bodies⟩
      (.word (input.add first) :: plan.step.helpers.foldl closureStep Solcore.Core.hostEnvironment)
      [] [] [[("sc_arg", .word (input.add first).val)]] primitive
      (single_abinding_agree (by simp [Frames.lookup, Scope.get?]) _ [])
      (single_abinding_cells _ _ _) (by simp) (by simpa using agree)
  rw [resultFound, Option.bind_some] at represents
  obtain ⟨_, lookup, computed, rfl, rfl⟩ := represents
  have sourceStep : file.context.call "sc_step" [.word (input.add first).val] =
      some (.word computed.val) := by
    rw [stepCall]
    simp [stepDecl, FunctionDecl.denote, FunctionDecl.bindParameters, LocalType.admits, exec,
      Expr.eval, lookup]
  let sum := computed.add (second.add (Solcore.Core.Word.ofNatModulo 1))
  refine ⟨rollbackOutcome (accountStorage installed.account) input second computed, ?_, ?_, ?_⟩
  · show (if file.method.name = "run" then file.method.run file.context
      (accountStorage installed.account) [input.val] else none) = _
    rw [if_pos (show file.method.name = "run" from rfl)]
    exact rollbackMethod_run file.context _ input first second computed sourceStep rfl rfl
  · unfold rollbackOutcome
    rw [rollback_parity]
    by_cases odd : input.val % 2 = 1 <;> simp [odd]
  · let context := TopLevelExecution.initialTransactionContext installed
    have stepEvaluates := dag_evaluates plan.step.entry plan.step.helpers
      Solcore.Core.hostEnvironment []
    have applied : Solcore.Core.Evaluates
        (.word (context.readStorage (Solcore.Core.Word.ofNatModulo 1)) ::
          .word (context.readStorage (Solcore.Core.Word.ofNatModulo 0)) ::
          .word input :: .closure (Solcore.Core.Wire.Ty.toCore .word)
            (Solcore.Core.Wire.Ty.toCore .word) plan.step.entry.toCore
            (plan.step.helpers.foldl closureStep Solcore.Core.hostEnvironment) ::
          Solcore.Core.hostEnvironment) []
        (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1))) (.word computed) store' :=
      .apply (.var rfl) (.binary (.var rfl) (.var rfl) rfl) evaluates
    obtain ⟨spent, path⟩ := rollback_handled (inputs := invocation.executionInputs)
      (context := context) stepEvaluates calldata applied
    have body : plan.contract.code.program.body =
        .letE (Solcore.Synthesis.Core.functionDAGExpression plan.step.helpers
          plan.step.entry).toCore rollbackTail1 := by
      show (rollbackExpression plan.step.program.body).toCore = _
      rw [rollbackExpression_toCore]
      rfl
    let final : TransactionHostStorageDriver.Context :=
      (context.writeStorage (Solcore.Core.Word.ofNatModulo 0) computed).writeStorage
        (Solcore.Core.Word.ofNatModulo 1) (second.add (Solcore.Core.Word.ofNatModulo 1))
    have raw : ∀ fuel, spent ≤ fuel →
        TopLevelExecution.rawRun plan.contract invocation installed fuel =
          ⟨final, .done (rollbackValue (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
            Solcore.Core.Word.ofNatModulo 1) sum) store'⟩ := by
      intro fuel enough
      show HostDriver.run (TransactionHostStorageDriver.handler invocation.executionInputs)
        context fuel (Solcore.Core.State.initial plan.contract.code.program.body
          Solcore.Core.hostEnvironment) = _
      rw [body]
      exact HostDriver.run_done_complete _ path enough
    have address : final.context.storageAddress = invocation.target := by
      simp [final, context]
    have account : final.storageAccount =
        (installed.account.storageWrite (Solcore.Core.Word.ofNatModulo 0) computed).storageWrite
          (Solcore.Core.Word.ofNatModulo 1) (second.add (Solcore.Core.Word.ofNatModulo 1)) := by
      simp [final, context]
    have settled : ∀ fuel, spent ≤ fuel → ∃ result,
        TopLevelExecution.run plan.contract invocation installed fuel = .completed result ∧
        match rollbackOutcome (accountStorage installed.account) input second computed with
        | .returned value storage =>
            ∃ word : Solcore.Core.Word, word.val = value ∧
              result.outcome = .returned (encodeWordBytesBE word) ∧
              ∃ account, result.finalWorld.account? invocation.target = some account ∧
                StorageAgrees account storage
        | .reverted data =>
            ∃ word : Solcore.Core.Word, word.val = data ∧
              result.outcome = .reverted (encodeWordBytesBE word) ∧ result.finalWorld = world := by
      intro fuel enough
      unfold rollbackOutcome
      cases flag : (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
          Solcore.Core.Word.ofNatModulo 1)
      · have rawFlag := raw fuel enough
        rw [flag] at rawFlag
        obtain ⟨result, run, outcome, finalWorld, _⟩ := topLevel_run_settled plan.contract
          invocation installed fuel _ _ _ _ rawFlag rfl
        refine ⟨result, run, sum, rfl, outcome, final.storageAccount, ?_, ?_⟩
        · rw [finalWorld _ rfl, ← address]
          exact final.storageAccount_present
        · rw [account]
          exact storageAgrees_writes installed.account computed _
      · have rawFlag := raw fuel enough
        rw [flag] at rawFlag
        obtain ⟨result, run, outcome, _, finalWorld⟩ := topLevel_run_settled plan.contract
          invocation installed fuel _ _ _ _ rawFlag rfl
        exact ⟨result, run, sum, rfl, outcome, finalWorld _ rfl⟩
    refine ⟨⟨spent, fun fuel enough => (settled fuel enough).elim fun result facts =>
      ⟨result, facts.1⟩⟩, ?_⟩
    intro fuel result run
    obtain ⟨result', run', facts⟩ := settled (fuel + spent) (by omega)
    have resumed := TopLevelExecution.resumeWithFuel_run plan.contract invocation installed fuel
      spent
    rw [run, TopLevelExecution.resumeWithFuel_completed, run'] at resumed
    cases resumed
    exact facts

/-- **Storage rollback emitter preservation, on the emitted text.** Read as a
rollback program, the emitted text called from the installed account's storage
reverts exactly when the input is odd. The original Core contract's
transaction settles as that outcome: it returns the same word and commits the
same storage, or reverts with the same word and leaves the world unchanged. -/
theorem StorageRollback.emit_source_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : StorageRollback.emit plan = .ok emitted)
    {world : WorldState} {invocation : TopLevelInvocation}
    (installed : InstalledCheckedCoreContract world invocation.target plan.contract)
    {input : Solcore.Core.Word}
    (calldata : invocation.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 4) = some input) :
    ∃ outcome : RollbackOutcome,
      rollbackSourceCall emitted.source (accountStorage installed.account) "run" [input.val] =
        some outcome ∧
      ((∃ data, outcome = .reverted data) ↔ input.val % 2 = 1) ∧
      CoreSettles plan.contract invocation installed outcome := by
  obtain ⟨file, _, parsed, meaning⟩ := StorageRollback.emit_preserves_meaning emitted_eq
  obtain ⟨outcome, call, parity, settles⟩ := meaning installed calldata
  exact ⟨outcome, by simp [rollbackSourceCall, parsed, call], parity, settles⟩

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.KeyedEmitter
/-! Meaning preservation for the actual keyed-storage emitter
(`KeyedStorage.emit`, profile `stateful-keyed-storage`). The method takes a key
and an input. It reads the key slot and counter slot zero, stores the step's
result for the input plus the old key slot in the key slot, the old key slot in
its wrapping successor and the counter plus one in slot zero, in that order. It
then reads the three slots back, binds their sum, and reverts with it for an
odd input or returns it otherwise. Keys zero and `2^256 - 1` alias the counter;
the later write wins, in the source as in Core.

The Core reference is a host-runtime contract with the three-way Word outcome
profile. It reads the key and the input from calldata at offsets 4 and 36 and
runs the same storage requests in the same order. One top-level transaction
runs it on a world in which it is installed. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core.KeyedStorage (CheckedPlan)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind?)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)
open Solcore.ContractRuntime

/-! ### The emitted text -/

theorem KeyedStorage.emit_success {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : KeyedStorage.emit plan = .ok emitted) :
    ∃ (names lines : List String) (entry : ARendered) (result : String),
      aggregateLoop plan.step.helpers 0 []
        ["import * from std;", "import * from std.dispatch;",
          rollbackImportLine (aggregateAliases (plan.step.helpers ++ [plan.step.entry])), ""] =
        .ok (names, lines) ∧
      AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry = .ok entry ∧
      entry.value = some result ∧
      emitted.source = String.intercalate "\n" (lines ++
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
        ["    return " ++ result ++ ";", "}", "",
          "contract " ++ KeyedStorage.contractName ++ " {",
          "    function " ++ KeyedStorage.methodName ++
            "(key: uint256, input: uint256) public returns (uint256) {",
          "        let sc_key: word = Typedef.rep(key);",
          "        let sc_input: word = Typedef.rep(input);",
          "        let sc_old: word = sload(sc_key);",
          "        let sc_count: word = sload(0);",
          "        let sc_computed: word = sc_step(sc_input + sc_old);",
          "        sstore(sc_key, sc_computed);",
          "        sstore(sc_key + 1, sc_old);",
          "        sstore(0, sc_count + 1);",
          "        let sc_final_key: word = sload(sc_key);",
          "        let sc_final_next: word = sload(sc_key + 1);",
          "        let sc_final_count: word = sload(0);",
          "        let sc_result: word = sc_final_key + sc_final_next + sc_final_count;",
          "        if ((sc_input & 1) == 1) {",
          "            mstore(0, sc_result);",
          "            revert_(0, 32);",
          "        }",
          "        return uint256(sc_result);", "    }", "}"]) ++ "\n" := by
  unfold KeyedStorage.emit at emitted_eq
  dsimp only at emitted_eq
  rw [forIn_aggregateLoop (fun _ _ _ _ => rfl), rollbackImport_eq] at emitted_eq
  cases loop : aggregateLoop plan.step.helpers 0 []
    ["import * from std;", "import * from std.dispatch;",
      rollbackImportLine (aggregateAliases (plan.step.helpers ++ [plan.step.entry])), ""] with
  | error error =>
      rw [loop] at emitted_eq
      cases emitted_eq
  | ok loopResult =>
      obtain ⟨names, lines⟩ := loopResult
      rw [loop] at emitted_eq
      cases entry : AggregateRenderer.render names .word [.word "sc_arg"] 4 0
        plan.step.entry with
      | error error =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases emitted_eq
      | ok rendered =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases value : AggregateRenderer.requireValue rendered with
          | error error =>
              simp only [value] at emitted_eq
              cases emitted_eq
          | ok result =>
              simp only [value, pure, Except.pure, Except.ok.injEq] at emitted_eq
              subst emitted_eq
              exact ⟨names, lines, rendered, result, rfl, entry, arequireValue_ok value, rfl⟩

/-- The method body the keyed-storage emitter prints. -/
def keyedBody : List KeyedStmt :=
  [.rollback (.storage (.plain (.letDecl "sc_key" .word (.typedefRep (.name "key"))))),
    .rollback (.storage (.plain (.letDecl "sc_input" .word (.typedefRep (.name "input"))))),
    .rollback (.storage (.plain (.letDecl "sc_old" .word (.call1 "sload" (.name "sc_key"))))),
    .rollback (.storage (.plain (.letDecl "sc_count" .word (.call1 "sload" (.number 0))))),
    .rollback (.storage (.letCall "sc_computed" .word "sc_step" .add (.name "sc_input")
      (.name "sc_old"))),
    .rollback (.storage (.store (.plain (.name "sc_key")) (.plain (.name "sc_computed")))),
    .rollback (.storage (.store (.operation .add (.name "sc_key") (.number 1))
      (.plain (.name "sc_old")))),
    .rollback (.storage (.store (.plain (.number 0))
      (.operation .add (.name "sc_count") (.number 1)))),
    .rollback (.storage (.plain (.letDecl "sc_final_key" .word
      (.call1 "sload" (.name "sc_key"))))),
    .rollback (.storage (.letCall "sc_final_next" .word "sload" .add (.name "sc_key")
      (.number 1))),
    .rollback (.storage (.plain (.letDecl "sc_final_count" .word
      (.call1 "sload" (.number 0))))),
    .letSum "sc_result" .word (.name "sc_final_key") (.name "sc_final_next")
      (.name "sc_final_count"),
    .rollback (.revertIf .eq (.binary .bitAnd (.name "sc_input") (.number 1)) (.number 1)
      (.plain (.number 0)) (.plain (.name "sc_result")) (.plain (.number 0))
      (.plain (.number 32)))]

/-- The method the keyed-storage emitter prints. -/
def keyedMethod : KeyedMethod where
  name := "run"
  parameters := ["key", "input"]
  body := keyedBody
  result := .plain (.name "sc_result")

/-- The keyed file printed by the keyed-storage emitter. -/
def keyedFile (aliases : List (String × String)) (declarations : List FunctionDecl)
    (statements : List Stmt) (value : String) : KeyedFile where
  opcodeAliases := aliases
  functions := declarations ++ [stepDecl statements value]
  contract := "SynthesizedKeyedStorage"
  method := keyedMethod

theorem keyedMethod_lines (rest : List String) :
    KeyedStmt.listLines 8 keyedMethod.body ++
      ("        return uint256(" ++ keyedMethod.result.print ++ ");") :: rest =
    "        let sc_key: word = Typedef.rep(key);" ::
      "        let sc_input: word = Typedef.rep(input);" ::
      "        let sc_old: word = sload(sc_key);" ::
      "        let sc_count: word = sload(0);" ::
      "        let sc_computed: word = sc_step(sc_input + sc_old);" ::
      "        sstore(sc_key, sc_computed);" ::
      "        sstore(sc_key + 1, sc_old);" ::
      "        sstore(0, sc_count + 1);" ::
      "        let sc_final_key: word = sload(sc_key);" ::
      "        let sc_final_next: word = sload(sc_key + 1);" ::
      "        let sc_final_count: word = sload(0);" ::
      "        let sc_result: word = sc_final_key + sc_final_next + sc_final_count;" ::
      "        if ((sc_input & 1) == 1) {" ::
      "            mstore(0, sc_result);" ::
      "            revert_(0, 32);" ::
      "        }" ::
      "        return uint256(sc_result);" :: rest := by
  apply lines_eq_of_chars
  simp [keyedMethod, keyedBody, KeyedStmt.listLines, KeyedStmt.lines, RollbackStmt.lines,
    StorageStmt.lines, Stmt.lines, indentLine, Expr.print, Operand.print, LocalType.spelling,
    BinaryOp.spelling, digits_one, digits_thirtyTwo]

theorem keyedBody_names_ok :
    ∀ name ∈ KeyedStmt.listIdentifiers keyedMethod.body ++ keyedMethod.result.identifiers,
      ValidIdentifier name ∧ isReserved name = false := by
  have checked : ∀ name ∈ ["sc_key", "key", "sc_input", "input", "sc_old", "sload", "sc_count",
      "sc_computed", "sc_step", "sc_final_key", "sc_final_next", "sc_final_count", "sc_result"],
      validIdentifier name = true ∧ isReserved name = false := by
    decide
  have within : ∀ name ∈ KeyedStmt.listIdentifiers keyedMethod.body ++
      keyedMethod.result.identifiers,
      name ∈ ["sc_key", "key", "sc_input", "input", "sc_old", "sload", "sc_count",
        "sc_computed", "sc_step", "sc_final_key", "sc_final_next", "sc_final_count",
        "sc_result"] := by
    simp [keyedMethod, keyedBody, KeyedStmt.listIdentifiers, KeyedStmt.identifiers,
      RollbackStmt.identifiers, StorageStmt.identifiers, Operand.identifiers, Stmt.identifiers,
      Expr.identifiers]
  intro name mem
  have found := within name mem
  exact ⟨keyword_valid (checked name found).1, (checked name found).2⟩

/-! ### The source method -/

/-- The source storage after the three writes, in the order key, successor,
counter. -/
def keyedStorage (storage : Storage) (key old count computed : Solcore.Core.Word) : Storage :=
  ((storage.write key.val computed.val).write (key.add (Solcore.Core.Word.ofNatModulo 1)).val
    old.val).write 0 (count.add (Solcore.Core.Word.ofNatModulo 1)).val

/-- The sum of the key slot, its successor and the counter slot. -/
def keyedSum (storage : Storage) (key : Solcore.Core.Word) : Nat :=
  Evm.add (Evm.add (storage key.val) (storage (key.add (Solcore.Core.Word.ofNatModulo 1)).val))
    (storage 0)

/-- The outcome the keyed method gives: the sum of the three slots read back,
reverted for an odd input and returned with the written storage otherwise. -/
def keyedOutcome (storage : Storage) (key input old count computed : Solcore.Core.Word) :
    RollbackOutcome :=
  if input.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1 then
    .reverted (keyedSum (keyedStorage storage key old count computed) key)
  else
    .returned (keyedSum (keyedStorage storage key old count computed) key)
      (keyedStorage storage key old count computed)

/-- The method reads the key slot and the counter, writes the three slots,
reads them back and reverts with or returns their sum. -/
theorem keyedMethod_run (context : Context) (storage : Storage)
    (key input old count computed : Solcore.Core.Word)
    (stepCall : context.call "sc_step" [.word (input.add old).val] =
      some (.word computed.val))
    (oldSlot : storage key.val = old.val) (countSlot : storage 0 = count.val) :
    keyedMethod.run context storage [key.val, input.val] =
      some (keyedOutcome storage key input old count computed) := by
  have zero : 0 < Evm.modulus := by decide
  have thirtyTwo : 32 < Evm.modulus := by decide
  have one : (Solcore.Core.Word.ofNatModulo 1).val = 1 := ofNatModulo_val_small (by decide)
  have successor : Evm.add key.val 1 = (key.add (Solcore.Core.Word.ofNatModulo 1)).val := by
    have := evm_add key (Solcore.Core.Word.ofNatModulo 1)
    rwa [one] at this
  have increment : Evm.add count.val 1 = (count.add (Solcore.Core.Word.ofNatModulo 1)).val := by
    have := evm_add count (Solcore.Core.Word.ofNatModulo 1)
    rwa [one] at this
  have stepCallBase : (context.withStorage storage).call "sc_step"
      [.word (input.add old).val] = some (.word computed.val) := by
    rw [Context.withStorage_call_other _ _ (by decide)]
    exact stepCall
  unfold keyedOutcome keyedSum keyedStorage
  cases flag : (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
      Solcore.Core.Word.ofNatModulo 1) <;>
    simp [KeyedMethod.run, keyedMethod, keyedBody, Method.bindParameters, word_lt_modulus,
      KeyedStmt.execList, KeyedStmt.exec, RollbackStmt.exec, StorageStmt.exec, Stmt.exec,
      Expr.eval, Operand.expr, Frames.lookup, Scope.get?, LocalType.admits, Frames.declare,
      BinaryOp.apply, Context.withStorage_call_sload, oldSlot, countSlot, evm_add, stepCallBase,
      successor, increment, rollback_flag, flag, one_lt_modulus, zero, thirtyTwo]

/-! ### The Core reference on the host machine -/

/-- The wrapper of `KeyedStorage.canonicalProgram`, restated: the key and the
input, both reads, the step's result, the three writes, the three reads back,
their sum and the outcome by the input's low bit. -/
def keyedExpression (stepBody : Solcore.Core.Wire.Expr) : Solcore.Core.Wire.Expr :=
  .letE stepBody
    (.letE (.caseE (.apply (.var 9) (.word (Solcore.Core.Word.ofNatModulo 4)))
        (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0))
      (.letE (.caseE (.apply (.var 10) (.word (Solcore.Core.Word.ofNatModulo 36)))
          (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0))
        (.letE (.apply (.var 3) (.var 1))
          (.letE (.apply (.var 4) (.word (Solcore.Core.Word.ofNatModulo 0)))
            (.letE (.apply (.var 4) (.binary .wordAdd (.var 2) (.var 1)))
              (.letE (.apply (.var 7) (.pair (.var 4) (.var 0)))
                (.letE (.apply (.var 8) (.pair (.binary .wordAdd (.var 5)
                    (.word (Solcore.Core.Word.ofNatModulo 1))) (.var 3)))
                  (.letE (.apply (.var 9) (.pair (.word (Solcore.Core.Word.ofNatModulo 0))
                      (.binary .wordAdd (.var 3) (.word (Solcore.Core.Word.ofNatModulo 1)))))
                    (.letE (.apply (.var 9) (.var 7))
                      (.letE (.apply (.var 10) (.binary .wordAdd (.var 8)
                          (.word (Solcore.Core.Word.ofNatModulo 1))))
                        (.letE (.apply (.var 11) (.word (Solcore.Core.Word.ofNatModulo 0)))
                          (.letE (.binary .wordAdd (.binary .wordAdd (.var 2) (.var 1)) (.var 0))
                            (.ifE (.binary .wordEq (.binary .wordAnd (.var 10)
                                (.word (Solcore.Core.Word.ofNatModulo 1)))
                                (.word (Solcore.Core.Word.ofNatModulo 1)))
                              (.inRight .word (.inLeft .word (.var 0)))
                              (.inLeft (.sum .word .word) (.var 0)))))))))))))))

theorem keyedProgram_body (step : Solcore.Synthesis.Core.Aggregates.CheckedDAG) :
    (Solcore.Synthesis.Core.KeyedStorage.canonicalProgram step).body =
      keyedExpression step.program.body :=
  rfl

/-- The outcome by the input's low bit, with the sum as payload. -/
def keyedCompletion : Solcore.Core.Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 10) (.word (Solcore.Core.Word.ofNatModulo 1)))
      (.word (Solcore.Core.Word.ofNatModulo 1)))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

/-- The Core continuations of the keyed wrapper, from the sum back to the key. -/
def keyedTail12 : Solcore.Core.Expr :=
  .letE (.binary .wordAdd (.binary .wordAdd (.var 2) (.var 1)) (.var 0)) keyedCompletion

def keyedTail11 : Solcore.Core.Expr :=
  .letE (.apply (.var 11) (.word (Solcore.Core.Word.ofNatModulo 0))) keyedTail12

def keyedTail10 : Solcore.Core.Expr :=
  .letE (.apply (.var 10) (.binary .wordAdd (.var 8) (.word (Solcore.Core.Word.ofNatModulo 1))))
    keyedTail11

def keyedTail9 : Solcore.Core.Expr := .letE (.apply (.var 9) (.var 7)) keyedTail10

def keyedTail8 : Solcore.Core.Expr :=
  .letE (.apply (.var 9) (.pair (.word (Solcore.Core.Word.ofNatModulo 0))
    (.binary .wordAdd (.var 3) (.word (Solcore.Core.Word.ofNatModulo 1))))) keyedTail9

def keyedTail7 : Solcore.Core.Expr :=
  .letE (.apply (.var 8) (.pair (.binary .wordAdd (.var 5)
    (.word (Solcore.Core.Word.ofNatModulo 1))) (.var 3))) keyedTail8

def keyedTail6 : Solcore.Core.Expr := .letE (.apply (.var 7) (.pair (.var 4) (.var 0))) keyedTail7

def keyedTail5 : Solcore.Core.Expr :=
  .letE (.apply (.var 4) (.binary .wordAdd (.var 2) (.var 1))) keyedTail6

def keyedTail4 : Solcore.Core.Expr :=
  .letE (.apply (.var 4) (.word (Solcore.Core.Word.ofNatModulo 0))) keyedTail5

def keyedTail3 : Solcore.Core.Expr := .letE (.apply (.var 3) (.var 1)) keyedTail4

def keyedTail2 : Solcore.Core.Expr :=
  .letE (.caseE (.apply (.var 10) (.word (Solcore.Core.Word.ofNatModulo 36)))
    (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0)) keyedTail3

def keyedTail1 : Solcore.Core.Expr :=
  .letE (.caseE (.apply (.var 9) (.word (Solcore.Core.Word.ofNatModulo 4)))
    (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0)) keyedTail2

theorem keyedExpression_toCore (stepBody : Solcore.Core.Wire.Expr) :
    (keyedExpression stepBody).toCore = .letE stepBody.toCore keyedTail1 := by
  simp only [keyedExpression, Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore,
    Solcore.Core.Wire.Ty.toCore, keyedTail1, keyedTail2, keyedTail3, keyedTail4, keyedTail5,
    keyedTail6, keyedTail7, keyedTail8, keyedTail9, keyedTail10, keyedTail11, keyedTail12,
    keyedCompletion]

theorem keyedCompletion_evaluates {environment : Solcore.Core.Environment}
    {store : Solcore.Core.Store} {input sum : Solcore.Core.Word}
    (inputAt : environment[9]? = some (.word input)) :
    Solcore.Core.Evaluates (.word sum :: environment) store keyedCompletion
      (rollbackValue (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
        Solcore.Core.Word.ofNatModulo 1) sum) store := by
  have condition : Solcore.Core.Evaluates (.word sum :: environment) store
      (.binary .wordEq (.binary .wordAnd (.var 10) (.word (Solcore.Core.Word.ofNatModulo 1)))
        (.word (Solcore.Core.Word.ofNatModulo 1)))
      (.bool (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
        Solcore.Core.Word.ofNatModulo 1)) store :=
    .binary (.binary (.var (by simpa using inputAt)) .word rfl) .word rfl
  unfold rollbackValue
  cases flag : (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
      Solcore.Core.Word.ofNatModulo 1)
  · rw [flag] at condition
    exact .ifFalse condition (.inLeft (.var rfl))
  · rw [flag] at condition
    exact .ifTrue condition (.inRight (.inLeft (.var rfl)))

/-- The context after the three writes, in the order key, successor, counter. -/
def keyedContext (context : TransactionHostStorageDriver.Context)
    (key computed : Solcore.Core.Word) : TransactionHostStorageDriver.Context :=
  ((context.writeStorage key computed).writeStorage (key.add (Solcore.Core.Word.ofNatModulo 1))
    (context.readStorage key)).writeStorage (Solcore.Core.Word.ofNatModulo 0)
    ((context.readStorage (Solcore.Core.Word.ofNatModulo 0)).add
      (Solcore.Core.Word.ofNatModulo 1))

/-- The sum of the three slots read back from a context. -/
def keyedContextSum (context : TransactionHostStorageDriver.Context)
    (key : Solcore.Core.Word) : Solcore.Core.Word :=
  ((context.readStorage key).add
    (context.readStorage (key.add (Solcore.Core.Word.ofNatModulo 1)))).add
    (context.readStorage (Solcore.Core.Word.ofNatModulo 0))

/-- **The keyed reference's transaction, as a handled host path.** From the
initial state, the wrapper reads the key and the input, runs the ten host
requests in order and ends with the outcome value of the three slots' sum. -/
theorem keyed_handled {inputs : HostStorageDriver.ExecutionInputs}
    {context : TransactionHostStorageDriver.Context} {step : Solcore.Core.Expr}
    {closure : CoreValue} {key input computed : Solcore.Core.Word} {store : Solcore.Core.Store}
    (stepEvaluates : Solcore.Core.Evaluates Solcore.Core.hostEnvironment [] step closure [])
    (keyDecoded : inputs.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 4) = some key)
    (inputDecoded : inputs.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 36) = some input)
    (applied : Solcore.Core.Evaluates
      (.word (context.readStorage (Solcore.Core.Word.ofNatModulo 0)) ::
        .word (context.readStorage key) :: .word input :: .word key :: closure ::
        Solcore.Core.hostEnvironment) []
      (.apply (.var 4) (.binary .wordAdd (.var 2) (.var 1))) (.word computed) store) :
    ∃ steps, HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
      (Solcore.Core.State.initial (.letE step keyedTail1) Solcore.Core.hostEnvironment)
      (keyedContext context key computed)
      (Solcore.Core.State.final (rollbackValue
        (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1)
        (keyedContextSum (keyedContext context key computed) key)) store) := by
  let environment1 : Solcore.Core.Environment := closure :: Solcore.Core.hostEnvironment
  let environment2 : Solcore.Core.Environment := .word key :: environment1
  let environment3 : Solcore.Core.Environment := .word input :: environment2
  let environment4 : Solcore.Core.Environment := .word (context.readStorage key) :: environment3
  let environment5 : Solcore.Core.Environment :=
    .word (context.readStorage (Solcore.Core.Word.ofNatModulo 0)) :: environment4
  let environment6 : Solcore.Core.Environment := .word computed :: environment5
  let environment7 : Solcore.Core.Environment := .unit :: environment6
  let environment8 : Solcore.Core.Environment := .unit :: environment7
  let environment9 : Solcore.Core.Environment := .unit :: environment8
  let first : TransactionHostStorageDriver.Context := context.writeStorage key computed
  let second : TransactionHostStorageDriver.Context :=
    first.writeStorage (key.add (Solcore.Core.Word.ofNatModulo 1)) (context.readStorage key)
  let final := keyedContext context key computed
  let readKey := final.readStorage key
  let readNext := final.readStorage (key.add (Solcore.Core.Word.ofNatModulo 1))
  let readCount := final.readStorage (Solcore.Core.Word.ofNatModulo 0)
  let environment10 : Solcore.Core.Environment := .word readKey :: environment9
  let environment11 : Solcore.Core.Environment := .word readNext :: environment10
  let environment12 : Solcore.Core.Environment := .word readCount :: environment11
  let outcome : Solcore.Core.State := Solcore.Core.State.final (rollbackValue
    (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1)
    (keyedContextSum final key)) store
  have finish : ∃ steps, HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs)
      steps final ⟨.ret (.word readCount), [.letBody keyedTail12 environment11], store⟩ final
      outcome :=
    handledSteps_core (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_eval (.binary (.binary (.var rfl) (.var rfl) rfl) (.var rfl) rfl)
        (hostSteps_cons .bindLet (hostSteps_eval (keyedCompletion_evaluates rfl)
          ⟨0, .refl⟩)))))
  have countRead : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps final
        ⟨.ret (.word readNext), [.letBody keyedTail11 environment10], store⟩ final outcome :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_apply (index := 11) rfl .word))) .storageRead rfl rfl finish
  have nextRead : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps final
        ⟨.ret (.word readKey), [.letBody keyedTail10 environment9], store⟩ final outcome :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_apply (index := 10) rfl (.binary (.var rfl) .word rfl)))) .storageRead rfl rfl
      countRead
  have keyRead : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps final
        ⟨.ret .unit, [.letBody keyedTail9 environment8], store⟩ final outcome :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_apply (index := 9) rfl (.var rfl)))) .storageRead rfl rfl nextRead
  have countWrite : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps second
        ⟨.ret .unit, [.letBody keyedTail8 environment7], store⟩ final outcome :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_apply (index := 9) rfl (.pair .word (.binary (.var rfl) .word rfl)))))
      .storageWrite rfl rfl keyRead
  have nextWrite : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps first
        ⟨.ret .unit, [.letBody keyedTail7 environment6], store⟩ final outcome :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_apply (index := 8) rfl (.pair (.binary (.var rfl) .word rfl) (.var rfl)))))
      .storageWrite rfl rfl countWrite
  have keyWrite : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.word (context.readStorage (Solcore.Core.Word.ofNatModulo 0))),
          [.letBody keyedTail5 environment4], []⟩ final outcome :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_eval applied (hostSteps_cons .bindLet (hostSteps_cons .enterLet
        (hostSteps_apply (index := 7) rfl (.pair (.var rfl) (.var rfl))))))))
      .storageWrite rfl rfl nextWrite
  have countLoad : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.word (context.readStorage key)), [.letBody keyedTail4 environment3], []⟩ final
        outcome :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_apply (index := 4) rfl .word))) .storageRead rfl rfl keyWrite
  have keyLoad : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.inRight .unit (.word input)),
          [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment2,
            .letBody keyedTail3 environment2], []⟩ final outcome :=
    handledSteps_request (hostSteps_cons .chooseRight (hostSteps_cons (.var rfl)
      (hostSteps_cons .bindLet (hostSteps_cons .enterLet
        (hostSteps_apply (index := 3) rfl (.var rfl)))))) .storageRead rfl rfl countLoad
  have inputResumed : (TransactionHostStorageDriver.handler inputs).handleSuspension context
      ⟨.inputDataWordBE? (Solcore.Core.Word.ofNatModulo 36),
        [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment2,
          .letBody keyedTail3 environment2], []⟩ =
      (context, ⟨.ret (.inRight .unit (.word input)),
        [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment2,
          .letBody keyedTail3 environment2], []⟩) := by
    rw [handleSuspension_inputDataWordBE, inputDecoded]
    rfl
  have inputLoad : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.inRight .unit (.word key)),
          [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment1,
            .letBody keyedTail2 environment1], []⟩ final outcome :=
    handledSteps_request (hostSteps_cons .chooseRight (hostSteps_cons (.var rfl)
      (hostSteps_cons .bindLet (hostSteps_cons .enterLet (hostSteps_cons .enterCase
        (hostSteps_apply (index := 10) rfl .word)))))) .inputDataWordBE? rfl inputResumed
      keyLoad
  have keyResumed : (TransactionHostStorageDriver.handler inputs).handleSuspension context
      ⟨.inputDataWordBE? (Solcore.Core.Word.ofNatModulo 4),
        [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment1,
          .letBody keyedTail2 environment1], []⟩ =
      (context, ⟨.ret (.inRight .unit (.word key)),
        [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment1,
          .letBody keyedTail2 environment1], []⟩) := by
    rw [handleSuspension_inputDataWordBE, keyDecoded]
    rfl
  exact handledSteps_request (hostSteps_cons .enterLet (hostSteps_eval stepEvaluates
    (hostSteps_cons .bindLet (hostSteps_cons .enterLet (hostSteps_cons .enterCase
      (hostSteps_apply (index := 9) rfl .word)))))) .inputDataWordBE? rfl keyResumed inputLoad

/-! ### Storage agreement -/

/-- A write of a word keeps an account in agreement with the source storage
written at that slot. -/
theorem storageAgrees_write {account : Account} {storage : Storage}
    (agrees : StorageAgrees account storage) (slot value : Solcore.Core.Word) :
    StorageAgrees (account.storageWrite slot value) (storage.write slot.val value.val) := by
  intro other
  by_cases same : other = slot
  · subst same
    rw [Account.storageRead_storageWrite_same]
    simp [Storage.write]
  · have values : other.val ≠ slot.val := fun equal => same (Fin.ext equal)
    rw [Account.storageRead_storageWrite_other _ _ _ _ same]
    simp [Storage.write, values, agrees other]

theorem storageAgrees_accountStorage (account : Account) :
    StorageAgrees account (accountStorage account) := by
  intro slot
  simp [accountStorage, word_ofNatModulo_val]

/-! ### Preservation -/

/-- **Keyed-storage emitter preservation.** If the actual emitter succeeds, its
source text is the printing of a keyed file with one free function per helper
and the step function `sc_step`, importing `sload`, `sstore`, `mstore`,
`revert_` and the raw opcode aliases exactly when a rendered body uses one,
and parses back to it. For every world in which the contract is installed and
every calldata whose words at offsets 4 and 36 are `key` and `input`, calling
`run(uint256,uint256)` from the installed account's storage under the keyed
source semantics reverts exactly when the input is odd, and the original Core
contract's top-level transaction settles as that outcome. -/
theorem KeyedStorage.emit_preserves_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : KeyedStorage.emit plan = .ok emitted) :
    ∃ file : KeyedFile, emitted.source = file.print ∧
      parseKeyedSource emitted.source = some file ∧
      ∀ {world : WorldState} {invocation : TopLevelInvocation}
        (installed : InstalledCheckedCoreContract world invocation.target plan.contract)
        {key input : Solcore.Core.Word},
        invocation.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 4) = some key →
        invocation.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 36) = some input →
        ∃ outcome : RollbackOutcome,
          file.call (accountStorage installed.account) "run" [key.val, input.val] =
            some outcome ∧
          ((∃ data, outcome = .reverted data) ↔ input.val % 2 = 1) ∧
          CoreSettles plan.contract invocation installed outcome := by
  obtain ⟨names, lines, entry, result, loop, entryEquation, resultFound, source⟩ :=
    KeyedStorage.emit_success emitted_eq
  let bodies := plan.step.helpers ++ [plan.step.entry]
  let uses := bodies.any AggregateRenderer.usesOpcodeAliases
  have aliasesOk : uses = true → aggregateAliases bodies = primitiveAliases := by
    intro used
    simp only [aggregateAliases]
    rw [if_pos used]
  have bodyUses : ∀ body ∈ bodies, AggregateRenderer.usesOpcodeAliases body = true →
      uses = true := fun body mem used => List.any_eq_true.mpr ⟨body, mem, used⟩
  have startPrimitive : uses = true → PrimitiveContext ⟨[], aggregateAliases bodies⟩ := by
    intro used
    rw [aliasesOk used]
    exact primitiveContext_aliases
  obtain ⟨declarations, linesEq, namesEq, declarationsOk, primitive, agree⟩ :=
    aggregateLoop_spec aliasesOk plan.step.helpers 0 _ names lines [] Solcore.Core.hostEnvironment
      loop
      (fun index body found =>
        ⟨aggregate_helpers_accepted plan.step.helperScopes index body found,
          bodyUses body (List.mem_append_left _ (List.mem_of_getElem? found))⟩)
      startPrimitive (fun _ _ found => by simp [helperNames] at found)
  have entryKind : initializerKind? ([Binding.word "sc_arg"].map Binding.kind) names.length
      plan.step.entry = some Local.word := by
    rw [namesEq, helperNames_length, Nat.zero_add]
    exact aggregate_acceptsAt_kind plan.step.entryScope
  obtain ⟨statements, entryLines, _, valueName, entryNames, simulates⟩ :=
    (aggregate_render_spec plan.step.entry).1
      (fun context => uses = true → PrimitiveContext context)
      (fun context admitted used =>
        admitted (bodyUses plan.step.entry (List.mem_append_right _ (by simp)) used))
      names .word [.word "sc_arg"] 4 0 entry entryKind entryEquation
      (single_abinding_fresh argument_not_temporary cellTemp_ne_argument
        payloadTemp_ne_argument)
      (single_abinding_distinct _)
  let file := keyedFile (aggregateAliases bodies) declarations statements result
  have argumentOk : ∀ index found, anameAt [Binding.word "sc_arg"] index = some found →
      ValidIdentifier found ∧ isReserved found = false :=
    single_abinding_ok (keyword_valid (by decide)) (by decide)
  have functionNamesOk : ∀ name ∈ names, ValidIdentifier name ∧ isReserved name = false := by
    rw [namesEq]
    exact helperNames_ok
  have valueOk := aggregate_identifier_ok argumentOk functionNamesOk
    (valueName result resultFound).uses
  have stepOk : (stepDecl statements result).NamesOk ∧
      ∀ name ∈ (stepDecl statements result).identifiers, ValidIdentifier name := by
    have bodyOk := fun name mem =>
      aggregate_identifier_ok argumentOk functionNamesOk (entryNames name mem)
    refine ⟨⟨show isReserved "sc_step" = false by decide, ?_,
      fun name mem => (bodyOk name mem).2, ?_⟩, ?_⟩
    · intro parameter mem
      simp only [stepDecl, List.mem_singleton] at mem
      subst mem
      decide
    · intro name mem
      simp only [stepDecl, Expr.identifiers, List.mem_singleton] at mem
      subst mem
      exact valueOk.2
    · intro name mem
      simp only [stepDecl, FunctionDecl.identifiers, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.mem_append, Expr.identifiers,
        List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | mem | rfl
      · exact keyword_valid (by decide)
      · exact keyword_valid (by decide)
      · exact (bodyOk name mem).1
      · exact valueOk.1
  have functionsOk : ∀ function ∈ file.functions, function.NamesOk ∧
      ∀ name ∈ function.identifiers, ValidIdentifier name := by
    intro function mem
    rcases List.mem_append.mp mem with mem | mem
    · exact declarationsOk function mem
    · simp only [List.mem_singleton] at mem
      subst mem
      exact stepOk
  have printed : emitted.source = file.print := by
    have stepLines : (stepDecl statements result).lines =
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
          ["    return " ++ result ++ ";", "}", ""] := by
      simp only [stepDecl, FunctionDecl.lines, entryLines, List.cons_append, List.nil_append,
        List.cons.injEq]
      refine ⟨?_, ?_⟩
      · apply String.toList_inj.mp
        simp [FunctionDecl.parameterText, LocalType.spelling]
      · simp [Expr.print]
    have functionLine : "    function " ++ KeyedStorage.methodName ++
        "(key: uint256, input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply String.toList_inj.mp
      simp [file, keyedFile, keyedMethod, Method.parameterText, KeyedStorage.methodName]
    rw [source, KeyedFile.print, KeyedFile.lines, linesEq, functionLine]
    simp [file, keyedFile, KeyedStorage.contractName, stepLines, bodies, keyedMethod_lines]
  have bodyNames := keyedBody_names_ok
  have parsed : parseKeyedSource emitted.source = some file := by
    rw [printed]
    apply parseKeyedSource_print
    · refine ⟨fun function mem => (functionsOk function mem).1, rfl, rfl, ?_,
        fun name mem => (bodyNames name (List.mem_append_left _ mem)).2,
        fun name mem => (bodyNames name (List.mem_append_right _ mem)).2⟩
      intro parameter mem
      simp only [file, keyedFile, keyedMethod, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> decide
    · refine ⟨aggregateAliases_valid bodies, fun function mem => (functionsOk function mem).2,
        keyword_valid (show validIdentifier "SynthesizedKeyedStorage" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (bodyNames name (List.mem_append_left _ mem)).1,
        fun name mem => (bodyNames name (List.mem_append_right _ mem)).1⟩
      intro parameter mem
      simp only [file, keyedFile, keyedMethod, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> exact keyword_valid (by decide)
  refine ⟨file, printed, parsed, ?_⟩
  intro world invocation installed key input keyData inputData
  have stepCall : ∀ arguments, file.context.call "sc_step" arguments =
      (stepDecl statements result).denote
        ⟨declareFunctions (aggregateAliases bodies) [] declarations, aggregateAliases bodies⟩
        arguments := by
    intro arguments
    show Context.call ⟨declareFunctions (aggregateAliases bodies) []
      (declarations ++ [stepDecl statements result]), aggregateAliases bodies⟩ "sc_step"
        arguments = _
    rw [declareFunctions_append_single]
    exact Context.call_cons_same _ _ _ _ _
  let old := installed.account.storageRead key
  let count := installed.account.storageRead (Solcore.Core.Word.ofNatModulo 0)
  obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _, _, _⟩ :=
    simulates ⟨declareFunctions (aggregateAliases bodies) [] declarations,
        aggregateAliases bodies⟩
      (.word (input.add old) :: plan.step.helpers.foldl closureStep Solcore.Core.hostEnvironment)
      [] [] [[("sc_arg", .word (input.add old).val)]] primitive
      (single_abinding_agree (by simp [Frames.lookup, Scope.get?]) _ [])
      (single_abinding_cells _ _ _) (by simp) (by simpa using agree)
  rw [resultFound, Option.bind_some] at represents
  obtain ⟨_, lookup, computed, rfl, rfl⟩ := represents
  have sourceStep : file.context.call "sc_step" [.word (input.add old).val] =
      some (.word computed.val) := by
    rw [stepCall]
    simp [stepDecl, FunctionDecl.denote, FunctionDecl.bindParameters, LocalType.admits, exec,
      Expr.eval, lookup]
  have initial := storageAgrees_accountStorage installed.account
  let written := keyedStorage (accountStorage installed.account) key old count computed
  let account :=
    ((installed.account.storageWrite key computed).storageWrite
      (key.add (Solcore.Core.Word.ofNatModulo 1)) old).storageWrite
      (Solcore.Core.Word.ofNatModulo 0) (count.add (Solcore.Core.Word.ofNatModulo 1))
  have agrees : StorageAgrees account written := by
    have zeroVal : (Solcore.Core.Word.ofNatModulo 0).val = 0 := ofNatModulo_val_small (by decide)
    have three := storageAgrees_write (storageAgrees_write (storageAgrees_write initial key
      computed) (key.add (Solcore.Core.Word.ofNatModulo 1)) old) (Solcore.Core.Word.ofNatModulo 0)
      (count.add (Solcore.Core.Word.ofNatModulo 1))
    rw [zeroVal] at three
    exact three
  let sum := ((account.storageRead key).add
    (account.storageRead (key.add (Solcore.Core.Word.ofNatModulo 1)))).add
    (account.storageRead (Solcore.Core.Word.ofNatModulo 0))
  have sumVal : sum.val = keyedSum written key := by
    have zeroVal : (Solcore.Core.Word.ofNatModulo 0).val = 0 := ofNatModulo_val_small (by decide)
    simp only [sum, keyedSum, ← evm_add, agrees key, agrees (key.add (Solcore.Core.Word.ofNatModulo 1)),
      agrees (Solcore.Core.Word.ofNatModulo 0), zeroVal]
  refine ⟨keyedOutcome (accountStorage installed.account) key input old count computed, ?_, ?_,
    ?_⟩
  · show (if file.method.name = "run" then file.method.run file.context
      (accountStorage installed.account) [key.val, input.val] else none) = _
    rw [if_pos (show file.method.name = "run" from rfl)]
    exact keyedMethod_run file.context _ key input old count computed sourceStep
      (by simp [accountStorage, word_ofNatModulo_val, old]) rfl
  · unfold keyedOutcome
    rw [rollback_parity]
    by_cases odd : input.val % 2 = 1 <;> simp [odd]
  · let context := TopLevelExecution.initialTransactionContext installed
    have stepEvaluates := dag_evaluates plan.step.entry plan.step.helpers
      Solcore.Core.hostEnvironment []
    have applied : Solcore.Core.Evaluates
        (.word (context.readStorage (Solcore.Core.Word.ofNatModulo 0)) ::
          .word (context.readStorage key) :: .word input :: .word key ::
          .closure (Solcore.Core.Wire.Ty.toCore .word)
            (Solcore.Core.Wire.Ty.toCore .word) plan.step.entry.toCore
            (plan.step.helpers.foldl closureStep Solcore.Core.hostEnvironment) ::
          Solcore.Core.hostEnvironment) []
        (.apply (.var 4) (.binary .wordAdd (.var 2) (.var 1))) (.word computed) store' :=
      .apply (.var rfl) (.binary (.var rfl) (.var rfl) rfl) evaluates
    obtain ⟨spent, path⟩ := keyed_handled (inputs := invocation.executionInputs)
      (context := context) stepEvaluates keyData inputData applied
    have body : plan.contract.code.program.body =
        .letE (Solcore.Synthesis.Core.functionDAGExpression plan.step.helpers
          plan.step.entry).toCore keyedTail1 := by
      show (keyedExpression plan.step.program.body).toCore = _
      rw [keyedExpression_toCore]
      rfl
    let final := keyedContext context key computed
    have finalAccount : final.storageAccount = account := by
      simp [final, keyedContext, context, account, old, count,
        FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage]
    have finalSum : keyedContextSum final key = sum := by
      simp only [keyedContextSum, sum,
        FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage, finalAccount]
    have address : final.context.storageAddress = invocation.target := by
      simp [final, keyedContext, context]
    have raw : ∀ fuel, spent ≤ fuel →
        TopLevelExecution.rawRun plan.contract invocation installed fuel =
          ⟨final, .done (rollbackValue (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
            Solcore.Core.Word.ofNatModulo 1) sum) store'⟩ := by
      intro fuel enough
      show HostDriver.run (TransactionHostStorageDriver.handler invocation.executionInputs)
        context fuel (Solcore.Core.State.initial plan.contract.code.program.body
          Solcore.Core.hostEnvironment) = _
      rw [body, ← finalSum]
      exact HostDriver.run_done_complete _ path enough
    have settled : ∀ fuel, spent ≤ fuel → ∃ result,
        TopLevelExecution.run plan.contract invocation installed fuel = .completed result ∧
        match keyedOutcome (accountStorage installed.account) key input old count computed with
        | .returned value storage =>
            ∃ word : Solcore.Core.Word, word.val = value ∧
              result.outcome = .returned (encodeWordBytesBE word) ∧
              ∃ account, result.finalWorld.account? invocation.target = some account ∧
                StorageAgrees account storage
        | .reverted data =>
            ∃ word : Solcore.Core.Word, word.val = data ∧
              result.outcome = .reverted (encodeWordBytesBE word) ∧ result.finalWorld = world := by
      intro fuel enough
      unfold keyedOutcome
      cases flag : (input.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
          Solcore.Core.Word.ofNatModulo 1)
      · have rawFlag := raw fuel enough
        rw [flag] at rawFlag
        obtain ⟨result, run, outcome, finalWorld, _⟩ := topLevel_run_settled plan.contract
          invocation installed fuel _ _ _ _ rawFlag rfl
        refine ⟨result, run, sum, sumVal, outcome, final.storageAccount, ?_, ?_⟩
        · rw [finalWorld _ rfl, ← address]
          exact final.storageAccount_present
        · rw [finalAccount]
          exact agrees
      · have rawFlag := raw fuel enough
        rw [flag] at rawFlag
        obtain ⟨result, run, outcome, _, finalWorld⟩ := topLevel_run_settled plan.contract
          invocation installed fuel _ _ _ _ rawFlag rfl
        exact ⟨result, run, sum, sumVal, outcome, finalWorld _ rfl⟩
    refine ⟨⟨spent, fun fuel enough => (settled fuel enough).elim fun result facts =>
      ⟨result, facts.1⟩⟩, ?_⟩
    intro fuel result run
    obtain ⟨result', run', facts⟩ := settled (fuel + spent) (by omega)
    have resumed := TopLevelExecution.resumeWithFuel_run plan.contract invocation installed fuel
      spent
    rw [run, TopLevelExecution.resumeWithFuel_completed, run'] at resumed
    cases resumed
    exact facts

/-- **Keyed-storage emitter preservation, on the emitted text.** Read as a
keyed program, the emitted text called with the key and the input from the
installed account's storage reverts exactly when the input is odd. The original
Core contract's transaction settles as that outcome: it returns the same word
and commits the same storage, or reverts with the same word and leaves the
world unchanged. -/
theorem KeyedStorage.emit_source_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : KeyedStorage.emit plan = .ok emitted)
    {world : WorldState} {invocation : TopLevelInvocation}
    (installed : InstalledCheckedCoreContract world invocation.target plan.contract)
    {key input : Solcore.Core.Word}
    (keyData : invocation.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 4) = some key)
    (inputData : invocation.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 36) = some input) :
    ∃ outcome : RollbackOutcome,
      keyedSourceCall emitted.source (accountStorage installed.account) "run"
        [key.val, input.val] = some outcome ∧
      ((∃ data, outcome = .reverted data) ↔ input.val % 2 = 1) ∧
      CoreSettles plan.contract invocation installed outcome := by
  obtain ⟨file, _, parsed, meaning⟩ := KeyedStorage.emit_preserves_meaning emitted_eq
  obtain ⟨outcome, call, parity, settles⟩ := meaning installed keyData inputData
  exact ⟨outcome, by simp [keyedSourceCall, parsed, call], parity, settles⟩

end Solcore.Synthesis.Source.ScalarMeaning
end

section
-- leanmerge: from Solcore.Synthesis.Source.ScalarMeaning.LogEmitter
/-! Meaning preservation for the actual event-log emitter (`EventLog.emit`,
profile `stateful-logs`). The method takes flags and an input. It reads slots
zero and one, stores the step's result for the input plus slot zero in slot
zero and the counter plus one in slot one, and reserves a 64-byte buffer from
the free-memory pointer at 64. Each site whose guard bit is set in the flags
binds the step's value for the result plus its guard, writes its data Words to
the buffer, and emits one log with its topics through the `std.opcodes`
wrapper for its topic count. Odd flags then revert with the result; even flags
return it.

The Core reference is a host-runtime contract with the three-way Word outcome
profile. It reads the flags and the input from calldata at offsets 4 and 36,
runs the same storage requests in the same order, and writes each enabled
site's log as a frame of word logs under `EventLog.framingVersion`. One
top-level transaction runs it on a world in which it is installed. Its
committed journal is the working journal on return and the empty checkpoint
journal on revert, so a revert discards the logs with the writes in Core as in
the source. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

open Solcore.Synthesis.Core.EventLog (CheckedPlan Site headerTag dataTag topicTag frame emitRecords
  siteExpression withSites contractExpression)
open Solcore.Synthesis.Core.Aggregates (Local initializerKind?)
open Solcore.Synthesis.Source.AggregateRenderer (Binding)
open Solcore.ContractRuntime

/-! ### The emitted text -/

/-- The wrapper aliases an event-log plan imports: `logN as sc_logN` for each
topic count its sites use, ascending. -/
def logAliases (sites : List Site) : List (String × String) :=
  (EventLog.usedArities sites).map fun topics =>
    ("log" ++ toString topics, EventLog.logAlias topics)

theorem logImport_eq (sites : List Site) (bodies : List CoreExpr) :
    AggregateRenderer.opcodeImportWith (["sload", "sstore", "mload", "mstore", "revert_"] ++
        (EventLog.usedArities sites).map fun topics =>
          "log" ++ toString topics ++ " as " ++ EventLog.logAlias topics) bodies =
      logImportLine (logAliases sites ++ aggregateAliases bodies) := by
  unfold AggregateRenderer.opcodeImportWith logImportLine aggregateAliases logAliases
  by_cases used : bodies.any AggregateRenderer.usesOpcodeAliases = true
  · simp only [used, if_true, primitiveAliases_printed, List.map_append, List.map_map,
      Function.comp_def, List.append_assoc]
  · simp only [used, Bool.false_eq_true, if_false, List.append_nil, List.map_map,
      Function.comp_def]

theorem EventLog.emit_success {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : EventLog.emit plan = .ok emitted) :
    ∃ (names lines : List String) (entry : ARendered) (result : String),
      aggregateLoop plan.step.helpers 0 []
        ["import * from std;", "import * from std.dispatch;",
          logImportLine (logAliases plan.sites ++
            aggregateAliases (plan.step.helpers ++ [plan.step.entry])), ""] =
        .ok (names, lines) ∧
      AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry = .ok entry ∧
      entry.value = some result ∧
      emitted.source = String.intercalate "\n" (lines ++
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
        ["    return " ++ result ++ ";", "}", "",
          "contract " ++ EventLog.contractName ++ " {",
          "    function " ++ EventLog.methodName ++
            "(flags: uint256, input: uint256) public returns (uint256) {",
          "        let sc_flags: word = Typedef.rep(flags);",
          "        let sc_input: word = Typedef.rep(input);",
          "        let sc_old: word = sload(0);",
          "        let sc_count: word = sload(1);",
          "        let sc_result: word = sc_step(sc_input + sc_old);",
          "        sstore(0, sc_result);",
          "        sstore(1, sc_count + 1);",
          "        let sc_ptr: word = mload(64);",
          "        mstore(64, sc_ptr + 64);"] ++ plan.sites.flatMap EventLog.siteLines ++
        ["        if ((sc_flags & 1) == 1) {",
          "            mstore(sc_ptr, sc_result);",
          "            revert_(sc_ptr, 32);",
          "        }",
          "        return uint256(sc_result);", "    }", "}"]) ++ "\n" := by
  unfold EventLog.emit at emitted_eq
  dsimp only at emitted_eq
  rw [forIn_aggregateLoop (fun _ _ _ _ => rfl), logImport_eq] at emitted_eq
  cases loop : aggregateLoop plan.step.helpers 0 []
    ["import * from std;", "import * from std.dispatch;",
      logImportLine (logAliases plan.sites ++
        aggregateAliases (plan.step.helpers ++ [plan.step.entry])), ""] with
  | error error =>
      rw [loop] at emitted_eq
      cases emitted_eq
  | ok loopResult =>
      obtain ⟨names, lines⟩ := loopResult
      rw [loop] at emitted_eq
      cases entry : AggregateRenderer.render names .word [.word "sc_arg"] 4 0
        plan.step.entry with
      | error error =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases emitted_eq
      | ok rendered =>
          simp only [bind, Except.bind, entry] at emitted_eq
          cases value : AggregateRenderer.requireValue rendered with
          | error error =>
              simp only [value] at emitted_eq
              cases emitted_eq
          | ok result =>
              simp only [value, pure, Except.pure, Except.ok.injEq] at emitted_eq
              subst emitted_eq
              exact ⟨names, lines, rendered, result, rfl, entry, arequireValue_ok value, rfl⟩

/-- The name a site binds its step value to. -/
def siteValue (site : Site) : String := "sc_value" ++ toString site.guard

/-- The stores a site prints: its value at `sc_ptr`, then the result 32 bytes
further, one per data Word. -/
def siteStores (site : Site) : List (Operand × Operand) :=
  (List.range site.dataWords).map fun index =>
    (if index = 0 then .plain (.name "sc_ptr") else .operation .add (.name "sc_ptr") (.number 32),
      .plain (.name (if index = 0 then siteValue site else "sc_result")))

/-- The source statement the event-log emitter prints for one site. -/
def siteStmt (site : Site) : LogStmt :=
  .logIf .eq (.binary .bitAnd (.name "sc_flags") (.number (2 ^ site.guard)))
    (.number (2 ^ site.guard))
    { identifier := siteValue site, type := .word, callee := "sc_step", op := .add,
      left := .name "sc_result", right := .number site.guard, stores := siteStores site,
      logger := EventLog.logAlias site.topics, dataOffset := .plain (.name "sc_ptr"),
      dataSize := .plain (.number (32 * site.dataWords)),
      topics := (List.range site.topics).map fun index =>
        .operation .add (.name (siteValue site)) (.number (index + 1)) }

/-- The method body the event-log emitter prints. -/
def logBody (sites : List Site) : List LogStmt :=
  [.rollback (.storage (.plain (.letDecl "sc_flags" .word (.typedefRep (.name "flags"))))),
    .rollback (.storage (.plain (.letDecl "sc_input" .word (.typedefRep (.name "input"))))),
    .rollback (.storage (.plain (.letDecl "sc_old" .word (.call1 "sload" (.number 0))))),
    .rollback (.storage (.plain (.letDecl "sc_count" .word (.call1 "sload" (.number 1))))),
    .rollback (.storage (.letCall "sc_result" .word "sc_step" .add (.name "sc_input")
      (.name "sc_old"))),
    .rollback (.storage (.store (.plain (.number 0)) (.plain (.name "sc_result")))),
    .rollback (.storage (.store (.plain (.number 1))
      (.operation .add (.name "sc_count") (.number 1)))),
    .rollback (.storage (.plain (.letDecl "sc_ptr" .word (.call1 "mload" (.number 64))))),
    .store (.plain (.number 64)) (.operation .add (.name "sc_ptr") (.number 64))] ++
  sites.map siteStmt ++
  [.rollback (.revertIf .eq (.binary .bitAnd (.name "sc_flags") (.number 1)) (.number 1)
    (.plain (.name "sc_ptr")) (.plain (.name "sc_result")) (.plain (.name "sc_ptr"))
    (.plain (.number 32)))]

/-- The method the event-log emitter prints. -/
def logMethod (sites : List Site) : LogMethod where
  name := "run"
  parameters := ["flags", "input"]
  body := logBody sites
  result := .plain (.name "sc_result")

/-- The log file printed by the event-log emitter. -/
def logFile (aliases : List (String × String)) (declarations : List FunctionDecl)
    (statements : List Stmt) (value : String) (sites : List Site) : LogFile where
  opcodeAliases := aliases
  functions := declarations ++ [stepDecl statements value]
  contract := "SynthesizedLogs"
  method := logMethod sites

private theorem digits_sixtyFour : Nat.toDigits 10 64 = ['6', '4'] := by decide

theorem storesLines_map {α : Type} (indent : Nat) (store : α → Operand × Operand) :
    ∀ (items : List α), storesLines indent (items.map store) =
      items.map fun item => storeLine indent (store item).1 (store item).2
  | [] => rfl
  | item :: rest => by
      simp [storesLines, storesLines_map indent store rest]

/-- Each text after a comma. -/
def commaTail : List String → String
  | [] => ""
  | text :: rest => ", " ++ text ++ commaTail rest

theorem intercalate_comma (first : String) :
    ∀ (rest : List String), String.intercalate ", " (first :: rest) = first ++ commaTail rest
  | [] => by simp [commaTail]
  | next :: more => by
      rw [String.intercalate_cons_cons, intercalate_comma next more]
      simp [commaTail, String.append_assoc]

theorem topicsText_map {α : Type} (topic : α → Operand) :
    ∀ (items : List α),
      topicsText (items.map topic) = commaTail (items.map fun item => (topic item).print)
  | [] => rfl
  | item :: rest => by
      simp [topicsText, commaTail, topicsText_map topic rest]

/-- A site's log call arguments: `sc_ptr`, the data size and each topic. -/
theorem siteTopics_text (site : Site) :
    String.intercalate ", " (["sc_ptr", toString (32 * site.dataWords)] ++
      (List.range site.topics).map fun index =>
        "sc_value" ++ toString site.guard ++ " + " ++ toString (index + 1)) =
      "sc_ptr" ++ (", " ++ toString (32 * site.dataWords) ++ topicsText
        ((List.range site.topics).map fun index =>
          .operation .add (.name (siteValue site)) (.number (index + 1)))) := by
  have printed : ((List.range site.topics).map fun index =>
      "sc_value" ++ toString site.guard ++ " + " ++ toString (index + 1)) =
      (List.range site.topics).map fun index =>
        (Operand.operation .add (.name (siteValue site)) (.number (index + 1))).print := by
    apply List.map_congr_left
    intro index _
    apply String.toList_inj.mp
    simp [Operand.print, Expr.print, BinaryOp.spelling, siteValue]
  rw [List.cons_append, List.cons_append, List.nil_append, intercalate_comma, commaTail,
    topicsText_map, printed]

/-- Each site prints as its source statement. -/
theorem siteStmt_lines (site : Site) : (siteStmt site).lines 8 = EventLog.siteLines site := by
  have stores : storesLines 12 (siteStores site) = (List.range site.dataWords).map fun index =>
      "            mstore(sc_ptr" ++ (if index = 0 then "" else " + 32") ++ ", " ++
        (if index = 0 then "sc_value" ++ toString site.guard else "sc_result") ++ ");" := by
    rw [siteStores, storesLines_map]
    apply List.map_congr_left
    intro index _
    apply String.toList_inj.mp
    by_cases zero : index = 0 <;>
      simp [zero, siteValue, storeLine, indentLine, Operand.print, Expr.print, BinaryOp.spelling,
        digits_thirtyTwo]
  unfold EventLog.siteLines
  simp only [siteStmt, LogStmt.lines, LogBlock.lines, LogBlock.binding, StorageStmt.lines, stores,
    siteTopics_text]
  apply lines_eq_of_chars
  simp [siteValue, indentLine, Operand.print, Expr.print, LocalType.spelling, BinaryOp.spelling]

theorem LogStmt.listLines_append (indent : Nat) (first second : List LogStmt) :
    LogStmt.listLines indent (first ++ second) =
      LogStmt.listLines indent first ++ LogStmt.listLines indent second := by
  induction first with
  | nil => rfl
  | cons statement rest ih => simp [LogStmt.listLines, ih, List.append_assoc]

theorem siteStmts_lines : ∀ (sites : List Site),
    LogStmt.listLines 8 (sites.map siteStmt) = sites.flatMap EventLog.siteLines
  | [] => rfl
  | site :: rest => by simp [LogStmt.listLines, siteStmt_lines, siteStmts_lines rest]

theorem logMethod_lines (sites : List Site) (rest : List String) :
    LogStmt.listLines 8 (logMethod sites).body ++
      ("        return uint256(" ++ (logMethod sites).result.print ++ ");") :: rest =
    ["        let sc_flags: word = Typedef.rep(flags);",
      "        let sc_input: word = Typedef.rep(input);",
      "        let sc_old: word = sload(0);",
      "        let sc_count: word = sload(1);",
      "        let sc_result: word = sc_step(sc_input + sc_old);",
      "        sstore(0, sc_result);",
      "        sstore(1, sc_count + 1);",
      "        let sc_ptr: word = mload(64);",
      "        mstore(64, sc_ptr + 64);"] ++ sites.flatMap EventLog.siteLines ++
    ["        if ((sc_flags & 1) == 1) {",
      "            mstore(sc_ptr, sc_result);",
      "            revert_(sc_ptr, 32);",
      "        }",
      "        return uint256(sc_result);"] ++ rest := by
  have prefixLines : LogStmt.listLines 8
      [.rollback (.storage (.plain (.letDecl "sc_flags" .word (.typedefRep (.name "flags"))))),
        .rollback (.storage (.plain (.letDecl "sc_input" .word (.typedefRep (.name "input"))))),
        .rollback (.storage (.plain (.letDecl "sc_old" .word (.call1 "sload" (.number 0))))),
        .rollback (.storage (.plain (.letDecl "sc_count" .word (.call1 "sload" (.number 1))))),
        .rollback (.storage (.letCall "sc_result" .word "sc_step" .add (.name "sc_input")
          (.name "sc_old"))),
        .rollback (.storage (.store (.plain (.number 0)) (.plain (.name "sc_result")))),
        .rollback (.storage (.store (.plain (.number 1))
          (.operation .add (.name "sc_count") (.number 1)))),
        .rollback (.storage (.plain (.letDecl "sc_ptr" .word (.call1 "mload" (.number 64))))),
        .store (.plain (.number 64)) (.operation .add (.name "sc_ptr") (.number 64))] =
      ["        let sc_flags: word = Typedef.rep(flags);",
        "        let sc_input: word = Typedef.rep(input);",
        "        let sc_old: word = sload(0);",
        "        let sc_count: word = sload(1);",
        "        let sc_result: word = sc_step(sc_input + sc_old);",
        "        sstore(0, sc_result);",
        "        sstore(1, sc_count + 1);",
        "        let sc_ptr: word = mload(64);",
        "        mstore(64, sc_ptr + 64);"] := by
    apply lines_eq_of_chars
    simp [LogStmt.listLines, LogStmt.lines, RollbackStmt.lines, StorageStmt.lines, Stmt.lines,
      storeLine, indentLine, Expr.print, Operand.print, LocalType.spelling, BinaryOp.spelling,
      digits_one, digits_sixtyFour]
  have suffixLines : LogStmt.listLines 8
      [.rollback (.revertIf .eq (.binary .bitAnd (.name "sc_flags") (.number 1)) (.number 1)
        (.plain (.name "sc_ptr")) (.plain (.name "sc_result")) (.plain (.name "sc_ptr"))
        (.plain (.number 32)))] ++
      ("        return uint256(" ++ (Operand.plain (.name "sc_result")).print ++ ");") :: rest =
      ["        if ((sc_flags & 1) == 1) {",
        "            mstore(sc_ptr, sc_result);",
        "            revert_(sc_ptr, 32);",
        "        }",
        "        return uint256(sc_result);"] ++ rest := by
    apply lines_eq_of_chars
    simp [LogStmt.listLines, LogStmt.lines, RollbackStmt.lines, indentLine, Expr.print,
      Operand.print, BinaryOp.spelling, digits_one, digits_thirtyTwo]
  simp only [logMethod, logBody, LogStmt.listLines_append, siteStmts_lines, prefixLines,
    List.append_assoc]
  rw [suffixLines]

/-- Every name of a valid site's statement. -/
def siteNames : List String :=
  ["sc_flags", "sc_value1", "sc_value2", "sc_value3", "sc_step", "sc_result", "sc_ptr",
    "sc_log0", "sc_log1", "sc_log2", "sc_log3", "sc_log4"]

theorem mem_storesIdentifiers_map {α : Type} (store : α → Operand × Operand) {name : String} :
    ∀ {items : List α}, name ∈ storesIdentifiers (items.map store) →
      ∃ item ∈ items,
        name ∈ (store item).1.identifiers ∨ name ∈ (store item).2.identifiers
  | [], mem => by simp [storesIdentifiers] at mem
  | item :: rest, mem => by
      simp only [List.map_cons, storesIdentifiers, List.mem_append] at mem
      rcases mem with (found | found) | found
      · exact ⟨item, by simp, Or.inl found⟩
      · exact ⟨item, by simp, Or.inr found⟩
      · obtain ⟨other, mem, found⟩ := mem_storesIdentifiers_map store found
        exact ⟨other, by simp [mem], found⟩

theorem mem_topicsIdentifiers_map {α : Type} (topic : α → Operand) {name : String} :
    ∀ {items : List α}, name ∈ topicsIdentifiers (items.map topic) →
      ∃ item ∈ items, name ∈ (topic item).identifiers
  | [], mem => by simp [topicsIdentifiers] at mem
  | item :: rest, mem => by
      simp only [List.map_cons, topicsIdentifiers, List.mem_append] at mem
      rcases mem with found | found
      · exact ⟨item, by simp, found⟩
      · obtain ⟨other, mem, found⟩ := mem_topicsIdentifiers_map topic found
        exact ⟨other, by simp [mem], found⟩

theorem siteStmt_identifiers (site : Site) :
    (siteStmt site).identifiers = "sc_flags" :: siteValue site :: "sc_step" :: "sc_result" ::
      (storesIdentifiers (siteStores site) ++ EventLog.logAlias site.topics :: "sc_ptr" ::
        topicsIdentifiers ((List.range site.topics).map fun index =>
          .operation .add (.name (siteValue site)) (.number (index + 1)))) := by
  simp [siteStmt, LogStmt.identifiers, LogBlock.identifiers, LogBlock.binding,
    StorageStmt.identifiers, Expr.identifiers, Operand.identifiers]

theorem siteStmt_names (site : Site) (guard : 1 ≤ site.guard ∧ site.guard ≤ 3)
    (topics : site.topics ≤ 4) :
    ∀ name ∈ (siteStmt site).identifiers, name ∈ siteNames := by
  have value : siteValue site ∈ siteNames := by
    have cases : site.guard = 1 ∨ site.guard = 2 ∨ site.guard = 3 := by omega
    rcases cases with same | same | same <;> simp only [siteValue, same] <;> decide
  have logger : EventLog.logAlias site.topics ∈ siteNames := by
    have cases : site.topics = 0 ∨ site.topics = 1 ∨ site.topics = 2 ∨ site.topics = 3 ∨
        site.topics = 4 := by omega
    rcases cases with same | same | same | same | same <;>
      simp only [EventLog.logAlias, same] <;> decide
  intro name mem
  rw [siteStmt_identifiers] at mem
  simp only [List.mem_cons, List.mem_append] at mem
  rcases mem with same | same | same | same | stores | same | same | topicNames
  · subst same
    decide
  · subst same
    exact value
  · subst same
    decide
  · subst same
    decide
  · rw [siteStores] at stores
    obtain ⟨index, _, found⟩ := mem_storesIdentifiers_map _ stores
    by_cases zero : index = 0 <;>
      simp [zero, Operand.identifiers, Expr.identifiers] at found
    · rcases found with same | same <;> subst same
      · decide
      · exact value
    · rcases found with same | same <;> subst same <;> decide
  · subst same
    exact logger
  · subst same
    decide
  · obtain ⟨index, _, found⟩ := mem_topicsIdentifiers_map _ topicNames
    simp [Operand.identifiers, Expr.identifiers] at found
    subst found
    exact value

/-! ### The Core reference on the host machine -/

/-- `EventLog.contractExpression`, restated through its private helpers: the
step closure, the flags and the input, both reads, the base, the result and
both writes, then the sites. -/
theorem contractExpression_eq (stepBody : Solcore.Core.Wire.Expr) (sites : List Site) :
    contractExpression stepBody sites =
      .letE stepBody
        (.letE (.caseE (.apply (.var 9) (.word (Solcore.Core.Word.ofNatModulo 4)))
            (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0))
          (.letE (.caseE (.apply (.var 10) (.word (Solcore.Core.Word.ofNatModulo 36)))
              (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0))
            (.letE (.apply (.var 3) (.word (Solcore.Core.Word.ofNatModulo 0)))
              (.letE (.apply (.var 4) (.word (Solcore.Core.Word.ofNatModulo 1)))
                (.letE (.binary .wordAdd (.var 2) (.var 1))
                  (.letE (.apply (.var 5) (.var 0))
                    (.letE (.apply (.var 8) (.pair (.word (Solcore.Core.Word.ofNatModulo 0))
                        (.var 0)))
                      (.letE (.apply (.var 9) (.pair (.word (Solcore.Core.Word.ofNatModulo 1))
                          (.binary .wordAdd (.var 3) (.word (Solcore.Core.Word.ofNatModulo 1)))))
                        (withSites 9 sites))))))))) :=
  rfl

/-- `EventLog.siteExpression`, restated: the guard test, the step applied to
`result + guard`, then the frame's records. -/
theorem siteExpression_eq (depth : Nat) (site : Site) :
    siteExpression depth site =
      .ifE (.binary .wordEq (.binary .wordAnd (.var (depth - 1 - 1))
            (.word (Solcore.Core.Word.ofNatModulo (2 ^ site.guard))))
          (.word (Solcore.Core.Word.ofNatModulo (2 ^ site.guard))))
        (.letE (.apply (.var (depth - 1 - 0)) (.binary .wordAdd (.var (depth - 1 - 6))
            (.word (Solcore.Core.Word.ofNatModulo site.guard))))
          (emitRecords (depth + 1) (frame site depth)))
        .unit :=
  rfl

/-- The completion after the last site, restated: the outcome by the flags'
low bit, with the result as payload. -/
theorem withSites_nil (depth : Nat) :
    withSites depth [] =
      .ifE (.binary .wordEq (.binary .wordAnd (.var (depth - 1 - 1))
          (.word (Solcore.Core.Word.ofNatModulo 1))) (.word (Solcore.Core.Word.ofNatModulo 1)))
        (.inRight .word (.inLeft .word (.var (depth - 1 - 6))))
        (.inLeft (.sum .word .word) (.var (depth - 1 - 6))) :=
  rfl

theorem withSites_cons (depth : Nat) (site : Site) (rest : List Site) :
    withSites depth (site :: rest) =
      .letE (siteExpression depth site) (withSites (depth + 1) rest) :=
  rfl

theorem emitRecords_nil (depth : Nat) : emitRecords depth [] = .unit := rfl

theorem emitRecords_cons (depth tag : Nat) (payload : Nat → Solcore.Core.Wire.Expr)
    (rest : List (Nat × (Nat → Solcore.Core.Wire.Expr))) :
    emitRecords depth ((tag, payload) :: rest) =
      .letE (.apply (.var (13 + depth)) (.pair (.word (Solcore.Core.Word.ofNatModulo tag))
        (payload depth))) (emitRecords (depth + 1) rest) :=
  rfl

/-- `EventLog.frame`, restated: the header, the data Words and the topics. -/
theorem frame_eq (site : Site) (value : Nat) :
    frame site value =
      [(headerTag site, fun _ => .word (Solcore.Core.Word.ofNatModulo 0))] ++
        ((List.range site.dataWords).map fun index =>
          (dataTag (index + 1), fun depth => .var (depth - 1 - if index = 0 then value else 6))) ++
        ((List.range site.topics).map fun index =>
          (topicTag (index + 1), fun depth => .binary .wordAdd (.var (depth - 1 - value))
            (.word (Solcore.Core.Word.ofNatModulo (index + 1))))) :=
  rfl

/-- The Core continuations of the wrapper, from the second write back to the
flags. -/
def logTail8 (sites : List Site) : Solcore.Core.Expr :=
  .letE (.apply (.var 9) (.pair (.word (Solcore.Core.Word.ofNatModulo 1))
    (.binary .wordAdd (.var 3) (.word (Solcore.Core.Word.ofNatModulo 1)))))
    (withSites 9 sites).toCore

def logTail7 (sites : List Site) : Solcore.Core.Expr :=
  .letE (.apply (.var 8) (.pair (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0)))
    (logTail8 sites)

def logTail6 (sites : List Site) : Solcore.Core.Expr :=
  .letE (.apply (.var 5) (.var 0)) (logTail7 sites)

def logTail5 (sites : List Site) : Solcore.Core.Expr :=
  .letE (.binary .wordAdd (.var 2) (.var 1)) (logTail6 sites)

def logTail4 (sites : List Site) : Solcore.Core.Expr :=
  .letE (.apply (.var 4) (.word (Solcore.Core.Word.ofNatModulo 1))) (logTail5 sites)

def logTail3 (sites : List Site) : Solcore.Core.Expr :=
  .letE (.apply (.var 3) (.word (Solcore.Core.Word.ofNatModulo 0))) (logTail4 sites)

def logTail2 (sites : List Site) : Solcore.Core.Expr :=
  .letE (.caseE (.apply (.var 10) (.word (Solcore.Core.Word.ofNatModulo 36)))
    (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0)) (logTail3 sites)

def logTail1 (sites : List Site) : Solcore.Core.Expr :=
  .letE (.caseE (.apply (.var 9) (.word (Solcore.Core.Word.ofNatModulo 4)))
    (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0)) (logTail2 sites)

theorem contractExpression_toCore (stepBody : Solcore.Core.Wire.Expr) (sites : List Site) :
    (contractExpression stepBody sites).toCore = .letE stepBody.toCore (logTail1 sites) := by
  rw [contractExpression_eq]
  simp only [Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore, logTail1, logTail2,
    logTail3, logTail4, logTail5, logTail6, logTail7, logTail8]

/-- The nine binders before the first site, innermost first: both Unit
writes, the result, the base, the counter, the old slot, the input, the flags
and the step closure. -/
def siteBase (closure : Solcore.Core.Value)
    (flags input old counter base result : Solcore.Core.Word) : Solcore.Core.Environment :=
  [.unit, .unit, .word result, .word base, .word counter, .word old, .word input, .word flags,
    closure]

theorem replicate_unit_get (count index : Nat) (rest : Solcore.Core.Environment) :
    (List.replicate count Solcore.Core.Value.unit ++ rest)[count + index]? = rest[index]? := by
  rw [List.getElem?_append_right (by simp)]
  simp

/-- Record word logs in order. -/
def recordWords (inputs : HostStorageDriver.ExecutionInputs) :
    TransactionHostStorageDriver.Context → List (Solcore.Core.Word × Solcore.Core.Word) →
      TransactionHostStorageDriver.Context
  | context, [] => context
  | context, (topic, payload) :: rest =>
      recordWords inputs
        (context.recordLog (TransactionHostStorageDriver.wordLog inputs topic payload)) rest

/-- Tags paired with their payload words. -/
def tagPairs (tags : List Nat) (words : List Solcore.Core.Word) :
    List (Solcore.Core.Word × Solcore.Core.Word) :=
  List.zipWith (fun tag word => (Solcore.Core.Word.ofNatModulo tag, word)) tags words

/-- A record's payload evaluates to `word` where the record is bound, after any
number of further Unit binders. -/
def PayloadStable (store : Solcore.Core.Store) (payload : Nat → Solcore.Core.Wire.Expr)
    (word : Solcore.Core.Word) (depth : Nat) (environment : Solcore.Core.Environment) : Prop :=
  ∀ count, Solcore.Core.Evaluates (List.replicate count .unit ++ environment) store
    (payload (depth + count)).toCore (.word word) store

/-- Every record's payload is stable with its word. -/
def AllStable (store : Solcore.Core.Store) (depth : Nat) (environment : Solcore.Core.Environment) :
    List (Nat × (Nat → Solcore.Core.Wire.Expr)) → List Solcore.Core.Word → Prop
  | [], [] => True
  | record :: records, word :: words =>
      PayloadStable store record.2 word depth environment ∧
        AllStable store depth environment records words
  | _, _ => False

theorem PayloadStable.shift {store : Solcore.Core.Store} {payload : Nat → Solcore.Core.Wire.Expr}
    {word : Solcore.Core.Word} {depth : Nat} {environment : Solcore.Core.Environment}
    (stable : PayloadStable store payload word depth environment) :
    PayloadStable store payload word (depth + 1) (.unit :: environment) := by
  intro count
  have shifted := stable (count + 1)
  rw [List.replicate_succ', List.append_assoc, List.singleton_append,
    show depth + (count + 1) = depth + 1 + count by omega] at shifted
  exact shifted

theorem AllStable.shift {store : Solcore.Core.Store} {depth : Nat}
    {environment : Solcore.Core.Environment} :
    ∀ {records : List (Nat × (Nat → Solcore.Core.Wire.Expr))} {words : List Solcore.Core.Word},
    AllStable store depth environment records words →
    AllStable store (depth + 1) (.unit :: environment) records words
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨first, rest⟩ => ⟨first.shift, AllStable.shift rest⟩

theorem AllStable.append {store : Solcore.Core.Store} {depth : Nat}
    {environment : Solcore.Core.Environment} :
    ∀ {first : List (Nat × (Nat → Solcore.Core.Wire.Expr))}
      {firstWords : List Solcore.Core.Word}
      {second : List (Nat × (Nat → Solcore.Core.Wire.Expr))}
      {secondWords : List Solcore.Core.Word},
    AllStable store depth environment first firstWords →
    AllStable store depth environment second secondWords →
    AllStable store depth environment (first ++ second) (firstWords ++ secondWords)
  | [], [], _, _, _, rest => rest
  | _ :: _, _ :: _, _, _, ⟨head, tail⟩, rest => ⟨head, AllStable.append tail rest⟩

theorem AllStable.map {store : Solcore.Core.Store} {depth : Nat}
    {environment : Solcore.Core.Environment} {α : Type}
    (record : α → Nat × (Nat → Solcore.Core.Wire.Expr)) (word : α → Solcore.Core.Word) :
    ∀ (items : List α), (∀ item ∈ items,
      PayloadStable store (record item).2 (word item) depth environment) →
    AllStable store depth environment (items.map record) (items.map word)
  | [], _ => trivial
  | item :: rest, stable =>
      ⟨stable item (by simp), AllStable.map record word rest
        (fun other mem => stable other (by simp [mem]))⟩

/-- **A frame's records, as a handled host path.** Each record applies the
log host function to its tag and payload; the handler appends the attributed
word log to the working journal, and the records end with Unit. -/
theorem emitRecords_handled {inputs : HostStorageDriver.ExecutionInputs}
    {continuation : List Solcore.Core.Frame} {store : Solcore.Core.Store} :
    ∀ (records : List (Nat × (Nat → Solcore.Core.Wire.Expr))) (words : List Solcore.Core.Word)
      (depth : Nat) (environment : Solcore.Core.Environment)
      (context : TransactionHostStorageDriver.Context),
    environment[13 + depth]? = some (.hostFunction .emitLogWord) →
    AllStable store depth environment records words →
    ∃ steps, HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
      ⟨.eval (emitRecords depth records).toCore environment, continuation, store⟩
      (recordWords inputs context (tagPairs (records.map Prod.fst) words))
      ⟨.ret .unit, continuation, store⟩
  | [], [], depth, environment, context, _, _ => by
      rw [emitRecords_nil]
      simp only [Solcore.Core.Wire.Expr.toCore]
      exact ⟨_, .core (.cons (.core .unit) .refl)⟩
  | (tag, payload) :: records, word :: words, depth, environment, context, hostAt,
      ⟨first, rest⟩ => by
      have hostAt' : (Solcore.Core.Value.unit :: environment)[13 + (depth + 1)]? =
          some (.hostFunction .emitLogWord) := by
        rw [show 13 + (depth + 1) = (13 + depth) + 1 by omega]
        simpa using hostAt
      obtain ⟨_, tail⟩ := emitRecords_handled (continuation := continuation) records words
        (depth + 1) (.unit :: environment)
        (context.recordLog (TransactionHostStorageDriver.wordLog inputs
          (Solcore.Core.Word.ofNatModulo tag) word)) hostAt' rest.shift
      have payloadEval : Solcore.Core.Evaluates environment store (payload depth).toCore
          (.word word) store := by
        simpa using first 0
      obtain ⟨_, applyPath⟩ := hostSteps_apply
        (continuation := .letBody (emitRecords (depth + 1) records).toCore environment ::
          continuation) hostAt (.pair .word payloadEval)
      rw [emitRecords_cons]
      simp only [Solcore.Core.Wire.Expr.toCore]
      exact ⟨_, .handle (.cons (.core .enterLet) applyPath) .emitLogWord rfl rfl
        ((HostDriver.HandledSteps.core (.cons (.core .bindLet) .refl)).trans tail)⟩

/-- Whether a site's guard bit is set in the flags. -/
def siteEnabled (flags : Solcore.Core.Word) (site : Site) : Bool :=
  flags.bitAnd (Solcore.Core.Word.ofNatModulo (2 ^ site.guard)) ==
    Solcore.Core.Word.ofNatModulo (2 ^ site.guard)

/-- The tags of a site's frame. -/
def frameTags (site : Site) : List Nat :=
  [headerTag site] ++ ((List.range site.dataWords).map fun index => dataTag (index + 1)) ++
    ((List.range site.topics).map fun index => topicTag (index + 1))

/-- The payload words of a site's frame for its value and the result. -/
def frameWords (site : Site) (value result : Solcore.Core.Word) : List Solcore.Core.Word :=
  [Solcore.Core.Word.ofNatModulo 0] ++
    ((List.range site.dataWords).map fun index => if index = 0 then value else result) ++
    ((List.range site.topics).map fun index =>
      value.add (Solcore.Core.Word.ofNatModulo (index + 1)))

theorem frame_tags (site : Site) (value : Nat) :
    (frame site value).map Prod.fst = frameTags site := by
  simp [frame_eq, frameTags, Function.comp_def]

/-- The frame's payloads at a site of the given depth, whose value is bound
innermost and whose environment holds the result `depth - 7` binders in. -/
theorem frame_stable {store : Solcore.Core.Store} {value result : Solcore.Core.Word}
    (site : Site) (depth : Nat) (environment : Solcore.Core.Environment)
    (resultAt : environment[depth - 7]? = some (.word result)) (enough : 7 ≤ depth) :
    AllStable store (depth + 1) (.word value :: environment) (frame site depth)
      (frameWords site value result) := by
  have valueStable : ∀ count, Solcore.Core.Evaluates
      (List.replicate count .unit ++ Solcore.Core.Value.word value :: environment) store
      (.var (depth + 1 + count - 1 - depth)) (.word value) store := by
    intro count
    rw [show depth + 1 + count - 1 - depth = count + 0 by omega]
    exact .var (by rw [replicate_unit_get]; rfl)
  rw [frame_eq]
  unfold frameWords
  refine AllStable.append (AllStable.append ⟨fun count => by
      simp only [Solcore.Core.Wire.Expr.toCore]
      exact .word, trivial⟩ ?_) ?_
  · apply AllStable.map
    intro index _
    intro count
    by_cases zero : index = 0
    · simp only [zero, if_true, Solcore.Core.Wire.Expr.toCore]
      exact valueStable count
    · simp only [zero, if_false, Solcore.Core.Wire.Expr.toCore]
      rw [show depth + 1 + count - 1 - 6 = count + (depth - 6) by omega]
      refine .var ?_
      rw [replicate_unit_get, show depth - 6 = (depth - 7) + 1 by omega]
      simpa using resultAt
  · apply AllStable.map
    intro index _
    intro count
    simp only [Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore]
    exact .binary (valueStable count) .word rfl

/-- The context after one site: unchanged when its guard bit is clear, and
with its frame's word logs appended otherwise. -/
def siteContext (inputs : HostStorageDriver.ExecutionInputs)
    (f : Solcore.Core.Word → Solcore.Core.Word)
    (flags result : Solcore.Core.Word) (context : TransactionHostStorageDriver.Context)
    (site : Site) : TransactionHostStorageDriver.Context :=
  if siteEnabled flags site then
    recordWords inputs context (tagPairs (frameTags site)
      (frameWords site (f (result.add (Solcore.Core.Word.ofNatModulo site.guard))) result))
  else context

/-- **One site, as a handled host path.** A site whose guard bit is clear does
nothing; otherwise it applies the step to `result + guard` and emits its
frame. -/
theorem site_handled {inputs : HostStorageDriver.ExecutionInputs}
    {continuation : List Solcore.Core.Frame} {parameterType resultType : Solcore.Core.Ty}
    {body : Solcore.Core.Expr} {captured : Solcore.Core.Environment}
    (f : Solcore.Core.Word → Solcore.Core.Word)
    (applies : ∀ argument store, ∃ store', Solcore.Core.Evaluates (.word argument :: captured)
      store body (.word (f argument)) store')
    (site : Site) (depth : Nat) (environment : Solcore.Core.Environment)
    (flags result : Solcore.Core.Word) (context : TransactionHostStorageDriver.Context)
    (store : Solcore.Core.Store) (enough : 7 ≤ depth)
    (flagsAt : environment[depth - 1 - 1]? = some (.word flags))
    (stepAt : environment[depth - 1 - 0]? =
      some (.closure parameterType resultType body captured))
    (resultAt : environment[depth - 1 - 6]? = some (.word result))
    (hostAt : environment[13 + depth]? = some (.hostFunction .emitLogWord)) :
    ∃ store' steps, HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps
      context ⟨.eval (siteExpression depth site).toCore environment, continuation, store⟩
      (siteContext inputs f flags result context site) ⟨.ret .unit, continuation, store'⟩ := by
  have condition : Solcore.Core.Evaluates environment store
      (.binary .wordEq (.binary .wordAnd (.var (depth - 1 - 1))
        (.word (Solcore.Core.Word.ofNatModulo (2 ^ site.guard))))
        (.word (Solcore.Core.Word.ofNatModulo (2 ^ site.guard))))
      (.bool (siteEnabled flags site)) store :=
    .binary (.binary (.var flagsAt) .word rfl) .word rfl
  rw [siteExpression_eq]
  simp only [Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore]
  unfold siteContext
  cases enabled : siteEnabled flags site
  · rw [enabled] at condition
    obtain ⟨_, path⟩ := hostSteps_eval (continuation := continuation) (.ifFalse condition .unit)
      ⟨0, .refl⟩
    exact ⟨store, _, .core path⟩
  · rw [enabled] at condition
    let argument := result.add (Solcore.Core.Word.ofNatModulo site.guard)
    obtain ⟨store', bodyEval⟩ := applies argument store
    have applied : Solcore.Core.Evaluates environment store
        (.apply (.var (depth - 1 - 0)) (.binary .wordAdd (.var (depth - 1 - 6))
          (.word (Solcore.Core.Word.ofNatModulo site.guard)))) (.word (f argument)) store' :=
      .apply (.var stepAt) (.binary (.var resultAt) .word rfl) bodyEval
    have hostAt' : (Solcore.Core.Value.word (f argument) :: environment)[13 + (depth + 1)]? =
        some (.hostFunction .emitLogWord) := by
      rw [show 13 + (depth + 1) = (13 + depth) + 1 by omega]
      simpa using hostAt
    have resultAt' : environment[depth - 7]? = some (.word result) := by
      rw [show depth - 7 = depth - 1 - 6 by omega]
      exact resultAt
    obtain ⟨_, records⟩ := emitRecords_handled (inputs := inputs) (continuation := continuation)
      (frame site depth) (frameWords site (f argument) result) (depth + 1)
      (.word (f argument) :: environment) context hostAt'
      (frame_stable site depth environment resultAt' enough)
    rw [frame_tags] at records
    obtain ⟨_, enter⟩ := hostSteps_cons (finish := ⟨.eval (.letE
        (.apply (.var (depth - 1 - 0)) (.binary .wordAdd (.var (depth - 1 - 6))
          (.word (Solcore.Core.Word.ofNatModulo site.guard))))
        (emitRecords (depth + 1) (frame site depth)).toCore) environment, continuation, store⟩)
      .enterIf (hostSteps_eval condition (hostSteps_cons .chooseTrue ⟨0, .refl⟩))
    obtain ⟨_, bind⟩ := hostSteps_cons (finish := ⟨.eval (emitRecords (depth + 1)
        (frame site depth)).toCore (.word (f argument) :: environment), continuation, store'⟩)
      .enterLet (hostSteps_eval applied (hostSteps_cons .bindLet ⟨0, .refl⟩))
    exact ⟨store', _, (HostDriver.HandledSteps.core (enter.trans bind)).trans records⟩

/-- The context after the sites, in order. -/
def sitesContext (inputs : HostStorageDriver.ExecutionInputs)
    (f : Solcore.Core.Word → Solcore.Core.Word) (flags result : Solcore.Core.Word) :
    TransactionHostStorageDriver.Context → List Site → TransactionHostStorageDriver.Context
  | context, [] => context
  | context, site :: rest =>
      sitesContext inputs f flags result (siteContext inputs f flags result context site) rest

/-- **The sites and the completion, as a handled host path.** After `done`
sites, each site binds Unit; the completion selects the outcome by the flags'
low bit with the result as payload. -/
theorem sites_handled {inputs : HostStorageDriver.ExecutionInputs}
    {parameterType resultType : Solcore.Core.Ty} {body : Solcore.Core.Expr}
    {captured : Solcore.Core.Environment} (f : Solcore.Core.Word → Solcore.Core.Word)
    (applies : ∀ argument store, ∃ store', Solcore.Core.Evaluates (.word argument :: captured)
      store body (.word (f argument)) store')
    (flags input old counter base result : Solcore.Core.Word) :
    ∀ (sites : List Site) (done : Nat) (context : TransactionHostStorageDriver.Context)
      (store : Solcore.Core.Store),
    ∃ store' steps, HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps
      context ⟨.eval (withSites (done + 9) sites).toCore
        (List.replicate done .unit ++ (siteBase (.closure parameterType resultType body captured)
          flags input old counter base result ++ Solcore.Core.hostEnvironment)), [], store⟩
      (sitesContext inputs f flags result context sites)
      (Solcore.Core.State.final (rollbackValue (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
        Solcore.Core.Word.ofNatModulo 1) result) store')
  | [], done, context, store => by
      let environment : Solcore.Core.Environment := List.replicate done .unit ++
        (siteBase (.closure parameterType resultType body captured) flags input old counter base
          result ++ Solcore.Core.hostEnvironment)
      have flagsAt : environment[done + 9 - 1 - 1]? = some (.word flags) := by
        rw [show done + 9 - 1 - 1 = done + 7 by omega, replicate_unit_get]
        rfl
      have resultAt : environment[done + 9 - 1 - 6]? = some (.word result) := by
        rw [show done + 9 - 1 - 6 = done + 2 by omega, replicate_unit_get]
        rfl
      have condition : Solcore.Core.Evaluates environment store
          (.binary .wordEq (.binary .wordAnd (.var (done + 9 - 1 - 1))
            (.word (Solcore.Core.Word.ofNatModulo 1))) (.word (Solcore.Core.Word.ofNatModulo 1)))
          (.bool (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
            Solcore.Core.Word.ofNatModulo 1)) store :=
        .binary (.binary (.var flagsAt) .word rfl) .word rfl
      rw [withSites_nil]
      simp only [Solcore.Core.Wire.Expr.toCore, Solcore.Core.Wire.BinaryOp.toCore,
        Solcore.Core.Wire.Ty.toCore]
      unfold rollbackValue
      cases flag : (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
          Solcore.Core.Word.ofNatModulo 1)
      · rw [flag] at condition
        obtain ⟨_, path⟩ := hostSteps_eval (continuation := [])
          (.ifFalse condition (.inLeft (.var resultAt))) ⟨0, .refl⟩
        exact ⟨store, _, .core path⟩
      · rw [flag] at condition
        obtain ⟨_, path⟩ := hostSteps_eval (continuation := [])
          (.ifTrue condition (.inRight (.inLeft (.var resultAt)))) ⟨0, .refl⟩
        exact ⟨store, _, .core path⟩
  | site :: rest, done, context, store => by
      let environment : Solcore.Core.Environment := List.replicate done .unit ++
        (siteBase (.closure parameterType resultType body captured) flags input old counter base
          result ++ Solcore.Core.hostEnvironment)
      have flagsAt : environment[done + 9 - 1 - 1]? = some (.word flags) := by
        rw [show done + 9 - 1 - 1 = done + 7 by omega, replicate_unit_get]
        rfl
      have stepAt : environment[done + 9 - 1 - 0]? =
          some (.closure parameterType resultType body captured) := by
        rw [show done + 9 - 1 - 0 = done + 8 by omega, replicate_unit_get]
        rfl
      have resultAt : environment[done + 9 - 1 - 6]? = some (.word result) := by
        rw [show done + 9 - 1 - 6 = done + 2 by omega, replicate_unit_get]
        rfl
      have hostAt : environment[13 + (done + 9)]? = some (.hostFunction .emitLogWord) := by
        rw [show 13 + (done + 9) = done + 22 by omega, replicate_unit_get]
        rfl
      obtain ⟨store1, _, sitePath⟩ := site_handled (inputs := inputs)
        (continuation := [.letBody (withSites (done + 9 + 1) rest).toCore environment]) f applies
        site (done + 9) environment flags result context store (by omega) flagsAt stepAt resultAt
        hostAt
      obtain ⟨store2, _, restPath⟩ := sites_handled f applies flags input old counter base
        result rest (done + 1) (siteContext inputs f flags result context site) store1
      rw [withSites_cons]
      simp only [Solcore.Core.Wire.Expr.toCore]
      rw [show done + 9 + 1 = done + 1 + 9 by omega] at sitePath ⊢
      exact ⟨store2, _, (HostDriver.HandledSteps.core (.cons (.core .enterLet) .refl)).trans
        (sitePath.trans ((HostDriver.HandledSteps.core (.cons (.core .bindLet) .refl)).trans
          restPath))⟩

/-- The step's result for the input plus slot zero. -/
def logResult (context : TransactionHostStorageDriver.Context)
    (f : Solcore.Core.Word → Solcore.Core.Word) (input : Solcore.Core.Word) : Solcore.Core.Word :=
  f (input.add (context.readStorage (Solcore.Core.Word.ofNatModulo 0)))

/-- The context after both writes: the result in slot zero, then the counter
plus one in slot one. -/
def logWritten (context : TransactionHostStorageDriver.Context)
    (f : Solcore.Core.Word → Solcore.Core.Word) (input : Solcore.Core.Word) :
    TransactionHostStorageDriver.Context :=
  (context.writeStorage (Solcore.Core.Word.ofNatModulo 0) (logResult context f input)).writeStorage
    (Solcore.Core.Word.ofNatModulo 1)
    ((context.readStorage (Solcore.Core.Word.ofNatModulo 1)).add (Solcore.Core.Word.ofNatModulo 1))

/-- **The event-log reference's transaction, as a handled host path.** From
the initial state, the wrapper reads the flags and the input, reads both
slots, applies the step, writes both slots, runs the sites in order and ends
with the outcome value of the result. -/
theorem log_handled {inputs : HostStorageDriver.ExecutionInputs}
    {context : TransactionHostStorageDriver.Context} {step : Solcore.Core.Expr}
    {parameterType resultType : Solcore.Core.Ty} {body : Solcore.Core.Expr}
    {captured : Solcore.Core.Environment} {flags input : Solcore.Core.Word}
    (f : Solcore.Core.Word → Solcore.Core.Word) (sites : List Site)
    (stepEvaluates : Solcore.Core.Evaluates Solcore.Core.hostEnvironment [] step
      (.closure parameterType resultType body captured) [])
    (applies : ∀ argument store, ∃ store', Solcore.Core.Evaluates (.word argument :: captured)
      store body (.word (f argument)) store')
    (flagsDecoded : inputs.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 4) = some flags)
    (inputDecoded : inputs.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 36) = some input) :
    ∃ store steps, HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps
      context
      (Solcore.Core.State.initial (.letE step (logTail1 sites)) Solcore.Core.hostEnvironment)
      (sitesContext inputs f flags (logResult context f input) (logWritten context f input) sites)
      (Solcore.Core.State.final (rollbackValue (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
        Solcore.Core.Word.ofNatModulo 1) (logResult context f input)) store) := by
  let closure : Solcore.Core.Value := .closure parameterType resultType body captured
  let old := context.readStorage (Solcore.Core.Word.ofNatModulo 0)
  let counter := context.readStorage (Solcore.Core.Word.ofNatModulo 1)
  let base := input.add old
  let result := f base
  let environment1 : Solcore.Core.Environment := closure :: Solcore.Core.hostEnvironment
  let environment2 : Solcore.Core.Environment := .word flags :: environment1
  let environment3 : Solcore.Core.Environment := .word input :: environment2
  let environment4 : Solcore.Core.Environment := .word old :: environment3
  let environment5 : Solcore.Core.Environment := .word counter :: environment4
  let environment6 : Solcore.Core.Environment := .word base :: environment5
  let environment7 : Solcore.Core.Environment := .word result :: environment6
  let environment8 : Solcore.Core.Environment := .unit :: environment7
  let first : TransactionHostStorageDriver.Context :=
    context.writeStorage (Solcore.Core.Word.ofNatModulo 0) result
  obtain ⟨store1, bodyEval⟩ := applies base []
  have applied : Solcore.Core.Evaluates environment6 [] (.apply (.var 5) (.var 0))
      (.word result) store1 :=
    .apply (.var rfl) (.var rfl) bodyEval
  obtain ⟨store2, _, sitesPath⟩ := sites_handled (inputs := inputs) f applies flags input old
    counter base result sites 0 (logWritten context f input) store1
  refine ⟨store2, ?_⟩
  have afterSecond : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps
        (logWritten context f input)
        ⟨.ret .unit, [.letBody (withSites 9 sites).toCore environment8], store1⟩
        (sitesContext inputs f flags result (logWritten context f input) sites)
        (Solcore.Core.State.final (rollbackValue (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
          Solcore.Core.Word.ofNatModulo 1) result) store2) :=
    ⟨_, (HostDriver.HandledSteps.core (.cons (.core .bindLet) .refl)).trans sitesPath⟩
  have secondWrite : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps first
        ⟨.ret .unit, [.letBody (logTail8 sites) environment7], store1⟩
        (sitesContext inputs f flags result (logWritten context f input) sites)
        (Solcore.Core.State.final (rollbackValue (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
          Solcore.Core.Word.ofNatModulo 1) result) store2) :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_apply (index := 9) rfl (.pair .word (.binary (.var rfl) .word rfl)))))
      .storageWrite rfl rfl afterSecond
  have firstWrite : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.word counter), [.letBody (logTail5 sites) environment4], []⟩
        (sitesContext inputs f flags result (logWritten context f input) sites)
        (Solcore.Core.State.final (rollbackValue (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
          Solcore.Core.Word.ofNatModulo 1) result) store2) :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_eval (.binary (.var rfl) (.var rfl) rfl) (hostSteps_cons .bindLet
        (hostSteps_cons .enterLet (hostSteps_eval applied (hostSteps_cons .bindLet
          (hostSteps_cons .enterLet (hostSteps_apply (index := 8) rfl
            (.pair .word (.var rfl)))))))))))
      .storageWrite rfl rfl secondWrite
  have counterLoad : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.word old), [.letBody (logTail4 sites) environment3], []⟩
        (sitesContext inputs f flags result (logWritten context f input) sites)
        (Solcore.Core.State.final (rollbackValue (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
          Solcore.Core.Word.ofNatModulo 1) result) store2) :=
    handledSteps_request (hostSteps_cons .bindLet (hostSteps_cons .enterLet
      (hostSteps_apply (index := 4) rfl .word))) .storageRead rfl rfl firstWrite
  have oldLoad : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.inRight .unit (.word input)),
          [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment2,
            .letBody (logTail3 sites) environment2], []⟩
        (sitesContext inputs f flags result (logWritten context f input) sites)
        (Solcore.Core.State.final (rollbackValue (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
          Solcore.Core.Word.ofNatModulo 1) result) store2) :=
    handledSteps_request (hostSteps_cons .chooseRight (hostSteps_cons (.var rfl)
      (hostSteps_cons .bindLet (hostSteps_cons .enterLet
        (hostSteps_apply (index := 3) rfl .word))))) .storageRead rfl rfl counterLoad
  have inputResumed : (TransactionHostStorageDriver.handler inputs).handleSuspension context
      ⟨.inputDataWordBE? (Solcore.Core.Word.ofNatModulo 36),
        [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment2,
          .letBody (logTail3 sites) environment2], []⟩ =
      (context, ⟨.ret (.inRight .unit (.word input)),
        [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment2,
          .letBody (logTail3 sites) environment2], []⟩) := by
    rw [handleSuspension_inputDataWordBE, inputDecoded]
    rfl
  have inputLoad : ∃ steps,
      HostDriver.HandledSteps (TransactionHostStorageDriver.handler inputs) steps context
        ⟨.ret (.inRight .unit (.word flags)),
          [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment1,
            .letBody (logTail2 sites) environment1], []⟩
        (sitesContext inputs f flags result (logWritten context f input) sites)
        (Solcore.Core.State.final (rollbackValue (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
          Solcore.Core.Word.ofNatModulo 1) result) store2) :=
    handledSteps_request (hostSteps_cons .chooseRight (hostSteps_cons (.var rfl)
      (hostSteps_cons .bindLet (hostSteps_cons .enterLet (hostSteps_cons .enterCase
        (hostSteps_apply (index := 10) rfl .word)))))) .inputDataWordBE? rfl inputResumed oldLoad
  have flagsResumed : (TransactionHostStorageDriver.handler inputs).handleSuspension context
      ⟨.inputDataWordBE? (Solcore.Core.Word.ofNatModulo 4),
        [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment1,
          .letBody (logTail2 sites) environment1], []⟩ =
      (context, ⟨.ret (.inRight .unit (.word flags)),
        [.caseBranches (.word (Solcore.Core.Word.ofNatModulo 0)) (.var 0) environment1,
          .letBody (logTail2 sites) environment1], []⟩) := by
    rw [handleSuspension_inputDataWordBE, flagsDecoded]
    rfl
  exact handledSteps_request (hostSteps_cons .enterLet (hostSteps_eval stepEvaluates
    (hostSteps_cons .bindLet (hostSteps_cons .enterLet (hostSteps_cons .enterCase
      (hostSteps_apply (index := 9) rfl .word)))))) .inputDataWordBE? rfl flagsResumed inputLoad

/-! ### The source method -/

theorem Context.withMemory_call_mload (context : Context) (memory : Memory) (offset : Nat) :
    (context.withMemory memory).call "mload" [.word offset] =
      memoryLoadMeaning memory [.word offset] := by
  simp [Context.withMemory, Context.call]

theorem Context.withMemory_call_other (context : Context) (memory : Memory)
    {callee : String} (different : callee ≠ "mload") (arguments : List Value) :
    (context.withMemory memory).call callee arguments = context.call callee arguments := by
  have notMload : ("mload" == callee) = false := by
    simp only [beq_eq_false_iff_ne]
    exact fun same => different same.symm
  simp only [Context.withMemory, Context.call, List.find?_cons, notMload]

theorem Context.withStorage_opcode (context : Context) (storage : Storage) {callee : String}
    (different : callee ≠ "sload") :
    (context.withStorage storage).opcode? callee = context.opcode? callee := by
  have notSload : ("sload" == callee) = false := by
    simp only [beq_eq_false_iff_ne]
    exact fun same => different same.symm
  simp only [Context.withStorage, Context.opcode?, List.find?_cons, notSload]

theorem Context.withMemory_opcode (context : Context) (memory : Memory) {callee : String}
    (different : callee ≠ "mload") :
    (context.withMemory memory).opcode? callee = context.opcode? callee := by
  have notMload : ("mload" == callee) = false := by
    simp only [beq_eq_false_iff_ne]
    exact fun same => different same.symm
  simp only [Context.withMemory, Context.opcode?, List.find?_cons, notMload]

theorem Memory.store_same (memory : Memory) (offset value : Nat) :
    memory.store offset value offset = some value := by
  simp [Memory.store]

theorem Memory.store_apart (memory : Memory) {offset other : Nat} (value : Nat)
    (apart : other + 32 ≤ offset ∨ offset + 32 ≤ other) :
    memory.store offset value other = memory other := by
  have different : other ≠ offset := by omega
  simp [Memory.store, different, apart]

theorem siteValue_ne (site : Site) {name : String}
    (other : name = "sc_flags" ∨ name = "sc_result" ∨ name = "sc_ptr" ∨ name = "sc_step") :
    siteValue site ≠ name := by
  intro same
  have chars := congrArg String.toList same
  rcases other with rfl | rfl | rfl | rfl <;> simp [siteValue] at chars

theorem logAlias_ne (topics : Nat) {name : String} (other : name = "sload" ∨ name = "mload") :
    EventLog.logAlias topics ≠ name := by
  intro same
  have chars := congrArg String.toList same
  rcases other with rfl | rfl <;> simp [EventLog.logAlias] at chars

/-- The words of a site's topics, `value + 1` to `value + count`. -/
theorem topics_words (context : Context) (frames : Frames) (name : String)
    (value : Solcore.Core.Word) (found : frames.lookup name = some (.word value.val)) :
    ∀ (indices : List Nat), (∀ index ∈ indices, index + 1 < Evm.modulus) →
    Operand.words? context frames (indices.map fun index =>
        .operation .add (.name name) (.number (index + 1))) =
      some (indices.map fun index => (value.add (Solcore.Core.Word.ofNatModulo (index + 1))).val)
  | [], _ => rfl
  | index :: rest, small => by
      have head : index + 1 < Evm.modulus := small index (by simp)
      have tail := topics_words context frames name value found rest
        (fun other mem => small other (by simp [mem]))
      have sum : Evm.add value.val (index + 1) =
          (value.add (Solcore.Core.Word.ofNatModulo (index + 1))).val := by
        have := evm_add value (Solcore.Core.Word.ofNatModulo (index + 1))
        rwa [ofNatModulo_val_small head] at this
      simp [Operand.words?, Operand.word?, Operand.expr, Expr.eval, found, head, BinaryOp.apply,
        sum, tail]

/-- The log a site emits for its step value and the result. -/
def siteLog (site : Site) (value result : Solcore.Core.Word) : SourceLog where
  topics := (List.range site.topics).map fun index =>
    (value.add (Solcore.Core.Word.ofNatModulo (index + 1))).val
  data := (List.range site.dataWords).map fun index => if index = 0 then value.val else result.val

/-- A site's guard bit, read as the source does. -/
theorem site_flag (flags : Solcore.Core.Word) (site : Site) (small : 2 ^ site.guard < Evm.modulus) :
    toBool (Evm.eq (Evm.and flags.val (2 ^ site.guard)) (2 ^ site.guard)) =
      siteEnabled flags site := by
  have conjunction := evm_and flags (Solcore.Core.Word.ofNatModulo (2 ^ site.guard))
  have equality := evm_eq (flags.bitAnd (Solcore.Core.Word.ofNatModulo (2 ^ site.guard)))
    (Solcore.Core.Word.ofNatModulo (2 ^ site.guard))
  rw [ofNatModulo_val_small small] at conjunction equality
  rw [conjunction]
  exact equality

/-- **One site in the source.** A site whose guard bit is clear does nothing;
otherwise it binds the step's value for `result + guard`, writes its data
Words to the buffer at `sc_ptr` and emits its log. -/
theorem siteStmt_run (context : Context) (storage : Storage) (frames : Frames)
    (f : Solcore.Core.Word → Solcore.Core.Word) (flags result : Solcore.Core.Word) (pointer : Nat)
    (stepCall : ∀ argument : Solcore.Core.Word,
      context.call "sc_step" [.word argument.val] = some (.word (f argument).val))
    (flagsAt : frames.lookup "sc_flags" = some (.word flags.val))
    (resultAt : frames.lookup "sc_result" = some (.word result.val))
    (pointerAt : frames.lookup "sc_ptr" = some (.word pointer))
    (room : pointer + 64 ≤ Evm.modulus) (site : Site) (memory : Memory) (logs : List SourceLog)
    (valid : 1 ≤ site.guard ∧ site.guard ≤ 3 ∧ site.topics ≤ 4 ∧ site.dataWords ≤ 2)
    (logger : context.opcode? (EventLog.logAlias site.topics) =
      some ("log" ++ toString site.topics)) :
    ∃ memory', (siteStmt site).exec context storage memory logs frames =
      some (.next storage memory' (logs ++ if siteEnabled flags site then
        [siteLog site (f (result.add (Solcore.Core.Word.ofNatModulo site.guard))) result]
        else []) frames) := by
  obtain ⟨_, guardHigh, topicsBound, dataBound⟩ := valid
  have maskSmall : 2 ^ site.guard < Evm.modulus :=
    Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) guardHigh) (by decide)
  have guardSmall : site.guard < Evm.modulus := Nat.lt_of_le_of_lt guardHigh (by decide)
  have pointerLe : pointer ≤ Evm.modulus := by omega
  have pointerNext : pointer + 32 < Evm.modulus := by omega
  have pointerFits : pointer + 32 ≤ Evm.modulus := by omega
  have nextFits : pointer + 32 + 32 ≤ Evm.modulus := by omega
  have zeroSmall : 0 < Evm.modulus := by decide
  have thirtyTwoSmall : 32 < Evm.modulus := by decide
  have sixtyFourSmall : 64 < Evm.modulus := by decide
  have condition : (Expr.binary .eq (.binary .bitAnd (.name "sc_flags") (.number (2 ^ site.guard)))
      (.number (2 ^ site.guard))).eval ((context.withMemory memory).withStorage storage) frames =
      some (.bool (siteEnabled flags site)) := by
    simp [Expr.eval, flagsAt, maskSmall, BinaryOp.apply, site_flag flags site maskSmall]
  unfold siteStmt
  simp only [LogStmt.exec]
  rw [condition]
  cases enabled : siteEnabled flags site
  · exact ⟨memory, by simp⟩
  · let argument := result.add (Solcore.Core.Word.ofNatModulo site.guard)
    have argumentVal : Evm.add result.val site.guard = argument.val := by
      have := evm_add result (Solcore.Core.Word.ofNatModulo site.guard)
      rwa [ofNatModulo_val_small guardSmall] at this
    have stepped : ∀ current : Memory, ((context.withMemory current).withStorage storage).call
        "sc_step" [.word argument.val] = some (.word (f argument).val) := by
      intro current
      rw [Context.withStorage_call_other _ _ (by decide),
        Context.withMemory_call_other _ _ (by decide)]
      exact stepCall argument
    have valuePtr : siteValue site ≠ "sc_ptr" := siteValue_ne site (by simp)
    have valueResult : siteValue site ≠ "sc_result" := siteValue_ne site (by simp)
    have loggerNotSload : EventLog.logAlias site.topics ≠ "sload" := logAlias_ne _ (by simp)
    have loggerNotMload : EventLog.logAlias site.topics ≠ "mload" := logAlias_ne _ (by simp)
    have loggerFound : ∀ current : Memory,
        ((context.withMemory current).withStorage storage).opcode? (EventLog.logAlias site.topics) =
          some ("log" ++ toString site.topics) := by
      intro current
      rw [Context.withStorage_opcode _ _ loggerNotSload,
        Context.withMemory_opcode _ _ loggerNotMload]
      exact logger
    have topicsSmall : ∀ index ∈ List.range site.topics, index + 1 < Evm.modulus := by
      intro index mem
      have : index < site.topics := List.mem_range.mp mem
      exact Nat.lt_of_le_of_lt (show index + 1 ≤ 4 by omega) (by decide)
    have topicWords := fun current : Memory => topics_words
      ((context.withMemory current).withStorage storage)
      ([(siteValue site, .word (f argument).val)] :: frames) (siteValue site) (f argument)
      (by simp [Frames.lookup, Scope.get?]) (List.range site.topics) topicsSmall
    have dataCases : site.dataWords = 0 ∨ site.dataWords = 1 ∨ site.dataWords = 2 := by omega
    rcases dataCases with data | data | data
    · refine ⟨memory, ?_⟩
      simp [LogBlock.exec, LogBlock.binding, StorageStmt.exec, Stmt.exec, Expr.eval,
        Frames.lookup, Scope.get?, resultAt, guardSmall, BinaryOp.apply, argumentVal, stepped,
        LocalType.admits, Frames.declare, siteStores, data, storeWords, Operand.word?,
        Operand.expr, valuePtr, pointerAt, topicWords, emitLog, loggerFound, topicsBound,
        Memory.words, siteLog, argument, zeroSmall, pointerLe]
    · refine ⟨memory.store pointer (f argument).val, ?_⟩
      simp [LogBlock.exec, LogBlock.binding, StorageStmt.exec, Stmt.exec, Expr.eval,
        Frames.lookup, Scope.get?, resultAt, guardSmall, BinaryOp.apply, argumentVal, stepped,
        LocalType.admits, Frames.declare, siteStores, data, storeWords, storeWord, Operand.word?,
        Operand.expr, valuePtr, pointerAt, topicWords, emitLog, loggerFound, topicsBound,
        Memory.words, Memory.store_same, siteLog, argument, pointerFits, thirtyTwoSmall]
    · refine ⟨(memory.store pointer (f argument).val).store (pointer + 32) result.val, ?_⟩
      have nextVal : Evm.add pointer 32 = pointer + 32 := by
        simp [Evm.add, Nat.mod_eq_of_lt pointerNext]
      have kept : (memory.store pointer (f argument).val).store (pointer + 32) result.val pointer =
          some (f argument).val := by
        rw [Memory.store_apart _ _ (Or.inl (Nat.le_refl _)), Memory.store_same]
      simp [LogBlock.exec, LogBlock.binding, StorageStmt.exec, Stmt.exec, Expr.eval,
        Frames.lookup, Scope.get?, resultAt, guardSmall, BinaryOp.apply, argumentVal, stepped,
        LocalType.admits, Frames.declare, siteStores, data, storeWords, storeWord, Operand.word?,
        Operand.expr, valuePtr, valueResult, pointerAt, topicWords, emitLog, loggerFound,
        topicsBound, Memory.words, Memory.store_same, kept, siteLog, argument, nextVal,
        List.range_succ, pointerFits, nextFits, thirtyTwoSmall, sixtyFourSmall]

theorem LogStmt.execList_append (context : Context) :
    ∀ (storage : Storage) (memory : Memory) (logs : List SourceLog) (frames : Frames)
      (first second : List LogStmt),
    LogStmt.execList context storage memory logs frames (first ++ second) =
      match LogStmt.execList context storage memory logs frames first with
      | some (.next storage' memory' logs' frames') =>
          LogStmt.execList context storage' memory' logs' frames' second
      | other => other
  | storage, memory, logs, frames, [], second => by simp [LogStmt.execList]
  | storage, memory, logs, frames, statement :: rest, second => by
      simp only [List.cons_append, LogStmt.execList]
      split
      · rename_i storage' memory' logs' frames' _
        exact LogStmt.execList_append context storage' memory' logs' frames' rest second
      · rfl
      · rfl

/-- The logs of the enabled sites, in order. -/
def sitesLogs (f : Solcore.Core.Word → Solcore.Core.Word) (flags result : Solcore.Core.Word) :
    List Site → List SourceLog
  | [] => []
  | site :: rest =>
      (if siteEnabled flags site then
        [siteLog site (f (result.add (Solcore.Core.Word.ofNatModulo site.guard))) result]
        else []) ++ sitesLogs f flags result rest

/-- A site is valid and its logger names the wrapper for its topic count. -/
def SiteReady (context : Context) (site : Site) : Prop :=
  (1 ≤ site.guard ∧ site.guard ≤ 3 ∧ site.topics ≤ 4 ∧ site.dataWords ≤ 2) ∧
    context.opcode? (EventLog.logAlias site.topics) = some ("log" ++ toString site.topics)

theorem siteStmts_run (context : Context) (storage : Storage) (frames : Frames)
    (f : Solcore.Core.Word → Solcore.Core.Word) (flags result : Solcore.Core.Word) (pointer : Nat)
    (stepCall : ∀ argument : Solcore.Core.Word,
      context.call "sc_step" [.word argument.val] = some (.word (f argument).val))
    (flagsAt : frames.lookup "sc_flags" = some (.word flags.val))
    (resultAt : frames.lookup "sc_result" = some (.word result.val))
    (pointerAt : frames.lookup "sc_ptr" = some (.word pointer))
    (room : pointer + 64 ≤ Evm.modulus) :
    ∀ (sites : List Site) (memory : Memory) (logs : List SourceLog),
    (∀ site ∈ sites, SiteReady context site) →
    ∃ memory', LogStmt.execList context storage memory logs frames (sites.map siteStmt) =
      some (.next storage memory' (logs ++ sitesLogs f flags result sites) frames)
  | [], memory, logs, _ => ⟨memory, by simp [LogStmt.execList, sitesLogs]⟩
  | site :: rest, memory, logs, ready => by
      obtain ⟨valid, logger⟩ := ready site (by simp)
      obtain ⟨memory1, siteRun⟩ := siteStmt_run context storage frames f flags result pointer
        stepCall flagsAt resultAt pointerAt room site memory logs valid logger
      obtain ⟨memory2, restRun⟩ := siteStmts_run context storage frames f flags result pointer
        stepCall flagsAt resultAt pointerAt room rest memory1
        (logs ++ if siteEnabled flags site then
          [siteLog site (f (result.add (Solcore.Core.Word.ofNatModulo site.guard))) result]
          else [])
        (fun other mem => ready other (by simp [mem]))
      refine ⟨memory2, ?_⟩
      rw [List.map_cons, LogStmt.execList, siteRun]
      dsimp only
      rw [restRun, sitesLogs, List.append_assoc]

/-- The source storage after both writes. -/
def logStorage (storage : Storage) (result counter : Solcore.Core.Word) : Storage :=
  (storage.write 0 result.val).write 1 (counter.add (Solcore.Core.Word.ofNatModulo 1)).val

/-- The outcome the event-log method gives: the step's result for the input
plus slot zero, reverted for odd flags, and otherwise returned with the
written storage and the enabled sites' logs. -/
def logOutcome (storage : Storage) (f : Solcore.Core.Word → Solcore.Core.Word)
    (flags input old counter : Solcore.Core.Word) (sites : List Site) : LogOutcome :=
  if flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1 then
    .reverted (f (input.add old)).val
  else
    .returned (f (input.add old)).val (logStorage storage (f (input.add old)) counter)
      (sitesLogs f flags (f (input.add old)) sites)

/-- The method reads both slots, writes the step's result and the counter,
reserves 64 bytes from the free-memory pointer, runs the sites, and reverts
with or returns the result. -/
theorem logMethod_run (context : Context) (storage : Storage) (memory : Memory)
    (f : Solcore.Core.Word → Solcore.Core.Word) (sites : List Site)
    (flags input old counter : Solcore.Core.Word) (pointer : Nat)
    (stepCall : ∀ argument : Solcore.Core.Word,
      context.call "sc_step" [.word argument.val] = some (.word (f argument).val))
    (ready : ∀ site ∈ sites, SiteReady context site)
    (oldSlot : storage 0 = old.val) (counterSlot : storage 1 = counter.val)
    (free : memory 64 = some pointer) (room : pointer + 64 ≤ Evm.modulus) :
    (logMethod sites).run context storage memory [flags.val, input.val] =
      some (logOutcome storage f flags input old counter sites) := by
  let result := f (input.add old)
  have zeroSmall : 0 < Evm.modulus := by decide
  have thirtyTwoSmall : 32 < Evm.modulus := by decide
  have sixtyFourSmall : 64 < Evm.modulus := by decide
  have loadFits : 64 + 32 ≤ Evm.modulus := by decide
  have stepAt : ∀ (current : Memory) (written : Storage),
      ((context.withMemory current).withStorage written).call "sc_step"
        [.word (input.add old).val] = some (.word result.val) := by
    intro current written
    rw [Context.withStorage_call_other _ _ (by decide),
      Context.withMemory_call_other _ _ (by decide)]
    exact stepCall (input.add old)
  have loadAt : ∀ written : Storage,
      ((context.withMemory memory).withStorage written).call "mload" [.word 64] =
        some (.word pointer) := by
    intro written
    rw [Context.withStorage_call_other _ _ (by decide), Context.withMemory_call_mload]
    simp [memoryLoadMeaning, loadFits, free]
  have increment : Evm.add counter.val 1 =
      (counter.add (Solcore.Core.Word.ofNatModulo 1)).val := by
    have := evm_add counter (Solcore.Core.Word.ofNatModulo 1)
    rwa [ofNatModulo_val_small (by decide)] at this
  let frames : Frames :=
    [[("sc_ptr", .word pointer), ("sc_result", .word result.val), ("sc_count", .word counter.val),
      ("sc_old", .word old.val), ("sc_input", .word input.val), ("sc_flags", .word flags.val)],
      [("input", .uint256 input.val), ("flags", .uint256 flags.val)]]
  have prefixRun : LogStmt.execList context storage memory []
      [[], [("input", .uint256 input.val), ("flags", .uint256 flags.val)]]
      [.rollback (.storage (.plain (.letDecl "sc_flags" .word (.typedefRep (.name "flags"))))),
        .rollback (.storage (.plain (.letDecl "sc_input" .word (.typedefRep (.name "input"))))),
        .rollback (.storage (.plain (.letDecl "sc_old" .word (.call1 "sload" (.number 0))))),
        .rollback (.storage (.plain (.letDecl "sc_count" .word (.call1 "sload" (.number 1))))),
        .rollback (.storage (.letCall "sc_result" .word "sc_step" .add (.name "sc_input")
          (.name "sc_old"))),
        .rollback (.storage (.store (.plain (.number 0)) (.plain (.name "sc_result")))),
        .rollback (.storage (.store (.plain (.number 1))
          (.operation .add (.name "sc_count") (.number 1)))),
        .rollback (.storage (.plain (.letDecl "sc_ptr" .word (.call1 "mload" (.number 64))))),
        .store (.plain (.number 64)) (.operation .add (.name "sc_ptr") (.number 64))] =
      some (.next (logStorage storage result counter) (memory.store 64 (Evm.add pointer 64)) []
        frames) := by
    simp [LogStmt.execList, LogStmt.exec, RollbackStmt.exec, StorageStmt.exec, Stmt.exec,
      Expr.eval, Operand.expr, Frames.lookup, Scope.get?, LocalType.admits, Frames.declare,
      BinaryOp.apply, Context.withStorage_call_sload, oldSlot, counterSlot, evm_add, stepAt,
      loadAt, storeWord, Operand.word?, zeroSmall, one_lt_modulus, sixtyFourSmall, loadFits,
      increment, logStorage, frames, result]
  obtain ⟨memory2, sitesRun⟩ := siteStmts_run context (logStorage storage result counter) frames
    f flags result pointer stepCall (by simp [frames, Frames.lookup, Scope.get?])
    (by simp [frames, Frames.lookup, Scope.get?]) (by simp [frames, Frames.lookup, Scope.get?])
    room sites (memory.store 64 (Evm.add pointer 64)) [] ready
  have bodyRun : LogStmt.execList context storage memory []
      [[], [("input", .uint256 input.val), ("flags", .uint256 flags.val)]] (logBody sites) =
      some (if flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) == Solcore.Core.Word.ofNatModulo 1
        then .reverted result.val
        else .next (logStorage storage result counter) memory2 (sitesLogs f flags result sites)
          frames) := by
    rw [logBody, LogStmt.execList_append, LogStmt.execList_append, prefixRun]
    dsimp only
    rw [sitesRun]
    dsimp only
    cases flag : (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
        Solcore.Core.Word.ofNatModulo 1) <;>
      simp [LogStmt.execList, LogStmt.exec, RollbackStmt.exec, Expr.eval, Operand.expr,
        Frames.lookup, Scope.get?, BinaryOp.apply, rollback_flag, flag, frames, result,
        thirtyTwoSmall, one_lt_modulus]
  unfold LogMethod.run logOutcome
  cases flag : (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
      Solcore.Core.Word.ofNatModulo 1) <;>
    simp [logMethod, Method.bindParameters, word_lt_modulus, bodyRun, flag, Expr.eval,
      Operand.expr, Frames.lookup, Scope.get?, frames, result]

/-! ### The step and its helpers -/

/-- `PrimitiveContext.extend` for any alias list: a helper's name is no
primitive callee, so declaring it keeps every primitive alias and `tobool`. -/
theorem PrimitiveContext.extendAny {functions : List (String × (List Value → Option Value))}
    {aliases : List (String × String)} (admitted : PrimitiveContext ⟨functions, aliases⟩)
    (index : Nat) (meaning : List Value → Option Value) :
    PrimitiveContext ⟨(Function.helperName index, meaning) :: functions, aliases⟩ := by
  refine ⟨fun alias mem arguments => ?_, fun arguments => ?_⟩
  · rw [Context.call_cons_other (helperName_not_callee index alias.2
      (List.mem_cons_of_mem _ (List.mem_map_of_mem mem)))]
    exact admitted.1 alias mem arguments
  · rw [Context.call_cons_other (helperName_not_callee index "tobool"
      (by simp [primitiveCallees]))]
    exact admitted.2 arguments

/-- `aggregateLoop_spec` for any alias list whose primitive context, when a
body uses a raw alias, the caller provides; the log file imports the `logN`
wrappers before the raw aliases. Every declaration is a helper. -/
theorem aggregateLoop_specWith {aliases : List (String × String)} {uses : Bool} :
    ∀ (bodies : List CoreExpr) (start : Nat) (lines names' lines' : List String)
      (functions : List (String × (List Value → Option Value))) (closures : List CoreValue),
    aggregateLoop bodies start (helperNames start) lines = .ok (names', lines') →
    (∀ (index : Nat) (body : CoreExpr), bodies[index]? = some body →
      Solcore.Synthesis.Core.Aggregates.acceptsAt [.word] (start + index) .word body = true ∧
        (AggregateRenderer.usesOpcodeAliases body = true → uses = true)) →
    (uses = true → PrimitiveContext ⟨functions, aliases⟩) →
    MFunctionsAgree ⟨functions, aliases⟩ (helperNames start) closures →
    ∃ declarations : List FunctionDecl,
      lines' = lines ++ declarations.flatMap FunctionDecl.lines ∧
      names' = helperNames (start + bodies.length) ∧
      (∀ declaration ∈ declarations, declaration.NamesOk ∧
        ∀ name ∈ declaration.identifiers, ValidIdentifier name) ∧
      (uses = true →
        PrimitiveContext ⟨declareFunctions aliases functions declarations, aliases⟩) ∧
      MFunctionsAgree ⟨declareFunctions aliases functions declarations, aliases⟩ names'
        (bodies.foldl closureStep closures) ∧
      (∀ declaration ∈ declarations, ∃ index, declaration.name = Function.helperName index)
  | [], start, lines, names', lines', functions, closures, loop, _, primitive, agree => by
      simp only [aggregateLoop, Except.ok.injEq, Prod.mk.injEq] at loop
      obtain ⟨rfl, rfl⟩ := loop
      exact ⟨[], by simp, by simp, by simp, by simpa [declareFunctions] using primitive,
        by simpa [declareFunctions] using agree, by simp⟩
  | body :: rest, start, lines, names', lines', functions, closures, loop, accepted, primitive,
      agree => by
      simp only [aggregateLoop] at loop
      obtain ⟨rendered, renderedEquation, loop⟩ := except_bind_eq_ok loop
      obtain ⟨result, resultEquation, loop⟩ := except_bind_eq_ok loop
      have resultFound := arequireValue_ok resultEquation
      obtain ⟨bodyAccepted, bodyUses⟩ := accepted 0 body rfl
      have bodyKind : initializerKind? ([Binding.word "sc_arg"].map Binding.kind)
          (helperNames start).length body = some Local.word := by
        rw [helperNames_length]
        exact aggregate_acceptsAt_kind bodyAccepted
      obtain ⟨statements, lines₁, _, valueName, names, simulates⟩ :=
        (aggregate_render_spec body).1 (fun context => uses = true → PrimitiveContext context)
          (fun context admitted used => admitted (bodyUses used)) (helperNames start) .word
          [.word "sc_arg"] 4 0 rendered bodyKind renderedEquation
          (single_abinding_fresh argument_not_temporary cellTemp_ne_argument
            payloadTemp_ne_argument)
          (single_abinding_distinct _)
      let declaration := helperDecl start statements result
      have behaves : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
          ∃ (value : Solcore.Core.Word) (store' : Solcore.Core.Store),
            Solcore.Core.Evaluates (.word argument :: closures) store body.toCore
              (.word value) store' ∧
            store.length ≤ store'.length ∧
            (∀ location, location < store.length →
              store'.read? location = store.read? location) ∧
            declaration.denote ⟨functions, aliases⟩ [.word argument.val] =
              some (.word value.val) := by
        intro argument store
        obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _, frame, _⟩ :=
          simulates ⟨functions, aliases⟩ (.word argument :: closures) store []
            [[("sc_arg", .word argument.val)]] primitive
            (single_abinding_agree (by simp [Frames.lookup, Scope.get?]) closures store)
            (single_abinding_cells _ _ _) (by simp) (by simpa using agree)
        rw [resultFound, Option.bind_some] at represents
        obtain ⟨_, lookup, value, rfl, rfl⟩ := represents
        refine ⟨value, store', evaluates, frame.1, fun location inBounds =>
          frame.2 location inBounds fun index isCell => ?_, ?_⟩
        · obtain ⟨⟨_, found⟩, _⟩ := isCell
          cases index with
          | zero => simp at found
          | succ index => simp at found
        · simp [declaration, helperDecl, FunctionDecl.denote, FunctionDecl.bindParameters,
            LocalType.admits, exec, Expr.eval, lookup]
      have extended := agree.extend (helperName_not_mem start) behaves
        (parameterType := Solcore.Core.Wire.Ty.toCore .word)
        (resultType := Solcore.Core.Wire.Ty.toCore .word)
      have extendedPrimitive : uses = true → PrimitiveContext
          ⟨(Function.helperName start, declaration.denote ⟨functions, aliases⟩) :: functions,
            aliases⟩ :=
        fun used => (primitive used).extendAny start _
      have restAccepted : ∀ (index : Nat) (body : CoreExpr), rest[index]? = some body →
          Solcore.Synthesis.Core.Aggregates.acceptsAt [.word] (start + 1 + index) .word body =
            true ∧ (AggregateRenderer.usesOpcodeAliases body = true → uses = true) := by
        intro index body found
        have accepted' := accepted (index + 1) body (by simpa using found)
        rwa [show start + (index + 1) = start + 1 + index by omega] at accepted'
      obtain ⟨declarations, rest₁, rest₂, rest₃, rest₄, rest₅, rest₆⟩ :=
        aggregateLoop_specWith rest (start + 1) _ names' lines' _ _ loop restAccepted
          extendedPrimitive extended
      have block :
          ["function " ++ Function.helperName start ++ "(sc_arg: word) returns (word) {"] ++
          rendered.lines ++ ["    return " ++ result ++ ";", "}", ""] =
          declaration.lines := by
        simp only [declaration, helperDecl, FunctionDecl.lines, lines₁, List.cons_append,
          List.nil_append, List.cons.injEq]
        refine ⟨?_, ?_⟩
        · apply String.toList_inj.mp
          simp [FunctionDecl.parameterText, LocalType.spelling]
        · simp [Expr.print]
      have argumentOk : ∀ index found, anameAt [Binding.word "sc_arg"] index = some found →
          ValidIdentifier found ∧ isReserved found = false :=
        single_abinding_ok (keyword_valid (by decide)) (by decide)
      refine ⟨declaration :: declarations, ?_, ?_, ?_, rest₄, rest₅, ?_⟩
      · rw [rest₁, List.flatMap_cons, ← block]
        simp [List.append_assoc]
      · rw [rest₂]
        simp only [List.length_cons]
        congr 1
        omega
      · intro other mem
        rcases List.mem_cons.mp mem with same | mem
        · subst same
          have bodyOk := fun name mem =>
            aggregate_identifier_ok argumentOk helperNames_ok (names name mem)
          have valueOk := aggregate_identifier_ok (functions := helperNames start) argumentOk
            helperNames_ok (valueName result resultFound).uses
          refine ⟨⟨helperName_not_reserved start, ?_, fun name mem => (bodyOk name mem).2,
            ?_⟩, ?_⟩
          · intro parameter mem
            simp only [declaration, helperDecl, List.mem_singleton] at mem
            subst mem
            decide
          · intro name mem
            simp only [declaration, helperDecl, Expr.identifiers, List.mem_singleton] at mem
            subst mem
            exact valueOk.2
          · intro name mem
            simp only [declaration, helperDecl, FunctionDecl.identifiers, List.map_cons,
              List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
              Expr.identifiers, List.not_mem_nil, or_false] at mem
            rcases mem with rfl | rfl | mem | rfl
            · exact helperName_valid start
            · exact keyword_valid (by decide)
            · exact (bodyOk name mem).1
            · exact valueOk.1
        · exact rest₃ other mem
      · intro other mem
        rcases List.mem_cons.mp mem with same | mem
        · subst same
          exact ⟨start, rfl⟩
        · exact rest₆ other mem


theorem logAlias_not_callee (topics : Nat) :
    ∀ callee ∈ primitiveCallees, EventLog.logAlias topics ≠ callee := by
  have heads : ∀ callee ∈ primitiveCallees, callee.toList.take 4 ≠ ['s', 'c', '_', 'l'] := by
    decide
  intro callee mem same
  apply heads callee mem
  rw [← same]
  simp [EventLog.logAlias]

theorem helperName_ne_logAlias (index topics : Nat) :
    Function.helperName index ≠ EventLog.logAlias topics := by
  intro same
  have heads := congrArg (fun text : String => text.toList.take 4) same
  simp [Function.helperName, EventLog.logAlias] at heads

theorem step_ne_logAlias (topics : Nat) : "sc_step" ≠ EventLog.logAlias topics := by
  intro same
  have heads := congrArg (fun text : String => text.toList.take 4) same
  simp [EventLog.logAlias] at heads

/-- Aliases in front that name another callee do not change a call. -/
theorem Context.call_aliases_append {functions : List (String × (List Value → Option Value))}
    {extra aliases : List (String × String)} {callee : String}
    (absent : ∀ alias ∈ extra, alias.2 ≠ callee) (arguments : List Value) :
    Context.call ⟨functions, extra ++ aliases⟩ callee arguments =
      Context.call ⟨functions, aliases⟩ callee arguments := by
  have none : extra.find? (·.2 == callee) = none := by
    rw [List.find?_eq_none]
    intro alias mem
    simpa using absent alias mem
  simp only [Context.call, List.find?_append, none, Option.none_or]

/-- With the `logN` wrappers in front, the primitive aliases and `tobool` keep
their meanings. -/
theorem primitiveContext_logAliases (sites : List Site) :
    PrimitiveContext ⟨[], logAliases sites ++ primitiveAliases⟩ := by
  have absent : ∀ callee ∈ primitiveCallees, ∀ alias ∈ logAliases sites,
      alias.2 ≠ callee := by
    intro callee mem alias found
    simp only [logAliases, List.mem_map] at found
    obtain ⟨topics, _, rfl⟩ := found
    exact logAlias_not_callee topics callee mem
  refine ⟨fun alias mem arguments => ?_, fun arguments => ?_⟩
  · rw [Context.call_aliases_append (absent alias.2
      (List.mem_cons_of_mem _ (List.mem_map_of_mem mem)))]
    exact primitiveContext_aliases.1 alias mem arguments
  · rw [Context.call_aliases_append (absent "tobool" (by simp [primitiveCallees]))]
    exact primitiveContext_aliases.2 arguments

theorem declareFunctions_find_none (aliases : List (String × String)) {name : String} :
    ∀ (functions : List (String × (List Value → Option Value)))
      (declarations : List FunctionDecl),
    (∀ function ∈ functions, function.1 ≠ name) →
    (∀ declaration ∈ declarations, declaration.name ≠ name) →
    (declareFunctions aliases functions declarations).find? (·.1 == name) = none
  | functions, [], absent, _ => by
      simp only [declareFunctions]
      rw [List.find?_eq_none]
      intro function mem
      simpa using absent function mem
  | functions, declaration :: rest, absent, notDeclared => by
      simp only [declareFunctions]
      apply declareFunctions_find_none aliases _ rest
      · intro function mem
        rcases List.mem_cons.mp mem with same | mem
        · subst same
          exact notDeclared declaration (by simp)
        · exact absent function mem
      · intro other mem
        exact notDeclared other (by simp [mem])

theorem find?_congr_mem {α : Type} {first second : α → Bool} :
    ∀ (items : List α), (∀ item ∈ items, first item = second item) →
      items.find? first = items.find? second
  | [], _ => rfl
  | item :: rest, same => by
      rw [List.find?_cons, List.find?_cons, same item (by simp),
        find?_congr_mem rest (fun other mem => same other (by simp [mem]))]

theorem find?_beq_mem {value : Nat} : ∀ {items : List Nat}, value ∈ items →
    items.find? (· == value) = some value
  | [], mem => by simp at mem
  | item :: rest, mem => by
      by_cases same : item = value
      · subst same
        simp
      · have later : value ∈ rest := by
          rcases List.mem_cons.mp mem with found | found
          · exact absurd found.symm same
          · exact found
        simp [same, find?_beq_mem later]

theorem logAlias_beq {first second : Nat} (firstSmall : first ≤ 4) (secondSmall : second ≤ 4) :
    (EventLog.logAlias first == EventLog.logAlias second) = (first == second) := by
  have cases : ∀ value : Nat, value ≤ 4 →
      value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 ∨ value = 4 := by omega
  rcases cases first firstSmall with rfl | rfl | rfl | rfl | rfl <;>
    rcases cases second secondSmall with rfl | rfl | rfl | rfl | rfl <;> decide

/-- A site's logger names the wrapper for its topic count among the imported
wrappers. -/
theorem logAliases_find {sites : List Site} {site : Site} (mem : site ∈ sites)
    (small : site.topics ≤ 4) :
    (logAliases sites).find? (·.2 == EventLog.logAlias site.topics) =
      some ("log" ++ toString site.topics, EventLog.logAlias site.topics) := by
  have used : site.topics ∈ EventLog.usedArities sites := by
    simp only [EventLog.usedArities, List.mem_filter, List.mem_range, List.any_eq_true, beq_iff_eq]
    exact ⟨by omega, site, mem, rfl⟩
  unfold logAliases
  rw [List.find?_map]
  rw [find?_congr_mem _ (second := (· == site.topics)) (fun topics found => by
    have within : topics ≤ 4 := by
      simp only [EventLog.usedArities, List.mem_filter, List.mem_range] at found
      omega
    simpa [Function.comp_def] using logAlias_beq within small)]
  rw [find?_beq_mem used]
  rfl

/-- The file context resolves a site's logger to its `logN` wrapper: no free
function is named after a wrapper. -/
theorem logContext_opcode {sites : List Site} {site : Site} (mem : site ∈ sites)
    (small : site.topics ≤ 4) (rest : List (String × String)) (declarations : List FunctionDecl)
    (named : ∀ declaration ∈ declarations, declaration.name ≠ EventLog.logAlias site.topics) :
    Context.opcode? ⟨declareFunctions (logAliases sites ++ rest) [] declarations,
      logAliases sites ++ rest⟩ (EventLog.logAlias site.topics) =
      some ("log" ++ toString site.topics) := by
  unfold Context.opcode?
  rw [declareFunctions_find_none _ [] declarations (by simp) named]
  simp [List.find?_append, logAliases_find mem small]

/-! ### The observed logs -/

/-- Word logs numbered from `index` under `tag`, one per word, all from
`emitter`. -/
def numberedLogs (emitter : Address) (tag : Nat → Nat) :
    Nat → List Nat → List CheckedCoreWordLog
  | _, [] => []
  | index, word :: rest =>
      ⟨emitter, Solcore.Core.Word.ofNatModulo (tag index),
        Solcore.Core.Word.ofNatModulo word⟩ :: numberedLogs emitter tag (index + 1) rest

/-- **The framing of one log.** The word logs of a source log under
`EventLog.framingVersion`, all from `emitter`: a header naming the topic count
and the data length with payload zero, then the data Words and the topics,
each numbered from one. -/
def logFrame (emitter : Address) (log : SourceLog) : List CheckedCoreWordLog :=
  ⟨emitter, Solcore.Core.Word.ofNatModulo (headerTag ⟨0, log.topics.length, log.data.length⟩),
    Solcore.Core.Word.ofNatModulo 0⟩ ::
    (numberedLogs emitter dataTag 1 log.data ++ numberedLogs emitter topicTag 1 log.topics)

theorem numberedLogs_range (emitter : Address) (tag : Nat → Nat) :
    ∀ (count start : Nat) (word : Nat → Nat),
    numberedLogs emitter tag start ((List.range count).map word) =
      (List.range count).map fun index => ⟨emitter,
        Solcore.Core.Word.ofNatModulo (tag (index + start)),
        Solcore.Core.Word.ofNatModulo (word index)⟩
  | 0, _, _ => rfl
  | count + 1, start, word => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map,
        numberedLogs, numberedLogs_range emitter tag count (start + 1) (word ∘ Nat.succ)]
      simp only [Function.comp_def, Nat.zero_add, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro index _
      rw [show index + (start + 1) = index + 1 + start by omega]

theorem zipWith_append_same {α β γ : Type} (f : α → β → γ) :
    ∀ (first : List α) (firstWords : List β) (second : List α) (secondWords : List β),
    first.length = firstWords.length →
    List.zipWith f (first ++ second) (firstWords ++ secondWords) =
      List.zipWith f first firstWords ++ List.zipWith f second secondWords
  | [], [], _, _, _ => rfl
  | _ :: rest, _ :: restWords, second, secondWords, same => by
      simp only [List.cons_append, List.zipWith_cons_cons,
        zipWith_append_same f rest restWords second secondWords (by simpa using same)]
  | [], _ :: _, _, _, same => by simp at same
  | _ :: _, [], _, _, same => by simp at same

theorem zipWith_map_same {α β γ δ : Type} (f : β → γ → δ) (first : α → β)
    (second : α → γ) :
    ∀ (items : List α), List.zipWith f (items.map first) (items.map second) =
      items.map fun item => f (first item) (second item)
  | [] => rfl
  | item :: rest => by simp [zipWith_map_same f first second rest]

/-- A site's word logs are the framing of its source log. -/
theorem siteFrame_eq (inputs : HostStorageDriver.ExecutionInputs) (site : Site)
    (value result : Solcore.Core.Word) :
    (tagPairs (frameTags site) (frameWords site value result)).map
        (fun pair => TransactionHostStorageDriver.wordLog inputs pair.1 pair.2) =
      logFrame inputs.currentAddress (siteLog site value result) := by
  unfold tagPairs frameTags frameWords
  rw [zipWith_append_same _ _ _ _ _ (by simp), zipWith_append_same _ _ _ _ _ (by simp),
    zipWith_map_same, zipWith_map_same]
  simp only [logFrame, siteLog, List.length_map, List.length_range, numberedLogs_range,
    List.map_append, List.map_map, List.zipWith_cons_cons, List.zipWith_nil_left, List.map_cons,
    List.cons_append, List.nil_append, Function.comp_def]
  congr 1
  congr 1
  · apply List.map_congr_left
    intro index _
    by_cases zero : index = 0 <;>
      simp [zero, TransactionHostStorageDriver.wordLog, word_ofNatModulo_val]
  · apply List.map_congr_left
    intro index _
    simp [TransactionHostStorageDriver.wordLog, word_ofNatModulo_val]

theorem recordWords_logList (inputs : HostStorageDriver.ExecutionInputs) :
    ∀ (context : TransactionHostStorageDriver.Context)
      (pairs : List (Solcore.Core.Word × Solcore.Core.Word)),
    (recordWords inputs context pairs).workingJournal.logList =
      context.workingJournal.logList ++
        pairs.map fun pair => TransactionHostStorageDriver.wordLog inputs pair.1 pair.2
  | context, [] => by simp [recordWords]
  | context, (topic, payload) :: rest => by
      simp [recordWords, recordWords_logList inputs _ rest, List.append_assoc]

theorem recordWords_storageAccount (inputs : HostStorageDriver.ExecutionInputs) :
    ∀ (context : TransactionHostStorageDriver.Context)
      (pairs : List (Solcore.Core.Word × Solcore.Core.Word)),
    (recordWords inputs context pairs).storageAccount = context.storageAccount
  | context, [] => rfl
  | context, (topic, payload) :: rest => by
      simp [recordWords, recordWords_storageAccount inputs _ rest]

theorem recordWords_storageAddress (inputs : HostStorageDriver.ExecutionInputs) :
    ∀ (context : TransactionHostStorageDriver.Context)
      (pairs : List (Solcore.Core.Word × Solcore.Core.Word)),
    (recordWords inputs context pairs).context.storageAddress = context.context.storageAddress
  | context, [] => rfl
  | context, (topic, payload) :: rest => by
      simp [recordWords, recordWords_storageAddress inputs _ rest]

theorem sitesContext_logList (inputs : HostStorageDriver.ExecutionInputs)
    (f : Solcore.Core.Word → Solcore.Core.Word) (flags result : Solcore.Core.Word) :
    ∀ (sites : List Site) (context : TransactionHostStorageDriver.Context),
    (sitesContext inputs f flags result context sites).workingJournal.logList =
      context.workingJournal.logList ++
        (sitesLogs f flags result sites).flatMap (logFrame inputs.currentAddress)
  | [], context => by simp [sitesContext, sitesLogs]
  | site :: rest, context => by
      rw [sitesContext, sitesContext_logList inputs f flags result rest, sitesLogs]
      unfold siteContext
      cases siteEnabled flags site <;>
        simp [recordWords_logList, siteFrame_eq, List.append_assoc]

theorem sitesContext_storageAccount (inputs : HostStorageDriver.ExecutionInputs)
    (f : Solcore.Core.Word → Solcore.Core.Word) (flags result : Solcore.Core.Word) :
    ∀ (sites : List Site) (context : TransactionHostStorageDriver.Context),
    (sitesContext inputs f flags result context sites).storageAccount = context.storageAccount
  | [], _ => rfl
  | site :: rest, context => by
      rw [sitesContext, sitesContext_storageAccount inputs f flags result rest]
      unfold siteContext
      cases siteEnabled flags site <;> simp [recordWords_storageAccount]

theorem sitesContext_storageAddress (inputs : HostStorageDriver.ExecutionInputs)
    (f : Solcore.Core.Word → Solcore.Core.Word) (flags result : Solcore.Core.Word) :
    ∀ (sites : List Site) (context : TransactionHostStorageDriver.Context),
    (sitesContext inputs f flags result context sites).context.storageAddress =
      context.context.storageAddress
  | [], _ => rfl
  | site :: rest, context => by
      rw [sitesContext, sitesContext_storageAddress inputs f flags result rest]
      unfold siteContext
      cases siteEnabled flags site <;> simp [recordWords_storageAddress]

/-! ### Names of the emitted file -/

/-- Every name the event-log method uses. -/
def bodyNames : List String :=
  ["flags", "input", "sc_input", "sc_old", "sload", "sc_count", "mload"] ++ siteNames

theorem LogStmt.listIdentifiers_append (first second : List LogStmt) :
    LogStmt.listIdentifiers (first ++ second) =
      LogStmt.listIdentifiers first ++ LogStmt.listIdentifiers second := by
  induction first with
  | nil => rfl
  | cons statement rest ih => simp [LogStmt.listIdentifiers, ih, List.append_assoc]

theorem mem_listIdentifiers_sites {name : String} : ∀ {sites : List Site},
    name ∈ LogStmt.listIdentifiers (sites.map siteStmt) →
      ∃ site ∈ sites, name ∈ (siteStmt site).identifiers
  | [], mem => by simp [LogStmt.listIdentifiers] at mem
  | site :: rest, mem => by
      simp only [List.map_cons, LogStmt.listIdentifiers, List.mem_append] at mem
      rcases mem with found | found
      · exact ⟨site, by simp, found⟩
      · obtain ⟨other, otherMem, otherFound⟩ := mem_listIdentifiers_sites found
        exact ⟨other, by simp [otherMem], otherFound⟩

/-- The validity facts `EventLog.validSites` gives each site. -/
theorem sites_valid {sites : List Site}
    (valid : Solcore.Synthesis.Core.EventLog.validSites sites = true) :
    ∀ site ∈ sites,
      1 ≤ site.guard ∧ site.guard ≤ 3 ∧ site.topics ≤ 4 ∧ site.dataWords ≤ 2 := by
  intro site mem
  simp only [Solcore.Synthesis.Core.EventLog.validSites, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at valid
  have := valid.1.2 site mem
  simp only [Solcore.Synthesis.Core.EventLog.maxTopics,
    Solcore.Synthesis.Core.EventLog.maxDataWords] at this
  omega

theorem logBody_names_ok (sites : List Site)
    (valid : ∀ site ∈ sites,
      1 ≤ site.guard ∧ site.guard ≤ 3 ∧ site.topics ≤ 4 ∧ site.dataWords ≤ 2) :
    ∀ name ∈ LogStmt.listIdentifiers (logMethod sites).body ++
      (logMethod sites).result.identifiers, ValidIdentifier name ∧ isReserved name = false := by
  have checked : ∀ name ∈ bodyNames,
      validIdentifier name = true ∧ isReserved name = false := by
    decide
  have prefixNames : ∀ name ∈ LogStmt.listIdentifiers
      [.rollback (.storage (.plain (.letDecl "sc_flags" .word (.typedefRep (.name "flags"))))),
        .rollback (.storage (.plain (.letDecl "sc_input" .word (.typedefRep (.name "input"))))),
        .rollback (.storage (.plain (.letDecl "sc_old" .word (.call1 "sload" (.number 0))))),
        .rollback (.storage (.plain (.letDecl "sc_count" .word (.call1 "sload" (.number 1))))),
        .rollback (.storage (.letCall "sc_result" .word "sc_step" .add (.name "sc_input")
          (.name "sc_old"))),
        .rollback (.storage (.store (.plain (.number 0)) (.plain (.name "sc_result")))),
        .rollback (.storage (.store (.plain (.number 1))
          (.operation .add (.name "sc_count") (.number 1)))),
        .rollback (.storage (.plain (.letDecl "sc_ptr" .word (.call1 "mload" (.number 64))))),
        .store (.plain (.number 64)) (.operation .add (.name "sc_ptr") (.number 64))],
      name ∈ bodyNames := by
    decide
  have revertNames : ∀ name ∈ LogStmt.listIdentifiers
      [.rollback (.revertIf .eq (.binary .bitAnd (.name "sc_flags") (.number 1)) (.number 1)
        (.plain (.name "sc_ptr")) (.plain (.name "sc_result")) (.plain (.name "sc_ptr"))
        (.plain (.number 32)))] ++ (Operand.plain (.name "sc_result")).identifiers,
      name ∈ bodyNames := by
    decide
  intro name mem
  have within : name ∈ bodyNames := by
    simp only [logMethod, logBody, LogStmt.listIdentifiers_append, List.mem_append] at mem
    rcases mem with ((found | found) | found) | found
    · exact prefixNames name found
    · obtain ⟨site, siteMem, siteFound⟩ := mem_listIdentifiers_sites found
      have siteValid := valid site siteMem
      exact List.mem_append_right _ (siteStmt_names site ⟨siteValid.1, siteValid.2.1⟩
        siteValid.2.2.1 name siteFound)
    · exact revertNames name (List.mem_append_left _ found)
    · exact revertNames name (List.mem_append_right _ found)
  exact ⟨keyword_valid (checked name within).1, (checked name within).2⟩

theorem logAlias_ne_mstore (topics : Nat) : EventLog.logAlias topics ≠ "mstore" := by
  intro same
  have chars := congrArg String.toList same
  simp [EventLog.logAlias] at chars

theorem logBody_loggers (sites : List Site) :
    ∀ statement ∈ (logMethod sites).body, statement.LoggerOk := by
  intro statement mem
  simp only [logMethod, logBody, List.mem_append, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at mem
  rcases mem with (found | ⟨site, _, rfl⟩) | rfl
  · rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · exact logAlias_ne_mstore site.topics
  · trivial

theorem logAliases_valid (sites : List Site) :
    ∀ alias ∈ logAliases sites, ValidIdentifier alias.1 ∧ ValidIdentifier alias.2 := by
  intro alias mem
  simp only [logAliases, List.mem_map] at mem
  obtain ⟨topics, found, rfl⟩ := mem
  have small : topics ≤ 4 := by
    simp only [EventLog.usedArities, List.mem_filter, List.mem_range] at found
    omega
  have cases : topics = 0 ∨ topics = 1 ∨ topics = 2 ∨ topics = 3 ∨ topics = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨keyword_valid (by decide), keyword_valid (by decide)⟩

/-! ### One top-level transaction with logs -/

/-- `topLevel_run_settled` with the terminal context the run ends in. -/
theorem topLevel_run_logged {initialWorld : WorldState} (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed : InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) (context : TransactionHostStorageDriver.Context) (value : CoreValue)
    (store : Solcore.Core.Store) (outcome : FrameOutcome Solcore.Core.Word)
    (raw : TopLevelExecution.rawRun contract invocation installed fuel =
      ⟨context, .done value store⟩)
    (decoded : contract.decodeCompletion? value = some outcome) :
    ∃ result, TopLevelExecution.run contract invocation installed fuel = .completed result ∧
      result.outcome = outcome ∧ result.terminalContext = context ∧
      (∀ data, outcome = .returned data →
        result.finalWorld = context.context.values.working.1) ∧
      (∀ data, outcome = .reverted data → result.finalWorld = initialWorld) := by
  have resultEq : (TopLevelExecution.validatedRawRun contract invocation installed fuel).result =
      TopLevelExecution.rawRun contract invocation installed fuel := rfl
  unfold TopLevelExecution.run TopLevelExecution.classifyRawResult
  split
  · rename_i value' store' outcomeEq
    rw [resultEq, raw] at outcomeEq
    cases outcomeEq
    split
    · rename_i outcome' decodedEq
      rw [decoded] at decodedEq
      cases decodedEq
      refine ⟨_, rfl, by simp, ?_, ?_, ?_⟩
      · simp only [TopLevelExecution.terminalContext_finalize]
        rw [resultEq, raw]
      · intro data same
        subst same
        simp only [TopLevelExecution.finalWorld_finalize_returned]
        rw [resultEq, raw]
      · intro data same
        subst same
        simp only [TopLevelExecution.finalWorld_finalize_reverted]
    · rename_i decodedEq
      rw [decoded] at decodedEq
      cases decodedEq
  all_goals
    rename_i outcomeEq
    rw [resultEq, raw] at outcomeEq
    cases outcomeEq

/-- A returned transaction commits the journal its run ends with. -/
theorem committedJournal_returned {initialWorld : WorldState} {target : Address}
    (result : TopLevelTerminalResult initialWorld target) {data : Bytes}
    (returned : result.outcome = .returned data) :
    result.committedJournal = result.terminalContext.workingJournal := by
  rw [result.committedJournal_eq, returned]

/-- A reverted transaction commits no observation: the checkpoint journal of a
top-level run is empty. -/
theorem committedJournal_reverted {initialWorld : WorldState} {target : Address}
    (result : TopLevelTerminalResult initialWorld target) {data : Bytes}
    (reverted : result.outcome = .reverted data) :
    result.committedJournal = TransactionJournal.empty := by
  rw [result.committedJournal_eq, reverted]
  exact result.checkpointJournal_eq

/-- **The observation of one transaction with logs.** With enough fuel, the
top-level transaction of the installed contract completes. Every completed run
settles as the source outcome: it returns the ABI encoding of the returned
word, commits a world whose target account holds the returned storage, and
commits the framing of the returned logs, all from the target, in order; or it
reverts with the 32-byte encoding of the reverted word, commits the world the
transaction started from, and commits no log. -/
def CoreLogs {world : WorldState} (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed : InstalledCheckedCoreContract world invocation.target contract)
    (outcome : LogOutcome) : Prop :=
  (∃ enough, ∀ fuel, enough ≤ fuel →
    ∃ result, TopLevelExecution.run contract invocation installed fuel = .completed result) ∧
  ∀ fuel result, TopLevelExecution.run contract invocation installed fuel = .completed result →
    match outcome with
    | .returned value storage logs =>
        ∃ word : Solcore.Core.Word, word.val = value ∧
          result.outcome = .returned (encodeWordBytesBE word) ∧
          (∃ account, result.finalWorld.account? invocation.target = some account ∧
            StorageAgrees account storage) ∧
          result.committedJournal.logList = logs.flatMap (logFrame invocation.target)
    | .reverted data =>
        ∃ word : Solcore.Core.Word, word.val = data ∧
          result.outcome = .reverted (encodeWordBytesBE word) ∧ result.finalWorld = world ∧
          result.committedJournal.logList = []

/-! ### Preservation -/

/-- **Event-log emitter preservation.** If the actual emitter succeeds, its
source text is the printing of a log file with one free function per helper
and the step function `sc_step`, importing `sload`, `sstore`, `mload`,
`mstore`, `revert_`, the `logN` wrapper of every topic count a site uses and
the raw opcode aliases exactly when a rendered body uses one, and parses back
to it. For every world in which the contract is installed, every calldata whose
words at offsets 4 and 36 are `flags` and `input`, and every memory the
dispatcher leaves whose free-memory pointer word at 64 holds `pointer` with the
64-byte buffer below `2^256`, calling `run(uint256,uint256)` from the installed
account's storage under the log source semantics reverts exactly when the
flags are odd. The original Core contract's top-level transaction settles as
that outcome with the framing of the same logs, or with none on revert. -/
theorem EventLog.emit_preserves_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : EventLog.emit plan = .ok emitted) :
    ∃ file : LogFile, emitted.source = file.print ∧
      parseLogSource emitted.source = some file ∧
      ∀ {world : WorldState} {invocation : TopLevelInvocation}
        (installed : InstalledCheckedCoreContract world invocation.target plan.contract)
        {flags input : Solcore.Core.Word} {memory : Memory} {pointer : Nat},
        invocation.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 4) = some flags →
        invocation.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 36) = some input →
        memory 64 = some pointer → pointer + 64 ≤ Evm.modulus →
        ∃ outcome : LogOutcome,
          file.call (accountStorage installed.account) memory "run" [flags.val, input.val] =
            some outcome ∧
          ((∃ data, outcome = .reverted data) ↔ flags.val % 2 = 1) ∧
          CoreLogs plan.contract invocation installed outcome := by
  obtain ⟨names, lines, entry, result, loop, entryEquation, resultFound, source⟩ :=
    EventLog.emit_success emitted_eq
  let bodies := plan.step.helpers ++ [plan.step.entry]
  let uses := bodies.any AggregateRenderer.usesOpcodeAliases
  let aliases := logAliases plan.sites ++ aggregateAliases bodies
  have bodyUses : ∀ body ∈ bodies, AggregateRenderer.usesOpcodeAliases body = true →
      uses = true := fun body mem used => List.any_eq_true.mpr ⟨body, mem, used⟩
  have startPrimitive : uses = true → PrimitiveContext ⟨[], aliases⟩ := by
    intro used
    have same : aggregateAliases bodies = primitiveAliases := by
      simp only [aggregateAliases]
      rw [if_pos used]
    show PrimitiveContext ⟨[], logAliases plan.sites ++ aggregateAliases bodies⟩
    rw [same]
    exact primitiveContext_logAliases plan.sites
  obtain ⟨declarations, linesEq, namesEq, declarationsOk, primitive, agree, helpers⟩ :=
    aggregateLoop_specWith (aliases := aliases) (uses := uses) plan.step.helpers 0 _ names lines
      [] Solcore.Core.hostEnvironment loop
      (fun index body found =>
        ⟨aggregate_helpers_accepted plan.step.helperScopes index body found,
          bodyUses body (List.mem_append_left _ (List.mem_of_getElem? found))⟩)
      startPrimitive (fun _ _ found => by simp [helperNames] at found)
  have entryKind : initializerKind? ([Binding.word "sc_arg"].map Binding.kind) names.length
      plan.step.entry = some Local.word := by
    rw [namesEq, helperNames_length, Nat.zero_add]
    exact aggregate_acceptsAt_kind plan.step.entryScope
  obtain ⟨statements, entryLines, _, valueName, entryNames, simulates⟩ :=
    (aggregate_render_spec plan.step.entry).1
      (fun context => uses = true → PrimitiveContext context)
      (fun context admitted used =>
        admitted (bodyUses plan.step.entry (List.mem_append_right _ (by simp)) used))
      names .word [.word "sc_arg"] 4 0 entry entryKind entryEquation
      (single_abinding_fresh argument_not_temporary cellTemp_ne_argument
        payloadTemp_ne_argument)
      (single_abinding_distinct _)
  let file := logFile aliases declarations statements result plan.sites
  have siteValid := sites_valid plan.sitesValid
  have argumentOk : ∀ index found, anameAt [Binding.word "sc_arg"] index = some found →
      ValidIdentifier found ∧ isReserved found = false :=
    single_abinding_ok (keyword_valid (by decide)) (by decide)
  have functionNamesOk : ∀ name ∈ names, ValidIdentifier name ∧ isReserved name = false := by
    rw [namesEq]
    exact helperNames_ok
  have valueOk := aggregate_identifier_ok argumentOk functionNamesOk
    (valueName result resultFound).uses
  have stepOk : (stepDecl statements result).NamesOk ∧
      ∀ name ∈ (stepDecl statements result).identifiers, ValidIdentifier name := by
    have bodyOk := fun name mem =>
      aggregate_identifier_ok argumentOk functionNamesOk (entryNames name mem)
    refine ⟨⟨show isReserved "sc_step" = false by decide, ?_,
      fun name mem => (bodyOk name mem).2, ?_⟩, ?_⟩
    · intro parameter mem
      simp only [stepDecl, List.mem_singleton] at mem
      subst mem
      decide
    · intro name mem
      simp only [stepDecl, Expr.identifiers, List.mem_singleton] at mem
      subst mem
      exact valueOk.2
    · intro name mem
      simp only [stepDecl, FunctionDecl.identifiers, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.mem_append, Expr.identifiers,
        List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | mem | rfl
      · exact keyword_valid (by decide)
      · exact keyword_valid (by decide)
      · exact (bodyOk name mem).1
      · exact valueOk.1
  have functionsOk : ∀ function ∈ file.functions, function.NamesOk ∧
      ∀ name ∈ function.identifiers, ValidIdentifier name := by
    intro function mem
    rcases List.mem_append.mp mem with mem | mem
    · exact declarationsOk function mem
    · simp only [List.mem_singleton] at mem
      subst mem
      exact stepOk
  have printed : emitted.source = file.print := by
    have stepLines : (stepDecl statements result).lines =
        ["function sc_step(sc_arg: word) returns (word) {"] ++ entry.lines ++
          ["    return " ++ result ++ ";", "}", ""] := by
      simp only [stepDecl, FunctionDecl.lines, entryLines, List.cons_append, List.nil_append,
        List.cons.injEq]
      refine ⟨?_, ?_⟩
      · apply String.toList_inj.mp
        simp [FunctionDecl.parameterText, LocalType.spelling]
      · simp [Expr.print]
    have functionLine : "    function " ++ EventLog.methodName ++
        "(flags: uint256, input: uint256) public returns (uint256) {" =
          "    function " ++ file.method.name ++ "(" ++
            Method.parameterText file.method.parameters ++ ") public returns (uint256) {" := by
      apply String.toList_inj.mp
      simp [file, logFile, logMethod, Method.parameterText, EventLog.methodName]
    rw [source, LogFile.print, LogFile.lines, linesEq, functionLine]
    simp [file, logFile, EventLog.contractName, stepLines, bodies, aliases, logMethod_lines]
  have bodyNamesOk := logBody_names_ok plan.sites siteValid
  have parsed : parseLogSource emitted.source = some file := by
    rw [printed]
    apply parseLogSource_print
    · refine ⟨fun function mem => (functionsOk function mem).1, rfl, rfl, ?_,
        fun name mem => (bodyNamesOk name (List.mem_append_left _ mem)).2,
        logBody_loggers plan.sites,
        fun name mem => (bodyNamesOk name (List.mem_append_right _ mem)).2⟩
      intro parameter mem
      simp only [file, logFile, logMethod, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> decide
    · refine ⟨?_, fun function mem => (functionsOk function mem).2,
        keyword_valid (show validIdentifier "SynthesizedLogs" = true by decide),
        keyword_valid (show validIdentifier "run" = true by decide), ?_,
        fun name mem => (bodyNamesOk name (List.mem_append_left _ mem)).1,
        fun name mem => (bodyNamesOk name (List.mem_append_right _ mem)).1⟩
      · intro alias mem
        rcases List.mem_append.mp mem with mem | mem
        · exact logAliases_valid plan.sites alias mem
        · exact aggregateAliases_valid bodies alias mem
      · intro parameter mem
        simp only [file, logFile, logMethod, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl <;> exact keyword_valid (by decide)
  refine ⟨file, printed, parsed, ?_⟩
  intro world invocation installed flags input memory pointer flagsData inputData free room
  have stepCall : ∀ arguments, file.context.call "sc_step" arguments =
      (stepDecl statements result).denote ⟨declareFunctions aliases [] declarations, aliases⟩
        arguments := by
    intro arguments
    show Context.call ⟨declareFunctions aliases [] (declarations ++ [stepDecl statements result]),
      aliases⟩ "sc_step" arguments = _
    rw [declareFunctions_append_single]
    exact Context.call_cons_same _ _ _ _ _
  let closures := plan.step.helpers.foldl closureStep Solcore.Core.hostEnvironment
  have stepSpec : ∀ (argument : Solcore.Core.Word) (store : Solcore.Core.Store),
      ∃ (value : Solcore.Core.Word) (store' : Solcore.Core.Store),
        Solcore.Core.Evaluates (.word argument :: closures) store plan.step.entry.toCore
          (.word value) store' ∧
        file.context.call "sc_step" [.word argument.val] = some (.word value.val) := by
    intro argument store
    obtain ⟨core, store', scope', outer', _, evaluates, represents, exec, _, _, _⟩ :=
      simulates ⟨declareFunctions aliases [] declarations, aliases⟩
        (.word argument :: closures) store [] [[("sc_arg", .word argument.val)]] primitive
        (single_abinding_agree (by simp [Frames.lookup, Scope.get?]) _ store)
        (single_abinding_cells _ _ _) (by simp) (by simpa using agree)
    rw [resultFound, Option.bind_some] at represents
    obtain ⟨_, lookup, value, rfl, rfl⟩ := represents
    refine ⟨value, store', evaluates, ?_⟩
    rw [stepCall]
    simp [stepDecl, FunctionDecl.denote, FunctionDecl.bindParameters, LocalType.admits, exec,
      Expr.eval, lookup]
  let f : Solcore.Core.Word → Solcore.Core.Word := fun argument =>
    Classical.choose (stepSpec argument [])
  have sourceStep : ∀ argument : Solcore.Core.Word,
      file.context.call "sc_step" [.word argument.val] = some (.word (f argument).val) :=
    fun argument => (Classical.choose_spec (Classical.choose_spec (stepSpec argument []))).2
  have applies : ∀ argument store, ∃ store', Solcore.Core.Evaluates (.word argument :: closures)
      store plan.step.entry.toCore (.word (f argument)) store' := by
    intro argument store
    obtain ⟨value, store', evaluates, call⟩ := stepSpec argument store
    have same : value = f argument := by
      have values := (sourceStep argument).symm.trans call
      simp only [Option.some.injEq, Value.word.injEq] at values
      exact Fin.ext values.symm
    exact ⟨store', same ▸ evaluates⟩
  have ready : ∀ site ∈ plan.sites, SiteReady file.context site := by
    intro site mem
    refine ⟨siteValid site mem, ?_⟩
    apply logContext_opcode mem (siteValid site mem).2.2.1
    intro declaration found
    rcases List.mem_append.mp found with found | found
    · obtain ⟨index, named⟩ := helpers declaration found
      rw [named]
      exact helperName_ne_logAlias index site.topics
    · simp only [List.mem_singleton] at found
      subst found
      exact step_ne_logAlias site.topics
  let old := installed.account.storageRead (Solcore.Core.Word.ofNatModulo 0)
  let counter := installed.account.storageRead (Solcore.Core.Word.ofNatModulo 1)
  refine ⟨logOutcome (accountStorage installed.account) f flags input old counter plan.sites, ?_,
    ?_, ?_⟩
  · show (if file.method.name = "run" then file.method.run file.context
      (accountStorage installed.account) memory [flags.val, input.val] else none) = _
    rw [if_pos (show file.method.name = "run" from rfl)]
    exact logMethod_run file.context _ memory f plan.sites flags input old counter pointer
      sourceStep ready (by simp [accountStorage, old]) (by simp [accountStorage, counter]) free room
  · unfold logOutcome
    rw [rollback_parity]
    by_cases odd : flags.val % 2 = 1 <;> simp [odd]
  · let context := TopLevelExecution.initialTransactionContext installed
    have stepEvaluates := dag_evaluates plan.step.entry plan.step.helpers
      Solcore.Core.hostEnvironment []
    obtain ⟨store, spent, path⟩ := log_handled (inputs := invocation.executionInputs)
      (context := context) f plan.sites stepEvaluates applies flagsData inputData
    have body : plan.contract.code.program.body =
        .letE (Solcore.Synthesis.Core.functionDAGExpression plan.step.helpers
          plan.step.entry).toCore (logTail1 plan.sites) := by
      show (contractExpression plan.step.program.body plan.sites).toCore = _
      rw [contractExpression_toCore]
      rfl
    let computed := f (input.add old)
    have resultSame : logResult context f input = computed := rfl
    let final := sitesContext invocation.executionInputs f flags computed
      (logWritten context f input) plan.sites
    let account := (installed.account.storageWrite (Solcore.Core.Word.ofNatModulo 0)
      computed).storageWrite (Solcore.Core.Word.ofNatModulo 1)
      (counter.add (Solcore.Core.Word.ofNatModulo 1))
    have finalAccount : final.storageAccount = account := by
      simp [final, sitesContext_storageAccount, logWritten, logResult, context, account, old,
        counter, computed, FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage]
    have address : final.context.storageAddress = invocation.target := by
      simp [final, sitesContext_storageAddress, logWritten, context]
    have journal : final.workingJournal.logList =
        (sitesLogs f flags computed plan.sites).flatMap (logFrame invocation.target) := by
      rw [sitesContext_logList]
      have empty : (logWritten context f input).workingJournal.logList = [] := by
        show context.workingJournal.logList = []
        simp [context]
      rw [empty, List.nil_append]
      rfl
    have agrees : StorageAgrees account
        (logStorage (accountStorage installed.account) computed counter) :=
      storageAgrees_writes installed.account computed
        (counter.add (Solcore.Core.Word.ofNatModulo 1))
    have raw : ∀ fuel, spent ≤ fuel →
        TopLevelExecution.rawRun plan.contract invocation installed fuel =
          ⟨final, .done (rollbackValue (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
            Solcore.Core.Word.ofNatModulo 1) computed) store⟩ := by
      intro fuel enough
      show HostDriver.run (TransactionHostStorageDriver.handler invocation.executionInputs)
        context fuel (Solcore.Core.State.initial plan.contract.code.program.body
          Solcore.Core.hostEnvironment) = _
      rw [body, ← resultSame]
      exact HostDriver.run_done_complete _ path enough
    have settled : ∀ fuel, spent ≤ fuel → ∃ result,
        TopLevelExecution.run plan.contract invocation installed fuel = .completed result ∧
        match logOutcome (accountStorage installed.account) f flags input old counter
            plan.sites with
        | .returned value storage logs =>
            ∃ word : Solcore.Core.Word, word.val = value ∧
              result.outcome = .returned (encodeWordBytesBE word) ∧
              (∃ account, result.finalWorld.account? invocation.target = some account ∧
                StorageAgrees account storage) ∧
              result.committedJournal.logList = logs.flatMap (logFrame invocation.target)
        | .reverted data =>
            ∃ word : Solcore.Core.Word, word.val = data ∧
              result.outcome = .reverted (encodeWordBytesBE word) ∧ result.finalWorld = world ∧
              result.committedJournal.logList = [] := by
      intro fuel enough
      unfold logOutcome
      cases flag : (flags.bitAnd (Solcore.Core.Word.ofNatModulo 1) ==
          Solcore.Core.Word.ofNatModulo 1)
      · have rawFlag := raw fuel enough
        rw [flag] at rawFlag
        obtain ⟨result, run, outcome, terminal, finalWorld, _⟩ := topLevel_run_logged
          plan.contract invocation installed fuel _ _ _ _ rawFlag rfl
        refine ⟨result, run, computed, rfl, outcome, ⟨final.storageAccount, ?_, ?_⟩, ?_⟩
        · rw [finalWorld _ rfl, ← address]
          exact final.storageAccount_present
        · rw [finalAccount]
          exact agrees
        · rw [committedJournal_returned result outcome, terminal]
          exact journal
      · have rawFlag := raw fuel enough
        rw [flag] at rawFlag
        obtain ⟨result, run, outcome, _, _, finalWorld⟩ := topLevel_run_logged plan.contract
          invocation installed fuel _ _ _ _ rawFlag rfl
        refine ⟨result, run, computed, rfl, outcome, finalWorld _ rfl, ?_⟩
        rw [committedJournal_reverted result outcome]
        rfl
    refine ⟨⟨spent, fun fuel enough => (settled fuel enough).elim fun result facts =>
      ⟨result, facts.1⟩⟩, ?_⟩
    intro fuel result run
    obtain ⟨result', run', facts⟩ := settled (fuel + spent) (by omega)
    have resumed := TopLevelExecution.resumeWithFuel_run plan.contract invocation installed fuel
      spent
    rw [run, TopLevelExecution.resumeWithFuel_completed, run'] at resumed
    cases resumed
    exact facts

/-- **Event-log emitter preservation, on the emitted text.** Read as a log
program, the emitted text called with the flags and the input from the
installed account's storage and the dispatcher's memory reverts exactly when
the flags are odd. The original Core contract's transaction settles as that
outcome: it returns the same word, commits the same storage and commits the
framing of the same logs in order, or reverts with the same word, leaves the
world unchanged and commits no log. -/
theorem EventLog.emit_source_meaning {plan : CheckedPlan} {emitted : EmittedProgram}
    (emitted_eq : EventLog.emit plan = .ok emitted)
    {world : WorldState} {invocation : TopLevelInvocation}
    (installed : InstalledCheckedCoreContract world invocation.target plan.contract)
    {flags input : Solcore.Core.Word} {memory : Memory} {pointer : Nat}
    (flagsData : invocation.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 4) = some flags)
    (inputData : invocation.inputData.wordBE? (Solcore.Core.Word.ofNatModulo 36) = some input)
    (free : memory 64 = some pointer) (room : pointer + 64 ≤ Evm.modulus) :
    ∃ outcome : LogOutcome,
      logSourceCall emitted.source (accountStorage installed.account) memory "run"
        [flags.val, input.val] = some outcome ∧
      ((∃ data, outcome = .reverted data) ↔ flags.val % 2 = 1) ∧
      CoreLogs plan.contract invocation installed outcome := by
  obtain ⟨file, _, parsed, meaning⟩ := EventLog.emit_preserves_meaning emitted_eq
  obtain ⟨outcome, call, parity, logged⟩ := meaning installed flagsData inputData free room
  exact ⟨outcome, by simp [logSourceCall, parsed, call], parity, logged⟩

end Solcore.Synthesis.Source.ScalarMeaning
end
