import Solcore.Synthesis.Source.StorageEmitter
import Solcore.Synthesis.Source.ScalarMeaning.AggregateEmitter
import Solcore.Synthesis.Source.ScalarMeaning.CallGraphLoopEmitter
import Solcore.Synthesis.Source.ScalarMeaning.StorageText
import Solcore.ContractRuntime.TopLevelExecution

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
