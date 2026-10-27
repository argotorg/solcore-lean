import Solcore.Synthesis.Source.StorageRollbackEmitter
import Solcore.Synthesis.Source.ScalarMeaning.StorageEmitter
import Solcore.Synthesis.Source.ScalarMeaning.RollbackText

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
