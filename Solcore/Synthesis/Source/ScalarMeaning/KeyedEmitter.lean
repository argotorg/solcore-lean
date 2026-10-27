import Solcore.Synthesis.Source.KeyedStorageEmitter
import Solcore.Synthesis.Source.ScalarMeaning.RollbackEmitter
import Solcore.Synthesis.Source.ScalarMeaning.KeyedText

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
