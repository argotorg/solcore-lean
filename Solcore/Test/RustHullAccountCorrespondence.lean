import Solcore.Frontend.RustHull.ContractAccountExecutionCorrespondence
import Solcore.Frontend.RustHull.RuntimeAccountEffectsSemantics
import Solcore.Abi.Keccak256

/-! Account inspection derives its world, balance ledger and memory from the
public context. Source code copying and isolated hashing reach public receipts. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullAccountCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | balance | selfbalance | size | copy | hash | missing | unknown | empty | fundedEmpty
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def targetText := "0x10000000000000000000000000000000000000002"
private def target : Core.Word := w (2 ^ 160 + 2)
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def codeBytes : List UInt8 := [171, 205]
def account (scenario : Scenario) : AccountState.Account := {
  address := w 2, nonce := w 0,
  code := if scenario = .unknown then none else if scenario = .empty ∨ scenario = .fundedEmpty then some [] else some codeBytes}
def context (scenario : Scenario) : Contract.Context := {
  address := w 1, balance := w 11,
  accounts := [(w 2, if scenario = .empty then w 0 else w 7)],
  world := if scenario = .missing then [] else [account scenario]
}
def observation (scenario : Scenario) : Expr := match scenario with
  | .balance => call .word "balance" [word targetText]
  | .selfbalance => call .word "selfbalance" []
  | .size | .missing | .unknown => call .word "extcodesize" [word targetText]
  | .copy => call .unit "extcodecopy" [word targetText, word "31", word "1", word "3"]
  | .hash | .empty | .fundedEmpty => call .word "extcodehash" [word targetText]
def seed : Expr := call .unit "mstore8" [word "7", word "171"]
def inspect (scenario : Scenario) : Expr :=
  if scenario = .copy then observation scenario else call .unit "mstore" [word "192", observation scenario]
def returned (scenario : Scenario) : Expr :=
  if scenario = .copy then call .unit "return" [word "31", word "3"] else call .unit "return" [word "192", word "32"]
def code (scenario : Scenario) : CodeBlock := {stmts := [expression seed, expression (inspect scenario), expression (returned scenario)], functions := []}
def program (scenario : Scenario) : Program := {entryPoints := [], functions := [], objects := [.object "Account" (code scenario) []]}
def initial (object : Contract.CompiledObject) (scenario : Scenario) : Semantics.State RuntimeAccountEffectsSemantics.State :=
  let normalized := Contract.normalizeContext (context scenario)
  ⟨[], ⟨ContractHashCorrespondence.contextInitialState object normalized,
    Core.WordMapping.insertEntries normalized.address normalized.balance normalized.accounts⟩⟩
def seeded : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 7) (w 171)).2
def memoryState (object : Contract.CompiledObject) (scenario : Scenario) (memory : MemorySemantics.State) : Semantics.State RuntimeAccountEffectsSemantics.State :=
  ⟨[], RuntimeAccountEffectsSemantics.withMemory (initial object scenario).external memory⟩
def copiedWords : MemorySemantics.Entries :=
  MemorySemantics.writeByte (MemorySemantics.writeByte (MemorySemantics.writeByte seeded.words (w 31) (w 205)) (w 32) (w 0)) (w 33) (w 0)
def copied : MemorySemantics.State := ⟨copiedWords, w 64⟩
def codeDigest (bytes : List UInt8) : Core.Word :=
  KeccakSemantics.digest (KeccakSemantics.permute (KeccakSemantics.absorbBlock
    (AccountObservationSemantics.packed bytes) (w 0) (w bytes.length) (List.replicate 25 Core.Word.zero)))
def observedWord : Scenario → Core.Word
  | .balance => w 7 | .selfbalance => w 11 | .size => w 2
  | .hash => codeDigest codeBytes | .fundedEmpty => codeDigest [] | _ => w 0
def fails : Scenario → Bool | .missing | .unknown => true | _ => false
def failureReason : Scenario → Core.Word | .missing => w 7 | _ => w 15
def observedResult (scenario : Scenario) : Semantics.Result Semantics.Value :=
  if fails scenario then .fault (.language (failureReason scenario))
  else if scenario = .copy then .value .unit else .value (.word (observedWord scenario))
def observedMemory (scenario : Scenario) : MemorySemantics.State := if scenario = .copy then copied else seeded

theorem copied_code : MemoryCopySemantics.From (AccountObservationSemantics.packed codeBytes)
    (w 31) (w 1) (w 3) seeded (.value .unit) copied := by
  apply MemoryCopySemantics.From.done (by decide +kernel)
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  exact .empty _ _ _ _

theorem hashed_code (bytes : List UInt8) (short : w 136 > w bytes.length)
    (touched : MemorySemantics.touchSize? (w 0) (w 0) (w bytes.length) = some (MemorySemantics.rounded (w bytes.length))) :
    KeccakSemantics.Hash (w 0) (w bytes.length) ⟨AccountObservationSemantics.packed bytes, w 0⟩
      (.value (.word (codeDigest bytes))) ⟨AccountObservationSemantics.packed bytes, MemorySemantics.rounded (w bytes.length)⟩ :=
  .done touched (.last _ _ _ short)

theorem observed (object : Contract.CompiledObject) (scenario : Scenario) :
    AccountObservationSemantics.Builtin
      (initial object scenario).external.runtime.runtime.runtime.storage.world
      (initial object scenario).external.runtime.runtime.runtime.storage.complete
      (initial object scenario).external.balances
      (initial object scenario).external.runtime.runtime.runtime.storage.address
      (match scenario with
        | .balance => "balance" | .selfbalance => "selfbalance"
        | .size | .missing | .unknown => "extcodesize"
        | .copy => "extcodecopy" | _ => "extcodehash")
      (if scenario = .copy then .unit else .word)
      (if scenario = .selfbalance then [] else if scenario = .copy then [.word target, .word (w 31), .word (w 1), .word (w 3)] else [.word target])
      seeded (observedResult scenario) (observedMemory scenario) := by
  cases scenario
  case balance => exact .balance .word target seeded
  case selfbalance => exact .selfbalance .word seeded
  case size => exact .sizeKnown (account := account .size) (by rfl) rfl
  case copy => exact .copyKnown (account := account .copy) (by rfl) rfl copied_code
  case hash =>
    exact .hashKnown (account := account .hash) (by rfl) rfl (by rfl)
      (hashed_code codeBytes (by decide +kernel) (by decide +kernel))
  case missing => exact .sizeFailure (by rfl)
  case unknown => exact .sizeUnknown (account := account .unknown) (by rfl) rfl
  case empty => exact .hashEmpty (account := account .empty) (by rfl) rfl (by rfl)
  case fundedEmpty =>
    exact .hashKnown (account := account .fundedEmpty) (by rfl) rfl (by rfl)
      (hashed_code [] (by decide +kernel) (by decide +kernel))

def inspectedMemory (scenario : Scenario) : MemorySemantics.State :=
  if fails scenario then seeded else if scenario = .copy then copied
  else (MemorySemantics.mstore seeded (w 192) (observedWord scenario)).2
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : Semantics.State RuntimeAccountEffectsSemantics.State :=
  if fails scenario then memoryState object scenario seeded else
    let state := (memoryState object scenario (inspectedMemory scenario)).external
    let memory := state.runtime.runtime.runtime
    let completed := RuntimeFullEffectsSemantics.withRuntime state.runtime
      (TerminationSemantics.terminate memory 1 (if scenario = .copy then w 31 else w 192)
        (if scenario = .copy then w 3 else w 32)).2
    ⟨[], {state with runtime := completed}⟩
def reason (scenario : Scenario) : Core.Word := if fails scenario then failureReason scenario else Core.Word.maximum
def result (scenario : Scenario) : Semantics.Result Semantics.Value := .fault (.language (reason scenario))

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeAccountEffectsSemantics.effects [] seed
      (initial object scenario) (.value .unit) (memoryState object scenario seeded) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))

private theorem observation_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeAccountEffectsSemantics.effects [] (observation scenario)
      (memoryState object scenario seeded) (observedResult scenario) (memoryState object scenario (observedMemory scenario)) := by
  cases scenario
  case selfbalance =>
    apply Semantics.EvalExpr.call rfl
    · exact .nil
    · exact .external (by rfl) rfl (.observation (observed object .selfbalance))
  case copy =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := targetText) rfl) (.cons (.word (text := "31") rfl)
        (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) .nil)))
    · exact .external (by rfl) rfl (.observation (observed object .copy))
  all_goals
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := targetText) rfl) .nil
    · exact .external (by rfl) rfl (.observation (observed object _))

private theorem inspect_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeAccountEffectsSemantics.effects [] (inspect scenario)
      (memoryState object scenario seeded)
      (if fails scenario then .fault (.language (failureReason scenario)) else .value .unit)
      (memoryState object scenario (inspectedMemory scenario)) := by
  by_cases copying : scenario = .copy
  · subst scenario
    exact observation_source object .copy
  · have observedSource := observation_source object scenario
    simp only [observedResult, observedMemory, copying, ↓reduceIte] at observedSource
    by_cases failed : fails scenario = true
    · simp only [inspect, inspectedMemory, copying, failed, ↓reduceIte]
      simp only [failed, ↓reduceIte] at observedSource
      apply Semantics.EvalExpr.callFault rfl
      exact .cons (.word (text := "192") rfl) (.fault observedSource)
    · simp only [inspect, inspectedMemory, copying, failed, Bool.false_eq_true, ↓reduceIte]
      simp only [failed, Bool.false_eq_true, ↓reduceIte] at observedSource
      apply Semantics.EvalExpr.call rfl
      · exact .cons (.word (text := "192") rfl) (.cons observedSource .nil)
      · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime rfl)))))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) (successful : fails scenario = false) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeAccountEffectsSemantics.effects [] (returned scenario)
      (memoryState object scenario (inspectedMemory scenario)) (result scenario) (finalState object scenario) := by
  simp only [result, reason, finalState, successful, Bool.false_eq_true, ↓reduceIte]
  cases scenario
  case missing => contradiction
  case unknown => contradiction
  case copy =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "31") rfl) (.cons (.word (text := "3") rfl) .nil)
    · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.termination rfl))))
  all_goals
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "192") rfl) (.cons (.word (text := "32") rfl) .nil)
    · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.termination rfl))))


theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] RuntimeAccountEffectsSemantics.effects
      (AccountRuntime.frameFunction (code scenario)) [] (initial object scenario) (result scenario) (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault (.language (reason scenario))) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object scenario))
  have inspected := inspect_source object scenario
  cases successful : fails scenario with
  | true =>
      simp only [inspectedMemory, successful, ↓reduceIte] at inspected
      simp only [reason, finalState, successful, ↓reduceIte]
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl inspected)
        (by intro impossible; cases impossible)
  | false =>
      simp only [successful, Bool.false_eq_true, ↓reduceIte] at inspected
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl inspected)
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object scenario successful))
        (by intro impossible; cases impossible)

private theorem observation_eligible (scenario : Scenario) :
    ExecutableExpression ContractAccountCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] (observation scenario) := by
  cases scenario
  case selfbalance => exact .external (Or.inr ⟨.selfbalance, rfl⟩) (by rfl) (by intro _ member; cases member) _ _
  case copy =>
    apply ExecutableExpression.external (name := "extcodecopy") (Or.inr ⟨.copy, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact .word _ _ _
  case balance =>
    apply ExecutableExpression.external (Or.inr ⟨.balance, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_singleton] at member
    subst argument
    exact .word _ _ _
  case size =>
    apply ExecutableExpression.external (Or.inr ⟨.size, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_singleton] at member
    subst argument
    exact .word _ _ _
  case hash =>
    apply ExecutableExpression.external (Or.inr ⟨.hash, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_singleton] at member
    subst argument
    exact .word _ _ _
  case missing =>
    apply ExecutableExpression.external (Or.inr ⟨.size, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_singleton] at member
    subst argument
    exact .word _ _ _
  case unknown =>
    apply ExecutableExpression.external (Or.inr ⟨.size, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_singleton] at member
    subst argument
    exact .word _ _ _
  case empty =>
    apply ExecutableExpression.external (Or.inr ⟨.hash, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_singleton] at member
    subst argument
    exact .word _ _ _
  case fundedEmpty =>
    apply ExecutableExpression.external (Or.inr ⟨.hash, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_singleton] at member
    subst argument
    exact .word _ _ _

theorem eligible (scenario : Scenario) :
    ExecutableProgram ContractAccountCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore8")
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨.store8, rfl⟩))))))) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · by_cases copying : scenario = .copy
    · subst scenario
      exact observation_eligible .copy
    · simp only [inspect, copying, ↓reduceIte]
      apply ExecutableExpression.external (name := "mstore")
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨.store, rfl⟩))))))) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .word _ _ _
      · exact observation_eligible scenario
  · cases scenario
    all_goals
      apply ExecutableExpression.external (name := "return")
        (Or.inl (Or.inl (Or.inl (Or.inr ⟨.returned, rfl⟩)))) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact .word _ _ _

theorem public_resumes (scenario : Scenario) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program scenario) ["Account"] (context scenario) 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program scenario) ["Account"] 64 none [] = .ok object ∧
      prepared = object.instantiate (context scenario) ∧
      ∃ value, ContractAccountCorrespondence.PublicMessageRel (context scenario) (result scenario) (finalState object scenario).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractAccountCorrespondence.prepare_resumes_exact
    (code := code scenario) (by rfl) accepted (eligible scenario) rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object scenario)⟩

private def wordBytes (value : Core.Word) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (Core.Word.byteAt (w index) value).val
private def expectedBytes (scenario : Scenario) : List UInt8 :=
  if scenario = .copy then [205, 0, 0] else wordBytes (observedWord scenario)
private def referenceDigest (bytes : List UInt8) : Core.Word :=
  w ((Abi.V1.Keccak256.hash bytes.toByteArray).data.foldl (fun value byte => value * 256 + byte.toNat) 0)

private def checkCallerMemory (scenario : Scenario) : IO Unit := do
  let observation := if scenario = .copy then
      AccountInspection.copy (.var 3) (.bool false) (.var 1) (.var 0)
        (.word target) (.word (w 31)) (.word (w 1)) (.word (w 3))
    else AccountInspection.hash (.var 3) (.bool false) (.var 2) (.word target)
  let expression := Core.Expr.letE (.newCell AccountState.type (AccountState.literal [(account scenario, 0)]))
    (.letE (.newCell Core.WordMapping.type (Core.WordMapping.literal (context scenario).accounts))
      (.letE (.newCell Core.WordMapping.type (Core.WordMapping.literal seeded.words))
        (.letE (.newCell .word (.word seeded.size)) observation)))
  let expected := if scenario = .copy then Core.Value.inRight .word .unit
    else .inRight .word (.word (observedWord scenario))
  let memory := if scenario = .copy then copied else seeded
  match Core.runStateful 10000000 (Core.State.initial expression) with
  | .done value store =>
      unless value == expected && store[2]? == some (Core.WordMapping.encode memory.words) &&
          store[3]? == some (.word memory.size) do
        throw (IO.userError "account correspondence: copy/hash changed caller memory or size incorrectly")
  | outcome => throw (IO.userError s!"account correspondence: direct observation failed: {reprStr outcome}")

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Account"] 64 with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"account correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate (context scenario)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"account correspondence: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"account correspondence: short resume completed: {reprStr outcome}")
  let receipt := Contract.resumeWithReceipt checkpoint 10000000
  if fails scenario then
    match receipt.outcome with
    | .languageFailure (.word reason) =>
        unless reason == failureReason scenario && receipt.world.isEmpty && receipt.logs.isEmpty do
          throw (IO.userError "account correspondence: failure reason or receipt differs")
    | outcome => throw (IO.userError s!"account correspondence: expected failure, got {reprStr outcome}")
  else
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == expectedBytes scenario && storage.isEmpty && receipt.logs.isEmpty do
          throw (IO.userError "account correspondence: returned observation differs")
    | outcome => throw (IO.userError s!"account correspondence: expected return, got {reprStr outcome}")
  match Core.runStateful 10000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair size (.pair memory (.pair _ (.pair _ (.pair _ (.pair balances _))))))))) _ =>
      let expected := (finalState object scenario).external
      let runtime := expected.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words && balances == Core.WordMapping.encode expected.balances &&
          exit == .word runtime.storage.exit && offset == .word runtime.storage.returnOffset && size == .word runtime.storage.returnSize do
        throw (IO.userError s!"account correspondence: public snapshot differs in {reprStr scenario}")
      unless MemoryCopySemantics.readByte runtime.memory.words (w 7) == w 171 do
        throw (IO.userError "account correspondence: account inspection changed caller memory outside the copy")
  | outcome => throw (IO.userError s!"account correspondence: Core failed: {reprStr outcome}")

def run : IO Unit := do
  unless codeDigest codeBytes == referenceDigest codeBytes && codeDigest [] == referenceDigest [] do
    throw (IO.userError "account correspondence: independent code hash differs from ABI reference")
  for scenario in [Scenario.balance, .selfbalance, .size, .copy, .hash, .missing, .unknown, .empty, .fundedEmpty] do
    check scenario
  for scenario in [Scenario.copy, .hash, .empty, .fundedEmpty] do checkCallerMemory scenario

end Tests.RustHullAccountCorrespondence
