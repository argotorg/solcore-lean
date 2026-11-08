import Solcore.Frontend.RustHull.ContractStateTheorems
import Solcore.Frontend.RustHull.Semantics.Layers
import Solcore.Abi.Keccak256
import Solcore.Frontend.RustHull.Effects
import Solcore.Core.Machine
import Solcore.Frontend.RustHull.Contract
import Solcore.Frontend.RustHull.Semantics.Frames
import Solcore.Frontend.RustHull.Internal.CallLayout
import Solcore.Frontend.RustHull.ContractCallTheorems
import Solcore.Test.Frontend.RustHull.Calls
import Solcore.Frontend.RustHull.LinkedContract

/-!
# Hull account tests

Account state, inspection and lifecycle, the ambient environment, world effects and runtime effects.
-/

section
-- leanmerge: from Solcore.Test.RustHullAccountCorrespondence
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
end

section
-- leanmerge: from Solcore.Test.RustHullAccountInspection
set_option autoImplicit false
namespace Tests.RustHullAccountInspection
open Solcore.Core Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Solcore.Core.Expr := .word (Word.ofNatModulo value)
private def scalar (value : Nat) : Value := .word (Word.ofNatModulo value)
private def account (target : Nat) (code : Option (List UInt8)) (nonce : Nat := 0)
    (destroyed : Bool := false) : AccountState.Account :=
  { address := Word.ofNatModulo target, code, nonce := Word.ofNatModulo nonce, destroyed }
private def longCode : List UInt8 := (List.range 137).map fun index => UInt8.ofNat (index * 17 + 3)
private def hashValue (bytes : List UInt8) : Nat :=
  (Solcore.Abi.V1.Keccak256.hash bytes.toByteArray).data.foldl
    (fun value byte => value * 256 + byte.toNat) 0
private def catalog : List (AccountState.Account × Nat) :=
  [(account 10 (some []), 0), (account 11 (some []) 1, 0),
   (account 12 (some []), 0), (account 13 (some [0x61, 0x62, 0x63]) 1, 1),
   (account 14 none 1, 0), (account 15 (some [0x61, 0x62, 0x63]) 1 true, 1),
   (account 16 (some longCode) 1, 2)]
private def balances : WordMapping.Entries := [(Word.ofNatModulo 12, Word.ofNatModulo 7)]

/-- Bodies see size, memory, balances and world cells at indices zero to three. -/
private def initialized (body : Solcore.Core.Expr) : Solcore.Core.Expr :=
  .letE (.newCell AccountState.type (AccountState.literal catalog))
    (.letE (.newCell WordMapping.type (WordMapping.literal balances))
      (.letE (.newCell WordMapping.type WordMapping.empty)
        (.letE (.newCell .word (word 0)) body)))
private def program (result : Solcore.Core.Ty) (body : Solcore.Core.Expr) : Solcore.Core.Program := {
  dataDefinitions := AccountInspection.definitions
  resultType := LanguageResult.resultType result
  body := initialized body
}
private def expect (label : String) (result : Solcore.Core.Ty) (body : Solcore.Core.Expr) (value : Value)
    (memorySize : Nat := 0) : IO Unit := do
  let compiled := program result body
  require compiled.check s!"{label}: generated Core is ill-typed"
  match compiled.runStateful 3000000 with
  | .done actual store =>
      require (actual == value) s!"{label}: expected {reprStr value}, got {reprStr actual}"
      require (store[3]? == some (scalar memorySize)) s!"{label}: caller memory size changed unexpectedly"
      require (store[1]? == some (WordMapping.encode balances)) s!"{label}: balances changed"
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def succeeded (value : Nat) : Value := .inRight .word (scalar value)
private def failed (type : Solcore.Core.Ty) (reason : Nat) : Value := .inLeft type (scalar reason)
private def size (target : Nat) (complete : Bool := false) : Solcore.Core.Expr :=
  AccountInspection.size (.var 3) (.bool complete) (word target)
private def hash (target : Nat) (complete : Bool := false) : Solcore.Core.Expr :=
  AccountInspection.hash (.var 3) (.bool complete) (.var 2) (word target)
private def copy (target destination source length : Nat) (complete : Bool := false) : Solcore.Core.Expr :=
  AccountInspection.copy (.var 3) (.bool complete) (.var 1) (.var 0)
    (word target) (word destination) (word source) (word length)
private def copiedWord (target destination source length readOffset : Nat)
    (complete : Bool := false) : Solcore.Core.Expr :=
  LanguageResult.bind .word (copy target destination source length complete)
    (Memory.readMemoryWord (.loadCell (.var 2)) (word readOffset))

def run : IO Unit := do
  let emptyHash := 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
  let abcHash := 0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45
  for target in [10, 11, 12] do
    expect s!"empty code size {target}" .word (size target) (succeeded 0)
  expect "registered code size" .word (size 13) (succeeded 3)
  expect "pending destruction retains size" .word (size 15) (succeeded 3)
  expect "size normalizes high address" .word (size (2 ^ 200 + 13)) (succeeded 3)
  expect "closed world absent size" .word (size 99 true) (succeeded 0)
  expect "open world absent size" .word (size 99) (failed .word 7)
  expect "supplied account lacks code size" .word (size 14) (failed .word 15)
  expect "closed world does not invent missing code" .word (size 14 true) (failed .word 15)
  expect "EIP161 empty account hash" .word (hash 10) (succeeded 0)
  expect "nonexistent hash" .word (hash 99 true) (succeeded 0)
  expect "nonce-only hash" .word (hash 11) (succeeded emptyHash)
  expect "funded code-empty hash" .word (hash 12) (succeeded emptyHash)
  expect "registered code hash" .word (hash 13) (succeeded abcHash)
  expect "pending destruction retains hash" .word (hash 15) (succeeded abcHash)
  expect "hash normalizes high address" .word (hash (2 ^ 200 + 13)) (succeeded abcHash)
  expect "open world absent hash" .word (hash 99) (failed .word 7)
  expect "unknown code hash" .word (hash 14) (failed .word 15)
  expect "multi-block code hash" .word (hash 16) (succeeded (hashValue longCode))
  let targetOnce := Solcore.Core.Expr.letE
    (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 1))) (word 13)
  expect "size target evaluated once" .word
    (AccountInspection.size (.var 3) (.bool false) targetOnce) (succeeded 3) 1
  expect "hash target evaluated once" .word
    (AccountInspection.hash (.var 3) (.bool false) (.var 2) targetOnce) (succeeded abcHash) 1
  expect "copy code and zero-pad suffix" .word (copiedWord 13 0 1 5 0)
    (succeeded (0x6263 * 256 ^ 30)) 32
  expect "copy crosses memory word boundary" .word (copiedWord 13 31 0 3 31)
    (succeeded (0x616263 * 256 ^ 29)) 64
  expect "copy source cannot wrap" .word (copiedWord 13 0 (wordModulus - 1) 64 0)
    (succeeded 0) 64
  expect "copy absent known empty account" .word (copiedWord 99 0 0 32 0 true)
    (succeeded 0) 32
  expect "copy normalizes high address" .word (copiedWord (2 ^ 200 + 13) 0 0 3 0)
    (succeeded (0x616263 * 256 ^ 29)) 32
  expect "copy zero length huge offsets" .unit (copy 13 (wordModulus - 1) (wordModulus - 1) 0)
    (.inRight .word .unit)
  expect "copy unknown account preserves memory" .unit (copy 99 0 0 32) (failed .unit 7)
  expect "copy unknown image preserves memory" .unit (copy 14 0 0 32) (failed .unit 15)
  expect "copy destination range overflow" .unit (copy 13 (wordModulus - 1) 0 1) (failed .unit 6)
  let unregistered := {program .word (size 13) with dataDefinitions := Memory.definitions}
  require (!unregistered.check) "account operations accepted an unregistered world mapping definition"
  match (program .word (hash 16)).runStateful 100 with
  | .outOfFuel state =>
      match runStateful 3000000 state with
      | .done actual _ =>
          require (actual == succeeded (hashValue longCode))
            "account hash resumption changed the returned digest"
      | _ => throw (IO.userError "account hash resumption failed")
  | _ => throw (IO.userError "account hash did not suspend with the small budget")

end Tests.RustHullAccountInspection
end

section
-- leanmerge: from Solcore.Test.RustHullAccountLifecycle
set_option autoImplicit false
namespace Tests.RustHullAccountLifecycle
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def packet : List Value → Value
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)
private def ok : Value := .inRight .word .unit
private def failure (reason : Nat) : Value := .inLeft .unit (scalar reason)
private def entries (values : List (Nat × Nat)) : WordMapping.Entries :=
  values.map fun (key, value) => (word key, word value)

private def current (created : Bool) : AccountState.Account := {
  address := word 0xabc, nonce := word 7,
  storage := entries [(1, 42)], transient := entries [(2, 33)],
  code := some [0x60, 0x00, 0x55], created}
private def neighbor : AccountState.Account := {
  address := word 0x123, nonce := word 8, storage := entries [(4, 99)],
  code := some [0x61, 0x22, 0x33]}
private def recordValue (account : AccountState.Account) (identity : Nat) : Value :=
  packet [WordMapping.encode account.storage, WordMapping.encode account.transient,
    .word account.nonce, scalar identity, WordMapping.encode (Memory.packBytes (account.code.getD [])),
    scalar (account.code.getD []).length, .bool account.code.isSome, .bool account.created, .bool account.destroyed]
private def worldValue (accounts : List (AccountState.Account × Nat)) : Value :=
  OrderedMapping.encode AccountState.layout (accounts.map fun (account, identity) =>
    (.word (word (account.address.val % 2 ^ 160)), recordValue account identity))

private def destroy (beneficiary : Nat) (address : Nat := 0xabc) (complete : Bool := false) : Expr :=
  AccountLifecycle.destroy (.var 1) (.var 0) (number address) (number beneficiary) (.bool complete)

/-- The result includes an actual post-update Core account read. -/
private def program (accounts : List (AccountState.Account × Nat)) (balances : WordMapping.Entries)
    (body : Expr) (address : Nat := 0xabc) (complete : Bool := false) : Program := {
  dataDefinitions := AccountLifecycle.definitions,
  resultType := .product (LanguageResult.resultType .unit) (LanguageResult.resultType AccountState.recordType),
  body := .letE (.newCell AccountState.type (AccountState.literal accounts))
    (.letE (.newCell WordMapping.type (WordMapping.literal balances))
      (.letE body (.pair (.var 0) (AccountState.get (.loadCell (.var 2))
        (number (address % 2 ^ 160)) (.bool complete)))))}

private def check (label : String) (compiled : Program) (status observed : Value)
    (accounts : List (AccountState.Account × Nat)) (balances : WordMapping.Entries) : IO Unit := do
  require compiled.check s!"{label}: lifecycle Core is ill-typed"
  match compiled.runStateful 200000 with
  | .done actual store =>
      require (actual == .pair status observed) s!"{label}: incorrect post-update observations {reprStr actual}"
      require (store[0]? == some (worldValue accounts)) s!"{label}: unexpected world mutation"
      require (store[1]? == some (WordMapping.encode balances)) s!"{label}: unexpected balance mutation"
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def observed (account : AccountState.Account) (identity : Nat := 4) : Value :=
  .inRight .word (recordValue account identity)

private def transferTests : IO Unit := do
  for created in [false, true] do
    let account := current created
    let pending := {account with destroyed := created}
    let catalog := [(account, 4), (neighbor, 9)]
    let after := [(pending, 4), (neighbor, 9)]
    let initial := entries [(0xabc, 20), (0xdef, 3), (0x123, 8)]
    let balances := entries [(0xabc, 0), (0xdef, 23), (0x123, 8)]
    check s!"transfer all balance created={created}"
      (program catalog initial (destroy 0xdef)) ok (observed pending) after balances
    check s!"canonical addresses created={created}"
      (program catalog initial (destroy (2 ^ 200 + 0xdef) (2 ^ 200 + 0xabc)))
      ok (observed pending) after balances
    check s!"recipient need not have a world record created={created}"
      (program catalog (entries [(0xabc, 20)]) (destroy 0xdef))
      ok (observed pending) after (entries [(0xabc, 0), (0xdef, 20)])
    check s!"zero balance retains ledger keys created={created}"
      (program catalog (entries [(0x123, 8)]) (destroy 0xdef))
      ok (observed pending) after (entries [(0x123, 8)])
    check s!"maximum transfer remains representable created={created}"
      (program catalog (entries [(0xabc, wordModulus - 1)]) (destroy 0xdef))
      ok (observed pending) after (entries [(0xabc, 0), (0xdef, wordModulus - 1)])
    let overflow := entries [(0xabc, 20), (0xdef, wordModulus - 20)]
    check s!"overflow precedes all public mutation created={created}"
      (program catalog overflow (destroy 0xdef)) (failure 12) (observed account) catalog overflow

private def selfTests : IO Unit := do
  for created in [false, true] do
    let account := current created
    let pending := {account with destroyed := created}
    let catalog := [(account, 4), (neighbor, 9)]
    let balances := entries [(0xabc, 20), (0xdef, 3)]
    let expected := if created then entries [(0xabc, 0), (0xdef, 3)] else balances
    check s!"self beneficiary created={created}"
      (program catalog balances (destroy 0xabc)) ok (observed pending)
      [(pending, 4), (neighbor, 9)] expected
    check s!"self beneficiary high-bit alias created={created}"
      (program catalog balances (destroy (2 ^ 200 + 0xabc))) ok (observed pending)
      [(pending, 4), (neighbor, 9)] expected

private def sequence (action next : Expr) : Expr :=
  LanguageResult.bind .unit action (next.weakenAt 0)

private def credit (amount : Nat) : Expr :=
  LanguageResult.bind .unit (WordMapping.insert (.loadCell (.var 0)) (number 0xabc) (number amount))
    (LanguageResult.success (.storeCell (.var 1) (.var 0)))

private def repeatedTests : IO Unit := do
  for created in [false, true] do
    let account := current created
    let pending := {account with destroyed := created}
    let catalog := [(account, 4), (neighbor, 9)]
    let after := [(pending, 4), (neighbor, 9)]
    let initial := entries [(0xabc, 20), (0xdef, 3)]
    let repeated := sequence (destroy 0xdef) (sequence (credit 7) (destroy 0x123))
    check s!"repeated destruction transfers newly received funds created={created}"
      (program catalog initial repeated) ok (observed pending) after
      (entries [(0xabc, 0), (0xdef, 23), (0x123, 7)])
    let repeatedSelf := sequence (destroy 0xdef) (sequence (credit 7) (destroy 0xabc))
    check s!"repeated destruction to self created={created}"
      (program catalog initial repeatedSelf) ok (observed pending) after
      (entries [(0xabc, if created then 0 else 7), (0xdef, 23)])
    check s!"repeated zero-balance destruction created={created}"
      (program catalog initial (sequence (destroy 0xdef) (destroy 0x123)))
      ok (observed pending) after (entries [(0xabc, 0), (0xdef, 23)])
  let account := {current true with destroyed := true}
  let catalog := [(account, 4), (neighbor, 9)]
  check "already pending account retains code, nonce and storage while receiving more funds"
    (program catalog (entries [(0xabc, 9), (0xdef, 2)]) (destroy 0xdef))
    ok (observed account) catalog (entries [(0xabc, 0), (0xdef, 11)])

private def missingTests : IO Unit := do
  let balances := entries [(0xabc, 20)]
  let catalog := [(neighbor, 9)]
  check "unknown current account fails without mutation"
    (program catalog balances (destroy 0xdef)) (failure 7)
    (.inLeft AccountState.recordType (scalar 7)) catalog balances
  let defaultAccount : AccountState.Account := {address := word 0xabc}
  check "complete world supplies empty current record"
    (program catalog balances (destroy 0xdef 0xabc true) 0xabc true) ok (observed defaultAccount 0)
    catalog (entries [(0xabc, 0), (0xdef, 20)])

private def resumeChunks : Nat → State → IO StatefulRunResult
  | 0, _ => throw (IO.userError "lifecycle resume budget exhausted")
  | attempts + 1, state => match runStateful 31 state with
      | .outOfFuel state => resumeChunks attempts state
      | result => pure result

private def onceAndResumeTests : IO Unit := do
  let account := current true
  let catalog := [(account, 4), (neighbor, 9)]
  let pending := {account with destroyed := true}
  let initial := entries [(0xabc, 20), (0xdef, 3)]
  let body := sequence (destroy 0xdef) (sequence (credit 7) (destroy 0x123))
  let compiled := program catalog initial body
  match compiled.runStateful 1 with
  | .outOfFuel checkpoint => match ← resumeChunks 10000 checkpoint with
      | .done actual store =>
          require (actual == .pair ok (observed pending)) "resumption changed account observations"
          require (store[0]? == some (worldValue [(pending, 4), (neighbor, 9)]))
            "resumption changed pending destruction"
          require (store[1]? == some (WordMapping.encode (entries [(0xabc, 0), (0xdef, 23), (0x123, 7)])))
            "resumption duplicated or lost a balance transfer"
      | other => throw (IO.userError s!"lifecycle resume: {reprStr other}")
  | _ => throw (IO.userError "lifecycle fixture did not suspend")
  let tick (value : Expr) := Expr.letE
    (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (number 1))) (value.weakenAt 0)
  let once : Program := {
    resultType := .product (LanguageResult.resultType .unit) .word,
    dataDefinitions := AccountLifecycle.definitions,
    body := .letE (.newCell AccountState.type (AccountState.literal catalog))
      (.letE (.newCell WordMapping.type (WordMapping.literal initial))
        (.letE (.newCell .word (number 0))
          (.letE (AccountLifecycle.destroy (tick (.var 2)) (tick (.var 1))
            (tick (number 0xabc)) (tick (number 0xdef)) (tick (.bool false)))
            (.pair (.var 0) (.loadCell (.var 1))))))}
  require once.check "argument-once lifecycle Core is ill-typed"
  match once.runStateful 200000 with
  | .done value _ => require (value == .pair ok (scalar 5)) "lifecycle repeated an input expression"
  | other => throw (IO.userError s!"lifecycle argument evaluation: {reprStr other}")

def run : IO Unit := do
  transferTests
  selfTests
  repeatedTests
  missingTests
  onceAndResumeTests
  IO.println "Rust Hull account lifecycle tests passed"

end Tests.RustHullAccountLifecycle
end

section
-- leanmerge: from Solcore.Test.RustHullAccountState
/-! Core execution tests for the shared world and transaction finalization. -/
set_option autoImplicit false
namespace Tests.RustHullAccountState
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def bytes (values : List Nat) : List UInt8 := values.map UInt8.ofNat
private def entries (values : List (Nat × Nat)) : WordMapping.Entries :=
  values.map fun (key, value) => (word key, word value)
private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false
private def values : List Value → Value
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (values rest)
private def mapping : Value → Except String WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor == WordMapping.nilConstructor then pure [] else .error "wrong empty balance mapping"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor == WordMapping.consConstructor do throw "wrong balance mapping constructor"
      pure ((key, value) :: (← mapping tail))
  | _ => .error "invalid balance mapping"
private def sequence (result : Ty) (action next : Expr) : Expr :=
  LanguageResult.bind result action (next.weakenAt 0)

private def initial : List AccountState.Account := [
  {address := word 0xaaa, storage := entries [(0, 1)], transient := entries [(0, 2)],
    nonce := word 5, code := some (bytes [0x60, 0xfe]), destroyed := true},
  {address := word 0xbbb, storage := entries [(0, 7)], transient := entries [(0, 8)],
    nonce := word 3, code := none, created := true},
  {address := word 0xccc, storage := entries [(0, 9)], transient := entries [(0, 10)],
    nonce := word 4, code := some (bytes [0]), created := true, destroyed := true},
  {address := word 0xddd}]
private def balances : WordMapping.Entries := entries [(0xaaa, 9), (0xbbb, 11), (0xccc, 123), (0xeee, 17)]

/-- Bodies see the balance reference at zero and world reference at one. -/
private def program (result : Ty) (body : Expr) (accounts := initial) (ledger := balances) : Program := {
  dataDefinitions := AccountState.definitions
  resultType := .product (LanguageResult.resultType result) (.product AccountState.type WordMapping.type)
  body := .letE (.newCell AccountState.type (AccountState.literal (accounts.map (·, 17))))
    (.letE (.newCell WordMapping.type (WordMapping.literal ledger))
      (.letE body (.pair (.var 0) (.pair (.loadCell (.var 2)) (.loadCell (.var 1))))))
}

private structure Snapshot where
  status : Value
  world : Value
  accounts : List AccountState.Account
  balances : WordMapping.Entries

private def snapshot (label : String) (value : Value) : IO Snapshot := do
  let .pair status (.pair world balanceValue) := value
    | throw (IO.userError s!"{label}: invalid snapshot shape")
  pure ⟨status, world, ← get (AccountState.decode world), ← get (mapping balanceValue)⟩

private def execute (label : String) (compiled : Program) : IO Snapshot := do
  require compiled.check s!"{label}: generated Core is ill-typed"
  match compiled.runStateful 3000000 with
  | .done value _ => snapshot label value
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def account (snapshot : Snapshot) (address : Nat) : IO AccountState.Account :=
  match snapshot.accounts.find? (·.address == word address) with
  | some account => pure account
  | none => throw (IO.userError s!"missing account {address}")

private def storageTests : IO Unit := do
  let action := sequence .word
    (AccountState.writeStorage (.var 1) (number 0xaaa) (.bool false) (number 0) (number 101))
    (sequence .word
      (AccountState.writeStorage (.var 1) (number 0xbbb) (.bool false) (number 0) (number 202) true)
      (sequence .word
        (AccountState.writeStorage (.var 1) (number 0xaaa) (.bool false) (number 1) (number 303) true)
        (sequence .word
          (AccountState.writeField (.var 1) (number 0xaaa) (.bool false) 2 (number 12))
          (AccountState.readStorage (.var 1) (number 0xaaa) (.bool false) (number 0)))))
  let actual ← execute "world storage helpers" (program .word action)
  require (actual.status == .inRight .word (scalar 101)) "persistent read did not observe write"
  let a ← account actual 0xaaa
  let b ← account actual 0xbbb
  require (a.storage == entries [(0, 101)] && a.transient == entries [(0, 2), (1, 303)] && a.nonce == word 12)
    "first account fields or updates were lost"
  require (b.storage == entries [(0, 7)] && b.transient == entries [(0, 202)] && b.nonce == word 3)
    "storage crossed account or persistent/transient boundaries"
  require (actual.balances == balances) "storage helper changed balances"
  let read ← execute "transient read" (program .word
    (AccountState.readStorage (.var 1) (number 0xbbb) (.bool false) (number 0) true))
  require (read.status == .inRight .word (scalar 8)) "transient read used persistent storage"
  let absent ← execute "incomplete world rejects unknown account" (program .word
    (AccountState.readStorage (.var 1) (number 0x999) (.bool false) (number 0)))
  require (absent.status == .inLeft .word (scalar 7) && absent.accounts.length == initial.length)
    "unknown account silently became empty"
  let absentWrite ← execute "incomplete world rejects unknown write" (program .unit
    (AccountState.writeStorage (.var 1) (number 0x999) (.bool false) (number 0) (number 42)))
  require (absentWrite.status == .inLeft .unit (scalar 7) && absentWrite.accounts.length == initial.length)
    "failed write inserted an unknown account"
  let created ← execute "complete world materializes empty account" (program .word
    (sequence .word
      (AccountState.writeStorage (.var 1) (number 0x999) (.bool true) (number 0) (number 42))
      (AccountState.readStorage (.var 1) (number 0x999) (.bool true) (number 0))))
  let fresh ← account created 0x999
  require (created.status == .inRight .word (scalar 42) && fresh.storage == entries [(0, 42)] &&
    fresh.nonce == word 0 && fresh.code == some []) "default account was not initialized consistently"

private def finalizeTests : IO Unit := do
  let finalizer := AccountState.finalize (.var 1) (.var 0)
  let compiled := program .unit finalizer
  let actual ← execute "transaction finalization" compiled
  require (actual.status == .inRight .word .unit) "finalization failed"
  require (actual.accounts.map (·.address.val) == [0xaaa, 0xbbb, 0xddd])
    "finalization removed an existing account, kept a destroyed new account, or reordered entries"
  for account in actual.accounts do
    require (account.transient.isEmpty && !account.created && !account.destroyed)
      "finalization retained transaction-local state"
  let old ← account actual 0xaaa
  require (old.storage == entries [(0, 1)] && old.nonce == word 5 && old.code == some (bytes [0x60, 0xfe]))
    "existing selfdestruct erased persistent state"
  let new ← account actual 0xbbb
  require (new.storage == entries [(0, 7)] && new.nonce == word 3 && new.code == none)
    "surviving new account lost persistent state or unknown-code status"
  require (actual.balances == entries [(0xaaa, 9), (0xbbb, 11), (0xccc, 0), (0xeee, 17)])
    "finalization did not burn a later credit to a removed account or changed other balances"
  let .constructed _ (.pair (.pair _ (.pair _ (.pair _ (.pair _ (.pair identity _))))) _) := actual.world
    | throw (IO.userError "finalizer produced an invalid record")
  require (identity == scalar 17) "finalization changed the internal code identity"
  let repeated ← execute "idempotent transaction finalization"
    (program .unit (sequence .unit finalizer finalizer))
  require (actual.world == repeated.world && actual.balances == repeated.balances)
    "repeated finalization changed the committed state"
  let empty ← execute "empty world finalization" (program .unit finalizer [] balances)
  require (empty.accounts.isEmpty && empty.balances == balances) "empty finalization changed the ledger"
  match compiled.runStateful 100 with
  | .outOfFuel checkpoint =>
      match runStateful 3000000 checkpoint with
      | .done value _ =>
          let resumed ← snapshot "resumed finalizer" value
          require (resumed.world == actual.world && resumed.balances == actual.balances &&
            resumed.status == actual.status) "resumption changed finalization"
      | other => throw (IO.userError s!"resumed finalizer failed: {reprStr other}")
  | other => throw (IO.userError s!"finalizer did not suspend: {reprStr other}")

private def record (code : Value := WordMapping.encode []) (size : Nat := 0)
    (known : Bool := true) : Value := values [WordMapping.encode (entries [(0, 8)]), WordMapping.encode [],
      scalar 7, scalar 99, code, scalar size, .bool known, .bool false, .bool true]
private def world (record : Value) : Value := OrderedMapping.encode AccountState.layout [(scalar 0xaaa, record)]

private def decoderTests : IO Unit := do
  let packed := WordMapping.encode (entries [(0, 0x1234 * 256 ^ 30), (0, 0xff * 256 ^ 31), (7, 123)])
  let [decoded] ← get (AccountState.decode (world (record packed 33)) 33)
    | throw (IO.userError "decoder lost account")
  require (decoded.address == word 0xaaa && decoded.storage == entries [(0, 8)] && decoded.nonce == word 7 &&
    decoded.code == some (bytes [0x12, 0x34] ++ List.replicate 31 0) && decoded.destroyed)
    "decoder changed fields, byte order, first-match lookup or zero padding"
  let [unknown] ← get (AccountState.decode (world (record packed 33 false)) 33)
    | throw (IO.userError "decoder lost unknown-code account")
  require unknown.code.isNone "decoder trusted an unknown code image"
  require (AccountState.decode (world (record packed 33)) 32 |> rejected) "decoder ignored code bound"
  require (AccountState.decode (world (record packed 33 false)) 32 |> rejected) "unknown code bypassed code bound"
  require (AccountState.decode (WordMapping.encode []) |> rejected) "decoder accepted wrong world data identity"
  require (AccountState.decode (.constructed AccountState.layout.consConstructor .unit) |> rejected)
    "decoder accepted malformed world constructor"
  require (AccountState.decode (world .unit) |> rejected) "decoder accepted truncated account record"
  require (AccountState.decode (world (record .unit)) |> rejected) "decoder accepted malformed code mapping"
  let malformed := values [WordMapping.encode [], WordMapping.encode [], scalar 0, .bool false,
    WordMapping.encode [], scalar 0, .bool true, .bool false, .bool false]
  require (AccountState.decode (world malformed) |> rejected) "decoder accepted malformed code identity"
  let badStorage := values [WordMapping.encode [], .unit, scalar 0, scalar 0,
    WordMapping.encode [], scalar 0, .bool true, .bool false, .bool false]
  require (AccountState.decode (world badStorage) |> rejected) "decoder accepted malformed transient mapping"
  require (AccountState.decode (.constructed AccountState.layout.consConstructor
    (.pair (.pair (scalar 1) (record)) .unit)) |> rejected) "decoder accepted malformed world tail"

def run : IO Unit := do
  storageTests
  finalizeTests
  decoderTests

end Tests.RustHullAccountState
end

section
-- leanmerge: from Solcore.Test.RustHullAccounts
set_option autoImplicit false
namespace Tests.RustHullAccounts
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def name (value : String) : YulName := {name := value}
private def w (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def call (value : String) (args : List YulExpr := []) : YulExpr := ⟨.call (name value) args, none⟩
private def action (value : String) (args : List YulExpr := []) : YulStmt := ⟨.expression (call value args), none⟩
private def wordBytes (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value / 256 ^ (31 - index) % 256)
private def words (values : List Nat) : List UInt8 := values.flatMap wordBytes
private def source (body : List YulStmt) : Program := {
  functions := []
  entryPoints := []
  objects := [.object "Runtime" {stmts := [⟨.assembly body, none⟩], functions := []} [] none]
}
private def branches (cases : List (Nat × List YulStmt)) : List YulStmt :=
  [⟨.switch (call "calldataload" [w 0])
    (cases.map fun (value, body) => ⟨.number (toString value), body, none⟩)
    (some [action "invalid"]), none⟩]
private def defaultContext : Contract.Context := {
  address := word 0xaaa
  caller := word 0xbbb
  balance := word 100
  accounts := [(word 0xbbb, word 1000), (word 0xccc, word 5)]
  emptyAccounts := [word 0xccc]
  availableGas := some (word 100000)
}
private def prepare (label : String) (body : List YulStmt) (context : Contract.Context := defaultContext) :
    IO Contract.Prepared :=
  match Contract.prepare (source body) ["Runtime"] context with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def returned (label : String) (receipt : Contract.Receipt) (expected : List UInt8)
    (topics : List Nat := []) : IO Core.WordMapping.Entries := do
  let logs := topics.map fun topic => {address := word 0xaaa, topics := [word topic], data := [] : Logs.Event}
  require (receipt.logs == logs) s!"{label}: incorrect committed logs {reprStr receipt.logs}"
  match receipt.outcome with
  | .returned actual storage =>
      require (actual == expected) s!"{label}: unexpected bytes {reprStr actual}"
      pure storage
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def checkSlot (label : String) (entries : Core.WordMapping.Entries) (key expected : Nat) : IO Unit :=
  require (Core.WordMapping.lookupEntries (word key) entries == word expected)
    s!"{label}: wrong value at {key}"
private def emit (topic : Nat) : YulStmt := action "log1" [w 0, w 0, w topic]
private def selfCall (value : Nat := 0) : YulExpr :=
  call "call" [w 100000, call "address", w value, w 0, w 32, w 64, w 32]
private def send (target value : Nat) (gas : Nat := 100000) : YulExpr :=
  call "call" [w gas, w target, w value, w 0, w 0, w 0, w 0]
private def resumeUntil : Nat → Contract.Receipt → IO Contract.Receipt
  | 0, _ => throw (IO.userError "account resume budget exhausted")
  | fuel + 1, receipt => match receipt.outcome with
      | .outOfFuel state => do
          require (receipt.logs.isEmpty && receipt.balances.isEmpty) "suspended frame published a receipt"
          resumeUntil fuel (Contract.resumeWithReceipt state 5000)
      | _ => pure receipt

private def reentrantTests : IO Unit := do
  let outer := [action "sstore" [w 0, w 11], action "tstore" [w 0, w 7], emit 10,
    action "mstore" [w 0, w 1], action "mstore" [w 128, selfCall 17], emit 30,
    action "mstore" [w 160, call "sload" [w 0]], action "mstore" [w 192, call "tload" [w 0]],
    action "mstore" [w 224, call "mload" [w 64]], action "mstore" [w 256, call "mload" [w 0]],
    action "return" [w 128, w 160]]
  let child := [action "sstore" [w 0, call "add" [call "sload" [w 0], w 1]],
    action "tstore" [w 0, call "add" [call "tload" [w 0], w 1]], emit 20,
    action "sstore" [w 1, call "caller"], action "sstore" [w 2, call "callvalue"],
    action "sstore" [w 3, call "selfbalance"],
    action "mstore" [w 0, call "sload" [w 0]], action "return" [w 0, w 32]]
  let prepared ← prepare "shared reentrant state" (branches [(0, outer), (1, child)])
  let expected := words [1, 12, 8, 12, 1]
  let receipt := Contract.runWithReceipt prepared
  let storage ← returned "reentrant writes and frame memory" receipt expected [10, 20, 30]
  checkSlot "outer update" storage 0 12
  checkSlot "child caller is current address" storage 1 0xaaa
  checkSlot "child receives value" storage 2 17
  checkSlot "self transfer keeps balance" storage 3 100
  checkSlot "self transfer receipt balance" receipt.balances 0xaaa 100
  let resumed ← resumeUntil 10000 (Contract.runWithReceipt prepared 100)
  let resumedStorage ← returned "reentrant call resumes" resumed expected [10, 20, 30]
  require (storage == resumedStorage && receipt.balances == resumed.balances)
    "resumption changed the committed world"
  let fresh ← prepare "transient storage resets at top-level entry"
    [action "mstore" [w 0, call "tload" [w 0]], action "return" [w 0, w 32]]
    {defaultContext with storage := storage}
  let _ ← returned "new top-level transient storage" (Contract.runWithReceipt fresh) (wordBytes 0)
  pure ()

private def rollbackTests : IO Unit := do
  let outer := [action "sstore" [w 0, w 11], action "tstore" [w 0, w 7], emit 10,
    action "mstore" [w 0, w 1], action "mstore" [w 128, selfCall], emit 30,
    action "mstore" [w 160, call "sload" [w 0]], action "mstore" [w 192, call "tload" [w 0]],
    action "mstore" [w 224, call "returndatasize"], action "mstore" [w 256, call "mload" [w 64]],
    action "return" [w 128, w 160]]
  let child := [action "sstore" [w 0, w 99], action "tstore" [w 0, w 88], emit 20,
    action "pop" [send 0xccc 3], action "mstore" [w 0, w 2], action "pop" [selfCall],
    action "mstore" [w 0, w 0xabcdef], action "revert" [w 29, w 3]]
  let grandchild := [action "sstore" [w 0, w 123], action "tstore" [w 0, w 234], emit 25, action "stop"]
  let prepared ← prepare "nested successful grandchild then child revert"
    (branches [(0, outer), (1, child), (2, grandchild)])
  let receipt := Contract.runWithReceipt prepared
  let storage ← returned "child rollback retains parent changes" receipt
    (words [0, 11, 7, 3, 0xabcdef * 256 ^ 29]) [10, 30]
  checkSlot "storage checkpoint" storage 0 11
  checkSlot "sender balance checkpoint" receipt.balances 0xaaa 100
  checkSlot "recipient balance checkpoint" receipt.balances 0xccc 5
  let invalidChild := child.take (child.length - 2) ++ [action "invalid"]
  let prepared ← prepare "child invalid after nested success"
    (branches [(0, outer), (1, invalidChild), (2, grandchild)])
  let receipt := Contract.runWithReceipt prepared
  let storage ← returned "exceptional child rollback" receipt (words [0, 11, 7, 0, 0]) [10, 30]
  checkSlot "exceptional storage checkpoint" storage 0 11
  checkSlot "exceptional sender balance checkpoint" receipt.balances 0xaaa 100
  checkSlot "exceptional recipient balance checkpoint" receipt.balances 0xccc 5
  let successfulChild := [action "sstore" [w 0, w 77], emit 20, action "pop" [send 0xccc 3], action "stop"]
  let revertedOuter := [emit 10, action "mstore" [w 0, w 1], action "pop" [selfCall],
    action "revert" [w 0, w 0]]
  let prepared ← prepare "outer revert after successful child" (branches [(0, revertedOuter), (1, successfulChild)])
  let receipt := Contract.runWithReceipt prepared
  require (receipt.logs.isEmpty && receipt.balances.isEmpty) "outer revert published nested effects"
  match receipt.outcome with
  | .reverted [] => pure ()
  | other => throw (IO.userError s!"outer revert: {reprStr other}")

private def balanceTests : IO Unit := do
  let body := [action "mstore" [w 0, send 0xccc 20], action "mstore" [w 32, send 0xccc 81],
    action "mstore" [w 64, call "selfbalance"], action "mstore" [w 96, call "returndatasize"],
    action "mstore" [w 128, call "balance" [call "address"]],
    action "mstore" [w 160, call "balance" [w 0xccc]], action "return" [w 0, w 192]]
  let prepared ← prepare "known empty recipient and insufficient funds" body
  let receipt := Contract.runWithReceipt prepared
  let _ ← returned "value transfers and balance reads" receipt (words [1, 0, 80, 0, 80, 25])
  checkSlot "sender debit" receipt.balances 0xaaa 80
  checkSlot "recipient credit" receipt.balances 0xccc 25
  let unknown ← prepare "unknown account fails explicitly" [emit 10, action "pop" [send 0xddd 20], action "stop"]
  let receipt := Contract.runWithReceipt unknown
  require (receipt.logs.isEmpty && receipt.balances.isEmpty) "unsupported call published world changes"
  match receipt.outcome with
  | .languageFailure (.word reason) => require (reason == word 7) "incorrect unknown-account failure"
  | other => throw (IO.userError s!"unknown account: {reprStr other}")
  let high := 2 ^ 200
  let canonical ← prepare "address canonicalization"
    [action "mstore" [w 0, call "address"], action "mstore" [w 32, call "caller"],
      action "mstore" [w 64, send (high + 0xccc) 20], action "return" [w 0, w 96]]
    {defaultContext with
      address := word (high + 0xaaa)
      caller := word (high + 0xbbb)
      emptyAccounts := [word (high + 0xccc)]
      accounts := [(word (high + 0xccc), word 5)]}
  let receipt := Contract.runWithReceipt canonical
  let _ ← returned "canonical frame and account addresses" receipt (words [0xaaa, 0xbbb, 1])
  checkSlot "canonical recipient" receipt.balances 0xccc 25

private def balanceReadTests : IO Unit := do
  let high := 2 ^ 200
  let prepared ← prepare "balance reads share the canonical ledger in static context"
    [action "mstore" [w 0, call "balance" [call "address"]],
      action "mstore" [w 32, call "balance" [w 0xccc]],
      action "mstore" [w 64, call "balance" [w (high + 0xccc)]],
      action "mstore" [w 96, call "balance" [w 0xddd]],
      action "mstore" [w 128, call "balance" [w 0xbbb]],
      action "return" [w 0, w 160]] {defaultContext with isStatic := true}
  let _ ← returned "self, external, high-bit alias, absent, and unknown-code account balances"
    (Contract.runWithReceipt prepared) (words [100, 5, 5, 0, 1000])
  let outer := [action "mstore" [w 0, w 1], action "mstore" [w 128, selfCall],
    action "mstore" [w 160, call "balance" [call "address"]],
    action "mstore" [w 192, call "balance" [w 0xccc]],
    action "mstore" [w 224, call "mload" [w 64]], action "return" [w 128, w 128]]
  let child := [action "pop" [send 0xccc 3],
    action "mstore" [w 0, call "balance" [w 0xccc]], action "revert" [w 0, w 32]]
  let prepared ← prepare "balance reads observe a reverted child transfer"
    (branches [(0, outer), (1, child)])
  let receipt := Contract.runWithReceipt prepared
  let _ ← returned "child sees transfer and parent sees restored balances" receipt (words [0, 100, 5, 8])
  checkSlot "balance read sender rollback" receipt.balances 0xaaa 100
  checkSlot "balance read recipient rollback" receipt.balances 0xccc 5

private def staticTests : IO Unit := do
  let outer := [action "sstore" [w 0, w 11], emit 10, action "mstore" [w 0, w 1],
    action "mstore" [w 128, call "staticcall" [w 100000, call "address", w 0, w 32, w 64, w 32]],
    emit 30, action "mstore" [w 160, call "sload" [w 0]], action "return" [w 128, w 64]]
  let attempts := [
    ("read", [action "mstore" [w 64, call "sload" [w 0]], action "return" [w 64, w 32]]),
    ("sstore", [action "sstore" [w 0, w 99]]),
    ("tstore", [action "tstore" [w 0, w 99]]),
    ("log", [emit 20]),
    ("value call", [action "pop" [send 0xccc 1]]),
    ("static inheritance through zero-value call", [action "mstore" [w 0, w 2],
      action "mstore" [w 64, selfCall], action "return" [w 64, w 32]])]
  for (label, operations) in attempts do
    let child := operations ++ [action "stop"]
    let prepared ← prepare s!"static {label}"
      (branches [(0, outer), (1, child), (2, [action "sstore" [w 0, w 99], action "stop"])])
    let receipt := Contract.runWithReceipt prepared
    -- The intermediate static child catches its descendant's exceptional halt.
    let status := if label == "read" || label == "static inheritance through zero-value call" then 1 else 0
    let storage ← returned s!"static {label}" receipt (words [status, 11]) [10, 30]
    checkSlot s!"static {label} unchanged storage" storage 0 11
    checkSlot s!"static {label} unchanged balance" receipt.balances 0xaaa 100
  let prepared ← prepare "top-level static violation" [action "sstore" [w 0, w 99]]
    {defaultContext with isStatic := true}
  let receipt := Contract.runWithReceipt prepared
  require (receipt.logs.isEmpty && receipt.balances.isEmpty) "static failure published a receipt"
  match receipt.outcome with
  | .invalid => pure ()
  | other => throw (IO.userError s!"top-level static write: {reprStr other}")

private def precompileValueTests : IO Unit := do
  let identity := call "call" [w 18, w 4, w 10, w 0, w 3, w 64, w 3]
  let insufficientRecovery := call "call" [w 0, w 1, w 10, w 0, w 3, w 96, w 32]
  let body := [action "calldatacopy" [w 0, w 0, w 3],
    action "mstore" [w 128, identity], action "mstore" [w 160, insufficientRecovery],
    action "mstore" [w 192, call "returndatasize"], action "mstore" [w 224, call "selfbalance"],
    action "return" [w 128, w 128]]
  let prepared ← prepare "precompile value transfer and gas-failure rollback" body
    {defaultContext with calldata := "abc".toUTF8.toList, accounts := [(word 1, word 7), (word 4, word 2)]}
  let receipt := Contract.runWithReceipt prepared
  let _ ← returned "precompile CALL" receipt (words [1, 0, 0, 90])
  checkSlot "successful precompile receives value" receipt.balances 4 12
  checkSlot "failed precompile keeps old balance" receipt.balances 1 7
  checkSlot "failed precompile refunds sender" receipt.balances 0xaaa 90

private def dispatchPriorityTests : IO Unit := do
  let constructor ← prepare "self code is unavailable during construction"
    [emit 10, action "mstore" [w 0, selfCall 5],
      action "mstore" [w 32, call "returndatasize"], action "mstore" [w 64, call "selfbalance"],
      action "return" [w 0, w 96]]
    {defaultContext with selfCodeAvailable := false}
  let receipt := Contract.runWithReceipt constructor
  let _ ← returned "constructor self call sees empty code" receipt (words [1, 0, 100]) [10]
  checkSlot "constructor self transfer" receipt.balances 0xaaa 100
  let precompile ← prepare "precompile wins over self-code selection"
    [action "calldatacopy" [w 0, w 0, w 3],
      action "mstore" [w 64, call "call" [w 18, call "address", w 0, w 0, w 3, w 96, w 3]],
      action "return" [w 64, w 35]]
    {defaultContext with address := word 4, calldata := "abc".toUTF8.toList}
  let receipt := Contract.runWithReceipt precompile
  let _ ← returned "precompile dispatch priority" receipt (wordBytes 1 ++ "abc".toUTF8.toList)
  checkSlot "precompile self transfer" receipt.balances 4 100

/-- Value-bearing calls include the protocol stipend in the explicit child budget. -/
def runValueStipend : IO Unit := do
  let prepared ← prepare "value CALL includes its stipend"
    [action "calldatacopy" [w 0, w 0, w 3],
      action "mstore" [w 128, call "call" [w 0, w 4, w 10, w 0, w 3, w 64, w 3]],
      action "return" [w 128, w 32]]
    {defaultContext with calldata := "abc".toUTF8.toList}
  let receipt := Contract.runWithReceipt prepared
  let _ ← returned "zero requested gas can use the value stipend" receipt (wordBytes 1)
  checkSlot "stipend call transfers value" receipt.balances 4 10
  checkSlot "stipend call debits sender" receipt.balances 0xaaa 90
  let outer := [action "mstore" [w 0, w 1],
    action "mstore" [w 128, call "call" [w 0, call "address", w 1, w 0, w 32, w 64, w 32]],
    action "mstore" [w 160, call "mload" [w 64]], action "return" [w 128, w 64]]
  let child := [action "mstore" [w 0, call "gas"], action "return" [w 0, w 32]]
  let prepared ← prepare "child gas environment includes stipend" (branches [(0, outer), (1, child)])
  let _ ← returned "child receives stipend" (Contract.runWithReceipt prepared) (words [1, 2300])
  let prepared ← prepare "value stipend overflow is explicit"
    [emit 10, action "pop" [send 0xccc 1 (Core.wordModulus - 1)], action "stop"]
  let receipt := Contract.runWithReceipt prepared
  require (receipt.logs.isEmpty && receipt.balances.isEmpty) "stipend overflow published a receipt"
  match receipt.outcome with
  | .languageFailure (.word reason) => require (reason == word 13) "incorrect stipend overflow reason"
  | other => throw (IO.userError s!"stipend overflow: {reprStr other}")

def runZeroValueLedger : IO Unit := do
  let prepared ← prepare "zero-value calls preserve the balance ledger"
    [action "mstore" [w 0, call "staticcall" [w 15, w 4, w 0, w 0, w 0, w 0]],
      action "mstore" [w 32, send 0xddd 0], action "return" [w 0, w 64]]
    {defaultContext with emptyAccounts := [word 0xddd]}
  let receipt := Contract.runWithReceipt prepared
  let _ ← returned "zero-value calls" receipt (words [1, 1])
  let expected := Core.WordMapping.insertEntries (word 0xaaa) (word 100) defaultContext.accounts
  require (receipt.balances == expected) "zero-value calls added ledger entries or changed balances"

def run : IO Unit := do
  reentrantTests
  rollbackTests
  balanceTests
  balanceReadTests
  staticTests
  precompileValueTests
  dispatchPriorityTests
  runValueStipend
  runZeroValueLedger

end Tests.RustHullAccounts
end

section
-- leanmerge: from Solcore.Test.RustHullAmbient
set_option autoImplicit false
namespace Tests.RustHullAmbient
open Solcore.Core
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Solcore.Core.Expr := .word (word value)
private def get {α : Type} (result : LowerM α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def scope : Scope := Ambient.slots.reverse.map fun (name, type) =>
  ⟨some ("$lean$evm$" ++ name), type, false⟩

private def allocate (context : Ambient.Context) (body : Solcore.Core.Expr) : Solcore.Core.Expr :=
  .letE (Ambient.contextExpression context)
    (Ambient.slots.zipIdx.foldr (fun ((_, type), index) body =>
      .letE (.newCell type (Ambient.initialValue index (.var index))) body) body)

private def program (context : Ambient.Context) (name : String)
    (arguments : List Solcore.Core.Expr := []) : IO Solcore.Core.Program := do
  let lowered ← get (Ambient.lowerBuiltin scope name arguments)
  pure {
    resultType := LanguageResult.resultType .word,
    dataDefinitions := Memory.definitions, body := allocate context lowered.expression}

private def result (label : String) (compiled : Solcore.Core.Program) (expected : Value) : IO Unit := do
  require compiled.check s!"{label}: ambient Core is ill-typed"
  match compiled.runStateful 100000 with
  | .done actual _ => require (actual == expected) s!"{label}: {reprStr actual}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def expect (label : String) (context : Ambient.Context) (name : String)
    (arguments : List Nat) (expected : Nat) : IO Unit := do
  result label (← program context name (arguments.map number)) (.inRight .word (.word (word expected)))

private def unavailable (label : String) (context : Ambient.Context) (name : String)
    (arguments : List Nat := []) : IO Unit := do
  result label (← program context name (arguments.map number))
    (.inLeft .word (.word Ambient.unavailableReason))

private def fieldTests : IO Unit := do
  let high := 2 ^ 200
  let context : Ambient.Context := {
    origin := some (word (high + 0xabc)), gasprice := some (word 7),
    coinbase := some (word (high + 0xdef)), timestamp := some (word 123456),
    number := some (word 300), prevrandao := some Word.maximum,
    gaslimit := some (word 30000000), chainid := some (word 1),
    basefee := some (word 9), blobbasefee := some (word 11)}
  for (name, expected) in [("origin", 0xabc), ("gasprice", 7), ("coinbase", 0xdef),
      ("timestamp", 123456), ("number", 300), ("prevrandao", wordModulus - 1),
      ("gaslimit", 30000000), ("chainid", 1), ("basefee", 9), ("blobbasefee", 11)] do
    expect s!"provided {name}" context name [] expected
    unavailable s!"missing {name}" {} name
    match Ambient.lowerBuiltin scope name [number 0] with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"{name}: wrong arity accepted")
  expect "supplied zero differs from missing" {origin := some Word.zero} "origin" [] 0
  expect "address maximum mask" {coinbase := some Word.maximum} "coinbase" [] (2 ^ 160 - 1)
  require (!Ambient.supports "gas" && !Ambient.supports "unknown") "ambient support list overreaches"
  require (Ambient.slots.length = 12) "ambient context slot count changed"

private def blockTests : IO Unit := do
  let context : Ambient.Context := {
    number := some (word 300), blockHashes := some [
      (word 299, word 0xa1), (word 44, word 0xa2), (word 43, word 0xa3),
      (word 300, word 0xa4), (word 301, word 0xa5), (Word.maximum, word 0xa6)]}
  for (index, expected) in [(299, 0xa1), (44, 0xa2), (43, 0), (300, 0),
      (301, 0), (298, 0), (wordModulus - 1, 0)] do
    expect s!"block hash at {index}" context "blockhash" [index] expected
  expect "genesis cannot wrap to maximum block"
    {number := some Word.zero, blockHashes := some [(Word.maximum, word 77)]}
    "blockhash" [wordModulus - 1] 0
  expect "maximum current number accepts preceding block"
    {number := some Word.maximum,
      blockHashes := some [(word (wordModulus - 2), word 88)]}
    "blockhash" [wordModulus - 2] 88
  expect "maximum current number cannot wrap a far history distance"
    {number := some Word.maximum, blockHashes := some [(Word.zero, word 99)]}
    "blockhash" [0] 0
  expect "supplied empty history" {number := some (word 1), blockHashes := some []}
    "blockhash" [0] 0
  unavailable "block hash requires current number" {blockHashes := some []} "blockhash" [0]
  unavailable "block hash requires history model" {number := some (word 1)} "blockhash" [0]
  unavailable "even excluded range requires explicit history" {number := some (word 1)} "blockhash" [1]

private def blobTests : IO Unit := do
  let context : Ambient.Context := {blobHashes := some [word 0x11, Word.zero, word 0x33]}
  for (index, expected) in [(0, 0x11), (1, 0), (2, 0x33), (3, 0), (wordModulus - 1, 0)] do
    expect s!"blob hash at {index}" context "blobhash" [index] expected
  expect "supplied empty blob list" {blobHashes := some []} "blobhash" [0] 0
  unavailable "missing blob list" {} "blobhash" [0]
  for name in ["blockhash", "blobhash"] do
    match Ambient.lowerBuiltin scope name [] with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"{name}: missing index accepted")
    match Ambient.lowerBuiltin scope name [number 0, number 1] with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"{name}: excess index accepted")

private def resumeChunks : Nat → State → IO Value
  | 0, _ => throw (IO.userError "ambient resume budget exhausted")
  | attempts + 1, state => match runStateful 29 state with
      | .done value _ => pure value
      | .outOfFuel state => resumeChunks attempts state
      | .fault error _ => throw (IO.userError s!"ambient resume fault: {reprStr error}")

private def onceAndResumeTests : IO Unit := do
  let context : Ambient.Context := {
    number := some (word 1), blockHashes := some [(Word.zero, word 0xabc)],
    blobHashes := some [word 0xabc]}
  for name in ["blockhash", "blobhash"] do
    let index : Solcore.Core.Expr := .letE
      (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (number 1))) (number 0)
    let lowered ← get (Ambient.lowerBuiltin (scope.temporary (.cell .word)) name [index])
    let compiled : Solcore.Core.Program := {
      resultType := .product (LanguageResult.resultType .word) .word,
      dataDefinitions := Memory.definitions,
      body := allocate context (.letE (.newCell .word (number 0))
        (.letE lowered.expression (.pair (.var 0) (.loadCell (.var 1)))))}
    let expected := Value.pair (.inRight .word (.word (word 0xabc))) (.word (word 1))
    result s!"{name} evaluates index once" compiled expected
    match compiled.runStateful 1 with
    | .outOfFuel checkpoint =>
        require ((← resumeChunks 1000 checkpoint) == expected) s!"{name}: resumption changed result"
    | other => throw (IO.userError s!"{name}: expected suspension, got {reprStr other}")

def run : IO Unit := do
  fieldTests
  blockTests
  blobTests
  onceAndResumeTests
  IO.println "Rust Hull ambient context tests passed"

end Tests.RustHullAmbient
end

section
-- leanmerge: from Solcore.Test.RustHullCreationRuntime
set_option autoImplicit false
namespace Tests.RustHullCreationRuntime
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program
open CodeBuilder

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def scalar (value : Nat) : Value := .word (word value)
private def bytes (values : List Nat) : List UInt8 := values.map UInt8.ofNat
private def entries (values : List (Nat × Nat)) : WordMapping.Entries :=
  values.map fun (key, value) => (word key, word value)
private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def mapping : Value → Except String WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor == WordMapping.nilConstructor then pure [] else .error "wrong mapping constructor"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor == WordMapping.consConstructor do throw "wrong mapping constructor"
      pure ((key, value) :: (← mapping tail))
  | _ => .error "invalid mapping"

-- Independently obtained with `cast compute-address 0x...aaaa --nonce 7`.
private def createdAddress : Nat := 0x21e44f0740e8cf48922d40250130b7fa7d305f15
private def initialLogs := entries [(0, 9)]
private structure Scenario where
  creator : Nat := 0xaaaa
  nonce : Nat := 7
  balance : Nat := 100
  value : Nat := 17
  target : Nat := createdAddress
  targetBalance : Nat := 5
  targetNonce : Nat := 0
  targetCode : Option (List UInt8) := some []
  create2 : Bool := false
  init : List UInt8 := bytes [0]
  output : List UInt8 := bytes [0x60, 0, 0xfe]
  outputLength : Nat := 3
  childOk : Bool := true
  childError : Option Nat := none
  installError : Option Nat := none

private def accounts (scenario : Scenario) : List AccountState.Account := [
  {address := word scenario.creator, nonce := word scenario.nonce, code := some (bytes [0x60])},
  {address := word scenario.target, storage := entries [(1, 99)], transient := entries [(2, 88)],
    nonce := word scenario.targetNonce, code := scenario.targetCode}]
private def ledger (scenario : Scenario) : WordMapping.Entries :=
  entries [(scenario.creator, scenario.balance), (scenario.target, scenario.targetBalance)]

private def program (scenario : Scenario) : Program := {
  dataDefinitions := AccountState.definitions
  resultType := bundleType [LanguageResult.resultType Creation.responseType, AccountState.type,
    WordMapping.type, WordMapping.type, .word]
  body := (bind (allocate AccountState.type (constant (AccountState.literal ((accounts scenario).map (·, 0))))) fun world =>
    bind (allocate WordMapping.type (constant (WordMapping.literal (ledger scenario)))) fun balances =>
    bind (allocate WordMapping.type (constant (WordMapping.literal initialLogs))) fun logs =>
    bind (allocate .word (number 1)) fun logSize =>
    let runInit (target request : Code) : Code :=
      bindResult Calls.responseType (fun depth => AccountState.writeStorage (world depth) (target depth)
        (.bool true) (.word (word 1)) (.word (word 42))) fun _ =>
      bindResult Calls.responseType (fun depth => AccountState.writeStorage (world depth) (target depth)
        (.bool true) (.word (word 3)) (part 1 8 request depth)) fun _ =>
      bind (store logs (constant (WordMapping.literal (entries [(0, 77)])))) fun _ =>
      bind (store logSize (number 2)) fun _ =>
      match scenario.childError with
      | some reason => failure Calls.responseType (number reason)
      | none => success (packet [boolean scenario.childOk,
          constant (WordMapping.literal (Memory.packBytes scenario.output)), number scenario.outputLength])
    let install (target child : Code) : Code :=
      bindResult .unit (fun depth => AccountState.writeField (world depth) (target depth) (.bool true) 3
        (.word (word 73))) fun _ =>
      match scenario.installError with
      | some reason => failure .unit (number reason)
      | none =>
          bindResult .unit (fun depth => AccountState.writeField (world depth) (target depth) (.bool true) 4
            (part 1 3 child depth)) fun _ =>
          fun depth => AccountState.writeField (world depth) (target depth) (.bool true) 5
            (part 2 3 child depth)
    let request := packet [number scenario.creator, number scenario.value, number 0, boolean scenario.create2,
      number 1, number 100000, constant (WordMapping.literal (Memory.packBytes scenario.init)),
      number scenario.init.length]
    bind (CreationRuntime.dispatch world balances logs logSize (boolean true) request runInit install) fun result =>
    packet [result, load world, load balances, load logs, load logSize]) 0
}

private structure Snapshot where
  status : Value
  world : Value
  accounts : List AccountState.Account
  balances : WordMapping.Entries
  logs : WordMapping.Entries
  logSize : Nat

private def snapshot (value : Value) : IO Snapshot := do
  let .pair status (.pair world (.pair balances (.pair logs (.word logSize)))) := value
    | throw (IO.userError "invalid creation snapshot")
  pure ⟨status, world, ← get (AccountState.decode world), ← get (mapping balances),
    ← get (mapping logs), logSize.val⟩
private def execute (label : String) (scenario : Scenario) : IO Snapshot := do
  let compiled := program scenario
  match inferDetailed [] [] compiled.body compiled.dataDefinitions with
  | .error error => throw (IO.userError s!"{label}: ill-typed Core: {reprStr error}")
  | .ok actual => require (actual == compiled.resultType) s!"{label}: wrong result type"
  match compiled.runStateful 10000000 with
  | .done value _ => snapshot value
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def account (snapshot : Snapshot) (address : Nat) : IO AccountState.Account :=
  match snapshot.accounts.find? (·.address == word address) with
  | some value => pure value
  | none => throw (IO.userError s!"missing account {address}")
private def returned (label : String) (snapshot : Snapshot) (address : Nat)
    (data : List UInt8 := []) : IO Unit := do
  let .inRight _ (.pair (.word actualAddress) (.pair actualData (.word length))) := snapshot.status
    | throw (IO.userError s!"{label}: did not return a creation response: {reprStr snapshot.status}")
  let actualData ← get (mapping actualData)
  let actualBytes := (List.range length.val).map fun index =>
    UInt8.ofNat (Memory.lookupByte actualData (word index)).val
  require (actualAddress == word address && actualBytes == data)
    s!"{label}: wrong creation address or return data"
private def rolledBack (label : String) (snapshot : Snapshot) (scenario : Scenario) (nonce : Nat) : IO Unit := do
  let creator ← account snapshot scenario.creator
  let target ← account snapshot scenario.target
  require (creator.nonce == word nonce) s!"{label}: creator nonce did not follow the checkpoint rule"
  require (target.storage == entries [(1, 99)] && target.transient == entries [(2, 88)] &&
    target.nonce == word scenario.targetNonce && target.code == scenario.targetCode && !target.created)
    s!"{label}: target state escaped rollback"
  require (snapshot.balances == ledger scenario && snapshot.logs == initialLogs && snapshot.logSize == 1)
    s!"{label}: balance or log state escaped rollback"

private def successTests : IO Unit := do
  let scenario : Scenario := {}
  let actual ← execute "successful creation" scenario
  returned "successful creation" actual createdAddress
  let creator ← account actual scenario.creator
  let target ← account actual scenario.target
  require (creator.nonce == word 8 && target.nonce == word 1 && target.created && !target.destroyed)
    "successful creation nonce or lifecycle flags"
  require (target.storage == entries [(1, 42), (3, 17)] && target.transient.isEmpty &&
    target.code == some scenario.output) "constructor state or deployed bytes were not installed"
  require (actual.balances == entries [(scenario.creator, 83), (scenario.target, 22)])
    "creation did not preserve prefunding or transfer value"
  require (actual.logs == entries [(0, 77)] && actual.logSize == 2) "successful constructor logs were lost"
  let emptyScenario : Scenario := {init := [], childError := some 77}
  let empty ← execute "empty init skips constructor" emptyScenario
  returned "empty init" empty createdAddress
  let target ← account empty emptyScenario.target
  require (target.storage.isEmpty && target.code == some [] && target.nonce == word 1 && target.created)
    "empty init did not create an empty account"
  require (empty.logs == initialLogs && empty.logSize == 1) "empty init ran the constructor callback"
  let create2 : Scenario := {
    creator := 0
    nonce := 0
    value := 0
    create2 := true
    target := 0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38
    output := []
    outputLength := 0
  }
  let actual ← execute "CREATE2 EIP-1014 address" create2
  returned "CREATE2" actual create2.target
  require ((← account actual 0).nonce == word 1) "CREATE2 did not increment creator nonce"
  let boundary : Scenario := {output := bytes [0x60], outputLength := 24576}
  let actual ← execute "maximum deployed code length" boundary
  returned "maximum deployed code length" actual createdAddress
  let target ← account actual boundary.target
  require (target.code.map List.length == some 24576) "maximum deployed code length was rejected"

private def failureTests : IO Unit := do
  for (label, scenario) in [
    ("insufficient balance", {value := 101 : Scenario}),
    ("nonce exhausted", {nonce := 2 ^ 64 - 1 : Scenario}),
    ("nonce outside protocol range", {nonce := 2 ^ 64 : Scenario})] do
    let actual ← execute label scenario
    returned label actual 0
    rolledBack label actual scenario scenario.nonce
  for (label, scenario) in [
    ("nonce collision", {targetNonce := 1 : Scenario}),
    ("code collision", {targetCode := some (bytes [0x60]) : Scenario}),
    ("oversized deployed code", {outputLength := 24577 : Scenario}),
    ("reserved deployed code prefix", {output := bytes [0xef], outputLength := 1 : Scenario})] do
    let actual ← execute label scenario
    returned label actual 0
    rolledBack label actual scenario 8
  let reverting : Scenario := {childOk := false, output := bytes [0xde, 0xad], outputLength := 2}
  let actual ← execute "constructor revert" reverting
  returned "constructor revert" actual 0 reverting.output
  rolledBack "constructor revert" actual reverting 8
  for (label, reason, scenario) in [
    ("constructor language failure", 77, {childError := some 77 : Scenario}),
    ("installation failure", 88, {installError := some 88 : Scenario}),
    ("balance overflow", 12, {targetBalance := wordModulus - 1, value := 1 : Scenario}),
    ("unknown target code", 7, {targetCode := none : Scenario})] do
    let actual ← execute label scenario
    require (actual.status == .inLeft Creation.responseType (scalar reason))
      s!"{label}: language failure was not propagated"
    rolledBack label actual scenario 8

def run : IO Unit := do
  successTests
  failureTests
  let compiled := program {}
  match compiled.runStateful 1000 with
  | .outOfFuel checkpoint =>
      match runStateful 10000000 checkpoint with
      | .done value _ =>
          let actual ← snapshot value
          returned "creation resumes" actual createdAddress
          require ((← account actual 0xaaaa).nonce == word 8) "resumed creation incremented nonce twice"
      | other => throw (IO.userError s!"resumed creation: {reprStr other}")
  | other => throw (IO.userError s!"creation did not suspend: {reprStr other}")

end Tests.RustHullCreationRuntime
end

section
-- leanmerge: from Solcore.Test.RustHullEffectReceipts
/-! Effects exercised through the public Hull object compiler and Core runner. -/
set_option autoImplicit false
namespace Tests.RustHullEffectReceipts
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def name (value : String) : YulName := {name := value}
private def w (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def call (value : String) (args : List YulExpr := []) : YulExpr := ⟨.call (name value) args, none⟩
private def action (value : String) (args : List YulExpr := []) : YulStmt := ⟨.expression (call value args), none⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def wordBytes (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value / 256 ^ (31 - index) % 256)
private def source (body : List YulStmt) : Program := {
  functions := []
  entryPoints := []
  objects := [.object "Runtime" {stmts := [⟨.assembly body, none⟩], functions := []} [] none]
}
private def prepare (label : String) (body : List YulStmt) (context : Contract.Context := {}) :
    IO Contract.Prepared :=
  match Contract.prepare (source body) ["Runtime"] context with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def returned (label : String) (receipt : Contract.Receipt) (expected : List UInt8)
    (logs : List Logs.Event := []) : IO Core.WordMapping.Entries := do
  require (receipt.logs == logs) s!"{label}: incorrect logs {reprStr receipt.logs}"
  match receipt.outcome with
  | .returned actual storage =>
      require (actual == expected) s!"{label}: incorrect output {reprStr actual}"
      pure storage
  | outcome => throw (IO.userError s!"{label}: {reprStr outcome}")
private def slot (entries : Core.WordMapping.Entries) (key value : Nat) : Bool :=
  Core.WordMapping.lookupEntries (word key) entries == word value

private def resumeUntil : Nat → Contract.Receipt → IO Contract.Receipt
  | 0, _ => throw (IO.userError "receipt resumption did not finish")
  | fuel + 1, receipt =>
      match receipt.outcome with
      | .outOfFuel state => do
          require receipt.logs.isEmpty "suspended execution published logs"
          resumeUntil fuel (Contract.resumeWithReceipt state 1000)
      | _ => pure receipt

private def logTests : IO Unit := do
  let input := "abc".toUTF8.toList
  let modified : List UInt8 := [0xee, 0x62, 0x63]
  let context : Contract.Context := {
    calldata := input
    address := word 0xabcd
    caller := word 0x456
    storage := [(word 9, word 5)]
  }
  let body := [action "calldatacopy" [w 0, w 0, w 3], action "log0" [w 0, w 3],
    action "mstore8" [w 0, w 0xee], action "emit", action "sstore" [w 9, w 77],
    action "return" [w 0, w 3], action "log0" [w 0, w 0],
    ⟨.functionDef (name "emit") [] [] [action "log2" [w 0, w 3, w 0x123, call "caller"]], none⟩]
  let prepared ← prepare "ordered logs with a local function" body context
  let logs : List Logs.Event := [
    {address := word 0xabcd, topics := [], data := input},
    {address := word 0xabcd, topics := [word 0x123, word 0x456], data := modified}]
  let storage ← returned "snapshot and local function effects" (Contract.runWithReceipt prepared) modified logs
  require (slot storage 9 77) "successful receipt lost storage writes"
  let suspended := Contract.runWithReceipt prepared 100
  match suspended.outcome with
  | .outOfFuel _ => pure ()
  | other => throw (IO.userError s!"receipt fixture should suspend: {reprStr other}")
  let resumed ← returned "repeated receipt resumption" (← resumeUntil 1000 suspended) modified logs
  require (slot resumed 9 77) "resumed receipt lost storage writes"
  let allTopics := (List.range 5).map fun count =>
    action s!"log{count}" ([w (Core.wordModulus - 1), w 0] ++ (List.range count).map w)
  let prepared ← prepare "log0 through log4" (allTopics ++ [action "stop"]) context
  let expected := (List.range 5).map fun count =>
    {address := word 0xabcd, topics := (List.range count).map word, data := [] : Logs.Event}
  let _ ← returned "all topic counts and empty maximal offset" (Contract.runWithReceipt prepared) [] expected
  let common := [action "mstore8" [w 0, w 0xde], action "log1" [w 0, w 1, w 9],
    action "sstore" [w 9, w 99]]
  for exit in ["revert", "invalid"] do
    let args := if exit == "revert" then [w 0, w 1] else []
    let prepared ← prepare s!"{exit} discards logs" (common ++ [action exit args]) context
    let result := Contract.runWithReceipt prepared
    require result.logs.isEmpty s!"{exit} published logs"
    match exit, result.outcome with
    | "revert", .reverted bytes => require (bytes == [0xde]) "wrong revert payload"
    | "invalid", .invalid => pure ()
    | _, other => throw (IO.userError s!"{exit}: {reprStr other}")
    require (slot prepared.context.storage 9 5) "failed frame changed its input storage"
  let prepared ← prepare "language failure discards logs"
    (common ++ [action "pop" [call "gas"]]) context
  let result := Contract.runWithReceipt prepared
  require result.logs.isEmpty "language failure published logs"
  match result.outcome with
  | .languageFailure (.word reason) => require (reason == word 9) "wrong unavailable gas failure"
  | other => throw (IO.userError s!"missing gas context: {reprStr other}")
  let prepared ← prepare "receipt export limit" [action "calldatacopy" [w 0, w 0, w 3],
    action "log0" [w 0, w 3], action "stop"] context
  let result := Contract.runWithReceipt prepared 1000000 2
  require result.logs.isEmpty "failed receipt export published logs"
  match result.outcome with
  | .exportError _ => pure ()
  | other => throw (IO.userError s!"log export limit was ignored: {reprStr other}")

private def gasTests : IO Unit := do
  let prepared ← prepare "available gas environment input"
    [action "mstore" [w 0, call "gas"], action "mstore" [w 32, call "gas"], action "return" [w 0, w 64]]
    {availableGas := some (word 123456)}
  let _ ← returned "supplied gas stays an explicit environment value" (Contract.runWithReceipt prepared)
    (wordBytes 123456 ++ wordBytes 123456)
  pure ()

private def precompileTests : IO Unit := do
  let input := "abc".toUTF8.toList
  let context : Contract.Context := {calldata := input, address := word 0x42, availableGas := some (word 18)}
  let initial := [action "calldatacopy" [w 0, w 0, w 3],
    action "sstore" [w 0, call "staticcall" [call "gas", w 4, w 0, w 3, w 64, w 2]],
    action "sstore" [w 1, call "returndatasize"]]
  let prepared ← prepare "identity through public effects" (initial ++ [
    action "mstore8" [w 0, w 0xee], action "returndatacopy" [w 96, w 0, w 3],
    action "log1" [w 96, w 3, w 4], action "return" [w 64, w 35]]) context
  let storage ← returned "identity return data snapshot" (Contract.runWithReceipt prepared)
    ([0x61, 0x62] ++ List.replicate 30 0 ++ input)
    [{address := word 0x42, topics := [word 4], data := input}]
  require (slot storage 0 1 && slot storage 1 3) "identity call status or return size is wrong"
  let digest := 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
  let prepared ← prepare "SHA256 through public effects" [
    action "calldatacopy" [w 0, w 0, w 3],
    action "sstore" [w 0, call "staticcall" [w 72, w 2, w 0, w 3, w 64, w 7]],
    action "sstore" [w 1, call "returndatasize"], action "log0" [w 64, w 7],
    action "returndatacopy" [w 128, w 0, w 32], action "return" [w 128, w 32]] context
  let storage ← returned "SHA256 retains full return data" (Contract.runWithReceipt prepared)
    (wordBytes digest) [{address := word 0x42, topics := [], data := (wordBytes digest).take 7}]
  require (slot storage 0 1 && slot storage 1 32) "SHA256 call status or return size is wrong"
  for (offset, length, valid) in [(3, 0, true), (4, 0, false), (2, 2, false), (0, 4, false),
      (Core.wordModulus - 1, 1, false)] do
    let prepared ← prepare "return data bounds" (initial ++ [action "log0" [w 0, w 0],
      action "returndatacopy" [w (if length == 0 then Core.wordModulus - 1 else 128), w offset, w length],
      action "stop"]) context
    let result := Contract.runWithReceipt prepared
    if valid then
      let _ ← returned "empty copy exactly at return-data end" result []
        [{address := word 0x42, topics := [], data := []}]
      pure ()
    else
      require result.logs.isEmpty "out-of-bounds return data copy published logs"
      match result.outcome with
      | .invalid => pure ()
      | other => throw (IO.userError s!"return data bounds {offset} {length}: {reprStr other}")
  let prepared ← prepare "initial return data is empty"
    [action "returndatacopy" [w 0, w 1, w 0], action "stop"]
  match (Contract.runWithReceipt prepared).outcome with
  | .invalid => pure ()
  | other => throw (IO.userError s!"initial return-data bounds: {reprStr other}")

def run : IO Unit := do
  logTests
  gasTests
  precompileTests

end Tests.RustHullEffectReceipts
end

section
-- leanmerge: from Solcore.Test.RustHullEnvironmentCorrespondence
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
end

section
-- leanmerge: from Solcore.Test.RustHullLifecycleCorrespondence
/-! A child schedules account destruction, then its parent observes the code
and continues. Transaction finalization and a parent revert are separate steps. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.RustHullLifecycleCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
private abbrev w := Core.Word.ofNatModulo
inductive Scenario where | existing | created | parentReverted
  deriving BEq, DecidableEq, Repr
def created (scenario : Scenario) : Bool := scenario != .existing
def reverts (scenario : Scenario) : Bool := scenario == .parentReverted
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def byte (offset data : String) : Expr := call .unit "mstore8" [word offset, word data]
def storage (key data : String) : Expr := call .unit "sstore" [word key, word data]
def childCode : CodeBlock := {stmts := [expression (byte "0" "187"), expression (storage "8" "99"),
  expression (call .unit "log0" [word "0", word "1"]), expression (call .unit "selfdestruct" [word "200"])], functions := []}
def invoke : Expr := call .word "call" [word "100", word "100", word "0", word "0", word "0", word "0", word "0"]
def storedStatus : Expr := call .unit "mstore8" [word "0", invoke]
def storedSize : Expr := call .unit "mstore8" [word "1", call .word "extcodesize" [word "100"]]
def finish (scenario : Scenario) : Expr := call .unit (if reverts scenario then "revert" else "return") [word "0", word "3"]
def code (scenario : Scenario) : CodeBlock := {stmts := [expression (byte "2" "170"), expression (storage "7" "42"),
  expression storedStatus, expression storedSize, expression (finish scenario)], functions := []}
def program (scenario : Scenario) : Program := {
  entryPoints := []
  functions := []
  objects := [.object "Parent" (code scenario) [], .object "Child" childCode []]
}
def childBytes : List UInt8 := [0x60, 0x00]
def compiledCatalog (scenario : Scenario) : List AccountRuntime.CodeDefinition :=
  [{program := program scenario, path := ["Child"], bytes := childBytes}]
def sourceCode (scenario : Scenario) : ChildFrameSemantics.Code := ⟨program scenario, childCode, childBytes⟩
def catalog (scenario : Scenario) : ChildFrameModeSemantics.Catalog := [(w 100, sourceCode scenario)]
def parentEffects (scenario : Scenario) := ChildFrameModeSemantics.effectsAt (catalog scenario) {} 1 none
def childEffects (scenario : Scenario) := ChildFrameModeSemantics.effectsAt (catalog scenario) {} 0 (some childBytes)
def parentFunctions (scenario : Scenario) := [AccountRuntime.frameFunction (code scenario)]
def childFunctions := [AccountRuntime.frameFunction childCode]
def childAccount (scenario : Scenario) : AccountState.Account :=
  {address := w 100, code := some childBytes, nonce := w 1, created := created scenario}
def context (scenario : Scenario) : Contract.Context :=
  {balance := w 100, accounts := [(w 100, w 60), (w 200, w 20)], world := [childAccount scenario], completeWorld := true}
abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def runtime (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withRuntime (state : SourceState) (next : RuntimeEffectsSemantics.State) : SourceState :=
  {state with external := {state.external with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime next}}
def written (state : SourceState) (offset data : Core.Word) : SourceState :=
  withRuntime state {runtime state with memory := (MemorySemantics.mstore8 (runtime state).memory offset data).2}
def stored (state : SourceState) (key data : Core.Word) : SourceState :=
  withRuntime state {runtime state with storage := (StorageSemantics.store (runtime state).storage key data false).2}
def initial (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState none object (Contract.normalizeContext (context scenario))⟩
def parentWritten (object : Contract.CompiledObject) (scenario : Scenario) := written (initial object scenario) (w 2) (w 170)
def parentBefore (object : Contract.CompiledObject) (scenario : Scenario) := stored (parentWritten object scenario) (w 7) (w 42)
def arguments (object : Contract.CompiledObject) (scenario : Scenario) :=
  RuntimeCallModeSemantics.arguments .ordinary (parentBefore object scenario).external (w 100) (w 100) (w 0) (w 0) (w 0) (w 0) (w 0)
def request (object : Contract.CompiledObject) (scenario : Scenario) := CallTransportSemantics.request (arguments object scenario) []
def childInitial (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], ChildFrameModeSemantics.initial .ordinary (w 0) (parentBefore object scenario).external
    (request object scenario) (RuntimeCallModeSemantics.shared (parentBefore object scenario).external) childBytes⟩
def childWritten (object : Contract.CompiledObject) (scenario : Scenario) := written (childInitial object scenario) (w 0) (w 187)
def childStored (object : Contract.CompiledObject) (scenario : Scenario) := stored (childWritten object scenario) (w 8) (w 99)
def childLogged (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := childStored object scenario
  let old := state.external.runtime.runtime.runtime
  let logs := RuntimeLogEffectsSemantics.logsState old
  let next := RuntimeLogEffectsSemantics.withLogs old {logs with
    words := Tests.RustHullNestedChildCallCorrespondence.logWords logs (w 0), cursor := LogsSemantics.nextCursor logs.cursor (w 1) []}
  {state with external := {state.external with runtime := {state.external.runtime with runtime := {state.external.runtime.runtime with runtime := next}}}}
def destroyedWorld (object : Contract.CompiledObject) (scenario : Scenario) :=
  AccountLifecycleSemantics.publish (runtime (childLogged object scenario)).storage.world (w 100)
    {childAccount scenario with storage := [(w 8, w 99)]}
def destroyedBalances : StorageSemantics.Words := [(w 100, w 0), (w 200, w 80), (w 0, w 100)]
def childFinal (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := childLogged object scenario
  {state with external := (RuntimeLifecycleSemantics.terminate
    (RuntimeLifecycleSemantics.updated state.external (destroyedWorld object scenario) destroyedBalances) 1).2}
def response : AccountCallSemantics.Response := AccountCallSemantics.emptyResponse true
def afterCall (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := parentBefore object scenario
  {state with external := (RuntimeCallModeSemantics.withTransport state.external ⟨(runtime state).memory, [], w 0⟩
    (RuntimeCallModeSemantics.shared (childFinal object scenario).external))}
def afterStatus (object : Contract.CompiledObject) (scenario : Scenario) := written (afterCall object scenario) (w 0) (w 1)
def afterSize (object : Contract.CompiledObject) (scenario : Scenario) := written (afterStatus object scenario) (w 1) (w 2)
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withRuntime (afterSize object scenario) (TerminationSemantics.terminate (runtime (afterSize object scenario))
    (if reverts scenario then 2 else 1) (w 0) (w 3)).2
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem child_written_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr childFunctions (childEffects scenario) [] (byte "0" "187")
      (childInitial object scenario) (.value .unit) (childWritten object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "187") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem child_stored_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr childFunctions (childEffects scenario) [] (storage "8" "99")
      (childWritten object scenario) (.value .unit) (childStored object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "8") rfl) (.cons (.word (text := "99") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem log_copied (state : LogsSemantics.State) :
    LogsSemantics.Copy state.memory.words (w 0) (w 1)
      (LogsSemantics.insertWords state.words state.cursor (LogsSemantics.headers state.address (w 1) []))
      (state.cursor.add (w 3)) (Tests.RustHullNestedChildCallCorrespondence.logWords state (w 0)) := by
  apply LogsSemantics.Copy.step (by decide +kernel)
  exact .empty _ _ _

private theorem child_logged_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr childFunctions (childEffects scenario) [] (call .unit "log0" [word "0", word "1"])
      (childStored object scenario) (.value .unit) (childLogged object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply RuntimeCallModeSemantics.Builtin.runtime
  apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
  apply RuntimeCodeEffectsSemantics.Builtin.runtime
  apply RuntimeAccountEffectsSemantics.Builtin.runtime
  apply RuntimeHashEffectsSemantics.Builtin.runtime
  apply RuntimeCopyEffectsSemantics.Builtin.runtime
  apply RuntimeFullEffectsSemantics.Builtin.runtime
  apply RuntimeLogEffectsSemantics.Builtin.logs
  apply LogsSemantics.Builtin.log .log0 .unit (w 0) (w 1) [] rfl
  apply LogsSemantics.Execute.writable rfl
  apply LogsSemantics.Append.done (size := w 32)
  · decide +kernel
  · change ¬w 0 > LogsSemantics.nextCursor (w 0) (w 1) []
    decide +kernel
  · change MemorySemantics.touchSize? (w 32) (w 0) (w 1) = some (w 32)
    decide +kernel
  · exact log_copied _

private theorem child_world (object : Contract.CompiledObject) (scenario : Scenario) :
 (runtime (childLogged object scenario)).storage.world =
 StorageSemantics.put (w 100) {childAccount scenario with storage := [(w 8, w 99)]}
   (runtime (parentBefore object scenario)).storage.world := by
  have address : (runtime (childWritten object scenario)).storage.address = w 100 := by
    change (w 100).bitAnd (w (2 ^ 160 - 1)) = w 100
    decide +kernel
  have found : StorageSemantics.get (runtime (childWritten object scenario)).storage.world (w 100) true =
    .ok (childAccount scenario) := rfl
  change (StorageSemantics.store (runtime (childWritten object scenario)).storage (w 8) (w 99) false).2.world = _
  unfold StorageSemantics.store
  change (match StorageSemantics.writeStorage (runtime (childWritten object scenario)).storage.world
    (runtime (childWritten object scenario)).storage.address true (w 8) (w 99) false with
    | .ok world => world
    | .error _ => (runtime (childWritten object scenario)).storage.world) = _
  rw [address]
  unfold StorageSemantics.writeStorage
  rw [found]
  rfl

theorem child_destroyed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr childFunctions (childEffects scenario) [] (call .unit "selfdestruct" [word "200"])
      (childLogged object scenario) result (childFinal object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "200") rfl) .nil)
  apply Semantics.EvalCall.external rfl rfl
  apply RuntimeCallModeSemantics.Builtin.destroy
  apply RuntimeLifecycleSemantics.Destroy.completed (state := (childLogged object scenario).external) (world := destroyedWorld object scenario) (balances := destroyedBalances) rfl
  change AccountLifecycleSemantics.destroy (runtime (childLogged object scenario)).storage.world
    (childLogged object scenario).external.runtime.runtime.balances (w 100) (w 200) true =
      .ok (destroyedWorld object scenario, destroyedBalances)
  have found : StorageSemantics.get (runtime (childLogged object scenario)).storage.world (w 100) true =
      .ok {childAccount scenario with storage := [(w 8, w 99)]} := by
    rw [child_world]
    rfl
  unfold AccountLifecycleSemantics.destroy
  change (do
    let account ← StorageSemantics.get (runtime (childLogged object scenario)).storage.world (w 100) true
    let next ← AccountLifecycleSemantics.balances account.created (w 100) (w 200)
      (childLogged object scenario).external.runtime.runtime.balances
    pure (AccountLifecycleSemantics.publish (runtime (childLogged object scenario)).storage.world (w 100) account, next)) = _
  rw [found]
  cases scenario <;> rfl

theorem child_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction childFunctions (childEffects scenario) (AccountRuntime.frameFunction childCode) []
      (childInitial object scenario) result (childFinal object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_written_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_stored_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (child_logged_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (child_destroyed_source object scenario))
    (by intro impossible; cases impossible)

theorem child_response (object : Contract.CompiledObject) (scenario : Scenario) :
    ChildResultSemantics.Respond (ChildFrameModeSemantics.completedStatus result (runtime (childFinal object scenario)))
      (runtime (childFinal object scenario)) (.value response) := by
  apply ChildResultSemantics.Respond.returned (data := .value []) rfl
  exact .empty rfl

theorem child_called (object : Contract.CompiledObject) (scenario : Scenario) :
    ChildFrameModeSemantics.Children (catalog scenario) (ChildFrameModeSemantics.effectsAt (catalog scenario) {} 0)
      (parentBefore object scenario).external .ordinary (w 0) (request object scenario)
      (RuntimeCallModeSemantics.shared (parentBefore object scenario).external) (.value response)
      (RuntimeCallModeSemantics.shared (childFinal object scenario).external) := by
  apply ChildFrameModeSemantics.Children.executed (account := childAccount scenario) (code := sourceCode scenario)
  · change AccountCallSemantics.isPrecompile (w 100) = false
    decide +kernel
  · rfl
  · rfl
  · rfl
  · exact child_source object scenario
  · exact child_response object scenario

theorem invoked (object : Contract.CompiledObject) (scenario : Scenario) :
    RuntimeCallModeSemantics.Call (ChildFrameModeSemantics.Children (catalog scenario) (ChildFrameModeSemantics.effectsAt (catalog scenario) {} 0))
      .ordinary (w 100) (w 100) (w 0) (w 0) (w 0) (w 0) (w 0) (parentBefore object scenario).external
      (.value (.word (w 1))) (afterCall object scenario).external := by
  apply RuntimeCallModeSemantics.Call.invoked
  · exact .inr (.inl rfl)
  · intro _ impossible
    exact False.elim (impossible rfl)
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 32) rfl rfl
  apply CallTransportSemantics.Dispatch.returned (input := {}) (response := response) (result := .value .unit)
  · change ¬w 0 > w 1023
    decide +kernel
  · exact .done rfl (.empty _ _ _ _)
  · rfl
  · apply AccountCallSemantics.Dispatch.succeeded (transferred := RuntimeCallModeSemantics.shared (parentBefore object scenario).external)
    · exact .inr (by change ¬w 0 > w 100; decide +kernel)
    · rfl
    · exact .child (child_called object scenario)
    · rfl
  · exact .done rfl (.empty _ _ _ _)

private theorem byte_builtin (children : RuntimeCallModeSemantics.State → AccountCallSemantics.Children)
    (image : Option (List UInt8)) (state : SourceState) (offset data size : Core.Word)
    (touched : MemorySemantics.touchSize? (runtime state).memory.size offset (w 1) = some size) :
    RuntimeCallModeSemantics.Builtin children image "mstore8" .unit [.word offset, .word data] state.external
      (.value .unit) (written state offset data).external := by
  apply RuntimeCallModeSemantics.Builtin.runtime
  apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
  apply RuntimeCodeEffectsSemantics.Builtin.runtime
  apply RuntimeAccountEffectsSemantics.Builtin.runtime
  apply RuntimeHashEffectsSemantics.Builtin.runtime
  apply RuntimeCopyEffectsSemantics.Builtin.runtime
  apply RuntimeFullEffectsSemantics.Builtin.runtime
  apply RuntimeLogEffectsSemantics.Builtin.runtime
  simp only [runtime] at touched
  simp only [RuntimeEnvironmentEffectsSemantics.builtin, RuntimeEffectsSemantics.builtin,
    MemorySemantics.builtin, MemorySemantics.mstore8, runtime, touched]

private theorem call_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] invoke
      (parentBefore object scenario) (.value (.word (w 1))) (afterCall object scenario) := by
  apply Semantics.EvalExpr.call rfl
    (.cons (.word (text := "100") rfl) (.cons (.word (text := "100") rfl) (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl)
        (.cons (.word (text := "0") rfl) .nil)))))))
  exact .external rfl rfl (.call (invoked object scenario))

private theorem status_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] storedStatus
      (parentBefore object scenario) (.value .unit) (afterStatus object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (call_source object scenario) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply byte_builtin (size := w 32)
  change MemorySemantics.touchSize? (w 32) (w 0) (w 1) = some (w 32)
  decide +kernel

theorem code_still_observable (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (call .word "extcodesize" [word "100"])
      (afterStatus object scenario) (.value (.word (w 2))) (afterStatus object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "100") rfl) .nil)
  apply Semantics.EvalCall.external rfl rfl
  apply RuntimeCallModeSemantics.Builtin.runtime
  apply RuntimeReturnDataEffectsSemantics.Builtin.runtime
  apply RuntimeCodeEffectsSemantics.Builtin.runtime
  apply RuntimeAccountEffectsSemantics.Builtin.observation
  apply AccountObservationSemantics.Builtin.sizeKnown (bytes := childBytes)
    (account := {childAccount scenario with storage := [(w 8, w 99)], destroyed := created scenario})
  · change StorageSemantics.get (destroyedWorld object scenario) (AccountObservationSemantics.address (w 100)) true = _
    have masked : AccountObservationSemantics.address (w 100) = w 100 := by decide +kernel
    rw [masked]
    unfold destroyedWorld
    rw [child_world]
    cases scenario <;> rfl
  · rfl

private theorem size_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] storedSize
      (afterStatus object scenario) (.value .unit) (afterSize object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "1") rfl) (.cons (code_still_observable object scenario) .nil))
  apply Semantics.EvalCall.external rfl rfl
  apply byte_builtin (size := w 32)
  change MemorySemantics.touchSize? (w 32) (w 1) (w 1) = some (w 32)
  decide +kernel

private theorem parent_written_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (byte "2" "170")
      (initial object scenario) (.value .unit) (parentWritten object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "2") rfl) (.cons (.word (text := "170") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem parent_stored_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (storage "7" "42")
      (parentWritten object scenario) (.value .unit) (parentBefore object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "7") rfl) (.cons (.word (text := "42") rfl) .nil))
  exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem finish_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (parentFunctions scenario) (parentEffects scenario) [] (finish scenario)
      (afterSize object scenario) result (finalState object scenario) := by
  cases scenario <;> apply Semantics.EvalExpr.call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "3") rfl) .nil))
  all_goals exact .external rfl rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (parentFunctions scenario) (parentEffects scenario) (AccountRuntime.frameFunction (code scenario)) []
      (initial object scenario) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (parent_written_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (parent_stored_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (status_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (size_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (finish_source object scenario))
    (by intro impossible; cases impossible)

def runtimeNames : List String := ["mstore8", "sstore", "log0", "extcodesize", "return", "revert"]
def usedNames : List String := runtimeNames ++ ["call", "selfdestruct"]

private theorem atoms {supported : String → Prop} (functions : List Function) (type : Ty) (name : String)
    (arguments : List String) (available : supported name)
    (absent : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (call type name (arguments.map word)) := by
  apply ExecutableExpression.external (name := name) available absent
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

theorem child_eligible {supported : String → Prop} (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported childFunctions := by
  intro function member statement statementMember
  simp only [childFunctions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, childCode, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["0", "187"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "sstore" ["8", "99"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "log0" ["0", "1"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "selfdestruct" ["200"] (available _ (by simp [usedNames, runtimeNames])) rfl

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) : ExecutableProgram supported (parentFunctions scenario) := by
  intro function member statement statementMember
  simp only [parentFunctions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["2", "170"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · exact atoms _ .unit "sstore" ["7", "42"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) rfl
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · exact atoms _ .word "call" ["100", "100", "0", "0", "0", "0", "0"] (available _ (by simp [usedNames])) rfl
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames, runtimeNames])) rfl
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · exact atoms _ .word "extcodesize" ["100"] (available _ (by simp [usedNames, runtimeNames])) rfl
  · cases scenario <;> first
      | exact atoms _ .unit "return" ["0", "3"] (available _ (by simp [usedNames, runtimeNames])) rfl
      | exact atoms _ .unit "revert" ["0", "3"] (available _ (by simp [usedNames, runtimeNames])) rfl

private theorem runtime_supported : ∀ name ∈ runtimeNames, ContractCodeCorrespondence.supported name := by
  intro name member
  simp only [runtimeNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (⟨.store8, rfl⟩))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.store false, rfl⟩)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inr ⟨.log0, rfl⟩)))))
  · exact .inl (.inr ⟨.size, rfl⟩)
  · exact .inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))
  · exact .inl (.inl (.inl (.inl (.inr ⟨.reverted, rfl⟩))))

theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with prior | rfl | rfl
  · exact .inl (.inl (runtime_supported name prior))
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))

end Tests.RustHullLifecycleCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullLifecyclePublic
/-! A child account destruction reaches public execution and resumption,
including successful finalization and a revert by the parent frame. -/
set_option autoImplicit false
namespace Tests.RustHullLifecycleCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
private abbrev number := Core.Word.ofNatModulo

def anchors : List CatalogWorldCorrespondence.Anchor := [⟨number 100, childBytes, 2⟩]

theorem catalog_connection_of_eligible (scenario : Scenario)
    (childEligible : ExecutableProgram (ContractCallModeCorrespondence.supported true) childFunctions) :
    ModeChildCatalogExecutionCorrespondence.CatalogConnection (catalog scenario) (compiledCatalog scenario) anchors := by
  intro target source selected
  by_cases child : number 100 == target
  · have addressEq : number 100 = target := by simpa only [beq_iff_eq] using child
    subst target
    have sourceEq : sourceCode scenario = source := by
      simpa [ChildFrameSemantics.select, ChildFrameModeSemantics.select, catalog] using selected
    subst source
    refine ⟨0, {program := program scenario, path := ["Child"], bytes := childBytes},
      rfl, rfl, rfl, rfl, ?_, ?_, ?_, childEligible⟩
    · simp [anchors, sourceCode]
    · decide +kernel
    · change (List.range 2).find? (fun candidate => number 2 == number (candidate + 1)) = some 1
      decide +kernel
  · simp [ChildFrameSemantics.select, catalog, child] at selected

theorem catalog_connection (scenario : Scenario) :
    ModeChildCatalogExecutionCorrespondence.CatalogConnection (catalog scenario) (compiledCatalog scenario) anchors :=
  catalog_connection_of_eligible scenario (child_eligible names_supported)

theorem initial_context_links (scenario : Scenario) (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks none (compiledCatalog scenario) object (context scenario) anchors := by
  intro anchor member
  simp only [anchors, List.mem_cons, List.not_mem_nil, or_false] at member
  subst anchor
  refine ⟨childAccount scenario, rfl, rfl, ?_, rfl⟩
  change number 100 ≠ number 0
  decide +kernel

theorem public_evaluates (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate (context scenario)).expression value final ∧
      ContractCallModeCorrespondence.PublicMessageRel (context scenario) result (finalState object scenario).external value := by
  exact ContractCallModeCorrespondence.compileObject_preserves (height := 0) (code := code scenario) (by rfl) accepted rfl
    (eligible scenario names_supported) (catalog_connection scenario) (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by cases scenario <;> decide)) (context scenario) rfl
    (initial_context_links scenario object) (source object scenario)

theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel (context scenario) result (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate (context scenario)) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl) accepted rfl
    (eligible scenario names_supported) (catalog_connection scenario) (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by cases scenario <;> decide)) (context scenario) rfl
    (initial_context_links scenario object) (source object scenario)

end Tests.RustHullLifecycleCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullLifecycleRuntime
/-! Child destruction transfers balances immediately. The public transaction
removes created accounts on success and withholds effects after a parent revert. -/
set_option autoImplicit false
namespace Tests.RustHullLifecycleRuntime
open Solcore Solcore.Frontend.RustHull RustHullLifecycleCorrespondence
private abbrev w := Core.Word.ofNatModulo

private def expectedStorage : StorageSemantics.Words := [(w 7, w 42)]
private def expectedEvents : List Logs.Event := [⟨w 100, [], [187]⟩]
private def expectedBytes : List UInt8 := [1, 2, 170]

private def checkWorld (label : String) (scenario : Scenario) (finalized : Bool)
    (world : List AccountState.Account) : IO Unit := do
  let some parent := world.find? (·.address == w 0) |
    throw (IO.userError s!"{label}: missing parent")
  unless parent.storage == expectedStorage && parent.transient.isEmpty && !parent.created && !parent.destroyed do
    throw (IO.userError s!"{label}: parent was changed by child destruction")
  if finalized && created scenario then
    unless world.length == 1 && (world.find? (·.address == w 100)).isNone do
      throw (IO.userError s!"{label}: created account was not removed")
  else
    let some child := world.find? (·.address == w 100) |
      throw (IO.userError s!"{label}: missing retained child")
    unless world.length == 2 && child.storage == [(w 8, w 99)] && child.code == some childBytes &&
        child.nonce == w 1 && child.transient.isEmpty &&
        child.created == (!finalized && created scenario) && child.destroyed == (!finalized && created scenario) do
      throw (IO.userError s!"{label}: wrong retained account for {reprStr scenario}: {reprStr child}")

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Parent"] 64 none (compiledCatalog scenario) with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"lifecycle: compile failed: {reprStr error}")
  let prepared := object.instantiate (context scenario)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"lifecycle: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"lifecycle: short resume completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 4000000, Contract.resumeWithReceipt checkpoint 4000000] do
    if reverts scenario then
      match receipt.outcome with
      | .reverted bytes =>
          unless bytes == expectedBytes && receipt.logs.isEmpty && receipt.balances.isEmpty && receipt.world.isEmpty do
            throw (IO.userError s!"lifecycle: parent revert published child effects: {reprStr receipt}")
      | outcome => throw (IO.userError s!"lifecycle: expected parent revert: {reprStr outcome}")
    else
      match receipt.outcome with
      | .returned bytes storage =>
          unless bytes == expectedBytes && storage == expectedStorage && receipt.logs == expectedEvents &&
              receipt.balances == destroyedBalances do
            throw (IO.userError s!"lifecycle: wrong result for {reprStr scenario}: {reprStr receipt}")
          checkWorld "receipt" scenario true receipt.world
      | outcome => throw (IO.userError s!"lifecycle: expected return for {reprStr scenario}: {reprStr outcome}")
  match Core.runStateful 4000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair count (.pair memory (.pair storage (.pair logs (.pair cursor (.pair balances world))))))))) _ =>
      let expected := finalState object scenario
      let state := runtime expected
      unless memory == Core.WordMapping.encode state.memory.words &&
          storage == Core.WordMapping.encode expectedStorage &&
          logs == Core.WordMapping.encode expected.external.runtime.runtime.runtime.words &&
          cursor == .word expected.external.runtime.runtime.runtime.cursor &&
          balances == Core.WordMapping.encode destroyedBalances &&
          exit == .word state.storage.exit && offset == .word state.storage.returnOffset && count == .word state.storage.returnSize do
        throw (IO.userError s!"lifecycle: snapshot differs from source for {reprStr scenario}")
      let accounts ← match AccountState.decode world with
        | .ok accounts => pure accounts
        | .error error => throw (IO.userError s!"lifecycle: bad world snapshot: {error}")
      let sourceWorld := if reverts scenario then state.storage.world else
        (StorageSemantics.finalize state.storage.world expected.external.runtime.runtime.balances).1
      unless StorageCorrespondence.world (accounts.map (fun account => (account, 0))) ==
          StorageCorrespondence.world (sourceWorld.map (fun account => (account, 0))) do
        throw (IO.userError s!"lifecycle: finalized world differs from source for {reprStr scenario}")
      checkWorld "Core snapshot" scenario (!reverts scenario) accounts
  | outcome => throw (IO.userError s!"lifecycle: Core failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.existing, .created, .parentReverted] do check scenario

end Tests.RustHullLifecycleRuntime
end

section
-- leanmerge: from Solcore.Test.RustHullRuntimeEffectsCorrespondence
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
end

section
-- leanmerge: from Solcore.Test.RustHullWorld
set_option autoImplicit false
namespace Tests.RustHullWorld
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def w (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def ident (value : String) : YulExpr := ⟨.ident ⟨value, none⟩, none⟩
private def call (name : String) (args : List YulExpr := []) : YulExpr := ⟨.call ⟨name, none⟩ args, none⟩
private def action (name : String) (args : List YulExpr := []) : YulStmt := ⟨.expression (call name args), none⟩
private def letVar (name : String) (value : YulExpr) : YulStmt := ⟨.letDecl [⟨name, none⟩] (some value), none⟩
private def wordBytes (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value / 256 ^ (31 - index) % 256)
private def words (values : List Nat) : List UInt8 := values.flatMap wordBytes
private def bytesNat (bytes : List UInt8) : Nat := bytes.foldl (fun value byte => value * 256 + byte.toNat) 0
private def hex (text : String) : List UInt8 :=
  let digit (char : Char) := if char ≤ '9' then char.toNat - '0'.toNat else char.toNat - 'a'.toNat + 10
  (List.range (text.length / 2)).map fun index =>
    UInt8.ofNat (16 * digit text.toList[2 * index]! + digit text.toList[2 * index + 1]!)
-- Exact solc0.8.35 Osaka bytes from EvmAccounts/Target.yul and observations.json.
private def targetCode : List UInt8 := hex
  "5f3580600114604657806002146039576003146034575b305f523360205234604052600754606052476080523860a05260c05ff35b602035ff5b63deadbeef5f526004601cfd5b50602035600755601656"
private def initCode : List UInt8 := hex
  "6063600755303b600855303f60095560518060195f395ff3fe5f3580600114604657806002146039576003146034575b305f523360205234604052600754606052476080523860a05260c05ff35b602035ff5b63deadbeef5f526004601cfd5b50602035600755601656"
private def revertCode : List UInt8 := hex "63deadbeef5f526004601cfd"
private def targetBody : List YulStmt :=
  [⟨.switch (call "calldataload" [w 0]) [
      ⟨.number "1", [action "sstore" [w 7, call "calldataload" [w 32]]], none⟩,
      ⟨.number "2", [action "sstore" [w 7, call "calldataload" [w 32]],
        action "mstore" [w 0, w 0xdeadbeef], action "revert" [w 28, w 4]], none⟩,
      ⟨.number "3", [action "selfdestruct" [call "calldataload" [w 32]]], none⟩] none, none⟩] ++
    ([call "address", call "caller", call "callvalue", call "sload" [w 7],
      call "selfbalance", call "codesize"].zipIdx.map fun (value, index) =>
        action "mstore" [w (32 * index), value]) ++ [action "return" [w 0, w 192]]
private def initBody : List YulStmt :=
  [action "sstore" [w 7, w 99], action "sstore" [w 8, call "extcodesize" [call "address"]],
   action "sstore" [w 9, call "extcodehash" [call "address"]],
   action "codecopy" [w 0, w 25, w 81], action "return" [w 0, w 81]]
private def source (body : List YulStmt) : Program := {
  objects := [.object "Object" {stmts := [⟨.assembly body, none⟩], functions := []} [] none]
  functions := []
  entryPoints := []
}
private def catalog : List AccountRuntime.CodeDefinition := [
  ⟨source targetBody, ["Object"], targetCode, false⟩,
  ⟨source initBody, ["Object"], initCode, true⟩,
  ⟨source [action "mstore" [w 0, w 0xdeadbeef], action "revert" [w 28, w 4]],
    ["Object"], revertCode, true⟩]
private def defaultContext : Contract.Context := {
  storage := [(word 7, word 10)]
  address := word 0xaaa
  caller := word 0xbbb
  balance := word 1000
  accounts := [(word 0xccc, word 1111), (word 0xddd, word 5)]
  emptyAccounts := [word 0xddd]
  world := [{
    address := word 0xccc
    code := some targetCode
    nonce := word 1
    storage := [(word 7, word 99)]
  }]
  availableGas := some (word 30000000)
}
private def prepare (label : String) (body : List YulStmt) (context : Contract.Context := defaultContext) :
    IO Contract.Prepared := do
  match Contract.compileObject (source body) ["Object"] 4096 (some [0x00]) catalog with
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
  | .ok compiled => pure (compiled.instantiate context)
private def returned (label : String) (receipt : Contract.Receipt) (expected : List UInt8) : IO Unit := do
  match receipt.outcome with
  | .returned bytes _ =>
      require (bytes == expected)
        s!"{label}: unexpected output {reprStr bytes}; expected {reprStr expected}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def account (label : String) (receipt : Contract.Receipt) (address : Nat) : IO AccountState.Account :=
  match receipt.world.find? (·.address == word address) with
  | some value => pure value
  | none => throw (IO.userError s!"{label}: missing account {address}")
private def slot (account : AccountState.Account) (key : Nat) : Core.Word :=
  Core.WordMapping.lookupEntries (word key) account.storage
private def balance (receipt : Contract.Receipt) (address : Nat) : Core.Word :=
  Core.WordMapping.lookupEntries (word address) receipt.balances
private def execute (label : String) (body : List YulStmt) (context : Contract.Context := defaultContext) :
    IO Contract.Receipt := do
  pure (Contract.runWithReceipt (← prepare label body context))

private def reportCall (operation : String) (value mode argument : Nat) (target : Nat := 0xccc) : List YulStmt :=
  let args := if operation == "call" || operation == "callcode" then
    [w 1000000, w target, w value, w 0, w 64, w 0, w 0]
    else [w 1000000, w target, w 0, w 64, w 0, w 0]
  [action "mstore" [w 0, w mode], action "mstore" [w 32, w argument],
   letVar "ok" (call operation args), letVar "size" (call "returndatasize"),
   action "mstore" [w 0, ident "ok"], action "mstore" [w 32, ident "size"],
   action "returndatacopy" [w 64, w 0, ident "size"],
   action "mstore" [call "add" [w 64, ident "size"], call "sload" [w 7]],
   action "mstore" [call "add" [w 96, ident "size"], call "selfbalance"],
   action "return" [w 0, call "add" [w 128, ident "size"]]]

private def callTests : IO Unit := do
  let receipt ← execute "delegate context" (reportCall "delegatecall" 0 1 77)
    {defaultContext with value := word 13, balance := word 1013}
  returned "delegate context" receipt (words [1, 192, 0xaaa, 0xbbb, 13, 77, 1013, 81, 77, 1013])
  require (slot (← account "delegate" receipt 0xaaa) 7 == word 77 &&
    slot (← account "delegate" receipt 0xccc) 7 == word 99) "delegate storage ownership"
  let receipt ← execute "callcode context" (reportCall "callcode" 17 1 88)
    {defaultContext with value := word 5, balance := word 1005}
  returned "callcode context" receipt (words [1, 192, 0xaaa, 0xaaa, 17, 88, 1005, 81, 88, 1005])
  require (balance receipt 0xccc == word 1111) "callcode transferred funds"
  let receipt ← execute "external call context" (reportCall "call" 17 1 77)
  returned "external call context" receipt (words [1, 192, 0xccc, 0xaaa, 17, 77, 1128, 81, 10, 983])
  require (slot (← account "call" receipt 0xccc) 7 == word 77 &&
    slot (← account "call" receipt 0xaaa) 7 == word 10) "call storage ownership"
  let receipt ← execute "insufficient callcode funds" (reportCall "callcode" 1001 1 55)
  returned "insufficient callcode funds" receipt (words [0, 0, 10, 1000])
  let receipt ← execute "delegate revert" (reportCall "delegatecall" 0 2 123)
  returned "delegate revert" receipt (words [0, 4] ++ hex "deadbeef" ++ words [10, 1000])
  require (slot (← account "reverted delegate" receipt 0xaaa) 7 == word 10) "delegate rollback"
  let receipt ← execute "static rejects write" (reportCall "staticcall" 0 1 42)
  returned "static rejects write" receipt (words [0, 0, 10, 1000])
  let receipt ← execute "static allows nonzero callcode" (reportCall "callcode" 17 0 0)
    {defaultContext with isStatic := true}
  returned "static allows nonzero callcode" receipt
    (words [1, 192, 0xaaa, 0xaaa, 17, 10, 1000, 81, 10, 1000])
  let receipt ← execute "known empty transfer" (reportCall "call" 3 0 0 0xddd)
  returned "known empty transfer" receipt (words [1, 0, 10, 997])
  require (balance receipt 0xddd == word 8) "empty recipient balance"
  let receipt ← execute "unknown executable image" (reportCall "call" 0 0 0)
    {defaultContext with world := [{address := word 0xccc, code := some [0x01], nonce := word 1}]}
  match receipt.outcome with
  | .languageFailure (.word reason) => require (reason == word 16) "unknown code failure reason"
  | other => throw (IO.userError s!"unknown code: {reprStr other}")
  require (receipt.world.isEmpty && receipt.balances.isEmpty && receipt.logs.isEmpty)
    "failed top-level call published account state"

private def writeMemory (bytes : List UInt8) : List YulStmt :=
  (List.range ((bytes.length + 31) / 32)).map fun index =>
    let chunk := (bytes.drop (32 * index)).take 32
    action "mstore" [w (32 * index), w (bytesNat (chunk ++ List.replicate (32 - chunk.length) 0))]
private def creation (two : Bool := false) (value : Nat := 17) (bytes : List UInt8 := initCode) : YulExpr :=
  if two then call "create2" [w value, w 0, w bytes.length, w 12345]
  else call "create" [w value, w 0, w bytes.length]
private def createBody (two : Bool := false) (bytes : List UInt8 := initCode) : List YulStmt :=
  writeMemory bytes ++ [letVar "child" (creation two 17 bytes),
    action "mstore" [w 0, ident "child"], action "mstore" [w 32, call "returndatasize"],
    action "mstore" [w 64, call "extcodesize" [ident "child"]],
    action "mstore" [w 96, call "extcodehash" [ident "child"]],
    action "return" [w 0, w 128]]
private def codeHash : Nat := bytesNat (Solcore.Abi.V1.Keccak256.hash targetCode.toByteArray).data.toList
private def createdAddress : Nat := 0x728c6cac8afdd93c35e798933d8d71a363fc4b4f
private def created2Address : Nat := bytesNat
  ((Solcore.Abi.V1.Keccak256.hash (([0xff] ++ (wordBytes 0xaaa).drop 12 ++ wordBytes 12345 ++
    (Solcore.Abi.V1.Keccak256.hash initCode.toByteArray).data.toList).toByteArray)).data.toList.drop 12)

private def creationTests : IO Unit := do
  let context := {defaultContext with completeWorld := true}
  let receipt ← execute "create public execution" (createBody) context
  returned "create public execution" receipt (words [createdAddress, 0, 81, codeHash])
  let child ← account "create" receipt createdAddress
  require (child.code == some targetCode && child.nonce == word 1 && slot child 7 == word 99)
    "created account image or persistent state"
  require (slot child 8 == word 0 && slot child 9 ==
    word 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)
    "constructing account exposed its code"
  require (!child.created && !child.destroyed && child.transient.isEmpty) "transaction flags escaped receipt"
  require ((← account "creator" receipt 0xaaa).nonce == word 2 &&
    balance receipt 0xaaa == word 983 && balance receipt createdAddress == word 17) "creation ledger/nonce"
  let collision := writeMemory initCode ++ [letVar "first" (creation true), letVar "second" (creation true 0),
    action "mstore" [w 0, ident "first"], action "mstore" [w 32, ident "second"], action "return" [w 0, w 64]]
  let receipt ← execute "create2 collision" collision context
  returned "create2 collision" receipt (words [created2Address, 0])
  require ((← account "create2 creator" receipt 0xaaa).nonce == word 3) "collision nonce increment"
  let reverted := writeMemory revertCode ++ [letVar "child" (creation false 17 revertCode),
    action "mstore" [w 0, ident "child"], action "mstore" [w 32, call "returndatasize"],
    action "returndatacopy" [w 64, w 0, w 4], action "return" [w 0, w 68]]
  let receipt ← execute "reverted constructor" reverted context
  returned "reverted constructor" receipt (words [0, 4] ++ hex "deadbeef")
  require ((← account "failed creator" receipt 0xaaa).nonce == word 2 && balance receipt 0xaaa == word 1000)
    "constructor failure lost nonce or retained transfer"
  require (!(receipt.world.any (·.address == word createdAddress))) "failed constructor account survived"
  let parentReverts := writeMemory initCode ++ [action "pop" [creation], action "revert" [w 0, w 0]]
  let receipt ← execute "parent reverts creation" parentReverts context
  match receipt.outcome with
  | .reverted [] => require (receipt.world.isEmpty && receipt.balances.isEmpty) "reverted parent published child"
  | other => throw (IO.userError s!"parent creation rollback: {reprStr other}")

private def destructionTests : IO Unit := do
  let receipt ← execute "existing selfdestruct" (reportCall "call" 0 3 0xddd)
  returned "existing selfdestruct" receipt (words [1, 0, 10, 1000])
  let target ← account "existing destruction" receipt 0xccc
  require (target.code == some targetCode && slot target 7 == word 99 && target.nonce == word 1)
    "existing selfdestruct deleted persistent state"
  require (balance receipt 0xccc == word 0 && balance receipt 0xddd == word 1116) "selfdestruct transfer"
  let receipt ← execute "existing self-beneficiary" (reportCall "call" 0 3 0xccc)
  returned "existing self-beneficiary" receipt (words [1, 0, 10, 1000])
  require (balance receipt 0xccc == word 1111) "existing self-beneficiary burned funds"
  let receipt ← execute "static selfdestruct" (reportCall "staticcall" 0 3 0xddd)
  returned "static selfdestruct" receipt (words [0, 0, 10, 1000])
  require (balance receipt 0xccc == word 1111) "static selfdestruct transferred funds"
  for selfBeneficiary in [false, true] do
    let recipient := if selfBeneficiary then ident "child" else w 0xddd
    let body := writeMemory initCode ++ [letVar "child" (creation true),
      action "mstore" [w 0, w 3], action "mstore" [w 32, recipient],
      letVar "ok" (call "call" [w 1000000, ident "child", w 0, w 0, w 64, w 0, w 0]),
      letVar "size" (call "extcodesize" [ident "child"]),
      letVar "hash" (call "extcodehash" [ident "child"])] ++ writeMemory initCode ++
      [letVar "again" (creation true 0), action "mstore" [w 0, ident "ok"],
       action "mstore" [w 32, ident "size"], action "mstore" [w 64, ident "hash"],
       action "mstore" [w 96, ident "again"], action "return" [w 0, w 128]]
    let receipt ← execute "created selfdestruct" body {defaultContext with completeWorld := true}
    returned "created selfdestruct" receipt (words [1, 81, codeHash, 0])
    require (!(receipt.world.any (·.address == word created2Address))) "created destroyed account survived finalization"
    require (balance receipt 0xddd == word (if selfBeneficiary then 5 else 22) &&
      balance receipt 0xaaa == word 983) "created destruction balance semantics"

private def hostWorldTests : IO Unit := do
  let alias := 2 ^ 200
  let context := {defaultContext with
    address := word (alias + 0xaaa)
    caller := word (alias + 0xbbb)
    emptyAccounts := [word (alias + 0xccc), word 0xccc, word (alias + 0xddd), word 0xddd]
    world := [
      {address := word (alias + 0xccc), code := some targetCode, created := true, destroyed := true},
      {address := word 0xccc, nonce := word 19, code := some targetCode},
      {address := word (alias + 0xaaa), nonce := word 20, storage := [(word 7, word 55)]},
      {address := word 0xaaa, nonce := word 21}]}
  let receipt ← execute "host normalizes duplicate account aliases"
    [action "mstore" [w 0, call "address"], action "mstore" [w 32, call "caller"],
     action "mstore" [w 64, call "sload" [w 7]], action "return" [w 0, w 96]] context
  returned "host normalizes duplicate account aliases" receipt (words [0xaaa, 0xbbb, 10])
  require (!(receipt.world.any (·.address == word 0xccc)))
    "finalization exposed a duplicate account after deleting its first alias"
  require ((← account "current account overrides aliases" receipt 0xaaa).nonce == word 1)
    "current account nonce did not override supplied aliases"
  let addresses := receipt.world.map AccountState.Account.address
  require (addresses.length == addresses.eraseDups.length && addresses.all (·.val < 2 ^ 160))
    "world receipt contains duplicate or noncanonical account addresses"

private def continuationTests : IO Unit := do
  let prepared ← prepare "creation suspension" createBody {defaultContext with completeWorld := true}
  let suspended := Contract.runWithReceipt prepared 1000
  let receipt ← match suspended.outcome with
    | .outOfFuel state =>
        require (suspended.world.isEmpty && suspended.balances.isEmpty && suspended.logs.isEmpty)
          "suspended transaction published partial account state"
        pure (Contract.resumeWithReceipt state)
    | other => throw (IO.userError s!"creation should suspend: {reprStr other}")
  returned "creation resumes with world references" receipt (words [createdAddress, 0, 81, codeHash])
  let creator ← account "resumed creator" receipt 0xaaa
  let next := {defaultContext with
    world := receipt.world, accounts := receipt.balances, storage := creator.storage,
    nonce := creator.nonce, balance := balance receipt 0xaaa, completeWorld := true}
  let nextReceipt ← execute "created image executes in a later transaction"
    (reportCall "call" 0 1 123 createdAddress) next
  returned "created image executes in a later transaction" nextReceipt
    (words [1, 192, createdAddress, 0xaaa, 0, 123, 17, 81, 10, 983])
  require (slot (← account "persisted child" nextReceipt createdAddress) 7 == word 123 &&
    (← account "persisted nonce" nextReceipt 0xaaa).nonce == word 2)
    "receipt replay lost child storage or creator nonce"
  let creator ← account "creator before later destruction" nextReceipt 0xaaa
  let finalContext := {next with
    world := nextReceipt.world, accounts := nextReceipt.balances, storage := creator.storage,
    nonce := creator.nonce, balance := balance nextReceipt 0xaaa}
  let finalReceipt ← execute "previously created child is now an existing account"
    (reportCall "call" 0 3 0xddd createdAddress) finalContext
  returned "previously created child is now an existing account" finalReceipt (words [1, 0, 10, 983])
  require ((← account "child survives later selfdestruct" finalReceipt createdAddress).code == some targetCode &&
    balance finalReceipt createdAddress == word 0 && balance finalReceipt 0xddd == word 22)
    "created flag incorrectly survived a public transaction boundary"

def run : IO Unit := do
  callTests
  creationTests
  destructionTests
  hostWorldTests
  continuationTests

end Tests.RustHullWorld
end

section
-- leanmerge: from Solcore.Test.RustHullWorldEffects
set_option autoImplicit false
namespace Tests.RustHullWorldEffects
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def number (n : Nat) : Solcore.Core.Expr := .word (Word.ofNatModulo n)
private def scalar (n : Nat) : Value := .word (Word.ofNatModulo n)
private def require (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)
private def slots := Effects.slots ++ Effects.codeSlots
private def scope : Scope := slots.reverse.map fun (name, type) =>
  ⟨some (Effects.slotName name), type, false⟩
private def account : AccountState.Account := {
  address := Word.ofNatModulo 0xaaa, nonce := Word.ofNatModulo 1,
  code := some [0x60, 0], created := true}
private def ambient : Ambient.Context := {
  origin := some (Word.ofNatModulo 0xbbb), number := some (Word.ofNatModulo 300),
  blockHashes := some [(Word.ofNatModulo 44, Word.ofNatModulo 123)],
  blobHashes := some [Word.ofNatModulo 42]}
private structure Settings where
  isStatic : Bool := false
  gas : Bool := true
  known : Bool := true
  mode : String := ""

private def callback (settings : Settings) (name : String) : Solcore.Core.Expr :=
  let expected := if name == "delegateCallHandler" then
    [(0, 0xccc), (1, 0xbbb), (2, 17), (4, 9), (5, 123)] else
    [(0, 0xccc), (1, 0xaaa), (2, 18), (4, 9), (5, 2423)]
  let rejected := LanguageResult.failure Calls.responseType (number 99)
  let success := LanguageResult.success (Calls.response (.bool true) WordMapping.empty (number 0))
  let checked := expected.foldr (fun (index, value) body =>
    .ifE (.binary .wordEq (Calls.requestField index (.var 0)) (number value)) body rejected) success
  .lambda Calls.requestType (LanguageResult.resultType Calls.responseType)
    (.ifE (.bool (settings.mode == name))
      (.ifE (Calls.requestField 3 (.var 0)) checked rejected) rejected)

private def creationCallback (settings : Settings) : Solcore.Core.Expr :=
  let expected := [(0, 0xaaa), (1, 9), (2, if settings.mode == "create2" then 77 else 0),
    (4, 9), (5, 222), (7, 0)]
  let rejected := LanguageResult.failure Creation.responseType (number 99)
  let success := LanguageResult.success (Creation.response (number 0x1234) WordMapping.empty (number 0))
  let checked := expected.foldr (fun (index, value) body =>
    .ifE (.binary .wordEq (Creation.requestField index (.var 0)) (number value)) body rejected) success
  let flag := Creation.requestField 3 (.var 0)
  .lambda Creation.requestType (LanguageResult.resultType Creation.responseType)
    (if settings.mode == "create2" then .ifE flag checked rejected else .ifE flag rejected checked)

private def initial (settings : Settings) (name : String) (type : Solcore.Core.Ty) : Solcore.Core.Expr :=
  match Ambient.slots.zipIdx.find? (fun entry => entry.1.1 == name) with
  | some (_, index) => Ambient.initialValue index (Ambient.contextExpression ambient)
  | none => match name with
    | "world" => AccountState.literal [(account, 1)]
    | "worldComplete" => .bool true
    | "balances" => WordMapping.literal [(Word.ofNatModulo 0xaaa, Word.ofNatModulo 100)]
    | "address" => number 0xaaa
    | "caller" => number 0xbbb
    | "callvalue" => number 17
    | "callDepth" => number 8
    | "isStatic" => .bool settings.isStatic
    | "availableGas" => if settings.gas then .inRight .unit (number 222) else .inLeft .word .unit
    | "codeKnown" => .bool settings.known
    | "code" => WordMapping.literal (Memory.packBytes [0x60, 0])
    | "codeSize" => number 2
    | "callHandler" | "callCodeHandler" | "delegateCallHandler" => .inRight .unit (callback settings name)
    | "createHandler" => .inRight .unit (creationCallback settings)
    | _ => match type with
      | .word => number 0
      | .bool => .bool false
      | .namedData _ => WordMapping.empty
      | _ => .unit

private def lower (name : String) (args : List Nat) : IO Lowered :=
  match Effects.lowerBuiltin scope name (args.map number) with
  | .ok value => pure value
  | .error error => throw (IO.userError error.message)

private def check (label : String) (lowered : Lowered) (settings : Settings)
    (expected : Value) (exit : Nat := 0) : IO Unit := do
  let compiled : Program := {
    resultType := LanguageResult.resultType lowered.type
    dataDefinitions := AccountState.definitions
    body := slots.foldr (fun (name, type) body =>
      .letE (.newCell type (initial settings name type)) body) lowered.expression
  }
  require compiled.check s!"{label}: ill-typed Core"
  match compiled.runStateful 3000000 with
  | .done value store =>
      require (value == expected) s!"{label}: expected {reprStr expected}, got {reprStr value}"
      let index := (slots.findIdx? (fun entry => entry.1 == "exit")).getD slots.length
      require (store[index]? == some (scalar exit)) s!"{label}: unexpected exit status"
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def success (n : Nat) : Value := .inRight .word (scalar n)
private def failure (type : Solcore.Core.Ty) (n : Nat) : Value := .inLeft type (scalar n)

def run : IO Unit := do
  for (writeName, readName) in [("sstore", "sload"), ("tstore", "tload")] do
    let write ← lower writeName [7, 99]
    let read ← lower readName [7]
    check writeName ⟨.word, LocalSequence.discard .word write.expression read.expression⟩ {} (success 99)
    check (writeName ++ " static") write {isStatic := true} (failure .unit (wordModulus - 1)) 3
  for (name, args, result) in [("origin", [], 0xbbb), ("blockhash", [44], 123),
      ("blobhash", [0], 42), ("extcodesize", [0xaaa], 2)] do
    check name (← lower name args) {} (success result)
  check "callcode" (← lower "callcode" [123, 0xccc, 18, 0, 0, 0, 0])
    {isStatic := true, mode := "callCodeHandler"} (success 1)
  check "delegatecall" (← lower "delegatecall" [123, 0xccc, 0, 0, 0, 0])
    {isStatic := true, mode := "delegateCallHandler"} (success 1)
  check "static nonzero call" (← lower "call" [123, 0xccc, 18, 0, 0, 0, 0])
    {isStatic := true} (failure .word (wordModulus - 1)) 3
  check "callcode stipend overflow" (← lower "callcode" [wordModulus - 1, 0xccc, 18, 0, 0, 0, 0])
    {isStatic := true} (failure .word 13)
  for (name, args) in [("create", [9, 0, 0]), ("create2", [9, 0, 0, 77])] do
    let effect ← lower name args
    check name effect {mode := name} (success 0x1234)
    check (name ++ " missing gas") effect {gas := false} (failure .word 9)
    check (name ++ " static") effect {gas := false, isStatic := true} (failure .word (wordModulus - 1)) 3
  check "oversized initcode" (← lower "create" [9, 0, 49153])
    {gas := false} (failure .word (wordModulus - 1)) 3
  for (name, args, type) in [("codesize", [], Solcore.Core.Ty.word),
      ("codecopy", [0, 0, 0], Solcore.Core.Ty.unit), ("datacopy", [0, 0, 0], Solcore.Core.Ty.unit)] do
    check name (← lower name args) {known := false} (failure type 15)
  check "selfdestruct" (← lower "selfdestruct" [0xdef]) {} (failure .unit (wordModulus - 1)) 1
  check "static selfdestruct" (← lower "selfdestruct" [0xdef])
    {isStatic := true} (failure .unit (wordModulus - 1)) 3
  IO.println "Rust Hull world effects tests passed"
end Tests.RustHullWorldEffects
end
