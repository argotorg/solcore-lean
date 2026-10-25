import Solcore.Frontend.RustHull.ContractHashExecutionCorrespondence
import Solcore.Abi.Keccak256

/-! Independent Keccak derivations reach public execution and repeated resume.
The output is stored beyond the hashed range, so the receipt and the original
memory bytes can both be checked against the source computation. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullKeccakCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where | empty | unaligned | rate | multiple | overflow
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def maximum := "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def offsetText : Scenario → String | .empty | .overflow => maximum | _ => "7"
def lengthText : Scenario → String
  | .empty => "0" | .unaligned => "3" | .rate => "136" | .multiple => "137" | .overflow => "1"
def offset : Scenario → Core.Word | .empty | .overflow => Core.Word.maximum | _ => w 7
def count : Scenario → Nat
  | .empty => 0 | .unaligned => 3 | .rate => 136 | .multiple => 137 | .overflow => 1
def hashCall (scenario : Scenario) : Expr := call .word "keccak256" [word (offsetText scenario), word (lengthText scenario)]
def seed : Expr := call .unit "mstore8" [word "7", word "171"]
def saveHash (scenario : Scenario) : Expr := call .unit "mstore" [word "192", hashCall scenario]
def returnHash : Expr := call .unit "return" [word "192", word "32"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression seed, expression (saveHash scenario), expression returnHash]
  functions := []
}
def program (scenario : Scenario) : Program := {
  entryPoints := [], functions := [], objects := [.object "Hash" (code scenario) []]
}
def context : Contract.Context := {}
def seeded : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 7) (w 171)).2
def firstBlock (scenario : Scenario) : KeccakSemantics.State :=
  KeccakSemantics.permute (KeccakSemantics.absorbBlock seeded.words (offset scenario) (w (count scenario)) (List.replicate 25 Core.Word.zero))
def digest (scenario : Scenario) : Core.Word :=
  if count scenario < 136 then KeccakSemantics.digest (firstBlock scenario)
  else KeccakSemantics.digest (KeccakSemantics.permute (KeccakSemantics.absorbBlock seeded.words
    ((offset scenario).add (w 136)) ((w (count scenario)).sub (w 136)) (firstBlock scenario)))
def touchedSize : Scenario → Core.Word
  | .empty | .unaligned | .overflow => w 32
  | .rate | .multiple => w 160

def hashed (scenario : Scenario) : MemorySemantics.State := {seeded with size := touchedSize scenario}
def saved (scenario : Scenario) : MemorySemantics.State := (MemorySemantics.mstore (hashed scenario) (w 192) (digest scenario)).2

def initial (object : Contract.CompiledObject) : Semantics.State RuntimeHashEffectsSemantics.State :=
  ⟨[], ContractHashCorrespondence.contextInitialState object (Contract.normalizeContext context)⟩
def memoryState (object : Contract.CompiledObject) (memory : MemorySemantics.State) : Semantics.State RuntimeHashEffectsSemantics.State :=
  ⟨[], RuntimeHashEffectsSemantics.withMemory (initial object).external memory⟩
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : Semantics.State RuntimeHashEffectsSemantics.State :=
  if scenario = .overflow then memoryState object seeded
  else ⟨[], RuntimeFullEffectsSemantics.withRuntime (memoryState object (saved scenario)).external
    (TerminationSemantics.terminate (memoryState object (saved scenario)).external.runtime.runtime 1 (w 192) (w 32)).2⟩
def reason (scenario : Scenario) : Core.Word := if scenario = .overflow then w 6 else Core.Word.maximum
def result (scenario : Scenario) : Semantics.Result Semantics.Value := .fault (.language (reason scenario))

theorem absorbed (scenario : Scenario) :
    KeccakSemantics.Absorb seeded.words (offset scenario) (w (count scenario))
      (List.replicate 25 Core.Word.zero) (digest scenario) := by
  cases scenario
  case empty => exact .last _ _ _ (by decide +kernel)
  case unaligned => exact .last _ _ _ (by decide +kernel)
  case rate => exact .more (by decide +kernel) (.last _ _ _ (by decide +kernel))
  case multiple => exact .more (by decide +kernel) (.last _ _ _ (by decide +kernel))
  case overflow => exact .last _ _ _ (by decide +kernel)

theorem hashing (scenario : Scenario) :
    KeccakSemantics.Hash (offset scenario) (w (count scenario)) seeded
      (if scenario = .overflow then MemorySemantics.overflow else .value (.word (digest scenario)))
      (if scenario = .overflow then seeded else hashed scenario) := by
  cases scenario
  case overflow => exact .overflow (by decide +kernel)
  all_goals exact .done (by decide +kernel) (absorbed _)

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeHashEffectsSemantics.effects [] seed
      (initial object) (.value .unit) (memoryState object seeded) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime rfl))))

private theorem hash_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeHashEffectsSemantics.effects [] (hashCall scenario)
      (memoryState object seeded)
      (if scenario = .overflow then MemorySemantics.overflow else .value (.word (digest scenario)))
      (memoryState object (if scenario = .overflow then seeded else hashed scenario)) := by
  cases scenario
  case empty =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "0") rfl) .nil)
    · exact .external (by rfl) rfl (.hash (.hash (hashing .empty)))
  case unaligned =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "3") rfl) .nil)
    · exact .external (by rfl) rfl (.hash (.hash (hashing .unaligned)))
  case rate =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "136") rfl) .nil)
    · exact .external (by rfl) rfl (.hash (.hash (hashing .rate)))
  case multiple =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "137") rfl) .nil)
    · exact .external (by rfl) rfl (.hash (.hash (hashing .multiple)))
  case overflow =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "1") rfl) .nil)
    · exact .external (by rfl) rfl (.hash (.hash (hashing .overflow)))


private theorem save_source (object : Contract.CompiledObject) (scenario : Scenario) (successful : scenario ≠ .overflow) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeHashEffectsSemantics.effects [] (saveHash scenario)
      (memoryState object seeded) (.value .unit) (memoryState object (saved scenario)) := by
  have hashedSource := hash_source object scenario
  simp only [successful, ↓reduceIte] at hashedSource
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "192") rfl) (.cons hashedSource .nil)
  · apply Semantics.EvalCall.external (by rfl) rfl
    apply RuntimeHashEffectsSemantics.Builtin.runtime
    apply RuntimeCopyEffectsSemantics.Builtin.runtime
    apply RuntimeFullEffectsSemantics.Builtin.runtime
    apply RuntimeLogEffectsSemantics.Builtin.runtime
    cases scenario <;> first | contradiction | rfl

private theorem overflow_source (object : Contract.CompiledObject) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code .overflow)] RuntimeHashEffectsSemantics.effects [] (saveHash .overflow)
      (memoryState object seeded) MemorySemantics.overflow (memoryState object seeded) := by
  apply Semantics.EvalExpr.callFault rfl
  exact .cons (.word (text := "192") rfl) (.fault (hash_source object .overflow))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) (successful : scenario ≠ .overflow) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeHashEffectsSemantics.effects [] returnHash
      (memoryState object (saved scenario)) (result scenario) (finalState object scenario) := by
  simp only [result, reason, finalState, successful, ↓reduceIte]
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "192") rfl) (.cons (.word (text := "32") rfl) .nil)
  · apply Semantics.EvalCall.external (by rfl) rfl
    exact .runtime (.runtime (.termination rfl))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] RuntimeHashEffectsSemantics.effects
      (AccountRuntime.frameFunction (code scenario)) [] (initial object) (result scenario) (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault (.language (reason scenario))) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object scenario))
  by_cases successful : scenario = .overflow
  · subst scenario
    exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (overflow_source object))
      (by intro impossible; cases impossible)
  · apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
      (.expression rfl (save_source object scenario successful))
    exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object scenario successful))
      (by intro impossible; cases impossible)

private theorem hash_eligible (scenario : Scenario) :
    ExecutableExpression ContractHashCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] (hashCall scenario) := by
  apply ExecutableExpression.external (name := "keccak256") (Or.inr rfl) (by rfl)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .word _ _ _

theorem eligible (scenario : Scenario) :
    ExecutableProgram ContractHashCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore8")
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨.store8, rfl⟩)))))) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "mstore")
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨.store, rfl⟩)))))) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · exact hash_eligible scenario
  · apply ExecutableExpression.external (name := "return")
      (Or.inl (Or.inl (Or.inr ⟨.returned, rfl⟩))) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _

theorem public_resumes (scenario : Scenario) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program scenario) ["Hash"] context 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program scenario) ["Hash"] 64 none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∃ value, ContractHashCorrespondence.PublicMessageRel context (result scenario) (finalState object scenario).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractHashCorrespondence.prepare_resumes_exact
    (code := code scenario) (by rfl) accepted (eligible scenario) rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object scenario)⟩

private def bytes (scenario : Scenario) : List UInt8 :=
  if count scenario = 0 then [] else 171 :: List.replicate (count scenario - 1) 0
private def referenceDigest (scenario : Scenario) : ByteArray := Abi.V1.Keccak256.hash (bytes scenario).toByteArray
private def referenceWord (scenario : Scenario) : Core.Word :=
  w ((referenceDigest scenario).data.foldl (fun value byte => value * 256 + byte.toNat) 0)

private def checkTouchedMemory (scenario : Scenario) : IO Unit := do
  let expression := Core.Expr.letE
    (.newCell Core.WordMapping.type (Core.WordMapping.literal seeded.words))
    (.letE (.newCell .word (.word seeded.size))
      (Core.LanguageResult.bind (.product .word .word)
        (Keccak.hash (.var 1) (.var 0) (.word (offset scenario)) (.word (w (count scenario))))
        (Core.LanguageResult.success (.pair (.var 0) (.loadCell (.var 1))))))
  let expected := if scenario = .overflow then Core.Value.inLeft (.product .word .word) (.word (w 6))
    else .inRight .word (.pair (.word (digest scenario)) (.word (touchedSize scenario)))
  match Core.runStateful 10000000 (Core.State.initial expression) with
  | .done value store =>
      unless value == expected && store[0]? == some (Core.WordMapping.encode seeded.words) &&
          store[1]? == some (.word (touchedSize scenario)) do
        throw (IO.userError "hash correspondence: hash changed memory or touched the wrong extent")
  | outcome => throw (IO.userError s!"hash correspondence: direct hash failed: {reprStr outcome}")

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Hash"] 64 with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"hash correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"hash correspondence: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 23).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"hash correspondence: short resume completed: {reprStr outcome}")
  let receipt := Contract.resumeWithReceipt checkpoint 10000000
  if scenario = .overflow then
    match receipt.outcome with
    | .languageFailure (.word reason) =>
        unless reason == w 6 && receipt.world.isEmpty && receipt.logs.isEmpty do
          throw (IO.userError "hash correspondence: overflow reason or receipt differs")
    | outcome => throw (IO.userError s!"hash correspondence: expected overflow, got {reprStr outcome}")
  else
    unless digest scenario == referenceWord scenario do
      throw (IO.userError "hash correspondence: independent source digest differs from the ABI hash")
    match receipt.outcome with
    | .returned returned storage =>
        unless returned == (referenceDigest scenario).data.toList && storage.isEmpty && receipt.logs.isEmpty do
          throw (IO.userError "hash correspondence: returned digest or empty effects differ")
    | outcome => throw (IO.userError s!"hash correspondence: expected returned digest, got {reprStr outcome}")
  match Core.runStateful 10000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair size (.pair memory _))))) _ =>
      let expected := (finalState object scenario).external.runtime.runtime
      unless memory == Core.WordMapping.encode expected.memory.words && exit == .word expected.storage.exit &&
          offset == .word expected.storage.returnOffset && size == .word expected.storage.returnSize do
        throw (IO.userError "hash correspondence: public snapshot differs from independent execution")
      for index in List.range 6 do
        unless MemorySemantics.lookup (w index) expected.memory.words == MemorySemantics.lookup (w index) seeded.words do
          throw (IO.userError "hash correspondence: hashing or padding changed input memory")
  | outcome => throw (IO.userError s!"hash correspondence: Core failed: {reprStr outcome}")

def run : IO Unit := do
  unless referenceWord .empty == w 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 do
    throw (IO.userError "hash correspondence: empty Keccak reference vector changed")
  for scenario in [Scenario.empty, .unaligned, .rate, .multiple, .overflow] do
    checkTouchedMemory scenario
    check scenario

end Tests.RustHullKeccakCorrespondence
